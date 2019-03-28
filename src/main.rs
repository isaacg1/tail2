#![allow(dead_code)]

extern crate rand;
use rand::distributions::{Distribution, Exp};
use rand::prelude::*;
use rand::Rng;
use rand::SeedableRng;

extern crate noisy_float;
use noisy_float::prelude::*;

use std::f64::INFINITY;

use std::collections::BTreeMap;
use std::collections::HashSet;

const EPSILON: f64 = 1e-10;

enum BST<T>
where
    T: Ord,
{
    Empty,
    Full(Box<BSTNode<T>>),
}

struct BSTNode<T: Ord> {
    size: usize,
    data: T,
    left: BST<T>,
    right: BST<T>,
}

impl<T: Ord> BST<T> {
    fn new() -> Self {
        BST::Empty
    }

    fn insert(&mut self, data: T) {
        match self {
            BST::Empty => {
                let new = BSTNode {
                    size: 1,
                    data,
                    left: Self::new(),
                    right: Self::new(),
                };
                *self = BST::Full(Box::new(new));
            }
            BST::Full(b) => {
                if data < b.data || data == b.data && thread_rng().gen() {
                    b.size += 1;
                    b.left.insert(data);
                } else {
                    b.size += 1;
                    b.right.insert(data);
                }
            }
        }
    }
    fn len(&self) -> usize {
        match self {
            BST::Empty => 0,
            BST::Full(b) => b.size,
        }
    }
    fn nth(&self, n: usize) -> Option<&T> {
        if n >= self.len() {
            return None;
        }
        match self {
            BST::Empty => unreachable!(),
            BST::Full(b) => {
                let left_size = b.left.len();
                if n < left_size {
                    b.left.nth(n)
                } else if n == left_size {
                    Some(&b.data)
                } else {
                    b.right.nth(n - left_size - 1)
                }
            }
        }
    }
}

#[derive(Debug)]
struct Job {
    id: usize,
    size: f64,
    rem_size: f64,
    arrival_time: f64,
    data: Option<f64>,
}

impl Job {
    fn new(size: f64, time: f64, id: usize) -> Self {
        Self {
            id,
            size,
            rem_size: size,
            arrival_time: time,
            data: None,
        }
    }
    fn new_with_data(size: f64, time: f64, id: usize, data: f64) -> Self {
        Self {
            id,
            size,
            rem_size: size,
            arrival_time: time,
            data: Some(data),
        }
    }
}

#[derive(Debug)]
struct Completion {
    id: usize,
    size: f64,
    response_time: f64,
    arrival_time: f64,
    data: Option<f64>,
}

impl Completion {
    fn from_job(job: Job, time: f64) -> Self {
        assert!(job.rem_size <= EPSILON);
        Self {
            id: job.id,
            size: job.size,
            response_time: time - job.arrival_time,
            arrival_time: job.arrival_time,
            data: job.data,
        }
    }
}

#[derive(Clone, Debug)]
struct Arrival {
    id: usize,
    size: f64,
    arrival_time: f64,
}

impl Arrival {
    fn from_completion(completion: &Completion) -> Self {
        Self {
            id: completion.id,
            size: completion.size,
            arrival_time: completion.arrival_time,
        }
    }
}

#[derive(Copy, Clone, Debug)]
enum Ranker {
    SRPT,
    FCFS,
    LeastLaxity,
    Random,
}

impl Ranker {
    fn rank(self, j: &Job) -> f64 {
        match self {
            Ranker::SRPT => j.rem_size,
            Ranker::FCFS => j.arrival_time,
            Ranker::LeastLaxity => j.arrival_time - j.rem_size,
            Ranker::Random => thread_rng().gen(),
        }
    }
}

#[derive(Copy, Clone, Debug)]
enum Target {
    Percentile(f64),
    Time(f64),
}

impl Target {
    fn eval(&self, latencies: &BST<N64>) -> f64 {
        match &self {
            Target::Time(t) => *t,
            Target::Percentile(p) => {
                let time_index = (latencies.len() as f64 * p) as usize;
                latencies
                    .nth(time_index)
                    .cloned()
                    .map_or(INFINITY, |t| t.raw())
            }
        }
    }
}

#[derive(Copy, Clone, Debug)]
enum Policy {
    SRPT,
    FCFS,
    PS,
    Undominated,
    BPS,
    TRR,
    FB,
    Hybrid,
    Threshold(Target),
    DelayLarge(f64),
    DelayLargeOrOld(f64, Target),
    DynamicLargeOrOld(Target),
    MooreSRPT(Target),
    MooreFCFS(Target),
    MooreG(Target, Ranker, Ranker),
    LeastLaxity(Target),
    MooreBuckets(f64, f64),
    LPS,
    SRPTEject(Target),
    Ejector(Target),
    BoundedNumberFCFS(usize, Target),
    BoundedNumberFB(usize, Target),
    OldestUnexchangable(Target),
    OldestUnexchangableMulti(Target),
    SmallestLate(Target),
    SmallestLateSimple(Target),
}

impl Policy {
    // More imputs in future
    fn rates(
        &self,
        queue: &[Job],
        current_time: f64,
        sizes: &BST<N64>,
        latencies: &BST<N64>,
        rho: f64,
        scratch: &mut HashSet<usize>,
    ) -> Vec<f64> {
        match &self {
            Policy::SRPT
            | Policy::FCFS
            | Policy::TRR
            | Policy::FB
            | Policy::LeastLaxity(_)
            | Policy::Threshold(_)
            | Policy::DelayLarge(_)
            | Policy::SRPTEject(_)
            | Policy::SmallestLate(_)
            | Policy::SmallestLateSimple(_)
            | Policy::DelayLargeOrOld(_, _) => {
                let best = queue.iter().enumerate().min_by_key(|(_i, job)| {
                    n64(match &self {
                        Policy::SRPT => job.rem_size,
                        Policy::FCFS => job.arrival_time,
                        Policy::TRR => job.rem_size / (current_time - job.arrival_time),
                        // Approximate FB
                        Policy::FB => job.size - job.rem_size,
                        Policy::Threshold(t) => {
                            let time_threshold = t.eval(&latencies);
                            if current_time - job.arrival_time > time_threshold {
                                job.arrival_time - current_time
                            } else {
                                job.size - job.rem_size
                            }
                        }
                        Policy::DelayLarge(p) => {
                            let index = (sizes.len() as f64 * p) as usize;
                            let size_threshold = *sizes.nth(index).unwrap();
                            if n64(job.size) <= size_threshold {
                                job.arrival_time
                            } else {
                                current_time + job.rem_size
                            }
                        }
                        Policy::DelayLargeOrOld(size_p, time_p) => {
                            let size_index = (sizes.len() as f64 * size_p) as usize;
                            let size_threshold =
                                sizes.nth(size_index).cloned().unwrap_or(n64(INFINITY));
                            let time_threshold = time_p.eval(&latencies);
                            if n64(current_time - job.arrival_time + job.rem_size) > time_threshold
                            {
                                current_time * 2.0 + job.rem_size
                            } else if n64(job.size) > size_threshold {
                                current_time + job.rem_size
                            } else {
                                job.arrival_time
                            }
                        }
                        Policy::LeastLaxity(p) => {
                            let time_threshold = p.eval(&latencies);
                            let laxity =
                                time_threshold - ((current_time - job.arrival_time) + job.rem_size);
                            if laxity >= 0.0 {
                                laxity
                            } else {
                                laxity + current_time
                            }
                        }
                        Policy::SRPTEject(p) => {
                            let time_threshold = p.eval(&latencies);
                            if n64(current_time - job.arrival_time + job.rem_size) > time_threshold
                            {
                                current_time + job.rem_size
                            } else {
                                job.rem_size
                            }
                        }
                        Policy::SmallestLate(t) => {
                            let time_threshold = t.eval(&latencies);
                            if n64(current_time - job.arrival_time + job.rem_size) > time_threshold
                            {
                                job.rem_size
                            } else {
                                job.arrival_time
                            }
                        }
                        Policy::SmallestLateSimple(t) => {
                            let time_threshold = t.eval(&latencies);
                            if n64(current_time - job.arrival_time) > time_threshold {
                                job.rem_size
                            } else {
                                job.arrival_time
                            }
                        }
                        _ => unreachable!(),
                    })
                });
                let mut out = vec![0.0; queue.len()];
                if let Some(best) = best {
                    out[best.0] = 1.0;
                }
                out
            }
            Policy::LPS => {
                let c = (1.0 / (1.0 - rho)).floor() as usize + 1;
                if c >= queue.len() {
                    vec![1.0 / queue.len() as f64; queue.len()]
                } else if queue.is_empty() {
                    vec![]
                } else {
                    let mut ordered_jobs: Vec<(usize, &Job)> = queue.iter().enumerate().collect();
                    ordered_jobs.sort_by_key(|(_, j)| n64(j.arrival_time));
                    let threshold_time = ordered_jobs[c - 1].1.arrival_time;
                    let mut out = vec![0.0; queue.len()];
                    for (index, job) in ordered_jobs {
                        if job.arrival_time <= threshold_time {
                            out[index] = 1.0 / c as f64;
                        }
                    }
                    out
                }
            }
            Policy::MooreG(p, low_ranker, high_ranker) => {
                if queue.is_empty() {
                    vec![]
                } else {
                    let time_threshold = p.eval(&latencies);
                    let mut ordered_jobs: Vec<(usize, &Job)> = queue
                        .iter()
                        .enumerate()
                        .filter(|(_, j)| {
                            n64(current_time - j.arrival_time + j.rem_size) <= time_threshold
                        })
                        .collect();
                    ordered_jobs.sort_by_key(|(_, j)| n64(j.arrival_time));
                    let mut removed_indices: HashSet<usize> = HashSet::new();
                    let mut current_sum = 0.0;
                    let mut i = 0;
                    while i < ordered_jobs.len() {
                        let j = &ordered_jobs[i].1;
                        current_sum += j.rem_size;
                        let j_deadline = time_threshold - (current_time - j.arrival_time);
                        if n64(current_sum) >= j_deadline {
                            let removed_index = (0..=i)
                                .filter(|index| !removed_indices.contains(index))
                                .max_by_key(|&index| n64(ordered_jobs[index].1.rem_size))
                                .unwrap();
                            let was_absent = removed_indices.insert(removed_index);
                            assert!(was_absent);
                            assert!(removed_index <= i);
                            current_sum -= ordered_jobs[removed_index].1.rem_size;
                            assert!(n64(current_sum) < j_deadline);
                        }
                        i += 1;
                    }
                    let opt_set: Vec<(usize, &Job)> = ordered_jobs
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| !removed_indices.contains(&i))
                        .map(|(_, t)| t)
                        .cloned()
                        .collect();
                    let mut allowed_first = vec![];
                    let mut current_sum = 0.0;
                    let mut max_additional_allowed = INFINITY;
                    for (i, j) in opt_set {
                        if j.rem_size <= max_additional_allowed {
                            allowed_first.push((i, j));
                        }
                        current_sum += j.rem_size;
                        let laxity =
                            time_threshold - ((current_time - j.arrival_time) + current_sum);
                        max_additional_allowed = max_additional_allowed.min(laxity);
                    }
                    let choice: (usize, &Job) = if allowed_first.is_empty() {
                        *if ordered_jobs.is_empty() {
                            queue.iter().enumerate().collect()
                        } else {
                            ordered_jobs
                        }
                        .iter()
                        .min_by_key(|(_, j)| n64(high_ranker.rank(j)))
                        .unwrap()
                    } else {
                        *allowed_first
                            .iter()
                            .min_by_key(|(_, j)| n64(low_ranker.rank(j)))
                            .unwrap()
                    };
                    let mut out = vec![0.0; queue.len()];
                    out[choice.0] = 1.0;
                    out
                }
            }
            Policy::MooreFCFS(p) => {
                if queue.is_empty() {
                    vec![]
                } else {
                    let time_threshold = p.eval(&latencies);
                    let mut ordered_jobs: Vec<(usize, &Job)> = queue
                        .iter()
                        .enumerate()
                        .filter(|(_, j)| {
                            n64(current_time - j.arrival_time + j.rem_size) <= time_threshold
                        })
                        .collect();
                    ordered_jobs.sort_by_key(|(_, j)| n64(j.arrival_time));
                    let mut removed_indices: HashSet<usize> = HashSet::new();
                    let mut current_sum = 0.0;
                    let mut i = 0;
                    while i < ordered_jobs.len() {
                        let j = &ordered_jobs[i].1;
                        current_sum += j.rem_size;
                        let j_deadline = time_threshold - (current_time - j.arrival_time);
                        if n64(current_sum) >= j_deadline {
                            let removed_index = (0..=i)
                                .filter(|index| !removed_indices.contains(index))
                                .max_by_key(|&index| n64(ordered_jobs[index].1.rem_size))
                                .unwrap();
                            let was_absent = removed_indices.insert(removed_index);
                            assert!(was_absent);
                            assert!(removed_index <= i);
                            current_sum -= ordered_jobs[removed_index].1.rem_size;
                            assert!(n64(current_sum) < j_deadline);
                        }
                        i += 1;
                    }
                    let choice = ordered_jobs
                        .iter()
                        .enumerate()
                        .find(|(i, _)| !removed_indices.contains(&i))
                        .map_or_else(
                            || {
                                // Fallback to FCFS
                                queue
                                    .iter()
                                    .enumerate()
                                    .min_by_key(|(_, j)| n64(j.arrival_time))
                                    .unwrap()
                                    .0
                            },
                            |(_, (i, _))|
                                // Extract original index
                                *i,
                        );
                    let mut out = vec![0.0; queue.len()];
                    out[choice] = 1.0;
                    out
                }
            }
            Policy::MooreSRPT(p) => {
                if queue.is_empty() {
                    vec![]
                } else {
                    /*
                    if latencies.len() < (10.0 / (1.0 - p)) as usize {
                        let smallest = queue
                            .iter()
                            .enumerate()
                            .min_by_key(|(_, j)| n64(j.rem_size))
                            .unwrap()
                            .0;
                        let mut out = vec![0.0; queue.len()];
                        out[smallest] = 1.0;
                        out
                    } else {*/
                    let time_threshold = p.eval(&latencies);
                    let mut ordered_jobs: Vec<(usize, &Job)> = queue
                        .iter()
                        .enumerate()
                        .filter(|(_, j)| {
                            n64(current_time - j.arrival_time + j.rem_size) <= time_threshold
                        })
                        .collect();
                    ordered_jobs.sort_by_key(|(_, j)| n64(j.rem_size));
                    let index = loop {
                        let mut time_spent = 0.0;
                        let mut reorder_at = None;
                        for (i, (_, job)) in ordered_jobs.iter().enumerate() {
                            time_spent += job.rem_size;
                            if n64(current_time - job.arrival_time + time_spent) > time_threshold {
                                reorder_at = Some(i);
                                break;
                            }
                        }
                        if let Some(position) = reorder_at {
                            let potential_removal_id = ordered_jobs[position].0;
                            // Ordered jobs sort up to position
                            let helper = &mut ordered_jobs[..=position];
                            helper.sort_by_key(|(_, j)| n64(j.arrival_time));
                            // Check whether all good up to position.
                            let mut all_good = true;
                            let mut time_spent = 0.0;
                            for (_, j) in helper {
                                time_spent += j.rem_size;
                                if n64(current_time - j.arrival_time + time_spent) > time_threshold
                                {
                                    all_good = false;
                                    break;
                                }
                            }
                            if !all_good {
                                let removal_position = ordered_jobs
                                    .iter()
                                    .position(|(i, _)| *i == potential_removal_id)
                                    .unwrap();
                                ordered_jobs.remove(removal_position);
                            }
                        } else {
                            // Arbitrary fallback to SRPT if everything fails
                            break ordered_jobs.first().map_or_else(
                                || {
                                    queue
                                        .iter()
                                        .enumerate()
                                        .min_by_key(|(_, j)| n64(j.rem_size))
                                        .unwrap()
                                        .0
                                },
                                |t| t.0,
                            );
                        }
                    };
                    let mut out = vec![0.0; queue.len()];
                    out[index] = 1.0;
                    out
                    //}
                }
            }
            Policy::MooreBuckets(base_inv_percentile, ratio) => {
                let maybe_smallest_achievable_deadline = queue
                    .iter()
                    .map(|j| n64(current_time - j.arrival_time + j.rem_size))
                    .min();
                if let Some(smallest_achievable_deadline) = maybe_smallest_achievable_deadline {
                    let mut target_inv_percentile = *base_inv_percentile;
                    let bucket_deadline = loop {
                        let time_index =
                            (latencies.len() as f64 * (1.0 - target_inv_percentile)) as usize;
                        let maybe_target_deadline = latencies.nth(time_index);
                        if let Some(target_deadline) = maybe_target_deadline {
                            if *target_deadline >= smallest_achievable_deadline {
                                break target_deadline.raw();
                            } else {
                                target_inv_percentile *= ratio
                            }
                        } else {
                            break INFINITY;
                        }
                    };
                    let mut ordered_jobs: Vec<(usize, &Job)> = queue
                        .iter()
                        .enumerate()
                        .filter(|(_, j)| {
                            n64(current_time - j.arrival_time + j.rem_size) <= bucket_deadline
                        })
                        .collect();
                    ordered_jobs.sort_by_key(|(_, j)| n64(j.arrival_time));
                    let mut removed_indices: HashSet<usize> = HashSet::new();
                    let mut current_sum = 0.0;
                    let mut i = 0;
                    while i < ordered_jobs.len() {
                        let j = &ordered_jobs[i].1;
                        current_sum += j.rem_size;
                        let j_deadline = bucket_deadline - (current_time - j.arrival_time);
                        if n64(current_sum) >= j_deadline {
                            let removed_index = (0..=i)
                                .filter(|index| !removed_indices.contains(index))
                                .max_by_key(|&index| n64(ordered_jobs[index].1.rem_size))
                                .unwrap();
                            let was_absent = removed_indices.insert(removed_index);
                            assert!(was_absent);
                            assert!(removed_index <= i);
                            current_sum -= ordered_jobs[removed_index].1.rem_size;
                            assert!(n64(current_sum) < j_deadline);
                        }
                        i += 1;
                    }
                    let choice = ordered_jobs
                        .iter()
                        .enumerate()
                        .find(|(i, _)| !removed_indices.contains(&i))
                        .unwrap();
                    let choice_index = choice.1 .0;
                    let mut out = vec![0.0; queue.len()];
                    out[choice_index] = 1.0;
                    out
                } else {
                    vec![]
                }
            }
            Policy::DynamicLargeOrOld(p) => {
                let time_threshold = p.eval(&latencies);
                let mut size_queue: Vec<&Job> = queue
                    .iter()
                    .filter(|job| {
                        n64(current_time - job.arrival_time + job.rem_size) <= time_threshold
                    })
                    .collect();
                size_queue.sort_by_key(|j| n64(j.rem_size));
                let size_threshold = (|| {
                    let mut size_sum = 0.0;
                    for j in size_queue {
                        size_sum += j.rem_size;
                        if n64(size_sum) >= time_threshold {
                            return j.rem_size;
                        }
                    }
                    INFINITY
                })();
                let best = queue.iter().enumerate().min_by_key(|(_i, job)| {
                    n64(
                        if n64(current_time - job.arrival_time + job.rem_size) > time_threshold {
                            current_time * 2.0 + job.rem_size
                        } else if job.rem_size >= size_threshold {
                            current_time + job.rem_size
                        } else {
                            job.arrival_time
                        },
                    )
                });
                let mut out = vec![0.0; queue.len()];
                if let Some(best) = best {
                    out[best.0] = 1.0;
                }
                out
            }
            Policy::PS => vec![1.0 / queue.len() as f64; queue.len()],
            Policy::Undominated => {
                let mut indices: Vec<usize> = (0..queue.len()).collect();
                indices.sort_by_key(|&i| n64(queue[i].rem_size));
                let mut undominated: Vec<usize> = vec![];
                for i in indices {
                    if let Some(l) = undominated.last() {
                        let j = &queue[i];
                        let l_j = &queue[*l];
                        if j.arrival_time < l_j.arrival_time {
                            undominated.push(i);
                        }
                    } else {
                        undominated.push(i);
                    }
                }
                let mut out = vec![0.0; queue.len()];
                for &u in &undominated {
                    out[u] += 1.0 / (undominated.len()) as f64;
                }
                out
            }
            Policy::Hybrid => {
                let lowest_age = queue
                    .iter()
                    .enumerate()
                    .min_by_key(|(_, j)| n64(j.size - j.rem_size));
                let highest_time = queue
                    .iter()
                    .enumerate()
                    .min_by_key(|(_, j)| n64(j.arrival_time));
                let mut out = vec![0.0; queue.len()];
                if let Some(lowest_age) = lowest_age {
                    out[lowest_age.0] += 0.5;
                }
                if let Some(highest_time) = highest_time {
                    out[highest_time.0] += 0.5;
                }
                out
            }
            // Note: currently slow
            Policy::BPS => {
                let mut indices: Vec<usize> = (0..queue.len()).collect();
                indices.sort_by_key(|&i| n64(queue[i].rem_size));
                let mut undominated: Vec<usize> = vec![];
                for i in indices {
                    if let Some(l) = undominated.last() {
                        let j = &queue[i];
                        let l_j = &queue[*l];
                        if j.arrival_time < l_j.arrival_time {
                            undominated.push(i);
                        }
                    } else {
                        undominated.push(i);
                    }
                }
                let mut out = vec![0.0; queue.len()];
                for job in queue {
                    for &u in &undominated {
                        let j_u = &queue[u];
                        if job.rem_size >= j_u.rem_size && job.arrival_time >= j_u.arrival_time {
                            out[u] += 1.0;
                        }
                    }
                }
                let sum: f64 = out.iter().sum();
                let real_out: Vec<f64> = out.iter().map(|o| o / sum).collect();
                real_out
            }
            Policy::Ejector(t) => {
                let time_threshold = t.eval(latencies);
                let queue_size: f64 = queue
                    .iter()
                    .filter(|j| !scratch.contains(&j.id))
                    .map(|j| j.rem_size)
                    .sum();
                if queue_size > time_threshold {
                    // Moore:
                    // let worst = queue.iter().filter(|j| !scratch.contains(&j.id)).max_by_key(|j| n64(j.rem_size)).unwrap();
                    let new = queue
                        .iter()
                        .max_by_key(|j| n64(j.arrival_time))
                        .expect("Something made it go over");
                    assert!(queue_size - new.rem_size <= time_threshold);
                    scratch.insert(new.id);
                }
                let maybe_choice = queue.iter().enumerate().min_by_key(|(_, j)| {
                    n64(if scratch.contains(&j.id) {
                        current_time + j.rem_size
                    } else {
                        j.arrival_time
                    })
                });
                let mut out = vec![0.0; queue.len()];
                if let Some((i, _)) = maybe_choice {
                    out[i] = 1.0;
                }
                out
            }
            Policy::BoundedNumberFCFS(b, t) => {
                let time_threshold = t.eval(latencies);
                for j in queue {
                    if current_time - j.arrival_time > time_threshold {
                        scratch.insert(j.id);
                    }
                }
                let queue_len = queue.iter().filter(|j| !scratch.contains(&j.id)).count();
                if queue_len > *b {
                    assert_eq!(queue_len - 1, *b);
                    let new = queue
                        .iter()
                        .filter(|j| !scratch.contains(&j.id))
                        .max_by_key(|j| n64(j.arrival_time))
                        .expect("Something made it go over");
                    scratch.insert(new.id);
                }
                let maybe_choice = queue.iter().enumerate().min_by_key(|(_, j)| {
                    (
                        current_time - j.arrival_time > time_threshold,
                        scratch.contains(&j.id),
                        n64(j.arrival_time),
                    )
                });
                let mut out = vec![0.0; queue.len()];
                if let Some((i, _)) = maybe_choice {
                    out[i] = 1.0;
                }
                out
            }
            Policy::BoundedNumberFB(b, t) => {
                let time_threshold = t.eval(latencies);
                for j in queue {
                    if current_time - j.arrival_time > time_threshold {
                        scratch.insert(j.id);
                    }
                }
                let queue_len = queue.iter().filter(|j| !scratch.contains(&j.id)).count();
                if queue_len > *b {
                    assert_eq!(queue_len - 1, *b);
                    let new = queue
                        .iter()
                        .filter(|j| !scratch.contains(&j.id))
                        .max_by_key(|j| n64(j.arrival_time))
                        .expect("Something made it go over");
                    scratch.insert(new.id);
                }
                let maybe_choice = queue.iter().enumerate().min_by_key(|(_, j)| {
                    (
                        current_time - j.arrival_time > time_threshold,
                        scratch.contains(&j.id),
                        n64(j.size - j.rem_size),
                    )
                });
                let mut out = vec![0.0; queue.len()];
                if let Some((i, _)) = maybe_choice {
                    out[i] = 1.0;
                }
                out
            }
            Policy::OldestUnexchangable(t) => {
                let time_threshold = t.eval(latencies);
                let mut indices: Vec<usize> = (0..queue.len()).collect();
                indices.sort_by_key(|&i| n64(queue[i].rem_size));
                let mut undominated: Vec<usize> = vec![];
                for i in indices {
                    if let Some(l) = undominated.last() {
                        let j = &queue[i];
                        let l_j = &queue[*l];
                        if j.arrival_time < l_j.arrival_time {
                            undominated.push(i);
                        }
                    } else {
                        undominated.push(i);
                    }
                }
                let mut strongest_threshold = time_threshold;
                let mut curr_out = None;
                for (_ui, &index) in undominated.iter().enumerate() {
                    let job = &queue[index];
                    if job.rem_size <= strongest_threshold {
                        curr_out = Some(index);
                        strongest_threshold = time_threshold - (current_time - job.arrival_time);
                    } else {
                        break;
                    }
                }
                let mut out = vec![0.0; queue.len()];
                if let Some(i) = curr_out.or_else(|| undominated.first().cloned()) {
                    out[i] = 1.0;
                }
                out
            }
            Policy::OldestUnexchangableMulti(t) => {
                let time_threshold = t.eval(latencies);
                let mut indices: Vec<usize> = (0..queue.len()).collect();
                indices.sort_by_key(|&i| n64(queue[i].rem_size));
                let mut undominated: Vec<(usize, usize)> = vec![];
                for (size_index, &queue_index) in indices.iter().enumerate() {
                    if let Some((_, old_queue_index)) = undominated.last() {
                        let j = &queue[queue_index];
                        let l_j = &queue[*old_queue_index];
                        if j.arrival_time < l_j.arrival_time {
                            undominated.push((size_index, queue_index));
                        }
                    } else {
                        undominated.push((size_index, queue_index));
                    }
                }
                let mut curr_out = None;
                for &(size_index, queue_index) in &undominated {
                    let mut strongest_threshold = INFINITY;
                    let mut smaller = indices[..size_index].to_vec();
                    smaller.sort_by_key(|i| {
                        n64(queue[*i].rem_size - (current_time - queue[*i].arrival_time))
                    });
                    let mut total_size = 0.0;
                    for i in smaller {
                        let job = &queue[i];
                        let threshold =
                            time_threshold - (total_size + current_time - job.arrival_time);
                        strongest_threshold = strongest_threshold.min(threshold);
                        total_size += job.rem_size;
                    }
                    if queue[queue_index].rem_size <= strongest_threshold {
                        curr_out = Some(queue_index);
                    } else {
                        break;
                    }
                }
                let mut out = vec![0.0; queue.len()];
                if let Some(i) = curr_out {
                    out[i] = 1.0;
                }
                out
            }
        }
    }
}

#[derive(Clone, Debug)]
enum Size {
    Exp(f64),
    Pareto(f64),
    Hyper(f64, f64, f64),
    Det(f64),
    Bimodal(f64, f64, f64),
}

impl Distribution<f64> for Size {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> f64 {
        match *self {
            Size::Exp(lambda) => {
                let dist = Exp::new(lambda);
                dist.sample(rng)
            }
            Size::Pareto(alpha) => rng.gen_range(0., 1.).powf(-1. / alpha),
            Size::Hyper(low, high, low_prob) => {
                let mean = if rng.gen_range(0., 1.) < low_prob {
                    low
                } else {
                    high
                };
                let dist = Exp::new(1.0 / mean);
                dist.sample(rng)
            }
            Size::Det(x) => x,
            Size::Bimodal(low, high, low_prob) => {
                if rng.gen::<f64>() < low_prob {
                    low
                } else {
                    high
                }
            }
        }
    }
}

impl Size {
    fn balanced_hyper(c_2: f64) -> Self {
        assert!(c_2 >= 1.0);
        let high = c_2 + (c_2 * c_2 - 1.0).sqrt();
        Size::Hyper(1.0, high, high / (high + 1.0))
    }
    fn mean(&self) -> f64 {
        match *self {
            Size::Exp(lambda) => 1.0 / lambda,
            Size::Pareto(alpha) => alpha / (alpha - 1.0),
            Size::Hyper(low, high, low_prob) => low * low_prob + high * (1.0 - low_prob),
            Size::Bimodal(low, high, low_prob) => low * low_prob + high * (1.0 - low_prob),
            Size::Det(x) => x,
        }
    }
}

fn opt(arrivals: Vec<Arrival>, target: f64) -> Vec<Completion> {
    let mut arrivals = arrivals;
    arrivals.sort_by_key(|a| n64(a.arrival_time));
    let mut ejections = HashSet::new();
    let mut finishing_time = 0.0;
    let mut last_arrival_to_empty_queue = 0;
    for (i, arrival) in arrivals.iter().enumerate() {
        let potential_finishing_time;
        if arrival.arrival_time > finishing_time {
            potential_finishing_time = arrival.arrival_time + arrival.size;
            last_arrival_to_empty_queue = i;
        } else {
            potential_finishing_time = finishing_time + arrival.size;
        }
        if potential_finishing_time > arrival.arrival_time + target {
            let potential_removal_indices: Vec<usize> = (last_arrival_to_empty_queue..=i)
                .filter(|pi| !ejections.contains(pi))
                .collect();
            let (removal, revised_finishing_time) = if potential_removal_indices.len() == 1 {
                assert_eq!(potential_removal_indices[0], i);
                (i, finishing_time)
            } else {
                let oldest = &arrivals[potential_removal_indices[0]];
                let second_oldest = &arrivals[potential_removal_indices[1]];
                let mut old_removal_candidate = potential_removal_indices[0];
                let mut old_finishing_time = second_oldest.arrival_time + second_oldest.size;
                let mut new_finishing_time = oldest.arrival_time + oldest.size;
                let mut consideration_index = 1;
                loop {
                    if old_finishing_time > new_finishing_time {
                        old_removal_candidate = potential_removal_indices[consideration_index];
                        old_finishing_time = new_finishing_time;
                    }
                    if consideration_index == potential_removal_indices.len() - 1 {
                        break (old_removal_candidate, old_finishing_time);
                    }
                    let current_arrival = &arrivals[potential_removal_indices[consideration_index]];
                    new_finishing_time =
                        new_finishing_time.max(current_arrival.arrival_time) + current_arrival.size;
                    consideration_index += 1;
                    let new_arrival = &arrivals[potential_removal_indices[consideration_index]];
                    old_finishing_time =
                        old_finishing_time.max(new_arrival.arrival_time) + new_arrival.size;
                }
            };
            finishing_time = revised_finishing_time;
            let was_absent = ejections.insert(removal);
            assert!(was_absent);
        } else {
            finishing_time = potential_finishing_time;
        }
    }
    let mut completions: Vec<Completion> = vec![];
    let mut queue: Vec<Job> = vec![];
    let mut ejection_queue: Vec<Job> = vec![];
    let mut next_arrival_index = 0;
    let mut time = 0.0;
    loop {
        enum NextEvent {
            QueueCompletion,
            EjectionCompletion,
            Arrival,
            Nothing,
        }
        let queue_event = queue
            .get(0)
            .map(|j| (time + j.rem_size, NextEvent::QueueCompletion));
        let ejection_event = ejection_queue
            .get(0)
            .map(|j| (time + j.rem_size, NextEvent::EjectionCompletion));
        let arrival_event = arrivals
            .get(next_arrival_index)
            .map(|a| (a.arrival_time, NextEvent::Arrival));
        let completion_event = queue_event.or(ejection_event);
        let arrival_event = arrival_event.unwrap_or((INFINITY, NextEvent::Nothing));
        let completion_event = completion_event.unwrap_or((INFINITY, NextEvent::Nothing));
        let event = vec![arrival_event, completion_event]
            .into_iter()
            .min_by_key(|t| n64(t.0))
            .unwrap();
        match event.1 {
            NextEvent::QueueCompletion => {
                let mut job = queue.remove(0);
                time += job.rem_size;
                job.rem_size -= job.rem_size;
                let completion = Completion::from_job(job, time);
                completions.push(completion);
            }
            NextEvent::EjectionCompletion => {
                assert!(queue.is_empty());
                let mut job = ejection_queue.remove(0);
                time += job.rem_size;
                job.rem_size -= job.rem_size;
                let completion = Completion::from_job(job, time);
                completions.push(completion);
            }
            NextEvent::Arrival => {
                let arrival = &arrivals[next_arrival_index];
                if let Some(job) = queue.get_mut(0) {
                    job.rem_size -= arrival.arrival_time - time;
                } else if let Some(job) = ejection_queue.get_mut(0) {
                    job.rem_size -= arrival.arrival_time - time;
                }
                assert!(arrival.arrival_time > time);
                time = arrival.arrival_time;
                //assert_eq!(arrival.id, next_arrival_index);
                let new_job = Job::new(arrival.size, time, next_arrival_index);
                if ejections.contains(&next_arrival_index) {
                    ejection_queue.push(new_job);
                } else {
                    queue.push(new_job);
                }
                next_arrival_index += 1;
            }
            NextEvent::Nothing => {
                assert!(queue.is_empty());
                assert!(ejection_queue.is_empty());
                assert_eq!(next_arrival_index, arrivals.len());
                assert_eq!(completions.len(), arrivals.len());
                //println!("OPT ejections: {} ({} success)", ejections.len(), (completions.len() - ejections.len()) as f64/completions.len() as f64);
                return completions;
            }
        }
    }
}

fn lower_bound(arrivals: &[Arrival], target: f64) -> f64 {
    let mut arrivals: Vec<Arrival> = arrivals.to_vec();
    arrivals.sort_by_key(|a| n64(a.arrival_time));
    let mut results: Vec<(usize, f64)> = vec![];
    let mut prior_time = 0.0;
    let mut work_in_queue = 0.0;
    let mut last_arrival_to_empty_queue = 0;
    for (i, arrival) in arrivals.iter().enumerate() {
        if i % 1000 == 0 {
            println!("{}/{}", i, arrivals.len());
        }
        let interval_length = arrival.arrival_time - prior_time;
        if interval_length > work_in_queue {
            work_in_queue = arrival.size;
            last_arrival_to_empty_queue = i;
        } else {
            work_in_queue = work_in_queue - interval_length + arrival.size;
        }
        let sim_arrivals = &arrivals[last_arrival_to_empty_queue..=i];
        let mut next_arrival_index = 0;
        let mut current_time = sim_arrivals[0].arrival_time;
        let mut queue: BTreeMap<N64, Job> = BTreeMap::new();
        while !queue.is_empty() || next_arrival_index < sim_arrivals.len() {
            let next_arrival_increment = sim_arrivals
                .get(next_arrival_index)
                .map(|a| a.arrival_time)
                .unwrap_or(INFINITY)
                - current_time;
            let next_completion_increment =
                queue.keys().next().map(|f| f.raw()).unwrap_or(INFINITY);
            if next_arrival_increment == INFINITY
                && current_time + next_completion_increment > arrival.arrival_time + target
            {
                break;
            }
            if next_arrival_increment < next_completion_increment {
                if !queue.is_empty() {
                    let min_size = *queue.keys().next().unwrap();
                    let mut min_size_job = queue.remove(&min_size).unwrap();
                    min_size_job.rem_size -= next_arrival_increment;
                    queue.insert(n64(min_size_job.rem_size), min_size_job);
                }
                current_time += next_arrival_increment;
                let new_arrival = &sim_arrivals[next_arrival_index];
                next_arrival_index += 1;
                let new_job = Job::new(new_arrival.size, current_time, next_arrival_index);
                queue.insert(n64(new_job.rem_size), new_job);
            } else {
                let min_size = *queue.keys().next().unwrap();
                queue.remove(&min_size);
                current_time += next_completion_increment;
            }
        }
        results.push((queue.len(), interval_length));
        prior_time = arrival.arrival_time;
    }
    let total_tardy: f64 = results
        .iter()
        .map(|&(num_tardy, interval_length)| num_tardy as f64 * interval_length)
        .sum();
    let total_time: f64 = results
        .iter()
        .map(|(_, interval_length)| interval_length)
        .sum();
    total_tardy / total_time
}

fn simulate(
    end_time: f64,
    rho: f64,
    size_dist: &Size,
    policy: Policy,
    seed: u64,
) -> Vec<Completion> {
    let lambda = rho / size_dist.mean();
    let mut current_time: f64 = 0.;
    let mut queue: Vec<Job> = vec![];
    let mut completions: Vec<Completion> = vec![];
    let mut scratch: HashSet<usize> = HashSet::new();
    let mut current_id = 0;

    let mut sizes: BST<N64> = BST::new();
    let mut latencies: BST<N64> = BST::new();
    let arrival_generator = Exp::new(lambda);
    let mut rng = StdRng::seed_from_u64(seed);
    let mut arrival_increment = arrival_generator.sample(&mut rng);
    while current_time < end_time || !queue.is_empty() {
        let rates = policy.rates(&queue, current_time, &sizes, &latencies, rho, &mut scratch);
        assert!(rates.len() == queue.len());
        assert!(rates.iter().sum::<f64>() < 1.0 + EPSILON);
        assert!(rates.is_empty() || rates.iter().sum::<f64>() > 1.0 - EPSILON);
        if false {
            if let Policy::MooreG(p, Ranker::FCFS, Ranker::FCFS) = policy {
                let oth_rates = (Policy::MooreFCFS(p)).rates(
                    &queue,
                    current_time,
                    &sizes,
                    &latencies,
                    rho,
                    &mut HashSet::new(),
                );
                if rates != oth_rates {
                    let time_threshold = p.eval(&latencies);
                    println!(
                        "Current time: {}, deadline: {}",
                        current_time, time_threshold
                    );
                    println!("Queue: {:?}", queue);
                    println!("MooreG: {:?}", rates);
                    println!("MooreFCFS: {:?}", oth_rates);
                    panic!()
                }
            }
        }
        let min_job_increment = queue
            .iter()
            .zip(&rates)
            .map(|(j, rate)| j.rem_size / rate)
            .min_by_key(|&f| n64(f))
            .unwrap_or(INFINITY);
        let increment = min_job_increment.min(arrival_increment);
        current_time += increment;
        arrival_increment -= increment;
        let mut to_remove = vec![];
        for (i, (job, rate)) in queue.iter_mut().zip(rates).enumerate() {
            job.rem_size -= increment * rate;
            if job.rem_size < EPSILON {
                to_remove.push(i);
            }
        }
        for removal_index in to_remove.into_iter().rev() {
            // Safe because indices processed back to front,
            // and swap_remove only affects index and later
            let job = queue.swap_remove(removal_index);
            completions.push(Completion::from_job(job, current_time));
            latencies.insert(n64(completions.last().unwrap().response_time));
        }
        if arrival_increment < EPSILON {
            arrival_increment = arrival_generator.sample(&mut rng);
            if current_time < end_time {
                let new_size = size_dist.sample(&mut rng);
                if true {
                    let work: f64 = queue.iter().map(|j| j.rem_size).sum();
                    queue.push(Job::new_with_data(
                        new_size,
                        current_time,
                        current_id,
                        work + new_size,
                    ))
                } else {
                    queue.push(Job::new(new_size, current_time, current_id));
                }
                sizes.insert(n64(new_size));
                current_id += 1;
            }
        }
    }
    /*
    if scratch.len() > 0 {
        println!("{:?} ejections: {} ({} success)", policy, scratch.len(), (completions.len() - scratch.len()) as f64/completions.len() as f64)
    }
    */
    completions
}

/*
fn single_percentile() {
    let percentile = 0.99;
    let seed = 0;
    let time = 1e6;
    let policies = vec![
        Policy::FCFS,
        Policy::SRPT,
        Policy::FB,
        Policy::DelayLarge(percentile),
        Policy::DelayLargeOrOld(percentile, percentile),
        Policy::DelayLargeOrOld(percentile, percentile + (1.0 - percentile) * 0.25),
        Policy::DelayLargeOrOld(percentile, percentile + (1.0 - percentile) * 0.5),
        Policy::DelayLargeOrOld(percentile, percentile + (1.0 - percentile) * 0.75),
        Policy::DelayLargeOrOld(percentile, 1.0),
        Policy::DynamicLargeOrOld(percentile),
        Policy::MooreSRPT(percentile),
        Policy::MooreFCFS(percentile),
    ];
    println!("per={},seed={},time={}", percentile, seed, time);
    println!(
        "policies: {}",
        policies
            .iter()
            .map(|p| format!("{:?}", p))
            .collect::<Vec<String>>()
            .join(" ")
    );
    for rho in vec![0.3, 0.5, 0.7, 0.9, 0.99] {
        for var in vec![1.0, 2.0, 4.0, 10.0] {
            let dist = Size::balanced_hyper(var);
            println!("     rho={},var={}", rho, var);
            let mut results = vec![];
            for &p in &policies {
                let mut completions = simulate(time, rho, &dist, p, seed);
                completions.sort_by_key(|c| n64(c.response_time));
                let index = (completions.len() as f64 * percentile) as usize;
                results.push(completions[index].response_time);
            }
            println!(
                "     {}",
                results
                    .iter()
                    .map(|f| format!("{}", f))
                    .collect::<Vec<String>>()
                    .join(",")
            );
            let (best_time, best_policy) = results
                .iter()
                .zip(&policies)
                .min_by_key(|(r, _)| n64(**r))
                .unwrap();
            println!("{:?} {}", best_policy, best_time);
        }
    }
}
*/

fn many_rhos() {
    let seed = 0;
    let time = 1e6;
    let targets: Vec<Target> = vec![Target::Time(1000.0)];

    let print_percentiles = false;
    for &target in &targets {
        println!("target={:?}, seed={}, time={}", target, seed, time);
        let policies = vec![
            Policy::Ejector(target),
            Policy::MooreG(target, Ranker::FCFS, Ranker::SRPT),
            Policy::DelayLarge(0.9999),
            Policy::FCFS,
            Policy::SRPT,
            Policy::SmallestLateSimple(target),
            //Policy::SmallestLate(target),
            //Policy::OldestUnexchangableMulti(target),
        ];
        let rhos = vec![0.99];
        let vars = vec![4.0];
        let fidelity = 100;
        let percentiles: Vec<f64> = (0..fidelity)
            .map(|f| 0.99 + f64::from(f) * (0.01 / f64::from(fidelity)))
            .collect();
        for rho in rhos {
            for &var in &vars {
                let dist = Size::balanced_hyper(var);
                //let dist = Size::Bimodal(1.0, var, 0.995);
                println!("rho={},var={},mean={}", rho, var, dist.mean());
                if print_percentiles {
                    println!(
                        ",{}",
                        percentiles
                            .iter()
                            .map(|f| format!("{:.4}", f))
                            .collect::<Vec<String>>()
                            .join(",")
                    );
                }
                let mut completionss: Vec<Vec<Completion>> = policies
                    .iter()
                    .map(|p| simulate(time, rho, &dist, *p, seed))
                    .collect();
                let mut policy_names: Vec<String> =
                    policies.iter().map(|p| format!("{:?}", p)).collect();
                if false {
                    if let Target::Time(t) = target {
                        let arrivals = completionss
                            .get(0)
                            .expect("At least one policy")
                            .iter()
                            .map(|c| Arrival::from_completion(c))
                            .collect();
                        let opt_completions = opt(arrivals, t);
                        completionss.push(opt_completions);
                        policy_names.push("OPT_FCFS".to_string());
                    }
                }
                completionss
                    .iter_mut()
                    .for_each(|completions| completions.sort_by_key(|c| n64(c.response_time)));
                for (completions, p) in completionss.iter().zip(&policy_names) {
                    let mut results = vec![];
                    for &percentile in &percentiles {
                        let index = (completions.len() as f64 * percentile) as usize;
                        results.push(completions[index].response_time);
                    }
                    if print_percentiles {
                        println!(
                            "'{}',{}",
                            p,
                            results
                                .iter()
                                .map(|f| f.to_string())
                                .collect::<Vec<String>>()
                                .join(",")
                        );
                    }
                }
                if let Target::Time(t) = target {
                    let mean_metric = true;
                    let fraction_metric = false;
                    if fraction_metric {
                        println!("Fraction on time");
                        for (completions, p) in completionss.iter().zip(&policy_names) {
                            let index = match completions
                                .binary_search_by_key(&n64(t), |c| n64(c.response_time))
                            {
                                Ok(i) => i,
                                Err(i) => i,
                            };
                            println!("'{}',{}", p, index as f64 / completions.len() as f64);
                        }
                    }
                    if mean_metric {
                        println!("Mean tardiness");
                        for (completions, p) in completionss.iter().zip(&policy_names) {
                            let total_tardiness: f64 = completions
                                .iter()
                                .map(|c| (c.response_time - t).max(0.0))
                                .sum();
                            println!("'{}',{}", p, total_tardiness / completions.len() as f64);
                            if p == "SRPT" {
                                let bound_tardiness: f64 = completions
                                    .iter()
                                    .map(|c| {
                                        if c.data.unwrap() <= t {
                                            0.0
                                        } else {
                                            c.response_time
                                        }
                                    })
                                    .sum();
                                println!(
                                    "'SRPT based bound',{}",
                                    bound_tardiness / completions.len() as f64
                                );
                            }
                        }
                        if false {
                            let arrivals: Vec<Arrival> = completionss
                                .get(0)
                                .expect("At least one policy")
                                .iter()
                                .map(Arrival::from_completion)
                                .collect();
                            let opt_tardiness = lower_bound(&arrivals, t);
                            println!("'Lower bound',{}", opt_tardiness);
                        }
                    }
                }
                if let Target::Percentile(perc) = target {
                    println!("policy,min,mean");
                    for (completions, policy) in completionss.iter().zip(&policy_names) {
                        let index = ((completions.len() as f64) * perc) as usize;
                        let above = &completions[index..];
                        let sum_above: f64 = above.iter().map(|c| c.response_time).sum();
                        println!(
                            "'{}',{},{}",
                            policy,
                            above[0].response_time,
                            sum_above / above.len() as f64
                        );
                        if policy == "SRPT" {
                            let mut bound_tardiness: Vec<f64> = completions
                                .iter()
                                .map(|c| {
                                    if c.data.unwrap() <= 100.0 {
                                        0.0
                                    } else {
                                        c.response_time + 100.0
                                    }
                                })
                                .collect();
                            bound_tardiness.sort_by_key(|&f| n64(f));
                            let above = &bound_tardiness[index..];
                            let sum_above: f64 = above.iter().sum();
                            println!(
                                "'SRPT based bound',{},{}",
                                above[0],
                                sum_above / above.len() as f64
                            );
                        }
                    }
                }
            }
        }
    }
}

fn ratio() {
    let time = 1e6;
    let seed = 0;
    let target = 640.0;
    let rho = 0.995;
    let high = 16.0;
    let prob = 0.995;
    let dist = Size::Bimodal(1.0, high, prob);
    let policies = vec![
        Policy::Ejector(Target::Time(target)),
        Policy::MooreG(Target::Time(target), Ranker::SRPT, Ranker::SRPT),
    ];
    let results: Vec<f64> = policies
        .into_iter()
        .map(|p| {
            let mut completions = simulate(time, rho, &dist, p, seed);
            completions.sort_by_key(|c| n64(c.response_time));
            let index =
                match completions.binary_search_by_key(&n64(target), |c| n64(c.response_time)) {
                    Ok(i) => i,
                    Err(i) => i,
                };
            1.0 - index as f64 / completions.len() as f64
        })
        .collect();
    println!(
        "Moore: {}, Ejector: {} - {} {} {} {}",
        results[1], results[0], target, rho, high, prob
    );
}
fn main() {
    many_rhos();
}

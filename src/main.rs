extern crate rand;
use rand::distributions::{Distribution, Exp};
use rand::prelude::*;
use rand::Rng;
use rand::SeedableRng;

extern crate noisy_float;
use noisy_float::prelude::*;

use std::f64::INFINITY;

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
                    data: data,
                    left: Self::new(),
                    right: Self::new(),
                };
                *self = BST::Full(Box::new(new));
            }
            BST::Full(b) => {
                if data < b.data {
                    b.size += 1;
                    b.left.insert(data);
                } else if data > b.data {
                    b.size += 1;
                    b.right.insert(data);
                }
                // If equal, drop
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

struct Job {
    size: f64,
    rem_size: f64,
    arrival_time: f64,
}

impl Job {
    fn new(size: f64, time: f64) -> Self {
        Self {
            size,
            rem_size: size,
            arrival_time: time,
        }
    }
}

#[derive(Debug)]
struct Completion {
    size: f64,
    response_time: f64,
}

impl Completion {
    fn from_job(job: Job, time: f64) -> Self {
        assert!(job.rem_size <= EPSILON);
        Self {
            size: job.size,
            response_time: time - job.arrival_time,
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
    Threshold(f64),
    DelayLarge(f64),
    DelayLargeOrOld(f64, f64),
    DynamicLargeOrOld(f64),
}

impl Policy {
    // More imputs in future
    fn rates(
        &self,
        queue: &Vec<Job>,
        current_time: f64,
        sizes: &BST<N64>,
        latencies: &BST<N64>,
    ) -> Vec<f64> {
        match &self {
            Policy::SRPT
            | Policy::FCFS
            | Policy::TRR
            | Policy::FB
            | Policy::Threshold(_)
            | Policy::DelayLarge(_)
            | Policy::DelayLargeOrOld(_, _) => {
                let best = queue.iter().enumerate().min_by_key(|(_i, job)| {
                    n64(match &self {
                        Policy::SRPT => job.rem_size,
                        Policy::FCFS => job.arrival_time,
                        Policy::TRR => job.rem_size / (current_time - job.arrival_time),
                        // Approximate FB
                        Policy::FB => job.size - job.rem_size,
                        Policy::Threshold(t) => {
                            if current_time - job.arrival_time > *t {
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
                        Policy::DelayLargeOrOld(time_p, size_p) => {
                            let size_index = (sizes.len() as f64 * size_p) as usize;
                            let size_threshold =
                                sizes.nth(size_index).cloned().unwrap_or(n64(INFINITY));
                            let time_index = (latencies.len() as f64 * time_p) as usize;
                            let time_threshold =
                                latencies.nth(time_index).cloned().unwrap_or(n64(INFINITY));
                            if n64(current_time - job.arrival_time + job.rem_size) > time_threshold
                            {
                                current_time * 2.0 + job.rem_size
                            } else if n64(job.size) > size_threshold {
                                current_time + job.rem_size
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
            Policy::DynamicLargeOrOld(p) => {
                let time_index = (latencies.len() as f64 * p) as usize;
                let time_threshold = latencies.nth(time_index).cloned().unwrap_or(n64(INFINITY));
                let mut size_queue: Vec<&Job> = queue.iter().collect();
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
                        } else if job.rem_size > size_threshold {
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
        }
    }
}

#[derive(Clone, Debug)]
enum Size {
    Exp(f64),
    Pareto(f64),
    Hyper(f64, f64, f64),
    Det(f64),
}

impl Distribution<f64> for Size {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> f64 {
        match self {
            &Size::Exp(lambda) => {
                let dist = Exp::new(lambda);
                dist.sample(rng)
            }
            &Size::Pareto(alpha) => rng.gen_range(0., 1.).powf(-1. / alpha),
            &Size::Hyper(low, high, low_prob) => {
                let mean = if rng.gen_range(0., 1.) < low_prob {
                    low
                } else {
                    high
                };
                let dist = Exp::new(1.0 / mean);
                dist.sample(rng)
            }
            &Size::Det(x) => x,
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
        match self {
            &Size::Exp(lambda) => 1.0 / lambda,
            &Size::Pareto(alpha) => alpha / (alpha - 1.0),
            &Size::Hyper(low, high, low_prob) => low * low_prob + high * (1.0 - low_prob),
            &Size::Det(x) => x,
        }
    }
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

    let mut sizes: BST<N64> = BST::new();
    let mut latencies: BST<N64> = BST::new();

    let arrival_generator = Exp::new(lambda);
    let mut rng = StdRng::seed_from_u64(seed);
    let mut arrival_increment = arrival_generator.sample(&mut rng);
    while current_time < end_time {
        let rates = policy.rates(&queue, current_time, &sizes, &latencies);
        assert!(rates.len() == queue.len());
        assert!(rates.iter().sum::<f64>() < 1.0 + EPSILON);
        assert!(rates.is_empty() || rates.iter().sum::<f64>() > 1.0 - EPSILON);
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
            let new_size = size_dist.sample(&mut rng);
            queue.push(Job::new(new_size, current_time));
            arrival_increment = arrival_generator.sample(&mut rng);
            sizes.insert(n64(new_size));
        }
    }
    completions
}

fn main() {
    let percentile = 0.99;
    let seed = 0;
    let time = 1e6;
    let policies = vec![
        Policy::FCFS,
        Policy::PS,
        Policy::SRPT,
        Policy::FB,
        Policy::DelayLarge(percentile),
        Policy::DelayLargeOrOld(percentile, percentile),
        Policy::DelayLargeOrOld(percentile, percentile + (1.0 - percentile) * 0.25),
        Policy::DelayLargeOrOld(percentile, percentile + (1.0 - percentile) * 0.5),
        Policy::DelayLargeOrOld(percentile, percentile + (1.0 - percentile) * 0.75),
        Policy::DelayLargeOrOld(percentile, 1.0),
        Policy::DynamicLargeOrOld(percentile),
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

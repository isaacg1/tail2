extern crate rand;
use rand::distributions::{Distribution, Exp};
use rand::prelude::*;
use rand::SeedableRng;
use rand::Rng;

extern crate noisy_float;
use noisy_float::prelude::*;

use std::f64::INFINITY;

const EPSILON: f64 = 1e-10;

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
}

impl Policy {
    // More imputs in future
    fn rates(&self, queue: &Vec<Job>) -> Vec<f64> {
        match &self {
            Policy::SRPT | Policy::FCFS => {
                let best = queue.iter().enumerate().min_by_key(|(_i, job)| {
                    n64(
                    match &self {
                        Policy::SRPT => job.rem_size,
                        Policy::FCFS => job.arrival_time,
                        Policy::PS => unreachable!(),
                    })});
                let mut out = vec![0.0; queue.len()];
                if let Some(best) = best {
                    out[best.0] = 1.0;
                }
                out
            }
            Policy::PS => {
                vec![1.0/queue.len() as f64; queue.len()]
            }
        }
    }
}

#[derive(Clone, Debug)]
enum Size {
    Exp(f64),
    Pareto(f64),
    Hyper(f64, f64, f64),
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
        }
    }
}

impl Size {
    fn balanced_hyper(covariance: f64) -> Self {
        let high = 2.0 * covariance + 1.0;
        Size::Hyper(1.0, high, high / (high + 1.0))
    }
    fn mean(&self) -> f64 {
        match self {
            &Size::Exp(lambda) => 1.0 / lambda,
            &Size::Pareto(alpha) => alpha / (alpha - 1.0),
            &Size::Hyper(low, high, low_prob) => low * low_prob + high * (1.0 - low_prob),
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
    let lambda = rho/size_dist.mean();
    let mut current_time: f64 = 0.;
    let mut queue: Vec<Job> = vec![];
    let mut completions: Vec<Completion> = vec![];

    let arrival_generator = Exp::new(lambda);
    let mut rng = StdRng::seed_from_u64(seed);
    let mut arrival_increment = arrival_generator.sample(&mut rng);
    while current_time < end_time {
        let rates = policy.rates(&queue);
        assert!(rates.len() == queue.len());
        assert!(rates.iter().sum::<f64>() < 1.0 + EPSILON);
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
        }
        if arrival_increment < EPSILON {
            let new_size = size_dist.sample(&mut rng);
            queue.push(Job::new(new_size, current_time));
            arrival_increment = arrival_generator.sample(&mut rng);
        }
    }
    completions
}

fn main() {
    let dist = Size::balanced_hyper(5.0);
    for p in vec![Policy::FCFS, Policy::SRPT, Policy::PS] {
        let mut completions = simulate(1e6, 0.99, &dist, p, 0);
        completions.sort_by_key(|c| n64(c.response_time));
        println!("{:?}", p);
        let cap = (completions.len() as f64).log(2.0).floor() as usize;
        for k in 1..= cap {
            let fraction = (0.5).powi(k as i32);
            let number = (completions.len() as f64 * fraction).floor() as usize;
            let job = &completions[completions.len() - number];
            println!("{}", job.response_time);
        }
    }
}

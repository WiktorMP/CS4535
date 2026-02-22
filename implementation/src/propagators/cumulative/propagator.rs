use std::collections::HashMap;
use std::marker::PhantomData;

use pumpkin_core::conjunction;
use pumpkin_core::declare_inference_label;
use pumpkin_core::predicate;
use pumpkin_core::predicates::PropositionalConjunction;
use pumpkin_core::proof::ConstraintTag;
use pumpkin_core::proof::InferenceCode;
use pumpkin_core::propagation::InferenceCheckers;
use pumpkin_core::propagation::LocalId;
use pumpkin_core::propagation::Priority;
use pumpkin_core::propagation::PropagationContext;
use pumpkin_core::propagation::Propagator;
use pumpkin_core::propagation::PropagatorConstructor;
use pumpkin_core::propagation::PropagatorConstructorContext;
use pumpkin_core::propagation::DomainEvents;
#[allow(unused, reason = "Will be used in the assignments")]
use pumpkin_core::propagation::ReadDomains;
use pumpkin_core::results::PropagationStatusCP;
use pumpkin_core::state::Conflict;
use pumpkin_core::state::PropagatorConflict;
use pumpkin_core::variables::IntegerVariable;

use crate::propagators::cumulative::CumulativeChecker;

declare_inference_label!(TimeTable);

#[derive(Clone, Debug)]
pub struct CumulativeConstructor<Var> {
    pub tasks: Box<[Task<Var>]>,
    pub capacity: u32,
    pub constraint_tag: ConstraintTag,
    pub conflict_detection_only: bool,
}

#[derive(Clone, Debug)]
pub struct Task<Var> {
    pub start_time: Var,
    pub duration: u32,
    pub resource_usage: u32,
}

impl<Var> PropagatorConstructor for CumulativeConstructor<Var>
where
    Var: IntegerVariable + 'static,
{
    type PropagatorImpl = CumulativeTimeTablePropagator<Var>;

    fn create(self, mut context: PropagatorConstructorContext) -> Self::PropagatorImpl {
        // Register for events
        let CumulativeConstructor {
            tasks,
            capacity,
            constraint_tag,
            conflict_detection_only,
        } = self;

        for (i, task) in tasks.iter().enumerate() {
            let i   = i.try_into().expect("error converting");
            context.register(task.start_time.clone(), DomainEvents::ANY_INT, LocalId::from(i));
        };

        CumulativeTimeTablePropagator {
            tasks: tasks.to_vec(),
            capacity: capacity,
            conflict_detection_only: self.conflict_detection_only,
            _inference_code: InferenceCode::new(self.constraint_tag, TimeTable),
            phantom_data: PhantomData,
        }
    }

    fn add_inference_checkers(&self, mut checkers: InferenceCheckers<'_>) {
        checkers.add_inference_checker(
            InferenceCode::new(self.constraint_tag, TimeTable),
            Box::new(CumulativeChecker {
                tasks: self.tasks.to_vec(),
                capacity: self.capacity,
            }),
        );
    }
}

/// Propagator for the Cumulative constraint using time-tabling.
#[derive(Clone, Debug)]
pub struct CumulativeTimeTablePropagator<Var> {
    tasks: Vec<Task<Var>>,
    capacity: u32,
    conflict_detection_only: bool,
    _inference_code: InferenceCode,
    /// Here to avoid build warnings
    phantom_data: PhantomData<Var>,
}

impl<Var: 'static> Propagator for CumulativeTimeTablePropagator<Var>
where
    Var: IntegerVariable,
{
    fn priority(&self) -> Priority {
        Priority::Low
    }

    fn name(&self) -> &str {
        "CumulativeTimeTable"
    }

    fn propagate_from_scratch(&self, mut context: PropagationContext) -> PropagationStatusCP {

        let mut max_end_time = 0;
        // map form task index to compulsory times
        let mut compulsory_map: HashMap<i32, Vec<i32>> = HashMap::new();

        for (i, t) in self.tasks.iter().enumerate(){


            let ub = context.upper_bound(&t.start_time);
            let lb = context.lower_bound(&t.start_time);

            println!("Task {}: start_time_lb {}, start_time_ub {}, duration {}, resource_usage {}", i, lb, ub, t.duration, t.resource_usage);
            if (ub + t.duration as i32) > max_end_time{
                max_end_time = ub + t.duration as i32;
            };

            let min_end = lb + t.duration as i32 - 1;
            compulsory_map.insert(i as i32,Vec::default());
            if ub <= min_end{
                for compulsory in ub..=min_end{
                    compulsory_map
                        .entry(i as i32)
                        .or_default()
                        .push(compulsory);
                    
                }
            }
        };

        println!("Compulsory map: {:?}", compulsory_map);

        let mut resource_profile: Vec<i32> = vec![0; (max_end_time+1).try_into().unwrap()];

        for (i, t) in self.tasks.iter().enumerate(){
            println!("Task {}: start_time_lb {:?}, start_time_ub {:?}, duration {}, resource_usage {}", i, context.lower_bound(&t.start_time), context.upper_bound(&t.start_time), t.duration, t.resource_usage);
            for v in compulsory_map[&(i as i32)].clone().iter(){
                
                let new_resource_usage = resource_profile[*v as usize] + t.resource_usage as i32;
                resource_profile[*v as usize] = new_resource_usage;
                
            }
        }

        println!("capacity: {}", self.capacity);
        println!("Resource profile: {:?}", resource_profile);
        
        for (time, usage) in resource_profile.iter().enumerate(){
            // find task at the violating time
            if usage >&(self.capacity as i32){
                let mut explanation = Vec::new();
                // find tasks at the violating time
                for (i, task) in self.tasks.iter().enumerate(){
                    // check if the task is compulsory at this time
                    if compulsory_map[&(i as i32)].contains(&(time as i32)){
                        explanation.push(predicate!(task.start_time >= context.lower_bound(&task.start_time)));
                        explanation.push(predicate!(task.start_time <= context.upper_bound(&task.start_time)));
                    }
                }
                return Err(Conflict::Propagator(PropagatorConflict{
                conjunction: PropositionalConjunction::from(explanation.clone()),
                inference_code: self._inference_code.clone(),
                }));
            }
        }
        
        if self.conflict_detection_only {
            // TODO: Only perform conflict detection
            // check if resource profile bigger

            #[allow(
                unreachable_code,
                reason = "Should not be a warning after implementing"
            )]
            return Ok(())
        }

        for (i, t) in self.tasks.iter().enumerate(){
            let lb = context.lower_bound(&t.start_time);
            let ub = context.upper_bound(&t.start_time);

            // delete values from resource_profile not to double count them
            let mut temp_resource_profile = resource_profile.clone();

            for v in compulsory_map[&(i as i32)].iter(){
                temp_resource_profile[*v as usize] -= t.resource_usage as i32;
            }

            for s in lb..=ub{
                let end_time = s + t.duration as i32;
                // for all timesteps check if enough resource available
                for j in s..end_time{            
                    // could do a reverse of hash for easier explanation generation
                    if temp_resource_profile[j as usize] + t.resource_usage as i32 > self.capacity as i32{
                        let mut explanation = Vec::new();
                        // find tasks at the violating time
                        for (task_id, task) in self.tasks.iter().enumerate(){
                            // check if the task is compulsory at this time
                            if compulsory_map[&(task_id as i32)].contains(&(j as i32)){
                                explanation.push(predicate!(task.start_time >= context.lower_bound(&task.start_time)));
                                explanation.push(predicate!(task.start_time <= context.upper_bound(&task.start_time)));
                            }
                        }
                        explanation.push(predicate!(t.start_time >= s-1));
                        explanation.push(predicate!(t.start_time <= s+1));
                        println!("Explanation: {:?}", explanation);
                        context.post(
                            predicate!(t.start_time != s),
                             PropositionalConjunction::from(explanation),
                            &self._inference_code
                        )?;
                        break;
                    }
                }
            }
        }
        Ok(())
    }
}

#[allow(deprecated, reason = "Will be refactored")]
#[cfg(test)]
mod tests {
    use core::task;

    use pumpkin_core::{Solver, TestSolver};

    use crate::propagators::cumulative::CumulativeConstructor;
    use crate::propagators::cumulative::Task;

    #[test]
    fn base_test() {
        let mut solver = TestSolver::default();
        let t1_start = solver.new_variable(0, 2);
        let t2_start = solver.new_variable(1, 4);

        let t1 = Task {
                start_time: t1_start,
                duration: 4,
                resource_usage: 1,
            };
        let t2 = Task {
                start_time: t2_start,
                duration: 2,
                resource_usage: 1,
            };

        let tasks = vec![t1, t2].into_boxed_slice();

        let capacity = 1;
        let constraint_tag = solver.new_constraint_tag();
        let result = solver.new_propagator(CumulativeConstructor {
            tasks: tasks,
            capacity,
            constraint_tag,
            conflict_detection_only: false,
        });

        assert!(result.is_ok());
        solver.assert_bounds(t1_start, 0, 0);
        solver.assert_bounds(t2_start, 4, 4);
    }

    #[test]
    fn negative_resource_overuse_test() {
        let mut solver = TestSolver::default();
        let t1_start = solver.new_variable(0, 2);
        let t2_start = solver.new_variable(1, 4);

        let t1 = Task {
                start_time: t1_start,
                duration: 4,
                resource_usage: 1,
            };
        let t2 = Task {
                start_time: t2_start,
                duration: 2,
                resource_usage: 3,
            };

        let tasks = vec![t1, t2].into_boxed_slice();

        let capacity = 1;
        let constraint_tag = solver.new_constraint_tag();
        let result = solver.new_propagator(CumulativeConstructor {
            tasks: tasks,
            capacity,
            constraint_tag,
            conflict_detection_only: false,
        });

        assert!(!result.is_ok());
    }

    #[test]
    fn base_overlap_test() {
        let mut solver = TestSolver::default();
        let t1_start = solver.new_variable(0, 2);
        let t2_start = solver.new_variable(1, 3);

        let t1 = Task {
                start_time: t1_start,
                duration: 4,
                resource_usage: 1,
            };
        let t2 = Task {
                start_time: t2_start,
                duration: 2,
                resource_usage: 1,
            };

        let tasks = vec![t1, t2].into_boxed_slice();

        let capacity = 1;
        let constraint_tag = solver.new_constraint_tag();
        let result = solver.new_propagator(CumulativeConstructor {
            tasks: tasks,
            capacity,
            constraint_tag,
            conflict_detection_only: false,
        });

        assert!(!result.is_ok());
    }

    #[test]
    fn no_change_test() {
        let mut solver = TestSolver::default();
        let t1_start = solver.new_variable(42, 161);
        let t2_start = solver.new_variable(36, 42);

        let t1 = Task {
                start_time: t1_start,
                duration: 4,
                resource_usage: 1,
            };
        let t2 = Task {
                start_time: t2_start,
                duration: 2,
                resource_usage: 1,
            };

        let tasks = vec![t1, t2].into_boxed_slice();

        let capacity = 1;
        let constraint_tag = solver.new_constraint_tag();
        let result = solver.new_propagator(CumulativeConstructor {
            tasks: tasks,
            capacity,
            constraint_tag,
            conflict_detection_only: false,
        });

        assert!(result.is_ok());
        solver.assert_bounds(t1_start, 42, 161);
        solver.assert_bounds(t2_start, 36, 42);
    }
}

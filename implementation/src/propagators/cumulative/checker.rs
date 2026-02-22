use std::collections::HashMap;
use pumpkin_checking::IntExt;
use pumpkin_checking::AtomicConstraint;
use pumpkin_checking::CheckerVariable;
use pumpkin_checking::InferenceChecker;

use crate::propagators::cumulative::Task;

#[derive(Debug, Clone)]
pub struct CumulativeChecker<Var> {
    pub tasks: Vec<Task<Var>>,
    pub capacity: u32,
}

impl<Atomic: AtomicConstraint, Var: CheckerVariable<Atomic>> InferenceChecker<Atomic>
    for CumulativeChecker<Var>
{
    fn check(
        &self,
        mut state: pumpkin_checking::VariableState<Atomic>,
        _premises: &[Atomic],
        _consequent: Option<&Atomic>,
    ) -> bool {
        let mut consistent = true;
        let mut max_end_time = 0;
        let mut valid_task_ids = Vec::new();
        // map form task index to compulsory times
        let mut compulsory_map: HashMap<i32, Vec<i32>> = HashMap::new();
        for t in self.tasks.iter() {
            let v = &t.start_time;
            println!("{:?},{:?}, {:?}", v, v.induced_lower_bound(&state), v.induced_upper_bound(&state));
        }

        for (i, t) in self.tasks.iter().enumerate(){

            if let IntExt::Int(ub) = t.start_time.induced_upper_bound(&state) && 
            let IntExt::Int(lb) = t.start_time.induced_lower_bound(&state)
            {   
                valid_task_ids.push(i as i32);
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
            }
        };

        println!("Compulsory map: {:?}", compulsory_map);

        let mut resource_profile: Vec<i32> = vec![0; (max_end_time+1).try_into().unwrap()];

        for i in valid_task_ids{
            let t = &self.tasks[i as usize];
            for v in compulsory_map[&i].clone().iter(){
                
                let new_resource_usage = resource_profile[*v as usize] + t.resource_usage as i32;
                resource_profile[*v as usize] = new_resource_usage;
                
            }
        }
        
        println!("capacity: {}", self.capacity);
        println!("Resource profile: {:?}", resource_profile);
        // Check if any time step exceeds capacity
        for (time, usage) in resource_profile.iter().enumerate(){
            if *usage > self.capacity as i32{
                consistent = false;
                break;
            }
        }
        
        !consistent
    }
}

use pumpkin_checking::AtomicConstraint;
use pumpkin_checking::CheckerVariable;
use pumpkin_checking::InferenceChecker;
use pumpkin_checking::IntExt;

#[derive(Debug, Clone)]
pub struct LinearChecker<Var> {
    pub x: Vec<Var>,
    pub bound: i32,
}

impl<Atomic: AtomicConstraint, Var: CheckerVariable<Atomic>> InferenceChecker<Atomic>
    for LinearChecker<Var>
{
    fn check(
        &self,
        mut state: pumpkin_checking::VariableState<Atomic>,
        _premises: &[Atomic],
        _consequent: Option<&Atomic>,
    ) -> bool {
        //println!("bound: {}",  self.bound);
        for v in self.x.iter() {
            //println!("{:?},{:?}, {:?}", v, v.induced_lower_bound(&state), v.induced_upper_bound(&state));
        }
        let mut consistent = true;

        let mut total= 0;
        let mut ninf_flag = false;

        for v in self.x.iter() {
            if let IntExt::Int(v_lb) = v.induced_lower_bound(&state) {
                total += v_lb;
            } else if let IntExt::NegativeInf = v.induced_lower_bound(&state){
                //println!("Variable {:?} has negative infinity as lower bound, skipping consistency check", v);
                ninf_flag = true;
                consistent = true;
                break;  
            } 
        }

        if (total > self.bound) && !ninf_flag {
            consistent = false;
        }
        //println!("total: {}, consistent: {}", total, consistent);
        !consistent
    }
}

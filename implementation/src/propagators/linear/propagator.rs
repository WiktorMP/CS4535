use std::marker::PhantomData;

use pumpkin_core::conjunction;
use pumpkin_core::declare_inference_label;
use pumpkin_core::predicate;
use pumpkin_core::predicates::PropositionalConjunction;
use pumpkin_core::proof::ConstraintTag;
use pumpkin_core::proof::InferenceCode;
use pumpkin_core::propagation::DomainEvents;
use pumpkin_core::propagation::InferenceCheckers;
use pumpkin_core::propagation::LocalId;
use pumpkin_core::propagation::Priority;
use pumpkin_core::propagation::PropagationContext;
use pumpkin_core::propagation::Propagator;
use pumpkin_core::containers::HashSet;
use pumpkin_core::propagation::PropagatorConstructor;
use pumpkin_core::propagation::PropagatorConstructorContext;
#[allow(unused, reason = "Will be used in the assignments")]
use pumpkin_core::propagation::ReadDomains;
use pumpkin_core::results::PropagationStatusCP;
use pumpkin_core::state::Conflict;
use pumpkin_core::state::PropagatorConflict;
use pumpkin_core::variables::IntegerVariable;

use crate::propagators::linear::LinearChecker;

declare_inference_label!(LinearBounds);

#[derive(Clone, Debug)]
pub struct LinearConstructor<Var> {
    pub x: Box<[Var]>,
    pub bound: i32,
    pub constraint_tag: ConstraintTag,
    pub conflict_detection_only: bool,
}

impl<Var> PropagatorConstructor for LinearConstructor<Var>
where
    Var: IntegerVariable + 'static,
{
    type PropagatorImpl = LinearLessOrEqualPropagator<Var>;

    fn create(self, mut context: PropagatorConstructorContext) -> Self::PropagatorImpl {
        // Register for events
        
        let LinearConstructor{
            x, 
            bound,
            constraint_tag,
            conflict_detection_only,
        } = self;
        
        for (i, v )in x.iter().enumerate(){
            let i   = i.try_into().expect("error converting");
            context.register(v.clone(), DomainEvents::ANY_INT, LocalId::from(i));
        }

        LinearLessOrEqualPropagator {
            x: x.to_vec(),
            bound: bound,
            conflict_detection_only: conflict_detection_only,
            _inference_code: InferenceCode::new(constraint_tag, LinearBounds),
            phantom_data: PhantomData,
        }
    }

    fn add_inference_checkers(&self, mut checkers: InferenceCheckers<'_>) {
        checkers.add_inference_checker(
            InferenceCode::new(self.constraint_tag, LinearBounds),
            Box::new(LinearChecker {
                x: self.x.to_vec(),
                bound: self.bound,
            }),
        );
    }
}

/// Propagator for the constraint `\sum x_i <= c`.
#[derive(Clone, Debug)]
pub struct LinearLessOrEqualPropagator<Var> {
    x: Vec<Var>,
    bound: i32,
    conflict_detection_only: bool,
    _inference_code: InferenceCode,
    /// Here to avoid build warnings
    phantom_data: PhantomData<Var>,
}

impl<Var: 'static> Propagator for LinearLessOrEqualPropagator<Var>
where
    Var: IntegerVariable,
{
    fn priority(&self) -> Priority {
        Priority::High
    }

    fn name(&self) -> &str {
        "LinearLeq"
    }

    fn propagate_from_scratch(&self, mut context: PropagationContext) -> PropagationStatusCP {

        let mut total = 0; 
        let mut explanation = Vec::new();
        //println!("Propagating LinearLessOrEqualPropagator with bound: {}", self.bound);
        for v in self.x.iter(){
            //println!("Variable: {:?}, lb: {}, ub: {}", v, context.lower_bound(v), context.upper_bound(v));
            //println!("{}",predicate![v >= context.lower_bound(v)]);
            total += context.lower_bound(v);
            explanation.push(predicate![v >= context.lower_bound(v)]);
        }

        if total > self.bound {
            //explanation.push(predicate!(total >= self.bound+1));
            return Err(Conflict::Propagator(PropagatorConflict{
                conjunction: PropositionalConjunction::from(explanation.clone()),
                inference_code: self._inference_code.clone(),
            }));
        }

        if self.conflict_detection_only {
            // TODO: Only perform conflict detection

            #[allow(
                unreachable_code,
                reason = "Should not be a warning after implementing"
            )]
            return Ok(());
        }
        
        /* for each contibuting v the upper bound can only be as big as the 
        b - (total - lower_bound(v)) */

        for v in self.x.iter(){
            let v_lb = context.lower_bound(v);
            let v_ub = context.upper_bound(v);
            // get the max upper bound that ensures with others optimistic result valid
            let max_ub = self.bound - (total - v_lb);
            //println!("Variable: {:?}, lb: {}, ub: {}, max_ub: {}", v, v_lb, v_ub, max_ub);
            // to not do updates that make no sense
            if max_ub < v_ub{
                // not to recalculate the explanation allow redundant predicate a_k >= a_k_lb for explanation of a_k <= max_ub
                //println!("Updating upper bound of variable {:?} from {} to {}", v, v_ub, max_ub);
                let mut new_explanation = explanation.clone();
                new_explanation.push(predicate![v >= max_ub]);
                //println!("Explanation for updating: {:?}",  new_explanation);
                context.post(
                    predicate![v <= max_ub],
                     PropositionalConjunction::from(new_explanation),
                     &self._inference_code
                )?;
            }
        }

        return Ok(());
        //todo!()
    }
}

#[allow(deprecated, reason = "Will be refactored")]
#[cfg(test)]
mod tests {
    use std::result;

    use pumpkin_core::{TestSolver, constraints};

    use crate::propagators::linear::LinearConstructor;

    #[test]
    fn base_test() {
        let mut solver = TestSolver::default();
        let v1 = solver.new_variable(2, 5);
        let v2 = solver.new_variable(1, 6);
        let v = vec![v1, v2];
        let x = v.into_boxed_slice();
        let b = 5;
        let constraint_tag = solver.new_constraint_tag();

        let result = solver.new_propagator(LinearConstructor{
            x,
            bound: b,
            constraint_tag,
            conflict_detection_only: false,
        });

        assert!(result.is_ok());

        solver.assert_bounds(v1,2, 4);
        solver.assert_bounds(v2,1, 3);

    }

    #[test]
    fn negative_base_test() {
        let mut solver = TestSolver::default();
        let v1 = solver.new_variable(-5, 2);
        let v2 = solver.new_variable(-3, 3);
        let v = vec![v1, v2];
        let x = v.into_boxed_slice();
        let b = -6;
        let constraint_tag = solver.new_constraint_tag();

        let result = solver.new_propagator(LinearConstructor{
            x,
            bound: b,
            constraint_tag,
            conflict_detection_only: false,
        });

        assert!(result.is_ok());

        solver.assert_bounds(v1,-5, -3);
        solver.assert_bounds(v2,-3, -1);

    }

    #[test]
    fn test_propagation() {
        let mut solver = TestSolver::default();
        let v1 = solver.new_variable(387, 387);
        let v2 = solver.new_variable(0, 30);
        let v3 = solver.new_variable(0, 8);
        let v4 = solver.new_variable(0, 60);
        let v = vec![v1, v2, v3, v4];
        let x = v.into_boxed_slice();
        let b = 407;
        let constraint_tag = solver.new_constraint_tag();

        let result = solver.new_propagator(LinearConstructor{
            x,
            bound: b,
            constraint_tag,
            conflict_detection_only: false,
        });

        assert!(result.is_ok());

        solver.assert_bounds(v1,387, 387);
        solver.assert_bounds(v2,0, 20);
        solver.assert_bounds(v3,0, 8);
        solver.assert_bounds(v4,0, 20);

    }
}

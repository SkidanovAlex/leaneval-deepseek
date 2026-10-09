import Mathlib
import Submission.Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Import hub: a place of an algebraic closure over a prescribed prime

Re-exports `Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime` so that
delegated statements living under `Submission/Work` can name it through a `Submission.Work.*`
module path.
-/

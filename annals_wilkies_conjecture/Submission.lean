import ChallengeDeps
import Submission.Helpers
import Submission.Work.Wilkies.Holes
import Submission.Work.WilFinal.WireOfProp9

open WilkiesConjecture
open FirstOrder Language IntermediateField

set_option autoImplicit false
variable {n : ℕ}
local notation "ℝⁿ" => Fin n → ℝ

namespace Submission

theorem corollary_1 (X : Set ℝⁿ) (h : IsRExpDefinable X) :
    ∃ f : MvPolynomial (Fin 2) ℝ, ∀ (g H : ℕ),
      Nat.card (degreeHeightLE X.trans g H) ≤ f.eval ![(g : ℝ), Real.log H] :=
  Work.WilFinal.corollary_1_final X h

end Submission

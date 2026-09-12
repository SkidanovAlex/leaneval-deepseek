import Mathlib
import Submission.LMMeas

/-!
Helper lemmas for the tower argument (ENNReal identities).  The tower itself is delegated.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory

noncomputable section
open Classical

namespace Submission.Discrepancy

lemma ofReal_exp_add (a b : ℝ) :
    ENNReal.ofReal (Real.exp (a + b)) = ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp b) := by
  rw [Real.exp_add]
  exact (ENNReal.ofReal_mul (Real.exp_nonneg a))

lemma lintegral_const_mul_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} (c : ℝ)
    (hc : 0 ≤ c) (f : α → ℝ) (hmeas : Measurable (fun x : α => ENNReal.ofReal (f x))) :
    (∫⁻ x, ENNReal.ofReal (c * f x) ∂μ) = ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  rw [show (fun x : α => ENNReal.ofReal (c * f x)) = fun x => ENNReal.ofReal c * ENNReal.ofReal (f x) by
    funext x
    exact (ENNReal.ofReal_mul hc)]
  exact lintegral_const_mul (ENNReal.ofReal c) hmeas

end Discrepancy

end Submission

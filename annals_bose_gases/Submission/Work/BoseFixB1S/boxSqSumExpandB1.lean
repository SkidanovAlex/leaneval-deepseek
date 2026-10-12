import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.integral_sq_sum_of_orth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators

/-- **Expansion of the box `L²`-norm of a finite sum** (no orthogonality needed): the square of a finite sum of box-integrable functions expands into the double sum of the pairwise pairings. Pure `integral_finsetSum` + `Finset.sum_mul_sum` bookkeeping, following the head of `Work.BoseFixB1S.integral_sq_sum_of_orth` (`Submission.Work.BoseFixB1S.integral_sq_sum_of_orth`). -/
theorem boxSqSumExpandB1 {N : ℕ} {ℓ : ℝ} {ι : Type*} {s : Finset ι}
    {f : ι → Submission.BoseGases.X N → ℝ}
    (hprod : ∀ p ∈ s, ∀ q ∈ s, MeasureTheory.IntegrableOn (fun x => f p x * f q x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    (∫ x in Submission.BoseGases.abox N ℓ, (∑ p ∈ s, f p x) ^ 2)
      = ∑ p ∈ s, ∑ q ∈ s,
          (∫ x in Submission.BoseGases.abox N ℓ, f p x * f q x) := by
  -- the pointwise expansion of the square of the sum as a double sum of pairwise products
  have hpoint : ∀ x, (∑ p ∈ s, f p x) ^ 2 = ∑ p ∈ s, ∑ q ∈ s, f p x * f q x := by
    intro x
    rw [sq, Finset.sum_mul_sum]
  calc (∫ x in Submission.BoseGases.abox N ℓ, (∑ p ∈ s, f p x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ, ∑ p ∈ s, ∑ q ∈ s, f p x * f q x := by
        apply integral_congr_ae
        filter_upwards with x
        exact hpoint x
    _ = ∑ p ∈ s, ∫ x in Submission.BoseGases.abox N ℓ, ∑ q ∈ s, f p x * f q x := by
        rw [integral_finsetSum]
        intro p hp
        exact integrable_finsetSum s (fun q hq => hprod p hp q hq)
    _ = ∑ p ∈ s, ∑ q ∈ s, ∫ x in Submission.BoseGases.abox N ℓ, f p x * f q x := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [integral_finsetSum]
        intro q hq
        exact hprod p hp q hq

end Work.BoseFixB1S

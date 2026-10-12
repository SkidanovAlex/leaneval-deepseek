import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxFlatAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators

/-- **Pythagoras for the analysis box.**  If all pairwise products `f p * f q` (`p, q ∈ s`) are
integrable on the N-particle box `abox N ℓ` and every *cross* integral `∫ (f p * f q)` with
`p ≠ q` vanishes, then the `L²` norm² of the sum is the sum of the `L²` norm² of the pieces:

  `∫_{abox} (∑_{p ∈ s} f p)² = ∑_{p ∈ s} ∫_{abox} (f p)²`.

No measurability of the box itself is needed: all cancellations are done at the level of the
Bochner integral against the restricted measure `volume.restrict (abox N ℓ)`. -/
theorem integral_sq_sum_of_orth {N : ℕ} {ℓ : ℝ} {ι : Type*} {s : Finset ι}
    {f : ι → Submission.BoseGases.X N → ℝ}
    (hprod : ∀ p ∈ s, ∀ q ∈ s,
      MeasureTheory.IntegrableOn (fun x => f p x * f q x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (horth : ∀ p ∈ s, ∀ q ∈ s, p ≠ q →
      (∫ x in Submission.BoseGases.abox N ℓ, f p x * f q x) = 0) :
    (∫ x in Submission.BoseGases.abox N ℓ, (∑ p ∈ s, f p x) ^ 2)
      = ∑ p ∈ s, ∫ x in Submission.BoseGases.abox N ℓ, (f p x) ^ 2 := by
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
    _ = ∑ p ∈ s, ∫ x in Submission.BoseGases.abox N ℓ, (f p x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_eq_single p]
        · congr 1 with x
          exact (sq (f p x)).symm
        · intro q hq hqp
          exact horth p hp q hq hqp.symm
        · intro hpnot
          exact absurd hp hpnot

end Work.BoseFixB1S

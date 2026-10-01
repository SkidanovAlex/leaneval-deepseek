import Mathlib
import Submission.Work.LinnikAreas.Density4.TestFun

open MeasureTheory

namespace Work.LinnikAreas.Density4

/-- `gT` is even: it depends on `|t|`, and `cos (ζ·(-t)) = cos (ζ·t)`. -/
lemma gT_neg (θ lam t : ℝ) : gT θ lam (-t) = gT θ lam t := by
  rw [gT, gT, abs_neg]
  by_cases h : |t| ≤ gammaT θ lam
  · rw [if_pos h, if_pos h, mul_neg, Real.cos_neg]
  · rw [if_neg h, if_neg h]

/-- The convolution of `gT` with itself is even in the displacement: substituting `s ↦ -s`
(available because Lebesgue measure on `ℝ` is negation-invariant) and using that `gT` is even. -/
theorem convT_even {θ lam : ℝ} (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) (hlam : 0 < lam) :
    ∀ v : ℝ, (∫ s : ℝ, gT θ lam s * gT θ lam (-v - s))
      = ∫ s : ℝ, gT θ lam s * gT θ lam (v - s) := by
  intro v
  rw [← integral_neg_eq_self (f := fun s => gT θ lam s * gT θ lam (-v - s))]
  apply integral_congr_ae
  filter_upwards with s
  rw [gT_neg]
  have : -v - -s = -(v - s) := by ring
  rw [this, gT_neg]

end Work.LinnikAreas.Density4

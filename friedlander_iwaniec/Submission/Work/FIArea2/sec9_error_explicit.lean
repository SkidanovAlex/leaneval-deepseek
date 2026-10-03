import Mathlib
import Submission.Work.FIArea2.sec9_error_from_poisson
import Submission.Work.FIArea2.G8Defs
import Submission.Work.FIArea2.SmoothSec6Defs

namespace Work.FIArea2

open scoped BigOperators

/-- The `secFreq₂` analogue of `secFreq_sq_mul`: the weight of the second frequency of Lemma 7.1's
`h`-sum is `(1 + h₂²c₂)^{−1}` with `c₂ = secWeight₂`. -/
lemma secFreq₂_sq_mul (Pa : Work.FITop.Params) (z1 z2 : GaussianInt)
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) (hγ0 : 0 ≤ gamOf z1 z2) (hγ1 : gamOf z1 z2 < 1)
    (hM : 1 ≤ Pa.M) (h : ℤ) :
    (secFreq₂ z1 z2 h) ^ 2 * Real.sqrt (1 - (gamOf z1 z2) ^ 2) * Real.sqrt Pa.M
      = (h : ℝ) ^ 2 * secWeight₂ Pa z1 z2 := by
  have hAbs : Work.FIPlan.absDelta z1 z2 ≠ 0 := by
    simp only [Work.FIPlan.absDelta]
    exact fun hz => hΔ ((Int.natAbs_eq_zero).mp hz)
  have hA : (0 : ℝ) < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hAbs
  have hz1 : z1 ≠ 0 := fun hz => hΔ (delta_eq_zero_of_fst_eq_zero z1 z2 hz)
  have hn1 : (0 : ℝ) < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := by
    exact_mod_cast gnorm_pos_of_ne_zero z1 hz1
  have hs1 : (0 : ℝ) < Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)) := Real.sqrt_pos.2 hn1
  have hD : (0 : ℝ) < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)) := mul_pos hA hs1
  have hMpos : (0 : ℝ) < Real.sqrt Pa.M := Real.sqrt_pos.2 (by linarith)
  have hδ2 : (0 : ℝ) < 1 - (gamOf z1 z2) ^ 2 := by
    nlinarith [hγ0, hγ1, sq_nonneg (gamOf z1 z2)]
  unfold secFreq₂ secWeight₂
  rw [div_pow, Real.sq_sqrt hD.le]
  field_simp

end Work.FIArea2

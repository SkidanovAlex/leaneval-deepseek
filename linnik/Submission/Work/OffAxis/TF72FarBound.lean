import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.OffAxis.TF72Calc
import Submission.Work.OffAxis.tf72_far_arith
import Submission.Work.ZeroFreeTables.XY.xyReQuadFarBound
import Submission.Work.OffAxis.tf72poly_iteratedDeriv_two_bound
import Submission.Work.ZeroFreeTables.tf72Fc_decay

namespace Work.OffAxis

/-- Second-derivative bound for the Lemma 7.2 polynomial at `λ = 6/7`, with the
explicit constant `3456/343 = 16·(6/7)³` supplied by
`tf72poly_iteratedDeriv_two_bound`. -/
private lemma tf72_M2_bound : ∀ t ∈ Set.Icc (0:ℝ) (2 / ((6:ℝ)/7)),
    ‖((iteratedDeriv 2 (Work.ZeroFreeTables.tf72poly ((6:ℝ)/7)) t : ℝ) : ℂ)‖
      ≤ 3456/343 := by
  intro t ht
  have h := tf72poly_iteratedDeriv_two_bound ((6:ℝ)/7) t (by norm_num) ht.1 ht.2
  have he : (16:ℝ) * ((6:ℝ)/7) ^ 3 = 3456/343 := by norm_num
  rwa [he] at h

/-- The value at the left endpoint: `tf72poly (6/7) 0 = 32/35`. -/
private lemma tf72_poly_at_zero : Work.ZeroFreeTables.tf72poly ((6:ℝ)/7) 0 = 32/35 := by
  unfold Work.ZeroFreeTables.tf72poly
  norm_num

theorem TF72FarBound : ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 → 200 ≤ |m| →
    (Work.ZeroFreeTables.tf72Fc ((6:ℝ)/7) (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re ≤ 16/105 := by
  intro a m ha0 ha6 hm
  set z : ℂ := ((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I with hz
  have hzin : z.im = m := by simp [hz]
  have hzre_eq : z.re = -a := by simp [hz]
  have hzre : |z.re| ≤ 1 := by
    rw [hzre_eq, abs_neg, abs_of_nonneg ha0]; linarith
  have hne : z.im ≠ 0 := by
    rw [hzin]
    intro h
    have : |m| = 0 := by rw [h, abs_zero]
    rw [this] at hm
    linarith
  -- the quadratic far-field bound of HB Lemma 7.2 at `λ = 6/7`
  have hquad := Work.ZeroFreeTables.XY.tf72Fc_re_quadLe ((6:ℝ)/7) (3456/343)
    (by norm_num) (by norm_num) tf72_M2_bound z hzre hne
  have hnum : (|Work.ZeroFreeTables.tf72poly ((6:ℝ)/7) 0|
        + Real.exp (2 / ((6:ℝ)/7)) * (3456/343) * (2 / ((6:ℝ)/7))) / z.im ^ 2
      = (32/35 + Real.exp (7/3) * (3456/343) * (7/3)) / m ^ 2 := by
    have harg : (2:ℝ) / ((6:ℝ)/7) = 7/3 := by norm_num
    rw [tf72_poly_at_zero, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 32/35), hzin, harg]
  have hfar := tf72_far_arith m hm
  calc (Work.ZeroFreeTables.tf72Fc ((6:ℝ)/7) z).re
      ≤ |(Work.ZeroFreeTables.tf72Fc ((6:ℝ)/7) z).re| := le_abs_self _
    _ ≤ (|Work.ZeroFreeTables.tf72poly ((6:ℝ)/7) 0|
          + Real.exp (2 / ((6:ℝ)/7)) * (3456/343) * (2 / ((6:ℝ)/7))) / z.im ^ 2 := hquad
    _ = (32/35 + Real.exp (7/3) * (3456/343) * (7/3)) / m ^ 2 := hnum
    _ ≤ 16/315 := hfar
    _ ≤ 16/105 := by norm_num

end Work.OffAxis

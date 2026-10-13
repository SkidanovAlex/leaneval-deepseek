import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

/-
`rgiB α m c y = ∫_{Ioi y} c t · t^{-p-1}` with `p = 2m/α > 0`.  Since `|c t| ≤ M`, the absolute
value of the tail integral is at most `∫_{Ioi y} M t^{-p-1} = M·y^{-p}/p`.
-/
theorem rgiB_abs_le {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) {c : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t : ℝ, |c t| ≤ M) :
    ∀ y : ℝ, 0 < y →
      |Work.FTS.PhiStar.Series.rgiB α m c y|
        ≤ M * y ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α) := by
  intro y hy
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hb0 : 0 < 2 * (m : ℝ) / α := div_pos (by linarith) hα
  have hdef : Work.FTS.PhiStar.Series.rgiB α m c y
      = ∫ t in Set.Ioi y, c t * t ^ (-(2 * (m : ℝ) / α) - 1) := rfl
  -- the dominating function is integrable on `Ioi y` because its exponent is `< -1`
  have hg : MeasureTheory.Integrable (fun t : ℝ => M * t ^ (-(2 * (m : ℝ) / α) - 1))
      (MeasureTheory.volume.restrict (Set.Ioi y)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -(2 * (m : ℝ) / α) - 1) (by linarith) hy).const_mul M
  -- pointwise domination on `Ioi y`
  have hpt : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi y)),
      ‖c t * t ^ (-(2 * (m : ℝ) / α) - 1)‖
        ≤ M * t ^ (-(2 * (m : ℝ) / α) - 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hy ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    exact mul_le_mul_of_nonneg_right (hb t) (Real.rpow_nonneg ht0.le _)
  have hmain := MeasureTheory.norm_integral_le_of_norm_le hg hpt
  -- the value of the dominating integral
  have hInt : ∫ t in Set.Ioi y, M * t ^ (-(2 * (m : ℝ) / α) - 1)
      = M * y ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α) := by
    rw [MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt (a := -(2 * (m : ℝ) / α) - 1) (by linarith) hy]
    have hexp : -(2 * (m : ℝ) / α) - 1 + 1 = -(2 * (m : ℝ) / α) := by ring
    rw [hexp]
    rw [show -y ^ (-(2 * (m : ℝ) / α)) / (-(2 * (m : ℝ) / α))
        = y ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α) from by ring]
    ring
  rw [← hdef, Real.norm_eq_abs] at hmain
  rw [hInt] at hmain
  exact hmain

end Work.FTS.PhiStar.Honesty

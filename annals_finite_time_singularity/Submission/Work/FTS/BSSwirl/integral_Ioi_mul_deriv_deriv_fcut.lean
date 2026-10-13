import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.BSSwirl.inv_norm_cut

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS.BSSwirl

/-- `∫_0^∞ y · fcut''(y) dy = -1`.

Integrate by parts on `[0, 3]` (the second derivative of `fcut` is supported in `[1, 2]`, so the
integral over `Ioi 0` is the one over `[0, 3]`):

`∫_0^3 y · fcut''(y) dy = [y · fcut'(y)]_0^3 - ∫_0^3 fcut'(y) dy = 0 - (fcut 3 - fcut 0) = -1`.

This is the `n = 0` instance of the "moment" identity for the smooth cutoff, used when
differentiating the Newtonian potential of a compactly supported field. -/
theorem integral_Ioi_mul_deriv_deriv_fcut :
    ∫ y in Set.Ioi (0 : ℝ), y * deriv (deriv Work.FTS.BSSwirl.fcut) y = -1 := by
  have hd1 : Differentiable ℝ fcut := (contDiff_fcut 1).differentiable (by norm_num)
  have hd2 : Differentiable ℝ (deriv fcut) := (contDiff_fcut 2).differentiable_deriv_two
  have hc1 : Continuous (deriv fcut) := (contDiff_fcut 2).continuous_deriv (by norm_num)
  have hc2 : Continuous (deriv (deriv fcut)) := by
    have h : ContDiff ℝ 0 (deriv^[2] fcut) :=
      ContDiff.iterate_deriv' (𝕜 := ℝ) 0 2 (contDiff_fcut 2)
    simpa [Function.iterate_succ, Function.comp_def] using h
  -- the integrand vanishes to the right of `2`
  have hzero : ∀ y ∈ Set.Ioi (0:ℝ) \ Set.Ioc (0:ℝ) 3, y * deriv (deriv fcut) y = 0 := by
    intro y hy
    have hy3 : 3 < y := by
      by_contra h
      exact hy.2 ⟨hy.1, le_of_not_gt h⟩
    rw [deriv_deriv_fcut_eq_zero_of_gt_two (by linarith), mul_zero]
  have hset : ∫ y in Set.Ioi (0:ℝ), y * deriv (deriv fcut) y
      = ∫ y in Set.Ioc (0:ℝ) 3, y * deriv (deriv fcut) y :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => hx.1) hzero
  -- integration by parts on `[0, 3]`
  have hibp : ∫ y in (0:ℝ)..3, y * deriv (deriv fcut) y
      = 3 * deriv fcut 3 - 0 * deriv fcut 0 - ∫ y in (0:ℝ)..3, (1:ℝ) * deriv fcut y := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := fun x : ℝ => x)
      (u' := fun _ => (1:ℝ)) (v := deriv fcut) (v' := deriv (deriv fcut)) ?_ ?_ ?_ ?_
    · intro x _
      exact hasDerivAt_id x
    · intro x _
      exact (hd2 x).hasDerivAt
    · exact intervalIntegrable_const
    · exact hc2.intervalIntegrable 0 3
  have hftc : ∫ y in (0:ℝ)..3, deriv fcut y = fcut 3 - fcut 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => (hd1 x).hasDerivAt)
      (hc1.intervalIntegrable 0 3)
  rw [hset, (intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 3)).symm, hibp]
  have h3 : deriv fcut 3 = (0:ℝ) := deriv_fcut_eq_zero_of_gt_two (by norm_num)
  have h03 : (∫ y in (0:ℝ)..3, (1:ℝ) * deriv fcut y) = 1 := by
    rw [show (∫ y in (0:ℝ)..3, (1:ℝ) * deriv fcut y) = ∫ y in (0:ℝ)..3, deriv fcut y by
      simp only [one_mul]]
    rw [hftc, fcut_three, fcut_zero]
    norm_num
  rw [h3, h03]
  ring

end Work.FTS.BSSwirl

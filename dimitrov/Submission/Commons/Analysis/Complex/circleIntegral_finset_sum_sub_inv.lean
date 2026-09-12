import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral

namespace Commons.Analysis.Complex

open Metric

/-- Key single-term computation: for `ρ > 0` and a point `u` not on the circle `|z| = ρ`,
the circle integral of `z ↦ c / (z - u)` is `2πi c` if `‖u‖ < ρ`, and `0` otherwise. -/
lemma circleIntegral_const_mul_sub_inv {ρ : ℝ} (hρ : 0 < ρ) {u : ℂ} {c : ℂ}
    (hu : ‖u‖ ≠ ρ) :
    circleIntegral (fun z => c * (z - u)⁻¹) 0 ρ =
      (2 * Real.pi * Complex.I) * (if ‖u‖ < ρ then c else 0) := by
  rcases lt_or_gt_of_ne hu with hlt | hgt
  · rw [if_pos hlt]
    have hmem : u ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball, dist_zero_right]
      exact hlt
    have h1 : circleIntegral (fun z => c * (z - u)⁻¹) 0 ρ
        = c * circleIntegral (fun z => (z - u)⁻¹) 0 ρ :=
      circleIntegral.integral_const_mul c (fun z => (z - u)⁻¹) 0 ρ
    rw [h1, circleIntegral.integral_sub_inv_of_mem_ball hmem]
    ring
  · rw [if_neg (not_lt.mpr hgt.le), mul_zero]
    refine _root_.Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hρ.le
      (s := ∅) Set.countable_empty ?_ ?_
    · have hne : ∀ z ∈ closedBall (0 : ℂ) ρ, z - u ≠ 0 := by
        intro z hz hzu
        have hzρ : ‖z‖ ≤ ρ := by
          rw [mem_closedBall, dist_zero_right] at hz
          exact hz
        rw [sub_eq_zero.mp hzu] at hzρ
        linarith
      exact ((continuousOn_id.sub continuousOn_const).inv₀ hne).const_mul c
    · intro z hz
      rw [Set.mem_sdiff] at hz
      have hzρ : ‖z‖ < ρ := by
        rw [mem_ball, dist_zero_right] at hz
        exact hz.1
      have hzne : z - u ≠ 0 := by
        intro h
        rw [sub_eq_zero.mp h] at hzρ
        linarith
      exact ((differentiableAt_id.sub_const u).inv hzne).const_mul c

theorem circleIntegral_finset_sum_sub_inv {ρ : ℝ} (hρ : 0 < ρ) {S : Finset ℂ} {c : ℂ → ℂ}
    (hS : ∀ u ∈ S, ‖u‖ ≠ ρ) :
    circleIntegral (fun z => ∑ u ∈ S, c u * (1 / (z - u))) 0 ρ =
      (2 * Real.pi * Complex.I) * (∑ u ∈ S, if ‖u‖ < ρ then c u else 0) := by
  have hfun : (fun z : ℂ => ∑ u ∈ S, c u * (1 / (z - u)))
      = fun z => ∑ u ∈ S, c u * (z - u)⁻¹ := by
    funext z
    simp only [one_div]
  rw [hfun]
  have hint : ∀ u ∈ S, CircleIntegrable (fun z => c u * (z - u)⁻¹) 0 ρ := by
    intro u hu
    have hne : ∀ z ∈ sphere (0 : ℂ) |ρ|, z - u ≠ 0 := by
      intro z hz hzu
      have hz' : ‖z‖ = |ρ| := by
        rw [mem_sphere, dist_zero_right] at hz
        exact hz
      rw [sub_eq_zero.mp hzu, abs_of_pos hρ] at hz'
      exact hS u hu hz'
    exact (((continuousOn_id.sub continuousOn_const).inv₀ hne).const_mul (c u)).circleIntegrable'
  have hsum := circleIntegral.integral_fun_sum (s := S) (f := fun u z => c u * (z - u)⁻¹)
    (c := 0) (R := ρ) hint
  rw [hsum]
  rw [Finset.sum_congr rfl (fun u hu => circleIntegral_const_mul_sub_inv hρ (hS u hu))]
  rw [Finset.mul_sum]

end Commons.Analysis.Complex
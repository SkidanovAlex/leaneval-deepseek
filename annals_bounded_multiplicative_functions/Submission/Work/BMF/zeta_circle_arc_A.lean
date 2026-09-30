import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open MeasureTheory

/-- The contribution of the arc `cos θ > 0`: the `cos θ`-weighted integral of the Euler-product
majorant `cos θ (1 + log (1/(R cos θ)))` is at most `2 log (1/R) + 4`, and the majorant is
interval integrable. -/
theorem zeta_circle_arc_A {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1 / 2) :
    IntervalIntegrable (fun θ : ℝ =>
        (if 0 < Real.cos θ then Real.cos θ * (1 + Real.log (1 / (R * Real.cos θ))) else 0))
      MeasureTheory.volume 0 (2 * Real.pi) ∧
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (if 0 < Real.cos θ then Real.cos θ * (1 + Real.log (1 / (R * Real.cos θ))) else 0))
      ≤ 2 * Real.log (1 / R) + 4 := by
  set G : ℝ → ℝ := fun θ =>
    (if 0 < Real.cos θ then Real.cos θ * (1 + Real.log (1 / (R * Real.cos θ))) else 0) with hGdef
  have hsin3 : Real.sin (3 * Real.pi / 2) = -1 := by
    have hsplit : (3 : ℝ) * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
    rw [hsplit, Real.sin_add_pi, Real.sin_pi_div_two]
  -- measurability and boundedness of `G`
  have hGmeas : Measurable G := by
    simp only [hGdef]
    refine Measurable.ite (p := fun θ : ℝ => 0 < Real.cos θ) ?_ ?_ measurable_const
    · exact measurableSet_lt measurable_const Real.measurable_cos
    · exact Real.measurable_cos.mul (measurable_const.add
        (Real.measurable_log.comp (measurable_const.div
          (measurable_const.mul Real.measurable_cos))))
  have hGbound : ∀ θ : ℝ, ‖G θ‖ ≤ 1 / R := by
    intro θ
    rw [Real.norm_eq_abs]
    simp only [hGdef]
    by_cases h : 0 < Real.cos θ
    · rw [if_pos h, abs_of_nonneg]
      · have hpos : 0 < 1 / (R * Real.cos θ) := by positivity
        have hlog : Real.log (1 / (R * Real.cos θ)) ≤ 1 / (R * Real.cos θ) - 1 :=
          Real.log_le_sub_one_of_pos hpos
        calc Real.cos θ * (1 + Real.log (1 / (R * Real.cos θ)))
            ≤ Real.cos θ * (1 / (R * Real.cos θ)) :=
              mul_le_mul_of_nonneg_left (by linarith) (le_of_lt h)
          _ = 1 / R := by field_simp
      · have hpos : 0 < 1 / (R * Real.cos θ) := by positivity
        have hle1 : 1 ≤ 1 / (R * Real.cos θ) := by
          rw [le_div_iff₀ (show (0 : ℝ) < R * Real.cos θ by positivity)]
          nlinarith [h.le, hR, hR1, Real.cos_le_one θ]
        exact mul_nonneg h.le (by linarith [Real.log_nonneg hle1])
    · rw [if_neg h, abs_zero]; positivity
  have hIntOn : ∀ s : Set ℝ, volume s < ⊤ → IntegrableOn G s volume := by
    intro s hs
    refine IntegrableOn.of_bound hs hGmeas.aestronglyMeasurable.restrict (1 / R) ?_
    exact Filter.Eventually.of_forall (fun x => hGbound x)
  have hfin : ∀ a b : ℝ, volume (Set.Ioc a b) < ⊤ := by
    intro a b; rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hGint : ∀ a b : ℝ, IntervalIntegrable G volume a b :=
    fun a b => ⟨hIntOn _ (hfin a b), hIntOn _ (hfin b a)⟩
  -- pointwise bound on the right half plane
  have hpt : ∀ θ : ℝ, 0 ≤ Real.cos θ → G θ ≤ Real.log (1 / R) * Real.cos θ + 1 := by
    intro θ hcos0
    simp only [hGdef]
    by_cases h : 0 < Real.cos θ
    · rw [if_pos h]
      have hsplit : Real.log (1 / (R * Real.cos θ))
          = Real.log (1 / R) + Real.log (1 / Real.cos θ) := by
        rw [show (1 : ℝ) / (R * Real.cos θ) = (1 / R) * (1 / Real.cos θ) by field_simp]
        rw [Real.log_mul (by positivity) (by positivity)]
      have hkey : Real.cos θ * Real.log (1 / Real.cos θ) ≤ 1 - Real.cos θ := by
        have h1 : Real.log (1 / Real.cos θ) ≤ 1 / Real.cos θ - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        calc Real.cos θ * Real.log (1 / Real.cos θ) ≤ Real.cos θ * (1 / Real.cos θ - 1) :=
              mul_le_mul_of_nonneg_left h1 (le_of_lt h)
          _ = 1 - Real.cos θ := by field_simp
      rw [hsplit]
      have hexp : Real.cos θ * (1 + (Real.log (1 / R) + Real.log (1 / Real.cos θ)))
          = Real.log (1 / R) * Real.cos θ
            + (Real.cos θ + Real.cos θ * Real.log (1 / Real.cos θ)) := by ring
      rw [hexp]
      linarith
    · rw [if_neg h]
      have hzero : Real.cos θ = 0 := le_antisymm (le_of_not_gt h) hcos0
      rw [hzero]; norm_num
  -- the three arcs
  have hL : (∫ θ in (0 : ℝ)..(Real.pi / 2), G θ) ≤ Real.log (1 / R) + Real.pi / 2 := by
    have hintg : IntervalIntegrable (fun θ : ℝ => Real.log (1 / R) * Real.cos θ + 1)
        volume (0 : ℝ) (Real.pi / 2) :=
      ((continuous_const.mul Real.continuous_cos).add continuous_const).intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
      (hGint 0 (Real.pi / 2)) hintg
      (fun θ hθ => hpt θ (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩))
    have hval : (∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.log (1 / R) * Real.cos θ + 1))
        = Real.log (1 / R) + Real.pi / 2 := by
      rw [intervalIntegral.integral_add]
      · rw [intervalIntegral.integral_const_mul, integral_cos]
        rw [intervalIntegral.integral_const]
        rw [Real.sin_pi_div_two, Real.sin_zero]
        ring
      · exact (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _
      · exact intervalIntegrable_const
    linarith [hmono, hval]
  have hM0 : (∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), G θ) = 0 := by
    have hEq : Set.EqOn G (fun _ : ℝ => (0 : ℝ)) (Set.uIcc (Real.pi / 2) (3 * Real.pi / 2)) := by
      intro θ hθ
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : Real.pi / 2 ≤ 3 * Real.pi / 2)] at hθ
      simp only [hGdef]
      rw [if_neg (by
        intro hgt
        exact absurd (Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 (by linarith [hθ.2]))
          (not_le.mpr hgt))]
    rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_zero]
  have hR2 : (∫ θ in (3 * Real.pi / 2)..(2 * Real.pi), G θ) ≤ Real.log (1 / R) + Real.pi / 2 := by
    have hintg : IntervalIntegrable (fun θ : ℝ => Real.log (1 / R) * Real.cos θ + 1)
        volume (3 * Real.pi / 2) (2 * Real.pi) :=
      ((continuous_const.mul Real.continuous_cos).add continuous_const).intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on
      (by linarith [Real.pi_pos] : 3 * Real.pi / 2 ≤ 2 * Real.pi)
      (hGint (3 * Real.pi / 2) (2 * Real.pi)) hintg
      (fun θ hθ => hpt θ (by
        have h2 : Real.cos θ = Real.cos (2 * Real.pi - θ) := (Real.cos_two_pi_sub θ).symm
        rw [h2]
        exact Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [hθ.2, Real.pi_pos], by linarith [hθ.1, Real.pi_pos]⟩))
    have hval : (∫ θ in (3 * Real.pi / 2)..(2 * Real.pi), (Real.log (1 / R) * Real.cos θ + 1))
        = Real.log (1 / R) + Real.pi / 2 := by
      rw [intervalIntegral.integral_add]
      · rw [intervalIntegral.integral_const_mul, integral_cos]
        rw [intervalIntegral.integral_const]
        rw [Real.sin_two_pi, hsin3]
        ring
      · exact (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _
      · exact intervalIntegrable_const
    linarith [hmono, hval]
  refine ⟨hGint 0 (2 * Real.pi), ?_⟩
  have hsplit : (∫ θ in (0 : ℝ)..(2 * Real.pi), G θ)
      = (∫ θ in (0 : ℝ)..(Real.pi / 2), G θ)
        + (∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), G θ)
        + (∫ θ in (3 * Real.pi / 2)..(2 * Real.pi), G θ) := by
    have a := intervalIntegral.integral_add_adjacent_intervals
      (hGint 0 (Real.pi / 2)) (hGint (Real.pi / 2) (3 * Real.pi / 2))
    have b := intervalIntegral.integral_add_adjacent_intervals
      (hGint 0 (3 * Real.pi / 2)) (hGint (3 * Real.pi / 2) (2 * Real.pi))
    linarith
  rw [hsplit]
  linarith [hL, hM0, hR2, Real.pi_lt_four]

end Work.BMF

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Ratio bounds for `tan (ρ/2)` versus `tan (√(c/4)/2)`

For `0 < c ≤ 1/4` and `√(c/4) < ρ ≤ π - arccos (1 - c)` the ratio
`tan (ρ/2) / tan (√(c/4)/2)` lies in the interval `[1, 8/c]`.

* Lower bound: `tan` is strictly increasing on `(-π/2, π/2)` and
  `√(c/4)/2 < ρ/2 < π/2`.
* Upper bound: writing `θ = arccos (1 - c)`, we have `ρ/2 ≤ π/2 - θ/2` and hence
  `tan (ρ/2) ≤ tan (π/2 - θ/2) = cot (θ/2) = √((2-c)/c) ≤ 2/√c`;
  while `tan (√(c/4)/2) ≥ √(c/4)/2 = √c/4`.  Multiplying gives
  `(2/√c) · (4/√c) = 8/c`.
-/

namespace Work.Diff.C.geoCrux

theorem tan_ratio_bounds {c ρ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hρ : 0 < ρ) (hρL : ρ ≤ Real.pi - Real.arccos (1 - c))
    (hδ : Real.sqrt (c / 4) < ρ) :
    1 ≤ Real.tan (ρ / 2) / Real.tan (Real.sqrt (c / 4) / 2) ∧
      Real.tan (ρ / 2) / Real.tan (Real.sqrt (c / 4) / 2) ≤ 8 / c := by
  -- Notation: `θ = arccos (1 - c)`.
  set θ := Real.arccos (1 - c) with hθ
  have hcosθ : Real.cos θ = 1 - c := by
    rw [hθ]; exact Real.cos_arccos (by linarith) (by linarith)
  have hθ_pos : 0 < θ := by rw [hθ]; exact Real.arccos_pos.mpr (by linarith)
  have hθ_le : θ ≤ Real.pi := Real.arccos_le_pi _
  have hρ_le : ρ ≤ Real.pi - θ := by rw [hθ] at hρL; exact hρL
  -- Upper bound for `tan (ρ/2)`.
  have hρ2_le : ρ / 2 ≤ Real.pi / 2 - θ / 2 := by linarith
  have hρ2_lt : ρ / 2 < Real.pi / 2 := by linarith
  have hright_lt : Real.pi / 2 - θ / 2 < Real.pi / 2 := by linarith
  have hright_gt : -(Real.pi / 2) < Real.pi / 2 - θ / 2 := by linarith
  have hmon : Real.tan (ρ / 2) ≤ Real.tan (Real.pi / 2 - θ / 2) :=
    Real.strictMonoOn_tan.monotoneOn
      ⟨by linarith [Real.pi_pos], hρ2_lt⟩ ⟨hright_gt, hright_lt⟩ hρ2_le
  have hsin : Real.sin (θ / 2) = Real.sqrt (c / 2) := by
    rw [Real.sin_half_eq_sqrt (le_of_lt hθ_pos) (by linarith)]
    congr 1
    rw [hcosθ]; ring
  have hcos : Real.cos (θ / 2) = Real.sqrt ((2 - c) / 2) := by
    rw [Real.cos_half (by linarith) hθ_le]
    congr 1
    rw [hcosθ]; ring
  have hval : Real.tan (Real.pi / 2 - θ / 2) = Real.sqrt ((2 - c) / c) := by
    rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, hcos, hsin]
    rw [← Real.sqrt_div (show (0 : ℝ) ≤ (2 - c) / 2 by linarith)]
    congr 1
    field_simp
  have hle : (2 - c) / c ≤ 4 / c := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hc)
    linarith
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have htan_rho : Real.tan (ρ / 2) ≤ 2 / Real.sqrt c :=
    calc Real.tan (ρ / 2) ≤ Real.tan (Real.pi / 2 - θ / 2) := hmon
      _ = Real.sqrt ((2 - c) / c) := hval
      _ ≤ Real.sqrt (4 / c) := Real.sqrt_le_sqrt hle
      _ = 2 / Real.sqrt c := by rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 4), h4]
  -- The small denominator.
  have hc4_pos : 0 < c / 4 := by linarith
  have hd_pos : 0 < Real.sqrt (c / 4) := Real.sqrt_pos.mpr hc4_pos
  have hd2_pos : 0 < Real.sqrt (c / 4) / 2 := by linarith
  have hd_le : Real.sqrt (c / 4) ≤ 1 / 4 := by
    have h1 : c / 4 ≤ (1 / 4 : ℝ) ^ 2 := by nlinarith
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 4)] at h2
  have hd2_lt : Real.sqrt (c / 4) / 2 < Real.pi / 2 := by
    nlinarith [hd_le, Real.pi_gt_three]
  have hden_pos : 0 < Real.tan (Real.sqrt (c / 4) / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two hd2_pos hd2_lt
  have htan_le : Real.tan (Real.sqrt (c / 4) / 2) ≤ Real.tan (ρ / 2) :=
    Real.strictMonoOn_tan.monotoneOn
      ⟨by linarith [hd2_pos, Real.pi_pos], hd2_lt⟩
      ⟨by linarith [hρ, Real.pi_pos], hρ2_lt⟩
      (by linarith [hδ])
  refine ⟨?_, ?_⟩
  · -- Lower bound: numerator dominates the denominator.
    rw [le_div_iff₀ hden_pos, one_mul]
    exact htan_le
  · have hd_eq : Real.sqrt (c / 4) / 2 = Real.sqrt c / 4 := by
      rw [Real.sqrt_div hc.le]
      rw [show Real.sqrt (4 : ℝ) = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      ring
    have hle_tan : Real.sqrt c / 4 ≤ Real.tan (Real.sqrt (c / 4) / 2) := by
      rw [← hd_eq]; exact Real.le_tan hd2_pos.le hd2_lt
    have hzinv : (Real.tan (Real.sqrt (c / 4) / 2))⁻¹ ≤ 4 / Real.sqrt c := by
      have h1 : (Real.tan (Real.sqrt (c / 4) / 2))⁻¹ ≤ (Real.sqrt c / 4)⁻¹ :=
        (inv_le_inv₀ hden_pos (div_pos (Real.sqrt_pos.mpr hc) (by norm_num))).mpr hle_tan
      rwa [inv_div] at h1
    have hnum_nn : 0 ≤ 2 / Real.sqrt c :=
      div_nonneg (by norm_num) (Real.sqrt_pos.mpr hc).le
    have hfinal : (2 / Real.sqrt c) * (4 / Real.sqrt c) = 8 / c := by
      rw [div_mul_div_comm, show (2 : ℝ) * 4 = 8 by norm_num,
        show Real.sqrt c * Real.sqrt c = (Real.sqrt c) ^ 2 by rw [pow_two],
        Real.sq_sqrt hc.le]
    calc Real.tan (ρ / 2) / Real.tan (Real.sqrt (c / 4) / 2)
        = Real.tan (ρ / 2) * (Real.tan (Real.sqrt (c / 4) / 2))⁻¹ := div_eq_mul_inv _ _
      _ ≤ (2 / Real.sqrt c) * (4 / Real.sqrt c) :=
          mul_le_mul htan_rho hzinv (inv_nonneg.mpr hden_pos.le) hnum_nn
      _ = 8 / c := hfinal

end Work.Diff.C.geoCrux

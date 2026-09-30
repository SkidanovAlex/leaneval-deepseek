import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VKChain

/-- Elementary numeric bound for the far tail: with `σ ∈ [3/4, 2]`, `M ≥ |t|²` and `|t| ≥ 16`,
`(‖σ + i t‖/σ) (M+a)^{-σ} ≤ 1`. -/
theorem tail_piece_le_one {σ t M a : ℝ} (ha : 0 < a) (hσ34 : 3 / 4 ≤ σ) (hσ2 : σ ≤ 2)
    (hM : |t| ^ 2 ≤ M) (ht : 16 ≤ |t|) :
    ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ * (M + a) ^ (-σ) ≤ 1 := by
  have hσpos : 0 < σ := by linarith
  have htpos : 0 < |t| := lt_of_lt_of_le (by norm_num : (0:ℝ) < 16) ht
  have ht2nonneg : (0:ℝ) ≤ |t| ^ 2 := by positivity
  have hMge : 0 ≤ M := le_trans ht2nonneg hM
  have hBpos : 0 < M + a := by linarith
  have hB1 : 1 ≤ M + a := by
    have h16 : (16:ℝ) ^ 2 ≤ |t| ^ 2 := pow_le_pow_left₀ (by norm_num) ht 2
    linarith
  -- Step 1: bound the complex norm `‖σ + i t‖ ≤ 2 |t|`
  have hn2 : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
  have hsq : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 ≤ (2 * |t|) ^ 2 := by
    rw [hn2]
    have hσ2sq : σ ^ 2 ≤ 4 := by nlinarith [hσ2, hσ34]
    have h16 : (16:ℝ) ^ 2 ≤ |t| ^ 2 := pow_le_pow_left₀ (by norm_num) ht 2
    have habs : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith [hσ2sq, h16, habs]
  have hn_le : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2 * |t| := by
    have h1 : 0 ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_nonneg _
    have h2 : 0 ≤ 2 * |t| := by positivity
    have h3 := sq_le_sq.mp hsq
    rwa [abs_of_nonneg h1, abs_of_nonneg h2] at h3
  -- Step 2: `1/σ ≤ 4/3`, hence `‖σ + i t‖/σ ≤ (8/3)|t|`
  have hinvσ : σ⁻¹ ≤ 4/3 := by
    have h := (inv_le_inv₀ hσpos (by norm_num : (0:ℝ) < 3/4)).mpr hσ34
    rwa [show ((3:ℝ)/4)⁻¹ = 4/3 by norm_num] at h
  have hcomb1 : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ ≤ 2 * |t| * (4/3) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul hn_le hinvσ (inv_nonneg.mpr (le_of_lt hσpos)) (by positivity)
  -- Step 3: `(M+a)^{-σ} ≤ |t|^{-3/2}`
  have hB_le : (M + a) ^ (-σ) ≤ |t| ^ (-(3/2 : ℝ)) := by
    have e1 : (M + a) ^ (-σ) ≤ (M + a) ^ (-(3/4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
    have e2 : (M + a) ^ (-(3/4 : ℝ)) ≤ (|t| ^ 2) ^ (-(3/4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ) < |t| ^ 2) (by linarith) (by norm_num)
    have e3 : (|t| ^ 2) ^ (-(3/4 : ℝ)) = |t| ^ (-(3/2 : ℝ)) := by
      rw [← Real.rpow_natCast_mul (abs_nonneg t) 2 (-(3/4 : ℝ))]
      rw [show ((2:ℕ):ℝ) * (-(3/4 : ℝ)) = -(3/2 : ℝ) by norm_num]
    exact le_trans e1 (le_trans e2 (le_of_eq e3))
  have hfinal : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ * (M + a) ^ (-σ)
      ≤ (2 * |t| * (4/3)) * |t| ^ (-(3/2 : ℝ)) :=
    mul_le_mul hcomb1 hB_le (Real.rpow_nonneg (le_of_lt hBpos) _) (by positivity)
  refine le_trans hfinal ?_
  -- Step 4: elementary arithmetic `(8/3)|t| |t|^{-3/2} = (8/3)|t|^{-1/2} ≤ (8/3)/4 ≤ 1`
  have h4 : |t| * |t| ^ (-(3/2 : ℝ)) = |t| ^ (-(1/2 : ℝ)) := by
    calc |t| * |t| ^ (-(3/2 : ℝ))
        = |t| ^ (1:ℝ) * |t| ^ (-(3/2 : ℝ)) := by rw [Real.rpow_one]
      _ = |t| ^ ((1:ℝ) + (-(3/2 : ℝ))) := (Real.rpow_add htpos 1 (-(3/2 : ℝ))).symm
      _ = |t| ^ (-(1/2 : ℝ)) := by
            rw [show (1:ℝ) + (-(3/2 : ℝ)) = -(1/2 : ℝ) by norm_num]
  have h6 : (16:ℝ) ^ (-(1/2 : ℝ)) = 1/4 := by
    have h16 : (16:ℝ) = (4:ℝ) ^ 2 := by norm_num
    rw [h16, ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 4) 2 (-(1/2 : ℝ))]
    rw [show ((2:ℕ):ℝ) * (-(1/2 : ℝ)) = -(1:ℝ) by norm_num]
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4) 1, Real.rpow_one]
    norm_num
  calc (2 * |t| * (4/3)) * |t| ^ (-(3/2 : ℝ))
      = (8/3) * (|t| * |t| ^ (-(3/2 : ℝ))) := by ring
    _ = (8/3) * |t| ^ (-(1/2 : ℝ)) := by rw [h4]
    _ ≤ (8/3) * (1/4) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 8/3)
        calc |t| ^ (-(1/2 : ℝ)) ≤ (16:ℝ) ^ (-(1/2 : ℝ)) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 16) ht (by norm_num)
          _ = 1/4 := h6
    _ ≤ 1 := by norm_num

end Work.BMF.VKChain

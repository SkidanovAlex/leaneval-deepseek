import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.N8.scales_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

theorem scales_large (θ ε : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1 / 2) (hε : 0 < ε)
    (hεθ : ε ≤ θ / 100) :
    ∃ C : ℝ, 0 < C ∧ ∀ X H P₁ P₂ : ℝ, C ≤ X → X ^ θ ≤ H → H ≤ X ^ (1 - θ) →
      X ^ (ε ^ 2 / 2) ≤ P₁ → P₁ ≤ X ^ ε → X ^ (ε ^ 2 / 2) ≤ P₂ → P₂ ≤ X ^ ε →
      0 < X ∧ 1 ≤ X ∧ 0 < H ∧ 0 < P₁ ∧ 1 ≤ P₁ ∧ 0 < P₂ ∧ 4 ≤ P₂ ∧
      0 < P₁ * P₂ ∧ 10 ≤ P₁ * P₂ ∧ 1 ≤ Real.log X ∧
      0 < X / (P₁ * P₂) ∧ 10 ≤ X / (P₁ * P₂) ∧ 1 ≤ X / (P₁ * P₂) ∧
      X ^ (1 - 2 * ε) ≤ X / (P₁ * P₂) ∧ X / (P₁ * P₂) ≤ X ∧
      10 * X ^ (1 / 2 : ℝ) ≤ X / (P₁ * P₂) ∧ 10 * (X / (P₁ * P₂)) ≤ X ∧
      0 < X / H ∧ 3 ≤ X / H ∧ X / H ≤ X ^ (1 - θ) ∧
      0 < H / (P₁ * P₂) ∧ 1 ≤ H / (P₁ * P₂) ∧ X ^ (θ - 2 * ε) ≤ H / (P₁ * P₂) ∧
      X ^ (θ / 2) ≤ H / (P₁ * P₂) ∧ H / (P₁ * P₂) ≤ X / (P₁ * P₂) ∧
      H / (P₁ * P₂) ≤ X ^ (1 - θ) ∧ X ^ (1 / 2 : ℝ) ≤ X / (P₁ * P₂) ∧
      0 < Real.log P₁ ∧ 1 ≤ Real.log P₁ ∧ 0 < Real.log P₂ ∧ 0 < Real.log (P₂ / 2) ∧
      X ^ (ε ^ 2 / 2) / Real.log X ≤ Work.BMF.pi0 P₁ := by
  -- ## elementary consequences of the hypotheses on `ε`
  have hε1 : ε < 1 / 2 := by nlinarith [hεθ, hθ₁]
  have h1m2e : (0 : ℝ) < 1 - 2 * ε := by nlinarith
  have hhalf : (0 : ℝ) < 1 / 2 - 2 * ε := by nlinarith
  have hεle1 : ε ≤ 1 := by nlinarith [hεθ, hθ₁]
  have hεq : 2 * ε ≤ θ / 2 := by nlinarith [hεθ, hθ₀]
  have hεh : (1 / 2 : ℝ) ≤ 1 - 2 * ε := by nlinarith [hεθ, hθ₁]
  have hεq0 : 2 * ε ≤ θ := by nlinarith [hεθ, hθ₀]
  -- ## the threshold constant
  refine ⟨Real.exp (scalesM θ ε), Real.exp_pos _, ?_⟩
  intro X H P₁ P₂ hCX hHlo hHhi hP1lo hP1hi hP2lo hP2hi
  -- ## nonnegativity of the individual summands of `scalesM θ ε`
  have h3 : (0 : ℝ) ≤ Real.log 3 / θ := div_nonneg (Real.log_nonneg (by norm_num)) hθ₀.le
  have h4 : (0 : ℝ) ≤ Real.log 4 / (ε ^ 2 / 2) :=
    div_nonneg (Real.log_nonneg (by norm_num)) (by positivity)
  have h10 : (0 : ℝ) ≤ Real.log 10 / ε ^ 2 :=
    div_nonneg (Real.log_nonneg (by norm_num)) (by positivity)
  have hb1 : (0 : ℝ) ≤ Real.log 10 / (1 - 2 * ε) :=
    div_nonneg (Real.log_nonneg (by norm_num)) h1m2e.le
  have hb2 : (0 : ℝ) ≤ Real.log 10 / (1 / 2 - 2 * ε) :=
    div_nonneg (Real.log_nonneg (by norm_num)) hhalf.le
  have hM1 : (1 : ℝ) ≤ scalesM θ ε := by rw [scalesM]; linarith
  have hM3' : Real.log 3 / θ ≤ scalesM θ ε := by rw [scalesM]; linarith
  have hM4' : Real.log 4 / (ε ^ 2 / 2) ≤ scalesM θ ε := by rw [scalesM]; linarith
  have hMe2' : Real.log 10 / ε ^ 2 ≤ scalesM θ ε := by rw [scalesM]; linarith
  have hMb1' : Real.log 10 / (1 - 2 * ε) ≤ scalesM θ ε := by rw [scalesM]; linarith
  have hMb2' : Real.log 10 / (1 / 2 - 2 * ε) ≤ scalesM θ ε := by rw [scalesM]; linarith
  have hM3 : Real.log 3 ≤ θ * scalesM θ ε := by
    have h := mul_le_mul_of_nonneg_left hM3' hθ₀.le
    rwa [mul_div_cancel₀ (Real.log 3) hθ₀.ne'] at h
  have hM4 : Real.log 4 ≤ (ε ^ 2 / 2) * scalesM θ ε := by
    have h := mul_le_mul_of_nonneg_left hM4' (by positivity : (0 : ℝ) ≤ ε ^ 2 / 2)
    rwa [mul_div_cancel₀ (Real.log 4) (by positivity : (ε ^ 2 / 2) ≠ 0)] at h
  have hMe2 : Real.log 10 ≤ ε ^ 2 * scalesM θ ε := by
    have h := mul_le_mul_of_nonneg_left hMe2' (sq_nonneg ε)
    rwa [mul_div_cancel₀ (Real.log 10) (by positivity : (ε ^ 2) ≠ 0)] at h
  have hMb1 : Real.log 10 ≤ (1 - 2 * ε) * scalesM θ ε := by
    have h := mul_le_mul_of_nonneg_left hMb1' h1m2e.le
    rwa [mul_div_cancel₀ (Real.log 10) h1m2e.ne'] at h
  have hMb2 : Real.log 10 ≤ (1 / 2 - 2 * ε) * scalesM θ ε := by
    have h := mul_le_mul_of_nonneg_left hMb2' hhalf.le
    rwa [mul_div_cancel₀ (Real.log 10) hhalf.ne'] at h
  -- ## `X ≥ exp (scalesM θ ε)` gives `X` large
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hCX
  have hlogXleM : scalesM θ ε ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos (scalesM θ ε)) hCX
    rwa [Real.log_exp] at h
  have hX1 : 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ Real.exp (scalesM θ ε) := by
      calc (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        _ ≤ Real.exp (scalesM θ ε) := Real.exp_le_exp.mpr hM1
    linarith
  -- ## transfer the `scalesM` bounds to `X`
  have hbound : ∀ a b : ℝ, 0 ≤ a → (0 : ℝ) < b → Real.log b ≤ a * scalesM θ ε → b ≤ X ^ a := by
    intro a b ha hb hlogb
    calc b = Real.exp (Real.log b) := (Real.exp_log hb).symm
      _ ≤ Real.exp (a * scalesM θ ε) := Real.exp_le_exp.mpr hlogb
      _ ≤ Real.exp (a * Real.log X) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlogXleM ha)
      _ = X ^ a := by rw [Real.rpow_def_of_pos hXpos a, mul_comm]
  have hXθ : 3 ≤ X ^ θ := hbound θ 3 hθ₀.le (by norm_num) hM3
  have hX4 : 4 ≤ X ^ (ε ^ 2 / 2) := hbound (ε ^ 2 / 2) 4 (by positivity) (by norm_num) hM4
  have hXe2 : 10 ≤ X ^ (ε ^ 2) := hbound (ε ^ 2) 10 (by positivity) (by norm_num) hMe2
  have hXa : 10 ≤ X ^ (1 - 2 * ε) := hbound (1 - 2 * ε) 10 h1m2e.le (by norm_num) hMb1
  have hXb : 10 ≤ X ^ (1 / 2 - 2 * ε) := hbound (1 / 2 - 2 * ε) 10 hhalf.le (by norm_num) hMb2
  have hlogX1 : 1 ≤ Real.log X := le_trans hM1 hlogXleM
  have hlogX0 : 0 < Real.log X := lt_of_lt_of_le (by norm_num) hlogX1
  -- ## the `P₁`, `P₂` and product bounds
  have hP1ge4 : 4 ≤ P₁ := le_trans hX4 hP1lo
  have hP1pos : 0 < P₁ := lt_of_lt_of_le (by norm_num) hP1ge4
  have hP1ge1 : 1 ≤ P₁ := le_trans (by norm_num) hP1ge4
  have hP2ge4 : 4 ≤ P₂ := le_trans hX4 hP2lo
  have hP2pos : 0 < P₂ := lt_of_lt_of_le (by norm_num) hP2ge4
  have hP2ge1 : 1 ≤ P₂ := le_trans (by norm_num) hP2ge4
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) (le_trans hXθ hHlo)
  have hPprodpos : 0 < P₁ * P₂ := mul_pos hP1pos hP2pos
  have hPprodge1 : 1 ≤ P₁ * P₂ := by
    have h := mul_le_mul hP1ge1 hP2ge1 (by norm_num : (0 : ℝ) ≤ 1) hP1pos.le
    simpa using h
  have hPprod_le : P₁ * P₂ ≤ X ^ (2 * ε) := by
    have h1 : P₁ * P₂ ≤ X ^ ε * X ^ ε :=
      mul_le_mul hP1hi hP2hi hP2pos.le (le_of_lt (Real.rpow_pos_of_pos hXpos ε))
    have h2 : X ^ ε * X ^ ε = X ^ (2 * ε) := by
      rw [← Real.rpow_add hXpos, show ε + ε = 2 * ε by ring]
    rwa [h2] at h1
  have hPprod_ge : X ^ (ε ^ 2) ≤ P₁ * P₂ := by
    have h1 : X ^ (ε ^ 2 / 2) * X ^ (ε ^ 2 / 2) ≤ P₁ * P₂ :=
      mul_le_mul hP1lo hP2lo (le_of_lt (Real.rpow_pos_of_pos hXpos _)) hP1pos.le
    have h2 : X ^ (ε ^ 2) = X ^ (ε ^ 2 / 2) * X ^ (ε ^ 2 / 2) := by
      rw [← Real.rpow_add hXpos, show ε ^ 2 / 2 + ε ^ 2 / 2 = ε ^ 2 by ring]
    rwa [h2]
  have hPprodge10 : 10 ≤ P₁ * P₂ := le_trans hXe2 hPprod_ge
  -- ## `X / (P₁ * P₂)`
  have hXoverpos : 0 < X / (P₁ * P₂) := div_pos hXpos hPprodpos
  have hXa_le : X ^ (1 - 2 * ε) ≤ X / (P₁ * P₂) := by
    have h0 : X ^ (1 - 2 * ε) = X / X ^ (2 * ε) := by
      rw [Real.rpow_sub hXpos, Real.rpow_one]
    rw [h0]
    exact div_le_div_of_nonneg_left hXpos.le hPprodpos hPprod_le
  have hXover10 : 10 ≤ X / (P₁ * P₂) := le_trans hXa hXa_le
  have hXover1 : 1 ≤ X / (P₁ * P₂) := le_trans (by norm_num) hXover10
  have hXover_le : X / (P₁ * P₂) ≤ X := by
    rw [div_le_iff₀ hPprodpos]
    calc X = X * 1 := by ring
      _ ≤ X * (P₁ * P₂) := mul_le_mul_of_nonneg_left hPprodge1 hXpos.le
  have h16 : 10 * X ^ (1 / 2 : ℝ) ≤ X / (P₁ * P₂) := by
    have h1 : 10 * X ^ (1 / 2 : ℝ) ≤ X ^ (1 / 2 - 2 * ε) * X ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hXb (le_of_lt (Real.rpow_pos_of_pos hXpos (1 / 2)))
    have h2 : X ^ (1 / 2 - 2 * ε) * X ^ (1 / 2 : ℝ) = X ^ (1 - 2 * ε) := by
      rw [← Real.rpow_add hXpos, show (1 / 2 - 2 * ε) + 1 / 2 = 1 - 2 * ε by ring]
    rw [h2] at h1
    exact le_trans h1 hXa_le
  have h17 : 10 * (X / (P₁ * P₂)) ≤ X := by
    rw [show 10 * (X / (P₁ * P₂)) = 10 * X / (P₁ * P₂) by ring, div_le_iff₀ hPprodpos]
    calc 10 * X = X * 10 := by ring
      _ ≤ X * (P₁ * P₂) := mul_le_mul_of_nonneg_left hPprodge10 hXpos.le
  -- ## `X / H`
  have hXHpos : 0 < X / H := div_pos hXpos hHpos
  have hHX : H * X ^ θ ≤ X := by
    calc H * X ^ θ ≤ X ^ (1 - θ) * X ^ θ :=
          mul_le_mul_of_nonneg_right hHhi (le_of_lt (Real.rpow_pos_of_pos hXpos θ))
      _ = X := by
          rw [← Real.rpow_add hXpos, show (1 - θ) + θ = 1 by ring, Real.rpow_one]
  have hHXle : X ≤ H * X ^ (1 - θ) := by
    calc X = X ^ θ * X ^ (1 - θ) := by
          rw [← Real.rpow_add hXpos, show θ + (1 - θ) = 1 by ring, Real.rpow_one]
      _ ≤ H * X ^ (1 - θ) :=
          mul_le_mul_of_nonneg_right hHlo (le_of_lt (Real.rpow_pos_of_pos hXpos (1 - θ)))
  have h19 : 3 ≤ X / H := by
    have h : X ^ θ ≤ X / H := by
      rw [le_div_iff₀ hHpos]
      calc X ^ θ * H = H * X ^ θ := by ring
        _ ≤ X := hHX
    exact le_trans hXθ h
  have h20 : X / H ≤ X ^ (1 - θ) := by
    rw [div_le_iff₀ hHpos]
    calc X ≤ H * X ^ (1 - θ) := hHXle
      _ = X ^ (1 - θ) * H := by ring
  -- ## `H / (P₁ * P₂)`
  have hHoverpos : 0 < H / (P₁ * P₂) := div_pos hHpos hPprodpos
  have h23 : X ^ (θ - 2 * ε) ≤ H / (P₁ * P₂) := by
    rw [le_div_iff₀ hPprodpos]
    calc X ^ (θ - 2 * ε) * (P₁ * P₂) ≤ X ^ (θ - 2 * ε) * X ^ (2 * ε) :=
          mul_le_mul_of_nonneg_left hPprod_le (le_of_lt (Real.rpow_pos_of_pos hXpos _))
      _ = X ^ θ := by
          rw [← Real.rpow_add hXpos, show (θ - 2 * ε) + 2 * ε = θ by ring]
      _ ≤ H := hHlo
  have h22 : 1 ≤ H / (P₁ * P₂) := by
    have h1 : (1 : ℝ) ≤ X ^ (θ - 2 * ε) := Real.one_le_rpow hX1 (by linarith)
    exact le_trans h1 h23
  have h24 : X ^ (θ / 2) ≤ H / (P₁ * P₂) := by
    have hθexp : θ / 2 ≤ θ - 2 * ε := by linarith
    exact le_trans (Real.rpow_le_rpow_of_exponent_le hX1 hθexp) h23
  have hHleX : H ≤ X := by
    have h1 : X ^ (1 - θ) ≤ X ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    rw [Real.rpow_one] at h1
    exact le_trans hHhi h1
  have h25 : H / (P₁ * P₂) ≤ X / (P₁ * P₂) :=
    div_le_div_of_nonneg_right hHleX hPprodpos.le
  have h26 : H / (P₁ * P₂) ≤ X ^ (1 - θ) := by
    rw [div_le_iff₀ hPprodpos]
    calc H ≤ X ^ (1 - θ) := hHhi
      _ = X ^ (1 - θ) * 1 := by ring
      _ ≤ X ^ (1 - θ) * (P₁ * P₂) :=
          mul_le_mul_of_nonneg_left hPprodge1 (Real.rpow_nonneg hXpos.le (1 - θ))
  have h27 : X ^ (1 / 2 : ℝ) ≤ X / (P₁ * P₂) :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hX1 hεh) hXa_le
  -- ## the logarithmic bounds
  have h28 : 0 < Real.log P₁ :=
    lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 4))
      (Real.log_le_log (by norm_num : (0 : ℝ) < 4) hP1ge4)
  have h29 : 1 ≤ Real.log P₁ :=
    (Real.le_log_iff_exp_le hP1pos).mpr (by linarith [Real.exp_one_lt_d9, hP1ge4])
  have h30 : 0 < Real.log P₂ := Real.log_pos (by linarith)
  have h31 : 0 < Real.log (P₂ / 2) := Real.log_pos (by linarith)
  -- ## the `π₀` bound
  have hXe_le_X : X ^ ε ≤ X := by
    have h1 := Real.rpow_le_rpow_of_exponent_le hX1 hεle1
    rwa [Real.rpow_one] at h1
  have hlogP1_le : Real.log P₁ ≤ Real.log X :=
    Real.log_le_log hP1pos (le_trans hP1hi hXe_le_X)
  have h32 : X ^ (ε ^ 2 / 2) / Real.log X ≤ Work.BMF.pi0 P₁ := by
    show X ^ (ε ^ 2 / 2) / Real.log X ≤ P₁ / Real.log P₁
    rw [div_le_div_iff₀ hlogX0 h28]
    calc X ^ (ε ^ 2 / 2) * Real.log P₁ ≤ X ^ (ε ^ 2 / 2) * Real.log X :=
          mul_le_mul_of_nonneg_left hlogP1_le (Real.rpow_nonneg hXpos.le _)
      _ ≤ P₁ * Real.log X := mul_le_mul_of_nonneg_right hP1lo hlogX0.le
  exact ⟨hXpos, hX1, hHpos, hP1pos, hP1ge1, hP2pos, hP2ge4, hPprodpos, hPprodge10, hlogX1,
    hXoverpos, hXover10, hXover1, hXa_le, hXover_le, h16, h17,
    hXHpos, h19, h20, hHoverpos, h22, h23, h24, h25, h26, h27,
    h28, h29, h30, h31, h32⟩

end Work.N8

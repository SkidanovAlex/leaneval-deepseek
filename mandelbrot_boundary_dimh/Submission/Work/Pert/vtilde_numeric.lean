import Mathlib

namespace Work.Pert

/-- `exp t - 1 ≤ (33/32) t` for `0 ≤ t ≤ 1/64` (Taylor: `exp t ≤ 1 + t + 3t²/4`). -/
private lemma exp_sub_one_le_ratio {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 64) :
    Real.exp t - 1 ≤ (33 / 32) * t := by
  have hb := Real.exp_bound' (x := t) h0 (le_trans h1 (by norm_num)) (n := 2) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  nlinarith [hb, h0, h1]

/-- `‖exp x - 1‖ ≥ ‖x‖ (1 - ‖x‖)` for `‖x‖ ≤ 1`. -/
private lemma norm_exp_sub_one_ge (x : ℂ) (hx : ‖x‖ ≤ 1) :
    ‖x‖ * (1 - ‖x‖) ≤ ‖Complex.exp x - 1‖ := by
  have htail : ‖Complex.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hx
  have h := norm_sub_norm_le x (Complex.exp x - 1)
  have he : x - (Complex.exp x - 1) = -(Complex.exp x - 1 - x) := by ring
  rw [he, norm_neg] at h
  nlinarith [h, htail]

/-- `‖exp x - 1‖ ≤ (33/32) ‖x‖` for `‖x‖ ≤ 1/64`. -/
private lemma norm_exp_sub_one_le_ratio (x : ℂ) (hx : ‖x‖ ≤ 1 / 64) :
    ‖Complex.exp x - 1‖ ≤ (33 / 32) * ‖x‖ := by
  have h1 : ‖Complex.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
    simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum x 1
  have h2 : Real.exp ‖x‖ - 1 ≤ (33 / 32) * ‖x‖ := exp_sub_one_le_ratio (norm_nonneg x) hx
  linarith

theorem vtilde_numeric {σ α τ uτ u0 W : ℂ}
    (hα : α ≠ 0) (hh : 1 + τ * uτ ≠ 0)
    (hαs : 2 * Real.pi * ‖α‖ ≤ 1 / 64) (hu0 : ‖u0 - 1‖ ≤ 1 / 1024) (hτ : ‖τ‖ ≤ 1 / 8)
    (hW : ‖W‖ ≤ 1 / 32)
    (hident : ‖Complex.exp (2 * Real.pi * Complex.I * α * W) - 1‖
      = ‖Complex.exp (-(2 * Real.pi * Complex.I * α)) - 1‖
        * ‖τ * uτ * u0 - (uτ - u0)‖ / (‖u0‖ * ‖1 + τ * uτ‖)) :
    ‖W‖ ≤ (3 / 2) * (‖τ‖ * ‖uτ‖ + ‖uτ - u0‖ / ‖u0‖) := by
  set w : ℂ := 2 * Real.pi * Complex.I * α with hw
  set z : ℂ := w * W with hz
  set B : ℝ := ‖τ * uτ * u0 - (uτ - u0)‖ / (‖u0‖ * ‖1 + τ * uτ‖) with hB
  set S : ℝ := ‖τ‖ * ‖uτ‖ + ‖uτ - u0‖ / ‖u0‖ with hS
  -- ## basic norms
  have hwnorm : ‖w‖ = 2 * Real.pi * ‖α‖ := by
    rw [hw, norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_I, mul_one, Complex.norm_ofNat]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hwpos : 0 < ‖w‖ := by rw [hwnorm]; positivity
  have hw64 : ‖w‖ ≤ 1 / 64 := by rw [hwnorm]; exact hαs
  have hznorm : ‖z‖ = ‖w‖ * ‖W‖ := by rw [hz, norm_mul]
  have hWnn : 0 ≤ ‖W‖ := norm_nonneg W
  have hzle : ‖z‖ ≤ 1 / 2048 := by
    rw [hznorm]
    nlinarith [hw64, hW, norm_nonneg w, norm_nonneg W]
  have hz1 : ‖z‖ ≤ 1 := by linarith [hzle]
  have hz64 : ‖z‖ ≤ 1 / 64 := by linarith [hzle]
  have hzge : (2047 / 2048 : ℝ) ≤ 1 - ‖z‖ := by linarith [hzle]
  -- ## rewrite `hident` in local notation
  have hid : ‖Complex.exp z - 1‖ = ‖Complex.exp (-w) - 1‖ * B := by
    have h1 : ‖Complex.exp z - 1‖
        = (‖Complex.exp (-w) - 1‖ * ‖τ * uτ * u0 - (uτ - u0)‖) / (‖u0‖ * ‖1 + τ * uτ‖) := by
      rw [hz, hw]; exact hident
    rw [h1, hB]
    ring
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact div_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  -- ## (i) `‖W‖ ≤ (33/32)·(2048/2047)·B`
  have hAub : ‖Complex.exp (-w) - 1‖ ≤ (33 / 32) * ‖w‖ := by
    have h := norm_exp_sub_one_le_ratio (-w) (by rw [norm_neg]; exact hw64)
    rwa [norm_neg] at h
  have hC1 : ‖W‖ ≤ (33 / 32) * (2048 / 2047) * B := by
    have hkey : (‖w‖ * ‖W‖) * (1 - ‖z‖) ≤ ((33 / 32) * ‖w‖) * B := by
      calc (‖w‖ * ‖W‖) * (1 - ‖z‖) = ‖z‖ * (1 - ‖z‖) := by rw [hznorm]
        _ ≤ ‖Complex.exp z - 1‖ := norm_exp_sub_one_ge z hz1
        _ = ‖Complex.exp (-w) - 1‖ * B := hid
        _ ≤ ((33 / 32) * ‖w‖) * B := mul_le_mul_of_nonneg_right hAub hBnn
    have e1 : (‖w‖ * ‖W‖) * (1 - ‖z‖) = ‖w‖ * (‖W‖ * (1 - ‖z‖)) := by ring
    have e2 : ((33 / 32) * ‖w‖) * B = ‖w‖ * ((33 / 32) * B) := by ring
    rw [e1, e2] at hkey
    have h2 : ‖W‖ * (1 - ‖z‖) ≤ (33 / 32) * B := le_of_mul_le_mul_left hkey hwpos
    have h3 : ‖W‖ * (2047 / 2048) ≤ (33 / 32) * B := by
      have h := mul_le_mul_of_nonneg_left hzge hWnn
      linarith
    have hpos : (0 : ℝ) < 2047 / 2048 := by norm_num
    have h4 := (le_div_iff₀ hpos).mpr h3
    have he : ((33 / 32) * B) / (2047 / 2048) = (33 / 32) * (2048 / 2047) * B := by
      field_simp
    linarith [h4, he]
  -- ## (ii) `B ≤ (33/32)·(64/63)·‖W‖`
  have hhu0pos : 0 < ‖u0‖ := by
    have h : ‖(1 : ℂ)‖ - ‖u0‖ ≤ ‖(1 : ℂ) - u0‖ := norm_sub_norm_le (1 : ℂ) u0
    rw [norm_one] at h
    have h2 : ‖(1 : ℂ) - u0‖ = ‖u0 - 1‖ := norm_sub_rev _ _
    linarith [h, h2, hu0]
  have hAlb : (63 / 64) * ‖w‖ ≤ ‖Complex.exp (-w) - 1‖ := by
    have h := norm_exp_sub_one_ge (-w) (by rw [norm_neg]; linarith [hw64])
    rw [norm_neg] at h
    have h2 : (63 / 64 : ℝ) ≤ 1 - ‖w‖ := by linarith [hw64]
    have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg w)
    linarith
  have hAlbpos : 0 < (63 / 64) * ‖w‖ := mul_pos (by norm_num) hwpos
  have hApos : 0 < ‖Complex.exp (-w) - 1‖ := lt_of_lt_of_le hAlbpos hAlb
  have hBub : B ≤ (33 / 32) * (64 / 63) * ‖W‖ := by
    have hB_eq : B = ‖Complex.exp z - 1‖ / ‖Complex.exp (-w) - 1‖ := by
      rw [eq_div_iff (ne_of_gt hApos)]
      rw [mul_comm]
      exact hid.symm
    rw [hB_eq]
    have hnumub : ‖Complex.exp z - 1‖ ≤ (33 / 32) * ‖z‖ := norm_exp_sub_one_le_ratio z hz64
    have h1a : ((33 / 32) * ‖z‖) / ‖Complex.exp (-w) - 1‖ ≤ ((33 / 32) * ‖z‖) / ((63 / 64) * ‖w‖) :=
      div_le_div_of_nonneg_left (by positivity) hAlbpos hAlb
    have h1b : ‖Complex.exp z - 1‖ / ‖Complex.exp (-w) - 1‖
        ≤ ((33 / 32) * ‖z‖) / ‖Complex.exp (-w) - 1‖ :=
      div_le_div_of_nonneg_right hnumub (le_of_lt hApos)
    have h2 : ((33 / 32) * ‖z‖) / ((63 / 64) * ‖w‖) = (33 / 32) * (64 / 63) * ‖W‖ := by
      rw [hznorm]
      field_simp
    linarith [h1a, h1b, h2]
  -- ## the case analysis bounding `B` by `S`
  have hSnn : 0 ≤ S := by
    rw [hS]
    have h1 : (0 : ℝ) ≤ ‖τ‖ * ‖uτ‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have h2 : 0 ≤ ‖uτ - u0‖ / ‖u0‖ := div_nonneg (norm_nonneg _) (le_of_lt hhu0pos)
    linarith
  have hBcase : B ≤ (21 / 20) * S := by
    by_cases hM : (1 : ℝ) / 32 ≤ ‖τ‖ * ‖uτ‖
    · have hSge : (1 : ℝ) / 32 ≤ S := by
        rw [hS]
        have h : 0 ≤ ‖uτ - u0‖ / ‖u0‖ := div_nonneg (norm_nonneg _) (le_of_lt hhu0pos)
        linarith
      calc B ≤ (33 / 32) * (64 / 63) * ‖W‖ := hBub
        _ ≤ (33 / 32) * (64 / 63) * (1 / 32) := mul_le_mul_of_nonneg_left hW (by norm_num)
        _ ≤ (21 / 20) * (1 / 32) := by norm_num
        _ ≤ (21 / 20) * S := mul_le_mul_of_nonneg_left hSge (by norm_num)
    · push_neg at hM
      have hpt : (0 : ℝ) < ‖1 + τ * uτ‖ := norm_pos_iff.mpr hh
      have hp_lb : (31 / 32 : ℝ) ≤ ‖1 + τ * uτ‖ := by
        have h1 : (1 : ℝ) ≤ ‖1 + τ * uτ‖ + ‖τ * uτ‖ := by
          have h := norm_sub_le (1 + τ * uτ) (τ * uτ)
          have he : (1 + τ * uτ) - τ * uτ = 1 := by ring
          rw [he, norm_one] at h
          exact h
        have h2 : ‖τ * uτ‖ ≤ 1 / 32 := by rw [norm_mul]; exact le_of_lt hM
        linarith
      have hnum2 : ‖τ * uτ * u0 - (uτ - u0)‖ ≤ ‖u0‖ * S := by
        rw [hS]
        have hnum : ‖τ * uτ * u0 - (uτ - u0)‖ ≤ ‖τ‖ * ‖uτ‖ * ‖u0‖ + ‖uτ - u0‖ := by
          have he : τ * uτ * u0 - (uτ - u0) = τ * uτ * u0 + (u0 - uτ) := by ring
          rw [he]
          calc ‖τ * uτ * u0 + (u0 - uτ)‖ ≤ ‖τ * uτ * u0‖ + ‖u0 - uτ‖ := norm_add_le _ _
            _ = ‖τ‖ * ‖uτ‖ * ‖u0‖ + ‖uτ - u0‖ := by
                rw [norm_mul, norm_mul, norm_sub_rev]
        have he : ‖u0‖ * (‖τ‖ * ‖uτ‖ + ‖uτ - u0‖ / ‖u0‖)
            = ‖τ‖ * ‖uτ‖ * ‖u0‖ + ‖uτ - u0‖ := by
          field_simp
        linarith [hnum, he]
      have hB_le : B ≤ S / ‖1 + τ * uτ‖ := by
        rw [hB]
        have hden : (0 : ℝ) < ‖u0‖ * ‖1 + τ * uτ‖ := mul_pos hhu0pos hpt
        have h1 : ‖τ * uτ * u0 - (uτ - u0)‖ / (‖u0‖ * ‖1 + τ * uτ‖)
            ≤ (‖u0‖ * S) / (‖u0‖ * ‖1 + τ * uτ‖) :=
          div_le_div_of_nonneg_right hnum2 (le_of_lt hden)
        have h2 : (‖u0‖ * S) / (‖u0‖ * ‖1 + τ * uτ‖) = S / ‖1 + τ * uτ‖ := by
          field_simp
        linarith [h1, h2]
      have hfin : S / ‖1 + τ * uτ‖ ≤ (21 / 20) * S := by
        have h1 : S / ‖1 + τ * uτ‖ ≤ S / (31 / 32) :=
          div_le_div_of_nonneg_left hSnn (by norm_num) hp_lb
        have he : S / (31 / 32) = (32 / 31) * S := by
          field_simp
        have h2 : (32 / 31) * S ≤ (21 / 20) * S :=
          mul_le_mul_of_nonneg_right (by norm_num) hSnn
        linarith [h1, he, h2]
      linarith [hB_le, hfin]
  -- ## assembly
  have hfinal : ‖W‖ ≤ (3 / 2) * S := by
    calc ‖W‖ ≤ (33 / 32) * (2048 / 2047) * B := hC1
      _ ≤ (33 / 32) * (2048 / 2047) * ((21 / 20) * S) :=
            mul_le_mul_of_nonneg_left hBcase (by norm_num)
      _ = (33 / 32) * (2048 / 2047) * (21 / 20) * S := by ring
      _ ≤ (3 / 2) * S := mul_le_mul_of_nonneg_right (by norm_num) hSnn
  simpa only [hS] using hfinal

end Work.Pert

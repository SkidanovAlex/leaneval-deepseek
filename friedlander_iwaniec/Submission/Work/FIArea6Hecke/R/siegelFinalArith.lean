import Mathlib

namespace Work.FIArea6Hecke.R

theorem siegelFinalArith (ε : ℝ) (hε : 0 < ε) :
    ∀ (d₁ d : ℕ) (c₃ β₁ B K D A x : ℝ),
      1 ≤ d₁ → 1 ≤ d → 0 < c₃ → 0 < β₁ → β₁ < 1 → 0 < B →
      1 ≤ A → 1 ≤ K → 0 < D →
      200 * (1 - β₁) ≤ ε / 8 →
      B * (d : ℝ) ^ (-(ε / 8)) ≤ (max (d₁ : ℝ) (d : ℝ)) ^ (-(200 * (1 - β₁))) →
      K ≤ A * (d : ℝ) ^ (ε / 400) →
      D ≤ A * (d : ℝ) ^ (3 * ε / 8) →
      c₃ * (1 - β₁) * K ^ (-(200 : ℝ)) * (max (d₁ : ℝ) (d : ℝ)) ^ (-(200 * (1 - β₁)))
        ≤ x * D →
      c₃ * (1 - β₁) * B / (A * A ^ (200 : ℕ)) / (d : ℝ) ^ ε ≤ x := by
  intro d₁ d c₃ β₁ B K D A x hd₁ hd hc₃ hβ₁pos hβ₁lt hB hA hK hD h4 h5 h6 h7 h8
  set M : ℝ := max (d₁ : ℝ) (d : ℝ) with hM
  set s : ℝ := 200 * (1 - β₁) with hs
  have hmβ : 0 < 1 - β₁ := by linarith
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM]; exact le_trans (by exact_mod_cast hd) (le_max_right _ _)
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  have hd1r : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := lt_of_lt_of_le one_pos hd1r
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  have hcfac : 0 < c₃ * (1 - β₁) := by positivity
  -- positivity of the building blocks
  have hMblk : 0 < M ^ (-s) := Real.rpow_pos_of_pos hMpos (-s)
  have hd8 : 0 < (d : ℝ) ^ (ε / 8) := Real.rpow_pos_of_pos hdpos (ε / 8)
  have hd38 : 0 < (d : ℝ) ^ (3 * ε / 8) := Real.rpow_pos_of_pos hdpos (3 * ε / 8)
  have hd2 : 0 < (d : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos hdpos (ε / 2)
  have hdeps : 0 < (d : ℝ) ^ ε := Real.rpow_pos_of_pos hdpos ε
  have hA200 : 0 < A ^ (200 : ℕ) := by positivity
  have hK200 : 0 < (K : ℝ) ^ (200 : ℕ) := by positivity
  -- (1) `B ≤ M^{-s} · d^{ε/8}` from the hypothesis `h5`.
  have hdle : (d : ℝ) ^ (-(ε / 8)) * (d : ℝ) ^ (ε / 8) = 1 := by
    rw [← Real.rpow_add hdpos, show -(ε / 8) + ε / 8 = 0 by ring, Real.rpow_zero]
  have hB_le : B ≤ M ^ (-s) * (d : ℝ) ^ (ε / 8) := by
    have h := mul_le_mul_of_nonneg_right h5 hd8.le
    rw [mul_assoc, hdle, mul_one] at h
    exact h
  -- (2) `B·D ≤ M^{-s}·A·d^{ε/2}` combining `h5` and `h7`.
  have hpowmid : (d : ℝ) ^ (ε / 8) * (d : ℝ) ^ (3 * ε / 8) = (d : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hdpos, show ε / 8 + 3 * ε / 8 = ε / 2 by ring]
  have hBD : B * D ≤ M ^ (-s) * A * (d : ℝ) ^ (ε / 2) := by
    have h1 : B * D ≤ (M ^ (-s) * (d : ℝ) ^ (ε / 8)) * (A * (d : ℝ) ^ (3 * ε / 8)) :=
      mul_le_mul hB_le h7 hD.le (mul_pos hMblk hd8).le
    have h2 : (M ^ (-s) * (d : ℝ) ^ (ε / 8)) * (A * (d : ℝ) ^ (3 * ε / 8))
        = M ^ (-s) * A * (d : ℝ) ^ (ε / 2) := by
      rw [show (M ^ (-s) * (d : ℝ) ^ (ε / 8)) * (A * (d : ℝ) ^ (3 * ε / 8))
            = (M ^ (-s) * A) * ((d : ℝ) ^ (ε / 8) * (d : ℝ) ^ (3 * ε / 8)) by ring,
          hpowmid]
    exact le_trans h1 (le_of_eq h2)
  -- (3) `K^200 ≤ A^200 · d^{ε/2}` from `h6`.
  have hdsq : (d : ℝ) ^ (ε / 2) * (d : ℝ) ^ (ε / 2) = (d : ℝ) ^ ε := by
    rw [← Real.rpow_add hdpos, show ε / 2 + ε / 2 = ε by ring]
  have hK200_le : (K : ℝ) ^ (200 : ℕ) ≤ A ^ (200 : ℕ) * (d : ℝ) ^ (ε / 2) := by
    have hp := pow_le_pow_left₀ hKpos.le h6 200
    have he : (A * (d : ℝ) ^ (ε / 400)) ^ (200 : ℕ) = A ^ (200 : ℕ) * (d : ℝ) ^ (ε / 2) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast ((d : ℝ) ^ (ε / 400)) 200, ← Real.rpow_mul hdpos.le]
      congr 1
      ring
    rw [he] at hp
    exact hp
  -- (4) `d^{ε/2} ≤ K^{-200}·A^200·d^ε`.
  have hKneg : K ^ (-(200 : ℝ)) = ((K : ℝ) ^ (200 : ℕ))⁻¹ := by
    rw [Real.rpow_neg (x := K) hKpos.le]
    simp
  have hstep : (d : ℝ) ^ (ε / 2) ≤ K ^ (-(200 : ℝ)) * A ^ (200 : ℕ) * (d : ℝ) ^ ε := by
    rw [hKneg]
    rw [show ((K : ℝ) ^ (200 : ℕ))⁻¹ * A ^ (200 : ℕ) * (d : ℝ) ^ ε
          = ((K : ℝ) ^ (200 : ℕ))⁻¹ * (A ^ (200 : ℕ) * (d : ℝ) ^ ε) by ring]
    rw [le_inv_mul_iff₀ hK200]
    calc ((K : ℝ) ^ (200 : ℕ)) * (d : ℝ) ^ (ε / 2)
        = (d : ℝ) ^ (ε / 2) * ((K : ℝ) ^ (200 : ℕ)) := by ring
      _ ≤ (d : ℝ) ^ (ε / 2) * (A ^ (200 : ℕ) * (d : ℝ) ^ (ε / 2)) :=
            mul_le_mul_of_nonneg_left hK200_le hd2.le
      _ = A ^ (200 : ℕ) * ((d : ℝ) ^ (ε / 2) * (d : ℝ) ^ (ε / 2)) := by ring
      _ = A ^ (200 : ℕ) * (d : ℝ) ^ ε := by rw [hdsq]
  -- (5) the cross-multiplied inequality `B·D ≤ K^{-200}·M^{-s}·A·A^200·d^ε`.
  have hcross : B * D
      ≤ (K ^ (-(200 : ℝ)) * M ^ (-s)) * ((A * A ^ (200 : ℕ)) * (d : ℝ) ^ ε) := by
    have h := mul_le_mul_of_nonneg_left hstep (mul_pos hMblk hApos).le
    have he : M ^ (-s) * A * (K ^ (-(200 : ℝ)) * A ^ (200 : ℕ) * (d : ℝ) ^ ε)
        = (K ^ (-(200 : ℝ)) * M ^ (-s)) * ((A * A ^ (200 : ℕ)) * (d : ℝ) ^ ε) := by
      ring
    exact le_trans (le_trans hBD h) (le_of_eq he)
  -- (6) the lower bound on `x` coming from `h8`.
  have hx : c₃ * (1 - β₁) * K ^ (-(200 : ℝ)) * M ^ (-s) / D ≤ x := by
    rw [div_le_iff₀ hD]; exact h8
  -- (7) the final assembly.
  have hABpos : 0 < A * A ^ (200 : ℕ) := mul_pos hApos hA200
  have hden : 0 < (A * A ^ (200 : ℕ)) * (d : ℝ) ^ ε := mul_pos hABpos hdeps
  have hW : B / ((A * A ^ (200 : ℕ)) * (d : ℝ) ^ ε) ≤ (K ^ (-(200 : ℝ)) * M ^ (-s)) / D := by
    rw [div_le_iff₀ hden, div_mul_eq_mul_div, le_div_iff₀ hD]
    exact hcross
  have hT_eq : c₃ * (1 - β₁) * B / (A * A ^ (200 : ℕ)) / (d : ℝ) ^ ε
      = (c₃ * (1 - β₁)) * (B / ((A * A ^ (200 : ℕ)) * (d : ℝ) ^ ε)) := by
    rw [div_div, mul_div_assoc]
  have hTW : c₃ * (1 - β₁) * B / (A * A ^ (200 : ℕ)) / (d : ℝ) ^ ε
      ≤ c₃ * (1 - β₁) * K ^ (-(200 : ℝ)) * M ^ (-s) / D := by
    rw [hT_eq, show c₃ * (1 - β₁) * K ^ (-(200 : ℝ)) * M ^ (-s) / D
          = (c₃ * (1 - β₁)) * ((K ^ (-(200 : ℝ)) * M ^ (-s)) / D) by ring]
    exact mul_le_mul_of_nonneg_left hW hcfac.le
  exact le_trans hTW hx

end Work.FIArea6Hecke.R

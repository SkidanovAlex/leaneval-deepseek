import Mathlib

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators

/-- **Arithmetic core of the Ingham assembly.**  Fix the constant `C ≥ 1` of the parameter choice
`K = ⌊C T⌋`, `Y = (C T)^{3/(4-2σ)}`.  There is `M > 0` (depending only on `C`) such that for
`1/2 ≤ σ ≤ 1` and `T ≥ 2`

`Y^{2-2σ} + (C T) K^{1-2σ} + T^{1/3} (T + K)^{2/3} Y^{(2-4σ)/3} ≤ M · T^{3(1-σ)/(2-σ) + ε}`

for every `ε > 0`.  Indeed `Y^{2-2σ} = (CT)^{3(1-σ)/(2-σ)}`, `(CT)K^{1-2σ} ≍ (CT)^{2-2σ} ≤ (CT)^{3(1-σ)/(2-σ)}`
(since `σ ≥ 1/2`) and `T^{1/3}(T+K)^{2/3}Y^{(2-4σ)/3} ≍ T^{(3-3σ)/(2-σ)}`. -/
theorem inghamArithmetic :
    ∀ C : ℝ, 1 ≤ C → ∃ M : ℝ, 0 < M ∧ ∀ (σ T : ℝ), 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      ∀ ε : ℝ, 0 < ε →
        let Y : ℝ := (C * T) ^ (3 / (4 - 2 * σ))
        let K : ℕ := ⌊C * T⌋₊
        Y ^ (2 - 2 * σ) + (C * T) * (K : ℝ) ^ (1 - 2 * σ)
            + T ^ ((1 : ℝ) / 3) * (T + (K : ℝ)) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3)
          ≤ M * T ^ (3 * (1 - σ) / (2 - σ) + ε) := by
  intro C hC
  refine ⟨3 * C + (1 + C) ^ ((2 : ℝ) / 3) + 1, ?_, ?_⟩
  · have h : 0 ≤ (1 + C) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
    linarith
  · intro σ T hσ1 hσ2 hT ε hε
    dsimp only
    have hTpos : 0 < T := by linarith
    have hTge1 : (1 : ℝ) ≤ T := by linarith
    have hCnn : (0 : ℝ) ≤ C := by linarith
    have hCTpos : 0 < C * T := mul_pos (by linarith) hTpos
    have hCTnonneg : 0 ≤ C * T := hCTpos.le
    have h4 : (4 - 2 * σ) ≠ 0 := by intro h; linarith
    have h2s : (2 - σ) ≠ 0 := by intro h; linarith
    have hCTgeT : T ≤ C * T := by
      calc T = 1 * T := by ring
        _ ≤ C * T := mul_le_mul_of_nonneg_right hC hTpos.le
    have hqnn : 0 ≤ (2 * σ - 1) / (2 - σ) := by apply div_nonneg <;> linarith
    -- First term
    have h1 : ((C * T) ^ (3 / (4 - 2 * σ))) ^ (2 - 2 * σ) ≤ C * T ^ (3 * (1 - σ) / (2 - σ)) := by
      have he0le1 : 3 * (1 - σ) / (2 - σ) ≤ 1 := by
        rw [div_le_one (by linarith : (0 : ℝ) < 2 - σ)]; linarith
      have hid : 3 / (4 - 2 * σ) * (2 - 2 * σ) = 3 * (1 - σ) / (2 - σ) := by
        field_simp; ring
      rw [← Real.rpow_mul hCTnonneg (3 / (4 - 2 * σ)) (2 - 2 * σ), hid,
        Real.mul_rpow hCnn hTpos.le]
      exact mul_le_mul_of_nonneg_right (by
        calc C ^ (3 * (1 - σ) / (2 - σ)) ≤ C ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hC he0le1
          _ = C := Real.rpow_one C) (Real.rpow_nonneg hTpos.le _)
    -- Second term
    have h2 : (C * T) * (⌊C * T⌋₊ : ℝ) ^ (1 - 2 * σ) ≤ 2 * C * T ^ (3 * (1 - σ) / (2 - σ)) := by
      have hzle : 1 - 2 * σ ≤ 0 := by linarith
      have h22le : 2 - 2 * σ ≤ 3 * (1 - σ) / (2 - σ) := by
        rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 - σ)]; nlinarith
      have hKhalf : C * T / 2 ≤ (⌊C * T⌋₊ : ℝ) := by
        have hh := Nat.lt_floor_add_one (C * T)
        have h2' : 2 ≤ C * T := by nlinarith [hC, hT]
        linarith
      have hK1 : (⌊C * T⌋₊ : ℝ) ^ (1 - 2 * σ) ≤ (C * T) ^ (1 - 2 * σ) * 2 := by
        have hKle : (⌊C * T⌋₊ : ℝ) ^ (1 - 2 * σ) ≤ (C * T / 2) ^ (1 - 2 * σ) :=
          Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < C * T / 2) hKhalf hzle
        have hsplit : (C * T / 2) ^ (1 - 2 * σ) = (C * T) ^ (1 - 2 * σ) * (1 / 2 : ℝ) ^ (1 - 2 * σ) := by
          rw [show C * T / 2 = (C * T) * (1 / 2) by ring,
            Real.mul_rpow hCTnonneg (by norm_num)]
        have hhalf2 : (1 / 2 : ℝ) ^ (1 - 2 * σ) ≤ 2 := by
          have h := Real.rpow_le_rpow_of_exponent_ge (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
            (show (-1 : ℝ) ≤ 1 - 2 * σ by linarith)
          rw [Real.rpow_neg_one] at h
          norm_num at h
          exact h
        calc (⌊C * T⌋₊ : ℝ) ^ (1 - 2 * σ) ≤ (C * T / 2) ^ (1 - 2 * σ) := hKle
          _ = (C * T) ^ (1 - 2 * σ) * (1 / 2 : ℝ) ^ (1 - 2 * σ) := hsplit
          _ ≤ (C * T) ^ (1 - 2 * σ) * 2 :=
              mul_le_mul_of_nonneg_left hhalf2 (Real.rpow_nonneg hCTnonneg _)
      have hstep : (C * T) * ((C * T) ^ (1 - 2 * σ) * 2) = 2 * (C * T) ^ (2 - 2 * σ) := by
        have hmain : (C * T) * (C * T) ^ (1 - 2 * σ) = (C * T) ^ (2 - 2 * σ) := by
          calc (C * T) * (C * T) ^ (1 - 2 * σ)
              = (C * T) ^ (1 : ℝ) * (C * T) ^ (1 - 2 * σ) := by rw [Real.rpow_one]
            _ = (C * T) ^ (1 + (1 - 2 * σ)) := by rw [Real.rpow_add hCTpos]
            _ = (C * T) ^ (2 - 2 * σ) := by rw [show (1 : ℝ) + (1 - 2 * σ) = 2 - 2 * σ by ring]
        rw [← mul_assoc, hmain]; ring
      calc (C * T) * (⌊C * T⌋₊ : ℝ) ^ (1 - 2 * σ)
          ≤ (C * T) * ((C * T) ^ (1 - 2 * σ) * 2) := mul_le_mul_of_nonneg_left hK1 hCTnonneg
        _ = 2 * (C * T) ^ (2 - 2 * σ) := hstep
        _ = 2 * (C ^ (2 - 2 * σ) * T ^ (2 - 2 * σ)) := by rw [Real.mul_rpow hCnn hTpos.le]
        _ ≤ 2 * (C * T ^ (3 * (1 - σ) / (2 - σ))) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
            apply mul_le_mul _ _ (Real.rpow_nonneg hTpos.le _) hCnn
            · calc C ^ (2 - 2 * σ) ≤ C ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le hC (by linarith)
                _ = C := Real.rpow_one C
            · exact Real.rpow_le_rpow_of_exponent_le hTge1 h22le
        _ = 2 * C * T ^ (3 * (1 - σ) / (2 - σ)) := by ring
    -- Third term
    have h3 : T ^ ((1 : ℝ) / 3) * (T + (⌊C * T⌋₊ : ℝ)) ^ ((2 : ℝ) / 3)
          * ((C * T) ^ (3 / (4 - 2 * σ))) ^ ((2 - 4 * σ) / 3)
        ≤ (1 + C) ^ ((2 : ℝ) / 3) * T ^ (3 * (1 - σ) / (2 - σ)) := by
      have hidq : 3 / (4 - 2 * σ) * ((2 - 4 * σ) / 3) = -((2 * σ - 1) / (2 - σ)) := by
        field_simp; ring
      have hYpow : ((C * T) ^ (3 / (4 - 2 * σ))) ^ ((2 - 4 * σ) / 3)
          = (C * T) ^ (-((2 * σ - 1) / (2 - σ))) := by
        rw [← Real.rpow_mul hCTnonneg (3 / (4 - 2 * σ)) ((2 - 4 * σ) / 3), hidq]
      have hYle : ((C * T) ^ (3 / (4 - 2 * σ))) ^ ((2 - 4 * σ) / 3)
          ≤ T ^ (-((2 * σ - 1) / (2 - σ))) := by
        rw [hYpow]
        exact Real.rpow_le_rpow_of_nonpos hTpos hCTgeT (neg_nonpos.mpr hqnn)
      have hTK : (T + (⌊C * T⌋₊ : ℝ)) ^ ((2 : ℝ) / 3)
          ≤ T ^ ((2 : ℝ) / 3) * (1 + C) ^ ((2 : ℝ) / 3) := by
        have hKle : (⌊C * T⌋₊ : ℝ) ≤ C * T := Nat.floor_le hCTnonneg
        have hle : T + (⌊C * T⌋₊ : ℝ) ≤ T * (1 + C) := by nlinarith [hKle]
        calc (T + (⌊C * T⌋₊ : ℝ)) ^ ((2 : ℝ) / 3) ≤ (T * (1 + C)) ^ ((2 : ℝ) / 3) :=
              Real.rpow_le_rpow (add_nonneg hTpos.le (Nat.cast_nonneg _)) hle (by norm_num)
          _ = T ^ ((2 : ℝ) / 3) * (1 + C) ^ ((2 : ℝ) / 3) := Real.mul_rpow hTpos.le (by linarith)
      have hpart1 : T ^ ((1 : ℝ) / 3) * (T + (⌊C * T⌋₊ : ℝ)) ^ ((2 : ℝ) / 3)
          ≤ T ^ ((1 : ℝ) / 3) * (T ^ ((2 : ℝ) / 3) * (1 + C) ^ ((2 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left hTK (Real.rpow_nonneg hTpos.le _)
      have hkey : T ^ ((1 : ℝ) / 3) * (T ^ ((2 : ℝ) / 3) * (1 + C) ^ ((2 : ℝ) / 3))
            * T ^ (-((2 * σ - 1) / (2 - σ)))
          = (1 + C) ^ ((2 : ℝ) / 3) * T ^ (3 * (1 - σ) / (2 - σ)) := by
        have hTs : T ^ ((1 : ℝ) / 3) * T ^ ((2 : ℝ) / 3) = T := by
          rw [← Real.rpow_add hTpos (1 / 3) (2 / 3)]
          rw [show (1 : ℝ) / 3 + 2 / 3 = 1 by norm_num, Real.rpow_one]
        have hTa : T * T ^ (-((2 * σ - 1) / (2 - σ))) = T ^ (1 - (2 * σ - 1) / (2 - σ)) := by
          calc T * T ^ (-((2 * σ - 1) / (2 - σ)))
              = T ^ (1 : ℝ) * T ^ (-((2 * σ - 1) / (2 - σ))) := by rw [Real.rpow_one]
            _ = T ^ (1 + -((2 * σ - 1) / (2 - σ))) := by rw [Real.rpow_add hTpos]
            _ = T ^ (1 - (2 * σ - 1) / (2 - σ)) := by
                  rw [show (1 : ℝ) + -((2 * σ - 1) / (2 - σ)) = 1 - (2 * σ - 1) / (2 - σ) by ring]
        have he0 : 1 - (2 * σ - 1) / (2 - σ) = 3 * (1 - σ) / (2 - σ) := by field_simp; ring
        calc T ^ ((1 : ℝ) / 3) * (T ^ ((2 : ℝ) / 3) * (1 + C) ^ ((2 : ℝ) / 3))
              * T ^ (-((2 * σ - 1) / (2 - σ)))
            = (T ^ ((1 : ℝ) / 3) * T ^ ((2 : ℝ) / 3)) * (1 + C) ^ ((2 : ℝ) / 3)
                * T ^ (-((2 * σ - 1) / (2 - σ))) := by ring
          _ = T * (1 + C) ^ ((2 : ℝ) / 3) * T ^ (-((2 * σ - 1) / (2 - σ))) := by rw [hTs]
          _ = (1 + C) ^ ((2 : ℝ) / 3) * (T * T ^ (-((2 * σ - 1) / (2 - σ)))) := by ring
          _ = (1 + C) ^ ((2 : ℝ) / 3) * T ^ (1 - (2 * σ - 1) / (2 - σ)) := by rw [hTa]
          _ = (1 + C) ^ ((2 : ℝ) / 3) * T ^ (3 * (1 - σ) / (2 - σ)) := by rw [he0]
      calc T ^ ((1 : ℝ) / 3) * (T + (⌊C * T⌋₊ : ℝ)) ^ ((2 : ℝ) / 3)
            * ((C * T) ^ (3 / (4 - 2 * σ))) ^ ((2 - 4 * σ) / 3)
          ≤ (T ^ ((1 : ℝ) / 3) * (T ^ ((2 : ℝ) / 3) * (1 + C) ^ ((2 : ℝ) / 3)))
              * T ^ (-((2 * σ - 1) / (2 - σ))) :=
            mul_le_mul hpart1 hYle (Real.rpow_nonneg (Real.rpow_nonneg hCTnonneg _) _)
              (mul_nonneg (Real.rpow_nonneg hTpos.le _)
                (mul_nonneg (Real.rpow_nonneg hTpos.le _) (Real.rpow_nonneg (by linarith) _)))
        _ = (1 + C) ^ ((2 : ℝ) / 3) * T ^ (3 * (1 - σ) / (2 - σ)) := hkey
    -- assembly
    have hTe : T ^ (3 * (1 - σ) / (2 - σ)) ≤ T ^ (3 * (1 - σ) / (2 - σ) + ε) :=
      Real.rpow_le_rpow_of_exponent_le hTge1 (by linarith)
    have hMnn : (0 : ℝ) ≤ 3 * C + (1 + C) ^ ((2 : ℝ) / 3) := by
      have h : 0 ≤ (1 + C) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
      linarith
    calc ((C * T) ^ (3 / (4 - 2 * σ))) ^ (2 - 2 * σ)
          + (C * T) * (⌊C * T⌋₊ : ℝ) ^ (1 - 2 * σ)
          + T ^ ((1 : ℝ) / 3) * (T + (⌊C * T⌋₊ : ℝ)) ^ ((2 : ℝ) / 3)
              * ((C * T) ^ (3 / (4 - 2 * σ))) ^ ((2 - 4 * σ) / 3)
        ≤ C * T ^ (3 * (1 - σ) / (2 - σ)) + 2 * C * T ^ (3 * (1 - σ) / (2 - σ))
            + (1 + C) ^ ((2 : ℝ) / 3) * T ^ (3 * (1 - σ) / (2 - σ)) :=
          add_le_add (add_le_add h1 h2) h3
      _ = (3 * C + (1 + C) ^ ((2 : ℝ) / 3)) * T ^ (3 * (1 - σ) / (2 - σ)) := by ring
      _ ≤ (3 * C + (1 + C) ^ ((2 : ℝ) / 3)) * T ^ (3 * (1 - σ) / (2 - σ) + ε) :=
          mul_le_mul_of_nonneg_left hTe hMnn
      _ ≤ (3 * C + (1 + C) ^ ((2 : ℝ) / 3) + 1) * T ^ (3 * (1 - σ) / (2 - σ) + ε) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hTpos.le _)

end Work.ZeroDensity.Ingham

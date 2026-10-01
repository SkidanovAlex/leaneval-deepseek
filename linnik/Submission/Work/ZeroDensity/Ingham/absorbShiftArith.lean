import Mathlib

namespace Work.ZeroDensity.Ingham

theorem absorbShiftArith (A ε : ℝ) (hA : 6 ≤ A) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
    ∀ (T K : ℝ), 2 ≤ T → 1 ≤ K →
      (A * Real.log (A * T) + 1) * (Real.log (A * T) + 1) ^ (6 : ℝ)
        * (T + A * Real.log (A * T)) ^ ((1 : ℝ) / 3)
        * (T + A * Real.log (A * T) + K) ^ ((2 : ℝ) / 3)
      ≤ C * T ^ ε * (T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3)) := by
  have hApos : 0 < A := by linarith
  have hA0 : 0 ≤ A := le_of_lt hApos
  set δ : ℝ := ε / 7 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos hε (by norm_num)
  have hδnn : 0 ≤ δ := le_of_lt hδpos
  have hδ6 : δ + 6 * δ = ε := by rw [hδdef]; ring
  have h1A2pos : 0 < 1 + A ^ 2 := by nlinarith [sq_nonneg A]
  have hX1pos : 0 < (1 + A ^ 2) ^ ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos h1A2pos ((1 : ℝ) / 3)
  have hX2pos : 0 < (1 + A ^ 2) ^ ((2 : ℝ) / 3) :=
    Real.rpow_pos_of_pos h1A2pos ((2 : ℝ) / 3)
  set c1 : ℝ := A ^ (1 + δ) / δ + 1 with hc1def
  set c2 : ℝ := A ^ δ / δ + 1 with hc2def
  have hc1pos : 0 < c1 := by
    rw [hc1def]
    have h1 : 0 < A ^ (1 + δ) := Real.rpow_pos_of_pos hApos (1 + δ)
    have h2 : 0 < A ^ (1 + δ) / δ := div_pos h1 hδpos
    linarith
  have hc2pos : 0 < c2 := by
    rw [hc2def]
    have h1 : 0 < A ^ δ := Real.rpow_pos_of_pos hApos δ
    have h2 : 0 < A ^ δ / δ := div_pos h1 hδpos
    linarith
  set X : ℝ := (1 + A ^ 2) ^ ((1 : ℝ) / 3) * (1 + A ^ 2) ^ ((2 : ℝ) / 3) with hXdef
  have hXpos : 0 < X := by rw [hXdef]; exact mul_pos hX1pos hX2pos
  have hCpos : 0 < c1 * c2 ^ (6 : ℝ) * X :=
    mul_pos (mul_pos hc1pos (Real.rpow_pos_of_pos hc2pos 6)) hXpos
  refine ⟨c1 * c2 ^ (6 : ℝ) * X, hCpos, ?_⟩
  intro T K hT hK
  have hTpos : 0 < T := by linarith
  have hT0 : 0 ≤ T := le_of_lt hTpos
  have hT1 : 1 ≤ T := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hATpos : 0 < A * T := mul_pos hApos hTpos
  have hAT12 : (12 : ℝ) ≤ A * T := by
    have h := mul_le_mul hA hT (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (0 : ℝ) ≤ A)
    linarith
  have hAT1 : 1 ≤ A * T := by linarith
  have hlogpos : 0 < Real.log (A * T) := Real.log_pos (by linarith)
  have hlog0 : 0 ≤ Real.log (A * T) := le_of_lt hlogpos
  have hTδ1 : 1 ≤ T ^ δ := Real.one_le_rpow hT1 hδnn
  have hTδ0 : 0 ≤ T ^ δ := Real.rpow_nonneg hT0 δ
  have hlog_le : Real.log (A * T) ≤ A ^ δ * T ^ δ / δ := by
    have h := Real.log_le_rpow_div hATpos.le hδpos
    rwa [Real.mul_rpow (x := A) (y := T) (z := δ) hA0 hT0] at h
  have hA_pow : A * A ^ δ = A ^ (1 + δ) := by
    rw [Real.rpow_add hApos 1 δ, Real.rpow_one]
  have hF1 : A * Real.log (A * T) + 1 ≤ c1 * T ^ δ := by
    have hmul : A * Real.log (A * T) ≤ A * (A ^ δ * T ^ δ / δ) :=
      mul_le_mul_of_nonneg_left hlog_le hA0
    have hsimp : A * (A ^ δ * T ^ δ / δ) = (A ^ (1 + δ) / δ) * T ^ δ := by
      rw [← hA_pow]; ring
    rw [hsimp] at hmul
    have h2 : A * Real.log (A * T) + 1 ≤ (A ^ (1 + δ) / δ) * T ^ δ + T ^ δ := by
      linarith
    calc A * Real.log (A * T) + 1 ≤ (A ^ (1 + δ) / δ) * T ^ δ + T ^ δ := h2
      _ = c1 * T ^ δ := by rw [hc1def]; ring
  have hF2 : Real.log (A * T) + 1 ≤ c2 * T ^ δ := by
    have h2 : Real.log (A * T) + 1 ≤ A ^ δ * T ^ δ / δ + T ^ δ := by linarith
    calc Real.log (A * T) + 1 ≤ A ^ δ * T ^ δ / δ + T ^ δ := h2
      _ = c2 * T ^ δ := by rw [hc2def]; ring
  have hF2nn : 0 ≤ Real.log (A * T) + 1 := by linarith
  have hF2pow : (Real.log (A * T) + 1) ^ (6 : ℝ) ≤ c2 ^ (6 : ℝ) * T ^ (6 * δ) := by
    have h1 : (Real.log (A * T) + 1) ^ (6 : ℝ) ≤ (c2 * T ^ δ) ^ (6 : ℝ) :=
      Real.rpow_le_rpow hF2nn hF2 (by norm_num)
    have h2 : (c2 * T ^ δ) ^ (6 : ℝ) = c2 ^ (6 : ℝ) * T ^ (6 * δ) := by
      rw [Real.mul_rpow (x := c2) (y := T ^ δ) (z := 6) (le_of_lt hc2pos) hTδ0,
          ← Real.rpow_mul hT0 δ 6, show δ * 6 = 6 * δ by ring]
    linarith
  have hTcomb : T ^ δ * T ^ (6 * δ) = T ^ ε := by
    rw [← Real.rpow_add hTpos δ (6 * δ), hδ6]
  have hFprod : (A * Real.log (A * T) + 1) * (Real.log (A * T) + 1) ^ (6 : ℝ)
      ≤ (c1 * c2 ^ (6 : ℝ)) * T ^ ε := by
    have h1 : (A * Real.log (A * T) + 1) * (Real.log (A * T) + 1) ^ (6 : ℝ)
        ≤ (c1 * T ^ δ) * (c2 ^ (6 : ℝ) * T ^ (6 * δ)) :=
      mul_le_mul hF1 hF2pow (Real.rpow_nonneg hF2nn 6) (mul_nonneg hc1pos.le hTδ0)
    calc (A * Real.log (A * T) + 1) * (Real.log (A * T) + 1) ^ (6 : ℝ)
        ≤ (c1 * T ^ δ) * (c2 ^ (6 : ℝ) * T ^ (6 * δ)) := h1
      _ = (c1 * c2 ^ (6 : ℝ)) * (T ^ δ * T ^ (6 * δ)) := by ring
      _ = (c1 * c2 ^ (6 : ℝ)) * T ^ ε := by rw [hTcomb]
  have hlog_le_AT : Real.log (A * T) ≤ A * T := by
    have h := Real.log_le_sub_one_of_pos hATpos; linarith
  have hTAg : T + A * Real.log (A * T) ≤ (1 + A ^ 2) * T := by
    have h1 : A * Real.log (A * T) ≤ A * (A * T) := mul_le_mul_of_nonneg_left hlog_le_AT hA0
    have h2 : A * (A * T) = A ^ 2 * T := by ring
    linarith
  have hbase1nn : 0 ≤ T + A * Real.log (A * T) := by
    have h := mul_nonneg hA0 hlog0; linarith
  have hG1 : (T + A * Real.log (A * T)) ^ ((1 : ℝ) / 3)
      ≤ (1 + A ^ 2) ^ ((1 : ℝ) / 3) * T ^ ((1 : ℝ) / 3) := by
    calc (T + A * Real.log (A * T)) ^ ((1 : ℝ) / 3) ≤ ((1 + A ^ 2) * T) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow hbase1nn hTAg (by norm_num)
      _ = (1 + A ^ 2) ^ ((1 : ℝ) / 3) * T ^ ((1 : ℝ) / 3) :=
          Real.mul_rpow (x := 1 + A ^ 2) (y := T) (z := (1 : ℝ) / 3) (le_of_lt h1A2pos) hT0
  have hA2nn : 0 ≤ A ^ 2 := sq_nonneg A
  have hTK : T + A * Real.log (A * T) + K ≤ (1 + A ^ 2) * (T + K) := by
    have hKle : K ≤ (1 + A ^ 2) * K := by
      have h := mul_nonneg hA2nn hK0
      nlinarith [h]
    linarith
  have hTK0 : 0 ≤ T + K := by linarith
  have hbase2nn : 0 ≤ T + A * Real.log (A * T) + K := by
    have h := mul_nonneg hA0 hlog0; linarith
  have hG2 : (T + A * Real.log (A * T) + K) ^ ((2 : ℝ) / 3)
      ≤ (1 + A ^ 2) ^ ((2 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3) := by
    calc (T + A * Real.log (A * T) + K) ^ ((2 : ℝ) / 3)
          ≤ ((1 + A ^ 2) * (T + K)) ^ ((2 : ℝ) / 3) :=
          Real.rpow_le_rpow hbase2nn hTK (by norm_num)
      _ = (1 + A ^ 2) ^ ((2 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3) :=
          Real.mul_rpow (x := 1 + A ^ 2) (y := T + K) (z := (2 : ℝ) / 3) (le_of_lt h1A2pos) hTK0
  have hG1nn : 0 ≤ (T + A * Real.log (A * T)) ^ ((1 : ℝ) / 3) :=
    Real.rpow_nonneg hbase1nn ((1 : ℝ) / 3)
  have hG2nn : 0 ≤ (T + A * Real.log (A * T) + K) ^ ((2 : ℝ) / 3) :=
    Real.rpow_nonneg hbase2nn ((2 : ℝ) / 3)
  have hGprod : (T + A * Real.log (A * T)) ^ ((1 : ℝ) / 3)
        * (T + A * Real.log (A * T) + K) ^ ((2 : ℝ) / 3)
      ≤ X * (T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3)) := by
    have h1 : (T + A * Real.log (A * T)) ^ ((1 : ℝ) / 3)
          * (T + A * Real.log (A * T) + K) ^ ((2 : ℝ) / 3)
        ≤ ((1 + A ^ 2) ^ ((1 : ℝ) / 3) * T ^ ((1 : ℝ) / 3))
          * ((1 + A ^ 2) ^ ((2 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3)) :=
      mul_le_mul hG1 hG2 hG2nn
        (mul_nonneg (Real.rpow_nonneg (le_of_lt h1A2pos) ((1 : ℝ) / 3))
          (Real.rpow_nonneg hT0 ((1 : ℝ) / 3)))
    calc (T + A * Real.log (A * T)) ^ ((1 : ℝ) / 3)
          * (T + A * Real.log (A * T) + K) ^ ((2 : ℝ) / 3)
        ≤ ((1 + A ^ 2) ^ ((1 : ℝ) / 3) * T ^ ((1 : ℝ) / 3))
          * ((1 + A ^ 2) ^ ((2 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3)) := h1
      _ = X * (T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3)) := by
          rw [hXdef]; ring
  have hRHSnn : 0 ≤ (c1 * c2 ^ (6 : ℝ)) * T ^ ε :=
    mul_nonneg (mul_nonneg hc1pos.le (Real.rpow_nonneg hc2pos.le 6)) (Real.rpow_nonneg hT0 ε)
  have hmain : ((A * Real.log (A * T) + 1) * (Real.log (A * T) + 1) ^ (6 : ℝ))
        * ((T + A * Real.log (A * T)) ^ ((1 : ℝ) / 3)
           * (T + A * Real.log (A * T) + K) ^ ((2 : ℝ) / 3))
      ≤ ((c1 * c2 ^ (6 : ℝ)) * T ^ ε) * (X * (T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3))) :=
    mul_le_mul hFprod hGprod (mul_nonneg hG1nn hG2nn) hRHSnn
  calc (A * Real.log (A * T) + 1) * (Real.log (A * T) + 1) ^ (6 : ℝ)
        * (T + A * Real.log (A * T)) ^ ((1 : ℝ) / 3)
        * (T + A * Real.log (A * T) + K) ^ ((2 : ℝ) / 3)
      = ((A * Real.log (A * T) + 1) * (Real.log (A * T) + 1) ^ (6 : ℝ))
        * ((T + A * Real.log (A * T)) ^ ((1 : ℝ) / 3)
           * (T + A * Real.log (A * T) + K) ^ ((2 : ℝ) / 3)) := by ring
    _ ≤ ((c1 * c2 ^ (6 : ℝ)) * T ^ ε) * (X * (T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3))) := hmain
    _ = c1 * c2 ^ (6 : ℝ) * X * T ^ ε * (T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3)) := by ring

end Work.ZeroDensity.Ingham

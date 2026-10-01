import Mathlib

namespace Work.LinnikAreas.BGTZArith

/-- The final step of the detector case of the BGTZ repulsion assembly: from the detector chain
`(1-σ)log N ≥ log(1/(1-β₁)) - log Φ - 1`, the size bound `log N ≤ Lq·U`, and the comparison
`Φ·e ≤ C₀·U·Lq`, conclude the repulsion inequality `(log(1/P) - log(C₀U))/U ≤ L`, where `P` and
`L` are the `λ`-normalised quantities `P = (1-β₁)Lq`, `L = (1-σ)Lq`. -/
lemma detector_step {Lq σ β₁ U P L N Φ C₀ : ℝ}
    (hLq : 0 < Lq) (hU : 0 < U) (hΦpos : 0 < Φ) (hLpos : 0 < L)
    (hL : L = (1 - σ) * Lq) (hPβ : P = (1 - β₁) * Lq) (hβ1 : β₁ < 1)
    (hN2 : 2 ≤ N) (hLmax : Real.log N ≤ Lq * U)
    (hchain : (1 - σ) * Real.log N ≥ Real.log (1 / (1 - β₁)) - Real.log Φ - 1)
    (hΦ : Φ * Real.exp 1 ≤ C₀ * U * Lq) :
    (Real.log (1 / P) - Real.log (C₀ * U)) / U ≤ L := by
  have hβ : 0 < 1 - β₁ := by linarith
  have hσpos : 0 < 1 - σ := by
    by_contra h
    have hle : 1 - σ ≤ 0 := le_of_not_gt h
    have : L ≤ 0 := by
      rw [hL]
      exact mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt hLq)
    linarith
  have hC0U : 0 < C₀ * U :=
    pos_of_mul_pos_left (lt_of_lt_of_le (mul_pos hΦpos (Real.exp_pos 1)) hΦ) (le_of_lt hLq)
  have hC0 : 0 < C₀ := pos_of_mul_pos_left hC0U (le_of_lt hU)
  -- `log(1/P) = log(1/(1-β₁)) - log Lq`
  have hlogP : Real.log (1 / P) = Real.log (1 / (1 - β₁)) - Real.log Lq := by
    have hβ' : (1 - β₁) ≠ 0 := ne_of_gt hβ
    have hLq' : Lq ≠ 0 := ne_of_gt hLq
    have hP' : P ≠ 0 := by rw [hPβ]; exact mul_ne_zero hβ' hLq'
    have e1 : Real.log (1 / P) = - Real.log P := by
      rw [Real.log_div one_ne_zero hP', Real.log_one, zero_sub]
    have e2 : Real.log P = Real.log (1 - β₁) + Real.log Lq := by
      rw [hPβ, Real.log_mul hβ' hLq']
    have e3 : Real.log (1 / (1 - β₁)) = - Real.log (1 - β₁) := by
      rw [Real.log_div one_ne_zero hβ', Real.log_one, zero_sub]
    rw [e1, e2, e3]; ring
  -- `log(Φ·e) = log Φ + 1`
  have hlogΦe : Real.log (Φ * Real.exp 1) = Real.log Φ + 1 := by
    rw [Real.log_mul (ne_of_gt hΦpos) (Real.exp_ne_zero 1), Real.log_exp]
  -- `log(C₀·U·Lq) = log(C₀·U) + log Lq`
  have hlogC : Real.log (C₀ * U * Lq) = Real.log (C₀ * U) + Real.log Lq :=
    Real.log_mul (ne_of_gt hC0U) (ne_of_gt hLq)
  have hstep1 : Real.log (1 / (1 - β₁)) ≤ (1 - σ) * Real.log N + Real.log Φ + 1 := by
    linarith [hchain]
  have hstep2 : (1 - σ) * Real.log N ≤ L * U := by
    have h2 := mul_le_mul_of_nonneg_left hLmax (le_of_lt hσpos)
    have h3 : (1 - σ) * (Lq * U) = L * U := by rw [hL]; ring
    linarith [h2, h3]
  have hstep3 : Real.log Φ + 1 ≤ Real.log (C₀ * U * Lq) := by
    have h := Real.log_le_log (mul_pos hΦpos (Real.exp_pos 1)) hΦ
    rwa [hlogΦe] at h
  have hmain : Real.log (1 / P) ≤ L * U + Real.log (C₀ * U) := by
    have h1 : Real.log (1 / P) ≤ (1 - σ) * Real.log N + Real.log Φ + 1 - Real.log Lq := by
      linarith [hlogP, hstep1]
    have h2 : (1 - σ) * Real.log N + Real.log Φ + 1 - Real.log Lq
        ≤ L * U + Real.log Φ + 1 - Real.log Lq := by linarith [hstep2]
    have h3 : L * U + Real.log Φ + 1 - Real.log Lq
        ≤ L * U + Real.log (C₀ * U * Lq) - Real.log Lq := by linarith [hstep3]
    have h4 : L * U + Real.log (C₀ * U * Lq) - Real.log Lq = L * U + Real.log (C₀ * U) := by
      rw [hlogC]; ring
    linarith [h1, h2, h3, h4]
  have hfin : Real.log (1 / P) - Real.log (C₀ * U) ≤ L * U := by linarith [hmain]
  calc
    (Real.log (1 / P) - Real.log (C₀ * U)) / U ≤ (L * U) / U :=
      div_le_div_of_nonneg_right hfin (le_of_lt hU)
    _ = L := by rw [mul_div_assoc, div_self (ne_of_gt hU), mul_one]

end Work.LinnikAreas.BGTZArith

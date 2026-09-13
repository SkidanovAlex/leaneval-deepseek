import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Growth

theorem fop_growth_arith {a c c' cu trC p τ ε : ℝ} (ha : 0 < a) (hc : 0 < c) (hε : 0 < ε) (hcu : c ≤ cu) (htr : trC ≤ 4 * c') (hτ1 : 1 ≤ τ) (hτ2 : τ ≤ 2 ^ (p + 2)) (hp : 2 ≤ p) (hpbig : 16 * c' / c + 2 ≤ p) (hεa : 48 * ε * a * 2 ^ (2 * p + 4) ≤ c) : 0 < a * (((p + 1) * τ - 1) * cu + (-τ - 1) * (trC - cu)) + ε * (a ^ 2 * (3 * ((p + 1) * τ - 1) * (-τ - 1) + 3 * (-τ - 1) ^ 2)) := by
  have hA : ((p + 1) * τ - 1) * cu + (-τ - 1) * (trC - cu) = (p + 2) * τ * cu - (τ + 1) * trC := by ring
  have hB : 3 * ((p + 1) * τ - 1) * (-τ - 1) + 3 * (-τ - 1) ^ 2 = 3 * (τ + 1) * (2 - p * τ) := by ring
  rw [hA, hB]
  -- Step 1: bound on c'
  have hcr : c' ≤ c * (p - 2) / 16 := by
    have h1 : 16 * c' / c ≤ p - 2 := by linarith
    have h2 : 16 * c' ≤ (p - 2) * c := (div_le_iff₀ hc).mp h1
    linarith
  have h4c' : 4 * c' ≤ c * (p - 2) / 4 := by linarith
  have htrD : trC ≤ c * (p - 2) / 4 := by linarith
  -- Step 2: lower bound on X = (p+2)*τ*cu - (τ+1)*trC
  have hX : c * (p + 6) / 2 ≤ (p + 2) * τ * cu - (τ + 1) * trC := by
    have h1 : (p + 2) * τ * c ≤ (p + 2) * τ * cu := by
      apply mul_le_mul_of_nonneg_left hcu
      nlinarith [hp, hτ1]
    have h2 : -(τ + 1) * (c * (p - 2) / 4) ≤ -(τ + 1) * trC := by
      apply mul_le_mul_of_nonpos_left htrD
      linarith
    have h3 : c * (p + 6) / 2 ≤ (p + 2) * τ * c - (τ + 1) * (c * (p - 2) / 4) := by
      have hid : (p + 2) * τ * c - (τ + 1) * (c * (p - 2) / 4) = c * (p + 6) / 2 + c * (3 * p + 10) * (τ - 1) / 4 := by ring
      have hnn : 0 ≤ c * (3 * p + 10) * (τ - 1) / 4 := by
        have : 0 ≤ c * (3 * p + 10) * (τ - 1) := by
          apply mul_nonneg
          · apply mul_nonneg <;> linarith
          · linarith
        linarith
      linarith [hid]
    linarith
  -- Step 3: epsilon term bound
  have hZ1 : (1:ℝ) ≤ 2 ^ (p + 2) := Real.one_le_rpow (by norm_num) (by linarith)
  have hτZ : τ + 1 ≤ 2 * 2 ^ (p + 2) := by linarith
  have hpτ : p * τ - 2 ≤ p * (2 ^ (p + 2)) := by
    have h : p * τ ≤ p * (2 ^ (p + 2)) := mul_le_mul_of_nonneg_left hτ2 (by linarith)
    linarith
  have hprod : (τ + 1) * (p * τ - 2) ≤ 2 * p * (2 ^ (p + 2)) ^ 2 := by
    have h := mul_le_mul hτZ hpτ (by nlinarith [hp, hτ1]) (by positivity)
    calc (τ + 1) * (p * τ - 2) ≤ (2 * 2 ^ (p + 2)) * (p * (2 ^ (p + 2))) := h
      _ = 2 * p * (2 ^ (p + 2)) ^ 2 := by ring
  have hZsq : ((2:ℝ) ^ (p + 2)) ^ (2:ℕ) = (2:ℝ) ^ (2 * p + 4) := by
    rw [pow_two, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  have hE : 3 * ε * a * (τ + 1) * (p * τ - 2) ≤ c * p / 8 := by
    have hnonneg : (0:ℝ) ≤ 3 * ε * a := by positivity
    have h1 : 3 * ε * a * ((τ + 1) * (p * τ - 2)) ≤ 3 * ε * a * (2 * p * (2 ^ (p + 2)) ^ 2) :=
      mul_le_mul_of_nonneg_left hprod hnonneg
    rw [hZsq] at h1
    have hεa' : ε * a * 2 ^ (2 * p + 4) ≤ c / 48 := by linarith
    have hstep : 3 * ε * a * (2 * p * 2 ^ (2 * p + 4)) ≤ c * p / 8 := by
      have h2 := mul_le_mul_of_nonneg_left hεa' (show (0:ℝ) ≤ 6 * p by linarith)
      nlinarith [h2]
    linarith [h1, hstep]
  -- Step 4: assemble
  have hcp : c * p / 8 < c * (p + 6) / 2 := by nlinarith [hc, hp]
  have hfinal : 0 < (p + 2) * τ * cu - (τ + 1) * trC - 3 * ε * a * (τ + 1) * (p * τ - 2) := by
    linarith [hX, hE, hcp]
  have heq : a * ((p + 2) * τ * cu - (τ + 1) * trC) + ε * (a ^ 2 * (3 * (τ + 1) * (2 - p * τ)))
      = a * ((p + 2) * τ * cu - (τ + 1) * trC - 3 * ε * a * (τ + 1) * (p * τ - 2)) := by ring
  rw [heq]
  exact mul_pos ha hfinal

end Commons.Analysis.Growth
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.MeanInequalities

namespace Commons.Analysis.SpecialFunctions

/-- Weighted AM-GM (Gibbs) core: for `a b ≥ 0` and `0 ≤ x ≤ 1`, the product
`x^a (1-x)^b` is bounded by its value at the weighted average `x = a/(a+b)`,
namely `(a/(a+b))^a (b/(a+b))^b`. -/
private theorem amgm_core {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) :
    x ^ a * (1 - x) ^ b ≤ (a / (a + b)) ^ a * (b / (a + b)) ^ b := by
  by_cases ha0 : a = 0
  · rw [ha0]
    have hR : (0 / (0 + b)) ^ (0 : ℝ) * (b / (0 + b)) ^ b = 1 := by
      rw [Real.rpow_zero, one_mul]
      rcases eq_or_lt_of_le hb with hb0 | hb0
      · subst hb0; rw [zero_div, Real.rpow_zero]
      · rw [zero_add, div_self (ne_of_gt hb0), Real.one_rpow]
    have hL : x ^ (0 : ℝ) * (1 - x) ^ b = (1 - x) ^ b := by
      rw [Real.rpow_zero, one_mul]
    rw [hL, hR]
    exact Real.rpow_le_one (by linarith) (by linarith) hb
  · by_cases hb0 : b = 0
    · rw [hb0]
      have hR : (a / (a + 0)) ^ a * (0 / (a + 0)) ^ (0 : ℝ) = 1 := by
        rw [Real.rpow_zero, mul_one, add_zero, div_self ha0, Real.one_rpow]
      have hL : x ^ a * (1 - x) ^ (0 : ℝ) = x ^ a := by
        rw [Real.rpow_zero, mul_one]
      rw [hL, hR]
      exact Real.rpow_le_one hx0 hx1 ha
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hab_pos : 0 < a + b := by linarith
      have h1x0 : 0 ≤ 1 - x := by linarith
      set p : ℝ := a / (a + b) with hpdef
      set q : ℝ := b / (a + b) with hqdef
      have hp_pos : 0 < p := by rw [hpdef]; exact div_pos ha_pos hab_pos
      have hq_pos : 0 < q := by rw [hqdef]; exact div_pos hb_pos hab_pos
      have hpq : p + q = 1 := by
        rw [hpdef, hqdef, ← add_div, div_self (ne_of_gt hab_pos)]
      have hgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := p) (w₂ := q)
        (p₁ := x / p) (p₂ := (1 - x) / q) hp_pos.le hq_pos.le
        (div_nonneg hx0 hp_pos.le) (div_nonneg h1x0 hq_pos.le) hpq
      have hgm' : (x / p) ^ p * ((1 - x) / q) ^ q ≤ 1 := by
        have hsimp : p * (x / p) + q * ((1 - x) / q) = 1 := by
          rw [mul_div_cancel₀ x (ne_of_gt hp_pos),
            mul_div_cancel₀ (1 - x) (ne_of_gt hq_pos)]
          ring
        linarith [hgm]
      have hval : (x / p) ^ p * ((1 - x) / q) ^ q =
          x ^ p * (1 - x) ^ q / (p ^ p * q ^ q) := by
        rw [Real.div_rpow hx0 hp_pos.le, Real.div_rpow h1x0 hq_pos.le]
        ring
      have hpq_pos : 0 < p ^ p * q ^ q :=
        mul_pos (Real.rpow_pos_of_pos hp_pos p) (Real.rpow_pos_of_pos hq_pos q)
      have hmain : x ^ p * (1 - x) ^ q ≤ p ^ p * q ^ q := by
        have h := (div_le_iff₀ hpq_pos).mp (hval ▸ hgm')
        simpa using h
      have hpa : p * (a + b) = a := by
        rw [hpdef, div_mul_cancel₀ a (ne_of_gt hab_pos)]
      have hqb : q * (a + b) = b := by
        rw [hqdef, div_mul_cancel₀ b (ne_of_gt hab_pos)]
      have hLHS : (x ^ p * (1 - x) ^ q) ^ (a + b) = x ^ a * (1 - x) ^ b := by
        rw [Real.mul_rpow (Real.rpow_nonneg hx0 p) (Real.rpow_nonneg h1x0 q)]
        rw [← Real.rpow_mul hx0 p (a + b), ← Real.rpow_mul h1x0 q (a + b), hpa, hqb]
      have hRHS : (p ^ p * q ^ q) ^ (a + b) = p ^ a * q ^ b := by
        rw [Real.mul_rpow (Real.rpow_nonneg hp_pos.le p) (Real.rpow_nonneg hq_pos.le q)]
        rw [← Real.rpow_mul hp_pos.le p (a + b), ← Real.rpow_mul hq_pos.le q (a + b),
          hpa, hqb]
      have hraised := Real.rpow_le_rpow
        (mul_nonneg (Real.rpow_nonneg hx0 p) (Real.rpow_nonneg h1x0 q)) hmain
        (by linarith : (0 : ℝ) ≤ a + b)
      rw [hLHS, hRHS] at hraised
      exact hraised

/-- For `a, b ≥ 0` and `u, v ≥ 0` with `u + v ≤ π/2`,
`(sin u)^a (sin v)^b ≤ (a/(a+b))^(a/2) (b/(a+b))^(b/2)`. -/
theorem sin_pow_mul_sin_pow_le {a b u v : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u)
    (hv : 0 ≤ v) (huv : u + v ≤ Real.pi / 2) :
    Real.sin u ^ a * Real.sin v ^ b ≤
      (a / (a + b)) ^ (a / 2) * (b / (a + b)) ^ (b / 2) := by
  have hu_le : u ≤ Real.pi / 2 := by linarith
  have hsinu_nonneg : 0 ≤ Real.sin u :=
    Real.sin_nonneg_of_nonneg_of_le_pi hu (by linarith [Real.pi_pos])
  have hsinv_nonneg : 0 ≤ Real.sin v :=
    Real.sin_nonneg_of_nonneg_of_le_pi hv (by linarith [Real.pi_pos])
  have hcosu_nonneg : 0 ≤ Real.cos u :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hu_le⟩
  have hsinv_le : Real.sin v ≤ Real.cos u := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two (x := v) (y := Real.pi / 2 - u)
      (by linarith [Real.pi_pos]) (by linarith) (by linarith)
    rwa [Real.sin_pi_div_two_sub] at h
  have step1 : Real.sin u ^ a * Real.sin v ^ b ≤ Real.sin u ^ a * Real.cos u ^ b :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hsinv_nonneg hsinv_le hb)
      (Real.rpow_nonneg hsinu_nonneg a)
  have hsin_id : Real.sin u ^ a = ((Real.sin u) ^ (2 : ℕ)) ^ (a / 2) := by
    rw [Real.rpow_div_two_eq_sqrt a (sq_nonneg (Real.sin u)), Real.sqrt_sq hsinu_nonneg]
  have hcos_id : Real.cos u ^ b = ((Real.cos u) ^ (2 : ℕ)) ^ (b / 2) := by
    rw [Real.rpow_div_two_eq_sqrt b (sq_nonneg (Real.cos u)), Real.sqrt_sq hcosu_nonneg]
  have h1msin : 1 - (Real.sin u) ^ (2 : ℕ) = (Real.cos u) ^ (2 : ℕ) := by
    have := Real.cos_sq_add_sin_sq u
    linarith
  have hx0 : 0 ≤ (Real.sin u) ^ (2 : ℕ) := sq_nonneg _
  have hx1 : (Real.sin u) ^ (2 : ℕ) ≤ 1 := by
    nlinarith [Real.sin_le_one u, hsinu_nonneg]
  have hcore := amgm_core (a := a / 2) (b := b / 2) (x := (Real.sin u) ^ (2 : ℕ))
      (by linarith) (by linarith) hx0 hx1
  rw [h1msin] at hcore
  have harg_a : a / 2 / (a / 2 + b / 2) = a / (a + b) := by
    rw [show a / 2 + b / 2 = (a + b) / 2 by ring, div_div,
      show (2 : ℝ) * ((a + b) / 2) = a + b by ring]
  have harg_b : b / 2 / (a / 2 + b / 2) = b / (a + b) := by
    rw [show a / 2 + b / 2 = (a + b) / 2 by ring, div_div,
      show (2 : ℝ) * ((a + b) / 2) = a + b by ring]
  rw [harg_a, harg_b] at hcore
  rw [hsin_id, hcos_id] at step1
  rw [hsin_id]
  exact le_trans step1 hcore

end Commons.Analysis.SpecialFunctions
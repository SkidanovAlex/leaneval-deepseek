/-
# ZeroFreeTables/Rep9/primePowSeriesLe_proof

`∑_{p^k} Λ(p^k) (p^k)^{-σ} (log p^k)^j ≤ 12 (log p)^{j+1} / p` for `σ > 1`, `j ≤ 2`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.tsum_sq_mul_geometric_le
import Submission.Work.ZeroFreeTables.P9.summable_vonMangoldt_primePow

open ArithmeticFunction
open scoped BigOperators

namespace Work.ZeroFreeTables.Rep9

theorem primePowSeriesLe_proof (p : ℕ) (hp : p.Prime) {σ : ℝ} (hσ : 1 < σ) (j : ℕ)
    (hj : j ≤ 2) :
    (∑' n : ℕ, if IsPrimePow n ∧ n.minFac = p then
        (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j
      else (0 : ℝ))
      ≤ 12 * (Real.log (p : ℝ)) ^ (j + 1) / (p : ℝ) := by
  set x : ℝ := (p : ℝ) ^ (-σ) with hxdef
  have hp2 : 2 ≤ p := hp.two_le
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hx0 : 0 ≤ x := Real.rpow_nonneg hp_pos.le _
  have hx1p : x ≤ 1 / (p : ℝ) := by
    have h1 : (1 : ℝ) / (p : ℝ) = (p : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
    rw [hxdef, h1]
    exact Real.rpow_le_rpow_of_exponent_le hp1R (by linarith : (-σ : ℝ) ≤ -1)
  have hx_half : x ≤ 1 / 2 := by
    have h2 : 1 / (p : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hp_pos (by norm_num)]; linarith
    linarith [hx1p, h2]
  have hx_lt1 : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]; linarith
  -- support of the summand
  have hsupp : Function.support (fun n : ℕ =>
      if IsPrimePow n ∧ n.minFac = p then
        (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j
      else (0 : ℝ)) ⊆ Set.range (fun k : ℕ => p ^ k) := by
    intro n hn
    rw [Function.mem_support] at hn
    by_cases h : IsPrimePow n ∧ n.minFac = p
    · obtain ⟨q, k, hq, hkpos, hqk⟩ := (isPrimePow_nat_iff n).1 h.1
      refine ⟨k, ?_⟩
      have hqp : q = p := by
        have h2 : (q ^ k).minFac = p := by rw [hqk]; exact h.2
        rw [hq.pow_minFac (ne_of_gt hkpos)] at h2
        exact h2
      rw [← hqk, hqp]
    · rw [if_neg h] at hn
      exact absurd rfl hn
  rw [← Function.Injective.tsum_eq (Nat.pow_right_injective hp2) hsupp]
  -- termwise comparison
  have hterm : ∀ k : ℕ,
      (if IsPrimePow (p ^ k) ∧ (p ^ k).minFac = p then
        (ArithmeticFunction.vonMangoldt (p ^ k) : ℝ) * (((p ^ k : ℕ) : ℝ)) ^ (-σ)
          * (Real.log ((p ^ k : ℕ) : ℝ)) ^ j
      else (0 : ℝ))
      ≤ (Real.log (p : ℝ)) ^ (j + 1) * (k : ℝ) ^ 2 * x ^ k := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · have hnot : ¬ (IsPrimePow (p ^ 0) ∧ (p ^ 0).minFac = p) := by
        intro h
        have h1 : (1 : ℕ) < 1 := by simpa [pow_zero] using IsPrimePow.one_lt h.1
        exact absurd h1 (lt_irrefl 1)
      rw [if_neg hnot]
      simp [x]
    · have hpp : IsPrimePow (p ^ k) :=
        (isPrimePow_nat_iff (p ^ k)).mpr ⟨p, k, hp, Nat.pos_of_ne_zero hk, rfl⟩
      have hminf : (p ^ k).minFac = p := hp.pow_minFac hk
      rw [if_pos ⟨hpp, hminf⟩]
      have hΛ : (ArithmeticFunction.vonMangoldt (p ^ k) : ℝ) = Real.log (p : ℝ) := by
        rw [ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hp]
      have hlog : Real.log (((p ^ k : ℕ) : ℝ)) = (k : ℝ) * Real.log (p : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
      have hrpow : (((p ^ k : ℕ) : ℝ)) ^ (-σ) = x ^ k := by
        rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) k,
          ← Real.rpow_mul hp_pos.le (k : ℝ) (-σ), mul_comm (k : ℝ) (-σ),
          Real.rpow_mul hp_pos.le (-σ) (k : ℝ), ← hxdef, Real.rpow_natCast]
      rw [hΛ, hlog, hrpow]
      have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1R
      have hkj : (k : ℝ) ^ j ≤ (k : ℝ) ^ 2 := by
        rcases eq_or_lt_of_le hj with h | h
        · rw [h]
        · exact pow_le_pow_right₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk) (le_of_lt h)
      rw [show (Real.log (p : ℝ) * x ^ k) * ((k : ℝ) * Real.log (p : ℝ)) ^ j
            = (Real.log (p : ℝ)) ^ (j + 1) * (k : ℝ) ^ j * x ^ k by
          rw [mul_pow, pow_succ']; ring]
      gcongr
  -- summability and comparison
  have hfs : Summable (fun k : ℕ =>
      if IsPrimePow (p ^ k) ∧ (p ^ k).minFac = p then
        (ArithmeticFunction.vonMangoldt (p ^ k) : ℝ) * (((p ^ k : ℕ) : ℝ)) ^ (-σ)
          * (Real.log ((p ^ k : ℕ) : ℝ)) ^ j
      else (0 : ℝ)) :=
    (Work.ZeroFreeTables.P9.summable_vonMangoldt_primePow p hp hσ j).comp_injective
      (Nat.pow_right_injective hp2)
  have hgs : Summable (fun k : ℕ => (Real.log (p : ℝ)) ^ (j + 1) * (k : ℝ) ^ 2 * x ^ k) := by
    have h := (summable_pow_mul_geometric_of_norm_lt_one 2 hx_lt1).mul_left
      ((Real.log (p : ℝ)) ^ (j + 1))
    exact h.congr (fun k => by ring)
  have hle := Summable.tsum_le_tsum hterm hfs hgs
  -- evaluate the majorant
  have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1R
  have hmaj : (∑' k : ℕ, (Real.log (p : ℝ)) ^ (j + 1) * (k : ℝ) ^ 2 * x ^ k)
      = (Real.log (p : ℝ)) ^ (j + 1) * ∑' k : ℕ, (k : ℝ) ^ 2 * x ^ k := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun k => by ring)
  have hgeom := Work.ZeroFreeTables.P9.tsum_sq_mul_geometric_le hx0 hx_half
  have hxterm : (Real.log (p : ℝ)) ^ (j + 1) * ∑' k : ℕ, (k : ℝ) ^ 2 * x ^ k
      ≤ (Real.log (p : ℝ)) ^ (j + 1) * (12 * x) :=
    mul_le_mul_of_nonneg_left hgeom (pow_nonneg hlogp_nn _)
  have hxfin : (Real.log (p : ℝ)) ^ (j + 1) * (12 * x)
      ≤ 12 * (Real.log (p : ℝ)) ^ (j + 1) / (p : ℝ) := by
    rw [show (12 : ℝ) * (Real.log (p : ℝ)) ^ (j + 1) / (p : ℝ)
          = (Real.log (p : ℝ)) ^ (j + 1) * (12 / (p : ℝ)) by ring]
    have h12 : (12 : ℝ) * x ≤ 12 / (p : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hx1p (by norm_num : (0 : ℝ) ≤ 12)
      rwa [mul_one_div] at h
    exact mul_le_mul_of_nonneg_left h12 (pow_nonneg hlogp_nn _)
  linarith [hle, hmaj, hxterm, hxfin]

end Work.ZeroFreeTables.Rep9

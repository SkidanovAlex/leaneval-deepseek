import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.PSeries

namespace Commons.Analysis.Series

open Filter

/-- For `p > 1`, the series `∑_n (log n)^{−p} / n` converges. This is the borderline
Bertrand-type series; prove e.g. by the Cauchy condensation test
(`summable_condensed_iff_of_eventually_nonneg`), noting
`2^k · (log (2^k))^{−p} / 2^k = (k log 2)^{−p}` and `∑ k^{−p} < ∞`. The terms at `n = 0, 1`
vanish since `log 0 = log 1 = 0`. -/
theorem summable_log_rpow_inv_div (p : ℝ) (hp : 1 < p) :
    Summable (fun n : ℕ => (Real.log (n : ℝ)) ^ (-p) / (n : ℝ)) := by
  -- The summand is nonnegative and antitone from `n = 2` on.
  have hanti : ∀ m n : ℕ, 2 ≤ m → m ≤ n →
      (Real.log (n : ℝ)) ^ (-p) / (n : ℝ) ≤ (Real.log (m : ℝ)) ^ (-p) / (m : ℝ) := by
    intro m n hm hmn
    have hm1 : 1 < m := by omega
    have hn1 : 1 < n := by omega
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm1)
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
    have hlogle : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log hm0 (by exact_mod_cast hmn)
    have hp0 : (0 : ℝ) ≤ p := by linarith
    have hle : (Real.log (m : ℝ)) ^ p ≤ (Real.log (n : ℝ)) ^ p :=
      Real.rpow_le_rpow (le_of_lt hlogm) hlogle hp0
    have hprod : (Real.log (m : ℝ)) ^ p * (m : ℝ) ≤ (Real.log (n : ℝ)) ^ p * (n : ℝ) :=
      mul_le_mul hle (by exact_mod_cast hmn) (Nat.cast_nonneg m)
        (le_of_lt (Real.rpow_pos_of_pos hlogn p))
    have hinv : ((Real.log (n : ℝ)) ^ p * (n : ℝ))⁻¹ ≤
        ((Real.log (m : ℝ)) ^ p * (m : ℝ))⁻¹ :=
      (inv_le_inv₀ (mul_pos (Real.rpow_pos_of_pos hlogn p) hn0)
        (mul_pos (Real.rpow_pos_of_pos hlogm p) hm0)).2 hprod
    rw [div_eq_mul_inv, div_eq_mul_inv, Real.rpow_neg (le_of_lt hlogm) p,
      Real.rpow_neg (le_of_lt hlogn) p, ← mul_inv, ← mul_inv]
    exact hinv
  have hnon : 0 ≤ᶠ[Filter.atTop] (fun n : ℕ => (Real.log (n : ℝ)) ^ (-p) / (n : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact div_nonneg (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (-p))
      (Nat.cast_nonneg n)
  have hmono : ∀ᶠ k in Filter.atTop,
      (fun n : ℕ => (Real.log (n : ℝ)) ^ (-p) / (n : ℝ)) (k + 1) ≤
        (fun n : ℕ => (Real.log (n : ℝ)) ^ (-p) / (n : ℝ)) k := by
    rw [Filter.eventually_atTop]
    exact ⟨2, fun k hk => hanti k (k + 1) hk (Nat.le_succ k)⟩
  rw [← summable_condensed_iff_of_eventually_nonneg
    (f := fun n : ℕ => (Real.log (n : ℝ)) ^ (-p) / (n : ℝ)) hnon hmono]
  -- Identify the condensed series with a constant multiple of `∑ k^{-p}`.
  have hcond : (fun k : ℕ => (2 : ℝ) ^ k *
        ((Real.log ((2 ^ k : ℕ) : ℝ)) ^ (-p) / ((2 ^ k : ℕ) : ℝ)))
      = fun k : ℕ => (Real.log 2) ^ (-p) * (k : ℝ) ^ (-p) := by
    funext k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have hzp : (0 : ℝ) ^ (-p) = 0 := Real.zero_rpow (by linarith : (-p : ℝ) ≠ 0)
      norm_num [hzp, Real.log_one]
    · have h2k : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
      rw [Real.mul_rpow (Nat.cast_nonneg k) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
      field_simp
  rw [hcond]
  have hbase : Summable (fun k : ℕ => (k : ℝ) ^ (-p)) :=
    (Real.summable_nat_rpow_inv.mpr hp).congr
      (fun k => (Real.rpow_neg (Nat.cast_nonneg k) p).symm)
  exact hbase.mul_left ((Real.log 2) ^ (-p))

end Commons.Analysis.Series
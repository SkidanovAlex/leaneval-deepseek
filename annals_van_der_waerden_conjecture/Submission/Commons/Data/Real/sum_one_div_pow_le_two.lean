import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries

open scoped BigOperators

set_option autoImplicit false

/-!
# `∑ r in s, ...` legacy binder

This Mathlib revision only supports the `∑ r ∈ s, ...` binder, but the lemma below
was requested with the legacy `∑ r in s, ...` spelling.  The local notation below
makes exactly that text parse, elaborating to the same `Finset.sum`.
-/
syntax (name := sumOneDivPowSumIn) "∑ " ident " in " term ", " term : term
macro_rules
  | `(∑ $x:ident in $s:term, $v) => `(Finset.sum $s (fun $x:ident => $v))

namespace Commons.Data.Real

/-- For `1 ≤ r` and `2 ≤ k` we have `1 / r ^ k ≤ 1 / r ^ 2`. -/
private lemma one_div_pow_le_one_div_sq {k r : ℕ} (hk : 2 ≤ k) (hr : 1 ≤ r) :
    (1 : ℝ) / (r : ℝ) ^ k ≤ (1 : ℝ) / (r : ℝ) ^ 2 := by
  have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hpow : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ k := pow_le_pow_right₀ h1 hk
  have hpos : 0 < (r : ℝ) ^ 2 := by positivity
  exact one_div_le_one_div_of_le hpos hpow

/-- The tail `∑ r = 2 .. H, 1 / r ^ 2` is at most `1`
(via comparison with the telescoping series `∑ 1 / (r * (r - 1))`). -/
private lemma sum_Icc_two_inv_sq_le_one (H : ℕ) :
    (∑ r ∈ Finset.Icc 2 H, (1 : ℝ) / (r : ℝ) ^ 2) ≤ 1 := by
  -- `Icc 2 H = Ioo 1 (H + 1)`
  have hset : Finset.Icc 2 H = Finset.Ioo 1 (H + 1) := by
    ext r
    simp [Finset.mem_Icc, Finset.mem_Ioo]
    omega
  rw [hset]
  -- Mathlib's `sum_Ioo_inv_sq_le 1 (H + 1)` bounds this tail by `2 / 2 = 1`.
  have hbd := sum_Ioo_inv_sq_le (α := ℝ) 1 (H + 1)
  calc
    (∑ r ∈ Finset.Ioo 1 (H + 1), (1 : ℝ) / (r : ℝ) ^ 2)
        ≤ 2 / (↑(1 : ℕ) + 1) := by
          simpa [one_div] using hbd
    _ = 1 := by norm_num

/-- `∑ r = 1 .. H, 1 / r ^ 2 ≤ 2`: split off the first term and bound the tail by `1`. -/
private lemma sum_one_div_sq_Icc_one_le_two (H : ℕ) :
    (∑ r ∈ Finset.Icc 1 H, (1 : ℝ) / (r : ℝ) ^ 2) ≤ 2 := by
  by_cases hH : 1 ≤ H
  · calc
      (∑ r ∈ Finset.Icc 1 H, (1 : ℝ) / (r : ℝ) ^ 2)
          = (1 : ℝ) / (1 : ℝ) ^ 2 + ∑ r ∈ Finset.Icc 2 H, (1 : ℝ) / (r : ℝ) ^ 2 := by
            have hset : Finset.Icc 1 H = insert 1 (Finset.Icc 2 H) := by
              ext r
              simp [Finset.mem_Icc]
              omega
            rw [hset, Finset.sum_insert]
            · simp [one_div]
            · simp [Finset.mem_Icc]
      _ = 1 + ∑ r ∈ Finset.Icc 2 H, (1 : ℝ) / (r : ℝ) ^ 2 := by norm_num
      _ ≤ 1 + 1 := by
        linarith [sum_Icc_two_inv_sq_le_one H]
      _ = 2 := by norm_num
  · have hH0 : H = 0 := by omega
    subst H
    simp

theorem sum_one_div_pow_le_two (H k : ℕ) (hk : 2 ≤ k) :
    (∑ r in Finset.Icc 1 H, (1 : ℝ) / (r : ℝ) ^ k) ≤ 2 := by
  calc
    (∑ r in Finset.Icc 1 H, (1 : ℝ) / (r : ℝ) ^ k)
        ≤ ∑ r in Finset.Icc 1 H, (1 : ℝ) / (r : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro r hr
          exact one_div_pow_le_one_div_sq hk (Finset.mem_Icc.mp hr).1
    _ ≤ 2 := sum_one_div_sq_Icc_one_le_two H

end Commons.Data.Real
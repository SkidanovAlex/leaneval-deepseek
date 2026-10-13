import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.PhiStar.Series.Deleg.phiASeriesDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

theorem phiAtermBound (α : ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) (n k : ℕ) (hn : n < 4) (hk : k ≤ 22)
    {z : ℝ} (hz : 0 < z) :
    |Work.FTS.PhiStar.Series.Deleg.phiAcoef α n
        * (∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i))
        * (1 + z) ^ (-(n : ℤ) - 1 - (k : ℤ))| ≤ 30 * 26 ^ 22 := by
  -- `|phiAcoef α n| ≤ 30` for `n < 4`, `0 < α ≤ 1/5`
  have hcoef : |phiAcoef α n| ≤ 30 := by
    interval_cases n <;> simp only [phiAcoef] <;>
      rw [abs_le] <;> constructor <;> linarith
  -- the falling-factorial product is bounded by `26^22`
  have hprod : |∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i)| ≤ 26 ^ 22 := by
    rw [Finset.abs_prod]
    have hle : ∀ i ∈ Finset.range k, |(-(n : ℝ) - 1) - i| ≤ (26 : ℝ) := by
      intro i hi
      have hi' : i < k := Finset.mem_range.mp hi
      have hn3 : (n : ℝ) ≤ 3 := by
        have : n ≤ 3 := by omega
        exact_mod_cast this
      have hi21 : (i : ℝ) ≤ 21 := by
        have : i ≤ 21 := by omega
        exact_mod_cast this
      rw [abs_le]
      constructor <;> linarith
    calc ∏ i ∈ Finset.range k, |(-(n : ℝ) - 1) - i|
        ≤ ∏ _i ∈ Finset.range k, (26 : ℝ) :=
          Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) hle
      _ = (26 : ℝ) ^ k := by rw [Finset.prod_const, Finset.card_range]
      _ ≤ (26 : ℝ) ^ 22 := pow_le_pow_right₀ (by norm_num) hk
  -- `1 + z > 1` and the exponent is a nonpositive integer, so the power is `≤ 1`
  have hpow : |(1 + z) ^ (-(n : ℤ) - 1 - (k : ℤ))| ≤ 1 := by
    have hbase : (1 : ℝ) < 1 + z := by linarith
    have hbase' : (0 : ℝ) ≤ 1 + z := by linarith
    have hexp : (-(n : ℤ) - 1 - (k : ℤ)) ≤ 0 := by omega
    rw [abs_of_nonneg (zpow_nonneg hbase' _)]
    exact (zpow_le_one_iff_right₀ hbase).mpr hexp
  calc
    |phiAcoef α n
        * (∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i))
        * (1 + z) ^ (-(n : ℤ) - 1 - (k : ℤ))|
        = |phiAcoef α n|
            * |∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i)|
            * |(1 + z) ^ (-(n : ℤ) - 1 - (k : ℤ))| := by rw [abs_mul, abs_mul]
    _ ≤ 30 * 26 ^ 22 * 1 := by
        have h1 : |phiAcoef α n|
              * |∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i)| ≤ 30 * 26 ^ 22 :=
          mul_le_mul hcoef hprod (abs_nonneg _) (by norm_num)
        exact mul_le_mul h1 hpow (abs_nonneg _) (by positivity)
    _ = 30 * 26 ^ 22 := by ring

end Work.FTS.PhiStar.Series.Deleg

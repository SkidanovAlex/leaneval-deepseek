import Mathlib
import Submission.Work.BW.est15defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Basic real inequality: for `y ≥ 0`, `log (y ^ N) ≤ N * log⁺ y`. -/
private lemma log_pow_le_nat_mul_posLog (y : ℝ) (N : ℕ) :
    Real.log (y ^ N) ≤ (N : ℝ) * Real.posLog y := by
  rw [Real.log_pow]
  exact mul_le_mul_of_nonneg_left (by rw [Real.posLog_apply]; exact le_max_right _ _)
    (Nat.cast_nonneg N)

theorem log_infinitePlace_zpow_le {K : Type*} [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) (a : K) (s : ℤ) (q : ℕ) :
    Real.log (w (a ^ (s * (q : ℤ)))) ≤ ((|s| : ℝ) * q) * Real.posLog (w (estBeta s a)) := by
  rcases lt_or_ge s 0 with hs | hs
  · -- `s < 0`: `estBeta s a = a⁻¹`, exponent `s * q ≤ 0`
    rw [estBeta, ite_eq_right (not_le.mpr hs),
      abs_of_neg (show (s : ℝ) < 0 by exact_mod_cast hs)]
    have hspos : (0 : ℤ) ≤ -s := by omega
    have hm : ((-s).toNat : ℤ) = -s := Int.toNat_of_nonneg hspos
    have hN : (((-s).toNat * q : ℕ) : ℝ) = |(s : ℝ)| * q := by
      rw [Nat.cast_mul, abs_of_neg (show (s : ℝ) < 0 by exact_mod_cast hs)]
      congr 1
      exact_mod_cast hm
    have hbase : a ^ (s * (q : ℤ)) = (a⁻¹) ^ ((((-s).toNat * q : ℕ)) : ℤ) := by
      have h : ((((-s).toNat * q : ℕ)) : ℤ) = -(s * (q : ℤ)) := by
        rw [Nat.cast_mul, hm]; ring
      rw [h, inv_zpow', neg_neg]
    rw [hbase, zpow_natCast, map_pow w]
    refine (log_pow_le_nat_mul_posLog (w a⁻¹) ((-s).toNat * q)).trans (le_of_eq ?_)
    rw [hN, abs_of_neg (show (s : ℝ) < 0 by exact_mod_cast hs)]
  · -- `0 ≤ s`: `estBeta s a = a`, exponent `s * q ≥ 0`
    rw [estBeta, ite_eq_left hs, abs_of_nonneg (show (0 : ℝ) ≤ s by exact_mod_cast hs)]
    have hs' : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hs
    have hexp : s * (q : ℤ) = ((s.toNat * q : ℕ) : ℤ) := by
      rw [Nat.cast_mul, hs']
    have hN : ((s.toNat * q : ℕ) : ℝ) = |(s : ℝ)| * q := by
      rw [Nat.cast_mul, abs_of_nonneg (show (0 : ℝ) ≤ s by exact_mod_cast hs)]
      congr 1
      exact_mod_cast hs'
    rw [hexp, zpow_natCast, map_pow w]
    refine (log_pow_le_nat_mul_posLog (w a) (s.toNat * q)).trans (le_of_eq ?_)
    rw [hN, abs_of_nonneg (show (0 : ℝ) ≤ s by exact_mod_cast hs)]

end Work.BW

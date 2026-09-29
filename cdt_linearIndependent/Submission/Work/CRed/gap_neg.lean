import Mathlib

namespace Work.CRed

lemma gap_neg (m n : ℤ) (hm : m ≤ -2) (hn : n ≤ -2) (hgap : 10 ^ 6 * |m - n| < |n|) :
    10 ^ 6 * (((-m - 1).toNat : ℤ) - (-n - 1).toNat).natAbs ≤ (-n - 1).toNat := by
  -- Both `-m - 1` and `-n - 1` are nonnegative integers, and they are exactly the
  -- values of the corresponding `toNat` casts.
  have hma : (0:ℤ) ≤ -m - 1 := by omega
  have hna : (0:ℤ) ≤ -n - 1 := by omega
  have hA : ((-m - 1).toNat : ℤ) = -m - 1 := Int.toNat_of_nonneg hma
  have hB : ((-n - 1).toNat : ℤ) = -n - 1 := Int.toNat_of_nonneg hna
  -- The integer inside the `natAbs` equals `n - m`.
  have hX : (((-m - 1).toNat : ℤ) - (-n - 1).toNat) = n - m := by
    rw [hA, hB]; ring
  rw [hX]
  -- Since `n ≤ -2 < 0`, we have `|n| = -n`.
  have hneg : |n| = -n := abs_of_neg (by omega)
  rw [hneg] at hgap
  -- Work in ℤ: it suffices to show `10^6 * |n - m| ≤ -n - 1`.
  apply Int.ofNat_le.mp
  push_cast
  rw [Int.toNat_of_nonneg hna, abs_sub_comm]
  -- Now: from `10^6 * |m - n| < -n` deduce `10^6 * |m - n| ≤ -n - 1`.
  omega

end Work.CRed

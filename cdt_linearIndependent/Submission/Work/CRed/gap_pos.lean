import Mathlib

namespace Work.CRed

/-- For integers `m, n ≥ 1` with `10 ^ 6 * |m - n| < |n|`, the rounded gap
`10 ^ 6 * |m.toNat - n.toNat|` is at most `n.toNat`.  Since `m, n ≥ 1` are
nonnegative, `m.toNat = m`, `n.toNat = n` as integers and `|n| = n`, so the
claim reduces to `10 ^ 6 * |m - n| ≤ n`, immediate from the strict hypothesis. -/
lemma gap_pos (m n : ℤ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hgap : 10 ^ 6 * |m - n| < |n|) :
    10 ^ 6 * ((m.toNat : ℤ) - n.toNat).natAbs ≤ n.toNat := by
  have hmn : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (by linarith)
  have hnn : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by linarith)
  have hnatAbs : ((m.toNat : ℤ) - n.toNat).natAbs = (m - n).natAbs := by rw [hmn, hnn]
  rw [hnatAbs]
  have hnabs : |n| = n := abs_of_nonneg (by linarith)
  rw [hnabs] at hgap
  have key : ((10 ^ 6 * (m - n).natAbs : ℕ) : ℤ) ≤ ((n.toNat : ℕ) : ℤ) := by
    push_cast
    rw [hnn]
    linarith
  exact_mod_cast key

end Work.CRed

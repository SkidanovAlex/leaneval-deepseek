import Mathlib
import Submission.Work.BG.keySmallNeNegOne
import Submission.Work.BG.keySmallOdd

namespace Work.BG

/-- **KEY-SMALL arithmetic leaf.**  Let `a, b, c` be odd integers with `1 + a + b + c = 0` and
let the "Lemma 2.2" identity
`N · (abc + bc + ac + ab) = 2 k² · (abc)` hold with `k ≠ 0`.  Then none of `a, b, c` equals
`-1`, and since an odd integer other than `-1` is either `1` or has absolute value at least
`3`, the conclusion follows.

The key point is that `x = -1` forces `z = -y`, whence the symmetric bracket
`xyz + yz + xz + xy` collapses to `0` while `xyz = y² ≠ 0`, contradicting `N·0 = 2k²y²`. -/
theorem keySmallFinal (N k : ℕ) (a b c : ℤ) (ha : Odd a) (hb : Odd b) (hc : Odd c)
    (hsum : 1 + a + b + c = 0)
    (heq : (N : ℤ) * (a * b * c + b * c + a * c + a * b) = 2 * (k : ℤ) ^ 2 * (a * b * c))
    (hk : k ≠ 0) :
    (a = 1 ∨ 3 ≤ |a|) ∧ (b = 1 ∨ 3 ≤ |b|) ∧ (c = 1 ∨ 3 ≤ |c|) := by
  -- None of the three variables can be `-1`; the hypotheses are symmetric in `a, b, c`,
  -- so a single generic statement is applied at each cyclic permutation.
  have hna : a ≠ -1 := keySmallNeNegOne N k a b c hb hsum heq hk
  have hnb : b ≠ -1 := keySmallNeNegOne N k b c a hc (by linarith [hsum])
    (by simpa only [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
      using heq) hk
  have hnc : c ≠ -1 := keySmallNeNegOne N k c a b ha (by linarith [hsum])
    (by simpa only [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
      using heq) hk
  exact ⟨keySmallOdd a ha hna, keySmallOdd b hb hnb, keySmallOdd c hc hnc⟩

end Work.BG

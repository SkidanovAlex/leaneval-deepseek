import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.twoLetterTlDefs

/-!
# The interior `b`-symbols of the two-letter walk lie in the window

The decorated walk of the two-letter relator `tlU p q = a ^ p * b ^ q` at starting level
`N = b + 1 - p * q` has, as its `b`-block, the letters `(1, true)` read at the levels
`N + p q - k p`, `k = 0, 1, …, q - 1`.  With `N = a - 1` (the window base of `winE (tlW p q) a (p*q)`)
the level of the `k`-th of these symbols is `a - 1 + p q - k p`, and its *target* level is
`a - 1 + p q - (k+1) p` because `tlW p q 1 = -p`.

This file proves that for `0 ≤ k` and `k + 2 ≤ q` — i.e. for all the `b`-symbols of the walk except
the last one — the edge `((1), a - 1 + p*q - k*p)` lies in the window `winE (tlW p q) a (p*q)`, so
that the corresponding factor `walkB` of the one-copy decoration is a product of generators of the
window subgroup.  All four conjuncts of `mem_winE` are immediate arithmetic inequalities; `nlinarith`
closes them from `1 ≤ p`, `2 ≤ q - k` (resp. `1 ≤ q - k`) and `a ≤ 1`.
-/

namespace Work.OROneRel

theorem walkMid_b_mem {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (a : ℤ) (ha : a ≤ 1) {k : ℕ}
    (hk : k + 2 ≤ q) :
    (((1 : Fin 2), a - 1 + (p : ℤ) * (q : ℤ) - (k : ℤ) * (p : ℤ)) : Fin 2 × ℤ) ∈
      Work.OROneRel.winE (Work.OROneRel.tlW p q) a ((p : ℤ) * (q : ℤ)) := by
  rw [mem_winE]
  have htl : tlW p q (1 : Fin 2) = -(p : ℤ) := by simp [tlW]
  have hkq2 : (2 : ℤ) ≤ (q : ℤ) - (k : ℤ) := by omega
  have hkq1 : (1 : ℤ) ≤ (q : ℤ) - (k : ℤ) := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · rw [htl]; nlinarith
  · rw [htl]; nlinarith

end Work.OROneRel

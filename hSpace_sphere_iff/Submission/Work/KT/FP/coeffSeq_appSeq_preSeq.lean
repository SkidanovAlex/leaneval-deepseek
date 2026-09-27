import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.Idx.WPen

/-!
# `Work.KT.FP.coeffSeq_appSeq_preSeq`

The coefficient sequence of a Laurent matrix `P` of degree bound `m` and that of the same matrix
regarded as of degree bound `m + 1` are related by

`coeffSeq (m+1) P = appSeq (preSeq (coeffSeq m P))`,

i.e. going from the degree bound `m` to `m + 1` replaces the coefficient sequence
`b = (b_0, …, b_{2m})` — the coefficients of `z^m P` — by `(0, b_0, …, b_{2m}, 0)`, the
coefficients of `z^{m+1} P = z · (z^m P)`: one *prepend* `b ↦ (0, b)` and one *append*
`b ↦ (b, 0)`.

The hypothesis `hb` is exactly the degree bound: the coefficients of `P` in degrees `> m` and in
degrees `< -m` vanish, which is what makes the two outer coefficients of `z^{m+1} P` (those of
`z^{-m-1}` and `z^{m+1}`) zero.  Concretely, writing `j : Fin (2m+3)` and
`k = (j : ℤ) - (m+1)`:

* `j = 0` gives `k = -(m+1) < -m`, so `hb` kills it;
* `1 ≤ j ≤ 2m+1` gives the identity `k = ((j-1 : Fin (2m+1)) : ℤ) - m`;
* `j = 2m+2` gives `k = m+1 > m`, so `hb` kills it.
-/

namespace Work.KT.FP

set_option linter.unusedSimpArgs false in
theorem coeffSeq_appSeq_preSeq (X : Type) [TopologicalSpace X] (n m : ℕ)
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
    (hb : ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) → (P i j).coeff k = 0) :
    Work.KT.FP.coeffSeq X n (m + 1) P
      = Work.KT.Idx.appSeq X (Work.KT.Idx.preSeq X (Work.KT.FP.coeffSeq X n m P)) := by
  funext j
  apply Matrix.ext
  intro a c
  simp only [Work.KT.FP.coeffSeq, Work.KT.Idx.appSeq, Work.KT.Idx.preSeq]
  split_ifs with h1 h2
  · congr 1
    simp only [Fin.val_mk]
    omega
  · rw [hb a c _ (Or.inr (by push_cast; omega))]
    rfl
  · rw [hb a c _ (Or.inl (by push_cast; omega))]
    rfl

end Work.KT.FP

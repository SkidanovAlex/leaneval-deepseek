import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Geom
import Submission.Work.KT.Fund.Clutch

/-!
# `Work.KT.Fund.kappa_add_defs` — index bookkeeping for `kappa_add`

The block-diagonal clutching function `u = u₁ ⊕ u₂` sits on the index set `Fin (n + k)`, while the
two summands sit on `Fin n` and `Fin k`.  This file provides the equivalence

`blkEquiv n k : (Fin n ⊕ Fin n) ⊕ (Fin k ⊕ Fin k) ≃ Fin (n + k) ⊕ Fin (n + k)`

which shuffles `(top-n, bottom-n) ⊕ (top-k, bottom-k)` into `(top, bottom)` (with
`top-n, top-k` combined by `finSumFinEquiv`), i.e. exactly the identification along which the
orthogonal projection `graphProj` (resp. `recipProj`) of a block-diagonal matrix splits as the
block sum of the two `graphProj`s (resp. `recipProj`s).
-/

namespace Work.KT.Fund

open Matrix

/-- `(A ⊕ B) ⊕ (C ⊕ D) ≃ (A ⊕ C) ⊕ (B ⊕ D)`. -/
def midSwap (A B C D : Type) : (A ⊕ B) ⊕ (C ⊕ D) ≃ (A ⊕ C) ⊕ (B ⊕ D) where
  toFun x := match x with
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
    | Sum.inr (Sum.inl c) => Sum.inl (Sum.inr c)
    | Sum.inr (Sum.inr d) => Sum.inr (Sum.inr d)
  invFun x := match x with
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr c) => Sum.inr (Sum.inl c)
    | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
    | Sum.inr (Sum.inr d) => Sum.inr (Sum.inr d)
  left_inv := by rintro ((a | b) | (c | d)) <;> rfl
  right_inv := by rintro ((a | c) | (b | d)) <;> rfl

/-- The shuffle `(top-n, bottom-n) ⊕ (top-k, bottom-k) ≃ (top, bottom)` used in the block
decomposition of `graphProj`/`recipProj`. -/
def blkEquiv (n k : ℕ) : (Fin n ⊕ Fin n) ⊕ (Fin k ⊕ Fin k) ≃ Fin (n + k) ⊕ Fin (n + k) :=
  (midSwap (Fin n) (Fin n) (Fin k) (Fin k)).trans
    (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)

@[simp] lemma blkEquiv_apply_inl_inl (n k : ℕ) (a : Fin n) :
    blkEquiv n k (Sum.inl (Sum.inl a)) = Sum.inl (finSumFinEquiv (Sum.inl a)) := rfl

@[simp] lemma blkEquiv_apply_inl_inr (n k : ℕ) (i : Fin n) :
    blkEquiv n k (Sum.inl (Sum.inr i)) = Sum.inr (finSumFinEquiv (Sum.inl i)) := rfl

@[simp] lemma blkEquiv_apply_inr_inl (n k : ℕ) (b : Fin k) :
    blkEquiv n k (Sum.inr (Sum.inl b)) = Sum.inl (finSumFinEquiv (Sum.inr b)) := rfl

@[simp] lemma blkEquiv_apply_inr_inr (n k : ℕ) (j : Fin k) :
    blkEquiv n k (Sum.inr (Sum.inr j)) = Sum.inr (finSumFinEquiv (Sum.inr j)) := rfl

@[simp] lemma blkEquiv_symm_inl_inl (n k : ℕ) (a : Fin n) :
    (blkEquiv n k).symm (Sum.inl (finSumFinEquiv (Sum.inl a))) = Sum.inl (Sum.inl a) := by
  simp [blkEquiv, midSwap]

@[simp] lemma blkEquiv_symm_inl_inr (n k : ℕ) (i : Fin n) :
    (blkEquiv n k).symm (Sum.inr (finSumFinEquiv (Sum.inl i))) = Sum.inl (Sum.inr i) := by
  simp [blkEquiv, midSwap]

@[simp] lemma blkEquiv_symm_inr_inl (n k : ℕ) (b : Fin k) :
    (blkEquiv n k).symm (Sum.inl (finSumFinEquiv (Sum.inr b))) = Sum.inr (Sum.inl b) := by
  simp [blkEquiv, midSwap]

@[simp] lemma blkEquiv_symm_inr_inr (n k : ℕ) (j : Fin k) :
    (blkEquiv n k).symm (Sum.inr (finSumFinEquiv (Sum.inr j))) = Sum.inr (Sum.inr j) := by
  simp [blkEquiv, midSwap]

end Work.KT.Fund

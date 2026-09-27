import Mathlib
import Submission.Work.KT.Psi.psi3sum_Setup

/-!
# `Work.KT.Psi.PWordSetup` — the `p`-word inside the triple tensor power of `p ⊕ q`

The index type of `kron3g (sumBlkP p q)` is `SQ (Fin p.1 ⊕ Fin q.1)`, the triple tensor power of
the block index set of `p ⊕ q`.  Since `sumBlkP p q` is the block matrix with `p.2` in the `p`-block
and `0` elsewhere, the matrix `kron3g (sumBlkP p q)` is supported on the three "words" all of whose
entries lie in the `p`-block.  This file isolates that word:

* `emb p.1 q.1 : SQ (Fin p.1) ↪ SQ (Fin p.1 ⊕ Fin q.1)` — its inclusion;
* `pWord p.1 q.1` — the predicate "lies in that word";
* `psiEquiv p.1 q.1 : SQ (Fin p.1) ⊕ (complement of the word) ≃ SQ (Fin p.1 ⊕ Fin q.1)`.

The point of `psiEquiv` is that `clsM` is invariant under reindexing without any idempotency
hypothesis (`clsI_reindex`), so once the matrix is known to be the block matrix with `cubePartP`
in its `p`-word and `0` elsewhere, its class can be computed by `clsM_fromBlocks_zero`.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

open Classical

/-- The inclusion of the `p`-word into the triple tensor-power index of `p ⊕ q`. -/
def emb (m n : ℕ) : SQ (Fin m) → SQ (Fin m ⊕ Fin n) :=
  fun x => ((Sum.inl x.1.1, Sum.inl x.1.2), Sum.inl x.2)

@[simp] theorem emb_apply (m n : ℕ) (x : SQ (Fin m)) :
    emb m n x = ((Sum.inl x.1.1, Sum.inl x.1.2), Sum.inl x.2) := rfl

theorem emb_injective (m n : ℕ) : Function.Injective (emb m n) := by
  intro x y h
  have h1 : Sum.inl x.1.1 = Sum.inl y.1.1 := congrArg (fun z => z.1.1) h
  have h2 : Sum.inl x.1.2 = Sum.inl y.1.2 := congrArg (fun z => z.1.2) h
  have h3 : Sum.inl x.2 = Sum.inl y.2 := congrArg (fun z => z.2) h
  have e1 := Sum.inl.inj h1
  have e2 := Sum.inl.inj h2
  have e3 := Sum.inl.inj h3
  exact Prod.ext (Prod.ext e1 e2) e3

@[simp] theorem emb_inj_eq (m n : ℕ) (x y : SQ (Fin m)) : emb m n x = emb m n y ↔ x = y :=
  ⟨fun h => emb_injective m n h, fun h => by rw [h]⟩

/-- The `p`-word of `SQ (Fin m ⊕ Fin n)`: the triples all of whose entries lie in the left summand. -/
def pWord (m n : ℕ) (x : SQ (Fin m ⊕ Fin n)) : Prop := ∃ y, emb m n y = x

theorem pWord_emb (m n : ℕ) (x : SQ (Fin m)) : pWord m n (emb m n x) := ⟨x, rfl⟩

/-- The cyclic permutation of the triple tensor power preserves the `p`-word, where it is the
cyclic permutation of `SQ (Fin m)`. -/
@[simp] theorem cyc3_emb (m n : ℕ) (x : SQ (Fin m)) :
    cyc3 (Fin m ⊕ Fin n) (emb m n x) = emb m n (cyc3 (Fin m) x) := rfl

@[simp] theorem cyc3_cyc3_emb (m n : ℕ) (x : SQ (Fin m)) :
    (cyc3 (Fin m ⊕ Fin n) * cyc3 (Fin m ⊕ Fin n)) (emb m n x)
      = emb m n ((cyc3 (Fin m) * cyc3 (Fin m)) x) := by
  simp [Equiv.Perm.mul_apply]

/-- The canonical equivalence `SQ (Fin m) ≃ {x // pWord m n x}`. -/
def embEquiv (m n : ℕ) : SQ (Fin m) ≃ {x : SQ (Fin m ⊕ Fin n) // pWord m n x} where
  toFun x := ⟨emb m n x, pWord_emb m n x⟩
  invFun x := x.2.choose
  left_inv x := emb_injective m n (Classical.choose_spec (pWord_emb m n x))
  right_inv x := Subtype.ext (Classical.choose_spec x.2)

/-- The block decomposition `SQ (Fin m) ⊕ (complement of the `p`-word) ≃ SQ (Fin m ⊕ Fin n)`. -/
def psiEquiv (m n : ℕ) :
    SQ (Fin m) ⊕ {x : SQ (Fin m ⊕ Fin n) // ¬ pWord m n x} ≃ SQ (Fin m ⊕ Fin n) :=
  (Equiv.sumCongr (embEquiv m n) (Equiv.refl _)).trans (Equiv.sumCompl (pWord m n))

@[simp] theorem psiEquiv_inl (m n : ℕ) (x : SQ (Fin m)) : psiEquiv m n (Sum.inl x) = emb m n x :=
  rfl

@[simp] theorem psiEquiv_inr (m n : ℕ) (x : {x : SQ (Fin m ⊕ Fin n) // ¬ pWord m n x}) :
    psiEquiv m n (Sum.inr x) = x.1 := rfl

end

end Work.KT.Psi

import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.Idx.WPen
import Submission.Work.KT.Idx.PenDefs
import Submission.Work.Idx.WPenAppendDefs

/-!
# `Work.KT.FP.PadDefs` — vocabulary for the degree-padding of the W linearisation

`Work.KT.FP.lindAt X n m P ρ` is the candidate index of a Laurent matrix `P` of degree bound `m`,
computed from the pencil projection of the `(2m+1)`-block W linearisation of the coefficient
sequence `coeffSeq X n m P = ((P)_{-m}, …, (P)_{m})`.  The invariance of this index under
`m ↦ m + 1` (`Work.KT.FP.lindAt_pad`) is the statement that the index does not depend on the degree
bound; its proof compares the `(d+1)`-block W pencil of a coefficient sequence `c` with the
`(d+2)`-block W pencils of the padded sequences

* `Work.KT.Idx.preSeq X c = (0, c₀, …, c_d)` (the polynomial `z·q_c`, one extra root at `z = 0`),
* `Work.KT.Idx.appSeq X c = (c₀, …, c_d, 0)` (the same polynomial `q_c`).

This file fixes the block decompositions used for that comparison:

* `BIdx n d = Fin (d+1) × Fin n` — the block index of the degree-`d` W linearisation;
* `ePre n d : Fin n ⊕ BIdx n d ≃ BIdx n (d+1)` — the block `0` and the remaining blocks
  `1,…,d+1` (the split in which the pencil of `preSeq X c` is block upper triangular);
* `eApp n d : BIdx n d ⊕ Fin n ≃ BIdx n (d+1)` — the blocks `0,…,d` and the last block `d+1`
  (the split in which the pencil of `appSeq X c` has its coefficient row in the last block row);
* `blkProj`, `clsBlk` — the unit-circle pencil projection of the degree-`d` W linearisation of a
  coefficient sequence, and its class in `K₀`, both on the flat index `Fin ((d+1)*n)`.

Everything here is `sorry`-free.
-/

namespace Work.KT.FP

open Matrix

noncomputable section

/-- The block index `Fin (d+1) × Fin n` of the degree-`d` W linearisation. -/
abbrev BIdx (n d : ℕ) := Fin (d + 1) × Fin n

/-- The split of `Fin (d+2) × Fin n` into the block `0` and the remaining blocks `1,…,d+1`
(the latter identified with `Fin (d+1) × Fin n`). -/
def ePre (n d : ℕ) : (Fin n ⊕ BIdx n d) ≃ BIdx n (d + 1) :=
  Equiv.ofBijective
    (fun x => match x with
      | Sum.inl a => (0, a)
      | Sum.inr i => (Fin.succ i.1, i.2))
    (by
      refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
      · rintro (a | ⟨k, a⟩) (b | ⟨l, b⟩) h
        · simpa using h
        · exact absurd (congrArg (fun p : BIdx n (d + 1) => (p.1 : ℕ)) h) (by simp [Fin.val_succ])
        · exact absurd (congrArg (fun p : BIdx n (d + 1) => (p.1 : ℕ)) h).symm (by simp [Fin.val_succ])
        · simp only [Prod.mk.injEq, Fin.succ_inj] at h
          rw [h.1, h.2]
      · have h1 : Fintype.card (Fin n ⊕ BIdx n d) = n + (d + 1) * n := by
          simp [Fintype.card_sum, Fintype.card_prod]
        have h2 : Fintype.card (BIdx n (d + 1)) = (d + 2) * n := by
          simp [Fintype.card_prod]
        rw [h1, h2]
        ring)

/-- The split of `Fin (d+2) × Fin n` into the blocks `0,…,d` and the last block `d+1`. -/
def eApp (n d : ℕ) : (BIdx n d ⊕ Fin n) ≃ BIdx n (d + 1) :=
  Equiv.ofBijective
    (fun x => match x with
      | Sum.inl i => (Fin.castSucc i.1, i.2)
      | Sum.inr a => (Fin.last (d + 1), a))
    (by
      refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
      · rintro (⟨k, a⟩ | a) (⟨l, b⟩ | b) h
        · simp only [Prod.mk.injEq, Fin.castSucc_inj] at h
          rw [h.1, h.2]
        · exfalso
          have hk : (k : ℕ) < d + 1 := k.isLt
          have hv := congrArg (fun p : BIdx n (d + 1) => (p.1 : ℕ)) h
          simp only [Fin.val_castSucc, Fin.val_last] at hv
          omega
        · exfalso
          have hl : (l : ℕ) < d + 1 := l.isLt
          have hv := congrArg (fun p : BIdx n (d + 1) => (p.1 : ℕ)) h
          simp only [Fin.val_castSucc, Fin.val_last] at hv
          omega
        · simpa using h
      · have h1 : Fintype.card (BIdx n d ⊕ Fin n) = (d + 1) * n + n := by
          simp [Fintype.card_sum, Fintype.card_prod]
        have h2 : Fintype.card (BIdx n (d + 1)) = (d + 2) * n := by
          simp [Fintype.card_prod]
        rw [h1, h2]
        ring)

@[simp] theorem ePre_inl (n d : ℕ) (a : Fin n) : ePre n d (Sum.inl a) = (0, a) := rfl

@[simp] theorem ePre_inr (n d : ℕ) (i : BIdx n d) :
    ePre n d (Sum.inr i) = (Fin.succ i.1, i.2) := rfl

@[simp] theorem eApp_inl (n d : ℕ) (i : BIdx n d) :
    eApp n d (Sum.inl i) = (Fin.castSucc i.1, i.2) := rfl

@[simp] theorem eApp_inr (n d : ℕ) (a : Fin n) :
    eApp n d (Sum.inr a) = (Fin.last (d + 1), a) := rfl

/-- `ePre` followed by the flat reindexing. -/
def ePreFlat (n d : ℕ) : (Fin n ⊕ BIdx n d) ≃ Fin ((d + 2) * n) :=
  (ePre n d).trans finProdFinEquiv

/-- `eApp` followed by the flat reindexing. -/
def eAppFlat (n d : ℕ) : (BIdx n d ⊕ Fin n) ≃ Fin ((d + 2) * n) :=
  (eApp n d).trans finProdFinEquiv

@[simp] theorem ePreFlat_apply (n d : ℕ) (x : Fin n ⊕ BIdx n d) :
    ePreFlat n d x = finProdFinEquiv (ePre n d x) := rfl

@[simp] theorem eAppFlat_apply (n d : ℕ) (x : BIdx n d ⊕ Fin n) :
    eAppFlat n d x = finProdFinEquiv (eApp n d x) := rfl

/-- Reindexing along a composite is the composite of the reindexings. -/
theorem reindex_trans {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (e : ι₁ ≃ ι₂) (f : ι₂ ≃ ι₃) {α : Type*} (M : Matrix ι₁ ι₁ α) :
    Matrix.reindex (e.trans f) (e.trans f) M = Matrix.reindex f f (Matrix.reindex e e M) := by
  ext i j
  simp [Matrix.reindex_apply]

end

end Work.KT.FP

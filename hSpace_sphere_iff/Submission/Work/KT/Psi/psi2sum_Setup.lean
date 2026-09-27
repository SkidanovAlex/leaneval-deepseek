import Mathlib
import Submission.Work.KT.Psi.Basic

/-!
# `Work.KT.Psi.psi2sum_Setup` — infrastructure for `psi2Cls_sum`

Additivity of `ψ²` on `K₀` is proved by decomposing `(p ⊕ q) ⊗ (p ⊕ q)` into four blocks
according to the decomposition `ι ⊕ κ` of the index set of `p ⊕ q`, and observing that the
symmetric/exterior projectors act blockwise, the "mixed" block `p ⊗ q ⊕ q ⊗ p` contributing the
same class for `ε = 1` and `ε = -1`.

This file contains the definitions and the elementary matrix identities:

* `cls_ofIdx_irrel`, `clsI` — the class of a square matrix over an arbitrary finite index type,
  well defined without idempotency hypotheses;
* `quadEquiv` — the four-block decomposition `(ι ⊕ κ) × (ι ⊕ κ) ≃ (ι × ι) ⊕ ((ι × κ) ⊕ (κ × ι)) ⊕ (κ × κ)`;
* `quadEquiv_kron`, `quadEquiv_perm` — the block forms of the Kronecker square and of the
  permutation matrix of the swap;
* `reindex_prodCongr_sq2PartP` — `sq2PartP ε (p.sum q)` expressed in terms of `p ⊗ q`;
* `kronP`, `midRaw`, `midPart`, `sqBlock` — the pieces of the block decomposition.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

/-! ## The class of a matrix over an arbitrary finite index type -/

theorem cls_ofIdx_irrel {R : Type} [Ring R] {ι : Type} [Fintype ι] (M : Matrix ι ι R)
    {n n' : ℕ} (e : ι ≃ Fin n) (e' : ι ≃ Fin n') :
    cls (Mat.ofIdx M n e) = cls (Mat.ofIdx M n' e') := by
  by_cases hM : M * M = M
  · exact clsE_wellDefined hM e e'
  · have h1 : ¬ (Mat.ofIdx M n e).IsIdem := by
      rintro hc
      change (Matrix.reindex e e M) * (Matrix.reindex e e M) = Matrix.reindex e e M at hc
      refine hM ?_
      have hc' : (Matrix.reindexRingEquiv R e) (M * M) = (Matrix.reindexRingEquiv R e) M := by
        rw [map_mul]
        exact hc
      exact (Matrix.reindexRingEquiv R e).injective hc'
    have h2 : ¬ (Mat.ofIdx M n' e').IsIdem := by
      rintro hc
      change (Matrix.reindex e' e' M) * (Matrix.reindex e' e' M) = Matrix.reindex e' e' M at hc
      refine hM ?_
      have hc' : (Matrix.reindexRingEquiv R e') (M * M) = (Matrix.reindexRingEquiv R e') M := by
        rw [map_mul]
        exact hc
      exact (Matrix.reindexRingEquiv R e').injective hc'
    rw [cls_zero_of_not_idem h1, cls_zero_of_not_idem h2]

/-- The class of a square matrix over an arbitrary finite index type. -/
def clsI {R : Type} [Ring R] {ι : Type} [Fintype ι] (M : Matrix ι ι R) : K0 R :=
  clsE M (Fintype.card ι) (Fintype.equivFin ι)

theorem clsI_eq {R : Type} [Ring R] {ι : Type} [Fintype ι] (M : Matrix ι ι R)
    {n : ℕ} (e : ι ≃ Fin n) : clsI M = cls (Mat.ofIdx M n e) :=
  cls_ofIdx_irrel M (Fintype.equivFin ι) e

theorem clsI_reindex {R : Type} [Ring R] {ι κ : Type} [Fintype ι] [Fintype κ]
    (g : ι ≃ κ) (M : Matrix ι ι R) :
    clsI (Matrix.reindex g g M) = clsI M := by
  rw [clsI_eq (Matrix.reindex g g M) (g.symm.trans (Fintype.equivFin ι)),
    clsI_eq M (Fintype.equivFin ι)]
  exact clsE_reindex M (Fintype.card ι) (Fintype.equivFin ι) g

/-! ## The four-block decomposition of a product index set -/

/-- `(ι ⊕ κ) × (ι ⊕ κ) ≃ (ι × ι) ⊕ ((ι × κ) ⊕ (κ × ι)) ⊕ (κ × κ)`. -/
def quadEquiv (ι κ : Type) : ((ι ⊕ κ) × (ι ⊕ κ)) ≃ (ι × ι ⊕ (ι × κ ⊕ κ × ι)) ⊕ (κ × κ) where
  toFun x := match x.1, x.2 with
    | Sum.inl a, Sum.inl b => Sum.inl (Sum.inl (a, b))
    | Sum.inl a, Sum.inr b => Sum.inl (Sum.inr (Sum.inl (a, b)))
    | Sum.inr a, Sum.inl b => Sum.inl (Sum.inr (Sum.inr (a, b)))
    | Sum.inr a, Sum.inr b => Sum.inr (a, b)
  invFun y := match y with
    | Sum.inl (Sum.inl (a, b)) => (Sum.inl a, Sum.inl b)
    | Sum.inl (Sum.inr (Sum.inl (a, b))) => (Sum.inl a, Sum.inr b)
    | Sum.inl (Sum.inr (Sum.inr (a, b))) => (Sum.inr a, Sum.inl b)
    | Sum.inr (a, b) => (Sum.inr a, Sum.inr b)
  left_inv := by rintro ⟨a | a, b | b⟩ <;> rfl
  right_inv := by rintro ((⟨a, b⟩ | (⟨a, b⟩ | ⟨a, b⟩)) | ⟨a, b⟩) <;> rfl

/-- The "relabelling matrix" of an equivalence `e : ι ≃ κ`, with rows `ι` and columns `κ`. -/
def relMat (R : Type) [Zero R] [One R] {ι κ : Type} [DecidableEq κ] (e : ι ≃ κ) :
    Matrix ι κ R := fun i j => if e i = j then 1 else 0

theorem matrix_reindex_apply_apply {R : Type} {α β : Type} (e : α ≃ β)
    (X : Matrix α α R) (x y : α) :
    Matrix.reindex e e X (e x) (e y) = X x y := by
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

theorem quadEquiv_kron {R : Type} [Ring R] {ι κ : Type}
    (p : Matrix ι ι R) (q : Matrix κ κ R) :
    Matrix.reindex (quadEquiv ι κ) (quadEquiv ι κ)
        (Matrix.kroneckerMap (· * ·) (Matrix.fromBlocks p 0 0 q) (Matrix.fromBlocks p 0 0 q))
      = Matrix.fromBlocks
          (Matrix.fromBlocks (Matrix.kroneckerMap (· * ·) p p) 0 0
            (Matrix.fromBlocks (Matrix.kroneckerMap (· * ·) p q) 0 0
              (Matrix.kroneckerMap (· * ·) q p)))
          0 0 (Matrix.kroneckerMap (· * ·) q q) := by
  ext u v
  obtain ⟨x, rfl⟩ := (quadEquiv ι κ).surjective u
  obtain ⟨y, rfl⟩ := (quadEquiv ι κ).surjective v
  rw [matrix_reindex_apply_apply]
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> rcases d with d | d <;>
    simp [Matrix.kroneckerMap_apply, quadEquiv]

theorem quadEquiv_perm {R : Type} [Ring R] {ι κ : Type} [DecidableEq ι] [DecidableEq κ] :
    Matrix.reindex (quadEquiv ι κ) (quadEquiv ι κ)
        (Equiv.Perm.permMatrix R (Equiv.prodComm (ι ⊕ κ) (ι ⊕ κ)))
      = Matrix.fromBlocks
          (Matrix.fromBlocks (Equiv.Perm.permMatrix R (Equiv.prodComm ι ι)) 0 0
            (Matrix.fromBlocks 0 (relMat R (Equiv.prodComm ι κ))
              (relMat R (Equiv.prodComm κ ι)) 0))
          0 0 (Equiv.Perm.permMatrix R (Equiv.prodComm κ κ)) := by
  ext u v
  obtain ⟨x, rfl⟩ := (quadEquiv ι κ).surjective u
  obtain ⟨y, rfl⟩ := (quadEquiv ι κ).surjective v
  rw [matrix_reindex_apply_apply]
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> rcases d with d | d <;>
    simp [quadEquiv, relMat, Equiv.prodComm_apply]

/-! ## The pieces of the block decomposition of `(p ⊕ q) ⊗ (p ⊕ q)` -/

section Adams

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- The Kronecker square `p ⊗ q`, on the product index set `Fin p.1 × Fin q.1`. -/
def kronP (p q : Mat A) : Matrix (Fin p.1 × Fin q.1) (Fin p.1 × Fin q.1) A :=
  Matrix.kroneckerMap (· * ·) p.2 q.2

/-- The "mixed" block `p ⊗ q ⊕ q ⊗ p` with the `ε`-projector applied, on
`(Fin p.1 × Fin q.1) ⊕ (Fin q.1 × Fin p.1)`. -/
def midRaw (ε : ℂ) (p q : Mat A) :
    Matrix ((Fin p.1 × Fin q.1) ⊕ (Fin q.1 × Fin p.1))
      ((Fin p.1 × Fin q.1) ⊕ (Fin q.1 × Fin p.1)) A :=
  algebraMap ℂ A (1/2) • Matrix.fromBlocks (kronP p q)
    (algebraMap ℂ A ε • (kronP p q * relMat A (Equiv.prodComm (Fin p.1) (Fin q.1))))
    (algebraMap ℂ A ε • (kronP q p * relMat A (Equiv.prodComm (Fin q.1) (Fin p.1))))
    (kronP q p)

/-- The mixed block after relabelling the second summand by `(a, b) ↦ (b, a)`. -/
def midPart (ε : ℂ) (p q : Mat A) :
    Matrix ((Fin p.1 × Fin q.1) ⊕ (Fin p.1 × Fin q.1))
      ((Fin p.1 × Fin q.1) ⊕ (Fin p.1 × Fin q.1)) A :=
  algebraMap ℂ A (1/2) • Matrix.fromBlocks (kronP p q)
    (algebraMap ℂ A ε • kronP p q) (algebraMap ℂ A ε • kronP p q) (kronP p q)

/-- The block decomposition of `(p ⊕ q) ⊗ (p ⊕ q)` with the `ε`-projector applied. -/
def sqBlock (ε : ℂ) (p q : Mat A) :
    Matrix (((Fin p.1 × Fin p.1) ⊕ ((Fin p.1 × Fin q.1) ⊕ (Fin q.1 × Fin p.1))) ⊕
        (Fin q.1 × Fin q.1))
      (((Fin p.1 × Fin p.1) ⊕ ((Fin p.1 × Fin q.1) ⊕ (Fin q.1 × Fin p.1))) ⊕
        (Fin q.1 × Fin q.1)) A :=
  Matrix.fromBlocks (Matrix.fromBlocks (sq2PartP ε p) 0 0 (midRaw ε p q)) 0 0 (sq2PartP ε q)

end Adams

end

end Work.KT.Psi

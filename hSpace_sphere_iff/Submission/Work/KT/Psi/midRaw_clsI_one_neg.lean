import Mathlib
import Submission.Work.KT.Psi.psi2sum_Setup
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.cls_conj
import Submission.Work.KT.Defs

/-!
# `Work.KT.Psi.midRaw_clsI_one_neg`

The "mixed" block `midRaw ε p q` of the block decomposition of `(p ⊕ q) ⊗ (p ⊕ q)` carries the
same `K₀`-class for `ε = 1` (symmetric projector) and `ε = -1` (alternating projector):

`clsI (midRaw 1 p q) = clsI (midRaw (-1) p q)`.

Mathematically, `midRaw ε p q` is `½ • [[X, εY], [εZ, W]]` where `X = p ⊗ q`, `W = q ⊗ p` and
`Y, Z` are the off-diagonal blocks that interchange the two summands.  Conjugating by the
invertible diagonal matrix `D = diag(1, -1)` flips precisely the signs of the two off-diagonal
blocks, so

`D * midRaw 1 p q * D = midRaw (-1) p q`,

and `K₀`-classes are invariant under conjugation by a unit (`clsI_conj` below, which is the
`clsI`-version of `Work.KT.Psi.cls_conj` for matrices over an arbitrary finite index type).

No commutativity of `A` is needed: the sign flip is a genuine conjugation, not a relabelling.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

/-- **Conjugation invariance of `clsI`.**  If `u` and `v` are mutually inverse matrices, then
conjugating a square matrix over an arbitrary finite index type by them does not change its
`K₀`-class.  (Reduced to `Work.KT.Psi.cls_conj`, which is stated for `Fin n`.) -/
theorem clsI_conj {R : Type} [Ring R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (P u v : Matrix ι ι R) (huv : u * v = 1) (hvu : v * u = 1) :
    clsI (u * P * v) = clsI P := by
  have e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  rw [clsI_eq (u * P * v) e, clsI_eq P e]
  have hstep1 : Matrix.reindex e e (u * P * v) =
      Matrix.reindex e e (u * P) * Matrix.reindex e e v :=
    map_mul (Matrix.reindexRingEquiv R e) (u * P) v
  have hstep2 : Matrix.reindex e e (u * P) =
      Matrix.reindex e e u * Matrix.reindex e e P :=
    map_mul (Matrix.reindexRingEquiv R e) u P
  have hstep3 : Matrix.reindex e e (u * v) =
      Matrix.reindex e e u * Matrix.reindex e e v :=
    map_mul (Matrix.reindexRingEquiv R e) u v
  have hstep4 : Matrix.reindex e e (v * u) =
      Matrix.reindex e e v * Matrix.reindex e e u :=
    map_mul (Matrix.reindexRingEquiv R e) v u
  have hone : Matrix.reindex e e (1 : Matrix ι ι R) = 1 :=
    map_one (Matrix.reindexRingEquiv R e)
  have hmul : Matrix.reindex e e (u * P * v) =
      Matrix.reindex e e u * Matrix.reindex e e P * Matrix.reindex e e v := by
    rw [hstep1, hstep2, Matrix.mul_assoc]
  have huv' : Matrix.reindex e e u * Matrix.reindex e e v = 1 := by
    rw [← hstep3, huv, hone]
  have hvu' : Matrix.reindex e e v * Matrix.reindex e e u = 1 := by
    rw [← hstep4, hvu, hone]
  show cls (⟨Fintype.card ι, Matrix.reindex e e (u * P * v)⟩ : Mat R) =
    cls (⟨Fintype.card ι, Matrix.reindex e e P⟩ : Mat R)
  rw [hmul]
  exact cls_conj R (Fintype.card ι) (Matrix.reindex e e P) (Matrix.reindex e e u)
    (Matrix.reindex e e v) huv' hvu'

theorem midRaw_clsI_one_neg {A : Type} [Ring A] [Algebra ℂ A] {p q : Work.KT.Mat A} :
    Work.KT.Psi.clsI (Work.KT.Psi.midRaw 1 p q) = Work.KT.Psi.clsI (Work.KT.Psi.midRaw (-1) p q) := by
  -- the sign-flipping diagonal matrix `diag(1, -1)`, which is its own inverse
  set D : Matrix ((Fin p.1 × Fin q.1) ⊕ (Fin q.1 × Fin p.1))
      ((Fin p.1 × Fin q.1) ⊕ (Fin q.1 × Fin p.1)) A := Matrix.fromBlocks 1 0 0 (-1) with hDdef
  -- `midRaw ε p q` in terms of the four blocks, with the scalar `1/2` pulled out
  have h1 : midRaw (1:ℂ) p q = (1/2 : ℂ) • Matrix.fromBlocks (kronP p q)
      (kronP p q * relMat A (Equiv.prodComm (Fin p.1) (Fin q.1)))
      (kronP q p * relMat A (Equiv.prodComm (Fin q.1) (Fin p.1))) (kronP q p) := by
    simp only [midRaw, IsScalarTower.algebraMap_smul, one_smul]
  have h2 : midRaw (-1:ℂ) p q = (1/2 : ℂ) • Matrix.fromBlocks (kronP p q)
      (-(kronP p q * relMat A (Equiv.prodComm (Fin p.1) (Fin q.1))))
      (-(kronP q p * relMat A (Equiv.prodComm (Fin q.1) (Fin p.1)))) (kronP q p) := by
    simp only [midRaw, IsScalarTower.algebraMap_smul, map_neg, map_one, neg_one_smul]
  have hDD : D * D = 1 := by
    rw [hDdef, Matrix.fromBlocks_multiply]
    simp
  -- conjugation by `D` flips the signs of the off-diagonal blocks
  have hconj : D * midRaw (1:ℂ) p q * D = midRaw (-1:ℂ) p q := by
    rw [h1, h2, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [hDdef, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  rw [← hconj]
  exact (clsI_conj (midRaw (1:ℂ) p q) D D hDD hDD).symm

end

end Work.KT.Psi

import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.ClsM
import Submission.Work.KT.Psi.cubeMvNAux
import Submission.Work.KT.Psi.k3Aux
import Submission.Work.KT.Psi.psi2sum_Setup

/-!
# `Work.KT.Psi.psi3sum_Setup` — the block framework for `psi3Cls_sum`

Additivity of `ψ³` on generators is proved by decomposing the triple tensor power
`(p ⊕ q)^{⊗3}` into the eight "words" in `{p, q}`, on each of which the cyclic permutation
`c = cyc3` acts, and observing that the two *mixed* orbits (`pq`-type words) are permuted freely
by `c`, so that *every* eigenspace of `c` on a free orbit has the class of one block, while the two
constant words give exactly `cubePart λ p` and `cubePart λ q`.

This file sets up the index types (`SQ`, `cyc3`), the block projectors `eBlk w`, the triple
tensor product `kron3m`/`kron3g`, and the two "per-word" matrices `T`, `Cp`.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

/-! ## The triple index type -/

/-- The index type of a triple tensor product. -/
abbrev SQ (S : Type) : Type := (S × S) × S

/-- The cyclic permutation `((a,b),c) ↦ ((c,a),b)` of `SQ S`. -/
def cyc3 (S : Type) : Equiv.Perm (SQ S) where
  toFun x := ((x.2, x.1.1), x.1.2)
  invFun x := ((x.1.2, x.2), x.1.1)
  left_inv x := by rcases x with ⟨⟨a, b⟩, c⟩; rfl
  right_inv x := by rcases x with ⟨⟨a, b⟩, c⟩; rfl

@[simp] theorem cyc3_apply (S : Type) (x : SQ S) : cyc3 S x = ((x.2, x.1.1), x.1.2) := rfl
@[simp] theorem cyc3_symm_apply (S : Type) (x : SQ S) :
    (cyc3 S).symm x = ((x.1.2, x.2), x.1.1) := rfl

theorem cyc3_cube_apply (S : Type) (x : SQ S) : (cyc3 S * cyc3 S * cyc3 S) x = x := by
  rcases x with ⟨⟨a, b⟩, c⟩; rfl

theorem cyc3_cube (S : Type) : cyc3 S * cyc3 S * cyc3 S = 1 := by
  apply Equiv.ext; intro x; exact cyc3_cube_apply S x

/-- The index lift `SQ α ≃ SQ β` of an equivalence `α ≃ β`. -/
def e3 {α β : Type} (e : α ≃ β) : SQ α ≃ SQ β := (e.prodCongr e).prodCongr e

@[simp] theorem e3_apply {α β : Type} (e : α ≃ β) (x : SQ α) :
    e3 e x = ((e x.1.1, e x.1.2), e x.2) := rfl
@[simp] theorem e3_symm_apply {α β : Type} (e : α ≃ β) (x : SQ β) :
    (e3 e).symm x = ((e.symm x.1.1, e.symm x.1.2), e.symm x.2) := rfl

@[simp] theorem e3_refl {α : Type} : e3 (Equiv.refl α) = Equiv.refl (SQ α) := by
  refine Equiv.ext ?_; intro x; rcases x with ⟨⟨a,b⟩,c⟩; rfl

/-- `e3` transports the cyclic permutation. -/
theorem e3_cyc3 {α β : Type} (e : α ≃ β) :
    (e3 e).symm.trans ((cyc3 α).trans (e3 e)) = cyc3 β := by
  apply Equiv.ext
  intro x
  rcases x with ⟨⟨a, b⟩, c⟩
  simp [e3, cyc3]

/-! ## The triple tensor product, with possibly different factors -/

/-- Triple tensor product `X ⊗ Y ⊗ Z` on the index type `SQ S`. -/
def kron3m {A : Type} [Mul A] {S : Type} (X Y Z : Matrix S S A) : Matrix (SQ S) (SQ S) A :=
  Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) X Y) Z

/-- Triple tensor product `X ⊗ X ⊗ X`. -/
def kron3g {A : Type} [Mul A] {S : Type} (X : Matrix S S A) : Matrix (SQ S) (SQ S) A :=
  kron3m X X X

@[simp] theorem kron3m_apply {A : Type} [Mul A] {S : Type} (X Y Z : Matrix S S A)
    (u v : SQ S) : kron3m X Y Z u v = (X u.1.1 v.1.1 * Y u.1.2 v.1.2) * Z u.2 v.2 := rfl

@[simp] theorem kron3g_apply {A : Type} [Mul A] {S : Type} (X : Matrix S S A)
    (u v : SQ S) : kron3g X u v = (X u.1.1 v.1.1 * X u.1.2 v.1.2) * X u.2 v.2 := rfl

theorem kron3g_eq_kron3 {A : Type} [Ring A] {n : ℕ} (X : Matrix (Fin n) (Fin n) A) :
    kron3g X = kron3r X := rfl

/-! ## The setup for `p ⊕ q` -/

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- The block matrix of `p ⊕ q` on the index type `Fin p.1 ⊕ Fin q.1`. -/
def sumBlk (p q : Mat A) : Matrix (Fin p.1 ⊕ Fin q.1) (Fin p.1 ⊕ Fin q.1) A :=
  Matrix.fromBlocks p.2 0 0 q.2

/-- The `p`-only part of `sumBlk p q`. -/
def sumBlkP (p q : Mat A) : Matrix (Fin p.1 ⊕ Fin q.1) (Fin p.1 ⊕ Fin q.1) A :=
  Matrix.fromBlocks p.2 0 0 0

/-- The `q`-only part of `sumBlk p q`. -/
def sumBlkQ (p q : Mat A) : Matrix (Fin p.1 ⊕ Fin q.1) (Fin p.1 ⊕ Fin q.1) A :=
  Matrix.fromBlocks 0 0 0 q.2

/-- The tensor coordinate projector: `0 ↦ 1_{Fin m}`, `1 ↦ 1_{Fin n}`. -/
def coord {m n : ℕ} (i : Fin 2) : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) A :=
  if i = 0 then Matrix.fromBlocks 1 0 0 0 else Matrix.fromBlocks 0 0 0 1

/-- The block projector of the word `w = (w₁,w₂,w₃)`: the tensor product of the coordinate
projectors. -/
def eBlk {m n : ℕ} (w : (Fin 2 × Fin 2) × Fin 2) :
    Matrix (SQ (Fin m ⊕ Fin n)) (SQ (Fin m ⊕ Fin n)) A :=
  kron3m (coord (m := m) (n := n) w.1.1) (coord w.1.2) (coord w.2)

/-- The spectral projector `(1 + λ⁻¹ c + λ⁻² c²)/3` of the cyclic permutation, on `SQ S`. -/
def Cp (S : Type) [Fintype S] [DecidableEq S] (lam : ℂ) : Matrix (SQ S) (SQ S) A :=
  algebraMap ℂ A (1 / 3) •
    (1 + algebraMap ℂ A lam⁻¹ • (cyc3 S).permMatrix A +
      algebraMap ℂ A ((lam⁻¹) ^ 2) •
        ((cyc3 S).permMatrix A * (cyc3 S).permMatrix A))

/-! ## The cyclic permutation matrix, the block orbit, and the word constants -/

/-- The permutation matrix of the cyclic permutation `cyc3 S`. -/
def uPerm (A : Type) [Ring A] (S : Type) [Fintype S] [DecidableEq S] :
    Matrix (SQ S) (SQ S) A := (cyc3 S).permMatrix A

/-- The rotation of words induced by conjugating a block projector by the cyclic permutation
matrix: `u * eBlk w * u⁻¹ = eBlk (rotW w)`, with `rotW (w₁,w₂,w₃) = (w₂,w₃,w₁)`. -/
def rotW (w : (Fin 2 × Fin 2) × Fin 2) : (Fin 2 × Fin 2) × Fin 2 :=
  ((w.1.2, w.2), w.1.1)

/-- The free orbit of a block projector under the cyclic permutation:
`e + u e u² + u² e u` (note `u² = u⁻¹`). -/
def orb3 {A : Type} [Ring A] (S : Type) [Fintype S] [DecidableEq S]
    (e : Matrix (SQ S) (SQ S) A) : Matrix (SQ S) (SQ S) A :=
  e + uPerm A S * e * (uPerm A S * uPerm A S) +
    (uPerm A S * uPerm A S) * e * uPerm A S

/-- The word `(0,0,0)`. -/
def w000 : (Fin 2 × Fin 2) × Fin 2 := ((0, 0), 0)
/-- The word `(1,1,1)`. -/
def w111 : (Fin 2 × Fin 2) × Fin 2 := ((1, 1), 1)
/-- The word `(0,0,1)`. -/
def w001 : (Fin 2 × Fin 2) × Fin 2 := ((0, 0), 1)
/-- The word `(0,1,1)`. -/
def w011 : (Fin 2 × Fin 2) × Fin 2 := ((0, 1), 1)

/-- The class in `K₀` of `cubePartP lam p` (over its own index type) is `cls (cubePart lam p)`. -/
theorem clsM_I3_cubePartP {A : Type} [Ring A] [Algebra ℂ A] (lam : ℂ) (p : Mat A) :
    clsM (SQ (Fin p.1)) (cubePartP lam p) = cls (cubePart lam p) := by
  rw [show clsM (SQ (Fin p.1)) (cubePartP lam p) =
      clsE (cubePartP lam p) (p.1 * p.1 * p.1) (cycIdx p.1).symm from
    cls_ofIdx_irrel (cubePartP lam p) (Fintype.equivFin (SQ (Fin p.1))) (cycIdx p.1).symm]
  exact cls_cubePartP lam p

end

end Work.KT.Psi

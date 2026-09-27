import Mathlib
import Submission.Work.KT.Idx.WPen
import Submission.Work.KT.Idx.PenDefs
import Submission.Work.KT.Basic

/-!
# `Work.Idx.WPenAppendDefs` — shared vocabulary for `Work.Idx.wPen_append`

Three layers, all `sorry`-free so that lemmas about them can be delegated:

1. `penProjMat X A B` — the Riesz projection `(2πi)⁻¹ ∮_{|z|=1} (zA+B)⁻¹ A dz` of a matrix pencil
   over `C(X, ℂ)`, for a matrix indexed by an **arbitrary** finite type `ι` (the definition in
   `PenDefs` only covers `Fin N`); `matPenProj` is the `Fin N` case
   (`matPenProj_eq_penProjMat`).
2. `MvNGen p q` — Murray–von Neumann equivalence for square matrices on arbitrary finite index
   types (`Mat.MvN` is the `Fin N` case); reindexing and transfer lemmas.
3. The block decomposition `Fin (d+2) × Fin n ≃ (Fin (d+1) × Fin n) ⊕ Fin n` (`eb`) of the
   `(d+2)`-block companion pencil together with its block matrices: `Ecol`, `Erow`, `BBl`, `rowb`
   and the auxiliary matrices `Ablk`, `Bblk` (the `(d+2)`-block pencil in block form), `Adiag`,
   `Bdiag` (the block diagonal pencil `diag(M_b, -1)`), `Smat` (the block swap of the last two
   block rows) and `Rmat` (the shear `v_{d+1} ↦ v_{d+1} - z v_d`).
-/

namespace Work.Idx

open Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The pencil projection `(2πi)⁻¹ ∮_{|z| = 1} (z • A + B)⁻¹ * A dz` for matrices over `C(X, ℂ)`
indexed by an arbitrary finite type `ι`. -/
def penProjMat {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι C(X, ℂ)) : Matrix ι ι C(X, ℂ) :=
  letI : NormedRing (Matrix ι ι C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix ι ι C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  Work.KT.Idx.penProj A B

/-- `matPenProj` is the `Fin N` case of `penProjMat`. -/
theorem matPenProj_eq_penProjMat {N : ℕ} (A B : Matrix (Fin N) (Fin N) C(X, ℂ)) :
    Work.KT.Idx.matPenProj X A B = penProjMat X A B := rfl

section MvNGen

variable {R : Type*} [Ring R]

/-- Murray–von Neumann equivalence for square matrices on arbitrary finite index types:
`p : Matrix ι₁ ι₁ R` and `q : Matrix ι₂ ι₂ R` are equivalent if there are rectangular matrices
`a : Matrix ι₂ ι₁ R`, `b : Matrix ι₁ ι₂ R` with `b * a = p` and `a * b = q`. -/
def MvNGen {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (p : Matrix ι₁ ι₁ R) (q : Matrix ι₂ ι₂ R) : Prop :=
  ∃ a : Matrix ι₂ ι₁ R, ∃ b : Matrix ι₁ ι₂ R, b * a = p ∧ a * b = q


/-- The block matrix `(P 0; C 0)`, with row type `ι ⊕ κ` and column type `ι ⊕ κ`. -/
def fromBlocks20 {R : Type*} [Ring R] {ι κ : Type*} (P : Matrix ι ι R) (C : Matrix κ ι R) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) R :=
  Matrix.fromBlocks P (0 : Matrix ι κ R) C (0 : Matrix κ κ R)

@[simp] lemma fromBlocks20_apply_inl_inl {R : Type*} [Ring R] {ι κ : Type*}
    (P : Matrix ι ι R) (C : Matrix κ ι R) (i j : ι) :
    fromBlocks20 P C (Sum.inl i) (Sum.inl j) = P i j := by
  simp [fromBlocks20, Matrix.fromBlocks]

@[simp] lemma fromBlocks20_apply_inr_inl {R : Type*} [Ring R] {ι κ : Type*}
    (P : Matrix ι ι R) (C : Matrix κ ι R) (i : κ) (j : ι) :
    fromBlocks20 P C (Sum.inr i) (Sum.inl j) = C i j := by
  simp [fromBlocks20, Matrix.fromBlocks]

@[simp] lemma fromBlocks20_apply_inl_inr {R : Type*} [Ring R] {ι κ : Type*}
    (P : Matrix ι ι R) (C : Matrix κ ι R) (i : ι) (j : κ) :
    fromBlocks20 P C (Sum.inl i) (Sum.inr j) = 0 := by
  simp [fromBlocks20, Matrix.fromBlocks]

@[simp] lemma fromBlocks20_apply_inr_inr {R : Type*} [Ring R] {ι κ : Type*}
    (P : Matrix ι ι R) (C : Matrix κ ι R) (i j : κ) :
    fromBlocks20 P C (Sum.inr i) (Sum.inr j) = 0 := by
  simp [fromBlocks20, Matrix.fromBlocks]

/-- `Mat.MvN` is `MvNGen`. -/
lemma Mat.mvN_eq_MvNGen {R : Type} [Ring R] {n m : ℕ}
    (p : Matrix (Fin n) (Fin n) R) (q : Matrix (Fin m) (Fin m) R) :
    Work.KT.Mat.MvN ⟨n, p⟩ ⟨m, q⟩ = MvNGen p q := rfl

/-- Rectangular reindexing is multiplicative (universe-polymorphic version of
`Work.KT.reindexMul`). -/
lemma reindexMul' {A : Type*} [AddCommMonoid A] [Mul A]
    {m m' n n' p p' : Type*} [Fintype n] [Fintype n']
    (e : m ≃ m') (f : n ≃ n') (g : p ≃ p') (X : Matrix m n A) (Y : Matrix n p A) :
    Matrix.reindex e f X * Matrix.reindex f g Y = Matrix.reindex e g (X * Y) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply]
  exact Matrix.submatrix_mul_equiv X Y e.symm f.symm g.symm

/-- `MvNGen` is unaffected by reindexing both matrices. -/
theorem MvNGen_reindex {ι₁ ι₁' ι₂ ι₂' : Type*} [Fintype ι₁] [Fintype ι₁'] [Fintype ι₂]
    [Fintype ι₂'] (e₁ : ι₁ ≃ ι₁') (e₂ : ι₂ ≃ ι₂')
    (p : Matrix ι₁ ι₁ R) (q : Matrix ι₂ ι₂ R) :
    MvNGen (Matrix.reindex e₁ e₁ p) (Matrix.reindex e₂ e₂ q) ↔ MvNGen p q := by
  constructor
  · rintro ⟨a, b, hba, hab⟩
    refine ⟨Matrix.reindex e₂.symm e₁.symm a, Matrix.reindex e₁.symm e₂.symm b, ?_, ?_⟩
    · rw [reindexMul' e₁.symm e₂.symm e₁.symm b a, hba]
      ext i j
      simp [Matrix.reindex_apply]
    · rw [reindexMul' e₂.symm e₁.symm e₂.symm a b, hab]
      ext i j
      simp [Matrix.reindex_apply]
  · rintro ⟨a, b, hba, hab⟩
    refine ⟨Matrix.reindex e₂ e₁ a, Matrix.reindex e₁ e₂ b, ?_, ?_⟩
    · rw [reindexMul' e₁ e₂ e₁ b a, hba]
    · rw [reindexMul' e₂ e₁ e₂ a b, hab]

/-- Reindexing a `MvNGen` pair to `Fin` types gives a `Mat.MvN`. -/
theorem MvNGen.toMat {R : Type} [Ring R] {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {n m : ℕ}
    (e : ι₁ ≃ Fin n) (f : ι₂ ≃ Fin m) {p : Matrix ι₁ ι₁ R} {q : Matrix ι₂ ι₂ R}
    (h : MvNGen p q) :
    Work.KT.Mat.MvN ⟨n, Matrix.reindex e e p⟩ ⟨m, Matrix.reindex f f q⟩ := by
  obtain ⟨a, b, hba, hab⟩ := h
  refine ⟨Matrix.reindex f e a, Matrix.reindex e f b, ?_, ?_⟩
  · rw [reindexMul' e f e b a, hba]
  · rw [reindexMul' f e f a b, hab]

/-- Reindexing preserves idempotency. -/
theorem isIdem_reindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    {p : Matrix ι ι R} (hp : p * p = p) :
    Matrix.reindex e e p * Matrix.reindex e e p = Matrix.reindex e e p := by
  rw [reindexMul' e e e p p, hp]

end MvNGen

/-! ## The `(d+1) ⊕ 1` block decomposition of the `(d+2)`-block index -/

section Block

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable {n d : ℕ}
variable (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))

/-- The block index of the `(d+1)`-block W pencil. -/
abbrev WIdx (n d : ℕ) := Fin (d + 1) × Fin n

/-- The last block `d+1` of `Fin (d+2)`. -/
def lastIdx (d : ℕ) : Fin (d + 2) := ⟨d + 1, by omega⟩

/-- The last block `d` of `Fin (d+1)`, where the W pencil carries its coefficients. -/
def dIdx (d : ℕ) : Fin (d + 1) := ⟨d, by omega⟩

lemma dIdx_val (d : ℕ) : ((dIdx d : Fin (d + 1)) : ℕ) = d := rfl

lemma lastIdx_val (d : ℕ) : ((lastIdx d : Fin (d + 2)) : ℕ) = d + 1 := rfl

lemma castSucc_val_lt (a : Fin (d + 1)) : ((Fin.castSucc a : Fin (d + 2)) : ℕ) < d + 1 := by
  rw [Fin.val_castSucc]
  exact a.isLt

lemma castSucc_ne_last (a : Fin (d + 1)) : (Fin.castSucc a : Fin (d + 2)) ≠ lastIdx d := by
  intro h
  have := castSucc_val_lt a
  rw [h] at this
  exact absurd this (by simp [lastIdx])

lemma val_succ_eq_iff (a : Fin (d + 1)) : ((a : ℕ) + 1 = d + 1) ↔ a = dIdx d := by
  constructor
  · intro h
    rw [Fin.ext_iff]
    have hd : ((dIdx d : Fin (d + 1)) : ℕ) = d := rfl
    omega
  · intro h
    rw [h]
    rfl

/-- Splitting the `(d+2)`-block index into the first `d+1` blocks and the last one. -/
def eb (n d : ℕ) : (WIdx n d) ⊕ Fin n ≃ Fin (d + 2) × Fin n :=
  (Equiv.sumCongr (Equiv.refl (WIdx n d)) (Equiv.uniqueProd (Fin n) (Fin 1)).symm).trans
    ((Equiv.sumProdDistrib (Fin (d + 1)) (Fin 1) (Fin n)).symm.trans
      (Equiv.prodCongr (finSumFinEquiv.trans (finCongr (by omega)))
        (Equiv.refl (Fin n))))

@[simp] lemma eb_inl (n d : ℕ) (a : Fin (d + 1)) (y : Fin n) :
    eb n d (Sum.inl (a, y)) = (Fin.castSucc a, y) := by
  simp only [eb, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.prodCongr_apply,
    Equiv.uniqueProd_symm_apply, Equiv.sumProdDistrib_symm_apply_left,
    finSumFinEquiv_apply_left, finCongr_apply_mk]
  exact Prod.ext (Fin.ext rfl) rfl

@[simp] lemma eb_inr (n d : ℕ) (y : Fin n) : eb n d (Sum.inr y) = (lastIdx d, y) := by
  simp only [eb, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.prodCongr_apply,
    Equiv.uniqueProd_symm_apply, Equiv.sumProdDistrib_symm_apply_right,
    finSumFinEquiv_apply_right, finCongr_apply_mk, lastIdx]
  exact Prod.ext (Fin.ext rfl) rfl

lemma eb_symm_inl (n d : ℕ) (i : WIdx n d) :
    (eb n d).symm (eb n d (Sum.inl i)) = Sum.inl i := Equiv.symm_apply_apply _ _

lemma eb_symm_castSucc (n d : ℕ) (a : Fin (d + 1)) (y : Fin n) :
    (eb n d).symm (Fin.castSucc a, y) = Sum.inl (a, y) := by
  rw [← eb_inl (n := n) (d := d) a y, Equiv.symm_apply_apply]

lemma eb_symm_last (n d : ℕ) (y : Fin n) :
    (eb n d).symm (lastIdx d, y) = Sum.inr y := by
  rw [← eb_inr (n := n) (d := d) y, Equiv.symm_apply_apply]

/-! ### The block matrices -/

/-- The `n × n` identity in the last (`d`-th) block, viewed as a map `ι → Fin n`. -/
def Ecol (X : Type) [TopologicalSpace X] (n d : ℕ) :
    Matrix (WIdx n d) (Fin n) C(X, ℂ) :=
  fun i y => if i.1 = dIdx d ∧ i.2 = y then 1 else 0

/-- The transpose of `Ecol`: the `(Fin n) × ι` matrix with the identity in the last block. -/
def Erow (X : Type) [TopologicalSpace X] (n d : ℕ) :
    Matrix (Fin n) (WIdx n d) C(X, ℂ) :=
  fun x i => if i.1 = dIdx d ∧ x = i.2 then 1 else 0

/-- The superdiagonal part of `wPenB X n d b` (the `-1` blocks). -/
def BBl (X : Type) [TopologicalSpace X] (n d : ℕ) :
    Matrix (WIdx n d) (WIdx n d) C(X, ℂ) :=
  fun i j => if (i.1 : ℕ) + 1 = (j.1 : ℕ) then
    -(1 : Matrix (Fin n) (Fin n) C(X, ℂ)) i.2 j.2 else 0

/-- The last block row of `wPenB X n d b`, the row of coefficient matrices. -/
def rowb (X : Type) [TopologicalSpace X] (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (WIdx n d) C(X, ℂ) :=
  fun x j => Work.KT.Idx.wPenB X n d b (dIdx d, x) j

@[simp] lemma Ecol_apply (i : WIdx n d) (y : Fin n) :
    Ecol X n d i y = if i.1 = dIdx d ∧ i.2 = y then 1 else 0 := rfl

@[simp] lemma Erow_apply (x : Fin n) (i : WIdx n d) :
    Erow X n d x i = if i.1 = dIdx d ∧ x = i.2 then 1 else 0 := rfl

@[simp] lemma BBl_apply (i j : WIdx n d) :
    BBl X n d i j = (if (i.1 : ℕ) + 1 = (j.1 : ℕ) then
      -(1 : Matrix (Fin n) (Fin n) C(X, ℂ)) i.2 j.2 else 0) := rfl

@[simp] lemma rowb_apply (x : Fin n) (j : WIdx n d) :
    rowb X n d b x j = Work.KT.Idx.wPenB X n d b (dIdx d, x) j := rfl

/-- Entry form of `wPenA`. -/
lemma wPenA_apply {X : Type} [TopologicalSpace X] {D m : ℕ}
    (i j : Fin (D + 1) × Fin m) :
    Work.KT.Idx.wPenA X m D i j =
      if i.1 = j.1 ∧ (i.1 : ℕ) ≠ D then (1 : Matrix (Fin m) (Fin m) C(X, ℂ)) i.2 j.2
        else 0 := rfl

/-- Entry form of `wPenB`. -/
lemma wPenB_apply {X : Type} [TopologicalSpace X] {D m : ℕ}
    (bb : Fin (D + 1) → Matrix (Fin m) (Fin m) C(X, ℂ)) (i j : Fin (D + 1) × Fin m) :
    Work.KT.Idx.wPenB X m D bb i j =
      (if (i.1 : ℕ) + 1 = (j.1 : ℕ) then
        (if (i.1 : ℕ) = D then bb j.1 i.2 j.2
          else -(1 : Matrix (Fin m) (Fin m) C(X, ℂ)) i.2 j.2)
        else if (i.1 : ℕ) = D then bb j.1 i.2 j.2 else 0) := rfl

/-! ### The auxiliary matrices of the append step, on the `(d+1) ⊕ 1` index -/

/-- The `z`-coefficient of the `(d+2)`-block pencil in block form: the identity on the first
`d+1` blocks, zero on the last one. -/
def Ablk (X : Type) [TopologicalSpace X] (n d : ℕ) :
    Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ) :=
  Matrix.fromBlocks (1 : Matrix (WIdx n d) (WIdx n d) C(X, ℂ)) 0 0 0

/-- The constant part of the `(d+2)`-block pencil in block form. -/
def Bblk (X : Type) [TopologicalSpace X] (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ) :=
  Matrix.fromBlocks (BBl X n d) (-(Ecol X n d)) (rowb X n d b) 0

/-- The `z`-coefficient of the block diagonal pencil `diag(M_b, -1)`. -/
def Adiag (X : Type) [TopologicalSpace X] (n d : ℕ) :
    Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ) :=
  Matrix.fromBlocks (Work.KT.Idx.wPenA X n d) 0 0 0

/-- The constant part of the block diagonal pencil `diag(M_b, -1)`. -/
def Bdiag (X : Type) [TopologicalSpace X] (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ) :=
  Matrix.fromBlocks (Work.KT.Idx.wPenB X n d b) 0 0 (-1)

/-- The block swap of the last two block rows (`d` and `d+1`). -/
def Smat (X : Type) [TopologicalSpace X] (n d : ℕ) :
    Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ) :=
  Matrix.fromBlocks (Work.KT.Idx.wPenA X n d) (Ecol X n d) (Erow X n d) 0

/-- The shear `R` (`v_{d+1} ↦ v_{d+1} - z v_d`). -/
def Rmat (X : Type) [TopologicalSpace X] (n d : ℕ) :
    Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ) :=
  Matrix.fromBlocks 0 0 (Erow X n d) 0

/-- The "moment" `(2πi)⁻¹ ∮_{|z|=1} z • (zA+B)⁻¹ A dz` for the block diagonal pencil
`diag(M_b, -1)`; it is the `Z` of the identity `E_-(M_{(b,0)}) = E_-(diag(M_b,-1)) + R * Z`. -/
def Zmat (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ) :=
  letI : NormedRing (Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ)) :=
    Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ)) :=
    Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix (WIdx n d ⊕ Fin n) (WIdx n d ⊕ Fin n) C(X, ℂ)) :=
    Matrix.instCompleteSpace _ _ _
  (2 * Real.pi * Complex.I)⁻¹ •
    (∮ z in C(0, 1), z • Work.KT.Idx.pResA (Adiag X n d) (Bdiag X n d b) z)

end Block

end

end Work.Idx

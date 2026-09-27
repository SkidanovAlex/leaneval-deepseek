import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.FPatch

/-!
# Utilities for matrices over a fibre product

Matrices over `FiberProd ρ₁ ρ₂` are pairs of matrices over `A₁` and `A₂` whose reductions agree.
This file provides the assembly `fiberMatrix`, its component lemmas, and the block bookkeeping
along `finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)` (which is how `Matrix.fromBlocks` and
`Work.KT.Mat.sum` present block matrices).
-/

namespace Work.KT

open Matrix

noncomputable section

/-! ## Block bookkeeping along `finSumFinEquiv` -/

section Blocks

variable {S : Type} [Ring S] {m : ℕ}

/-- Every index of `Fin (m+m)` is in the first or the second block. -/
lemma finSumFinEquiv_cases (j : Fin (m + m)) :
    (∃ i : Fin m, j = finSumFinEquiv (Sum.inl i)) ∨
      (∃ i : Fin m, j = finSumFinEquiv (Sum.inr i)) := by
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  rcases s with i | i
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

/-- Every index of `Fin (m+n)` is in the first or the second block. -/
lemma finSumFinEquiv_cases' (m n : ℕ) (j : Fin (m + n)) :
    (∃ i : Fin m, j = finSumFinEquiv (Sum.inl i)) ∨
      (∃ i : Fin n, j = finSumFinEquiv (Sum.inr i)) := by
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  rcases s with i | i
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

/-- `mulVec` of a block-diagonal matrix, first block. -/
lemma blockMulVec_inl (A D : Matrix (Fin m) (Fin m) S) (w : Fin (m + m) → S) (i : Fin m) :
    ((Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 D)) *ᵥ w)
        (finSumFinEquiv (Sum.inl i)) =
      (A *ᵥ (fun j => w (finSumFinEquiv (Sum.inl j)))) i := by
  rw [Matrix.reindex_apply]
  rw [Matrix.submatrix_mulVec_equiv (Matrix.fromBlocks A 0 0 D) w
    (⇑(finSumFinEquiv.symm) : Fin (m + m) → Fin m ⊕ Fin m)
    (finSumFinEquiv.symm : Fin (m + m) ≃ Fin m ⊕ Fin m)]
  rw [Matrix.fromBlocks_mulVec]
  simp only [Equiv.symm_apply_apply, Equiv.symm_symm, Sum.elim_inl, Matrix.zero_mulVec, add_zero,
    Function.comp_apply]
  have hfun : ((w ∘ ⇑finSumFinEquiv) ∘ Sum.inl) =
      fun j : Fin m => w (finSumFinEquiv (Sum.inl j)) := rfl
  rw [hfun]

/-- `mulVec` of a block-diagonal matrix, second block. -/
lemma blockMulVec_inr (A D : Matrix (Fin m) (Fin m) S) (w : Fin (m + m) → S) (i : Fin m) :
    ((Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 D)) *ᵥ w)
        (finSumFinEquiv (Sum.inr i)) =
      (D *ᵥ (fun j => w (finSumFinEquiv (Sum.inr j)))) i := by
  rw [Matrix.reindex_apply]
  rw [Matrix.submatrix_mulVec_equiv (Matrix.fromBlocks A 0 0 D) w
    (⇑(finSumFinEquiv.symm) : Fin (m + m) → Fin m ⊕ Fin m)
    (finSumFinEquiv.symm : Fin (m + m) ≃ Fin m ⊕ Fin m)]
  rw [Matrix.fromBlocks_mulVec]
  simp only [Equiv.symm_apply_apply, Equiv.symm_symm, Sum.elim_inr, Matrix.zero_mulVec, zero_add,
    Function.comp_apply]
  have hfun : ((w ∘ ⇑finSumFinEquiv) ∘ Sum.inr) =
      fun j : Fin m => w (finSumFinEquiv (Sum.inr j)) := rfl
  rw [hfun]

/-- The standard projection `diag(1_m, 0_m)` on `S^{m+m}`. -/
def stdProj (S : Type) [Ring S] (m : ℕ) : Matrix (Fin (m + m)) (Fin (m + m)) S :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 0)

lemma stdProj_mulVec_inl (v : Fin (m + m) → S) (i : Fin m) :
    (stdProj S m *ᵥ v) (finSumFinEquiv (Sum.inl i)) = v (finSumFinEquiv (Sum.inl i)) := by
  rw [stdProj, blockMulVec_inl (1 : Matrix (Fin m) (Fin m) S) 0 v i, Matrix.one_mulVec]

lemma stdProj_mulVec_inr (v : Fin (m + m) → S) (i : Fin m) :
    (stdProj S m *ᵥ v) (finSumFinEquiv (Sum.inr i)) = 0 := by
  rw [stdProj, blockMulVec_inr (1 : Matrix (Fin m) (Fin m) S) 0 v i, Matrix.zero_mulVec]
  rfl

/-- A vector is fixed by the standard projection iff its second block vanishes. -/
lemma stdProj_mulVec_eq_self_iff (v : Fin (m + m) → S) :
    stdProj S m *ᵥ v = v ↔ ∀ i : Fin m, v (finSumFinEquiv (Sum.inr i)) = 0 := by
  constructor
  · intro h i
    have h2 := stdProj_mulVec_inr (S := S) v i
    rw [h] at h2
    exact h2
  · intro h
    funext j
    rcases finSumFinEquiv_cases j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [stdProj_mulVec_inl]
    · rw [stdProj_mulVec_inr, h]

end Blocks

/-! ## Matrices over a fibre product -/

section FiberMatrix

variable {A₁ A₂ A₀ : Type} [Ring A₁] [Ring A₂] [Ring A₀]
variable {ρ₁ : A₁ →+* A₀} {ρ₂ : A₂ →+* A₀}

/-- Assemble a matrix over the fibre product from a compatible pair of matrices over
`A₁` and `A₂`. -/
def fiberMatrix {N : ℕ} (X : Matrix (Fin N) (Fin N) A₁) (Y : Matrix (Fin N) (Fin N) A₂)
    (h : RingHom.mapMatrix ρ₁ X = RingHom.mapMatrix ρ₂ Y) :
    Matrix (Fin N) (Fin N) (FiberProd ρ₁ ρ₂) :=
  fun i j => ⟨(X i j, Y i j), by
    show ρ₁ (X i j) = ρ₂ (Y i j)
    have hh := congrFun (congrFun h i) j
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using hh⟩

theorem fiberMatrix_fst {N : ℕ} (X : Matrix (Fin N) (Fin N) A₁)
    (Y : Matrix (Fin N) (Fin N) A₂) (h : RingHom.mapMatrix ρ₁ X = RingHom.mapMatrix ρ₂ Y)
    (i j : Fin N) : (fiberMatrix X Y h i j).1.1 = X i j := rfl

theorem fiberMatrix_snd {N : ℕ} (X : Matrix (Fin N) (Fin N) A₁)
    (Y : Matrix (Fin N) (Fin N) A₂) (h : RingHom.mapMatrix ρ₁ X = RingHom.mapMatrix ρ₂ Y)
    (i j : Fin N) : (fiberMatrix X Y h i j).1.2 = Y i j := rfl

theorem mapMatrix_fstHom_fiberMatrix {N : ℕ} (X : Matrix (Fin N) (Fin N) A₁)
    (Y : Matrix (Fin N) (Fin N) A₂) (h : RingHom.mapMatrix ρ₁ X = RingHom.mapMatrix ρ₂ Y) :
    RingHom.mapMatrix (FiberProd.fstHom : FiberProd ρ₁ ρ₂ →+* A₁)
      (fiberMatrix X Y h) = X := by
  ext i j
  rfl

theorem mapMatrix_sndHom_fiberMatrix {N : ℕ} (X : Matrix (Fin N) (Fin N) A₁)
    (Y : Matrix (Fin N) (Fin N) A₂) (h : RingHom.mapMatrix ρ₁ X = RingHom.mapMatrix ρ₂ Y) :
    RingHom.mapMatrix (FiberProd.sndHom : FiberProd ρ₁ ρ₂ →+* A₂)
      (fiberMatrix X Y h) = Y := by
  ext i j
  rfl

/-- Two matrices over the fibre product agree if their `A₁`- and `A₂`-components do. -/
theorem fiberMatrix_ext {N : ℕ} {M M' : Matrix (Fin N) (Fin N) (FiberProd ρ₁ ρ₂)}
    (h : RingHom.mapMatrix (FiberProd.fstHom : FiberProd ρ₁ ρ₂ →+* A₁) M =
      RingHom.mapMatrix (FiberProd.fstHom : FiberProd ρ₁ ρ₂ →+* A₁) M')
    (h' : RingHom.mapMatrix (FiberProd.sndHom : FiberProd ρ₁ ρ₂ →+* A₂) M =
      RingHom.mapMatrix (FiberProd.sndHom : FiberProd ρ₁ ρ₂ →+* A₂) M') : M = M' := by
  have h1 : ∀ i j, (M i j).1.1 = (M' i j).1.1 := fun i j => congrFun (congrFun h i) j
  have h2 : ∀ i j, (M i j).1.2 = (M' i j).1.2 := fun i j => congrFun (congrFun h' i) j
  funext i j
  exact Subtype.ext (Prod.ext (h1 i j) (h2 i j))

theorem fiberMatrix_mul {N : ℕ} (X : Matrix (Fin N) (Fin N) A₁) (Y : Matrix (Fin N) (Fin N) A₂)
    (h : RingHom.mapMatrix ρ₁ X = RingHom.mapMatrix ρ₂ Y)
    (X' : Matrix (Fin N) (Fin N) A₁) (Y' : Matrix (Fin N) (Fin N) A₂)
    (h' : RingHom.mapMatrix ρ₁ X' = RingHom.mapMatrix ρ₂ Y') :
    fiberMatrix X Y h * fiberMatrix X' Y' h' =
      fiberMatrix (X * X') (Y * Y') (by rw [map_mul, map_mul, h, h']) := by
  apply fiberMatrix_ext
  · rw [map_mul, mapMatrix_fstHom_fiberMatrix, mapMatrix_fstHom_fiberMatrix,
      mapMatrix_fstHom_fiberMatrix]
  · rw [map_mul, mapMatrix_sndHom_fiberMatrix, mapMatrix_sndHom_fiberMatrix,
      mapMatrix_sndHom_fiberMatrix]

theorem fiberMatrix_one {N : ℕ}
    (h : RingHom.mapMatrix ρ₁ (1 : Matrix (Fin N) (Fin N) A₁) =
      RingHom.mapMatrix ρ₂ (1 : Matrix (Fin N) (Fin N) A₂)) :
    fiberMatrix (1 : Matrix (Fin N) (Fin N) A₁) (1 : Matrix (Fin N) (Fin N) A₂) h = 1 := by
  apply fiberMatrix_ext
  · rw [map_one, mapMatrix_fstHom_fiberMatrix]
  · rw [map_one, mapMatrix_sndHom_fiberMatrix]

/-- First component of a matrix–vector product over the fibre product. -/
theorem map_fstHom_mulVec {N : ℕ} (M : Matrix (Fin N) (Fin N) (FiberProd ρ₁ ρ₂))
    (v : Fin N → FiberProd ρ₁ ρ₂) :
    (fun i => (M *ᵥ v) i |>.1.1) =
      RingHom.mapMatrix (FiberProd.fstHom : FiberProd ρ₁ ρ₂ →+* A₁) M *ᵥ
        (fun i => (v i).1.1) := by
  funext i
  rw [RingHom.mapMatrix_apply]
  exact RingHom.map_mulVec (FiberProd.fstHom : FiberProd ρ₁ ρ₂ →+* A₁) M v i

/-- Second component of a matrix–vector product over the fibre product. -/
theorem map_sndHom_mulVec {N : ℕ} (M : Matrix (Fin N) (Fin N) (FiberProd ρ₁ ρ₂))
    (v : Fin N → FiberProd ρ₁ ρ₂) :
    (fun i => (M *ᵥ v) i |>.1.2) =
      RingHom.mapMatrix (FiberProd.sndHom : FiberProd ρ₁ ρ₂ →+* A₂) M *ᵥ
        (fun i => (v i).1.2) := by
  funext i
  rw [RingHom.mapMatrix_apply]
  exact RingHom.map_mulVec (FiberProd.sndHom : FiberProd ρ₁ ρ₂ →+* A₂) M v i

end FiberMatrix

end

end Work.KT

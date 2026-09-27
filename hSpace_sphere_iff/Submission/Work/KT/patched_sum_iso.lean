import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.FPatch

/-!
# Splitting a block-diagonal gluing (`Work.KT.patched_sum_iso`)

Let `R = FiberProd ρ₁ ρ₂` be the fibre product of two rings over a common quotient and let
`patched hcomm n γ` be the `R`-module of pairs `(f, g) ∈ A₁ⁿ × A₂ⁿ` with `ρ₁ f = γ · ρ₂ g`
(sections of the bundle obtained by clutching two trivial bundles along `γ`).

For a **block diagonal** gluing `γ ⊕ 1_k` the clutching splits: the first `m` coordinates keep the
gluing `γ`, while the last `k` coordinates are glued by the identity matrix, and an identity
gluing is the same as being a section over the whole glued space, i.e. an element of `R^k`:

`patched hcomm (m+k) (γ ⊕ 1_k) ≅ patched hcomm m γ × R^k`.

The only computation is the block structure of `Matrix.mulVec` for
`γ ⊕ 1_k = Matrix.fromBlocks γ 0 0 1` reindexed along `finSumFinEquiv`: on the first block the
matrix acts by `γ`, and on the second block it acts by the identity matrix.
-/

namespace Work.KT

open Matrix

noncomputable section

/-! ## The matrix `γ ⊕ 1_k` in unfurled form -/

section SumMat

variable {A₀ : Type} [Ring A₀]

/-- The matrix `(Mat.sum ⟨m, γ⟩ (Mat.one A₀ k)).2`, written as a reindexed block matrix. -/
abbrev sumMat {m k : ℕ} (γ : Matrix (Fin m) (Fin m) A₀) : Matrix (Fin (m + k)) (Fin (m + k)) A₀ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks γ 0 0 (1 : Matrix (Fin k) (Fin k) A₀))

/-- The unfurled form of `γ ⊕ 1_k` really is the block sum of `Mat.sum`. -/
lemma sumMat_eq {m k : ℕ} (γ : Matrix (Fin m) (Fin m) A₀) :
    (Mat.sum ⟨m, γ⟩ (Mat.one A₀ k)).2 = sumMat γ := rfl

/-- On the first block, `γ ⊕ 1_k` acts by `γ`. -/
lemma sumMat_mulVec_inl {m k : ℕ} (γ : Matrix (Fin m) (Fin m) A₀) (v : Fin (m + k) → A₀)
    (i : Fin m) :
    ((sumMat γ).mulVec v) (finSumFinEquiv (Sum.inl i))
      = (γ.mulVec fun j => v (finSumFinEquiv (Sum.inl j))) i := by
  dsimp only [sumMat]
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Matrix.mulVec_apply, dotProduct,
    Matrix.row_apply]
  rw [Fintype.sum_sum_type]
  simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]

/-- On the second block, `γ ⊕ 1_k` acts by the identity matrix. -/
lemma sumMat_mulVec_inr {m k : ℕ} (γ : Matrix (Fin m) (Fin m) A₀) (v : Fin (m + k) → A₀)
    (i : Fin k) :
    ((sumMat γ).mulVec v) (finSumFinEquiv (Sum.inr i)) = v (finSumFinEquiv (Sum.inr i)) := by
  dsimp only [sumMat]
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Matrix.mulVec_apply, dotProduct,
    Matrix.row_apply]
  rw [Fintype.sum_sum_type]
  simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add]
  simpa [Matrix.mulVec_apply, dotProduct] using
    congrFun (Matrix.one_mulVec (fun a => v (finSumFinEquiv (Sum.inr a)))) i

end SumMat

/-! ## The splitting isomorphism -/

section Split

variable {A₁ A₂ A₀ : Type} [Ring A₁] [Ring A₂] [Ring A₀]
  {ρ₁ : A₁ →+* A₀} {ρ₂ : A₂ →+* A₀}

/-- `patched (γ ⊕ 1_k) ≅ patched γ × R^k`, stated for the unfurled block matrix `sumMat γ`
(which is definitionally the second component of `Mat.sum ⟨m, γ⟩ (Mat.one A₀ k)`). -/
lemma patchedSumAux (hcomm : ∀ x y : A₀, x * y = y * x) {m k : ℕ}
    (γ : Matrix (Fin m) (Fin m) A₀) :
    Nonempty (FiberProd.patched (ρ₁ := ρ₁) (ρ₂ := ρ₂) hcomm (m + k) (sumMat γ)
      ≃ₗ[FiberProd ρ₁ ρ₂]
        (FiberProd.patched (ρ₁ := ρ₁) (ρ₂ := ρ₂) hcomm m γ ×
          (Fin k → FiberProd ρ₁ ρ₂))) := by
  classical
  refine ⟨{
    toFun := fun z =>
      (⟨(fun i => z.1.1 (finSumFinEquiv (Sum.inl i)),
         fun i => z.1.2 (finSumFinEquiv (Sum.inl i))),
        funext fun i => by
          have hz : (fun i => ρ₁ (z.1.1 i)) = (sumMat γ).mulVec (fun i => ρ₂ (z.1.2 i)) := z.2
          exact (congrFun hz (finSumFinEquiv (Sum.inl i))).trans
              (sumMat_mulVec_inl γ (fun j => ρ₂ (z.1.2 j)) i)⟩,
       fun i => ⟨(z.1.1 (finSumFinEquiv (Sum.inr i)), z.1.2 (finSumFinEquiv (Sum.inr i))),
         by
          have hz : (fun i => ρ₁ (z.1.1 i)) = (sumMat γ).mulVec (fun i => ρ₂ (z.1.2 i)) := z.2
          exact (congrFun hz (finSumFinEquiv (Sum.inr i))).trans
              (sumMat_mulVec_inr γ (fun j => ρ₂ (z.1.2 j)) i)⟩)
    invFun := fun w =>
      ⟨(fun j => Sum.elim (fun i => w.1.1.1 i) (fun i => (w.2 i).1.1) (finSumFinEquiv.symm j),
        fun j => Sum.elim (fun i => w.1.1.2 i) (fun i => (w.2 i).1.2) (finSumFinEquiv.symm j)),
       funext fun j => by
        obtain ⟨s, rfl⟩ : ∃ s, finSumFinEquiv s = j :=
          ⟨_, Equiv.apply_symm_apply finSumFinEquiv j⟩
        rcases s with i | i
        · have hkey := sumMat_mulVec_inl γ (fun j => ρ₂ (Sum.elim (fun i => w.1.1.2 i)
              (fun i => (w.2 i).1.2) (finSumFinEquiv.symm j))) i
          rw [hkey]
          simp only [Equiv.symm_apply_apply, Sum.elim_inl]
          exact congrFun w.1.2 i
        · have hkey := sumMat_mulVec_inr γ (fun j => ρ₂ (Sum.elim (fun i => w.1.1.2 i)
              (fun i => (w.2 i).1.2) (finSumFinEquiv.symm j))) i
          rw [hkey]
          simp only [Equiv.symm_apply_apply, Sum.elim_inr]
          exact (w.2 i).2⟩
    left_inv := fun z => by
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · funext j
        obtain ⟨s, rfl⟩ : ∃ s, finSumFinEquiv s = j :=
          ⟨_, Equiv.apply_symm_apply finSumFinEquiv j⟩
        rcases s with i | i <;> simp
      · funext j
        obtain ⟨s, rfl⟩ : ∃ s, finSumFinEquiv s = j :=
          ⟨_, Equiv.apply_symm_apply finSumFinEquiv j⟩
        rcases s with i | i <;> simp
    right_inv := fun w => by
      apply Prod.ext
      · apply Subtype.ext
        refine Prod.ext ?_ ?_
        · funext i; simp
        · funext i; simp
      · funext i
        apply Subtype.ext
        refine Prod.ext ?_ ?_
        · simp
        · simp
    map_add' := fun x y => by
      apply Prod.ext
      · apply Subtype.ext
        refine Prod.ext ?_ ?_
        · funext i; rfl
        · funext i; rfl
      · funext i
        apply Subtype.ext
        refine Prod.ext ?_ ?_ <;> rfl
    map_smul' := fun a x => by
      apply Prod.ext
      · apply Subtype.ext
        refine Prod.ext ?_ ?_
        · funext i; rfl
        · funext i; rfl
      · funext i
        apply Subtype.ext
        refine Prod.ext ?_ ?_ <;> rfl }⟩

/-- `patched (γ ⊕ 1_k) ≅ patched γ × R^k`: a block-diagonal gluing splits. -/
theorem patched_sum_iso {A₁ A₂ A₀ : Type} [Ring A₁] [Ring A₂] [Ring A₀]
    {ρ₁ : A₁ →+* A₀} {ρ₂ : A₂ →+* A₀} (hcomm : ∀ x y : A₀, x * y = y * x)
    {m k : ℕ} (γ : Matrix (Fin m) (Fin m) A₀) :
    Nonempty (FiberProd.patched (ρ₁ := ρ₁) (ρ₂ := ρ₂) hcomm (m + k)
        ((Mat.sum ⟨m, γ⟩ (Mat.one A₀ k)).2)
      ≃ₗ[FiberProd ρ₁ ρ₂]
        (FiberProd.patched (ρ₁ := ρ₁) (ρ₂ := ρ₂) hcomm m γ ×
          (Fin k → FiberProd ρ₁ ρ₂))) :=
  patchedSumAux hcomm γ

end Split

end

end Work.KT

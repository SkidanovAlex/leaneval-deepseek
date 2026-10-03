/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Additivity of `fpDim` on direct sums of finitely presented modules

For a Sylvester matrix rank function `rk` on a ring `R` and finitely presented `R`-modules
`M`, `N` one has

`fpDim rk (M × N) = fpDim rk M + fpDim rk N`.

This is the matrix-level statement of additivity of Li's dimension function on direct sums
([Li20, Definition 2.1 (2)] combined with Malcolmson's theorem `fpDim rk (coker A) = n - rk A`).

The proof is entirely matrix-theoretic: from presentations `M ≅ coker A` and `N ≅ coker B` one
obtains the presentation `M × N ≅ coker (A ⊕ B)` of the direct sum with the block diagonal
matrix `A ⊕ B = blockDiagFin A B`, and the Sylvester rank of a block diagonal matrix is the sum
of the ranks of its blocks (`SylvesterRank.rk_blockDiag`).

The only substantial input is that the cokernel of the block diagonal matrix is the product of
the cokernels, which we prove here by identifying the two submodules

* `range (rowMulLin (blockDiagFin A B))` inside `Fin (n + n') → R`, and
* `range (rowMulLin A) × range (rowMulLin B)` inside `(Fin n → R) × (Fin n' → R)`

under the "concatenation" linear equivalence `fpDimProd_eSum R n n'`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Epic.DimTheory
import Submission.Work.ORHughesFree.Epic.fpDim_eq_of_presentation
import Submission.Work.ORHughesFree.Epic.LiDim.RowSpaceToolkit

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

namespace Work.ORHughesFree.Epic.LiDim

open Matrix
open Work.ORHughesFree (blockDiagFin)
open Work.ORHughesFree.Epic

/-- The "concatenation" linear equivalence
`(Fin (m + n) → R) ≃ₗ (Fin m → R) × (Fin n → R)`: it reads a vector of length `m + n` as
the pair of its first `m` and last `n` entries. -/
noncomputable def fpDimProd_eSum (R : Type*) [Ring R] (m n : ℕ) :
    (Fin (m+n) → R) ≃ₗ[R] (Fin m → R) × (Fin n → R) :=
  (LinearEquiv.funCongrLeft R R finSumFinEquiv).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin n) R R)

@[simp] theorem fpDimProd_eSum_apply_fst (R : Type*) [Ring R] (m n : ℕ)
    (u : Fin (m+n) → R) (i : Fin m) :
    (fpDimProd_eSum R m n u).1 i = u (finSumFinEquiv (Sum.inl i)) := by
  simp [fpDimProd_eSum]

@[simp] theorem fpDimProd_eSum_apply_snd (R : Type*) [Ring R] (m n : ℕ)
    (u : Fin (m+n) → R) (j : Fin n) :
    (fpDimProd_eSum R m n u).2 j = u (finSumFinEquiv (Sum.inr j)) := by
  simp [fpDimProd_eSum]

@[simp] theorem fpDimProd_rowMulLin_apply {R : Type*} [Ring R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (v : Fin m → R) (j : Fin n) :
    rowMulLin A v j = ∑ i, v i * A i j := rfl

@[simp] theorem fpDimProd_blockDiagFin_apply_inl_inl {R : Type*} [Ring R] {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin p) (Fin q) R) (i : Fin n) (j : Fin m) :
    blockDiagFin A B (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = A i j := by
  simp [blockDiagFin]

@[simp] theorem fpDimProd_blockDiagFin_apply_inl_inr {R : Type*} [Ring R] {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin p) (Fin q) R) (i : Fin n) (j : Fin q) :
    blockDiagFin A B (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = 0 := by
  simp [blockDiagFin]

@[simp] theorem fpDimProd_blockDiagFin_apply_inr_inl {R : Type*} [Ring R] {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin p) (Fin q) R) (i : Fin p) (j : Fin m) :
    blockDiagFin A B (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := by
  simp [blockDiagFin]

@[simp] theorem fpDimProd_blockDiagFin_apply_inr_inr {R : Type*} [Ring R] {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin p) (Fin q) R) (i : Fin p) (j : Fin q) :
    blockDiagFin A B (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = B i j := by
  simp [blockDiagFin]

/-- The row map of a block diagonal matrix is conjugate, under the concatenation equivalence,
to the pair of the row maps of its blocks. -/
theorem fpDimProd_eSum_rowMulLin_blockDiag (R : Type*) [Ring R] {m n m' n' : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin m') (Fin n') R) (v : Fin (m+m') → R) :
    fpDimProd_eSum R n n' (rowMulLin (blockDiagFin A B) v)
      = (rowMulLin A (fpDimProd_eSum R m m' v).1, rowMulLin B (fpDimProd_eSum R m m' v).2) := by
  refine Prod.ext ?_ ?_
  · funext j
    simp only [fpDimProd_eSum_apply_fst, fpDimProd_rowMulLin_apply]
    rw [← Equiv.sum_comp finSumFinEquiv
      (fun i => v i * blockDiagFin A B i (finSumFinEquiv (Sum.inl j)))]
    rw [Fintype.sum_sum_type]
    simp only [fpDimProd_blockDiagFin_apply_inl_inl, fpDimProd_blockDiagFin_apply_inr_inl,
      mul_zero, Finset.sum_const_zero, add_zero]
  · funext j
    simp only [fpDimProd_eSum_apply_snd, fpDimProd_rowMulLin_apply]
    rw [← Equiv.sum_comp finSumFinEquiv
      (fun i => v i * blockDiagFin A B i (finSumFinEquiv (Sum.inr j)))]
    rw [Fintype.sum_sum_type]
    simp only [fpDimProd_blockDiagFin_apply_inl_inr, fpDimProd_blockDiagFin_apply_inr_inr,
      mul_zero, Finset.sum_const_zero, zero_add]

/-- Under the concatenation equivalence, the row space of the block diagonal matrix
`A ⊕ B` is the product of the row spaces of `A` and of `B`. -/
theorem fpDimProd_map_eSum_range_blockDiag (R : Type*) [Ring R] {m n m' n' : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin m') (Fin n') R) :
    Submodule.map (fpDimProd_eSum R n n' : (Fin (n+n') → R) →ₗ[R] (Fin n → R) × (Fin n' → R))
      (LinearMap.range (rowMulLin (blockDiagFin A B)))
    = (LinearMap.range (rowMulLin A)).prod (LinearMap.range (rowMulLin B)) := by
  ext y
  constructor
  · intro hy
    rw [Submodule.mem_map] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hv
    rw [Submodule.mem_prod]
    exact ⟨LinearMap.mem_range.mpr
        ⟨_, (congrArg Prod.fst (fpDimProd_eSum_rowMulLin_blockDiag R A B w)).symm⟩,
      LinearMap.mem_range.mpr
        ⟨_, (congrArg Prod.snd (fpDimProd_eSum_rowMulLin_blockDiag R A B w)).symm⟩⟩
  · intro hy
    rw [Submodule.mem_prod] at hy
    obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩ := hy
    rw [Submodule.mem_map]
    refine ⟨rowMulLin (blockDiagFin A B) ((fpDimProd_eSum R m m').symm (x₁, x₂)), ?_, ?_⟩
    · exact LinearMap.mem_range.mpr ⟨_, rfl⟩
    · change fpDimProd_eSum R n n'
        (rowMulLin (blockDiagFin A B) ((fpDimProd_eSum R m m').symm (x₁, x₂))) = y
      rw [fpDimProd_eSum_rowMulLin_blockDiag, (fpDimProd_eSum R m m').apply_symm_apply, hx₁, hx₂]

/-- The canonical map `(R^n × R^{n'}) ⧸ (range A × range B) → coker A × coker B`. -/
noncomputable def fpDimProd_prodMap (R : Type*) [Ring R] {m n m' n' : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin m') (Fin n') R) :
    ((Fin n → R) × (Fin n' → R)) →ₗ[R] cokerMat A × cokerMat B :=
  LinearMap.prod
    ((Submodule.mkQ (rowMulLin A).range).comp (LinearMap.fst R (Fin n → R) (Fin n' → R)))
    ((Submodule.mkQ (rowMulLin B).range).comp (LinearMap.snd R (Fin n → R) (Fin n' → R)))

theorem fpDimProd_prodMap_ker (R : Type*) [Ring R] {m n m' n' : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin m') (Fin n') R) :
    (fpDimProd_prodMap R A B).ker = (rowMulLin A).range.prod (rowMulLin B).range := by
  rw [fpDimProd_prodMap, LinearMap.ker_prod]
  simp only [LinearMap.ker_comp, Submodule.ker_mkQ]
  rw [LinearMap.prod_eq_inf_comap]

theorem fpDimProd_prodMap_surjective (R : Type*) [Ring R] {m n m' n' : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin m') (Fin n') R) :
    Function.Surjective (fpDimProd_prodMap R A B) := by
  intro y
  obtain ⟨y₁, hy₁⟩ := Submodule.mkQ_surjective (rowMulLin A).range y.1
  obtain ⟨y₂, hy₂⟩ := Submodule.mkQ_surjective (rowMulLin B).range y.2
  refine ⟨(y₁, y₂), ?_⟩
  show ((Submodule.mkQ (rowMulLin A).range) y₁, (Submodule.mkQ (rowMulLin B).range) y₂) = y
  rw [hy₁, hy₂]

/-- **The cokernel of a block diagonal matrix is the product of the cokernels.**
`R^{n+n'} / R^{m+m'}(A ⊕ B) ≅ (R^n / R^m A) × (R^{n'} / R^{m'} B)`. -/
noncomputable def fpDimProd_cokerBlockDiagEquiv (R : Type*) [Ring R] {m n m' n' : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin m') (Fin n') R) :
    cokerMat (blockDiagFin A B) ≃ₗ[R] cokerMat A × cokerMat B :=
  (Submodule.Quotient.equiv _ _ (fpDimProd_eSum R n n')
      (fpDimProd_map_eSum_range_blockDiag R A B)).trans
    ((Submodule.quotEquivOfEq (fpDimProd_prodMap R A B).ker _
        (fpDimProd_prodMap_ker R A B)).symm.trans
      ((fpDimProd_prodMap R A B).quotKerEquivOfSurjective
        (fpDimProd_prodMap_surjective R A B)))

/-- **Additivity of `fpDim` on direct sums of finitely presented modules.** -/
theorem fpDim_prod {R : Type u} [Ring R] (rk : Work.ORHughesFree.SylvesterRank R)
    (M N : Type u) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    [AddCommGroup N] [Module R N] [Module.FinitePresentation R N] :
    Work.ORHughesFree.Epic.fpDim rk (M × N)
      = Work.ORHughesFree.Epic.fpDim rk M + Work.ORHughesFree.Epic.fpDim rk N := by
  obtain ⟨nA, mA, fA, gA, hfA, hexA⟩ := Module.FinitePresentation.exists_fin' R M
  obtain ⟨nB, mB, fB, gB, hfB, hexB⟩ := Module.FinitePresentation.exists_fin' R N
  let AM : Matrix (Fin mA) (Fin nA) R := matOf gA
  let AN : Matrix (Fin mB) (Fin nB) R := matOf gB
  have hAM : Work.ORHughesFree.Epic.rowMulLin AM = gA := rowMulLin_matOf gA
  have hAN : Work.ORHughesFree.Epic.rowMulLin AN = gB := rowMulLin_matOf gB
  have hkerA : (Work.ORHughesFree.Epic.rowMulLin AM).range = LinearMap.ker fA := by
    rw [hAM]; exact (LinearMap.exact_iff.mp hexA).symm
  have hkerB : (Work.ORHughesFree.Epic.rowMulLin AN).range = LinearMap.ker fB := by
    rw [hAN]; exact (LinearMap.exact_iff.mp hexB).symm
  have eA : cokerMat AM ≃ₗ[R] M :=
    (Submodule.quotEquivOfEq _ _ hkerA).trans (fA.quotKerEquivOfSurjective hfA)
  have eB : cokerMat AN ≃ₗ[R] N :=
    (Submodule.quotEquivOfEq _ _ hkerB).trans (fB.quotKerEquivOfSurjective hfB)
  have hprod : cokerMat (blockDiagFin AM AN) ≃ₗ[R] M × N :=
    (fpDimProd_cokerBlockDiagEquiv R AM AN).trans (LinearEquiv.prodCongr eA eB)
  rw [Work.ORHughesFree.Epic.fpDim_eq_of_presentation rk (M × N) (blockDiagFin AM AN) hprod,
    Work.ORHughesFree.Epic.fpDim_eq_of_presentation rk M AM eA,
    Work.ORHughesFree.Epic.fpDim_eq_of_presentation rk N AN eB,
    rk.rk_blockDiag]
  push_cast
  ring

end Work.ORHughesFree.Epic.LiDim

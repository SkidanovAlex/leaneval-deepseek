/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The kernel of a block upper triangular operator meets `ker (retR)` in `ker (blockDiag A 1)`

For matrices `A : Mat_{n×m}(N(G))`, `C : Mat_{n×q}(N(G))`, `B : Mat_{p×q}(N(G))` over the
group von Neumann algebra `N(G) = Work.ORVonNeumann.groupVonNeumann G`, consider the block
upper triangular operator `T = matOp (blockUpper A C B) = matOp [[A, C], [0, B]]` acting on
`HSum (m + q) = HSum m ⊕ HSum q`, together with the retraction `retR m q` onto the second
summand.  A vector `w` lies in `ker T` exactly when `A w₁ + C w₂ = 0` and `B w₂ = 0`, where
`w₁ = retL m q w` and `w₂ = retR m q w`; imposing in addition `retR m q w = 0` (i.e. `w₂ = 0`)
leaves the condition `A w₁ = 0` with `w₂ = 0`, which is precisely membership in the kernel of
the block diagonal operator `matOp (blockDiag A 1)`:

`(matOp (blockUpper A C B)).ker ⊓ (retR m q).ker = (matOp (blockDiag A 1)).ker`.

The substance is the pair of coordinate computations `vBK_retL` and `vBK_retR` describing the
two block coordinates of `matOp (blockUpper A C B) w` (the same computation as in the block
diagonal case `vnBd_retL_matOp_blockDiag` / `vnBd_retR_matOp_blockDiag`, with the extra `C`
entry of the upper right corner), together with the fact that the operator attached to the
identity matrix is the identity (`vBK_matOp_one`).
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnCore
import Submission.Work.ORVonNeumann.Rep.vnBlockDiagDefs
import Submission.Work.ORVonNeumann.Rep.vnBlockDiagKernel

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace
open scoped InnerProduct

namespace Work.ORVonNeumann.Rep

universe u

section BlockUpperKerInf

variable {G : Type u} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-! ### The block entries of `blockUpper` -/

theorem vBK_apply_inl_inl {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (C : Matrix (Fin n) (Fin q) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (j : Fin n) (j' : Fin m) :
    (blockUpper A C B) (finSumFinEquiv (Sum.inl j)) (finSumFinEquiv (Sum.inl j')) = A j j' := by
  simp only [Work.ORVonNeumann.blockUpper, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

theorem vBK_apply_inl_inr {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (C : Matrix (Fin n) (Fin q) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (j : Fin n) (k' : Fin q) :
    (blockUpper A C B) (finSumFinEquiv (Sum.inl j)) (finSumFinEquiv (Sum.inr k')) = C j k' := by
  simp only [Work.ORVonNeumann.blockUpper, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂]

theorem vBK_apply_inr_inl {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (C : Matrix (Fin n) (Fin q) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (k : Fin p) (j' : Fin m) :
    (blockUpper A C B) (finSumFinEquiv (Sum.inr k)) (finSumFinEquiv (Sum.inl j')) = 0 := by
  simp only [Work.ORVonNeumann.blockUpper, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

theorem vBK_apply_inr_inr {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (C : Matrix (Fin n) (Fin q) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (k : Fin p) (k' : Fin q) :
    (blockUpper A C B) (finSumFinEquiv (Sum.inr k)) (finSumFinEquiv (Sum.inr k')) = B k k' := by
  simp only [Work.ORVonNeumann.blockUpper, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]

/-! ### The operator of the identity matrix -/

/-- `matOp` of the identity matrix is the identity operator. -/
theorem vBK_matOp_one (k : ℕ) :
    matOp (G := G) (1 : Matrix (Fin k) (Fin k) (↥(groupVonNeumann G))) = 1 := by
  refine matOp_ext (fun i => ?_)
  rw [hcoord_matOp]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, Subalgebra.coe_one]
    simp [ContinuousLinearMap.one_def]
  · intro j _ hj
    rw [Matrix.one_apply_ne (Ne.symm hj), Subalgebra.coe_zero,
      ContinuousLinearMap.zero_comp]
  · intro h; exact absurd (Finset.mem_univ i) h

/-! ### The two block coordinates of `matOp (blockUpper A C B) w` -/

/-- The second block coordinate of `matOp (blockUpper A C B) w` is `matOp B` applied to the
second block coordinate of `w`. -/
theorem vBK_retR {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (C : Matrix (Fin n) (Fin q) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (w : HSum (G := G) (m + q)) :
    retR (G := G) n p (matOp (G := G) (blockUpper A C B) w)
      = matOp (G := G) B (retR (G := G) m q w) := by
  apply hsum_ext
  intro k
  rw [vnBd_hcoord_retR, hcoord_matOp_apply, hcoord_matOp_apply]
  simp_rw [vnBd_hcoord_retR (G := G)]
  have hzero : (∑ j' : Fin m,
      ((blockUpper A C B) (finSumFinEquiv (Sum.inr k))
        (finSumFinEquiv (Sum.inl j')) : boundedEnd G)
          (hcoord (G := G) (m + q) (finSumFinEquiv (Sum.inl j')) w)) = 0 := by
    refine Finset.sum_eq_zero fun j' _ => ?_
    rw [vBK_apply_inr_inl]; simp
  have hright : (∑ k' : Fin q,
      ((blockUpper A C B) (finSumFinEquiv (Sum.inr k))
        (finSumFinEquiv (Sum.inr k')) : boundedEnd G)
          (hcoord (G := G) (m + q) (finSumFinEquiv (Sum.inr k')) w))
    = ∑ k' : Fin q, ((B k k' : ↥(groupVonNeumann G)) : boundedEnd G)
          (hcoord (G := G) (m + q) (finSumFinEquiv (Sum.inr k')) w) := by
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [vBK_apply_inr_inr]
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type, hzero, zero_add, hright]

/-- The first block coordinate of `matOp (blockUpper A C B) w` is `matOp A` applied to the
first block coordinate of `w` plus `matOp C` applied to the second block coordinate of `w`. -/
theorem vBK_retL {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (C : Matrix (Fin n) (Fin q) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (w : HSum (G := G) (m + q)) :
    retL (G := G) n p (matOp (G := G) (blockUpper A C B) w)
      = matOp (G := G) A (retL (G := G) m q w) + matOp (G := G) C (retR (G := G) m q w) := by
  apply hsum_ext
  intro j
  rw [vnBd_hcoord_retL, hcoord_matOp_apply, map_add, hcoord_matOp_apply, hcoord_matOp_apply]
  simp_rw [vnBd_hcoord_retL (G := G), vnBd_hcoord_retR (G := G)]
  have hleft : (∑ j' : Fin m,
      ((blockUpper A C B) (finSumFinEquiv (Sum.inl j))
        (finSumFinEquiv (Sum.inl j')) : boundedEnd G)
          (hcoord (G := G) (m + q) (finSumFinEquiv (Sum.inl j')) w))
      = ∑ j' : Fin m, ((A j j' : ↥(groupVonNeumann G)) : boundedEnd G)
          (hcoord (G := G) (m + q) (finSumFinEquiv (Sum.inl j')) w) := by
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [vBK_apply_inl_inl]
  have hcross : (∑ k' : Fin q,
      ((blockUpper A C B) (finSumFinEquiv (Sum.inl j))
        (finSumFinEquiv (Sum.inr k')) : boundedEnd G)
          (hcoord (G := G) (m + q) (finSumFinEquiv (Sum.inr k')) w))
      = ∑ k' : Fin q, ((C j k' : ↥(groupVonNeumann G)) : boundedEnd G)
          (hcoord (G := G) (m + q) (finSumFinEquiv (Sum.inr k')) w) := by
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [vBK_apply_inl_inr]
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type, hleft, hcross]

/-! ### Membership criteria for the two kernels -/

/-- A vector of `HSum (a + b)` is zero exactly when both of its block retractions are zero. -/
theorem vBK_eq_zero_iff (a b : ℕ) (x : HSum (G := G) (a + b)) :
    x = 0 ↔ retL (G := G) a b x = 0 ∧ retR (G := G) a b x = 0 := by
  constructor
  · intro h; rw [h]; simp
  · rintro ⟨h1, h2⟩
    have h := vnBd_incL_retL_add_incR_retR (G := G) a b x
    rw [h1, h2] at h
    rw [← h, map_zero, map_zero, add_zero]

/-- Membership in the kernel of `matOp (blockUpper A C B)`, in terms of the two block
coordinates. -/
theorem vBK_mem_ker_blockUpper {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (C : Matrix (Fin n) (Fin q) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G)))
    (w : HSum (G := G) (m + q)) :
    w ∈ (matOp (G := G) (blockUpper A C B)).ker ↔
      retL (G := G) n p (matOp (G := G) (blockUpper A C B) w) = 0 ∧
        retR (G := G) n p (matOp (G := G) (blockUpper A C B) w) = 0 := by
  rw [LinearMap.mem_ker]
  exact vBK_eq_zero_iff n p (matOp (G := G) (blockUpper A C B) w)

/-- The kernel of `matOp (1 : Matrix (Fin k) (Fin k) N(G))` is trivial. -/
theorem vBK_mem_ker_matOp_one (k : ℕ) (x : HSum (G := G) k) :
    x ∈ (matOp (G := G) (1 : Matrix (Fin k) (Fin k) (↥(groupVonNeumann G)))).ker ↔ x = 0 := by
  rw [LinearMap.mem_ker, vBK_matOp_one]
  simp

/-! ### The main result -/

/-- The kernel of the block upper triangular operator `matOp [[A, C], [0, B]]` meets the kernel
of the second block retraction `retR m q` in the kernel of the block diagonal operator
`matOp (blockDiag A 1)`. -/
theorem vBK_target {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (C : Matrix (Fin n) (Fin q) (↥(groupVonNeumann G)))
    (B : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) :
    (matOp (G := G) (blockUpper A C B)).ker ⊓ (retR (G := G) m q).ker
      = (matOp (G := G) (blockDiag A
          (1 : Matrix (Fin q) (Fin q) (↥(groupVonNeumann G))))).ker := by
  ext w
  rw [Submodule.mem_inf, vnBd_mem_ker_blockDiag (G := G) A
    (1 : Matrix (Fin q) (Fin q) (↥(groupVonNeumann G))) w]
  constructor
  · rintro ⟨hwT, hwR⟩
    have hwR' : retR (G := G) m q w = 0 := hwR
    rw [vBK_mem_ker_blockUpper] at hwT
    obtain ⟨h1, _h2⟩ := hwT
    have hA : matOp (G := G) A (retL (G := G) m q w) = 0 := by
      have h := h1
      rw [vBK_retL, hwR', map_zero, add_zero] at h
      exact h
    exact ⟨LinearMap.mem_ker.mpr hA, (vBK_mem_ker_matOp_one (G := G) q _).mpr hwR'⟩
  · rintro ⟨h1, h2⟩
    rw [vBK_mem_ker_matOp_one] at h2
    have h1' : matOp (G := G) A (retL (G := G) m q w) = 0 := LinearMap.mem_ker.mp h1
    refine ⟨?_, ?_⟩
    · rw [vBK_mem_ker_blockUpper]
      constructor
      · rw [vBK_retL, h1', h2, map_zero, add_zero]
      · rw [vBK_retR, h2, map_zero]
    · rw [LinearMap.mem_ker]
      exact h2

end BlockUpperKerInf

theorem vnBlockUpperKerInf {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (↥(Work.ORVonNeumann.groupVonNeumann G))) (C : Matrix (Fin n) (Fin q) (↥(Work.ORVonNeumann.groupVonNeumann G))) (B : Matrix (Fin p) (Fin q) (↥(Work.ORVonNeumann.groupVonNeumann G))) : (Work.ORVonNeumann.Rep.matOp (G := G) (Work.ORVonNeumann.blockUpper A C B)).ker ⊓ (Work.ORVonNeumann.Rep.retR (G := G) m q).ker = (Work.ORVonNeumann.Rep.matOp (G := G) (Work.ORVonNeumann.blockDiag A (1 : Matrix (Fin q) (Fin q) (↥(Work.ORVonNeumann.groupVonNeumann G))))).ker := by
  exact vBK_target A C B

end Work.ORVonNeumann.Rep

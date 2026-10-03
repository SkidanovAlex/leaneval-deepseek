/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The extended rank function `rk_G` of the group von Neumann algebra

For a countable group `G` we define the extended rank function of
`N(G) = Work.ORVonNeumann.groupVonNeumann G` by

`rk_G(A) = n - dim_G (ker A†)`   for `A ∈ M_{n×m}(N(G))`,

and prove that it is a faithful Sylvester rank function (Jaikin-Zapirain–López-Álvarez,
arXiv:1810.12135, §3.2–3.4; Lück, *L²-Invariants*, Theorem 6.7).

The five axioms are verified as follows.

* `map_zero`, `map_one`: `matOp 0 = 0` and `matOp !![1] = 1`.
* `mul_le`: with `vnKeyRank` (the equality `n - dim ker T† = m - dim ker T` for an `n × m`
  matrix operator `T`), both inequalities become kernel inclusions, using
  `matOp (A*B) = matOp A ∘ matOp B` and `(matOp (A*B))† = (matOp B)† ∘ (matOp A)†`.
* `blockDiag_add`: `vnBlockDiagKernel`, transported across `vnKeyRank`.
* `blockUpper_le`: `vnBlockUpperAdjointKernel`, transported across `vnKeyRank`.

Faithfulness is `vnFaithful`: `hdim (ker (matOp !![x])†) = 1` forces `x = 0`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.SylvesterRank
import Submission.Work.ORVonNeumann.Rep.vnCore
import Submission.Work.ORVonNeumann.Rep.vnAssembly
import Submission.Work.ORVonNeumann.Rep.vnMatOpMul
import Submission.Work.ORVonNeumann.Rep.vnMatOpAdjoint
import Submission.Work.ORVonNeumann.Rep.vnHdimCompl
import Submission.Work.ORVonNeumann.Rep.vnHdimMono
import Submission.Work.ORVonNeumann.Rep.vnBlockDiagKernel
import Submission.Work.ORVonNeumann.Rep.vnFaithful
import Submission.Work.ORVonNeumann.Rep.vnKeyRank
import Submission.Work.ORVonNeumann.Rep.vnBlockUpperAdjointKernel

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace InnerProduct

namespace Work.ORVonNeumann.Rep

universe u

variable {G : Type u} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The rank of a matrix, computed as `m - dim_G (ker T)` instead of `n - dim_G (ker T†)`
(`vnKeyRank`). -/
theorem vnRank_eq_kernel {n m : ℕ} (X : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G))) :
    vnRank (G := G) n m X = (m : ℝ) - hdim (G := G) (matOp (G := G) X).ker := by
  rw [vnRank_eq]
  exact (vnKeyRank (G := G) X).symm

/-- `rk_G` of the zero matrix vanishes. -/
theorem vnRank_zero (n m : ℕ) :
    vnRank (G := G) n m (0 : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G))) = 0 := by
  have hadj : ContinuousLinearMap.adjoint
      (matOp (G := G) (0 : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))) = 0 := by
    rw [matOp_zero', eq_comm, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    simp
  have hproj : ((ContinuousLinearMap.adjoint (matOp (G := G)
      (0 : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G))))).ker).starProjection = 1 := by
    apply ContinuousLinearMap.ext
    intro u
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (K := (ContinuousLinearMap.adjoint (matOp (G := G)
        (0 : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G))))).ker) ?_ ?_
    · rw [hadj]
      simp
    · intro w _
      simp [one_apply_eq_self]
  have hval : vnRank (G := G) n m (0 : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
      = (n : ℝ) - hdim (G := G) ((ContinuousLinearMap.adjoint (matOp (G := G)
          (0 : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G))))).ker) :=
    vnRank_eq (G := G) n m (0 : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
  rw [hval, hdim_apply, hproj]
  simp [vnNormSqHdelta]

/-- `rk_G` of the `1 × 1` identity matrix is one. -/
theorem vnRank_one :
    vnRank (G := G) 1 1 (1 : Matrix (Fin 1) (Fin 1) (↥(groupVonNeumann G))) = 1 := by
  have hadj : ContinuousLinearMap.adjoint
      (matOp (G := G) (1 : Matrix (Fin 1) (Fin 1) (↥(groupVonNeumann G)))) = 1 := by
    rw [matOp_one_one, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    simp
  have hproj : ((ContinuousLinearMap.adjoint (matOp (G := G)
      (1 : Matrix (Fin 1) (Fin 1) (↥(groupVonNeumann G))))).ker).starProjection = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (K := (ContinuousLinearMap.adjoint (matOp (G := G)
        (1 : Matrix (Fin 1) (Fin 1) (↥(groupVonNeumann G))))).ker) ?_ ?_
    · rw [hadj]
      simp
    intro w hw
    have hw1 : ContinuousLinearMap.adjoint (matOp (G := G)
        (1 : Matrix (Fin 1) (Fin 1) (↥(groupVonNeumann G)))) w = 0 := hw
    rw [hadj] at hw1
    have hw0 : w = 0 := by simpa [one_apply_eq_self] using hw1
    rw [hw0]
    simp
  have hval : vnRank (G := G) 1 1 (1 : Matrix (Fin 1) (Fin 1) (↥(groupVonNeumann G)))
      = (1 : ℝ) - hdim (G := G) ((ContinuousLinearMap.adjoint (matOp (G := G)
          (1 : Matrix (Fin 1) (Fin 1) (↥(groupVonNeumann G))))).ker) := by
    simpa using vnRank_eq (G := G) 1 1 (1 : Matrix (Fin 1) (Fin 1) (↥(groupVonNeumann G)))
  rw [hval, hdim_apply, hproj]
  simp

/-- **The extended rank function `rk_G`** of the group von Neumann algebra `N(G)`: the
Sylvester matrix rank function `A ↦ n - dim_G (ker A†)` on matrices over `N(G)`
(Jaikin-Zapirain–López-Álvarez §3.4). -/
noncomputable def vnRankFunction : SylvesterRankFunction (↥(groupVonNeumann G)) where
  toFun n m A := vnRank (G := G) n m A
  map_zero n m := vnRank_zero (G := G) n m
  map_one := vnRank_one (G := G)
  mul_le A B := by
    have hA : (ContinuousLinearMap.adjoint (matOp (G := G) A)).ker
        ≤ (ContinuousLinearMap.adjoint (matOp (G := G) (A * B))).ker := by
      intro x hx
      have hx' : ContinuousLinearMap.adjoint (matOp (G := G) A) x = 0 := hx
      have hcomp : ContinuousLinearMap.adjoint (matOp (G := G) (A * B))
          = (ContinuousLinearMap.adjoint (matOp (G := G) B)).comp
              (ContinuousLinearMap.adjoint (matOp (G := G) A)) := by
        rw [vnMatOpMul, ContinuousLinearMap.adjoint_comp]
      show ContinuousLinearMap.adjoint (matOp (G := G) (A * B)) x = 0
      rw [hcomp, ContinuousLinearMap.comp_apply, hx', map_zero]
    have hB : (matOp (G := G) B).ker ≤ (matOp (G := G) (A * B)).ker := by
      intro x hx
      have hx' : matOp (G := G) B x = 0 := hx
      show matOp (G := G) (A * B) x = 0
      rw [vnMatOpMul, ContinuousLinearMap.comp_apply, hx', map_zero]
    have h1 : hdim (G := G) ((ContinuousLinearMap.adjoint (matOp (G := G) A)).ker)
        ≤ hdim (G := G) ((ContinuousLinearMap.adjoint (matOp (G := G) (A * B))).ker) :=
      vnHdimMono (G := G) hA
    have h2 : hdim (G := G) ((matOp (G := G) B).ker)
        ≤ hdim (G := G) ((matOp (G := G) (A * B)).ker) :=
      vnHdimMono (G := G) hB
    rw [le_min_iff]
    constructor
    · simp only [vnRank_eq]
      exact sub_le_sub_left h1 _
    · simp only [vnRank_eq_kernel]
      exact sub_le_sub_left h2 _
  blockDiag_add A B := by
    simp only [vnRank_eq_kernel]
    rw [vnBlockDiagKernel (G := G) A B]
    push_cast
    ring
  blockUpper_le A C B := by
    have hA := vnKeyRank (G := G) A
    have hB := vnKeyRank (G := G) B
    have hT := vnKeyRank (G := G) (blockUpper A C B)
    have hk := vnBlockUpperAdjointKernel (G := G) A C B
    simp only [vnRank_eq_kernel]
    push_cast at hA hB hT ⊢
    linarith

/-- **Faithfulness of `rk_G`**: a `1 × 1` matrix of rank zero over `N(G)` is zero. -/
theorem vnRankFunction_faithful : (vnRankFunction (G := G)).Faithful := by
  intro x hx
  rw [SylvesterRankFunction.rank_eq] at hx
  simp only [vnRankFunction, vnRank_eq] at hx
  have hd : hdim (G := G) ((ContinuousLinearMap.adjoint (matOp (G := G)
      (!![x] : Matrix (Fin 1) (Fin 1) (↥(groupVonNeumann G))))).ker) = 1 := by
    norm_num at hx
    linarith
  exact vnFaithful (G := G) x hd

end Work.ORVonNeumann.Rep

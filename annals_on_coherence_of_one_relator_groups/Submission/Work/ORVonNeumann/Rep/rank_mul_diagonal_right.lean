/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The rank of `N(G)` is invariant under right multiplication by a diagonal of
non-zero-divisors

For a countable group `G` and the extended rank function `rk_G` of the group von Neumann
algebra `N(G) = Work.ORVonNeumann.groupVonNeumann G`, right multiplication of the `j`-th
*column* of a matrix by a non-zero-divisor `y j` does not change the rank:

`rk_G (C * diag y) = rk_G C`.

The proof uses the two halves of the fact that `A ↦ matOp A` is a `*`-representation of the
matrix ring over `N(G)` on `⊕_j ℓ²(G)`:

* `matOp` is multiplicative (`vnMatOpMul`), so
  `matOp (C * diag y) = (matOp C).comp (matOp (diag y))`;
* the adjoint of `matOp A` is `matOp Aᴴ` (`vnMatOpAdjoint`), i.e. `⋆` on `N(G)` is the
  Hilbert-space adjoint (`coe_star_eq_adjoint`).

Taking adjoints, `(matOp (C * diag y))† = matOp (diag (⋆ ∘ y)) ∘ (matOp C)†`, and the operator
`matOp (diag (⋆ ∘ y))` is *injective*: it acts coordinatewise by the entries `(y j)⋆`, each of
which is again a non-zero-divisor (`Ore.star_mem_nonZeroDivisors`), hence an injective operator
(`Work.Rep.Ore.injective_of_mem_nonZeroDivisors`).  Therefore the two adjoints have the same
kernel, and since `rk_G A = n - dim_G (ker A†)` the ranks agree.

## Main result

* `Work.ORVonNeumann.Rep.rank_mul_diagonal_right`
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnRankFunction
import Submission.Work.ORVonNeumann.Rep.vnKeyRank
import Submission.Work.ORVonNeumann.Rep.vnMatOpAdjoint
import Submission.Work.Rep.Ore.injective_of_mem_nonZeroDivisors
import Submission.Work.ORVonNeumann.Ore.star_mem_nonZeroDivisors

set_option synthInstance.maxHeartbeats 200000

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace InnerProduct

namespace Work.ORVonNeumann.Rep

universe u

variable {G : Type u} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The `i`-th coordinate of `matOp (diagonal z)` in terms of the `i`-th coordinate of the
argument: the diagonal matrix operator acts coordinatewise by its entries. -/
theorem matOp_diagonal_apply {m : ℕ} (z : Fin m → ↥(groupVonNeumann G))
    (w : HSum (G := G) m) (i : Fin m) :
    (matOp (G := G) (Matrix.diagonal z) w).ofLp i
      = ((z i : ↥(groupVonNeumann G)) : boundedEnd G) (w.ofLp i) := by
  rw [matOp_apply]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
    simp
  · intro h; exact absurd (Finset.mem_univ i) h

/-- If every entry of a diagonal matrix `diag z` over `N(G)` acts as an injective operator,
then so does `matOp (diag z)`: its `i`-th coordinate is the entry `z i` applied to the `i`-th
coordinate of the argument (`matOp_diagonal_apply`). -/
theorem matOp_diagonal_injective {m : ℕ} (z : Fin m → ↥(groupVonNeumann G))
    (hz : ∀ j, Function.Injective ((z j : ↥(groupVonNeumann G)) : boundedEnd G)) :
    Function.Injective (matOp (G := G) (Matrix.diagonal z)) := by
  intro x x' hxx
  apply hsum_ext
  intro i
  rw [hcoord_apply, hcoord_apply]
  exact hz i (by
    have h := congrArg (fun v : HSum (G := G) m => v.ofLp i) hxx
    rw [matOp_diagonal_apply, matOp_diagonal_apply] at h
    exact h)

/-- An injective continuous linear operator can be cancelled on the left of a composite:
`ker (g ∘ f) = ker f`. -/
theorem ker_comp_eq_ker_of_injective {E F H : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup H] [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
    [InnerProductSpace ℂ H] (g : F →L[ℂ] H) (f : E →L[ℂ] F) (hg : Function.Injective g) :
    (g.comp f).ker = f.ker := by
  ext u
  show u ∈ (g.comp f).toLinearMap.ker ↔ u ∈ f.toLinearMap.ker
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro h; exact hg (by simpa using h)
  · intro h; simpa using congrArg g h

/-- **The rank of `N(G)` is invariant under right multiplication by a diagonal whose entries are
non-zero-divisors**: `rk_G (C * diag y) = rk_G C`.

Writing `rk_G A = n - dim_G (ker A†)`, both sides have the same adjoint kernel: taking adjoints
of `matOp (C * diag y) = (matOp C).comp (matOp (diag y))` gives
`(matOp (C * diag y))† = matOp (diag (⋆ ∘ y)) ∘ (matOp C)†`, and `matOp (diag (⋆ ∘ y))` is
injective because the entries `(y j)⋆` are non-zero-divisors, hence injective operators. -/
theorem rank_mul_diagonal_right {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n m : ℕ} (y : Fin m → ↥(Work.ORVonNeumann.groupVonNeumann G)) (hy : ∀ j, y j ∈ nonZeroDivisors ↥(Work.ORVonNeumann.groupVonNeumann G)) (C : Matrix (Fin n) (Fin m) (↥(Work.ORVonNeumann.groupVonNeumann G))) : (Work.ORVonNeumann.Rep.vnRankFunction (G := G)).rank (fun i j => C i j * y j) = (Work.ORVonNeumann.Rep.vnRankFunction (G := G)).rank C := by
  have hmat : (fun i j => C i j * y j) = C * Matrix.diagonal y := by
    ext i j
    rw [Matrix.mul_diagonal]
  rw [hmat]
  rw [SylvesterRankFunction.rank_eq, SylvesterRankFunction.rank_eq]
  simp only [vnRankFunction, vnRank_eq]
  -- the two adjoint kernels agree, the second factor of the adjoint of `matOp (C * diag y)`
  -- being the injective operator `matOp (diag (⋆ ∘ y))`
  have hinj : Function.Injective
      (ContinuousLinearMap.adjoint (matOp (G := G) (Matrix.diagonal y))) := by
    rw [vnMatOpAdjoint, Matrix.diagonal_conjTranspose (α := ↥(groupVonNeumann G)) y]
    exact matOp_diagonal_injective _
      (fun j => Work.Rep.Ore.injective_of_mem_nonZeroDivisors (star (y j))
        (Work.ORVonNeumann.Ore.star_mem_nonZeroDivisors (hy j)))
  have hker : (ContinuousLinearMap.adjoint (matOp (G := G) (C * Matrix.diagonal y))).ker
      = (ContinuousLinearMap.adjoint (matOp (G := G) C)).ker := by
    rw [vnMatOpMul, ContinuousLinearMap.adjoint_comp]
    exact ker_comp_eq_ker_of_injective _ _ hinj
  rw [hdim_congr hker]

end Work.ORVonNeumann.Rep

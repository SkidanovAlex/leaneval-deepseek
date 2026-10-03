/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The rank of `N(G)` is invariant under left multiplication by a diagonal of
non-zero-divisors

For a countable group `G` and the extended rank function `rk_G` of the group von Neumann
algebra `N(G) = Work.ORVonNeumann.groupVonNeumann G` (`Work.ORVonNeumann.Rep.vnRankFunction`),
multiplying the `i`-th *row* of a matrix by a non-zero-divisor `x i` does not change the rank:

`rk_G (fun i j => x i * C i j) = rk_G C`, i.e. `rk_G (diag x * C) = rk_G C`.

The proof is the operator form of the classical fact that multiplying a matrix by an
invertible diagonal does not change the rank.  Writing `D = Matrix.diagonal x`:

* `matOp (D * C) = (matOp D).comp (matOp C)` (`vnMatOpMul`), and
* `matOp D` acts coordinatewise by the entries `x i`: `(matOp D w).ofLp i = x i (w.ofLp i)`
  (`matOp_diagonal_coord`).

Each `x i` is a non-zero-divisor of `N(G)`, hence acts by an *injective* operator on `ℓ²(G)`
(`Work.Rep.Ore.injective_of_mem_nonZeroDivisors`, via the orthogonal projection onto the kernel,
which lies in `N(G)`).  Therefore `matOp D` is injective and `ker (matOp (D * C)) = ker (matOp C)`.
Since `rk_G A = m - dim_G (ker (matOp A))` for an `n × m` matrix `A` (`vnRank_eq_kernel`, which
is the key identity `m - dim ker T = n - dim ker T†`), the two ranks agree.

## Main result

* `Work.ORVonNeumann.Rep.rank_mul_diagonal_left`
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnRankFunction
import Submission.Work.ORVonNeumann.Rep.vnMatOpMul
import Submission.Work.ORVonNeumann.Rep.vnAssembly
import Submission.Work.Rep.Ore.injective_of_mem_nonZeroDivisors

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace InnerProduct

namespace Work.ORVonNeumann.Rep

/-- The `i`-th coordinate of `matOp (Matrix.diagonal x)` in terms of the `i`-th coordinate of
the argument: a diagonal matrix over `N(G)` acts coordinatewise by its entries.

(Kept private so that it cannot clash with the closely related `matOp_diagonal_apply` of the
companion file `rank_mul_diagonal_right`.) -/
private theorem matOp_diagonal_coord {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ}
    (x : Fin n → ↥(Work.ORVonNeumann.groupVonNeumann G)) (w : HSum (G := G) n) (i : Fin n) :
    hcoord (G := G) n i (matOp (G := G) (Matrix.diagonal x) w)
      = ((x i : ↥(Work.ORVonNeumann.groupVonNeumann G)) : Work.ORVonNeumann.boundedEnd G)
          (hcoord (G := G) n i w) := by
  rw [hcoord_matOp_apply]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne x (Ne.symm hj)]
    simp
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `matOp (Matrix.diagonal x)` is an injective operator whenever every entry `x i` is a
non-zero-divisor of `N(G)`: up to the identification `⊕_{i : Fin n} ℓ²(G) ≅ n · ℓ²(G)` it is the
direct sum of the injective operators `x i`. -/
private theorem matOp_diagonal_injective {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ}
    (x : Fin n → ↥(Work.ORVonNeumann.groupVonNeumann G))
    (hx : ∀ i, x i ∈ nonZeroDivisors ↥(Work.ORVonNeumann.groupVonNeumann G)) :
    Function.Injective (matOp (G := G) (Matrix.diagonal x)) := by
  intro w w' hww
  apply hsum_ext
  intro i
  have h := congrArg (fun v => hcoord (G := G) n i v) hww
  rw [matOp_diagonal_coord, matOp_diagonal_coord] at h
  exact Work.Rep.Ore.injective_of_mem_nonZeroDivisors (G := G) (x i) (hx i) h

/-- **The rank of `N(G)` is invariant under left multiplication by a diagonal whose entries are
non-zero-divisors**: `rk_G (fun i j => x i * C i j) = rk_G C`.

Indeed `(fun i j => x i * C i j) = diag x * C`, so `matOp` of the left hand side is
`(matOp (diag x)).comp (matOp C)`; `matOp (diag x)` is injective because its entries are
non-zero-divisors, so the two operators have the same kernel, and `rk_G A = m - dim_G (ker A)`. -/
theorem rank_mul_diagonal_left {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n m : ℕ} (x : Fin n → ↥(Work.ORVonNeumann.groupVonNeumann G)) (hx : ∀ i, x i ∈ nonZeroDivisors ↥(Work.ORVonNeumann.groupVonNeumann G)) (C : Matrix (Fin n) (Fin m) (↥(Work.ORVonNeumann.groupVonNeumann G))) : (Work.ORVonNeumann.Rep.vnRankFunction (G := G)).rank (fun i j => x i * C i j) = (Work.ORVonNeumann.Rep.vnRankFunction (G := G)).rank C := by
  have hmat : (fun i j => x i * C i j) = Matrix.diagonal x * C := by
    ext i j
    rw [Matrix.diagonal_mul]
  rw [hmat]
  -- `matOp (diag x)` is injective, so it can be cancelled on the left of the composite
  have hinj : Function.Injective (matOp (G := G) (Matrix.diagonal x)) :=
    matOp_diagonal_injective (G := G) x hx
  have hker : (matOp (G := G) (Matrix.diagonal x * C)).ker = (matOp (G := G) C).ker := by
    rw [vnMatOpMul]
    have h := LinearMap.ker_comp_of_ker_eq_bot ((matOp (G := G) C).toLinearMap)
      (g := (matOp (G := G) (Matrix.diagonal x)).toLinearMap)
      (LinearMap.ker_eq_bot.mpr hinj)
    rw [show ((matOp (G := G) (Matrix.diagonal x)).comp (matOp (G := G) C)).ker
        = LinearMap.ker ((matOp (G := G) (Matrix.diagonal x)).toLinearMap.comp
            (matOp (G := G) C).toLinearMap) from rfl] at *
    rw [h]
  -- both ranks are `m - dim_G (ker (matOp ·))`
  rw [SylvesterRankFunction.rank_eq, SylvesterRankFunction.rank_eq]
  change vnRank (G := G) n m (Matrix.diagonal x * C) = vnRank (G := G) n m C
  rw [vnRank_eq_kernel, vnRank_eq_kernel, hdim_congr hker]

end Work.ORVonNeumann.Rep

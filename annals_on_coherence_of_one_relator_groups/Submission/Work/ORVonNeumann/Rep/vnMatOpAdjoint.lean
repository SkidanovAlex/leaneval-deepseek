/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The adjoint of the matrix operator `matOp`

`Work.ORVonNeumann.Rep.matOp A` (`Submission.Work.ORVonNeumann.Rep.vnCore`) is the bounded
operator `⊕_{j : Fin m} ℓ²(G) → ⊕_{i : Fin n} ℓ²(G)` attached to a matrix
`A : Mat_{n × m}(N(G))`, given on the `i`-th coordinate by `(matOp A x)_i = ∑_j A_{ij} x_j`.

This file computes its Hilbert-space adjoint.  The point is that the involution of the group
von Neumann algebra *is* the Hilbert-space adjoint of operators (`N(G)` is a `*`-subalgebra
of `B(ℓ²(G))` with the `C`-algebra involution), so the adjoint of `matOp A` is the matrix
operator of the conjugate transpose:

* `Work.ORVonNeumann.Rep.coe_star_eq_adjoint` — for `a : N(G)`,
  `(a⋆ : B(ℓ²(G))) = (a : B(ℓ²(G)))†`;
* `Work.ORVonNeumann.Rep.inner_matOp_left`, `…inner_matOp_right` — the matrix coefficients
  of `matOp A`, i.e. `matOp A` tested against the inner product of `HSum`;
* **`Work.ORVonNeumann.Rep.vnMatOpAdjoint`** — `(matOp A)† = matOp A*`.

Together with `Work.ORVonNeumann.Rep.vnMatOpMul` (the multiplicative half) this says that
`A ↦ matOp A` is a `*`-representation of the matrix ring `Matₙ(N(G))` on `⊕^n ℓ²(G)`, which
is what makes the von Neumann dimension of the kernel/range of `matOp A` a genuine rank
function on matrices over `N(G)` (Jaikin-Zapirain–López-Álvarez, arXiv:1810.12135, §3.2).

## Main results

* `Work.ORVonNeumann.Rep.coe_star_eq_adjoint`;
* `Work.ORVonNeumann.Rep.inner_matOp_left`, `Work.ORVonNeumann.Rep.inner_matOp_right`;
* `Work.ORVonNeumann.Rep.vnMatOpAdjoint`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnCore

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace
open scoped InnerProduct

namespace Work.ORVonNeumann.Rep

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The involution of the group von Neumann algebra is the Hilbert-space adjoint: for
`a ∈ N(G) ⊆ B(ℓ²(G))` the operator `a⋆` is the adjoint of `a`. -/
theorem coe_star_eq_adjoint (a : ↥(groupVonNeumann G)) :
    (((star a : ↥(groupVonNeumann G))) : boundedEnd G) = (a : boundedEnd G)† := by
  rw [StarMemClass.coe_star, ContinuousLinearMap.star_eq_adjoint]

/-- The `i`-th coordinates of `matOp A x` evaluated against the `i`-th coordinates of `y`:
the inner product `⟪matOp A x, y⟫` is the sum of the matrix coefficients
`⟪A i j (x j), y i⟫` over all `i : Fin n`, `j : Fin m`. -/
theorem inner_matOp_left {n m : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (x : HSum (G := G) m) (y : HSum (G := G) n) :
    inner ℂ (matOp (G := G) A x) y
      = ∑ i : Fin n, ∑ j : Fin m,
          inner ℂ ((((A i j : ↥(groupVonNeumann G))) : boundedEnd G) (x.ofLp j)) (y.ofLp i) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [matOp_apply, sum_inner]

/-- The mirror image of `inner_matOp_left`: `⟪x, matOp A y⟫` is the sum of the matrix
coefficients `⟪x i, A i j (y j)⟫`. -/
theorem inner_matOp_right {n m : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (x : HSum (G := G) n) (y : HSum (G := G) m) :
    inner ℂ x (matOp (G := G) A y)
      = ∑ i : Fin n, ∑ j : Fin m,
          inner ℂ (x.ofLp i) ((((A i j : ↥(groupVonNeumann G))) : boundedEnd G) (y.ofLp j)) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [matOp_apply, inner_sum]

theorem vnMatOpAdjoint {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n m : ℕ} (A : Matrix (Fin n) (Fin m) (↥(Work.ORVonNeumann.groupVonNeumann G))) : ContinuousLinearMap.adjoint (Work.ORVonNeumann.Rep.matOp (G := G) A) = Work.ORVonNeumann.Rep.matOp (G := G) (Matrix.conjTranspose A) := by
  -- `matOp A*` is the adjoint of `matOp A`; it suffices to check the defining identity of
  -- the adjoint on inner products.
  rw [eq_comm]
  refine (ContinuousLinearMap.eq_adjoint_iff (matOp (G := G) (Matrix.conjTranspose A))
    (matOp (G := G) A)).mpr ?_
  intro x y
  -- compute both sides as a double sum of the same matrix coefficients and interchange the
  -- order of summation; the entries match because `(A*) i j = (A j i)⋆` and `⋆` is `†`.
  rw [inner_matOp_left (G := G) (Matrix.conjTranspose A) x y,
      inner_matOp_right (G := G) A x y]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_apply]
  rw [← ContinuousLinearMap.adjoint_inner_right
    (A := (((star (A i j) : ↥(groupVonNeumann G))) : boundedEnd G))
    (x := x.ofLp i) (y := y.ofLp j)]
  rw [coe_star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint]

end Work.ORVonNeumann.Rep

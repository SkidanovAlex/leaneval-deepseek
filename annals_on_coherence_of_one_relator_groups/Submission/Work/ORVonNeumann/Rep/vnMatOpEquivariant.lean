/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# Equivariance of the matrix operators `matOp`

`Work.ORVonNeumann.Rep.matOp A` is the operator on `⊕_{j : Fin m} ℓ²(G)` attached to a matrix
`A : Mat_{n × m}(N(G))` (`Submission.Work.ORVonNeumann.Rep.vnCore`).  It acts on the `i`-th
coordinate by `(matOp A x)_i = ∑_j A_{ij} (x_j)`, i.e. it is built out of the matrix entries
`A_{ij} ∈ N(G)`.

Since `N(G)` is by definition the commutant of the right regular representation `ρ`, every
entry `A_{ij}` commutes with `ρ g`; the block diagonal amplification `diagOp` of `ρ`
(`Submission.Work.ORVonNeumann.Rep.vnDiag`) is exactly the right regular representation on
`⊕^n ℓ²(G)`, and it follows that `matOp A` is *equivariant*: it commutes with the block
diagonal action.

This is statement D1 of the von Neumann dimension machinery (`vnStmtsRKV`): it is what makes
`matOp A` an operator "over the ring `N(G)`", and it is the hypothesis under which the cyclic
trace `vnCyclicTrace` applies to a pair of matrix operators.

## Main results

* `Work.ORVonNeumann.Rep.coe_comp_rightRegOp` — an element of `N(G)` commutes with `ρ g`
  (in composition form);
* `Work.ORVonNeumann.Rep.vnMatOpEquivariant` — `matOp A` is equivariant.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnDiag
import Submission.Work.ORVonNeumann.Rep.vnMatOpMul

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace InnerProduct

namespace Work.ORVonNeumann.Rep

universe u

variable {G : Type u} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- **The defining commutation of `N(G)`**, in composition form: an element `a` of the group
von Neumann algebra `N(G) = ρ(G)'` commutes with the right regular representation. -/
theorem coe_comp_rightRegOp (a : ↥(groupVonNeumann G)) (g : G) :
    (a : boundedEnd G) ∘SL rightRegOp g = rightRegOp g ∘SL (a : boundedEnd G) := by
  have h : (a : boundedEnd G) * rightRegOp g = rightRegOp g * (a : boundedEnd G) :=
    (Work.ORVonNeumann.mem_groupVonNeumann_iff (a : boundedEnd G)).mp a.2 g
  exact h

/-- Pointwise form of `coe_comp_rightRegOp`. -/
theorem coe_comp_rightRegOp_apply (a : ↥(groupVonNeumann G)) (g : G) (y : l2 G) :
    (a : boundedEnd G) (rightRegOp g y) = rightRegOp g ((a : boundedEnd G) y) :=
  congrArg (fun T : boundedEnd G => T y) (coe_comp_rightRegOp a g)

/-- **`matOp` is equivariant**: the operator of a matrix over `N(G)` commutes with the block
diagonal right regular action.  This is statement D1 of `vnStmtsRKV`. -/
theorem vnMatOpEquivariant {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n m : ℕ} (X : Matrix (Fin n) (Fin m) (↥(Work.ORVonNeumann.groupVonNeumann G))) : Work.ORVonNeumann.Rep.Equivariant (G := G) (Work.ORVonNeumann.Rep.matOp (G := G) X) := by
  intro g
  apply ContinuousLinearMap.ext
  intro x
  apply hsum_ext
  intro i
  -- Compare the `i`-th coordinates of `matOp X (diagOp m g x)` and of `diagOp n g (matOp X x)`:
  -- both are `∑ j, A_{ij} (ρ g (x_j))`, because `diagOp` acts coordinatewise by `ρ g` and the
  -- matrix entries `A_{ij} ∈ N(G)` commute with `ρ g`.
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    hcoord_diagOp_apply, hcoord_matOp_apply, hcoord_matOp_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcoord_diagOp_apply]
  exact congrArg (fun T : boundedEnd G => T (hcoord m j x)) (coe_comp_rightRegOp (X i j) g)

end Work.ORVonNeumann.Rep

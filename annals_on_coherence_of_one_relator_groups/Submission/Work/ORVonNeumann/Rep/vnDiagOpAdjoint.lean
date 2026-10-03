/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The adjoint of the block diagonal right regular action

`Work.ORVonNeumann.Rep.diagOp n g = ⊕_{i : Fin n} ρ g` is the block diagonal operator on
`HSum n = ⊕_{i : Fin n} ℓ²(G)` induced by the right regular representation `ρ`.  Since `ρ` is
a unitary representation (`(ρ g)† = ρ g⁻¹`), so is its `n`-fold amplification:

* `Work.ORVonNeumann.Rep.vnDiagOpAdjoint` — `(diagOp n g)† = diagOp n g⁻¹`.

The proof is coordinatewise: `diagOp n g` acts on the `i`-th summand by `ρ g`, and
`(ρ g)† = ρ g⁻¹` is the adjoint identity for `ρ`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnDiag

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace InnerProduct

namespace Work.ORVonNeumann.Rep

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- Coordinatewise description of `diagOp`: the `i`-th coordinate of `diagOp n g x` is the
`i`-th coordinate of `x` acted on by `ρ g`. -/
theorem diagOp_ofLp (n : ℕ) (g : G) (i : Fin n) (x : HSum (G := G) n) :
    (diagOp (G := G) n g x).ofLp i = rightRegOp g (x.ofLp i) := by
  rw [← hcoord_apply, ← hcoord_apply]
  exact hcoord_diagOp_apply n g i x

/-- **The adjoint of the block diagonal right regular action.**  Since `diagOp n g` acts by the
unitary `ρ g` on each summand, its Hilbert-space adjoint is `diagOp n g⁻¹`. -/
theorem vnDiagOpAdjoint {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (g : G) : ContinuousLinearMap.adjoint (Work.ORVonNeumann.Rep.diagOp (G := G) n g) = Work.ORVonNeumann.Rep.diagOp (G := G) n g⁻¹ := by
  -- It suffices to verify the defining identity of the adjoint on inner products.
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff (diagOp (G := G) n g⁻¹) (diagOp (G := G) n g)).mpr ?_
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diagOp_ofLp (G := G) n g⁻¹ i x, diagOp_ofLp (G := G) n g i y]
  -- `(ρ g)† = ρ g⁻¹`, so the two coordinate inner products agree.
  rw [← ContinuousLinearMap.adjoint_inner_right
      (A := rightRegOp (G := G) g⁻¹) (x := x.ofLp i) (y := y.ofLp i),
    ← ContinuousLinearMap.star_eq_adjoint, rightRegOp_star, inv_inv]

end Work.ORVonNeumann.Rep

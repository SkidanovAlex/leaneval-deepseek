/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GLUE area (fundmath3-gorenstein_walter)
-/
import Submission.Work.GLUE.Bridge

set_option autoImplicit false

open scoped MatrixGroups
open Subgroup

/-!
# GLUE: `p`-stability — our `IsPStable'` is the library's `IsPStableOp`

`Work.GW2.IsPStable' p X` is the contract's form of group-theoretic `p`-stability: for every
normal `p`-subgroup `K ≤ X` and every `p`-subgroup `A ≤ X` with `[[K,A],A] = 1`, the image of
`A` in `X/C_X(K)` lies in `O_p(X/C_X(K))`.  The odd-order library's `Subgroup.IsPStableOp`
is *the same proposition*, with `opCore` in place of `pCore`; by the bridge
`pCore_eq_opCore` the two are equivalent.

The area `PSTAB` supplies `PStableProp`, i.e. `IsPStable' p X` for every finite `X` with
dihedral or cyclic Sylow 2-subgroups and every odd prime `p`.  The corollaries below turn
that into the hypothesis consumed by Glauberman's `Z(J)`-theorem (see `ZjA.lean`).
-/

namespace Work.GW2

/-- The contract's `p`-stability is the library's `p`-stability. -/
theorem isPStable'_iff_isPStableOp (p : ℕ) [Fact p.Prime] (X : Type*) [Group X] [Finite X] :
    IsPStable' p X ↔ Subgroup.IsPStableOp p X := by
  simp only [IsPStable', Subgroup.IsPStableOp, pCore_eq_opCore]

theorem isPStableOp_of_isPStable' (p : ℕ) [Fact p.Prime] (X : Type*) [Group X] [Finite X]
    (h : IsPStable' p X) : Subgroup.IsPStableOp p X :=
  (isPStable'_iff_isPStableOp p X).mp h

theorem isPStable'_of_isPStableOp (p : ℕ) [Fact p.Prime] (X : Type*) [Group X] [Finite X]
    (h : Subgroup.IsPStableOp p X) : IsPStable' p X :=
  (isPStable'_iff_isPStableOp p X).mpr h

/-- `PStableProp` (the `PSTAB` area's deliverable) gives `IsPStable'` at any finite group
of the class. -/
theorem isPStable'_of_pStableProp (hPS : PStableProp) (X : Type) [Group X] [Finite X]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (h : DihOrCycSylow X) : IsPStable' p X :=
  hPS X p Fact.out hp2 h

/-- `PStableProp` in the library's shape `Subgroup.IsPStableOp`, which is what Glauberman's
`Z(J)`-theorem is stated with. -/
theorem isPStableOp_of_pStableProp (hPS : PStableProp) (X : Type) [Group X] [Finite X]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (h : DihOrCycSylow X) :
    Subgroup.IsPStableOp p X :=
  isPStableOp_of_isPStable' p X (isPStable'_of_pStableProp hPS X p hp2 h)

end Work.GW2

/-
Copyright (c) 2025. All rights reserved.

# The connecting map `δ : H¹(G, C) → H²(G, A)`

This file assembles the connecting map of a short exact sequence of `G`-modules
`0 → A --iota--> B --pi--> C → 0` from the cocycle-level construction of
`Submission/Work/GroupCohomology/Connecting.lean`:

* `ShortExactSeq.deltaCocycle_zero`, `ShortExactSeq.deltaZ` : `Z¹(G,C) →+ H²(G,A)`;
* `ShortExactSeq.deltaH1` : the connecting map `H¹(G,C) →+ H²(G,A)`, characterised by
  `deltaH1_H1π`.
-/
import Submission.Work.GroupCohomology.Connecting
import Submission.Work.GroupCohomology.deltaCocycle_eq_class
import Submission.Work.GroupCohomology.deltaCocycle_add
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w x

namespace Work.GroupCohomology

variable {G : Type u} {A : Type v} {B : Type w} {C : Type x} [Group G]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]

namespace ShortExactSeq

variable (S : ShortExactSeq G A B C)

/-- The connecting map kills the zero cocycle; equivalently, a `1`-cocycle of `C` whose class is
zero has connecting image zero. -/
theorem deltaCocycle_zero : H2π G A (S.deltaCocycle 0) = 0 := by
  have h : H2π G A (S.deltaCocycle 0) =
      H2π G A (S.deltaCocycle 0) + H2π G A (S.deltaCocycle 0) := by
    simpa using deltaCocycle_add S (0 : Z1 G C) 0
  have h2 : H2π G A (S.deltaCocycle 0) + 0 =
      H2π G A (S.deltaCocycle 0) + H2π G A (S.deltaCocycle 0) := by
    rw [add_zero]
    exact h
  exact (add_left_cancel h2).symm

/-- The connecting map on cocycles, as an additive homomorphism `Z¹(G,C) →+ H²(G,A)`. -/
noncomputable def deltaZ : Z1 G C →+ H2 G A where
  toFun c := H2π G A (S.deltaCocycle c)
  map_zero' := S.deltaCocycle_zero
  map_add' c c' := deltaCocycle_add S c c'

/-- **The connecting map** `δ¹ : H¹(G, C) →+ H²(G, A)` of a short exact sequence of `G`-modules. -/
noncomputable def deltaH1 : H1 G C →+ H2 G A :=
  QuotientAddGroup.lift ((B1 G C).comap (Z1 G C).subtype) (S.deltaZ) (by
    intro z hz
    have hz' : ((z : Z1 G C) : G → C) ∈ B1 G C := by
      simpa using (AddSubgroup.mem_comap.mp hz)
    have hker : H1π G C z = 0 := by
      rw [H1π, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
      exact hz'
    have h0 : H1π G C (0 : Z1 G C) = 0 := map_zero _
    have h := deltaCocycle_eq_class S z 0 (by rw [hker, h0])
    show H2π G A (S.deltaCocycle z) = 0
    rw [h, S.deltaCocycle_zero])

theorem deltaH1_H1π (c : Z1 G C) :
    S.deltaH1 (H1π G C c) = H2π G A (S.deltaCocycle c) :=
  QuotientAddGroup.lift_mk' _ _ c

end ShortExactSeq

end Work.GroupCohomology

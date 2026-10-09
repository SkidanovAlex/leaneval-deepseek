/-
Copyright (c) 2025. All rights reserved.

# The connecting map `δ⁰ : H⁰(G, C) →+ H¹(G, A)`

This assembles the degree `0 → 1` connecting map of a short exact sequence of `G`-modules from the
cocycle-level construction in `Submission/Work/GroupCohomology/Delta0.lean`.

The exactness statements
`range_mapH0_eq_ker_delta0H` and `range_delta0H_eq_ker_mapH1` (modules of the same names) close
the long exact sequence at the left end.
-/
import Submission.Work.GroupCohomology.Delta0
import Submission.Work.GroupCohomology.delta0Elem_add
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

/-- **The connecting map** `δ⁰ : H⁰(G, C) →+ H¹(G, A)` of a short exact sequence of `G`-modules. -/
noncomputable def delta0H : H0 G C →+ H1 G A where
  toFun c := H1π G A (S.delta0Elem c)
  map_zero' := S.delta0Elem_zero
  map_add' c c' := delta0Elem_add S c c'

@[simp] theorem delta0H_apply (c : H0 G C) :
    S.delta0H c = H1π G A (S.delta0Elem c) := rfl

end ShortExactSeq

end Work.GroupCohomology

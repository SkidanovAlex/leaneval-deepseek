/-
Copyright (c) 2025. All rights reserved.

# Restriction lands in the invariants of the quotient action

For a normal subgroup `N ◁ G` and a `G`-module `A`, restriction
`resH1 G N : H¹(G, A) → H¹(N, A)` has image contained in the invariants of the conjugation action
of `G ⧸ N` on `H¹(N, A)` (`Work.GroupCohomology.invariants (G ⧸ N) (H1 N A)`), by
`Work.GroupCohomology.conjH1_resH1` and the fact that the action of `G` on `H¹(N,A)` factors
through `G ⧸ N`.

Together with `range_infH1_eq_ker_resH1` and `ker_infH1_eq_bot` this identifies the first three
terms of the five-term sequence: the third term is exactly these invariants.
-/
import Submission.Work.GroupCohomology.conjH1_resH1
import Submission.Work.GroupCohomology.ConjugationAction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.GroupCohomology

variable {G : Type u} {A : Type v} [Group G] [AddCommGroup A] [DistribMulAction G A]
variable (N : Subgroup G) [N.Normal]

/-- **Restriction lands in the invariants of the quotient action.** -/
theorem mem_invariants_resH1 (y : H1 G A) :
    resH1 (A := A) G N y ∈ invariants (G ⧸ N) (H1 N A) := by
  rw [mem_invariants]
  intro q
  induction q using QuotientGroup.induction_on with
  | _ g =>
    show (QuotientGroup.mk' N g) • resH1 (A := A) G N y = resH1 (A := A) G N y
    rw [quotientConjSMul_mk']
    exact conjH1_resH1 N g y

end Work.GroupCohomology

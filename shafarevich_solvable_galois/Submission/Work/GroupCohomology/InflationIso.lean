/-
Copyright (c) 2025. All rights reserved.

# The inflation isomorphism in the vanishing case

If `N ◁ G` is a normal subgroup and `H¹(N, A) = 0` for the `G`-module `A`, then the inflation map
`infH1 N : H¹(G ⧸ N, A^N) → H¹(G, A)` is an isomorphism
(`Work.GroupCohomology.infH1_bijective_of_subsingleton`), with inverse `Classical.choose` of the
surjectivity statement.  This packaged form, together with the computation rules for the
equivalence and its inverse, is what a caller uses.

## Main results

* `Work.GroupCohomology.infH1AddEquiv`
* `Work.GroupCohomology.infH1AddEquiv_apply`, `Work.GroupCohomology.infH1AddEquiv_symm_apply`
* `Work.GroupCohomology.infH1_addEquiv_of_subsingleton`
-/
import Submission.Work.GroupCohomology.infH1_bijective_of_subsingleton
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.GroupCohomology

variable {G : Type u} {A : Type v} [Group G] [AddCommGroup A] [DistribMulAction G A]
variable (N : Subgroup G) [N.Normal]

/-- **The inflation isomorphism** `H¹(G ⧸ N, A^N) ≃+ H¹(G, A)`, when `H¹(N, A) = 0`. -/
noncomputable def infH1AddEquiv [Subsingleton (H1 N A)] :
    H1 (G ⧸ N) (invariants N A) ≃+ H1 G A :=
  AddEquiv.ofBijective (infH1 (A := A) N) (infH1_bijective_of_subsingleton N)

@[simp] theorem infH1AddEquiv_apply [Subsingleton (H1 N A)]
    (x : H1 (G ⧸ N) (invariants N A)) :
    infH1AddEquiv N x = infH1 (A := A) N x := rfl

@[simp] theorem infH1AddEquiv_symm_apply [Subsingleton (H1 N A)]
    (x : H1 (G ⧸ N) (invariants N A)) :
    (infH1AddEquiv N).symm (infH1 (A := A) N x) = x :=
  AddEquiv.symm_apply_apply _ x

/-- **Inflation is an isomorphism when the restriction term vanishes**, in the packaged form. -/
theorem infH1_addEquiv_of_subsingleton [Subsingleton (H1 N A)] :
    Nonempty (H1 (G ⧸ N) (invariants N A) ≃+ H1 G A) :=
  ⟨infH1AddEquiv N⟩

end Work.GroupCohomology

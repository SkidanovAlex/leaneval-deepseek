import Mathlib
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- The quotient map `H2π : Z²(G, A) → H²(G, A)` is surjective, so to prove a property of an
arbitrary class in `H²` it suffices to prove it on cocycle representatives. -/
theorem H2_induction_on {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] {C : Work.GroupCohomology.H2 G A → Prop} (x : Work.GroupCohomology.H2 G A)
    (h : ∀ c : Work.GroupCohomology.Z2 G A, C (Work.GroupCohomology.H2π G A c)) : C x := by
  obtain ⟨c, hc⟩ :=
    QuotientAddGroup.mk'_surjective ((B2 G A).comap (Z2 G A).subtype) x
  rw [← hc]
  exact h c

end Work.GroupCohomology

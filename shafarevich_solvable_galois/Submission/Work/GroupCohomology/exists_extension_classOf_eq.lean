import Mathlib
import Submission.Work.GroupCohomology.BaerSum
import Submission.Work.GroupCohomology.H2_induction_on
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- Every class in `H²(Q, A)` is realised by an extension of `Q` by `A` with the prescribed action: together with `Work.GroupCohomology.nonempty_equiv_iff_classOf_eq` (two such extensions are isomorphic iff their classes agree) this is the classification of extensions by `H²(Q, A)`. -/
theorem exists_extension_classOf_eq {Q : Type*} {A : Type*} [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] (ξ : Work.GroupCohomology.H2 Q A) :
    ∃ X : Work.GroupCohomology.Extension Q A, Work.GroupCohomology.classOf X = ξ :=
  H2_induction_on (G := Q) (A := A)
    (C := fun x => ∃ X : Extension Q A, classOf X = x) ξ
    (fun c => ⟨Extension.ofCocycle Q A c, classOf_ofCocycle c⟩)

end Work.GroupCohomology

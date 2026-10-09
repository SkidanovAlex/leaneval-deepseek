import Mathlib
import Submission.Work.GroupCohomology.BaerSum
import Submission.Work.GroupCohomology.Classification
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

set_option linter.style.haveILetI false

/-- An extension of `Q` by `A` with the prescribed action splits (admits a homomorphic section `Q → E`) if and only if its class in `H²(Q, A)` vanishes. -/
theorem nonempty_splitting_iff_classOf_eq_zero {Q : Type*} {A : Type*} [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] (X : Work.GroupCohomology.Extension Q A) :
    Nonempty (Work.GroupCohomology.Extension.Splitting X) ↔
      Work.GroupCohomology.classOf X = 0 := by
  -- `X` is equivalent to the explicit extension `Y` attached to its representing cocycle,
  -- and splitting is invariant under equivalence of extensions
  -- (`nonempty_splitting_of_equiv`), so it suffices to treat `Y`.
  let Y := Extension.ofCocycle Q A (cocycleOf X)
  letI : Group X.E := X.groupE
  letI : Group Y.E := Y.groupE
  constructor
  · intro h
    -- a splitting of `X` transports along `X ≅ Y` to a splitting of `Y`
    obtain ⟨e⟩ := cocycleOf_equiv X
    have hY : Nonempty (Extension.Splitting Y) :=
      nonempty_splitting_of_equiv e.symm h
    -- and a splitting of the extension of a cocycle forces that cocycle to be a coboundary
    exact class_zero_of_splits_ofCocycle (cocycleOf X) hY
  · intro h
    -- conversely a vanishing class means the representing cocycle is a coboundary,
    -- and the extension it defines splits, which transports back to `X`
    obtain ⟨e⟩ := cocycleOf_equiv X
    have hY : Nonempty (Extension.Splitting Y) :=
      ofCocycle_splits_of_class_zero (cocycleOf X) h
    exact nonempty_splitting_of_equiv e hY

end Work.GroupCohomology

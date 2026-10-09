import Mathlib
import Submission.Work.GroupCohomology.BaerSum
import Submission.Work.GroupCohomology.Classification
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- Two extensions of `Q` by `A` with the prescribed conjugation action are isomorphic (as extensions of `Q` by `A`) if and only if their classes in `H²(Q, A)` coincide. -/
theorem nonempty_equiv_iff_classOf_eq {Q : Type*} {A : Type*} [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] (X Y : Work.GroupCohomology.Extension Q A) :
    Nonempty (Work.GroupCohomology.Extension.Equiv X Y) ↔
      Work.GroupCohomology.classOf X = Work.GroupCohomology.classOf Y := by
  constructor
  · rintro ⟨e⟩
    letI := X.groupE
    letI := Y.groupE
    letI := (Extension.ofCocycle Q A (cocycleOf X)).groupE
    letI := (Extension.ofCocycle Q A (cocycleOf Y)).groupE
    obtain ⟨eX⟩ := cocycleOf_equiv X
    obtain ⟨eY⟩ := cocycleOf_equiv Y
    -- `X ≅ E_{cX}`, `X ≅ Y` and `Y ≅ E_{cY}` compose to `E_{cX} ≅ E_{cY}`
    have h : Nonempty (Extension.Equiv (Extension.ofCocycle Q A (cocycleOf X))
        (Extension.ofCocycle Q A (cocycleOf Y))) :=
      ⟨(eX.symm.trans e).trans eY⟩
    exact (ofCocycle_equiv_iff (cocycleOf X) (cocycleOf Y)).mp h
  · intro h
    letI := X.groupE
    letI := Y.groupE
    letI := (Extension.ofCocycle Q A (cocycleOf X)).groupE
    letI := (Extension.ofCocycle Q A (cocycleOf Y)).groupE
    obtain ⟨eX⟩ := cocycleOf_equiv X
    obtain ⟨eY⟩ := cocycleOf_equiv Y
    -- equal classes give `E_{cX} ≅ E_{cY}`, which we compose with `X ≅ E_{cX}` and `E_{cY} ≅ Y`
    obtain ⟨e⟩ := (ofCocycle_equiv_iff (cocycleOf X) (cocycleOf Y)).mpr h
    exact ⟨(eX.trans e).trans eY.symm⟩

end Work.GroupCohomology

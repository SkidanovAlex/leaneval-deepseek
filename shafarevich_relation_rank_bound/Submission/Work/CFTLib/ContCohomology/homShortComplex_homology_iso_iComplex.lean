import Mathlib
import Submission.Work.CFTLib.ContCohomology.P1Iso
import Submission.Work.CFTLib.ContCohomology.Inhomogeneous
import Submission.Work.CFTLib.ContCohomology.exists_homCochain_iso_iCochain

open CategoryTheory

namespace Work.CFTLib.ContCohomology

/-- The second homology of the concrete homogeneous short complex `homCochain 1 → homCochain 2 →
homCochain 3` is the second cohomology of the inhomogeneous complex of continuous cochains.  The
isomorphism is induced by the termwise isomorphisms `homIsoInh p 1`, `homIsoInh p 2`, `homIsoInh p 3`,
which intertwine the differentials (`homIsoInh_homDiff`). -/
theorem homShortComplex_homology_iso_iComplex (p : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [LocallyCompactSpace Γ] :
    Nonempty ((Work.CFTLib.ContCohomology.homShortComplex
        (Work.CFTLib.ContCohomology.trivRep p Γ) 1).homology ≅
      (Work.CFTLib.ContCohomology.iComplex (Γ := Γ) p).homology 2) := by
  refine ⟨(ShortComplex.homologyMapIso ?e).trans
    (((iComplex (Γ := Γ) p).homologyIsoSc' 1 2 3 (ComplexShape.prev_eq' _ (by rfl))
      (ComplexShape.next_eq' _ (by rfl)))).symm⟩
  refine ShortComplex.isoMk (LinearEquiv.toModuleIso (homIsoInh p 1))
    (LinearEquiv.toModuleIso (homIsoInh p 2))
    (LinearEquiv.toModuleIso (homIsoInh p 3)) ?_ ?_
  · apply ModuleCat.hom_ext
    ext x
    exact (homIsoInh_homDiff p 1 x).symm
  · apply ModuleCat.hom_ext
    ext x
    exact (homIsoInh_homDiff p 2 x).symm

end Work.CFTLib.ContCohomology

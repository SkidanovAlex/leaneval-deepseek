/-
AREA DERFORMAL — holes 4–7 of the blueprint `Submission/Blueprint/Interfaces.lean`.

This is the top-level file of the area.  It contains the deliverable

  `derived_prop : Submission.Blueprint.ResolutionProp → Submission.Blueprint.DerivedProp`

together with the explicit construction `derivedPackage` of the derived package
(holes 4, 5, 6, 7 and the isomorphism property of the counit at solid-cofibrant complexes).

Mathematical content (REFS/02 §1):

* B1: if `K` is solid-cofibrant, then `solC K` is K-projective (`B1KProjective`) and the
  adjunction identifies `Hom_D(Q(solC K), Q N)` with `Hom_D(Q K, Q(incC N))` (`homDEquiv`,
  natural in `K`);
* B2: quasi-isomorphisms between solid-cofibrant complexes are sent to quasi-isomorphisms by
  `solC` (`B2`), so that `ρ ⋙ solC ⋙ Q` inverts quasi-isomorphisms and descends to
  `L : D(LightCondAb) ⥤ D(Solid)` (`ResData.L`), with counit `α : Q ⋙ L ⟶ solC ⋙ Q`
  (`ResData.alpha`), which is an isomorphism at solid-cofibrant complexes
  (`ResData.iso_of_cofibrant`);
* B3: `L` is the total left derived functor of `solC ⋙ Q` (`ResData.isLeft`) and is left adjoint
  to the derived inclusion (`ResData.adj`).

Everything is stated for the solidification functor `sol := isSolid.ι.leftAdjoint` determined by
`Submission.Blueprint.ReflProp`; the only assumption beyond that is the existence of functorial
solid-cofibrant resolutions (`Submission.Blueprint.ResolutionProp`, area RESOL).

What a caller imports: `Submission.Work.DERFORMAL.Main`.

Main declarations (all in namespace `Work.DERFORMAL`):

* `derived_prop (hres : ResolutionProp) : DerivedProp`
* `derivedPackage (hres : ResolutionProp) : DerivedPackage`
* `ResData.L`, `ResData.alpha`, `ResData.isLeft`, `ResData.adj`, `ResData.iso_of_cofibrant`
* `solidEquiv_iff : SolidEquiv f ↔ IsIso (D.L.map f)`
  (`D : DerivedPackage`, for an arbitrary such package)
* `B1KProjective`, `homDEquiv`, `homDEquiv_naturality`, `B2` (the technical core)
-/
import Submission.Work.DERFORMAL.Package

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.DERFORMAL

variable [isSolid.ι.IsRightAdjoint]

/-- The resolution data of `Submission.Blueprint.ResolutionProp`, together with the
K-projectivity of `solC` on solid-cofibrant complexes (B1). -/
noncomputable def resDataOf (hres : Submission.Blueprint.ResolutionProp) : ResData :=
  let h := hres.1
  { ρ := h.choose
    ε := h.choose_spec.choose
    hcof := h.choose_spec.choose_spec.1
    hqiso := h.choose_spec.choose_spec.2
    hproj := fun K hK => B1KProjective K hK }

/-- The derived package of `Submission.Blueprint.ResolutionProp` (explicit form of the first half
of `derived_prop`). -/
noncomputable def derivedPackage (hres : Submission.Blueprint.ResolutionProp) :
    Submission.Blueprint.DerivedPackage :=
  (resDataOf hres).package

/-- **AREA DERFORMAL — holes 4–7.**  From functorial solid-cofibrant resolutions, derived
solidification exists: it is the total left derived functor of degreewise solidification, left
adjoint to the derived inclusion, with a counit that is an isomorphism at solid-cofibrant
complexes; and solid-equivalences are exactly the maps inverted by it.

`Submission.Blueprint.DerivedProp` carries no hypothesis on resolutions, while the area is
instructed to assume `Submission.Blueprint.ResolutionProp` (area RESOL); this is recorded here
as an explicit hypothesis. -/
theorem derived_prop (hres : Submission.Blueprint.ResolutionProp) :
    Submission.Blueprint.DerivedProp := by
  intro inst
  exact ⟨⟨resDataOf hres |>.package⟩, fun D X Y f => solidEquiv_iff D f⟩

end Work.DERFORMAL

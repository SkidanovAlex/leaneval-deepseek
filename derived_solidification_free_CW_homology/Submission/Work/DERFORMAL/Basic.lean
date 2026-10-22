/-
AREA DERFORMAL — holes 4–7: derived solidification from functorial resolutions.

This file sets up the vocabulary of the area.  Everything else in `Submission/Work/DERFORMAL/`
builds on the definitions and lemmas below.

Conventions (identical to `Submission.Blueprint.Interfaces`):
* `sl : LightCondAb ⥤ Solid` is the solidification functor, i.e. the left adjoint of the
  inclusion `isSolid.ι` (`slAdj : sl ⊣ isSolid.ι`); it depends on the ambient instance
  `[isSolid.ι.IsRightAdjoint]` (`ReflProp`);
* `solC` (resp. `incC`) is `sl` (resp. `isSolid.ι`) applied degreewise to cochain complexes,
  indexed cohomologically by `ComplexShape.up ℤ`;
* `K`/`D` are the homotopy/derived categories and `Qh`/`Q` the localization functors, so that
  `Q = HomotopyCategory.quotient ⋙ Qh`.
-/
import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.DERFORMAL

/-! ## Basic abbreviations (not depending on `ReflProp`) -/

/-- The category of cochain complexes of light condensed abelian groups. -/
abbrev Cpx : Type 1 := CochainComplex LightCondAb ℤ

/-- The category of cochain complexes of solid light condensed abelian groups. -/
abbrev SCpx : Type 1 := CochainComplex Solid ℤ

/-- The homotopy category `K(LightCondAb)` of cochain complexes. -/
abbrev KCat : Type 1 := HomotopyCategory LightCondAb (ComplexShape.up ℤ)

/-- The homotopy category `K(Solid)` of cochain complexes of solid objects. -/
abbrev SKCat : Type 1 := HomotopyCategory Solid (ComplexShape.up ℤ)

/-- The derived category `D(LightCondAb)`. -/
abbrev DCat : Type 1 := DerivedCategory LightCondAb

/-- The derived category `D(Solid)`. -/
abbrev SDCat : Type 1 := DerivedCategory Solid

/-- The degreewise inclusion of complexes of solid objects. -/
abbrev incC : SCpx ⥤ Cpx := Submission.Blueprint.ιC

/-- The cochain complex as an object of the homotopy category of light condensed abelian
groups. -/
abbrev hq (K : Cpx) : KCat := Submission.Blueprint.hq K

/-- The cochain complex as an object of the homotopy category of solid objects. -/
abbrev hs (K : SCpx) : SKCat := (HomotopyCategory.quotient Solid (ComplexShape.up ℤ)).obj K

/-- The localization functor `C(C) ⥤ D(C)` (for any abelian `C` with a chosen derived
category). -/
abbrev Q := @DerivedCategory.Q

/-- The localization functor `C(C) ⥤ D(C)`, used on the solid side. -/
abbrev Qs := @DerivedCategory.Q

/-- The functor `K(C) ⥤ D(C)`. -/
abbrev Qh := @DerivedCategory.Qh

/-- The class of quasi-isomorphisms of complexes of light condensed abelian groups. -/
abbrev Wq : MorphismProperty Cpx := HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ)

/-- The class of quasi-isomorphisms of complexes of solid objects. -/
abbrev Ws : MorphismProperty SCpx := HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ)

/-- Solid-cofibrant complexes (blueprint terminology). -/
abbrev Cofibrant (K : Cpx) : Prop := Submission.Blueprint.SolidCofibrant K

/-- Solid-equivalences (blueprint terminology). -/
abbrev SEquiv {X Y : DCat} (f : X ⟶ Y) : Prop := Submission.Blueprint.SolidEquiv f

section

variable [isSolid.ι.IsRightAdjoint]

/-! ## Degreewise solidification and its adjunction -/

/-- The solidification functor (the left adjoint of the inclusion `isSolid.ι`). -/
abbrev sl : LightCondAb ⥤ Solid := Submission.Blueprint.sol

/-- The solidification adjunction. -/
abbrev slAdj : sl ⊣ isSolid.ι := Submission.Blueprint.solAdj

/-- Degreewise solidification of cochain complexes. -/
abbrev solC : Cpx ⥤ SCpx := Submission.Blueprint.solC

/-- The homotopy-category functor induced by solidification. -/
abbrev solK : KCat ⥤ SKCat := sl.mapHomotopyCategory (ComplexShape.up ℤ)

/-- The homotopy-category functor induced by the inclusion of solid objects. -/
abbrev incK : SKCat ⥤ KCat := isSolid.ι.mapHomotopyCategory (ComplexShape.up ℤ)

/-- The counit of the solidification adjunction is an isomorphism (the right adjoint is fully
faithful, being the inclusion of a full subcategory). -/
instance isIso_counit_slAdj : IsIso slAdj.counit :=
  Adjunction.counit_isIso_of_R_fully_faithful _

/-- The natural isomorphism `isSolid.ι ⋙ sl ≅ 𝟭 Solid` given by the counit of the
solidification adjunction. -/
def incC_comp_solC_iso : incC ⋙ solC ≅ 𝟭 SCpx :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl (isSolid.ι ⋙ sl)) (ComplexShape.up ℤ)) ≪≫
    (NatIso.mapHomologicalComplex (asIso slAdj.counit) (ComplexShape.up ℤ)) ≪≫
    (Functor.mapHomologicalComplexIdIso Solid (ComplexShape.up ℤ)).symm

end

end Work.DERFORMAL

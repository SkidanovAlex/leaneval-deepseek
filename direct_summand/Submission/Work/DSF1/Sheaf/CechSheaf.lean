/-
# The sheaf-level Čech complex of a family of opens (DSF1, obligation O1) — partial

For a scheme `X` and a family of opens `U : ι → X.Opens`, the Čech complex of the structure sheaf
is the complex whose degree-`p` term is the product, over `x : Fin (p+1) → ι`, of the sheaves
`(j)_* 𝒪` for the open immersion `j` of `U (x 0) ⊓ ⋯ ⊓ U (x p)` into `X`; its sections over an
open `V` are `Γ(X, (U (x 0) ⊓ ⋯ ⊓ U (x p)) ⊓ V)`, so applying global sections recovers the
challenge's complex `DSMap.cech A X f U`.

This file contains the two basic ingredients of that presheaf: the sheaves `secSheaf V` and their
restriction maps `secSheafMap h`.  What is still missing (see `DSF1/DESIGN.md`, obligation (O1)) is
the functoriality `secSheafMap h₁ ≫ secSheafMap h₂ = secSheafMap (h₂.trans h₁)` (which is checked
on `⊤`-sections, where the maps are the restriction maps of the structure sheaf), the resulting
presheaf `cechSheafPresheaf : (X.Opens)ᵒᵖ ⥤ X.Modules` (and hence the sheaf-level Čech complex)
together with its augmentation, and the comparison of complexes with `DSMap.cechZ`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.DSMap.Map
import Submission.Work.DSF1.Modules.pushforward_unit_sections

open CategoryTheory AlgebraicGeometry Opposite Limits

namespace Work.DSF1

universe u

variable {X : Scheme.{u}}

/-- The sheaf on `X` pushed forward from the structure sheaf of the open `V`: its sections over
`W` are the sections of `𝒪_X` over `V ⊓ W`.  This is the building block of the Čech complex of a
family of opens. -/
noncomputable abbrev secSheaf (V : X.Opens) : X.Modules :=
  (Scheme.Modules.pushforward V.ι).obj (SheafOfModules.unit V.toScheme.ringCatSheaf)

/-- Restriction of sections `secSheaf V ⟶ secSheaf V'` for `V' ≤ V`, built from the mate of
`Scheme.Modules.restrictUnitIso` along the adjunction `Scheme.Modules.restrictFunctor ⊣
Scheme.Modules.pushforward` and the composition iso `Scheme.Modules.pushforwardComp`. -/
noncomputable def secSheafMap {V V' : X.Opens} (h : V' ≤ V) : secSheaf V ⟶ secSheaf V' :=
  (Scheme.Modules.pushforward V.ι).map
      ((Scheme.Modules.restrictAdjunction (X.homOfLE h)).unit.app
          (SheafOfModules.unit V.toScheme.ringCatSheaf) ≫
        (Scheme.Modules.pushforward (X.homOfLE h)).map
          (Scheme.Modules.restrictUnitIso (X.homOfLE h)).hom) ≫
    (Scheme.Modules.pushforwardComp (X.homOfLE h) V.ι).hom.app
      (SheafOfModules.unit V'.toScheme.ringCatSheaf) ≫
    (Scheme.Modules.pushforwardCongr (Scheme.homOfLE_ι X h)).hom.app
      (SheafOfModules.unit V'.toScheme.ringCatSheaf)

end Work.DSF1

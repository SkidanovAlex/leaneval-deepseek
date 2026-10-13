import Mathlib
import ChallengeDeps
import Submission.Work.DSF1.Sheaf.exists_cechSheafPresheaf

/-!
# The canonical identification `𝒪_X ⟶ (V.ι)_* 𝒪_V` (DSF1)

For an open `V` of a scheme `X`, the sheaf `Work.DSF1.secSheaf V = (V.ι)_* 𝒪_V` is the pushforward
of the structure sheaf of the open subscheme `V`.  The *canonical* map

`canonical V : 𝒪_X ⟶ (V.ι)_* 𝒪_V`

is the restriction of the structure sheaf from `X` to `V`: it is the unit of the adjunction
`Scheme.Modules.restrictFunctor V.ι ⊣ Scheme.Modules.pushforward V.ι`, followed by the pushforward
of the identification `(V.ι)^* 𝒪_X ≅ 𝒪_V`
(`Scheme.Modules.restrictUnitIso`).  It is the building block of the Čech coaugmentation
`Work.DSF1.Cech.cechSheafCoaug`, which is stated at `V = ⊤`; the passage from that base object to
the challenge's `SheafOfModules.unit X.ringCatSheaf` is through `canonical ⊤`.

The two facts about `canonical ⊤` used by the assembly of area `F1`:

* `canonical ⊤` is an isomorphism;
* `Γ(X, canonical ⊤) ≫ (psi ⊤).hom` is the identity identification
  `Γ(X, 𝒪_X) ≅ Γ(X, ⊤)` of the structure sheaf, so that the Čech coaugmentation of the challenge
  (`DSMap.coaug0`) is the transport of `cechSheafCoaug` along `canonical ⊤`.
-/

namespace Work.DSF1

open CategoryTheory AlgebraicGeometry Opposite Limits

universe u

/-- The canonical map `𝒪_X ⟶ (V.ι)_* 𝒪_V` (restriction of the structure sheaf to the open `V`):
the unit of the adjunction `restrictFunctor V.ι ⊣ pushforward V.ι`, followed by the pushforward of
`(V.ι)^* 𝒪_X ≅ 𝒪_V`. -/
noncomputable def canonical {X : AlgebraicGeometry.Scheme.{u}} (V : X.Opens) :
    SheafOfModules.unit X.ringCatSheaf ⟶ Work.DSF1.secSheaf V :=
  (Scheme.Modules.restrictAdjunction V.ι).unit.app (SheafOfModules.unit X.ringCatSheaf) ≫
    (Scheme.Modules.pushforward V.ι).map ((Scheme.Modules.restrictUnitIso V.ι).hom)

end Work.DSF1

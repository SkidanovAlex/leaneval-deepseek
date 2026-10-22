import Mathlib
import Submission.Work.ANALYTIC.ProdZModel
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ANALYTIC.ProdZAux
import Submission.Work.ANALYTIC.LcZIsoCz

/-!
# The model `∏_ℕ ℤ` is the product `∏ᶜ (fun _ : ℕ => ℤ)`

`Work.ANALYTIC.prodZ = ∏ᶜ (fun _ : ℕ => Z)` is the `ℕ`-indexed product of copies of the constant
light condensed abelian group `ℤ`, and `Work.ANALYTIC.prodZModel` is the light condensed abelian
group whose `S`-points are *definitionally* the families `ℕ → C(S,ℤ)` of continuous `ℤ`-valued
functions on `S`.  The present file shows that the two are isomorphic, so that statements about
`∏ℤ` (as used in REFS/03 §3) may be checked on the explicit sections of `prodZModel`.

The proof is a composition of four isomorphisms of presheaves on `LightProfinite`
(`Work.ANALYTIC.ProdZAux` and `Work.ANALYTIC.LcZIsoCz`):

* `prodZObj_iso_piZobj` : `(∏ᶜ fun _ => Z).obj ≅ ∏ᶜ (fun _ => Z.obj)`, i.e. the presheaf underlying
  the product is the pointwise product, because `sheafToPresheaf` creates limits
  (`CategoryTheory.Sheaf.createsLimitsOfShape`);
* `ZobjIsoLcZ` : `Z.obj ≅ lcZ`, the identification of the constant sheaf `ℤ` with the presheaf of
  locally constant `ℤ`-valued functions (`LightCondMod.LocallyConstant.functorIsoDiscrete`);
* `LcZIsoCz` : `lcZ ≅ Cz`, the identification of locally constant with continuous `ℤ`-valued
  functions (a light profinite space is totally disconnected and `ℤ` is discrete);
* `piCz_iso_prodZPresheaf` : `∏ᶜ (fun _ => Cz) ≅ prodZPresheaf`, because limits in a functor
  category are computed pointwise, where the `d`-points of `prodZPresheaf` are, definitionally, the
  concrete product `ModuleCat.productCone` of the `ℤ`-modules `C(d.unop,ℤ)`.

Since `LightCondAb` is a full subcategory of presheaves, an isomorphism of the underlying presheaves
is an isomorphism of light condensed abelian groups (`ObjectProperty.isoMk`).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

theorem prodZModel_isoC :
    Nonempty (CategoryTheory.Iso Work.ANALYTIC.prodZModel Work.ANALYTIC.prodZ) := by
  obtain ⟨eP⟩ := prodZObj_iso_piZobj
  obtain ⟨eB⟩ := LcZIsoCz
  obtain ⟨eC⟩ := piCz_iso_prodZPresheaf
  exact ⟨ObjectProperty.isoMk
    (P := Presheaf.IsSheaf (coherentTopology LightProfinite) (A := ModuleCat ℤ))
    (eP ≪≫ Pi.mapIso (fun _ : ℕ => ZobjIsoLcZ ≪≫ eB) ≪≫ eC).symm⟩

end Work.ANALYTIC

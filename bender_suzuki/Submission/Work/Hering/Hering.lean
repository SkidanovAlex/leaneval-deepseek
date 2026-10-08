import Submission.Work.Hering.Main
import Submission.Work.Hering.HardCore.nonAbelianCase
import Submission.Work.Hering.AppVIII.appVIIIProp1
import Submission.Work.Hering.AppVIII.appVIIIProp3
import Submission.Work.Hering.AppVIII.appVIIIProp4
import Submission.Work.Hering.GL32.appIX
import Submission.Work.Hering.AppVII.appVII

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The area theorem `HeringProp`

This file discharges the two named hypotheses of `Work.Hering.Main`:

* `NonAbelianCaseProp` (the non-abelian case §4 of the hard core) from the Higman area's full
  classification `Work.Higman.HigmanClassProp` and the Appendices VIII/IX inputs of this area;
* the reduction's `AppVIIProp` from `Work.Hering.AppVII.appVII`.
-/

set_option autoImplicit false

namespace Work.Hering

open LeanEval.GroupTheory.Defs

/-- The non-abelian case of the hard core, from Higman's classification (with the order-`q³` types
`B`, `C`, `D`) and Appendix VIII/IX. -/
theorem nonAbelianCaseProp_of_higmanClass (hHig : Work.Higman.HigmanClassProp) :
    ∀ {G : Type} [Group G] [Finite G], NonAbelianCaseProp (G := G) :=
  fun {G} _ _ => HardCore.nonAbelianCase hHig AppVIII.appVIIIProp1 AppVIII.appVIIIProp3
    AppVIII.appVIIIProp4 GL32.appIX

/-- The hard core of Hering's theorem, from Higman's classification and Appendix VIII/IX. -/
theorem no_reduced_config_of_higmanClass (hHig : Work.Higman.HigmanClassProp) :
    NoReducedConfigProp :=
  no_reduced_config (nonAbelianCaseProp_of_higmanClass hHig)

/-- **Hering's theorem** (Peterfalvi I, Théorème E, p. 188): a finite group of even order acting
doubly transitively by conjugation on its involutions has 2-rank one.

The external inputs are Feit–Thompson (`hFT`, used only inside Appendix VII, in the
non-solvable case — see the docstring of `Work.Hering.AppVII.appVII`), G. Higman's classification
of Suzuki 2-groups (the area `Higman`'s `HigmanClassProp`, which covers the order-`q²` and
order-`q³` types), and Appendices II(5), VII, VIII, IX and Wagner's proposition, all proved in
this area. -/
theorem Hering (hFT : Submission.Blueprint.FeitThompsonProp)
    (hHig : Work.Higman.HigmanClassProp) : Submission.Blueprint.HeringProp :=
  Hering_of_noReducedConfig (no_reduced_config_of_higmanClass hHig)
    (AppVII.appVII_of_FT hFT)

/-- Hering's theorem from Higman's classification, with Appendix VII taken as the (true but
Feit–Thompson-dependent) `AppVIIProp`. -/
theorem Hering_of_higmanClass (hHig : Work.Higman.HigmanClassProp)
    (hAppVII : AppVIIProp.{0, 0}) : Submission.Blueprint.HeringProp :=
  Hering_of_noReducedConfig (no_reduced_config_of_higmanClass hHig) hAppVII

/-- Hering's theorem from the two halves of Higman's classification separately
(`HigmanProp` covers the order-`q²` types and the general structure, `HigmanQ3Prop` the
order-`q³` types `B`, `C`, `D`). -/
theorem Hering_of_higmanQ3 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hHig : Submission.Blueprint.HigmanProp) (hQ3 : Work.Higman.HigmanQ3Prop) :
    Submission.Blueprint.HeringProp :=
  Hering hFT ⟨hHig, hQ3⟩

end Work.Hering

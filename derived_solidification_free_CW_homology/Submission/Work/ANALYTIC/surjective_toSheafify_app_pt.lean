import Mathlib
import Submission.Work.ATOM.Defs

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

namespace Work.ANALYTIC

open _root_.LightCondensed
open Opposite

/-- The unit of sheafification is surjective at the one-point light profinite set `∗`.  Route:
`Presheaf.IsLocallySurjective (coherentTopology LightProfinite) (toSheafify J P)` is an instance
(`Mathlib/CategoryTheory/Sites/LocallyBijective`), so for `s : (sheafify J P)(∗)` the sieve
`Presheaf.imageSieve (toSheafify J P) s ∈ J ∗`; by the hypothesis it is `⊤`, hence contains
`𝟙 ∗`, and the defining property of `imageSieve` (`Presheaf.app_localPreimage`) gives `t` with
`(toSheafify J P).app _ t = s`. -/
theorem surjective_toSheafify_app_pt
    (h : ∀ S : (coherentTopology LightProfinite.{0}).Cover Work.ATOM.pt, S = ⊤)
    (P : (LightProfinite.{0})ᵒᵖ ⥤ ModuleCat.{0} ℤ) :
    Function.Surjective ((CategoryTheory.toSheafify (coherentTopology LightProfinite.{0}) P).app
      (Opposite.op Work.ATOM.pt)) := by
  intro s
  have hmem : Presheaf.imageSieve
      (CategoryTheory.toSheafify (coherentTopology LightProfinite.{0}) P) s ∈
      (coherentTopology LightProfinite.{0}) Work.ATOM.pt :=
    Presheaf.imageSieve_mem (coherentTopology LightProfinite.{0}) _ s
  have htop : Presheaf.imageSieve
      (CategoryTheory.toSheafify (coherentTopology LightProfinite.{0}) P) s = ⊤ :=
    congrArg Subtype.val (h ⟨_, hmem⟩)
  refine ⟨Presheaf.localPreimage
    (CategoryTheory.toSheafify (coherentTopology LightProfinite.{0}) P) s
    (𝟙 Work.ATOM.pt) ?_, ?_⟩
  · rw [htop]; exact trivial
  · rw [Presheaf.app_localPreimage]; simp

end Work.ANALYTIC

/-- The statement of `Work.ANALYTIC.Work.ANALYTIC.surjective_toSheafify_app_pt` under the name
`Work.ANALYTIC.surjective_toSheafify_app_pt`, which is the name derived from the module path
`Submission.Work.ANALYTIC.surjective_toSheafify_app_pt`. -/
theorem surjective_toSheafify_app_pt
    (h : ∀ S : (coherentTopology LightProfinite.{0}).Cover Work.ATOM.pt, S = ⊤)
    (P : (LightProfinite.{0})ᵒᵖ ⥤ ModuleCat.{0} ℤ) :
    Function.Surjective ((CategoryTheory.toSheafify (coherentTopology LightProfinite.{0}) P).app
      (Opposite.op Work.ATOM.pt)) :=
  _root_.Work.ANALYTIC.Work.ANALYTIC.surjective_toSheafify_app_pt h P

end Work.ANALYTIC

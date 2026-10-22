import Mathlib
import Submission.Work.ANALYTIC.CechPt.DdZfAux
import Submission.Work.ANALYTIC.CechPt.LCZhom_eq_unit

/-!
# The section of `Cdisc T` attached to the span of the constant function `1`

For a light profinite set `T`, the composite

`𝟙 --lcDiscIntIso.inv--> lcDisc ℤ --lcDisc.map (span 1)--> lcDisc (LC T) = Cdisc T`

is the global section of `Cdisc T` whose value at the point is the constant function `1 ∈ C(T,ℤ)`.

## Proof

`toPointEquiv (Cdisc T) u = homFreeEquiv ∗ (Cdisc T) (unitIso.inv ≫ u)`
(`Work.ATOM.toPointEquiv_apply`), and `homFreeEquiv` is natural in the target
(`Work.ATOM.homFreeEquiv_naturality_target`): precomposing with a morphism of light condensed
abelian groups applies the corresponding map on sections.  It therefore suffices to know the value
at the point of `unitIso.inv ≫ lcDiscIntIso.inv : ℤ[∗] ⟶ lcDisc ℤ`, which is the canonical
generator `oneLCZ = LocallyConstant.const 1` of `LCZ(∗)` — this is `LCZhom_eq_unit` together with
`Work.ATOM.ZS.Unred.homFreeEquiv_LCZhom` — and then to evaluate the section map of
`lcDisc.map (span 1)`, which is *definitionally* `LocallyConstant.map` of the span map, on the
constant function `1`.

Two transparency remarks.  `Work.ANALYTIC.Cdisc T` is a semireducible `def`, so we unfold it once
by `dsimp only` before rewriting under `homFreeEquiv`; and the `rw`s run under
`backward.isDefEq.respectTransparency false`, the standard device in this workspace for rewriting
under binders whose instance arguments were elaborated through the reducible alias
`LightCondAb = LightCondMod ℤ`.
-/

open CategoryTheory LightProfinite MonoidalCategory Opposite

noncomputable section

namespace Work.ANALYTIC.CechPt

/-- The section map of a composite is the composite of the section maps (at the level of
elements). -/
private lemma comp_app_apply {X Y Z : LightCondAb} (f : X ⟶ Y) (g : Y ⟶ Z)
    (S : LightProfinite) (x : X.obj.obj (Opposite.op S)) :
    ((f ≫ g).hom.app (Opposite.op S)) x
      = (g.hom.app (Opposite.op S)) ((f.hom.app (Opposite.op S)) x) := rfl

/-- The section map of `lcDisc (span 1)` at the point is `LocallyConstant.map` of the span map, and
it sends the constant function `1` to the constant function `1`. -/
private lemma lcDisc_map_span_one_apply (T : LightProfinite.{0}) :
    (((LightCondMod.LocallyConstant.functor ℤ).map (ModuleCat.ofHom
        (LinearMap.toSpanSingleton ℤ (LocallyConstant ↥T ℤ) (1 : LocallyConstant ↥T ℤ)))).hom.app
        (Opposite.op Work.ATOM.pt)) Work.ATOM.ZS.Unred.oneLCZ
      = LocallyConstant.const ↥(Work.ATOM.pt.toTop) (1 : Work.ANALYTIC.Haar.LC T) := by
  show LocallyConstant.map (fun n : ℤ => n • (1 : LocallyConstant ↥T ℤ))
      (LocallyConstant.const ↥(Work.ATOM.pt.toTop) 1)
    = LocallyConstant.const ↥(Work.ATOM.pt.toTop) (1 : LocallyConstant ↥T ℤ)
  ext x
  simp

/-- The point section of the canonical identification `𝟙 ≅ lcDisc ℤ` is the canonical generator
`oneLCZ` of `LCZ(∗)`: this is `LCZhom_eq_unit` (`LCZhom = unitIso.inv ≫ lcDiscIntIso.inv`),
`LCZhom` being by definition the morphism `ℤ[∗] ⟶ LCZ` carrying the canonical generator of `ℤ[∗]`
to `oneLCZ`. -/
private lemma homFreeEquiv_pt_lcDiscIntIso :
    Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ATOM.ZS.Unred.LCZ
      (Work.ATOM.unitIso.inv ≫ Work.ANALYTIC.CechPt.lcDiscIntIso.inv) = Work.ATOM.ZS.Unred.oneLCZ := by
  rw [← Work.ANALYTIC.CechPt.LCZhom_eq_unit]
  exact Work.ATOM.ZS.Unred.homFreeEquiv_LCZhom

set_option backward.isDefEq.respectTransparency false in
theorem toPointEquiv_lcDisc_span_zz (T : LightProfinite.{0}) :
    Work.ATOM.toPointEquiv (Work.ANALYTIC.Cdisc T)
      (CategoryTheory.CategoryStruct.comp Work.ANALYTIC.CechPt.lcDiscIntIso.inv
        ((LightCondMod.LocallyConstant.functor ℤ).map
          (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (LocallyConstant ↥T ℤ)
            (1 : LocallyConstant ↥T ℤ)))))
      = LocallyConstant.const ↥(Work.ATOM.pt.toTop) (1 : Work.ANALYTIC.Haar.LC T) := by
  -- `toPointEquiv` is `homFreeEquiv` composed with the monoidal unit isomorphism
  rw [Work.ATOM.toPointEquiv_apply]
  -- unfold the semireducible `Cdisc`
  dsimp only [Work.ANALYTIC.Cdisc]
  -- naturality of `homFreeEquiv` in the target: move `lcDiscIntIso.inv ≫ lcDisc.map (span 1)`
  -- to the section side
  rw [Work.ATOM.homFreeEquiv_naturality_target (S := Work.ATOM.pt)
      (h := Work.ANALYTIC.CechPt.lcDiscIntIso.inv ≫
        (LightCondMod.LocallyConstant.functor ℤ).map
          (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (LocallyConstant ↥T ℤ)
            (1 : LocallyConstant ↥T ℤ))))
      (g := Work.ATOM.unitIso.inv)]
  -- split the two section maps
  rw [comp_app_apply]
  -- and identify the value of the first one at the canonical generator
  rw [← Work.ATOM.homFreeEquiv_naturality_target (S := Work.ATOM.pt)
      (h := Work.ANALYTIC.CechPt.lcDiscIntIso.inv) (g := Work.ATOM.unitIso.inv)]
  rw [homFreeEquiv_pt_lcDiscIntIso]
  exact lcDisc_map_span_one_apply T

end Work.ANALYTIC.CechPt

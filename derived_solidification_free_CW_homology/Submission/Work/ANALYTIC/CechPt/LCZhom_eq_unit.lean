import Mathlib
import Submission.Work.ANALYTIC.CechPt.DualCechBridge
import Submission.Work.ANALYTIC.CechPt.DdZfAux

/-!
# `LCZhom = unitIso.inv ≫ lcDiscIntIso.inv`

Both `ℤ[∗]` (`zfree pt`) and the monoidal unit `𝟙_ LightCondAb` (which is, by definition, the
"discrete" sheaf `Z = (discrete ℤ).obj ℤ`) represent the same functor
`A ↦ A(∗)` — the first through the free/forget adjunction (`homFreeEquiv`), the second
through `toPointEquiv`, which is *defined* using the monoidal unit isomorphism
`unitIso : 𝟙_ ≅ ℤ[∗]` of the monoidal functor `zfree = lightProfiniteToCondensed ⋙ free ℤ`.
The Yoneda comparison between the two representing objects is exactly `unitIso.inv`.

Similarly `lcDisc ℤ = LCZ` is the "locally constant model" of the constant sheaf `ℤ`, and
`lcDiscIntIso.inv : 𝟙_ ⟶ LCZ` is the canonical identification (`functorIsoDiscrete`), which
carries the canonical generator of `Z(∗)` to `oneLCZ` (`ZisoLCZ_hom_unitConstSheaf`).

Since `LCZhom = (homFreeEquiv ∗ LCZ).symm oneLCZ` is the map carrying the canonical generator
`e₁ = homFreeEquiv ∗ ℤ[∗] 𝟙` of `ℤ[∗](∗)` to `oneLCZ`, it suffices to know that the canonical
generator of `Z(∗)` is

* `homFreeEquiv ∗ Z unitIso.inv = (discreteUnderlyingAdj ℤ).unit.app ℤ 1`

— the coherence between the monoidal unit isomorphism of `zfree` and the unit of the
constant-sheaf adjunction `discrete ⊣ underlying` — which is what is proved first below.

## The computation of `homFreeEquiv ∗ Z unitIso.inv`

`unitIso.inv = ε⁻¹` is the inverse of the `ε`-isomorphism of the composite monoidal functor
`zfree`, so

`unitIso.inv = zfree.map (η lightProfiniteToLightCondSet) ≫ η (free ℤ)`

(`Functor.OplaxMonoidal.comp_η`).  Both factors are `presheafToSheaf`-images of presheaf maps
(they are the inverse `η`-coherences of the localised monoidal structure), so evaluating them on
the generic element `e₁ = toSheafify (freeMk 𝟙)` of `ℤ[∗]` is a two-step computation:

1. `η (free ℤ) = presheafToSheaf.map (η WR)` where `WR = whiskeringRight (ModuleCat.free ℤ)`;
   `ε (presheafToSheaf) = 𝟙` (`rfl`) and `ε (sheafToPresheaf) = 𝟙` (`sheafToPresheaf_ε`);
2. the general formula `p2s_toSheafify` for the value of a sheafification-induced map on
   `toSheafify y`;
3. the value of `η WR` at the point is `η (ModuleCat.free ℤ) = (ε (ModuleCat.free ℤ))⁻¹`, and
   `ε (ModuleCat.free ℤ) 1 = freeMk PUnit.unit`; since the `∗`-sections of `𝟙_ LightCondSet`
   are a subsingleton, the argument `xSect` of `freeMk` is that canonical element;
4. `(ε (ModuleCat.free ℤ))⁻¹ (freeMk ∗) = 1` because `(ε ≫ η) 1 = 1`
   (`Functor.Monoidal.ε_η`).

The result is the element `toSheafify 1` of the constant sheaf, which is exactly
`(discreteUnderlyingAdj ℤ).unit.app ℤ 1` (`unitConst_eq_toSheafify`).
-/

namespace Work.ANALYTIC.CechPt

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed

set_option maxHeartbeats 800000

set_option backward.isDefEq.respectTransparency false in
/-- **The value of a sheafification-induced map on `toSheafify`.**  This is
`CategoryTheory.toSheafify_naturality`: the canonical map `P ⟶ P⁺` is natural, so a map
`P⁺ ⟶ Q⁺` induced by `β : P ⟶ Q` sends the image of `y` to the image of `β y`. -/
private theorem p2s_toSheafify {P Q : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ} (β : P ⟶ Q)
    (U : LightProfinite) (y : P.obj (Opposite.op U)) :
    ConcreteCategory.hom (((presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)).map
        β).hom.app (Opposite.op U))
        (ConcreteCategory.hom
          ((CategoryTheory.toSheafify (coherentTopology LightProfinite) P).app (Opposite.op U)) y)
      = ConcreteCategory.hom
          ((CategoryTheory.toSheafify (coherentTopology LightProfinite) Q).app (Opposite.op U))
        (ConcreteCategory.hom (β.app (Opposite.op U)) y) := by
  rw [← ConcreteCategory.comp_apply]
  rw [show ((presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)).map β).hom.app
        (Opposite.op U)
      = (CategoryTheory.sheafifyMap (coherentTopology LightProfinite) β).app (Opposite.op U)
      from rfl]
  rw [← NatTrans.comp_app]
  rw [← CategoryTheory.toSheafify_naturality (coherentTopology LightProfinite) β]
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply]

/-- The identity morphism of the point, viewed (through Yoneda) as the canonical element of the
`∗`-sections of `∗.toCondensed`.  This is the generic element used by the workspace's
`Work.ANALYTIC.zlz_unitElem`. -/
private noncomputable def ptSection :
    (Work.ATOM.pt.toCondensed).obj.obj (Opposite.op Work.ATOM.pt) :=
  𝟙 Work.ATOM.pt

/-- The canonical element `xSect = η lightProfiniteToLightCondSet (𝟙 ∗)` of the `∗`-sections of
the terminal light condensed set; it is the argument of `freeMk` which appears in the value of
`ℤ[η]` on the generic element. -/
private noncomputable def xSect : (𝟙_ LightCondSet).obj.obj (Opposite.op Work.ATOM.pt) :=
  ConcreteCategory.hom
    ((Functor.OplaxMonoidal.η lightProfiniteToLightCondSet).hom.app (Opposite.op Work.ATOM.pt))
    ptSection

set_option backward.isDefEq.respectTransparency false in
/-- **The `η`-isomorphism of the free functor is induced by the presheaf level `η`.**  The
monoidal functor `free ℤ = sheafToPresheaf ⋙ whiskeringRight (ModuleCat.free ℤ) ⋙
presheafToSheaf` is the composite of the (op)monoidal structures of its factors, and both
`presheafToSheaf` and `sheafToPresheaf` have `ε`- (and hence `η`-) isomorphism the identity. -/
private theorem eta_free_sh :
    Functor.OplaxMonoidal.η (LightCondensed.free ℤ)
      = (presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)).map
        (Functor.OplaxMonoidal.η
          ((Functor.whiskeringRight (LightProfiniteᵒᵖ) Type (ModuleCat ℤ)).obj
            (ModuleCat.free ℤ))) := by
  dsimp only [LightCondensed.free, Sheaf.composeAndSheafify]
  rw [Functor.OplaxMonoidal.comp_η, Functor.OplaxMonoidal.comp_η]
  rw [show Functor.OplaxMonoidal.η (sheafToPresheaf (coherentTopology LightProfinite) Type)
        = 𝟙 _ from by
        have h := Functor.Monoidal.η_ε (sheafToPresheaf (coherentTopology LightProfinite) Type)
        rw [sheafToPresheaf_ε, Category.comp_id] at h
        exact h,
      show Functor.OplaxMonoidal.η
          (presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)) = 𝟙 _ from by
        have h := Functor.Monoidal.η_ε
          (presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ))
        rw [show Functor.LaxMonoidal.ε
              (presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)) = 𝟙 _ from rfl,
          Category.comp_id] at h
        exact h]
  simp

/-- The `ε`-isomorphism of the free module functor sends the canonical generator `1` of `ℤ` to
the basis vector `freeMk PUnit.unit` of the free module on the point. -/
private theorem eps_free_freeMk :
    ConcreteCategory.hom (Functor.LaxMonoidal.ε (ModuleCat.free ℤ)) (1 : ℤ)
      = ModuleCat.freeMk PUnit.unit := by
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The unit of the constant-sheaf adjunction at `ℤ` is the sheafification of the canonical
element `1` of the constant presheaf `ℤ`. -/
private theorem unitConst_eq_toSheafify :
    (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app (ModuleCat.of ℤ ℤ) (1 : ℤ)
      = ConcreteCategory.hom ((CategoryTheory.toSheafify (coherentTopology LightProfinite)
          ((Functor.const (LightProfiniteᵒᵖ)).obj (ModuleCat.of ℤ ℤ))).app
            (Opposite.op Work.ATOM.pt)) (1 : ℤ) := by
  simp only [LightCondensed.discreteUnderlyingAdj, constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, Functor.comp_obj]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The coherence between the monoidal unit isomorphism of `zfree = ℤ[-]` and the unit of the
constant-sheaf adjunction.**  The generic element of `ℤ[∗](∗)` is carried by `unitIso.inv` to the
canonical element `(discreteUnderlyingAdj ℤ).unit.app ℤ 1` of `Z(∗)`. -/
private theorem homFreeEquiv_unitIso_inv_aux :
    Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ANALYTIC.Z Work.ATOM.unitIso.inv
      = (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app (ModuleCat.of ℤ ℤ)
          (1 : ℤ) := by
  rw [Work.ANALYTIC.zlz_homFreeEquiv_eq_eval]
  rw [show Work.ANALYTIC.zlz_unitElem Work.ATOM.pt = Work.ATOM.ZS.Unred.e1 from
    (Work.ANALYTIC.zlz_homFreeEquiv_id Work.ATOM.pt).symm]
  rw [show Work.ATOM.unitIso.inv
      = (LightCondensed.free ℤ).map (Functor.OplaxMonoidal.η lightProfiniteToLightCondSet)
        ≫ Functor.OplaxMonoidal.η (LightCondensed.free ℤ) from
    (Functor.OplaxMonoidal.comp_η lightProfiniteToLightCondSet (LightCondensed.free ℤ)).symm]
  erw [NatTrans.comp_app, ConcreteCategory.comp_apply]
  -- the inner factor `ℤ[η]` evaluated on the generic element
  have key1 : ConcreteCategory.hom (((LightCondensed.free ℤ).map
        (Functor.OplaxMonoidal.η lightProfiniteToLightCondSet)).hom.app
          (Opposite.op Work.ATOM.pt)) Work.ATOM.ZS.Unred.e1
      = ConcreteCategory.hom ((CategoryTheory.toSheafify (coherentTopology LightProfinite)
          (((Functor.whiskeringRight (LightProfiniteᵒᵖ) Type (ModuleCat ℤ)).obj
            (ModuleCat.free ℤ)).obj ((𝟙_ LightCondSet).obj))).app
              (Opposite.op Work.ATOM.pt)) (ModuleCat.freeMk xSect) := by
    let α : (((Functor.whiskeringRight (LightProfiniteᵒᵖ) Type (ModuleCat ℤ)).obj
        (ModuleCat.free ℤ)).obj (Work.ATOM.pt.toCondensed).obj)
        ⟶ (((Functor.whiskeringRight (LightProfiniteᵒᵖ) Type (ModuleCat ℤ)).obj
            (ModuleCat.free ℤ)).obj ((𝟙_ LightCondSet).obj)) :=
      ((Functor.whiskeringRight (LightProfiniteᵒᵖ) Type (ModuleCat ℤ)).obj
        (ModuleCat.free ℤ)).map
          ((sheafToPresheaf (coherentTopology LightProfinite) Type).map
            (Functor.OplaxMonoidal.η lightProfiniteToLightCondSet))
    have hα : ((LightCondensed.free ℤ).map
          (Functor.OplaxMonoidal.η lightProfiniteToLightCondSet)).hom
        = ((presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)).map α).hom := rfl
    have he1 : Work.ATOM.ZS.Unred.e1
        = ConcreteCategory.hom ((CategoryTheory.toSheafify (coherentTopology LightProfinite)
            (((Functor.whiskeringRight (LightProfiniteᵒᵖ) Type (ModuleCat ℤ)).obj
              (ModuleCat.free ℤ)).obj (Work.ATOM.pt.toCondensed).obj)).app
                (Opposite.op Work.ATOM.pt)) (ModuleCat.freeMk ptSection) := by
      rw [show Work.ATOM.ZS.Unred.e1 = Work.ANALYTIC.zlz_unitElem Work.ATOM.pt from
        Work.ANALYTIC.zlz_homFreeEquiv_id Work.ATOM.pt]
      exact Work.ANALYTIC.zlz_unitElem_eq_toSheafify_freeMk Work.ATOM.pt
    rw [he1]
    erw [hα]
    erw [p2s_toSheafify α Work.ATOM.pt (ModuleCat.freeMk ptSection)]
    have hαpt : ConcreteCategory.hom (α.app (Opposite.op Work.ATOM.pt)) (ModuleCat.freeMk ptSection)
        = ModuleCat.freeMk (ConcreteCategory.hom
            ((Functor.OplaxMonoidal.η lightProfiniteToLightCondSet).hom.app
              (Opposite.op Work.ATOM.pt)) ptSection) := by
      rw [show α.app (Opposite.op Work.ATOM.pt)
          = (ModuleCat.free ℤ).map ((Functor.OplaxMonoidal.η lightProfiniteToLightCondSet).hom.app
              (Opposite.op Work.ATOM.pt)) from rfl]
      exact ModuleCat.free_map_apply _ _
    rw [hαpt]
    rfl
  erw [key1]
  -- the outer factor `η (free ℤ)` evaluated on `toSheafify (freeMk xSect)`
  have key2 : ConcreteCategory.hom
        ((Functor.OplaxMonoidal.η (LightCondensed.free ℤ)).hom.app (Opposite.op Work.ATOM.pt))
        (ConcreteCategory.hom ((CategoryTheory.toSheafify (coherentTopology LightProfinite)
          (((Functor.whiskeringRight (LightProfiniteᵒᵖ) Type (ModuleCat ℤ)).obj
            (ModuleCat.free ℤ)).obj ((𝟙_ LightCondSet).obj))).app
              (Opposite.op Work.ATOM.pt)) (ModuleCat.freeMk xSect))
      = ConcreteCategory.hom ((CategoryTheory.toSheafify (coherentTopology LightProfinite)
          ((Functor.const (LightProfiniteᵒᵖ)).obj (ModuleCat.of ℤ ℤ))).app
            (Opposite.op Work.ATOM.pt)) (1 : ℤ) := by
    erw [eta_free_sh]
    erw [p2s_toSheafify
      (Functor.OplaxMonoidal.η ((Functor.whiskeringRight (LightProfiniteᵒᵖ) Type (ModuleCat ℤ)).obj
        (ModuleCat.free ℤ))) Work.ATOM.pt (ModuleCat.freeMk xSect)]
    congr 1
    rw [show (Functor.OplaxMonoidal.η ((Functor.whiskeringRight (LightProfiniteᵒᵖ) Type
        (ModuleCat ℤ)).obj (ModuleCat.free ℤ))).app (Opposite.op Work.ATOM.pt)
        = Functor.OplaxMonoidal.η (ModuleCat.free ℤ) from rfl]
    -- the `∗`-sections of `𝟙_ LightCondSet` are a subsingleton, so `xSect = PUnit.unit`
    have hx : xSect = PUnit.unit := by
      have h : Subsingleton ((𝟙_ LightCondSet).obj.obj (Opposite.op Work.ATOM.pt)) :=
        inferInstanceAs (Subsingleton PUnit)
      exact h.elim xSect PUnit.unit
    rw [show ModuleCat.freeMk xSect
        = ConcreteCategory.hom (Functor.LaxMonoidal.ε (ModuleCat.free ℤ)) (1 : ℤ) from by
      rw [eps_free_freeMk, hx]]
    have hcomp : ConcreteCategory.hom (Functor.OplaxMonoidal.η (ModuleCat.free ℤ))
        (ConcreteCategory.hom (Functor.LaxMonoidal.ε (ModuleCat.free ℤ)) (1 : ℤ)) = 1 := by
      have h := congrArg (fun f : 𝟙_ (ModuleCat ℤ) ⟶ 𝟙_ (ModuleCat ℤ) =>
          ConcreteCategory.hom f (1 : ℤ)) (Functor.Monoidal.ε_η (ModuleCat.free ℤ))
      rw [ConcreteCategory.comp_apply] at h
      simpa using h
    exact hcomp
  erw [key2]
  exact unitConst_eq_toSheafify.symm

set_option backward.isDefEq.respectTransparency false in
/-- **The canonical identification `ZisoLCZ = lcDiscIntIso` carries the canonical generator of
`Z(∗)` to `oneLCZ`.**  `ZisoLCZ.hom` is the inverse of `functorIsoDiscrete`, whose inverse
component is `functorIsoDiscreteComponents`, and that comparison is
`discrete.map (LCZauxHom ℤ) ≫ counit`; `LCZauxHom ℤ` is the unit of the locally constant
adjunction (whose value on `1` is the constant function `1`, `LCZ_unit_const`). -/
private theorem ZisoLCZ_hom_unitConstSheaf_local :
    ConcreteCategory.hom ((Work.ANALYTIC.ZisoLCZ.hom).hom.app (Opposite.op Work.ATOM.pt))
      ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app (ModuleCat.of ℤ ℤ)
        (1 : ℤ))
    = Work.ATOM.ZS.Unred.oneLCZ := by
  have h1 : Work.ATOM.ZS.Unred.LCZauxHom (ModuleCat.of ℤ ℤ)
      = (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app (ModuleCat.of ℤ ℤ)
        ≫ (LightCondensed.underlying (ModuleCat ℤ)).map (Work.ANALYTIC.ZisoLCZ.hom) := by
    rw [← Work.ATOM.ZS.Unred.LCZ_unit_eq_auxHom]
    exact Work.ATOM.ZS.Unred.ofNatIsoLeft_unit_app (LightCondensed.discreteUnderlyingAdj
      (ModuleCat ℤ)) ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).symm)
      (ModuleCat.of ℤ ℤ)
  have h2 : ConcreteCategory.hom (Work.ATOM.ZS.Unred.LCZauxHom (ModuleCat.of ℤ ℤ)) (1 : ℤ)
      = ConcreteCategory.hom ((Work.ANALYTIC.ZisoLCZ.hom).hom.app (Opposite.op Work.ATOM.pt))
          ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app (ModuleCat.of ℤ ℤ)
            (1 : ℤ)) := by
    rw [h1]; rfl
  rw [← h2, ← Work.ATOM.ZS.Unred.LCZ_unit_eq_auxHom]
  exact Work.ATOM.ZS.Unred.LCZ_unit_const (ModuleCat.of ℤ ℤ) 1

set_option backward.isDefEq.respectTransparency false in
theorem LCZhom_eq_unit :
    Work.ATOM.ZS.Unred.LCZhom =
      CategoryTheory.CategoryStruct.comp Work.ATOM.unitIso.inv
        Work.ANALYTIC.CechPt.lcDiscIntIso.inv := by
  apply (Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ATOM.ZS.Unred.LCZ).injective
  rw [Work.ATOM.ZS.Unred.homFreeEquiv_LCZhom]
  erw [Work.ATOM.ZS.Unred.homFreeEquiv_comp]
  erw [homFreeEquiv_unitIso_inv_aux]
  exact ZisoLCZ_hom_unitConstSheaf_local.symm

end Work.ANALYTIC.CechPt

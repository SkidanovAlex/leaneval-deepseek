import Mathlib
import Submission.Work.ANALYTIC.CechPt.CoordDefs
import Submission.Work.ANALYTIC.CechPt.sd_zf_iso_Cdisc
import Submission.Work.ANALYTIC.HaarBasisMain
import Submission.Work.ANALYTIC.disc_finsupp_iso_coprod
import Submission.Work.ANALYTIC.pi_option_iso_biprod
import Submission.Work.ANALYTIC.ihom_coprod_iso
import Submission.Work.REFL.pre_app_points

/-!
# Auxiliary definitions for `ddZf_iso_prod`

This module fixes the vocabulary used by
`Submission/Work/ANALYTIC/CechPt/ddZf_iso_prod.lean`.

We work with `X = zf T = ℤ[T]` for an infinite light profinite set `T`, and with

* `sd X = (X ⟹ 𝟙)` (the single dual) and `dd X = sd (sd X)` (the double dual);
* `phiOf X lam = curry (ρ_X ≫ lam) : 𝟙 ⟶ sd X`, the global section of `sd X` attached to a
  functional `lam : X ⟶ 𝟙`; `coordMap X lam` is by definition `pre (phiOf X lam) ≫ unitIsoSelf`, so
  `coordMap X lam` is *evaluation of a double dual element at `phiOf X lam`*;
* `lamHat T lam ∈ LC T = LocallyConstant ↥T ℤ`, the locally constant function attached to `lam`
  under the canonical identification `sd (zf T) ≅ Cdisc T = lcDisc (LC T)`.  Concretely
  `lamHat T lam = homFreeEquiv T LCZ (lam ≫ ZisoLCZ.hom)`, i.e. `lam` transported to the
  `LCZ`-model `lcDisc ℤ` of `ℤ` (whose sections are *definitionally* locally constant functions);
* `phiT T : sd (zf T) ≅ Cdisc T`, the canonical isomorphism of
  `Submission/Work/ANALYTIC/CechPt/sd_zf_iso_Cdisc.lean` (with the `𝟙 ≅ lcDisc ℤ` transport made
  explicit so that its components can be computed);
* `dualElement T j`, `j : Haar.JIdx = ℕ ∪ {∞}`, the two families `lamJ T j` (`j : ℕ`) and
  `lamInf T` of dual elements;
* `ddProjMap T : dd (zf T) ⟶ ∏_{Haar.JIdx} 𝟙`, the comparison whose `j`-th coordinate is
  `coordMap (zf T) (dualElement T j)`.

## The two mathematical inputs

**(a) `phiT` is the evaluation pairing.**  For every light profinite `U` and every functional
`lam : zf T ⟶ 𝟙`, the `U`-points of `sd (zf T)` are `C(T × U, ℤ)` (`Work.DISC.sdPhi`) and the
`U`-points of `Cdisc T = lcDisc (LC T)` are the locally constant functions `U → C(T,ℤ)`
(`lcCurryEquiv`), and the comparison `sdComp T ℤ U` of `sd_zf_iso_Cdisc.lean` is *currying*.  Hence
at the point `U = *` the canonical isomorphism sends the section `phiOf (zf T) lam` to `lamHat T lam`
(see `gamma_phiT` below).

**(b) The dual elements are the Haar basis elements.**  `lamHat T (lamJ T j) = Haar.fCyl T j`
(from the pointwise description `kappaLCZ_pt` of `kappaLCZ`) and `lamHat T (lamInf T) = 1`
(from `aug = zmap (toPt T)` and the fact that `unitIso.inv ≫ ZisoLCZ.hom : zf * ⟶ lcDisc ℤ`
carries the canonical generator `e₁` to the constant function `1`).

Given (a), (b) and the Haar/Schauder basis `haar_basisIso`, the family `(phiOf (zf T) (dualElement T j))_j`
exhibits `sd (zf T)` as the coproduct `∐_{j} 𝟙`, and `ddProjMap T` is (the transpose of) the
canonical isomorphism `Hom(∐_j 𝟙, 𝟙) ≅ ∏_j 𝟙`.

## Route hints for the two hard lemmas

**`gamma_phiT`** (`toPointEquiv (Cdisc T) (phiOf (zf T) lam ≫ (phiT T).hom) = const (lamHat T lam)`):

1. `Work.ATOM.toPointEquiv Y u = homFreeEquiv * Y (unitIso.inv ≫ u)` (definitional);
2. naturality of `homFreeEquiv` in the target, and `phiT_hom`, reduce the claim to the component at
   `U = *` of `sdIsoHom T ℤ = sdNatTrans T ℤ` (transported through
   `(sheafToPresheaf _ _).map (sdIsoHom T ℤ) = sdNatTrans T ℤ`, from `Functor.map_preimage`), whose
   section map at `U` is `sdComp T ℤ U` (`sdComp_apply`/`sdPhi_apply`);
3. `sdPhi M T U g = homFreeEquiv (T ⊗ U) (lcDisc M) ((freeTensorIso T U).inv ≫ uncurry g)` and
   `homFreeEquiv_eq_eval` evaluate at the generic element `unitElem (T ⊗ U)`;
4. for `U = *` use the isomorphism `eT := (ρ_ T).inv : T ⟶ T ⊗ *` and `homFreeEquiv_naturality` to
   replace `T ⊗ *` by `T`: the key coherence is the *unitality* of the monoidal functor
   `zfree = lightProfiniteToLightCondSet ⋙ free ℤ`, i.e.
   `CoreMonoidal.right_unitality (F := zfree) T`:
   `(ρ_ (zf T)).hom = (zf T ◁ εIso.hom) ≫ (zfreeTensorIso T *).hom ≫ zmap ((ρ_ T).hom)`
   (note `εIso` of this composite functor is `unitIso`); its inverse gives
   `zmap ((ρ_ T).inv) ≫ (zfreeTensorIso T *).inv = (ρ_ (zf T)).inv ≫ (zf T ◁ unitIso.inv)`;
5. unitor/braiding bookkeeping then turns the result into
   `homFreeEquiv T (lcDisc ℤ) (lam ≫ lcDiscIntIso.inv)`, which is `lamHat T lam`
   (`lamHat_eq` and `lcDiscIntIso_inv_eq_ZisoLCZ_hom`).

**`lamHat_lamInf`** (`lamHat T (lamInf T) = 1`):

`lamInf T = aug T ≫ unitIso.inv = zmap (toPt T) ≫ unitIso.inv`.  Apply `zmap_ptAt_comp_aug`
(`zmap (ptAt t) ≫ aug T = 𝟙 (zfree *)`) and the pointwise criterion for sections of `LCZ`
(`LCZcoe_map_apply`, `homFreeEquiv_naturality`): all values of `lamHat T (lamInf T)` are equal to
`homFreeEquiv * (lcDisc ℤ) (unitIso.inv ≫ lcDiscIntIso.inv)`, so it suffices to prove that this
element of `lcDisc ℤ (*)` is `oneLCZ`.  Equivalently (`LCZ_iso.lean`:
`LCZhom = (homFreeEquiv * LCZ).symm oneLCZ` and `homFreeEquiv` is injective on `zfree * ⟶ LCZ`),
it suffices to show `unitIso.inv ≫ lcDiscIntIso.inv = LCZhom`, i.e. that
`unitIso.inv ≫ ZisoLCZ.hom : zfree * ⟶ lcDisc ℤ` carries the canonical generator `e₁`
(`homFreeEquiv * (zfree *) 𝟙`) to `oneLCZ`.  The same style of argument as in
`Submission/Work/ATOM/ZS/Unred/LCZ_iso.lean` (`unit_app_eq_aux₁`, which uses the triangle identity
of `discreteUnderlyingAdj`) is relevant here.

**`lamHat_lamJ`** is easier: `lamJ T n = kappaLCZ T n ≫ ZisoLCZ.inv`, so
`lamHat T (lamJ T n) = LCZcoe T (homFreeEquiv T (lcDisc ℤ) (kappaLCZ T n))`; prove this equals
`Haar.fCyl T n` by `LocallyConstant.ext` on `t : ↥T`, using `LCZcoe_map_apply`,
`homFreeEquiv_naturality`, `kappaLCZ_pt`, `homFreeEquiv_smul_LCZisoPt` and
`LCZcoe_smul_oneLCZ_val`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ANALYTIC.CechPt

/-- The global section `𝟙 ⟶ sd X` of the single dual attached to a functional `lam : X ⟶ 𝟙`. -/
noncomputable def phiOf (X : LightCondAb) (lam : X ⟶ 𝟙_ LightCondAb) :
    𝟙_ LightCondAb ⟶ sd X :=
  MonoidalClosed.curry ((ρ_ X).hom ≫ lam)

/-- **The locally constant function attached to a functional.**  A functional `lam : ℤ[T] ⟶ 𝟙` is
transported to the `LCZ`-model `lcDisc ℤ` of `ℤ` (via `ZisoLCZ.hom`), where its value at a light
profinite set is *definitionally* a locally constant `ℤ`-valued function. -/
noncomputable def lamHat (T : LightProfinite.{0}) (lam : zf T ⟶ 𝟙_ LightCondAb) :
    Haar.LC T :=
  Work.ANALYTIC.LCZcoe T
    (Work.ATOM.homFreeEquiv T Work.ATOM.ZS.Unred.LCZ (lam ≫ Work.ANALYTIC.ZisoLCZ.hom))

/-- Note: `lcDiscIntIso.inv` and `ZisoLCZ.hom` are the *same* morphism `𝟙 ⟶ lcDisc ℤ`
(both are the inverse of `(functorIsoDiscrete ℤ).app ℤ`). -/
theorem lcDiscIntIso_inv_eq_ZisoLCZ_hom :
    lcDiscIntIso.inv = (Work.ANALYTIC.ZisoLCZ.hom : (𝟙_ LightCondAb) ⟶
      Work.ATOM.ZS.Unred.LCZ) := rfl

theorem lamHat_eq (T : LightProfinite.{0}) (lam : zf T ⟶ 𝟙_ LightCondAb) :
    lamHat T lam =
      Work.ANALYTIC.LCZcoe T
        (Work.ATOM.homFreeEquiv T Work.ATOM.ZS.Unred.LCZ
          (lam ≫ lcDiscIntIso.inv)) := rfl

/-- **The canonical isomorphism `sd (ℤ[T]) ≅ Cdisc T`.**  This is the isomorphism of
`Submission/Work/ANALYTIC/CechPt/sd_zf_iso_Cdisc.lean` (`sdIsoHom`), preceded by the transport
`𝟙 ≅ lcDisc ℤ` so that the source is literally `sd (zf T) = (zf T ⟹ 𝟙)`. -/
noncomputable def phiT (T : LightProfinite.{0}) :
    sd (zf T) ≅ Work.ANALYTIC.Cdisc T :=
  (CategoryTheory.ihom (zf T)).mapIso lcDiscIntIso.symm ≪≫
    @asIso _ _ _ _ (sdIsoHom T (ModuleCat.of ℤ ℤ)) (sdIsoHom_isIso T (ModuleCat.of ℤ ℤ))

/-- The morphism underlying `phiT`: the transport `(zf T ⟹ 𝟙) ⟶ (zf T ⟹ lcDisc ℤ)` followed by
the sectionwise comparison `sdIsoHom`. -/
theorem phiT_hom (T : LightProfinite.{0}) :
    (phiT T).hom =
      (CategoryTheory.ihom (zf T)).map lcDiscIntIso.inv ≫
        sdIsoHom T (ModuleCat.of ℤ ℤ) := rfl

/-- The `j`-th dual element of `ℤ[T]`, `j : Haar.JIdx = ℕ ∪ {∞}`: `lamJ T j` for `j : ℕ` and
`lamInf T` for the index `∞`. -/
noncomputable def dualElement (T : LightProfinite.{0}) [Infinite T] :
    Haar.JIdx → (zf T ⟶ 𝟙_ LightCondAb) :=
  fun j => j.elim (lamInf T) (fun n => lamJ T n)

@[simp]
theorem dualElement_infty (T : LightProfinite.{0}) [Infinite T] :
    dualElement T Haar.inf = lamInf T := rfl

@[simp]
theorem dualElement_coe (T : LightProfinite.{0}) [Infinite T] (n : ℕ) :
    dualElement T (n : Haar.JIdx) = lamJ T n := rfl

/-- **The comparison map** `dd (ℤ[T]) ⟶ ∏_{j : JIdx} 𝟙` whose `j`-th coordinate is the coordinate
map of the `j`-th dual element.  This is the map whose being an isomorphism is the content of
`ddZf_iso_prod`. -/
noncomputable def ddProjMap (T : LightProfinite.{0}) [Infinite T] :
    dd (zf T) ⟶ ∏ᶜ (fun _ : Haar.JIdx => Z) :=
  Pi.lift (fun j => coordMap (zf T) (dualElement T j))

@[simp]
theorem ddProjMap_π (T : LightProfinite.{0}) [Infinite T] (j : Haar.JIdx) :
    ddProjMap T ≫ Pi.π (fun _ : Haar.JIdx => Z) j =
      coordMap (zf T) (dualElement T j) :=
  Limits.Pi.lift_comp_π _ _

/-- The coordinate map is evaluation at `phiOf`: this is the definition of `coordMap` together
with the definition of `phiOf`. -/
theorem coordMap_eq_pre_phiOf (X : LightCondAb) (lam : X ⟶ 𝟙_ LightCondAb) :
    coordMap X lam =
      (MonoidalClosed.pre (phiOf X lam)).app (𝟙_ LightCondAb) ≫
        (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom := rfl

/-- Evaluation at the unique point of `Cdisc T(U)` for `U = *`. -/
def evPt (T : LightProfinite.{0}) :
    (Work.ANALYTIC.Cdisc T).obj.obj (Opposite.op Work.ATOM.pt) → Haar.LC T :=
  fun f => (show LocallyConstant ↥(Work.ATOM.pt.toTop) (Haar.LC T) from f) PUnit.unit

theorem evPt_apply (T : LightProfinite.{0})
    (f : (Work.ANALYTIC.Cdisc T).obj.obj (Opposite.op Work.ATOM.pt)) :
    evPt T f = (show LocallyConstant ↥(Work.ATOM.pt.toTop) (Haar.LC T) from f) PUnit.unit := rfl

@[simp]
theorem evPt_const (T : LightProfinite.{0}) (f : Haar.LC T) :
    evPt T (LocallyConstant.const ↥(Work.ATOM.pt.toTop) f) = f := rfl

end Work.ANALYTIC.CechPt

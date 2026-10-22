import Mathlib
import Submission.Work.ANALYTIC.CechPt.DdZfAux
import Submission.Work.ANALYTIC.CechPt.LCZhom_eq_unit

/-!
# The coherence `homFreeEquiv ∗ unitIso.inv = (discrete ⊣ underlying).unit ℤ 1`

Both sides are the canonical generator of the sections over the point of the constant sheaf `ℤ`:

* on the left, `homFreeEquiv ∗ Z` evaluates a morphism `ℤ[∗] ⟶ ℤ` at the canonical generator of
  `ℤ[∗](∗)`, and `unitIso.inv : ℤ[∗] ⟶ 𝟙` is the monoidal-unit comparison of the free functor;
* on the right, `(discreteUnderlyingAdj ℤ).unit.app ℤ 1` is the unit of the constant-sheaf
  adjunction `discrete ℤ ⊣ underlying ℤ = (-)(∗)` at `1 : ℤ`.

The mathematical content is the coherence between the two trivialisations of the constant sheaf
`ℤ`: the morphism `LCZhom : ℤ[∗] ⟶ LCZ = C(−,ℤ)` carrying the canonical generator to the constant
function `1` is the composite of `unitIso.inv` with the locally-constant-model comparison
`lcDiscIntIso.inv`, i.e. `Work.ANALYTIC.CechPt.LCZhom_eq_unit`, proved in
`Submission/Work/ANALYTIC/CechPt/LCZhom_eq_unit.lean`.

Given that, the proof below is bookkeeping.  Writing `ℓ = lcDiscIntIso.inv : Z ⟶ LCZ` and
`y = (discreteUnderlyingAdj ℤ).unit.app ℤ 1 : Z(∗)`:

* both `unitIso.inv` and the classifying morphism `ψ = (homFreeEquiv ∗ Z).symm y` of `y` become
  `LCZhom` after composition with `ℓ` (the first by `LCZhom_eq_unit`, the second because the
  section of `LCZ` they classify is `oneLCZ` in both cases, `LCZhom_eq_unit` and
  `lcDiscIntIso_inv_unitConstSheaf` below);
* hence they are equal by cancellation with the isomorphism `ℓ`;
* and evaluating `ψ` at the canonical generator gives back `y` (`Equiv.apply_symm_apply`).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed
open Opposite

noncomputable section

namespace Work.ANALYTIC.CechPt

set_option backward.isDefEq.respectTransparency false in
/-- **The generator of `Z(∗)` in the locally constant model.**  The section map at `∗` of
`lcDiscIntIso.inv = ZisoLCZ.hom : Z ⟶ LCZ` carries the unit of the constant-sheaf adjunction at
`1 : ℤ` — the canonical generator of `Z(∗)` — to the constant function `1`.

Indeed that comparison is the inverse component of `functorIsoDiscrete ℤ`, which is
`discrete.map (LCZauxHom ℤ) ≫ counit`, and `LCZauxHom ℤ` is the unit of the locally constant
adjunction, whose value on `1` is the constant function `1`
(`Work.ATOM.ZS.Unred.LCZ_unit_const`). -/
theorem lcDiscIntIso_inv_unitConstSheaf :
    (ConcreteCategory.hom ((lcDiscIntIso.inv).hom.app (Opposite.op Work.ATOM.pt)))
      ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app (ModuleCat.of ℤ ℤ) (1 : ℤ))
    = Work.ATOM.ZS.Unred.oneLCZ := by
  have h1 : Work.ATOM.ZS.Unred.LCZauxHom (ModuleCat.of ℤ ℤ)
      = (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app (ModuleCat.of ℤ ℤ)
        ≫ (LightCondensed.underlying (ModuleCat ℤ)).map
            (lcDiscIntIso.inv : Work.ANALYTIC.Z ⟶ Work.ATOM.ZS.Unred.LCZ) := by
    rw [← Work.ATOM.ZS.Unred.LCZ_unit_eq_auxHom]
    exact Work.ATOM.ZS.Unred.ofNatIsoLeft_unit_app (LightCondensed.discreteUnderlyingAdj
      (ModuleCat ℤ)) ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).symm)
      (ModuleCat.of ℤ ℤ)
  have h2 : (ConcreteCategory.hom (Work.ATOM.ZS.Unred.LCZauxHom (ModuleCat.of ℤ ℤ))) (1 : ℤ)
      = (ConcreteCategory.hom ((lcDiscIntIso.inv).hom.app (Opposite.op Work.ATOM.pt)))
          ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app (ModuleCat.of ℤ ℤ)
            (1 : ℤ)) := by
    rw [h1]
    rfl
  have h3 : (ConcreteCategory.hom (Work.ATOM.ZS.Unred.LCZauxHom (ModuleCat.of ℤ ℤ))) (1 : ℤ)
      = Work.ATOM.ZS.Unred.oneLCZ :=
    (congrArg (fun f => (ConcreteCategory.hom f) (1 : ℤ))
      (Work.ATOM.ZS.Unred.LCZ_unit_eq_auxHom (ModuleCat.of ℤ ℤ))).symm.trans
      (Work.ATOM.ZS.Unred.LCZ_unit_const (ModuleCat.of ℤ ℤ) 1)
  exact h2.symm.trans h3

theorem homFreeEquiv_unitIso_inv :
    Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ANALYTIC.Z Work.ATOM.unitIso.inv
      = (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app (ModuleCat.of ℤ ℤ)
          (1 : ℤ) := by
  -- the element on the right-hand side, as the section of `Z` over `∗` that it classifies
  have hsymm : Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ANALYTIC.Z
      ((Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ANALYTIC.Z).symm
        ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app (ModuleCat.of ℤ ℤ)
          (1 : ℤ)))
      = (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app (ModuleCat.of ℤ ℤ)
          (1 : ℤ) :=
    Equiv.apply_symm_apply _ _
  -- the section of `LCZ` over `∗` classified by the classifying morphism of the right-hand side
  have hψ : Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ATOM.ZS.Unred.LCZ
      (((Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ANALYTIC.Z).symm
        ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app (ModuleCat.of ℤ ℤ)
          (1 : ℤ))) ≫ lcDiscIntIso.inv) = Work.ATOM.ZS.Unred.oneLCZ :=
    (Work.ATOM.ZS.Unred.homFreeEquiv_comp
        ((Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ANALYTIC.Z).symm
          ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app (ModuleCat.of ℤ ℤ)
            (1 : ℤ)))
        lcDiscIntIso.inv).trans
      ((congrArg (fun z => (ConcreteCategory.hom (lcDiscIntIso.inv.hom.app
          (Opposite.op Work.ATOM.pt))) z) hsymm).trans lcDiscIntIso_inv_unitConstSheaf)
  -- both morphisms agree after composition with the isomorphism `lcDiscIntIso.inv`
  have hcomp : ((Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ANALYTIC.Z).symm
        ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app (ModuleCat.of ℤ ℤ)
          (1 : ℤ))) ≫ lcDiscIntIso.inv = Work.ATOM.ZS.Unred.LCZhom :=
    (Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ATOM.ZS.Unred.LCZ).injective
      (hψ.trans (Work.ATOM.ZS.Unred.homFreeEquiv_LCZhom).symm)
  have hunit : Work.ATOM.unitIso.inv
      = (Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ANALYTIC.Z).symm
          ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app (ModuleCat.of ℤ ℤ)
            (1 : ℤ)) :=
    (cancel_mono lcDiscIntIso.inv).mp (LCZhom_eq_unit.symm.trans hcomp.symm)
  exact (congrArg (fun φ => Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ANALYTIC.Z φ)
    hunit).trans hsymm

end Work.ANALYTIC.CechPt

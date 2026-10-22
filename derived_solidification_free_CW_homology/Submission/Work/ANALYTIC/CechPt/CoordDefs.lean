import Mathlib
import Submission.Work.ANALYTIC.CechPt.DoubleDual
import Submission.Work.ANALYTIC.kTildeDefs
import Submission.Work.ANALYTIC.MuT
import Submission.Work.ANALYTIC.HaarDefs
import Submission.Work.ATOM.Main

/-!
# Coordinates of the canonical double-dual unit of `ℤ[T]`

This module fixes the vocabulary used by
`Submission/Work/ANALYTIC/CechPt/doubleDualUnit_solidEquiv.lean`.

The canonical double-dual unit `u = doubleDualUnit X : X ⟶ ((X ⟹ 𝟙) ⟹ 𝟙)` is the evaluation
pairing; a "dual element" `λ : X ⟶ 𝟙` (i.e. a functional) gives a *coordinate map*

`coordMap X λ : ((X ⟹ 𝟙) ⟹ 𝟙) ⟶ 𝟙`

(transpose of `λ` along the internal-hom adjunction, followed by the evaluation
`(𝟙 ⟹ 𝟙) ≅ 𝟙`), and `doubleDualUnit_coord` records the defining property of the unit:

`doubleDualUnit X ≫ coordMap X λ = λ`.

For `X = ℤ[T]` the elements `λ` that matter are the Haar basis elements `fJ T j` of
`C(T,ℤ) = Hom(ℤ[T], 𝟙)`, together with the constant function `1`:
* `lamInf T` is the functional corresponding to the constant function `1`;
* `lamJ T j` is the functional corresponding to `fJ T j = fCyl T j` (`j : ℕ`).

Finally `kMap T : ℤ̃[T] ⟶ ∏_ℕ ℤ` is the "Haar coordinate" map on the reduced object
`ℤ̃[T] = coker (ℤ[pt] → ℤ[T])` (the `j`-th coordinate is the descent of `λ_j`), whose
solid-equivalence is the content of AN3 (`Work.ANALYTIC.exists_kTilde`).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ANALYTIC.CechPt

/-- **The coordinate map of the double dual of `X` attached to a dual element `λ`.** -/
noncomputable def coordMap (X : LightCondAb) (lam : X ⟶ 𝟙_ LightCondAb) :
    dd X ⟶ 𝟙_ LightCondAb :=
  (MonoidalClosed.pre (MonoidalClosed.curry ((ρ_ X).hom ≫ lam))).app (𝟙_ LightCondAb) ≫
    (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom

/-! ## The currying computation: the coordinates of the double-dual unit -/

/-- **The unit of the internal hom `𝟙 ⟹ X` is the identity.** -/
lemma uncurry_unitNatIso (Z : LightCondAb) :
    MonoidalClosed.uncurry ((MonoidalClosed.unitNatIso.app Z).hom) = (λ_ Z).hom := by
  change MonoidalClosed.uncurry (((conjugateEquiv Adjunction.id (ihom.adjunction (𝟙_ LightCondAb)))
    (leftUnitorNatIso LightCondAb).hom).app Z) = _
  rw [conjugateEquiv_apply_app]
  simp only [Adjunction.id_counit, NatTrans.id_app, Functor.comp_obj, Functor.id_obj,
    leftUnitorNatIso_hom_app]
  have hm : (ihom (𝟙_ LightCondAb)).map (𝟙 Z) = 𝟙 ((ihom (𝟙_ LightCondAb)).obj Z) :=
    CategoryTheory.Functor.map_id _ _
  rw [hm, Category.comp_id, MonoidalClosed.uncurry_natural_right]
  have hη : MonoidalClosed.uncurry ((ihom.adjunction (𝟙_ LightCondAb)).unit.app Z) =
      𝟙 (𝟙_ LightCondAb ⊗ Z) := by
    have h : (ihom.adjunction (𝟙_ LightCondAb)).unit.app Z =
        (ihom.adjunction (𝟙_ LightCondAb)).homEquiv Z (𝟙_ LightCondAb ⊗ Z) (𝟙 _) := by
      rw [Adjunction.homEquiv_unit]
      simp
    rw [h]
    exact MonoidalClosed.uncurry_curry _
  rw [hη, Category.id_comp]

/-- Evaluating a curried map at the unit: `curry h ≫ (unitIsoSelf Z).hom = (λ_ X).inv ≫ h`
for `h : 𝟙 ⊗ X ⟶ Z`. -/
lemma curry_unitIsoSelf (X Z : LightCondAb) (h : 𝟙_ LightCondAb ⊗ X ⟶ Z) :
    MonoidalClosed.curry h ≫ (MonoidalClosed.unitIsoSelf Z).hom = (λ_ X).inv ≫ h := by
  have key : ∀ (g : X ⟶ Z), MonoidalClosed.curry ((λ_ X).hom ≫ g) =
      g ≫ (MonoidalClosed.unitNatIso.app Z).hom := by
    intro g
    rw [← MonoidalCategory.leftUnitor_naturality (f := g), MonoidalClosed.curry_natural_left]
    congr 1
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_curry, uncurry_unitNatIso]
  have h2 : curry h = ((λ_ X).inv ≫ h) ≫ (unitNatIso.app Z).hom := by
    have := key ((λ_ X).inv ≫ h)
    rwa [Iso.hom_inv_id_assoc] at this
  rw [h2, MonoidalClosed.unitIsoSelf, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The coordinates of the canonical double-dual unit.**  For every dual element
`λ : X ⟶ 𝟙`, the composite of the canonical unit `doubleDualUnit X` with the coordinate map
`coordMap X λ` is `λ` itself. -/
theorem doubleDualUnit_coord (X : LightCondAb) (lam : X ⟶ 𝟙_ LightCondAb) :
    doubleDualUnit X ≫ coordMap X lam = lam := by
  set φ : 𝟙_ LightCondAb ⟶ (ihom X).obj (𝟙_ LightCondAb) :=
    MonoidalClosed.curry ((ρ_ X).hom ≫ lam) with hφ
  have hstep : MonoidalClosed.curry ((β_ (sd X) X).hom ≫ (ihom.ev X).app (𝟙_ LightCondAb)) ≫
      (MonoidalClosed.pre φ).app (𝟙_ LightCondAb) =
      MonoidalClosed.curry (φ ▷ X ≫ ((β_ (sd X) X).hom ≫ (ihom.ev X).app (𝟙_ LightCondAb))) :=
    MonoidalClosed.curry_pre_app _ _
  rw [coordMap]
  calc doubleDualUnit X ≫ (MonoidalClosed.pre φ).app (𝟙_ LightCondAb) ≫
        (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom
      = MonoidalClosed.curry ((β_ (sd X) X).hom ≫ (ihom.ev X).app (𝟙_ LightCondAb)) ≫
          (MonoidalClosed.pre φ).app (𝟙_ LightCondAb) ≫
          (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom := by rw [doubleDualUnit]
    _ = MonoidalClosed.curry (φ ▷ X ≫ ((β_ (sd X) X).hom ≫ (ihom.ev X).app (𝟙_ LightCondAb))) ≫
          (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom := by
        rw [← Category.assoc, hstep]
    _ = (λ_ X).inv ≫ (φ ▷ X ≫ ((β_ (sd X) X).hom ≫ (ihom.ev X).app (𝟙_ LightCondAb))) :=
        curry_unitIsoSelf _ _ _
    _ = lam := by
        rw [BraidedCategory.braiding_naturality_left_assoc]
        rw [← MonoidalClosed.uncurry_eq]
        rw [hφ, MonoidalClosed.uncurry_curry]
        have hcoh : (λ_ X).inv ≫ (β_ (𝟙_ LightCondAb) X).hom ≫ (ρ_ X).hom = 𝟙 X := by simp
        calc (λ_ X).inv ≫ (β_ (𝟙_ LightCondAb) X).hom ≫ (ρ_ X).hom ≫ lam
            = ((λ_ X).inv ≫ (β_ (𝟙_ LightCondAb) X).hom ≫ (ρ_ X).hom) ≫ lam := by
              simp only [Category.assoc]
          _ = 𝟙 X ≫ lam := by rw [hcoh]
          _ = lam := by simp

/-! ## The dual elements used in the Haar basis -/

/-- **The dual element corresponding to the constant function `1`.** -/
noncomputable def lamInf (T : LightProfinite.{0}) : zf T ⟶ 𝟙_ LightCondAb :=
  Work.ATOM.aug T ≫ Work.ATOM.unitIso.inv

/-- **The dual element corresponding to the Haar basis vector `fJ T j`, `j : ℕ`.** -/
noncomputable def lamJ (T : LightProfinite.{0}) [Infinite T] (j : ℕ) :
    zf T ⟶ 𝟙_ LightCondAb :=
  Work.ANALYTIC.kappaLCZ T j ≫ Work.ANALYTIC.ZisoLCZ.inv

/-- **The Haar coordinate map on the reduced object.**  Its `j`-th coordinate is the descent of
`lamJ T j` to `ℤ̃[T] = coker (ℤ[pt] → ℤ[T])`; this is the map whose solid-equivalence is the
content of AN3 (`Work.ANALYTIC.exists_kTilde`). -/
noncomputable def kMap (T : LightProfinite.{0}) [Infinite T] :
    Work.ATOM.zred T (Work.ATOM.levelData T).s₀ ⟶ Work.ANALYTIC.prodZ :=
  Work.ANALYTIC.kLCZ T ≫ Work.ANALYTIC.prodZisoProdLCZ.inv

end Work.ANALYTIC.CechPt

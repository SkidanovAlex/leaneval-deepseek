import Mathlib
import Submission.Work.CurveBasics.Place.exists_place_of_valuationSubring
import Submission.Work.CurveBasics.Place.Valuation

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.CurveBasics

namespace Curve.Place

noncomputable section

variable {k : Type*} [Field k] {C : Curve k}

/-- The `Spec`-map of the structure map `𝒪_{C,x} → K(C)` followed by `fromSpecStalk x` is the
generic point of `C`. -/
private lemma specMap_algebraMap_fromSpecStalk (X : Scheme) [IrreducibleSpace X] (x : X) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField))
      ≫ X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) := by
  rw [RingHom.algebraMap_toAlgebra]
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X).specializes trivial)

/-- The discrete valuation ring isomorphism between the local ring at a place and its
valuation subring of the function field. -/
private noncomputable def dvIso (Q : C.Place) :
    C.left.presheaf.stalk Q.point ≃+* Q.valuationSubring :=
  haveI := Q.instIsDiscreteValuationRing
  IsDiscreteValuationRing.equivValuationSubring (A := C.left.presheaf.stalk Q.point)
    (K := C.functionField)

/-- The isomorphism `dvIso` is compatible with the inclusions of both rings into `K(C)`. -/
private lemma dvIso_apply_coe (Q : C.Place) (a : C.left.presheaf.stalk Q.point) :
    ((dvIso Q a : Q.valuationSubring) : C.functionField)
      = algebraMap (C.left.presheaf.stalk Q.point) C.functionField a := by
  unfold Curve.Place.valuationSubring
  rw [dvIso]
  simp only [IsDiscreteValuationRing.equivValuationSubring]
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply]
  rw [RingEquiv.coe_subringCongr_apply, Subring.coe_equivMapOfInjective_apply,
    Subring.topEquiv_symm_apply_coe]

/-- The canonical lift `Spec ↥(Q.valuationSubring) ⟶ C` of the generic point of `C`,
constructed from `dvIso` and `Scheme.fromSpecStalk`. -/
private noncomputable def placeLift (Q : C.Place) : Spec ↧(Q.valuationSubring) ⟶ C.left :=
  Spec.map (CommRingCat.ofHom (dvIso Q).toRingHom) ≫ C.left.fromSpecStalk Q.point

private lemma dvIso_isLocalHom (Q : C.Place) : IsLocalHom (dvIso Q).toRingHom := by
  have := Q.instIsDiscreteValuationRing
  exact IsLocalHom.of_surjective _ (dvIso Q).surjective

/-- `placeLift` sends the closed point of `Spec ↥(Q.valuationSubring)` to `Q.point`. -/
private lemma placeLift_closedPoint (Q : C.Place) :
    placeLift Q (IsLocalRing.closedPoint (↥(Q.valuationSubring))) = Q.point := by
  haveI := dvIso_isLocalHom Q
  have hh := Equiv.apply_symm_apply (SpecToEquivOfLocalRing C.left ↧(Q.valuationSubring))
    ⟨Q.point, ⟨CommRingCat.ofHom (dvIso Q).toRingHom, dvIso_isLocalHom Q⟩⟩
  exact congrArg Sigma.fst hh

/-- `placeLift` is a lift of the generic point of `C`. -/
private lemma placeLift_fac (Q : C.Place) :
    Spec.map (CommRingCat.ofHom (algebraMap ↥(Q.valuationSubring) ↥(C.functionField)))
      ≫ placeLift Q = C.left.fromSpecStalk (genericPoint C.left) := by
  have hcomp : (algebraMap ↥(Q.valuationSubring) ↥(C.functionField)).comp (dvIso Q).toRingHom
      = algebraMap (C.left.presheaf.stalk Q.point) ↥(C.functionField) := by
    ext a
    simp only [RingHom.comp_apply]
    rw [ValuationSubring.algebraMap_apply]
    exact dvIso_apply_coe Q a
  rw [placeLift, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  exact specMap_algebraMap_fromSpecStalk C.left Q.point

/-- Transporting `dvIso Q'` along an equality of valuation subrings yields an isomorphism
`𝒪_{C,Q'} ≃ ↥(Q.valuationSubring)`. -/
private noncomputable def dvIso' (Q Q' : C.Place)
    (h : Q.valuationSubring = Q'.valuationSubring) :
    C.left.presheaf.stalk Q'.point ≃+* Q.valuationSubring :=
  (dvIso Q').trans (RingEquiv.subringCongr (congrArg ValuationSubring.toSubring h.symm))

private lemma dvIso'_apply_coe (Q Q' : C.Place) (h : Q.valuationSubring = Q'.valuationSubring)
    (a : C.left.presheaf.stalk Q'.point) :
    ((dvIso' Q Q' h a : Q.valuationSubring) : C.functionField)
      = algebraMap (C.left.presheaf.stalk Q'.point) C.functionField a := by
  rw [dvIso', RingEquiv.trans_apply]
  rw [RingEquiv.coe_subringCongr_apply]
  exact dvIso_apply_coe Q' a

/-- The lift `Spec ↥(Q.valuationSubring) ⟶ C` of the generic point of `C` built from `Q'`
and the identification of valuation subrings. -/
private noncomputable def placeLift' (Q Q' : C.Place)
    (h : Q.valuationSubring = Q'.valuationSubring) :
    Spec ↧(Q.valuationSubring) ⟶ C.left :=
  Spec.map (CommRingCat.ofHom (dvIso' Q Q' h).toRingHom) ≫ C.left.fromSpecStalk Q'.point

private lemma dvIso'_isLocalHom (Q Q' : C.Place)
    (h : Q.valuationSubring = Q'.valuationSubring) :
    IsLocalHom (dvIso' Q Q' h).toRingHom := by
  have := Q'.instIsDiscreteValuationRing
  exact IsLocalHom.of_surjective _ (dvIso' Q Q' h).surjective

private lemma placeLift'_closedPoint (Q Q' : C.Place)
    (h : Q.valuationSubring = Q'.valuationSubring) :
    placeLift' Q Q' h (IsLocalRing.closedPoint (↥(Q.valuationSubring))) = Q'.point := by
  haveI := dvIso'_isLocalHom Q Q' h
  have hh := Equiv.apply_symm_apply (SpecToEquivOfLocalRing C.left ↧(Q.valuationSubring))
    ⟨Q'.point, ⟨CommRingCat.ofHom (dvIso' Q Q' h).toRingHom, dvIso'_isLocalHom Q Q' h⟩⟩
  exact congrArg Sigma.fst hh

private lemma placeLift'_fac (Q Q' : C.Place) (h : Q.valuationSubring = Q'.valuationSubring) :
    Spec.map (CommRingCat.ofHom (algebraMap ↥(Q.valuationSubring) ↥(C.functionField)))
      ≫ placeLift' Q Q' h = C.left.fromSpecStalk (genericPoint C.left) := by
  have hcomp : (algebraMap ↥(Q.valuationSubring) ↥(C.functionField)).comp
        (dvIso' Q Q' h).toRingHom
      = algebraMap (C.left.presheaf.stalk Q'.point) ↥(C.functionField) := by
    ext a
    simp only [RingHom.comp_apply]
    rw [ValuationSubring.algebraMap_apply]
    exact dvIso'_apply_coe Q Q' h a
  rw [placeLift', ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  exact specMap_algebraMap_fromSpecStalk C.left Q'.point

end

end Curve.Place

namespace Place

open Work.CurveBasics in
/-- Two places of a curve with the same valuation subring of the function field are equal.
(Equivalently: the map sending a closed point of a curve to the corresponding valuation subring of
`K(C)` is injective.)

Intended proof: given `Q`, let `l_Q : Spec ↥(Q.valuationSubring) ⟶ C` be the composite of
`Spec.map` of the inverse of the ring isomorphism `IsDiscreteValuationRing.equivValuationSubring`
from the stalk at `Q.point` to `Q.valuationSubring` with `C.left.fromSpecStalk Q.point`.  This is a
lift of the valuative commutative square for `C.hom : C.left ⟶ Spec k` with `R := ↥(Q.valuationSubring)`
and `K := K(C)` (build the square as in `Place.exists_place_of_valuationSubring`, where the
commutativity of the square relies on `Place.fromSpecStalk_genericPoint_comp_hom`).  If
`Q.valuationSubring = Q'.valuationSubring` the two lifts `l_Q` and `l_{Q'}` are lifts of the *same*
square, so `Subsingleton.elim` (from `IsSeparated.valuativeCriterion`, using that `C` is proper
hence separated) identifies them; evaluating at the closed point of `Spec ↥(Q.valuationSubring)`
and using `Scheme.fromSpecStalk_closedPoint` (and the fact that `Spec.map` of a ring iso sends the
closed point to the closed point) gives `Q.point = Q'.point`, hence `Q = Q'`. -/
theorem place_eq_of_valuationSubring_eq {k : Type*} [Field k] (C : Curve k) {Q Q' : C.Place}
    (h : Q.valuationSubring = Q'.valuationSubring) : Q = Q' := by
  haveI : IsLocalHom (Curve.Place.dvIso Q).toRingHom := Curve.Place.dvIso_isLocalHom Q
  haveI : IsLocalHom (Curve.Place.dvIso' Q Q' h).toRingHom := Curve.Place.dvIso'_isLocalHom Q Q' h
  -- The two lifts of the generic point of `C` have the same composite with `C.hom`.
  have hcancel : Curve.Place.placeLift' Q Q' h ≫ C.hom = Curve.Place.placeLift Q ≫ C.hom := by
    obtain ⟨α, hα⟩ := Spec.map_surjective (Curve.Place.placeLift' Q Q' h ≫ C.hom)
    obtain ⟨β, hβ⟩ := Spec.map_surjective (Curve.Place.placeLift Q ≫ C.hom)
    rw [← hα, ← hβ]
    have hαβ : α = β := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro c
      exact Subtype.ext (by
        have key : Spec.map (α ≫ CommRingCat.ofHom (algebraMap ↥(Q.valuationSubring)
              ↥(C.functionField)))
            = Spec.map (β ≫ CommRingCat.ofHom (algebraMap ↥(Q.valuationSubring)
              ↥(C.functionField))) := by
          rw [Spec.map_comp, Spec.map_comp, hα, hβ, ← Category.assoc, Curve.Place.placeLift'_fac,
            ← Category.assoc, Curve.Place.placeLift_fac]
        have hkey := Spec.map_injective key
        have h2 : (α ≫ CommRingCat.ofHom (algebraMap ↥(Q.valuationSubring)
              ↥(C.functionField))).hom c
            = (β ≫ CommRingCat.ofHom (algebraMap ↥(Q.valuationSubring)
              ↥(C.functionField))).hom c :=
          DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hkey) c
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h2
        simpa only [ValuationSubring.algebraMap_apply] using h2)
    rw [hαβ]
  -- The valuative square whose two lifts are `placeLift Q` and `placeLift' Q Q' h`.
  let SQ : ValuativeCommSq C.hom :=
    { R := ↥(Q.valuationSubring)
      K := ↥(C.functionField)
      i₁ := C.left.fromSpecStalk (genericPoint C.left)
      i₂ := Curve.Place.placeLift Q ≫ C.hom
      commSq := ⟨by rw [← Category.assoc, Curve.Place.placeLift_fac]⟩ }
  have hsub : Subsingleton SQ.commSq.LiftStruct := (IsSeparated.valuativeCriterion C.hom) SQ
  have hl : Curve.Place.placeLift Q = Curve.Place.placeLift' Q Q' h := by
    have hlit : (⟨Curve.Place.placeLift Q, Curve.Place.placeLift_fac Q, rfl⟩ :
        SQ.commSq.LiftStruct) =
        ⟨Curve.Place.placeLift' Q Q' h, Curve.Place.placeLift'_fac Q Q' h, hcancel⟩ :=
      @Subsingleton.elim _ hsub _ _
    exact congrArg CommSq.LiftStruct.l hlit
  have hp : Q.point = Q'.point := by
    rw [← Curve.Place.placeLift_closedPoint Q,
      ← Curve.Place.placeLift'_closedPoint Q Q' h, hl]
  exact Subtype.ext hp

end Place

end Work.CurveBasics

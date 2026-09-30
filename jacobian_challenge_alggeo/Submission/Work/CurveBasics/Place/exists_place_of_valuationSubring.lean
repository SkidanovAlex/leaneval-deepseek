/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Places are the nontrivial valuation subrings of the function field

Let `C` be a smooth, proper, geometrically irreducible curve over a field `k` (the bundled
`Work.CurveBasics.Curve`) and let `V` be a valuation subring of `K(C)` containing `k` which is
not all of `K(C)`.  Then `V` is the subring of functions regular at a closed point of `C`;
that is, `V = Q.valuationSubring` for a place `Q` of `C`.

This is the converse direction of the dictionary between places of a curve and nontrivial
valuation subrings of its function field.  Existence of the *center* of the valuation is
supplied by the valuative criterion for the proper morphism `C ⟶ Spec k`, and its uniqueness
(so that the local ring at the center coincides with `V`) uses that the local ring of a curve
at a closed point is a discrete valuation ring.

## Main result

* `Work.CurveBasics.Place.exists_place_of_valuationSubring`
-/
import Mathlib
import Submission.Work.CurveBasics.Place.Valuation

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics

variable {k : Type u} [Field k]

/-- The generic point map `Spec K(C) ⟶ C` is a morphism over `Spec k`, for the canonical
`k`-algebra structure on the function field of `C`. -/
theorem fromSpecStalk_genericPoint_comp_hom (C : Curve k) :
    C.left.fromSpecStalk (genericPoint C.left) ≫ C.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k ↥(C.functionField))) := by
  haveI : Nonempty (⊤ : C.left.Opens) := ⟨⟨genericPoint C.left, trivial⟩⟩
  rw [← cancel_mono (Spec (CommRingCat.of k)).toSpecΓ]
  rw [Category.assoc, Scheme.toSpecΓ_naturality, ← Category.assoc,
      Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
  rw [show (Spec (CommRingCat.of k)).toSpecΓ =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).hom) from by
    rw [← Scheme.isoSpec_hom]; simp [Scheme.isoSpec_Spec]]
  rw [← Spec.map_comp]
  refine (Spec.map_injective.eq_iff).mpr ?_
  rw [show CommRingCat.ofHom (algebraMap k ↥(C.functionField)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ C.hom.appTop ≫
        C.left.germToFunctionField ⊤ from rfl]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- If every non-zero-divisor of `R` is a unit, and `K` is the fraction field of `R`, then
`R → K` is surjective: in a fraction field every element is a quotient, and if the denominator
is a unit the quotient is already in the image. -/
theorem surjective_algebraMap_of_units {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (hR : ∀ t : nonZeroDivisors R, ∃ u : R, (t : R) * u = 1) :
    Function.Surjective (algebraMap R K) := by
  intro z
  obtain ⟨x, hx⟩ := IsLocalization.surj (nonZeroDivisors R) z
  obtain ⟨s, t⟩ := x
  simp only at hx
  obtain ⟨u, hu⟩ := hR t
  refine ⟨s * u, ?_⟩
  have hu' : algebraMap R K (t : R) * algebraMap R K u = 1 := by rw [← map_mul, hu, map_one]
  calc algebraMap R K (s * u) = algebraMap R K s * algebraMap R K u := by rw [map_mul]
    _ = z * algebraMap R K (t : R) * algebraMap R K u := by rw [← hx]
    _ = z * (algebraMap R K (t : R) * algebraMap R K u) := by rw [mul_assoc]
    _ = z := by rw [hu', mul_one]

namespace Place

/-- **The compatibility of the center with the function field.**

Let `V` be a valuation subring of `K(C)` and let `l : Spec V ⟶ C` be a lift of the generic
point map `Spec K(C) ⟶ C` along `Spec V ⟶ Spec K(C)`.  Then the local ring homomorphism
`𝒪_{C,x} ⟶ V` induced by `l` at the image `x` of the closed point is compatible with the
inclusions of both rings into `K(C)`. -/
theorem stalkClosedPointTo_comp_algebraMap (C : Curve k)
    (V : ValuationSubring C.functionField) (l : Spec ↧V ⟶ C.left)
    (hl : Spec.map (CommRingCat.ofHom (algebraMap ↥V ↥(C.functionField))) ≫ l =
      C.left.fromSpecStalk (genericPoint C.left)) :
    Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap ↥V ↥(C.functionField)) =
      C.left.presheaf.stalkSpecializes ((genericPoint_spec C.left).specializes trivial) := by
  let x : C.left := l (IsLocalRing.closedPoint (CommRingCat.of ↥V))
  obtain ⟨v, hv, hxU, hsub⟩ :=
    C.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨U, hU, hUv⟩ := hv
  rw [← hUv] at hxU hsub
  have hU' : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hηU : genericPoint C.left ∈ U := by
    have h : (Set.univ ∩ (U : Set C.left)).Nonempty := by rw [Set.univ_inter]; exact ⟨x, hxU⟩
    exact ((genericPoint_spec C.left).mem_open_set_iff U.isOpen).mpr h
  have hx_ss : C.left.fromSpecStalk x = Spec.map (C.left.presheaf.germ U x hxU) ≫ hU'.fromSpec := by
    rw [← IsAffineOpen.fromSpecStalk_eq_fromSpecStalk hU' hxU]; rfl
  have hη_ss : C.left.fromSpecStalk (genericPoint C.left)
      = Spec.map (C.left.presheaf.germ U (genericPoint C.left) hηU) ≫ hU'.fromSpec := by
    rw [← IsAffineOpen.fromSpecStalk_eq_fromSpecStalk hU' hηU]; rfl
  have hl' : Spec.map (Scheme.stalkClosedPointTo l) ≫ C.left.fromSpecStalk x = l :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
  have key0 : Spec.map (Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap ↥V ↥(C.functionField)))
      ≫ C.left.fromSpecStalk x = C.left.fromSpecStalk (genericPoint C.left) := by
    rw [Spec.map_comp, Category.assoc, hl']
    exact hl
  rw [hx_ss, hη_ss] at key0
  have key2 : Spec.map (Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap ↥V ↥(C.functionField)))
      ≫ Spec.map (C.left.presheaf.germ U x hxU)
      = Spec.map (C.left.presheaf.germ U (genericPoint C.left) hηU) := by
    rw [← cancel_mono hU'.fromSpec]
    simpa only [Category.assoc] using key0
  have key3 : C.left.presheaf.germ U x hxU ≫ (Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap ↥V ↥(C.functionField)))
      = C.left.presheaf.germ U (genericPoint C.left) hηU := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    exact key2
  have key4 : C.left.presheaf.germ U x hxU ≫ CommRingCat.ofHom (algebraMap ↥(C.left.presheaf.stalk x) ↥(C.functionField))
      = C.left.presheaf.germ U (genericPoint C.left) hηU := by
    ext a
    exact Scheme.algebraMap_germ_eq_germToFunctionField C.left hxU a
  letI : Algebra Γ(C.left, U) (C.left.presheaf.stalk x) := (C.left.presheaf.germ U x hxU).hom.toAlgebra
  haveI hloc : IsLocalization.AtPrime (C.left.presheaf.stalk x) (hU'.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU'.isLocalization_stalk ⟨x, hxU⟩
  have key5 : (Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap ↥V ↥(C.functionField)))
      = CommRingCat.ofHom (algebraMap ↥(C.left.presheaf.stalk x) ↥(C.functionField)) := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (hU'.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    have h3 : (Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap ↥V ↥(C.functionField))).hom.comp (C.left.presheaf.germ U x hxU).hom
        = (C.left.presheaf.germ U (genericPoint C.left) hηU).hom := by
      ext a
      exact congrArg (fun f => f a) (congrArg CommRingCat.Hom.hom key3)
    have h4 : (CommRingCat.ofHom (algebraMap ↥(C.left.presheaf.stalk x) ↥(C.functionField))).hom.comp (C.left.presheaf.germ U x hxU).hom
        = (C.left.presheaf.germ U (genericPoint C.left) hηU).hom := by
      ext a
      exact Scheme.algebraMap_germ_eq_germToFunctionField C.left hxU a
    show (Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap ↥V ↥(C.functionField))).hom.comp (C.left.presheaf.germ U x hxU).hom
        = (CommRingCat.ofHom (algebraMap ↥(C.left.presheaf.stalk x) ↥(C.functionField))).hom.comp (C.left.presheaf.germ U x hxU).hom
    exact h3.trans h4.symm
  rw [key5]
  rfl

end Place

namespace Place

open Work.CurveBasics in
/-- Every nontrivial valuation subring of the function field of a curve containing the
constants is the subring of functions regular at a place. -/
theorem exists_place_of_valuationSubring {k : Type*} [Field k] (C : Curve k)
    (V : ValuationSubring C.functionField)
    (hV : ∀ c : k, algebraMap k C.functionField c ∈ V) (hne : V ≠ ⊤) :
    ∃ Q : C.Place, V = Q.valuationSubring := by
  have hmapk : C.left.fromSpecStalk (genericPoint C.left) ≫ C.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k ↥(C.functionField))) :=
    fromSpecStalk_genericPoint_comp_hom C
  let φ : k →+* ↥V :=
    { toFun := fun c => ⟨algebraMap k ↥(C.functionField) c, hV c⟩
      map_one' := by ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp
      map_mul' := by intro a b; ext; simp }
  have hφ : (CommRingCat.ofHom φ) ≫ (CommRingCat.ofHom (algebraMap ↥V ↥(C.functionField)))
      = CommRingCat.ofHom (algebraMap k ↥(C.functionField)) := by
    rw [← CommRingCat.ofHom_comp]
    congr 1
  have hcomm : C.left.fromSpecStalk (genericPoint C.left) ≫ C.hom =
      Spec.map (CommRingCat.ofHom (algebraMap ↥V ↥(C.functionField))) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, hφ, hmapk]
  let SQ : ValuativeCommSq C.hom :=
    { R := ↥V
      K := ↥(C.functionField)
      i₁ := C.left.fromSpecStalk (genericPoint C.left)
      i₂ := Spec.map (CommRingCat.ofHom φ)
      commSq := ⟨hcomm⟩ }
  have hcrit : ValuativeCriterion C.hom := by
    have h : IsProper C.hom := inferInstance
    rw [AlgebraicGeometry.IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  obtain ⟨l, hl₁, hl₂⟩ := (hcrit SQ).some.default
  have hcrux := Place.stalkClosedPointTo_comp_algebraMap C V l hl₁
  set x : C.left := l (IsLocalRing.closedPoint (CommRingCat.of ↥V)) with hx_def
  -- the compatibility, elementwise
  have hkey : ∀ b : C.left.presheaf.stalk x,
      algebraMap (C.left.presheaf.stalk x) ↥(C.functionField) b
        = (algebraMap ↥V ↥(C.functionField)) ((Scheme.stalkClosedPointTo l) b) := by
    intro b
    have hhom : (C.left.presheaf.stalkSpecializes ((genericPoint_spec C.left).specializes trivial)).hom
        = (algebraMap ↥V ↥(C.functionField)).comp ((Scheme.stalkClosedPointTo l).hom) := by
      rw [← congrArg CommRingCat.Hom.hom hcrux]
      rfl
    have h2 : algebraMap (C.left.presheaf.stalk x) ↥(C.functionField)
        = (C.left.presheaf.stalkSpecializes ((genericPoint_spec C.left).specializes trivial)).hom := rfl
    rw [h2, hhom]
    rfl
  have hxne : x ≠ genericPoint C.left := by
    intro hxx
    apply hne
    refine ValuationSubring.ext V ⊤ (fun a => ⟨fun _ => trivial, fun _ => ?_⟩)
    -- under `x = η`, every non-zero-divisor of the stalk is a unit
    have hR : ∀ t : nonZeroDivisors (C.left.presheaf.stalk x),
        ∃ u : C.left.presheaf.stalk x, (t : C.left.presheaf.stalk x) * u = 1 := by
      rw [hxx]
      intro t
      exact ⟨(t : ↥(C.left.presheaf.stalk (genericPoint C.left)))⁻¹,
        mul_inv_cancel₀ (nonZeroDivisors.ne_zero t.2)⟩
    obtain ⟨b, hb⟩ := surjective_algebraMap_of_units (R := C.left.presheaf.stalk x)
      (K := ↥(C.functionField)) hR a
    have ha : a = (algebraMap ↥V ↥(C.functionField)) ((Scheme.stalkClosedPointTo l) b) := by
      rw [← hb, hkey b]
    rw [ha]
    simpa using ((Scheme.stalkClosedPointTo l) b).2
  have hxclosed : IsClosed {x} := (Curve.eq_genericPoint_or_isClosed C x).resolve_left hxne
  let Q : C.Place := ⟨x, hxclosed⟩
  haveI hdvr : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) := Q.instIsDiscreteValuationRing
  have hQle : Q.valuationSubring ≤ V := by
    intro a ha
    have hQdef : Q.valuationSubring.toSubring
        = Subring.map (algebraMap (C.left.presheaf.stalk Q.point) ↥(C.functionField)) ⊤ :=
      (IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
        (A := C.left.presheaf.stalk Q.point) (K := ↥(C.functionField))).symm
    have hsub : a ∈ Subring.map (algebraMap (C.left.presheaf.stalk Q.point) ↥(C.functionField)) ⊤ := by
      rw [← hQdef]
      exact ha
    obtain ⟨b, -, rfl⟩ := hsub
    have ha' : (algebraMap (C.left.presheaf.stalk x) ↥(C.functionField)) b
        = (algebraMap ↥V ↥(C.functionField)) ((Scheme.stalkClosedPointTo l) b) := hkey b
    rw [ha']
    simpa using ((Scheme.stalkClosedPointTo l) b).2
  haveI hdvrQ : IsDiscreteValuationRing ↥(Q.valuationSubring) := by
    change IsDiscreteValuationRing
      ↥(IsDedekindDomain.HeightOneSpectrum.valuation (↥C.functionField)
        (IsDiscreteValuationRing.maximalIdeal (C.left.presheaf.stalk Q.point))).valuationSubring
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (IsDiscreteValuationRing.equivValuationSubring (A := C.left.presheaf.stalk Q.point)
        (K := ↥(C.functionField)))
  exact ⟨Q, (ValuationSubring.eq_of_le_of_ne_top Q.valuationSubring hQle hne).symm⟩

end Place

end Work.CurveBasics

import Mathlib
import Submission.Work.SpecLin.Chart.Regular
import Submission.Work.SpecLin.Chart.RegularOpensMap
import Submission.Work.SpecLin.Chart.RegularOpensAffineAux
import Submission.Work.CurveBasics.All

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TopCat
open scoped Classical

namespace Work.SpecLin.Chart

open Work.CurveBasics

universe u

variable {K : Type u} [Field K]

/-! ## Auxiliary lemmas for the core of the valuative criterion -/



private lemma ΓSpecIso_hom_eq_stalkClosedPointIso {R : CommRingCat} [IsLocalRing ↥R]
    (z : Γ(Spec R, ⊤)) :
    (Scheme.ΓSpecIso R).hom z =
      (stalkClosedPointIso R).hom ((Spec R).presheaf.germ ⊤ (IsLocalRing.closedPoint ↥R) trivial z) := by
  rw [← ConcreteCategory.comp_apply, germ_stalkClosedPointIso_hom]

private lemma topIso_inv_germ_apply {X : Scheme} (U : X.Opens) (w : U.toScheme) (s : Γ(X, U)) :
    (U.stalkIso w).hom ((U.toScheme).presheaf.germ ⊤ w trivial (U.topIso.inv s)) =
      X.presheaf.germ U (U.ι w) w.2 s := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  rw [show U.topIso.inv ≫ (U.toScheme).presheaf.germ ⊤ w trivial ≫ (U.stalkIso w).hom =
      X.presheaf.germ U (U.ι w) w.2 from by
    rw [Scheme.Opens.germ_stalkIso_hom]
    rw [show U.topIso.inv = X.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U)).op from by
      rw [Scheme.Opens.topIso_inv]]
    exact TopCat.Presheaf.germ_res X.presheaf (eqToHom (Scheme.Opens.ι_image_top U)) (U.ι w)
      (by rw [Scheme.Opens.ι_image_top]; exact w.2)]
  rfl

private lemma stalkCongr_inv_algebraMap {X : Scheme} [IrreducibleSpace X] {x y : X}
    (e : Inseparable x y) :
    (X.presheaf.stalkCongr e).inv ≫
        CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk y) X.functionField) := by
  rw [TopCat.Presheaf.stalkCongr_inv]
  simp only [RingHom.algebraMap_toAlgebra]
  rw [CommRingCat.ofHom_hom]
  exact TopCat.Presheaf.stalkSpecializes_comp (X.presheaf)
    ((genericPoint_spec X).specializes trivial) e.le

private lemma ΓSpecIso_appTop_specMap_algebraMap {R : CommRingCat} {S : Type u} [CommRing S]
    [Algebra ↥R S] (z : Γ(Spec R, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom
        ((Spec.map (CommRingCat.ofHom (algebraMap ↥R S))).appTop z) =
      algebraMap ↥R S ((Scheme.ΓSpecIso R).hom z) := by
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]
  rfl

private theorem closedPoint_mem_regularOpens' (C : Curve K) (x : C.functionField) (hx : Transcendental K x)
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {L : Type u} [Field L] [Algebra R L] [IsFractionRing R L]
    (i₁ : Spec (CommRingCat.of L) ⟶ (regularOpens C x).toScheme)
    (i₂ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Polynomial K)))
    (hw : i₁ ≫ regularOpensMap C x = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ i₂)
    (l : Spec (CommRingCat.of R) ⟶ C.left)
    (hl1 : Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ l =
      i₁ ≫ (regularOpens C x).ι) :
    l (IsLocalRing.closedPoint R) ∈ ((regularOpens C x : C.left.Opens) : Set C.left) := by
  by_contra hnot
  have hxne : x ≠ 0 := fun h0 => hx (h0 ▸ isAlgebraic_zero)
  have hpole : l (IsLocalRing.closedPoint R) ∈ poleSet C x := by
    have h1 : l (IsLocalRing.closedPoint R) ∈ ((regularOpens C x : C.left.Opens) : Set C.left)ᶜ := by
      simpa using hnot
    simpa [regularOpens] using h1
  have hclosed : IsClosed ({l (IsLocalRing.closedPoint R)} : Set C.left) := by
    rw [poleSet, Set.mem_iUnion₂] at hpole
    obtain ⟨Q, -, hQmem⟩ := hpole
    have hQ' : l (IsLocalRing.closedPoint R) = Q.point := by simpa using hQmem
    rw [hQ']; exact Q.isClosed
  set Q : C.Place := ⟨l (IsLocalRing.closedPoint R), hclosed⟩ with hQdef
  have hQord : C.ordAt x Q < 0 := by
    have hmem : Q.point ∈ poleSet C x := hpole
    rw [poleSet, Set.mem_iUnion₂] at hmem
    obtain ⟨Q', hQ'mem, hQ'pt⟩ := hmem
    have hQ'eq : Q' = Q := Subtype.ext (by simpa using (show Q'.1 = Q.1 from hQ'pt.symm))
    rw [hQ'eq] at hQ'mem
    exact hQ'mem
  have hxinvord : 0 ≤ C.ordAt x⁻¹ Q := by
    change 0 ≤ Scheme.ord x⁻¹ Q.point
    rw [Work.CurveBasics.Order.ordAt_inv C hxne Q]
    have h' : Scheme.ord x Q.point < 0 := hQord
    omega
  obtain ⟨y, hy⟩ := (BaseChange.mem_range_algebraMap_stalk_iff C Q x⁻¹).mpr hxinvord
  have hynotunit : ¬ IsUnit y := by
    intro hyu
    obtain ⟨u, hu⟩ := hyu
    have hyu' : algebraMap (C.left.presheaf.stalk Q.point) C.functionField (↑u) = x⁻¹ := by
      rw [hu]; exact hy
    have hxrange : x ∈ (algebraMap (C.left.presheaf.stalk Q.point) C.functionField).range := by
      refine ⟨(↑(u⁻¹) : C.left.presheaf.stalk Q.point), ?_⟩
      have h1 : algebraMap (C.left.presheaf.stalk Q.point) C.functionField
          (↑(u⁻¹) : C.left.presheaf.stalk Q.point) * x⁻¹ = 1 := by
        rw [← hyu', ← map_mul, ← Units.val_mul, inv_mul_cancel u, Units.val_one, map_one]
      have h4 := congrArg (fun t => t * x) h1
      simp only [mul_one, one_mul] at h4
      rwa [mul_assoc, inv_mul_cancel₀ hxne, mul_one] at h4
    exact absurd ((BaseChange.mem_range_algebraMap_stalk_iff C Q x).mp hxrange) (by omega)
  set σ : R := (Scheme.stalkClosedPointTo l).hom y with hσdef
  have hσmem : σ ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal]
    exact fun hσu => hynotunit ((Scheme.isLocalHom_stalkClosedPointTo l).map_nonunit y hσu)
  -- ===== Part 2: the value comparison =====
  set ψsch : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R L)) with hψschdef
  have hw' : i₁ ≫ regularOpensMap C x = ψsch ≫ i₂ := hw
  have hl1' : ψsch ≫ l = i₁ ≫ (regularOpens C x).ι := hl1
  set pt : Spec (CommRingCat.of L) := IsLocalRing.closedPoint L with hptdef
  set η : Spec (CommRingCat.of R) := ψsch pt with hηdef
  set cR : Spec (CommRingCat.of R) := IsLocalRing.closedPoint R with hcRdef
  have hsp : η ⤳ cR := IsLocalRing.specializes_closedPoint η
  set w : (regularOpens C x).toScheme := i₁ pt with hwdef
  have hu : l η = (regularOpens C x).ι w := by
    rw [hηdef, hwdef, ← Scheme.Hom.comp_apply, hl1', Scheme.Hom.comp_apply]
  have hγ : l η ⤳ l cR := hsp.map l.continuous
  set γ₀ : C.left.presheaf.stalk (l cR) ⟶ C.left.presheaf.stalk (l η) :=
    C.left.presheaf.stalkSpecializes hγ with hγ₀def
  set e : Inseparable (l η) ((regularOpens C x).ι w) := Inseparable.of_eq hu with hedef
  set τinv : C.left.presheaf.stalk ((regularOpens C x).ι w) ⟶ C.left.presheaf.stalk (l η) :=
    (C.left.presheaf.stalkCongr e).inv with hτinvdef
  set xw : ((regularOpens C x).toScheme).presheaf.stalk w :=
    ((regularOpens C x).toScheme).presheaf.germ ⊤ w trivial (regularOpensTopSection C x) with hxwdef
  set xu : C.left.presheaf.stalk ((regularOpens C x).ι w) :=
    C.left.presheaf.germ (regularOpens C x) ((regularOpens C x).ι w) w.2
      (regularOpensSection C x) with hxudef
  set Ψ : C.left.presheaf.stalk (l η) ⟶ CommRingCat.of L :=
    Scheme.Hom.stalkMap (ψsch ≫ l) pt ≫ (stalkClosedPointIso (CommRingCat.of L)).hom with hΨdef
  set 𝕏 : Γ(Spec (CommRingCat.of (Polynomial K)), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv Polynomial.X with h𝕏def
  set r : R := (Scheme.ΓSpecIso (CommRingCat.of R)).hom (i₂.appTop 𝕏) with hrdef
  have h_xu : (Scheme.Opens.stalkIso (regularOpens C x) w).hom xw = xu := by
    rw [hxwdef, hxudef]
    exact topIso_inv_germ_apply _ w _
  have hιx : Scheme.Hom.stalkMap (regularOpens C x).ι w xu = xw := by
    rw [← Scheme.Opens.stalkIso_inv (regularOpens C x) w, ← h_xu]
    exact Iso.hom_inv_id_apply _ xw
  have hxu_alg : (algebraMap (C.left.presheaf.stalk ((regularOpens C x).ι w))
      C.functionField) xu = x := by
    rw [hxudef, Scheme.algebraMap_germ_eq_germToFunctionField,
      germToFunctionField_regularOpensSection]
  have hF1 : γ₀ y * τinv xu = 1 := by
    apply IsFractionRing.injective (C.left.presheaf.stalk (l η)) C.functionField
    rw [map_mul, map_one]
    have h1 : (algebraMap (C.left.presheaf.stalk (l η)) C.functionField) (γ₀ y) = x⁻¹ := by
      change (γ₀ ≫ CommRingCat.ofHom
        (algebraMap (C.left.presheaf.stalk (l η)) C.functionField)) y = x⁻¹
      have hcomp : γ₀ ≫ CommRingCat.ofHom
          (algebraMap (C.left.presheaf.stalk (l η)) C.functionField) =
          CommRingCat.ofHom (algebraMap (C.left.presheaf.stalk (l cR)) C.functionField) := by
        rw [hγ₀def]
        simp only [RingHom.algebraMap_toAlgebra]
        rw [CommRingCat.ofHom_hom, CommRingCat.ofHom_hom]
        exact TopCat.Presheaf.stalkSpecializes_comp C.left.presheaf
          ((genericPoint_spec C.left).specializes trivial) hγ
      rw [hcomp]
      simpa using hy
    have h2 : (algebraMap (C.left.presheaf.stalk (l η)) C.functionField) (τinv xu) = x := by
      change (τinv ≫ CommRingCat.ofHom
        (algebraMap (C.left.presheaf.stalk (l η)) C.functionField)) xu = x
      have hcomp : τinv ≫ CommRingCat.ofHom
          (algebraMap (C.left.presheaf.stalk (l η)) C.functionField) =
          CommRingCat.ofHom (algebraMap (C.left.presheaf.stalk ((regularOpens C x).ι w))
            C.functionField) := by
        rw [hτinvdef]
        exact stalkCongr_inv_algebraMap e
      rw [hcomp]
      simpa using hxu_alg
    rw [h1, h2, inv_mul_cancel₀ hxne]
  have hE1 : (algebraMap R L) σ = Ψ (γ₀ y) := by
    have h1 : (algebraMap R L) σ =
        (Scheme.ΓSpecIso (CommRingCat.of L)).hom
          (ψsch.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv σ)) := by
      have h := ΓSpecIso_appTop_specMap_algebraMap (R := CommRingCat.of R) (S := L)
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv σ)
      rw [Iso.inv_hom_id_apply] at h
      exact h.symm
    rw [h1, ΓSpecIso_hom_eq_stalkClosedPointIso]
    have h2 : (Spec (CommRingCat.of L)).presheaf.germ ⊤ pt trivial
        (ψsch.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv σ)) =
        ψsch.stalkMap pt ((Spec (CommRingCat.of R)).presheaf.germ ⊤ η trivial
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv σ)) :=
      (Scheme.Hom.germ_stalkMap_apply ψsch ⊤ pt (by simp)
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv σ)).symm
    rw [h2]
    have h3 : (Spec (CommRingCat.of R)).presheaf.germ ⊤ η trivial
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv σ) = l.stalkMap η (γ₀ y) := by
      have hgerm : (Spec (CommRingCat.of R)).presheaf.germ ⊤ cR (by simp) ≫
            (Spec (CommRingCat.of R)).presheaf.stalkSpecializes hsp =
          (Spec (CommRingCat.of R)).presheaf.germ ⊤ η (by simp) :=
        TopCat.Presheaf.germ_stalkSpecializes ((Spec (CommRingCat.of R)).presheaf)
          (U := ⊤) (y := cR) (x := η) (by simp) hsp
      rw [← hgerm]
      have h4 : (Spec (CommRingCat.of R)).presheaf.germ ⊤ cR (by simp)
            ((Scheme.ΓSpecIso (CommRingCat.of R)).inv σ) =
          (stalkClosedPointIso (CommRingCat.of R)).inv σ := by
        rw [← ConcreteCategory.comp_apply, ← ΓSpecIso_hom_stalkClosedPointIso_inv,
          Iso.inv_hom_id_assoc]
      have h5 : (stalkClosedPointIso (CommRingCat.of R)).inv σ = l.stalkMap cR y := by
        show (stalkClosedPointIso (CommRingCat.of R)).inv
          ((Scheme.stalkClosedPointTo l).hom y) = l.stalkMap cR y
        rw [show Scheme.stalkClosedPointTo l =
            l.stalkMap (IsLocalRing.closedPoint R) ≫
              (stalkClosedPointIso (CommRingCat.of R)).hom from rfl,
          ConcreteCategory.comp_apply]
        exact Iso.hom_inv_id_apply (stalkClosedPointIso (CommRingCat.of R))
          ((l.stalkMap (IsLocalRing.closedPoint R)) y)
      have hnat : C.left.presheaf.stalkSpecializes hγ ≫ Scheme.Hom.stalkMap l η =
          Scheme.Hom.stalkMap l cR ≫ (Spec (CommRingCat.of R)).presheaf.stalkSpecializes hsp :=
        Scheme.Hom.stalkSpecializes_stalkMap l η cR hsp
      rw [ConcreteCategory.comp_apply, h4, h5, hγ₀def]
      simpa only [ConcreteCategory.comp_apply] using (ConcreteCategory.congr_hom hnat y).symm
    rw [h3, hΨdef, ConcreteCategory.comp_apply]
    congr 1
    rw [Scheme.Hom.stalkMap_comp, ConcreteCategory.comp_apply]
  have hφ : (regularOpensMap C x).appTop 𝕏 = regularOpensTopSection C x := by
    rw [h𝕏def, ← ConcreteCategory.comp_apply, ΓSpecIso_inv_comp_regularOpensMap_appTop]
    show (regularOpensCoeff C x) Polynomial.X = regularOpensTopSection C x
    rw [regularOpensCoeff]
    simp
  have hE2 : (algebraMap R L) r = Ψ (τinv xu) := by
    have h1 : (algebraMap R L) r =
        (Scheme.ΓSpecIso (CommRingCat.of L)).hom
          (ψsch.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) := by
      have h := ΓSpecIso_appTop_specMap_algebraMap (R := CommRingCat.of R) (S := L)
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
      rw [Iso.inv_hom_id_apply] at h
      exact h.symm
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv r = i₂.appTop 𝕏 := by
      rw [hrdef, Iso.hom_inv_id_apply]
    have h3 : ψsch.appTop (i₂.appTop 𝕏) = i₁.appTop (regularOpensTopSection C x) := by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop ψsch i₂, ← hw',
        Scheme.Hom.comp_appTop i₁ (regularOpensMap C x), ConcreteCategory.comp_apply, hφ]
    have h4 : (Scheme.ΓSpecIso (CommRingCat.of L)).hom (i₁.appTop (regularOpensTopSection C x)) =
        (stalkClosedPointIso (CommRingCat.of L)).hom (i₁.stalkMap pt xw) := by
      rw [ΓSpecIso_hom_eq_stalkClosedPointIso]
      congr 1
      exact (Scheme.Hom.germ_stalkMap_apply i₁ ⊤ pt (by simp)
        (regularOpensTopSection C x)).symm
    have h5 : i₁.stalkMap pt xw = (ψsch ≫ l).stalkMap pt (τinv xu) := by
      have ha : i₁.stalkMap pt xw = (i₁ ≫ (regularOpens C x).ι).stalkMap pt xu := by
        rw [← hιx, Scheme.Hom.stalkMap_comp, ConcreteCategory.comp_apply]
        rfl
      have hq : (ψsch ≫ l).stalkMap pt = (C.left.presheaf.stalkCongr e).hom ≫
          (i₁ ≫ (regularOpens C x).ι).stalkMap pt :=
        Scheme.Hom.stalkMap_congr_hom (ψsch ≫ l) (i₁ ≫ (regularOpens C x).ι) hl1' pt
      have hA : (i₁ ≫ (regularOpens C x).ι).stalkMap pt =
          τinv ≫ (ψsch ≫ l).stalkMap pt := by
        rw [hq, ← Category.assoc,
          show τinv ≫ (C.left.presheaf.stalkCongr e).hom = 𝟙 _ from hτinvdef ▸ Iso.inv_hom_id _,
          Category.id_comp]
      rw [ha, hA, ConcreteCategory.comp_apply]
      rfl
    rw [h1, h2, h3, h4, h5, hΨdef, ConcreteCategory.comp_apply]
    rfl
  have hσr : σ * r = 1 := by
    apply IsFractionRing.injective R L
    rw [map_mul, map_one, hE1, hE2, ← map_mul, hF1, map_one]
  exact (IsLocalRing.mem_maximalIdeal σ).mp hσmem
    (isUnit_iff_exists.mpr ⟨r, hσr, by rw [mul_comm, hσr]⟩)
/-- A morphism `l' : Spec R ⟶ W` whose composite with `W.ι` is a lift over `C.hom` with generic
fibre `i₁` is a lift over `regularOpensMap C x`. -/
private theorem lift_comp_regularOpensMap (C : Curve K) (x : C.functionField)
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {L : Type u} [Field L] [Algebra R L] [IsFractionRing R L]
    (i₁ : Spec (CommRingCat.of L) ⟶ (regularOpens C x).toScheme)
    (i₂ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Polynomial K)))
    (hw : i₁ ≫ regularOpensMap C x = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ i₂)
    (l' : Spec (CommRingCat.of R) ⟶ (regularOpens C x).toScheme)
    (hl'1 : Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ l' = i₁) :
    l' ≫ regularOpensMap C x = i₂ := by
  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ (l' ≫ regularOpensMap C x) =
      Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ i₂ := by
    rw [← Category.assoc, hl'1, hw]
  have h2 : Spec.preimage (l' ≫ regularOpensMap C x) ≫ CommRingCat.ofHom (algebraMap R L) =
      Spec.preimage i₂ ≫ CommRingCat.ofHom (algebraMap R L) := by
    rw [← Spec.preimage_map (CommRingCat.ofHom (algebraMap R L)),
      ← Spec.preimage_comp (Spec.map (CommRingCat.ofHom (algebraMap R L)))
        (l' ≫ regularOpensMap C x),
      ← Spec.preimage_comp (Spec.map (CommRingCat.ofHom (algebraMap R L))) i₂, hcomp]
  have h3 : Spec.preimage (l' ≫ regularOpensMap C x) = Spec.preimage i₂ := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    have h4 := RingHom.congr_fun (CommRingCat.hom_ext_iff.mp h2) a
    simp only [ConcreteCategory.comp_apply, CommRingCat.hom_ofHom] at h4
    exact IsFractionRing.injective R L h4
  have h5 := congrArg Spec.map h3
  rwa [Spec.map_preimage, Spec.map_preimage] at h5

/-! ## The valuative criterion for `regularOpensMap` -/

open CategoryTheory AlgebraicGeometry in
/-- The coordinate morphism `regularOpensMap C x : (regularOpens C x).toScheme ⟶ Spec K[X]` of a
transcendental rational function satisfies the existence part of the valuative criterion (and is
therefore universally closed, hence proper, by
`Work.SpecLin.Chart.isProper_regularOpensMap_of_valuativeCriterion`).

Proof sketch.  Let `W := regularOpens C x` and let a valuative square over
`φ := regularOpensMap C x` be given, with valuation ring `R`, fraction field `L`,
`i₁ : Spec L ⟶ W`, `i₂ : Spec R ⟶ Spec K[X]`, commuting: `i₁ ≫ φ = Spec.map (algebraMap R L) ≫ i₂`.

(1) The square over `C.hom : C.left ⟶ Spec K` with top map `i₁ ≫ W.ι` and bottom map
`i₂ ≫ Spec.map (ofHom Polynomial.C)` is commutative by `regularOpensMap_over`; by properness of
`C.hom` (`IsProper.eq_valuativeCriterion`, `ValuativeCriterion.existence`) it admits a lift
`ℓ : Spec R ⟶ C.left`, with `Spec.map (algebraMap R L) ≫ ℓ = i₁ ≫ W.ι` and
`ℓ ≫ C.hom = i₂ ≫ Spec.map (ofHom Polynomial.C)`.

(2) `ℓ ≫ φ = i₂`: by `ΓSpecIso_inv_comp_regularOpensMap_appTop` it suffices to compare the induced
ring maps `K[X] ⟶ R`; both agree after composing with `R ⟶ L` (use the given square and
`Spec.map (algebraMap R L) ≫ ℓ = i₁ ≫ W.ι`), and `R ⟶ L` is injective.

(3) `ℓ` maps the closed point of `Spec R` into `W`.  The generic point maps into `W` (it maps to
the generic point of `W`, via `i₁`).  Suppose the closed point `p` were a pole of `x`.  Every
nonempty closed subset of `Spec R` (a local ring) contains its closed point, so it suffices to
exclude this.  The stalk map `O_{C,p} → R` is local; if `ord_p x < 0` then `x⁻¹ ∈ m_p`, so its
image `s ∈ m_R`.  On the other hand, from (2), the coordinate `X ∈ K[X]` maps to some `r ∈ R`
with `r ↦ x_L` under `R ⟶ L`, and the stalk map composed with `R ⟶ L` sends `x` to `x_L`
(the generic-point/generic-point compatibility), so `x⁻¹ ↦ x_L⁻¹ = r⁻¹`; injectivity of
`R ⟶ L` gives `s = r⁻¹`, a unit, contradicting `s ∈ m_R`.

(4) By (3) `ℓ` factors through the open immersion `W.ι` (`ℓ` lands in `W` because `W` is open and
every point of `Spec R` specialises to the closed point, hmm — or directly argue with the closed
point and `IsOpenImmersion.factor` style API), giving the required lift. -/
theorem valuativeCriterion_regularOpensMap {K : Type*} [Field K] (C : Work.CurveBasics.Curve K)
    (x : C.functionField) (hx : Transcendental K x) :
    ValuativeCriterion.Existence (Work.SpecLin.Chart.regularOpensMap C x) := by

  intro S
  set W : C.left.Opens := regularOpens C x with hW
  set ψcat : CommRingCat.of S.R ⟶ CommRingCat.of S.K := CommRingCat.ofHom (algebraMap S.R S.K) with hψcat
  -- Step 1: the valuative square over `C.hom` and a lift
  have hsq : (S.i₁ ≫ W.ι) ≫ C.hom = Spec.map ψcat ≫
      (S.i₂ ≫ Spec.map (CommRingCat.ofHom Polynomial.C)) := by
    rw [Category.assoc]
    show S.i₁ ≫ ((regularOpens C x).toScheme ↘ Spec (CommRingCat.of K)) = _
    rw [← regularOpensMap_over C x, ← Category.assoc, S.commSq.w, Category.assoc]
  have hvc : ValuativeCriterion C.hom := by
    have h1 : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme) C.hom := by
      rw [← IsProper.eq_valuativeCriterion]
      exact C.proper
    exact h1.1.1.1
  obtain ⟨l, hl1, _hl2⟩ := (ValuativeCriterion.existence hvc
    ({ R := S.R, K := S.K, i₁ := S.i₁ ≫ W.ι,
       i₂ := S.i₂ ≫ Spec.map (CommRingCat.ofHom Polynomial.C), commSq := ⟨hsq⟩ } :
      ValuativeCommSq C.hom)).exists_lift
  have hl1' : Spec.map ψcat ≫ l = S.i₁ ≫ W.ι := hl1
  -- Step 2: the closed point of `Spec R` lies in `W`
  have hmem : l (IsLocalRing.closedPoint S.R) ∈ (W : Set C.left) :=
    closedPoint_mem_regularOpens' C x hx S.i₁ S.i₂ (S.commSq.w) l hl1'
  -- Step 3: `l` factors through `W`
  have hrange : Set.range l.base ⊆ Set.range W.ι.base := by
    rintro y ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hsp : z ⤳ IsLocalRing.closedPoint S.R := IsLocalRing.specializes_closedPoint z
    exact (specializes_iff_forall_open.mp (hsp.map l.continuous)) (W : Set C.left) W.2 hmem
  let l' : Spec (CommRingCat.of S.R) ⟶ W.toScheme := IsOpenImmersion.lift W.ι l hrange
  have hl' : l' ≫ W.ι = l := IsOpenImmersion.lift_fac W.ι l hrange
  have hl'1 : Spec.map ψcat ≫ l' = S.i₁ := by
    rw [← cancel_mono W.ι, Category.assoc, hl', hl1']
  refine ⟨⟨l', hl'1, ?_⟩⟩
  exact lift_comp_regularOpensMap C x S.i₁ S.i₂ S.commSq.w l' hl'1

end Work.SpecLin.Chart

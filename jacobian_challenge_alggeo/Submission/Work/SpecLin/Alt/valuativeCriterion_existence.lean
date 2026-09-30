import Mathlib
import Submission.Work.SpecLin.Alt.CurveAffine
import Submission.Work.CurveBasics.All
import Submission.Work.SpecLin.Chart.Regular

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry TopCat
open scoped Classical

universe u

namespace Work.SpecLin.Alt


theorem specMap_genericPoint {R L : Type u} [CommRing R] [IsDomain R] [Field L] [Algebra R L]
    [IsFractionRing R L] :
    (Spec.map (CommRingCat.ofHom (algebraMap R L))) (genericPoint (Spec (CommRingCat.of L)))
      = genericPoint (Spec (CommRingCat.of R)) := by
  rw [AlgebraicGeometry.genericPoint_eq_bot_of_affine (CommRingCat.of L),
      AlgebraicGeometry.genericPoint_eq_bot_of_affine (CommRingCat.of R)]
  change PrimeSpectrum.comap (algebraMap R L) ⊥ = (⊥ : PrimeSpectrum R)
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.comap_asIdeal]
  simp only [PrimeSpectrum.asIdeal_bot (R := L), PrimeSpectrum.asIdeal_bot (R := R),
    Ideal.comap_bot_of_injective _ (IsFractionRing.injective R L)]

theorem appTop_specMap_injective {R S : CommRingCat} (f : R ⟶ S)
    (hf : Function.Injective f.hom) :
    Function.Injective ((Spec.map f).appTop.hom) := by
  have hnat := Scheme.ΓSpecIso_naturality f
  have hinj : Function.Injective (((Scheme.ΓSpecIso R).hom ≫ f).hom) := by
    have h1 : Function.Injective ((Scheme.ΓSpecIso R).hom.hom) :=
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.injective
    rw [CommRingCat.hom_comp]
    exact hf.comp h1
  intro a b hab
  apply hinj
  rw [← hnat, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact congrArg _ hab

theorem toStalk_injective (R : CommRingCat) [IsDomain ↥R] (w : ↥(Spec R)) :
    Function.Injective ((StructureSheaf.toStalk ↥R w).hom) := by
  haveI : IsIntegral (Spec R) := inferInstance
  have hg : Function.Injective ((Spec R).presheaf.germ ⊤ w (show w ∈ ⊤ from trivial)).hom :=
    AlgebraicGeometry.germ_injective_of_isIntegral (X := Spec R) (U := ⊤) w (by trivial)
  have hbij : Function.Bijective (algebraMap ↥R Γ((Spec R), ⊤)) :=
    StructureSheaf.algebraMap_obj_top_bijective
  unfold StructureSheaf.toStalk
  exact hg.comp hbij.injective

theorem stalkSpecializes_closedPoint_injective (R : CommRingCat) [IsDomain ↥R] [IsLocalRing ↥R]
    (w : ↥(Spec R)) :
    Function.Injective (((Spec R).presheaf.stalkSpecializes
      (IsLocalRing.specializes_closedPoint w)).hom) := by
  have hkey : (AlgebraicGeometry.stalkClosedPointIso R).inv ≫
      (Spec R).presheaf.stalkSpecializes (IsLocalRing.specializes_closedPoint w) =
      StructureSheaf.toStalk ↥R w := by
    rw [AlgebraicGeometry.stalkClosedPointIso_inv]
    exact StructureSheaf.toStalk_stalkSpecializes _
  rw [Iso.inv_comp_eq (AlgebraicGeometry.stalkClosedPointIso R)] at hkey
  intro a b hab
  have h1 : (StructureSheaf.toStalk ↥R w) ((AlgebraicGeometry.stalkClosedPointIso R).hom a)
      = (StructureSheaf.toStalk ↥R w) ((AlgebraicGeometry.stalkClosedPointIso R).hom b) := by
    simp only [hkey, ConcreteCategory.comp_apply] at hab
    exact hab
  exact (AlgebraicGeometry.stalkClosedPointIso R).commRingCatIsoToRingEquiv.injective
    (toStalk_injective R w h1)

lemma germ_congr {X : Scheme} {U : X.Opens} {x : X} (h1 h2 : x ∈ U) (s : Γ(X, U)) :
    X.presheaf.germ U x h1 s = X.presheaf.germ U x h2 s :=
  congrArg (fun g => g s) (congrArg (fun h => X.presheaf.germ U x h) (Subsingleton.elim h1 h2))

lemma Scheme_Hom_appTop_eq {X Y : Scheme} {f g : X ⟶ Y} (h : f = g) :
    f.appTop = g.appTop := by subst h; rfl




/-- **Existence part of the valuative criterion for `phi`.**

`C` a smooth proper geometrically irreducible curve over a field `K`, `x ∈ K(C)` transcendental,
`s ∈ Γ(C, W)` a section over `W = Work.SpecLin.Alt.regularOpens C x` with `germ s = x`, and
`Work.SpecLin.Alt.phi W s : W ⟶ 𝔸¹_K` the morphism over `Spec K` with coordinate function `s`
(see `Submission/Work/SpecLin/Alt/CurveAffine.lean`).  Then every valuative square over
`phi W s` has a lift.

Detailed route (this is the whole content of "`W` is affine": `C ∖ poles(x)` is the preimage of
`𝔸¹` under a proper map).

Let `V : ValuativeCommSq (phi W s)`, with valuation ring `R = V.R`, fraction field `L = V.K`, top
map `V.i₁ : Spec L ⟶ W.toScheme` and bottom map `V.i₂ : Spec R ⟶ 𝔸¹_K`.

(1) The square over `C.hom` with top map `V.i₁ ≫ W.ι` and bottom map `V.i₂ ≫ (𝔸¹_K ↘ Spec K)` is
commutative (`phi_over`).  Since `C.hom` is proper, the existence part of the valuative criterion
(`IsProper.eq_valuativeCriterion`) gives a lift `l : Spec R ⟶ C.left` with
`Spec.map (ofHom (algebraMap R L)) ≫ l = V.i₁ ≫ W.ι` and `l ≫ C.hom = V.i₂ ≫ (𝔸¹_K ↘ Spec K)`.
(Use `ValuativeCriterion.existence`, as `Work.SpecLin.Setup.exists_CurvePt_of_FPt` does.)

(2) `l` maps the closed point `c := IsLocalRing.closedPoint V.R` into `W`.  Suppose not; then
`q := l c` is a pole of `x`: there is a place `Q` of `C` with `Q.point = q` and
`0 < -C.ordAt x Q` (`Work.SpecLin.Chart.mem_regularOpens`).
Take `g` in the stalk `O := C.left.presheaf.stalk q` with `algebraMap O K(C) g = x⁻¹`
(`Work.CurveBasics.BaseChange.mem_range_algebraMap_stalk_iff` plus
`Work.CurveBasics.Order.ordAt_inv`).  Then `g` is *not* a unit: if `g` were a unit then
`x ∈ range (algebraMap O K(C))`, contradicting `0 ≤ C.ordAt x Q`.

Let `γ := genericPoint (Spec ↧V.R)`, so `l γ = W.ι (V.i₁ ptL) ∈ W` where
`ptL := genericPoint (Spec ↧V.K)` (use `hl₁` and the fact that a point of an open subscheme lies
in that open).  Since `γ ⤳ c` (`IsLocalRing.specializes_closedPoint`), continuity gives
`l γ ⤳ l c`; as `l γ ∈ W` and `l c ∉ W`, the point `l γ` is not closed, hence
`l γ = genericPoint C.left` (`Curve.eq_genericPoint_or_isClosed`) — note that a closed point has
`closure {l γ} = {l γ} ∋ l c`, forcing `l γ = l c ∈ W`.

(3) *The key identity.*  Let `co : Γ(𝔸¹_K, ⊤)` be the coordinate and `r := V.i₂.appTop co ∈ Γ(Spec R,⊤)`.
From `V.commSq.w` applied to `appTop` and `co` (`Scheme.Hom.comp_appTop`,
`Work.SpecLin.Alt.phi_appTop_coord`) one gets
`V.i₁.appTop (W.topIso.inv s) = (Spec.map (ofHom (algebraMap V.R V.K))).appTop r`.
Applying the naturality of `Scheme.Hom.stalkMap` with germs
(`Scheme.Hom.germ_stalkMap_apply`, in both directions) and the compatibility
`Scheme.Opens.stalkIso_inv`, `Scheme.Opens.germ_stalkIso_inv` between the stalks of `W` and of `C`
(the germ of the section `s` at the generic point of `C` is `x`, which is `hs`) yields, for
`tgt := (Spec.map (ofHom (algebraMap V.R V.K))).stalkMap ptL`, the identity
`tgt (l.stalkMap γ x) = tgt ((Spec ↧V.R).presheaf.germ ⊤ γ trivial r)`.
Since `γ` is the generic point of `Spec R`, the source of `tgt` is the function field
`(Spec ↧V.R).functionField`, a field, so `tgt` is injective (`RingHom.injective`), and therefore
`l.stalkMap γ x = (Spec ↧V.R).presheaf.germ ⊤ γ trivial r`.

(4) Multiply with the pole.  Since `x ≠ 0` and `l.stalkMap γ` is a ring homomorphism into a field
(and `l γ = genericPoint C.left`, so that `l.stalkMap γ` is a map `K(C) → (Spec ↧V.R).functionField`),
`l.stalkMap γ x⁻¹ = (l.stalkMap γ x)⁻¹`.  By
`Scheme.Hom.stalkSpecializes_stalkMap_apply` applied to `g` (and using
`algebraMap = stalkSpecializes` for the generic point) we get
`l.stalkMap γ x⁻¹ = (Spec ↧V.R).presheaf.stalkSpecializes hsp (l.stalkMap c g)`, where
`hsp : γ ⤳ c`.  Hence, with `u := l.stalkMap c g` (which is a nonunit of `O_{Spec R,c}` because
`l.stalkMap c` is a local homomorphism of local rings — `IsLocalHom.map_nonunit` — and `g` is a
nonunit),
`1 = (germ_γ r) * stalkSpecializes hsp u = stalkSpecializes hsp (germ_c r * u)`
(using `TopCat.Presheaf.germ_stalkSpecializes`).  The map `stalkSpecializes hsp` is injective: it
is the localisation map `R → Frac R` up to the isomorphism
`AlgebraicGeometry.stalkClosedPointIso ↧R` (compare `StructureSheaf.toStalk` and
`TopCat.Presheaf.germ_stalkSpecializes`), hence injective by
`IsFractionRing.injective R ((Spec ↧R).functionField)`.  So `germ_c r * u = 1` and `u` is a unit,
contradiction.

(5) Consequently every point of `Spec R` maps into `W`: for `z : Spec ↧V.R` one has `z ⤳ c`
(`IsLocalRing.specializes_closedPoint`), hence `l z ⤳ l c` (`Specializes.map`) and
`l z ∈ W` because `W` is open and contains `l c` (`Specializes.mem_open`).  Therefore
`Set.range l ⊆ W = Set.range W.ι` and, with `l' := IsOpenImmersion.lift W.ι l H`, one has
`l' ≫ W.ι = l` (`IsOpenImmersion.lift_fac`).  Finally `l'` is the required lift:
`Spec.map (ofHom (algebraMap R L)) ≫ l' = V.i₁` because the two sides become equal after
composing with the monomorphism `W.ι` (`IsOpenImmersion.mono`), and `l' ≫ phi W s = V.i₂` by
`AffineSpace.hom_ext`: both sides agree after composing with `𝔸¹_K ↘ Spec K`, and their `appTop`
on the coordinate agree because they agree after applying
`(Spec.map (ofHom (algebraMap R L))).appTop`, which is injective up to `Scheme.ΓSpecIso`
(`Scheme.ΓSpecIso_naturality` and `IsFractionRing.injective`), and `V.commSq.w` applied to
`appTop` 
identifies both with `V.i₁.appTop (W.topIso.inv s)`. -/
lemma germ_stalkMap_ι_eq {X : Scheme} (U : X.Opens) (x : U) (hx : (x : X) ∈ U)
    (s : Γ(X, U)) :
    Scheme.Hom.stalkMap U.ι x (X.presheaf.germ U x hx s) =
      (U.toScheme).presheaf.germ ⊤ x trivial (U.topIso.inv s) := by
  rw [← Scheme.Opens.stalkIso_inv]
  refine (U.stalkIso x).commRingCatIsoToRingEquiv.injective ?_
  show (ConcreteCategory.hom (U.stalkIso x).hom)
      ((ConcreteCategory.hom (U.stalkIso x).inv) (X.presheaf.germ U x hx s)) =
    (ConcreteCategory.hom (U.stalkIso x).hom)
      ((ConcreteCategory.hom ((U.toScheme).presheaf.germ ⊤ x trivial))
        ((ConcreteCategory.hom U.topIso.inv) s))
  rw [Iso.inv_hom_id_apply]
  have h2 : (ConcreteCategory.hom (U.stalkIso x).hom)
      ((ConcreteCategory.hom ((U.toScheme).presheaf.germ ⊤ x trivial))
        ((ConcreteCategory.hom U.topIso.inv) s)) =
      X.presheaf.germ (U.ι ''ᵁ ⊤) (x : X) ⟨x, trivial, rfl⟩
        ((ConcreteCategory.hom U.topIso.inv) s) := by
    rw [← ConcreteCategory.comp_apply]
    exact congrArg (fun g => (ConcreteCategory.hom g) ((ConcreteCategory.hom U.topIso.inv) s))
      (Scheme.Opens.germ_stalkIso_hom U (V := ⊤) x trivial)
  rw [h2]
  refine TopCat.Presheaf.germ_ext X.presheaf U hx (𝟙 U)
    (eqToHom (Scheme.Opens.ι_image_top U).symm) ?_
  have hid : X.presheaf.map (𝟙 U).op = 𝟙 (X.presheaf.obj (Opposite.op U)) := by
    rw [CategoryTheory.op_id]
    exact CategoryTheory.Functor.map_id X.presheaf (Opposite.op U)
  rw [hid, ConcreteCategory.id_apply, ← Scheme.Opens.topIso_hom]
  exact (Iso.inv_hom_id_apply U.topIso s).symm


theorem valuativeCriterion_existence {K : Type*} [Field K] {C : Work.CurveBasics.Curve K}
    {x : C.functionField} (hx : Transcendental K x)
    (s : C.left.presheaf.obj (Opposite.op (Work.SpecLin.Alt.regularOpens C x)))
    [Nonempty (Work.SpecLin.Alt.regularOpens C x)]
    (hs : (C.germToFunctionField (Work.SpecLin.Alt.regularOpens C x)).hom s = x) :
    AlgebraicGeometry.ValuativeCriterion.Existence
      (Work.SpecLin.Alt.phi (Work.SpecLin.Alt.regularOpens C x) s) := by
  intro V
  haveI hdomR : IsDomain V.R := V.domain
  haveI hvalR : ValuationRing V.R := V.valuationRing
  haveI hlocR : IsLocalRing V.R := inferInstance
  have hsq : (V.i₁ ≫ (regularOpens C x).ι) ≫ C.hom =
      Spec.map (CommRingCat.ofHom (algebraMap V.R V.K)) ≫ (V.i₂ ≫ A1Over K) := by
    rw [Category.assoc,
      show (regularOpens C x).ι ≫ C.hom = phi (regularOpens C x) s ≫ A1Over K from
        (phi_over C s).symm,
      ← Category.assoc, V.commSq.w, Category.assoc]
  have hvc : ValuativeCriterion C.hom := by
    have h1 : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme) C.hom := by
      rw [← IsProper.eq_valuativeCriterion]
      exact C.proper
    exact h1.1.1.1
  let S' : ValuativeCommSq C.hom :=
    { R := V.R, commRing := V.commRing, domain := V.domain, valuationRing := V.valuationRing,
      K := V.K, field := V.field, algebra := V.algebra, isFractionRing := V.isFractionRing,
      i₁ := V.i₁ ≫ (regularOpens C x).ι, i₂ := V.i₂ ≫ A1Over K, commSq := ⟨hsq⟩ }
  obtain ⟨l, hl1, hl2⟩ := (ValuativeCriterion.existence hvc S').exists_lift
  -- local notation
  have hl1' : Spec.map (CommRingCat.ofHom (algebraMap V.R V.K)) ≫ l =
      V.i₁ ≫ (regularOpens C x).ι := hl1
  have hl2' : l ≫ C.hom = V.i₂ ≫ A1Over K := hl2
  have hcomm : Spec.map (CommRingCat.ofHom (algebraMap V.R V.K)) ≫ V.i₂ =
      V.i₁ ≫ phi (regularOpens C x) s := V.commSq.w.symm
  set pi : Spec (CommRingCat.of V.K) ⟶ Spec (CommRingCat.of V.R) :=
    Spec.map (CommRingCat.ofHom (algebraMap V.R V.K)) with hpi
  set ptL : ↥(Spec (CommRingCat.of V.K)) := genericPoint (Spec (CommRingCat.of V.K)) with hptL
  set clp : ↥(Spec (CommRingCat.of V.R)) := IsLocalRing.closedPoint V.R with hclp
  set r : Γ(Spec (CommRingCat.of V.R), ⊤) :=
    V.i₂.appTop (AffineSpace.coord (Spec (CommRingCat.of K)) PUnit.unit) with hr
  have hcomm' : pi ≫ V.i₂ = V.i₁ ≫ phi (regularOpens C x) s := by
    rw [hpi]; exact V.commSq.w.symm
  have hlin : l (pi ptL) = (regularOpens C x).ι (V.i₁ ptL) := by
    have h := congrArg (fun (f : Spec (CommRingCat.of V.K) ⟶ C.left) => f ptL) hl1'
    simpa only [Scheme.Hom.comp_apply] using h
  have hstar : V.i₁.appTop ((regularOpens C x).topIso.inv s) = pi.appTop r := by
    have h1 : (V.i₁ ≫ phi (regularOpens C x) s).appTop
        (AffineSpace.coord (Spec (CommRingCat.of K)) PUnit.unit) =
        (pi ≫ V.i₂).appTop (AffineSpace.coord (Spec (CommRingCat.of K)) PUnit.unit) := by
      rw [hcomm']
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h1
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
    simp only [phi_appTop_coord] at h1
    exact h1
  have hγR : pi ptL = genericPoint (Spec (CommRingCat.of V.R)) := by
    rw [hpi, hptL]
    exact specMap_genericPoint (R := V.R) (L := V.K)
  have hsp : pi ptL ⤳ clp := IsLocalRing.specializes_closedPoint (pi ptL)
  have hsp' : l (pi ptL) ⤳ l clp := Specializes.map hsp l.continuous
  have hlcmem : l clp ∈ ((regularOpens C x : C.left.Opens) : Set C.left) := by
    by_contra hnot
    by_cases hclosed : IsClosed ({l (pi ptL)} : Set C.left)
    · have hy : l clp = l (pi ptL) := by
        have hmem : l clp ∈ closure ({l (pi ptL)} : Set C.left) :=
          specializes_iff_mem_closure.mp hsp'
        rwa [hclosed.closure_eq] at hmem
      exact hnot (by rw [hy, hlin]; exact (V.i₁ ptL).2)
    · have hγC : l (pi ptL) = genericPoint C.left :=
        (C.eq_genericPoint_or_isClosed (l (pi ptL))).resolve_right hclosed
      exfalso
      have hlγW : l (pi ptL) ∈ ((regularOpens C x : C.left.Opens) : Set C.left) := by
        rw [hlin]; exact (V.i₁ ptL).2
      have hpole : ¬ (∀ Q : C.Place, Q.point = l clp → 0 ≤ C.ordAt x Q) := by
        intro h
        exact hnot ((Work.SpecLin.Chart.mem_regularOpens C x).mpr h)
      push_neg at hpole
      obtain ⟨Q₀, hQ₀pt, hQ₀lt⟩ := hpole
      have hQclosed : IsClosed ({l clp} : Set C.left) := hQ₀pt ▸ Q₀.isClosed
      let Q : C.Place := ⟨l clp, hQclosed⟩
      have hQeq : Q = Q₀ := Subtype.ext hQ₀pt.symm
      have hQlt : C.ordAt x Q < 0 := hQeq.symm ▸ hQ₀lt
      have hxne : x ≠ 0 := hx.ne_zero
      have hordinv : 0 ≤ C.ordAt x⁻¹ Q := by
        show 0 ≤ Scheme.ord x⁻¹ Q.point
        have hQlt' : Scheme.ord x Q.point < 0 := hQlt
        rw [Work.CurveBasics.Order.ordAt_inv C hxne Q]; linarith
      obtain ⟨g, hg⟩ :=
        (Work.CurveBasics.BaseChange.mem_range_algebraMap_stalk_iff C Q x⁻¹).mpr hordinv
      have hg_nonunit : ¬ IsUnit g := by
        rintro ⟨u, hu⟩
        have hxmem : x ∈ (algebraMap (C.left.presheaf.stalk Q.point) C.functionField).range := by
          refine ⟨↑(u⁻¹), ?_⟩
          have h2 : algebraMap (C.left.presheaf.stalk Q.point) C.functionField (↑u) = x⁻¹ := by
            rw [hu]; exact hg
          have h3 : algebraMap (C.left.presheaf.stalk Q.point) C.functionField (↑(u⁻¹)) *
              algebraMap (C.left.presheaf.stalk Q.point) C.functionField (↑u) = 1 := by
            rw [← map_mul, Units.inv_mul, map_one]
          rw [h2] at h3
          calc algebraMap (C.left.presheaf.stalk Q.point) C.functionField (↑(u⁻¹))
              = algebraMap (C.left.presheaf.stalk Q.point) C.functionField (↑(u⁻¹)) *
                  (x * x⁻¹) := by rw [mul_inv_cancel₀ hxne, mul_one]
            _ = (algebraMap (C.left.presheaf.stalk Q.point) C.functionField (↑(u⁻¹)) * x⁻¹) * x := by
                  ring
            _ = 1 * x := by rw [h3]
            _ = x := one_mul x
        have h4 := (Work.CurveBasics.BaseChange.mem_range_algebraMap_stalk_iff C Q x).mp hxmem
        linarith
      have hu_nonunit : ¬ IsUnit (l.stalkMap clp g) := by
        intro hu
        exact hg_nonunit (IsLocalHom.map_nonunit (f := (l.stalkMap clp).hom) g hu)
      have hT_spec : l (pi ptL) ⤳ genericPoint C.left := specializes_of_eq hγC
      let T : C.left.presheaf.stalk (genericPoint C.left) ⟶
          C.left.presheaf.stalk (l (pi ptL)) := C.left.presheaf.stalkSpecializes hT_spec
      have hTs : T x = C.left.presheaf.germ (regularOpens C x) (l (pi ptL)) hlγW s := by
        refine (congrArg (fun z => (ConcreteCategory.hom T) z)
          (show x = C.left.presheaf.germ (regularOpens C x) (genericPoint C.left) _ s from hs.symm)).trans ?_
        exact congrArg (fun (g : C.left.presheaf.obj (Opposite.op (regularOpens C x)) ⟶
            C.left.presheaf.stalk (l (pi ptL))) => (ConcreteCategory.hom g) s)
          (TopCat.Presheaf.germ_stalkSpecializes C.left.presheaf
            (U := (regularOpens C x : C.left.Opens)) (y := genericPoint C.left) _
            (x := l (pi ptL)) hT_spec)
      have hl1c : (V.i₁ ≫ (regularOpens C x).ι) ptL = (pi ≫ l) ptL := hl1.symm ▸ rfl
      have hkey : l.stalkMap (pi ptL) (T x) =
          (Spec (CommRingCat.of V.R)).presheaf.germ ⊤ (pi ptL) trivial r := by
        haveI hsr : IsSimpleRing ((Spec (CommRingCat.of V.R)).presheaf.stalk (pi ptL)) :=
          hγR.symm ▸ (inferInstance : IsSimpleRing ((Spec (CommRingCat.of V.R)).presheaf.stalk
            (genericPoint (Spec (CommRingCat.of V.R)))))
        have hinj : Function.Injective ((pi.stalkMap ptL).hom) := RingHom.injective _
        refine hinj ?_
        have hb : Scheme.Hom.stalkMap (regularOpens C x).ι (V.i₁ ptL)
            (C.left.presheaf.germ (regularOpens C x) ((regularOpens C x).ι (V.i₁ ptL))
              (V.i₁ ptL).2 s) =
            (regularOpens C x).toScheme.presheaf.germ ⊤ (V.i₁ ptL) trivial
              ((regularOpens C x).topIso.inv s) :=
          germ_stalkMap_ι_eq (regularOpens C x) (V.i₁ ptL) (V.i₁ ptL).2 s
        have e3 : (C.left.presheaf.stalkCongr (Inseparable.of_eq hl1c)).inv (T x) =
            C.left.presheaf.germ (regularOpens C x) ((regularOpens C x).ι (V.i₁ ptL))
              (V.i₁ ptL).2 s := by
          rw [TopCat.Presheaf.stalkCongr_inv, hTs]
          exact (ConcreteCategory.comp_apply (C.left.presheaf.germ (regularOpens C x)
              (l (pi ptL)) hlγW) (C.left.presheaf.stalkSpecializes
                (Inseparable.of_eq hl1c).specializes) s).symm.trans
            (congrArg (fun (g : C.left.presheaf.obj (Opposite.op (regularOpens C x)) ⟶
                C.left.presheaf.stalk ((regularOpens C x).ι (V.i₁ ptL))) => (ConcreteCategory.hom g) s)
              (TopCat.Presheaf.germ_stalkSpecializes C.left.presheaf
                (U := (regularOpens C x : C.left.Opens)) (y := l (pi ptL)) hlγW
                (x := (regularOpens C x).ι (V.i₁ ptL)) (Inseparable.of_eq hl1c).specializes))
        have hG : ((V.i₁ ≫ (regularOpens C x).ι).stalkMap ptL)
              (C.left.presheaf.germ (regularOpens C x) ((regularOpens C x).ι (V.i₁ ptL))
                (V.i₁ ptL).2 s) =
            (Spec (CommRingCat.of V.K)).presheaf.germ ⊤ ptL trivial
              (V.i₁.appTop ((regularOpens C x).topIso.inv s)) := by
          rw [Scheme.Hom.stalkMap_comp (V.i₁) (regularOpens C x).ι ptL,
            ConcreteCategory.comp_apply]
          exact (congrArg (fun z => V.i₁.stalkMap ptL z) hb).trans
            (Scheme.Hom.germ_stalkMap_apply V.i₁ ⊤ ptL trivial
              ((regularOpens C x).topIso.inv s))
        have hc := Scheme.Hom.stalkMap_congr_hom (V.i₁ ≫ (regularOpens C x).ι) (pi ≫ l)
          hl1.symm ptL
        calc (pi.stalkMap ptL) (l.stalkMap (pi ptL) (T x))
            = ((pi ≫ l).stalkMap ptL) (T x) := by
                rw [Scheme.Hom.stalkMap_comp (pi) l ptL, ConcreteCategory.comp_apply]
                rfl
          _ = ((pi ≫ l).stalkMap ptL)
                ((C.left.presheaf.stalkCongr (Inseparable.of_eq hl1c)).hom
                  ((C.left.presheaf.stalkCongr (Inseparable.of_eq hl1c)).inv (T x))) :=
                congrArg _ (Iso.inv_hom_id_apply _ (T x)).symm
          _ = (((C.left.presheaf.stalkCongr (Inseparable.of_eq hl1c)).hom ≫
                  (pi ≫ l).stalkMap ptL)
                ((C.left.presheaf.stalkCongr (Inseparable.of_eq hl1c)).inv (T x))) :=
                (ConcreteCategory.comp_apply _ _ _).symm
          _ = ((V.i₁ ≫ (regularOpens C x).ι).stalkMap ptL)
                ((C.left.presheaf.stalkCongr (Inseparable.of_eq hl1c)).inv (T x)) :=
                congrArg (fun (f : C.left.presheaf.stalk ((V.i₁ ≫ (regularOpens C x).ι) ptL) ⟶
                  (Spec (CommRingCat.of V.K)).presheaf.stalk ptL) =>
                    f ((C.left.presheaf.stalkCongr (Inseparable.of_eq hl1c)).inv (T x))) hc.symm
          _ = ((V.i₁ ≫ (regularOpens C x).ι).stalkMap ptL)
                (C.left.presheaf.germ (regularOpens C x) ((regularOpens C x).ι (V.i₁ ptL))
                  (V.i₁ ptL).2 s) := congrArg _ e3
          _ = (Spec (CommRingCat.of V.K)).presheaf.germ ⊤ ptL trivial
                (V.i₁.appTop ((regularOpens C x).topIso.inv s)) := hG
          _ = (Spec (CommRingCat.of V.K)).presheaf.germ ⊤ ptL trivial (pi.appTop r) :=
                congrArg _ hstar
          _ = (pi.stalkMap ptL)
                ((Spec (CommRingCat.of V.R)).presheaf.germ ⊤ (pi ptL) trivial r) :=
                (Scheme.Hom.germ_stalkMap_apply pi ⊤ ptL trivial r).symm
      have e2final : (Spec (CommRingCat.of V.R)).presheaf.stalkSpecializes hsp (l.stalkMap clp g) =
          l.stalkMap (pi ptL) (C.left.presheaf.stalkSpecializes hsp' g) :=
        (Scheme.Hom.stalkSpecializes_stalkMap_apply l (pi ptL) clp hsp g).symm
      have hq1 : C.left.presheaf.stalkSpecializes (hγC ▸ hsp')
          (g : C.left.presheaf.stalk (l clp)) = x⁻¹ := by
        rw [← hg]; rfl
      have e3final : C.left.presheaf.stalkSpecializes hsp' g = T (x⁻¹) := by
        calc C.left.presheaf.stalkSpecializes hsp' g
            = C.left.presheaf.stalkSpecializes (hT_spec.trans (hγC ▸ hsp')) g := by
                rw [Subsingleton.elim (hT_spec.trans (hγC ▸ hsp')) hsp']
          _ = C.left.presheaf.stalkSpecializes hT_spec
                (C.left.presheaf.stalkSpecializes (hγC ▸ hsp') g) := by
                rw [← TopCat.Presheaf.stalkSpecializes_comp C.left.presheaf hT_spec
                  (hγC ▸ hsp'), ConcreteCategory.comp_apply]
          _ = T (x⁻¹) := by rw [hq1]
      have hfin : (Spec (CommRingCat.of V.R)).presheaf.stalkSpecializes hsp
          ((Spec (CommRingCat.of V.R)).presheaf.germ ⊤ clp trivial r) =
          (Spec (CommRingCat.of V.R)).presheaf.germ ⊤ (pi ptL) trivial r := by
        exact congrArg (fun (g : (Spec (CommRingCat.of V.R)).presheaf.obj (Opposite.op ⊤) ⟶
            (Spec (CommRingCat.of V.R)).presheaf.stalk (pi ptL)) => (ConcreteCategory.hom g) r)
          (TopCat.Presheaf.germ_stalkSpecializes ((Spec (CommRingCat.of V.R)).presheaf)
            (U := ⊤) (y := clp) trivial (x := pi ptL) hsp)
      have hfinal : (Spec (CommRingCat.of V.R)).presheaf.stalkSpecializes hsp
          ((Spec (CommRingCat.of V.R)).presheaf.germ ⊤ clp trivial r * l.stalkMap clp g) = 1 := by
        calc (Spec (CommRingCat.of V.R)).presheaf.stalkSpecializes hsp
              ((Spec (CommRingCat.of V.R)).presheaf.germ ⊤ clp trivial r * l.stalkMap clp g)
            = (Spec (CommRingCat.of V.R)).presheaf.stalkSpecializes hsp
                ((Spec (CommRingCat.of V.R)).presheaf.germ ⊤ clp trivial r) *
              (Spec (CommRingCat.of V.R)).presheaf.stalkSpecializes hsp (l.stalkMap clp g) :=
                map_mul _ _ _
            _ = (Spec (CommRingCat.of V.R)).presheaf.germ ⊤ (pi ptL) trivial r *
                l.stalkMap (pi ptL) (C.left.presheaf.stalkSpecializes hsp' g) := by
                rw [hfin, e2final]
            _ = (Spec (CommRingCat.of V.R)).presheaf.germ ⊤ (pi ptL) trivial r *
                l.stalkMap (pi ptL) (T (x⁻¹)) := by rw [e3final]
            _ = l.stalkMap (pi ptL) (T x) * l.stalkMap (pi ptL) (T (x⁻¹)) := by rw [hkey]
            _ = l.stalkMap (pi ptL) (T x * T (x⁻¹)) :=
                  (map_mul (ConcreteCategory.hom (Scheme.Hom.stalkMap l (pi ptL))) (T x) (T (x⁻¹))).symm
            _ = l.stalkMap (pi ptL) (T (x * x⁻¹)) := by
                  rw [map_mul (ConcreteCategory.hom T) x (x⁻¹)]
            _ = l.stalkMap (pi ptL) (T 1) := by rw [mul_inv_cancel₀ hxne]
            _ = l.stalkMap (pi ptL) 1 := by rw [map_one (ConcreteCategory.hom T)]
            _ = 1 := map_one (ConcreteCategory.hom (Scheme.Hom.stalkMap l (pi ptL)))
      have hspk : (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of V.R)).inv ≫
          (Spec (CommRingCat.of V.R)).presheaf.stalkSpecializes hsp =
          StructureSheaf.toStalk ↥(CommRingCat.of V.R) (pi ptL) := by
        rw [AlgebraicGeometry.stalkClosedPointIso_inv]
        exact StructureSheaf.toStalk_stalkSpecializes hsp
      rw [Iso.inv_comp_eq (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of V.R))] at hspk
      have h2v : (StructureSheaf.toStalk ↥(CommRingCat.of V.R) (pi ptL))
          ((AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of V.R)).hom
            ((Spec (CommRingCat.of V.R)).presheaf.germ ⊤ clp trivial r * l.stalkMap clp g)) = 1 := by
        rw [← ConcreteCategory.comp_apply, ← hspk]
        exact hfinal
      have h3v : (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of V.R)).hom
          ((Spec (CommRingCat.of V.R)).presheaf.germ ⊤ clp trivial r * l.stalkMap clp g) = 1 :=
        toStalk_injective (CommRingCat.of V.R) (pi ptL) (by rw [h2v, map_one])
      have h4v : (Spec (CommRingCat.of V.R)).presheaf.germ ⊤ clp trivial r * l.stalkMap clp g = 1 := by
        have h5 := congrArg (fun x => (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of V.R)).inv x) h3v
        rw [Iso.hom_inv_id_apply, map_one] at h5
        exact h5
      exact hu_nonunit ⟨⟨l.stalkMap clp g,
        (Spec (CommRingCat.of V.R)).presheaf.germ ⊤ clp trivial r,
        by rw [mul_comm, h4v], h4v⟩, rfl⟩
  have hrange : Set.range l ⊆ Set.range ((regularOpens C x).ι) := by
    rintro _ ⟨z, rfl⟩
    have hz : z ⤳ clp := IsLocalRing.specializes_closedPoint z
    have hz' : l z ⤳ l clp := Specializes.map hz l.continuous
    exact ⟨⟨l z, Specializes.mem_open hz' (regularOpens C x).isOpen hlcmem⟩, rfl⟩
  haveI : Mono (regularOpens C x).ι := IsOpenImmersion.mono _
  have hl'fac : IsOpenImmersion.lift (regularOpens C x).ι l hrange ≫ (regularOpens C x).ι = l :=
    IsOpenImmersion.lift_fac _ _ _
  have hfac1 : Spec.map (CommRingCat.ofHom (algebraMap V.R V.K)) ≫
      IsOpenImmersion.lift (regularOpens C x).ι l hrange = V.i₁ := by
    refine (cancel_mono (regularOpens C x).ι).mp ?_
    rw [Category.assoc, hl'fac]
    exact hl1'
  have hfac2 : IsOpenImmersion.lift (regularOpens C x).ι l hrange ≫ phi (regularOpens C x) s = V.i₂ := by
    apply AffineSpace.hom_ext
    · rw [Category.assoc, phi_over]
      rw [← Category.assoc, hl'fac]
      exact hl2'
    · intro i
      obtain rfl : i = PUnit.unit := Subsingleton.elim i _
      rw [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]
      simp only [phi_appTop_coord]
      apply appTop_specMap_injective (CommRingCat.ofHom (algebraMap V.R V.K))
        (IsFractionRing.injective V.R V.K)
      rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hfac1, hstar]
  exact ⟨⟨{ l := IsOpenImmersion.lift (regularOpens C x).ι l hrange, fac_left := hfac1,
             fac_right := hfac2 }⟩⟩

end Work.SpecLin.Alt

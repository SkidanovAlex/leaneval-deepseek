import Mathlib
import Submission.Work.BNChart.Chart
import Submission.Work.Charts.eval_bnDelta

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.BNChart

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

noncomputable section

/-- **The evaluation of a section at a field point is the image of its germ under the local
homomorphism `O_{X,f(c)} ⟶ F` determined by `f`.**

This is the technical heart of `evalSection_eq_evalAt`: `evalSection` is defined by pulling a
section back along `f` and reading the result in `Γ(Spec F, ⊤) ≅ F`, while
`Scheme.stalkClosedPointTo f` is the composite of the stalk map of `f` at the closed point of
`Spec F` with `(stalkClosedPointIso F).hom`; both are the same composite. -/
theorem evalSection_eq_stalkClosedPointTo {F : Type u} [Field F] {X : Scheme.{u}}
    (f : Spec (CommRingCat.of F) ⟶ X) (U : X.Opens)
    (hU : f (IsLocalRing.closedPoint F) ∈ U) (s : Γ(X, U)) :
    Scheme.stalkClosedPointTo f (X.presheaf.germ U (f (IsLocalRing.closedPoint F)) hU s)
      = Work.Charts.evalSection f hU s := by
  rw [← ConcreteCategory.comp_apply, Scheme.germ_stalkClosedPointTo f U hU]
  unfold Work.Charts.evalSection
  rw [Scheme.Hom.appLE]
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply, Functor.mapIso_hom, Iso.op_hom,
    eqToIso.hom]
  congr 2

/-- **`evalSection` only depends on the underlying morphism.** -/
theorem evalSection_congr {F : Type u} [Field F] {X : Scheme.{u}} {U : X.Opens}
    {p₁ p₂ : Spec (CommRingCat.of F) ⟶ X} (h : p₁ = p₂)
    (h₁ : p₁ (IsLocalRing.closedPoint F) ∈ U) (h₂ : p₂ (IsLocalRing.closedPoint F) ∈ U)
    (s : Γ(X, U)) :
    Work.Charts.evalSection p₁ h₁ s = Work.Charts.evalSection p₂ h₂ s := by
  cases h
  congr 1

/-- **The value of a structure constant.**  If `f` is a section of the structure morphism
`D ⟶ Spec R`, then the evaluation at `f` of the structure constant `r ∈ R` (viewed as a
section of the structure sheaf of `D` over any open) is `r`. -/
theorem evalSection_algebraMap {R : Type u} [Field R] (D : Work.CurveBasics.Curve R)
    (f : Spec (CommRingCat.of R) ⟶ D.left)
    (hfs : f ≫ D.hom = 𝟙 (Spec (CommRingCat.of R)))
    (V : D.left.Opens) (hV : f (IsLocalRing.closedPoint R) ∈ V) (r : R) :
    Work.Charts.evalSection f hV ((algebraMap R Γ(D.left, V)) r) = r := by
  have halg : (algebraMap R Γ(D.left, V)) r
      = (D.hom.appLE ⊤ V le_top) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := rfl
  rw [halg]
  unfold Work.Charts.evalSection
  conv_lhs => arg 2; rw [← ConcreteCategory.comp_apply]
  erw [Scheme.Hom.appLE_comp_appLE]
  rw [hfs]
  simp only [Scheme.Hom.id_app, Category.id_comp]
  exact Iso.hom_inv_id_apply _ _

/-- **The scalar-free bridge between evaluation on `C` and on `C_F`.**

If `y ∈ Γ(C,U)` is a section on `C` and `π : C_F ⟶ C` is the base-change projection, then
evaluating the pullback `π.app U y` at the `F`-point `ptLeft x` of `C_F` agrees with
evaluating `y` at the `F`-point `x` of `C`.  This is functoriality of `Scheme.Hom.appLE` for
the composite `ptLeft x ≫ π = x.left`. -/
theorem evalSection_ptLeft {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type u} [Field F] [Algebra K F] (x : Work.SpecLin.CurveFPt C F) (U : C.left.Opens)
    (hP : Work.SpecLin.ptLeft x (IsLocalRing.closedPoint F)
      ∈ (Work.CurveBasics.Curve.bcSquare C F).π ⁻¹ᵁ U)
    (hxU : x.left (IsLocalRing.closedPoint F) ∈ U) (y : Γ(C.left, U)) :
    Work.Charts.evalSection (Work.SpecLin.ptLeft x) hP
        ((Work.CurveBasics.Curve.bcSquare C F).π.app U y)
      = Work.Charts.evalSection x.left hxU y := by
  have key : ∀ {p₁ p₂ : Spec (CommRingCat.of F) ⟶ C.left} (hh : p₁ = p₂)
      (h₁ : p₁ (IsLocalRing.closedPoint F) ∈ U) (h₂ : p₂ (IsLocalRing.closedPoint F) ∈ U),
      Work.Charts.evalSection p₁ h₁ y = Work.Charts.evalSection p₂ h₂ y := by
    intro p₁ p₂ hh h₁ h₂
    cases hh
    congr 1
  have step1 : Work.Charts.evalSection (Work.SpecLin.ptLeft x) hP
        ((Work.CurveBasics.Curve.bcSquare C F).π.app U y)
      = Work.Charts.evalSection
        (Work.SpecLin.ptLeft x ≫ (Work.CurveBasics.Curve.bcSquare C F).π) hP y := by
    unfold Work.Charts.evalSection
    rw [Scheme.Hom.app_eq_appLE ((Work.CurveBasics.Curve.bcSquare C F).π) (U := U)]
    conv_lhs => arg 2; rw [← ConcreteCategory.comp_apply]
    erw [Scheme.Hom.appLE_comp_appLE]
  rw [step1]
  exact key (Work.SpecLin.ptLeft_fst x) _ _

/-- **The bridge between the sections `s_j` on `C` and the functions `fieldMap (h_j)` on `C_F`.**

Let `x` be an `F`-point of the curve `C`, `U` an open containing the underlying point of `x` on
which the rational functions `h j` are regular, and `s j` the section of `Γ(C,U)` representing
`h j` (namely `regularOpensSection C (h j)` restricted to `U`).  Then the `F`-linear combination
`f := ∑ j, c j • fieldMap (h j)` of base-changed rational functions has *positive order of
vanishing* at the place `ptPlace x` of `C_F` **if and only if** the corresponding `F`-linear
combination of the values of the sections `s j` at `x` is zero.  Both `0 < n` (so that `Fin n`
is nonempty) and `f ≠ 0` are needed: `ordAt 0 = 0`, so without `hf` the equivalence fails.

Route.  Both sides are the image of the same element of the local ring `O_{C_F, ptPlace x}`
under the local homomorphism `O_{C_F, ptPlace x} → F` induced by the section
`Work.SpecLin.ptLeft x : Spec F ⟶ C_F` of the base change, composed with the canonical
isomorphism of the stalk of `Spec F` at its closed point with `F`.

* On the left: `t := ∑ j, c j • (bcSquare C F).π.app U (s j)` is a section of `Γ(C_F, π⁻¹U)`;
  its value under `(ptLeft x).app (π⁻¹U)` read in `F` is `∑ j, c j * evalSection x.left hxU
  (s j restricted)`, by functoriality of `Scheme.Hom.appLE` for the composite
  `ptLeft x ≫ π = x.left` (`Work.SpecLin.ptLeft_fst`).
* On the right: the `germToFunctionField` of that section is `∑ j, c j • fieldMap (h j)`, by
  `Curve.BCSquare.fieldMap_germToFunctionField_apply` and
  `SpecLin.Chart.germToFunctionField_regularOpensSection`; and the image of an element of
  `O_{C_F, ptPlace x}` under the stalk map vanishes if and only if the element lies in the
  maximal ideal, i.e. (given regularity, `hreg`) if and only if its order of vanishing is
  positive.

Mathlib's `Scheme.Hom.evaluation_naturality` and `Scheme.Hom.stalkMap_germ` are the tools. -/
theorem evalSection_eq_evalAt {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type u} [Field F] [Algebra K F] {n : ℕ} (hn : 0 < n)
    (x : Work.SpecLin.CurveFPt C F) (h : Fin n → C.functionField) (U : C.left.Opens)
    (hU : ∀ j, U ≤ Work.SpecLin.Chart.regularOpens C (h j))
    (hxU : x.left (IsLocalRing.closedPoint F) ∈ U) (c : Fin n → F)
    (hf : (∑ j, c j • (Work.CurveBasics.Curve.bcSquare C F).fieldMap.hom (h j)) ≠ 0)
    (hreg : 0 ≤ (C.baseChange F).ordAt
      (∑ j, c j • (Work.CurveBasics.Curve.bcSquare C F).fieldMap.hom (h j))
      (Work.SpecLin.ptPlace x)) :
    (∑ j, c j * Work.Charts.evalSection x.left hxU
        ((C.left.presheaf.map (CategoryTheory.homOfLE (hU j)).op)
          (Work.SpecLin.Chart.regularOpensSection C (h j)))) = 0 ↔
      0 < (C.baseChange F).ordAt
        (∑ j, c j • (Work.CurveBasics.Curve.bcSquare C F).fieldMap.hom (h j))
        (Work.SpecLin.ptPlace x) := by
  classical
  haveI hUne : Nonempty U := ⟨x.left (IsLocalRing.closedPoint F), hxU⟩
  have hP : (Work.SpecLin.ptLeft x) (IsLocalRing.closedPoint F)
      ∈ (Work.CurveBasics.Curve.bcSquare C F).π ⁻¹ᵁ U := by
    show ((Work.SpecLin.ptLeft x ≫ Work.CurveBasics.Curve.baseChangeFst C F)
      (IsLocalRing.closedPoint F)) ∈ U
    rw [Work.SpecLin.ptLeft_fst]
    exact hxU
  set t : Γ((C.baseChange F).left, (Work.CurveBasics.Curve.bcSquare C F).π ⁻¹ᵁ U)
      := ∑ j, (algebraMap F Γ((C.baseChange F).left, (Work.CurveBasics.Curve.bcSquare C F).π ⁻¹ᵁ U)) (c j)
          * (Work.CurveBasics.Curve.bcSquare C F).π.app U
              ((C.left.presheaf.map (CategoryTheory.homOfLE (hU j)).op)
                (Work.SpecLin.Chart.regularOpensSection C (h j))) with htdef
  have hA : Work.Charts.evalSection (Work.SpecLin.ptLeft x) hP t
      = ∑ j, c j * Work.Charts.evalSection x.left hxU
          ((C.left.presheaf.map (CategoryTheory.homOfLE (hU j)).op)
            (Work.SpecLin.Chart.regularOpensSection C (h j))) := by
    rw [htdef]
    rw [← Work.Charts.evalSectionHom_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul]
    rw [Work.Charts.evalSectionHom_apply, Work.Charts.evalSectionHom_apply]
    rw [evalSection_algebraMap (C.baseChange F) (Work.SpecLin.ptLeft x)
      (Work.SpecLin.Points.ptLeft_comp_hom x) ((Work.CurveBasics.Curve.bcSquare C F).π ⁻¹ᵁ U) hP (c j)]
    rw [evalSection_ptLeft x U hP hxU]
  have hB : (Work.CurveBasics.Curve.germToFunctionField (C.baseChange F)
        ((Work.CurveBasics.Curve.bcSquare C F).π ⁻¹ᵁ U)).hom t
      = ∑ j, c j • (Work.CurveBasics.Curve.bcSquare C F).fieldMap.hom (h j) := by
    rw [htdef]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul]
    rw [Work.CurveBasics.Curve.BCSquare.germToFunctionField_algebraMap]
    congr 1
    rw [← Work.CurveBasics.Curve.BCSquare.fieldMap_germToFunctionField_apply
      (Work.CurveBasics.Curve.bcSquare C F) U
      ((C.left.presheaf.map (CategoryTheory.homOfLE (hU j)).op)
        (Work.SpecLin.Chart.regularOpensSection C (h j)))]
    congr 1
    rw [Work.SpecLin.Chart.germToFunctionField_map_eq]
    rw [Work.SpecLin.Chart.germToFunctionField_regularOpensSection]
  set a : (C.baseChange F).left.presheaf.stalk ((Work.SpecLin.ptLeft x) (IsLocalRing.closedPoint F))
      := (C.baseChange F).left.presheaf.germ ((Work.CurveBasics.Curve.bcSquare C F).π ⁻¹ᵁ U)
          ((Work.SpecLin.ptLeft x) (IsLocalRing.closedPoint F)) hP t with ha
  have hsk : Work.Charts.evalSection (Work.SpecLin.ptLeft x) hP t
      = Scheme.stalkClosedPointTo (Work.SpecLin.ptLeft x) a := by
    rw [ha]
    exact (evalSection_eq_stalkClosedPointTo (Work.SpecLin.ptLeft x)
      ((Work.CurveBasics.Curve.bcSquare C F).π ⁻¹ᵁ U) hP t).symm
  have hpoly : (∑ j, c j • (Work.CurveBasics.Curve.bcSquare C F).fieldMap.hom (h j))
      = (algebraMap ((C.baseChange F).left.presheaf.stalk
          ((Work.SpecLin.ptLeft x) (IsLocalRing.closedPoint F)))
          (C.baseChange F).functionField) a := by
    have h1 : (algebraMap ((C.baseChange F).left.presheaf.stalk
          ((Work.SpecLin.ptLeft x) (IsLocalRing.closedPoint F)))
          (C.baseChange F).functionField) a
        = (Work.CurveBasics.Curve.germToFunctionField (C.baseChange F)
            ((Work.CurveBasics.Curve.bcSquare C F).π ⁻¹ᵁ U)).hom t := by
      rw [ha]
      exact Scheme.algebraMap_germ_eq_germToFunctionField (X := (C.baseChange F).left) hP t
    exact hB.symm.trans h1.symm
  have hfne : ((algebraMap ((C.baseChange F).left.presheaf.stalk
      ((Work.SpecLin.ptLeft x) (IsLocalRing.closedPoint F)))
      (C.baseChange F).functionField) a) ≠ 0 := by
    rw [← hpoly]
    exact hf
  have hreg' : 0 ≤ (C.baseChange F).ordAt
      ((algebraMap ((C.baseChange F).left.presheaf.stalk
        ((Work.SpecLin.ptLeft x) (IsLocalRing.closedPoint F)))
        (C.baseChange F).functionField) a) (Work.SpecLin.ptPlace x) := by
    rw [← hpoly]
    exact hreg
  have hloc : IsLocalHom (Scheme.stalkClosedPointTo (Work.SpecLin.ptLeft x)).hom := inferInstance
  have hkey : (Scheme.stalkClosedPointTo (Work.SpecLin.ptLeft x)) a = 0 ↔ ¬ IsUnit a := by
    constructor
    · intro h0 hu
      have h1 : IsUnit ((Scheme.stalkClosedPointTo (Work.SpecLin.ptLeft x)) a) := hu.map _
      rw [h0] at h1
      exact not_isUnit_zero h1
    · intro hnu
      by_contra hne
      exact hnu (hloc.map_nonunit a (isUnit_iff_ne_zero.mpr hne))
  haveI hdvr : IsDiscreteValuationRing
      ↑((C.baseChange F).left.presheaf.stalk ((Work.SpecLin.ptLeft x) (IsLocalRing.closedPoint F))) :=
    Work.CurveBasics.Curve.Place.instIsDiscreteValuationRing (Work.SpecLin.ptPlace x)
  have hunit : IsUnit a ↔ (C.baseChange F).ordAt
      ((algebraMap ((C.baseChange F).left.presheaf.stalk
        ((Work.SpecLin.ptLeft x) (IsLocalRing.closedPoint F)))
        (C.baseChange F).functionField) a) (Work.SpecLin.ptPlace x) = 0 := by
    have h1 : IsUnit a ↔ Ring.ordFrac ↑((C.baseChange F).left.presheaf.stalk
        ((Work.SpecLin.ptLeft x) (IsLocalRing.closedPoint F)))
        ((algebraMap ((C.baseChange F).left.presheaf.stalk
          ((Work.SpecLin.ptLeft x) (IsLocalRing.closedPoint F)))
          (C.baseChange F).functionField) a) = 1 :=
      Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing
    have h2 : Ring.ordFrac ↑((C.baseChange F).left.presheaf.stalk
          ((Work.SpecLin.ptLeft x) (IsLocalRing.closedPoint F)))
          ((algebraMap ((C.baseChange F).left.presheaf.stalk
            ((Work.SpecLin.ptLeft x) (IsLocalRing.closedPoint F)))
            (C.baseChange F).functionField) a) = 1 ↔ (C.baseChange F).ordAt
          ((algebraMap ((C.baseChange F).left.presheaf.stalk
            ((Work.SpecLin.ptLeft x) (IsLocalRing.closedPoint F)))
            (C.baseChange F).functionField) a) (Work.SpecLin.ptPlace x) = 0 := by
      have hq : Order.coheight (Work.SpecLin.ptPlace x).point = 1 :=
        (Work.SpecLin.ptPlace x).eq_coheight_one
      have h3 := (Scheme.ord_eq_iff hq hfne (n := 0)).symm
      exact h3
    exact h1.trans h2
  rw [← hA, hsk, hpoly, hkey]
  constructor
  · intro hnu
    have hne : (C.baseChange F).ordAt
        ((algebraMap ((C.baseChange F).left.presheaf.stalk
          ((Work.SpecLin.ptLeft x) (IsLocalRing.closedPoint F)))
          (C.baseChange F).functionField) a) (Work.SpecLin.ptPlace x) ≠ 0 :=
      fun hz => hnu (hunit.mpr hz)
    exact lt_of_le_of_ne' hreg' hne
  · intro hpos hu
    rw [hunit.mp hu] at hpos
    exact lt_irrefl _ hpos

end

end Work.BNChart

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Base-change squares of curves

For a curve `C` over a field `k` and a field extension `F/k`, the base change `C_F` of `C` to
`F` is the fibre product `C ×_k Spec F`.  For the theory of divisors under field extensions it is
convenient to work not only with the tautological projection `C_F ⟶ C` but with an arbitrary
cartesian square

```
C'  ⟶  C
↓      ↓
Spec F ⟶ Spec k
```

since this is the shape in which iterated base changes (a field extension `F → F'` applied to
an already base changed curve `C_F`) appear.  This file sets up the structure `BCSquare` of such
squares, the tautological square `bcSquare C F`, the induced map of function fields
`K(C) ⟶ K(C')`, and the pullback of divisors `C.Div →+ C'.Div`, whose coefficient at a place
`Q'` of `C'` is `e(Q'/Q)·D(Q)` with `Q` the place of `C` below `Q'` and `e(Q'/Q)` the
ramification index.

## Main definitions

* `Work.CurveBasics.Curve.BCSquare` — a cartesian square as above, with `π : C'.left ⟶ C.left`
  and `isPullback`;
* `Work.CurveBasics.Curve.bcSquare` — the tautological square for `C.baseChange F`;
* `Curve.BCSquare.fieldMap` — the induced map `K(C) ⟶ K(C')` of function fields;
* `Curve.BCSquare.under`, `Curve.BCSquare.ramIdx` — the place below a place of `C'` and its
  ramification index;
* `Curve.BCSquare.divMap` — the pullback of divisors `C.Div →+ C'.Div`.

## Main results

* `Curve.BCSquare.π_genericPoint` — `π` maps the generic point of `C'` to the generic point of
  `C`;
* `Curve.BCSquare.divMap_apply` — the coefficient formula for `divMap`.
-/
import Mathlib
import Submission.Work.CurveBasics.BaseChange
import Submission.Work.CurveBasics.BaseChangeDivisor
import Submission.Work.CurveBasics.Place.ord_uniformizer

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics
namespace Curve

noncomputable section

variable {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]

/-- `C'` (over `F`) is a base change of `C` (over `k`) along `Spec F ⟶ Spec k`: a cartesian
square with `π : C'.left ⟶ C.left`. -/
structure BCSquare (C : Curve k) (C' : Curve F) where
  π : C'.left ⟶ C.left
  isPullback : IsPullback π C'.hom C.hom (specMap k F)

/-- The tautological square exhibiting `C.baseChange F` as a base change of `C`. -/
def bcSquare (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    BCSquare C (C.baseChange F) :=
  ⟨baseChangeFst C F, IsPullback.of_hasPullback _ _⟩

namespace BCSquare

variable {C : Curve k} {C' : Curve F}

/-- The projection of a base-change square is surjective: it is the base change of the
surjective morphism `Spec F ⟶ Spec k`. -/
instance instSurjective (S : BCSquare C C') : Surjective S.π := by
  haveI : MorphismProperty.IsStableUnderBaseChangeAlong (@Surjective) C.hom :=
    ⟨fun pb h => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb h⟩
  have h : Surjective (S.isPullback.isoPullback.hom ≫ pullback.fst C.hom (specMap k F)) :=
    inferInstance
  rwa [S.isPullback.isoPullback_hom_fst] at h

/-- The preimage of an open subset of `C` under the projection of a base-change square. -/
abbrev preimage (S : BCSquare C C') (W : C.left.Opens) : C'.left.Opens := S.π ⁻¹ᵁ W

/-- The preimage of a nonempty open subset of `C` under the (surjective) projection is
nonempty. -/
instance instNonemptyPreimage (S : BCSquare C C') (W : C.left.Opens) [Nonempty W] :
    Nonempty (S.π ⁻¹ᵁ W) := by
  obtain ⟨w⟩ := ‹Nonempty W›
  obtain ⟨y, hy⟩ := S.π.surjective w.1
  exact ⟨⟨y, by show S.π y ∈ W; rw [hy]; exact w.2⟩⟩

/-- The projection `C' ⟶ C` maps the generic point of `C'` to the generic point of `C`. -/
theorem π_genericPoint (S : BCSquare C C') :
    S.π (genericPoint C'.left) = genericPoint C.left := by
  have hcont : Continuous S.π := S.π.continuous
  have hsurj : Function.Surjective S.π := S.π.surjective
  have hcl : closure ({S.π (genericPoint C'.left)} : Set C.left) = Set.univ := by
    have h1 : closure ({genericPoint C'.left} : Set C'.left) = Set.univ := genericPoint_spec _
    rw [← Set.image_singleton]
    have h2 : S.π '' closure ({genericPoint C'.left} : Set C'.left) ⊆
        closure (S.π '' {genericPoint C'.left}) := image_closure_subset_closure_image hcont
    rw [h1, Set.image_univ, Set.range_eq_univ.mpr hsurj] at h2
    exact Set.eq_univ_of_univ_subset h2
  exact T0Space.t0 (inseparable_iff_specializes_and.mpr
    ⟨by rw [specializes_iff_mem_closure, hcl]; trivial,
     by rw [specializes_iff_mem_closure, genericPoint_spec]; trivial⟩)

/-- The field homomorphism `K(C) ⟶ K(C')` induced by the projection of a base-change
square. -/
def fieldMap (S : BCSquare C C') : C.functionField ⟶ C'.functionField :=
  C.left.presheaf.stalkSpecializes (by rw [S.π_genericPoint]; exact specializes_rfl) ≫
    S.π.stalkMap (genericPoint C'.left)

/-- The place of `C` below a place of `C'`, when it is again a place. -/
def under (S : BCSquare C C') (Q' : C'.Place)
    (h : IsClosed ({S.π Q'.point} : Set C.left)) : C.Place :=
  ⟨S.π Q'.point, h⟩

/-- The ramification index of a place of `C'` over its image in `C`; `0` if the image is the
generic point. -/
noncomputable def ramIdx (S : BCSquare C C') (Q' : C'.Place) : ℤ :=
  if h : IsClosed ({S.π Q'.point} : Set C.left) then
    C'.ordAt (S.fieldMap.hom (S.under Q' h).uniformizer) Q'
  else 0

/-- The coefficient at a place of `C'` of the base change of a divisor. -/
noncomputable def divMapCoeff (S : BCSquare C C') (D : C.Div) (Q' : C'.Place) : ℤ :=
  if h : IsClosed ({S.π Q'.point} : Set C.left) then
    D (S.under Q' h) * S.ramIdx Q'
  else 0

/-- The support of `divMapCoeff` is finite: it is contained in the union, over the support of
`D`, of the supports of the principal divisors of the images of the uniformizers. -/
theorem finite_support_divMapCoeff (S : BCSquare C C') (D : C.Div) :
    (Function.support (S.divMapCoeff D)).Finite := by
  classical
  refine Set.Finite.subset (s := ⋃ Q ∈ D.support, {Q' : C'.Place |
      C'.ordAt (S.fieldMap.hom Q.uniformizer) Q' ≠ 0}) ?_ (fun Q' hQ' => ?_)
  · refine Set.Finite.biUnion D.support.finite_toSet (fun Q _ => ?_)
    exact C'.finite_support_ordAt (S.fieldMap.hom Q.uniformizer)
  · simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe]
    by_cases h : IsClosed ({S.π Q'.point} : Set C.left)
    · have h1 : D (S.under Q' h) * S.ramIdx Q' ≠ 0 := by
        simpa only [Set.mem_setOf_eq, Function.mem_support, divMapCoeff, dif_pos h] using hQ'
      have h2 : D (S.under Q' h) ≠ 0 := fun h0 => h1 (by rw [h0, zero_mul])
      refine ⟨S.under Q' h, ?_, ?_⟩
      · simpa only [Finsupp.mem_support_iff] using h2
      · have h3 : S.ramIdx Q' ≠ 0 := fun h0 => h1 (by rw [h0, mul_zero])
        have h4 : S.ramIdx Q' = C'.ordAt (S.fieldMap.hom (S.under Q' h).uniformizer) Q' := by
          simp only [ramIdx, dif_pos h]
        rw [← h4]
        simpa only [Function.mem_support] using h3
    · exact absurd (by rw [divMapCoeff, dite_eq_right h]) hQ'

/-- **Base change of divisors.**  The pullback of a divisor along the projection of a
base-change square, with the ramification weights: the coefficient of `[Q']` is
`e(Q'/Q) · D(Q)`. -/
noncomputable def divMap (S : BCSquare C C') : C.Div →+ C'.Div where
  toFun D := Finsupp.ofSupportFinite (S.divMapCoeff D) (S.finite_support_divMapCoeff D)
  map_zero' := by
    ext Q'
    simp only [Finsupp.ofSupportFinite_coe, Finsupp.zero_apply, divMapCoeff]
    split <;> simp
  map_add' D E := by
    ext Q'
    simp only [Finsupp.ofSupportFinite_coe, Finsupp.add_apply, divMapCoeff]
    split
    · ring
    · simp

@[simp]
theorem divMap_apply (S : BCSquare C C') (D : C.Div) (Q' : C'.Place) :
    S.divMap D Q' = S.divMapCoeff D Q' :=
  congrFun (Finsupp.ofSupportFinite_coe (f := S.divMapCoeff D)
    (hf := S.finite_support_divMapCoeff D)) Q'

end BCSquare

variable {C : Curve k} {C' : Curve F}

/-- Composition of base-change squares: given a tower of fields `k → F → F'` and squares over
each step, the outer square is again cartesian. -/
def BCSquare.comp (S : BCSquare C C') {F' : Type u} [Field F'] [Algebra F F']
    [Algebra k F'] [IsScalarTower k F F'] {C'' : Curve F'} (T : BCSquare C' C'') :
    BCSquare C C'' :=
  ⟨T.π ≫ S.π, by
    have hspec : (specMap k F' : Spec (CommRingCat.of F') ⟶ Spec (CommRingCat.of k)) =
        specMap F F' ≫ specMap k F := by
      simp only [specMap]
      rw [IsScalarTower.algebraMap_eq k F F', CommRingCat.ofHom_comp, Spec.map_comp]
    rw [hspec]
    exact (T.isPullback.flip.paste_vert S.isPullback.flip).flip⟩

end

end Curve
end Work.CurveBasics

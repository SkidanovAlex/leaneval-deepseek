/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The function field of a curve has a separating element

For a smooth, proper, geometrically irreducible curve `C` over a field `k` there is an element
`t ∈ K(C)` which is transcendental over `k` and such that `K(C)/k(t)` is finite and separable
(a *separating element* of the function field, Stichtenoth, *Algebraic Function Fields and
Codes*, Chapter 3).

The proof has three ingredients.

* There is a transcendental element: at any place `Q` the uniformizer `Q.uniformizer` has order of
  vanishing `1` at `Q`, while the image of a constant has order `0`;
  since every element of `K(C)` algebraic over `k` is a constant
  (`Work.CurveBasics.Basic.eq_algebraMap_of_isAlgebraic`), `Q.uniformizer` is transcendental.
* For any transcendental `h`, the extension `K(C)/k(h)` is finite
  (`Work.CurveBasics.Order.finiteDimensional_adjoin_functionField`); combining this with
  `Algebra.IsAlgebraic.trdeg_le_cardinalMk` gives `trdeg_k K(C) ≤ 1`.
* In characteristic `0` any transcendental element is already separating (fields of
  characteristic `0` are perfect).  In characteristic `p > 0` we use the geometric input
  `C.geomReduced`, which makes `K(C) ⊗[k] k̄` a domain for `k̄` the algebraic closure of `k`
  (`Work.CurveBasics.Curve.isDomain_tensor_sections` together with
  `Work.CurveBasics.isDomain_tensor_of_fractionRing`).  This says that the `p`-th powers of a
  `k`-linearly independent family in `K(C)` stay `k`-linearly independent, i.e. hypothesis (2)
  of Stacks 030W; that lemma
  (`exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType`) provides
  a separating transcendence basis `s`, which is a single element because
  `trdeg_k K(C) ≤ 1`.
-/
import Mathlib
import Submission.Work.CurveBasics.Basic
import Submission.Work.CurveBasics.Basic.eq_algebraMap_of_isAlgebraic
import Submission.Work.CurveBasics.Order
import Submission.Work.CurveBasics.Order.div_algebraMap_eq_zero
import Submission.Work.CurveBasics.Order.finiteDimensional_adjoin_functionField
import Submission.Work.CurveBasics.Basic.isDomain_tensor_sections
import Submission.Work.CurveBasics.Basic.isDomain_tensor_fractionRing
import Submission.Work.CurveBasics.Place.ord_uniformizer
import Submission.Work.CurveBasics.SeparatingElement.linearIndependent_pow_of_isDomain_tensor
import Submission.Work.CurveBasics.SeparatingElement.exists_eq_singleton_of_isTranscendenceBasis_of_trdeg_le_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical TensorProduct

universe u

namespace Work.CurveBasics

open Work.CurveBasics in
/-- A curve has a place: a point which is not the generic point is closed, and a curve has more
than one point. -/
theorem exists_place {k : Type*} [Field k] (C : Curve k) : Nonempty C.Place := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne C.left
  have hex : ∃ z : C.left, z ≠ genericPoint C.left := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hab ((h a).trans (h b).symm)
  obtain ⟨z, hz⟩ := hex
  exact ⟨⟨z, (C.eq_genericPoint_or_isClosed z).resolve_left hz⟩⟩

open Work.CurveBasics in
/-- **The function field of a curve has a transcendental element.**  The uniformizer at any place
`Q` has order of vanishing `1` at `Q`, whereas every constant has order `0`; an element of `K(C)`
algebraic over `k` is a constant, so `Q.uniformizer` is transcendental. -/
theorem exists_transcendental {k : Type*} [Field k] (C : Curve k) :
    ∃ h : C.functionField, Transcendental k h := by
  obtain ⟨Q⟩ := exists_place C
  refine ⟨Q.uniformizer, fun halg => ?_⟩
  obtain ⟨c, hc⟩ := Basic.eq_algebraMap_of_isAlgebraic C halg
  have h1 : C.ordAt Q.uniformizer Q = 1 := by
    rw [Curve.ordAt, Place.ord_uniformizer]
  have h2 : C.ordAt (algebraMap k C.functionField c) Q = 0 :=
    Order.ordAt_algebraMap_eq_zero C c Q
  rw [hc] at h1
  rw [h1] at h2
  exact one_ne_zero h2

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- **The function field of a curve has transcendence degree at most one over `k`.**  If `h` is
transcendental and `K(C)/k(h)` is finite dimensional (hence algebraic), then
`trdeg_k K(C) ≤ #({h} : Set K(C)) ≤ 1` by `Algebra.IsAlgebraic.trdeg_le_cardinalMk`. -/
theorem trdeg_functionField_le_one {k : Type*} [Field k] (C : Curve k) {h : C.functionField}
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin k ({h} : Set C.functionField))
      C.functionField) :
    Algebra.trdeg k C.functionField ≤ 1 := by
  have h1 : Algebra.IsAlgebraic ↥(IntermediateField.adjoin k ({h} : Set C.functionField))
      C.functionField := Algebra.IsAlgebraic.of_finite _ _
  have h2 : Algebra.IsAlgebraic ↥(Algebra.adjoin k ({h} : Set C.functionField))
      ↥(IntermediateField.adjoin k ({h} : Set C.functionField)) := inferInstance
  have h3 : Algebra.IsAlgebraic ↥(Algebra.adjoin k ({h} : Set C.functionField))
      C.functionField :=
    Algebra.IsAlgebraic.trans ↥(Algebra.adjoin k ({h} : Set C.functionField))
      ↥(IntermediateField.adjoin k ({h} : Set C.functionField)) C.functionField
  refine (Algebra.IsAlgebraic.trdeg_le_cardinalMk k ({h} : Set C.functionField)).trans ?_
  rw [Cardinal.mk_le_one_iff_set_subsingleton]
  exact fun x hx y hy => hx.trans hy.symm

open Work.CurveBasics in
/-- The function field of a curve has a separating element: an element `t` transcendental over `k`
such that `K(C)/k(t)` is finite separable. -/
theorem exists_separating_element {k : Type*} [Field k] (C : Curve k) :
    ∃ t : C.functionField,
      Transcendental k t ∧
      FiniteDimensional ↥(IntermediateField.adjoin k ({t} : Set C.functionField))
        C.functionField ∧
      Algebra.IsSeparable ↥(IntermediateField.adjoin k ({t} : Set C.functionField))
        C.functionField := by
  classical
  -- a transcendental element of the function field, and the facts attached to it
  obtain ⟨h, hh⟩ := exists_transcendental C
  have hfin : FiniteDimensional ↥(IntermediateField.adjoin k ({h} : Set C.functionField))
      C.functionField := Order.finiteDimensional_adjoin_functionField C hh
  have htr : Algebra.trdeg k C.functionField ≤ 1 := trdeg_functionField_le_one C hfin
  -- an affine chart of the curve, used for the algebraic inputs over `k`
  obtain ⟨x₀⟩ := (inferInstance : Nonempty C.left)
  obtain ⟨U, hU, hxU, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp C.left.isBasis_affineOpens)
      (show x₀ ∈ (⊤ : C.left.Opens) from trivial)
  haveI hUne : Nonempty U := ⟨⟨x₀, hxU⟩⟩
  haveI hfrac : IsFractionRing Γ(C.left, U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C.left U hU
  haveI hST : IsScalarTower k Γ(C.left, U) C.functionField := Curve.isScalarTower_sections C U
  haveI hfg : Algebra.FiniteType k Γ(C.left, U) := Order.algebra_finiteType_sections C hU
  haveI hEFTA : Algebra.EssFiniteType Γ(C.left, U) C.functionField :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors Γ(C.left, U))
  haveI hEFT : Algebra.EssFiniteType k C.functionField :=
    Algebra.EssFiniteType.comp k Γ(C.left, U) C.functionField
  -- geometric reducedness: `K(C) ⊗[k] L` is a domain for every field extension `L/k`
  have hdom : IsDomain (C.functionField ⊗[k] AlgebraicClosure k) :=
    isDomain_tensor_of_fractionRing (k := k) (A := Γ(C.left, U)) (L := AlgebraicClosure k)
      (K := C.functionField) (Curve.isDomain_tensor_sections C hU (AlgebraicClosure k))
  rcases CharP.exists' k with hchar0 | ⟨p, hp, hpk⟩
  · -- in characteristic zero any transcendental element is separating
    haveI : CharZero k := hchar0
    exact ⟨h, hh, hfin, inferInstance⟩
  · -- in characteristic `p` we use Stacks 030W with the `p`-th power criterion
    haveI : CharP k p := hpk
    haveI : ExpChar k p := .prime hp.out
    have H : ∀ s : Finset C.functionField, LinearIndepOn k id (s : Set C.functionField) →
        LinearIndepOn k (· ^ p) (s : Set C.functionField) := by
      intro s hs
      exact SeparatingElement.linearIndependent_pow_of_isDomain_tensor p hp.out hdom hs
    obtain ⟨s, hs, hsep⟩ :=
      exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType p hp.out H
    obtain ⟨t, ht, httr⟩ :=
      SeparatingElement.exists_eq_singleton_of_isTranscendenceBasis_of_trdeg_le_one h hh htr hs
    refine ⟨t, httr, Order.finiteDimensional_adjoin_functionField C httr, ?_⟩
    have hsq : ({t} : Set C.functionField) = (s : Set C.functionField) := by
      rw [ht]
      simp
    rw [hsq]
    exact hsep

end Work.CurveBasics

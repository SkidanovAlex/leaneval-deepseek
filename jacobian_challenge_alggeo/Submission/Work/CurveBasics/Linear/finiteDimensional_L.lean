/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite-dimensionality of the Riemann–Roch space `L(D)`

For a smooth, proper, geometrically irreducible curve `C` over a field `k` and a divisor `D`,
the Riemann–Roch space `L(D) = {h : K(C) | div h + D ≥ 0} ∪ {0}` is finite dimensional over `k`.

The heart of the argument is the case `D = 0`: a rational function without poles is algebraic
over `k`.  Indeed, a transcendental `h ∈ K(C)` lies outside some valuation subring `V ⊆ K(C)`
containing `k` (`Work.CurveBasics.Linear.valuationRing_notMem`); the converse direction of the
dictionary between places of `C` and valuation subrings of `K(C)`
(`Work.CurveBasics.Place.exists_place_of_valuationSubring`, a consequence of the valuative
criterion for the proper morphism `C ⟶ Spec k`) exhibits a place `Q` with `V = Q.valuationSubring`,
and `Work.CurveBasics.Place.mem_valuationSubring_iff` then says that `h` has a pole at `Q`.

Since `k` is relatively algebraically closed in `K(C)`
(`Work.CurveBasics.Basic.eq_algebraMap_of_isAlgebraic`), `L 0` consists of the constants and is
finite dimensional.  The general case is reduced to `D = 0` by the assembly argument below: one
replaces `D` by its positive part `D⁺` (`D⁺ Q = max 0 (D Q)`, so that `L D ≤ L D⁺`), and for an
effective divisor one inducts on `∑_Q D Q`, adding one place at a time; adding a place increases
`dim L` by at most the degree of the place
(`Work.CurveBasics.Linear.finrank_quotient_add_place`).
-/
import Mathlib
import Submission.Work.CurveBasics.All
import Submission.Work.CurveBasics.Place.exists_place_of_valuationSubring
import Submission.Work.CurveBasics.Linear
import Submission.Work.CurveBasics.Linear.valuationRing_notMem
import Submission.Work.CurveBasics.Linear.finrank_quotient_add_place

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics.Linear

open Work.CurveBasics

/-! ## A rational function without poles is constant -/

/-- **A rational function without poles is algebraic over `k`.**

If `h` lies in the Riemann–Roch space of the zero divisor, i.e. `div h ≥ 0`, then `h` is
algebraic over `k`.  Indeed, if `h` were transcendental then by `valuationRing_notMem` there is a
valuation subring `V ⊆ K(C)` containing `k` with `h ∉ V`; the converse direction of the
place/valuation dictionary (`Place.exists_place_of_valuationSubring`) exhibits a place `Q` with
`V = Q.valuationSubring`, and `Place.mem_valuationSubring_iff` then gives
`Scheme.ord h Q.point < 0`, i.e. `h` has a pole at `Q`, contradicting `div h ≥ 0`. -/
theorem isAlgebraic_of_mem_L_zero {k : Type u} [Field k] (C : Curve k) {h : C.functionField}
    (hh : h ∈ C.L 0) : IsAlgebraic k h := by
  by_contra htr
  obtain ⟨V, hVk, hVnot⟩ := valuationRing_notMem (k := k) (K := ↥(C.functionField)) htr
  have hVk' : ∀ c : k, algebraMap k ↥(C.functionField) c ∈ V :=
    fun c => (ValuationSubring.mem_toSubring V _).mp (hVk c)
  have hVnot' : h ∉ V := fun hm => hVnot ((ValuationSubring.mem_toSubring V h).mpr hm)
  have hVne : V ≠ ⊤ := fun htop => hVnot' (htop ▸ trivial)
  obtain ⟨Q, hQ⟩ := Place.exists_place_of_valuationSubring C V hVk' hVne
  have hnotmem : h ∉ Q.valuationSubring := fun hm => hVnot' (hQ ▸ hm)
  have hord : ¬ (0 ≤ Scheme.ord h Q.point) :=
    fun h0 => hnotmem ((Place.mem_valuationSubring_iff C Q h).mpr h0)
  have hdiv : C.div h Q < 0 := by rw [Curve.div_apply]; exact lt_of_not_ge hord
  rcases (Curve.mem_L_iff C).mp hh with h0 | heff
  · exact htr (h0 ▸ isAlgebraic_zero)
  · have hge := heff Q
    simp only [Finsupp.add_apply, Finsupp.zero_apply] at hge
    linarith

/-- The Riemann–Roch space of the zero divisor consists of the constants. -/
theorem L_zero_le_span_one {k : Type u} [Field k] (C : Curve k) :
    C.L 0 ≤ Submodule.span k ({1} : Set C.functionField) := by
  intro h hh
  obtain ⟨c, hc⟩ :=
    Work.CurveBasics.Basic.eq_algebraMap_of_isAlgebraic C (isAlgebraic_of_mem_L_zero C hh)
  rw [hc, Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton 1))

/-- The Riemann–Roch space of the zero divisor is finite dimensional. -/
theorem finiteDimensional_L_zero {k : Type u} [Field k] (C : Curve k) :
    FiniteDimensional k (C.L 0) := by
  haveI : FiniteDimensional k ↥(Submodule.span k ({1} : Set C.functionField)) :=
    FiniteDimensional.span_singleton k (1 : C.functionField)
  exact Submodule.finiteDimensional_of_le (L_zero_le_span_one C)

/-! ## Adding one place at a time -/

/-- Adding a single place to a divisor preserves finite dimensionality of the Riemann–Roch
space: `L (D + [Q])` sits in the extension of `L D` by the quotient `L (D + [Q]) / L D`, which
embeds into the residue field `κ(Q)` and therefore is finite dimensional over `k`
(`finrank_quotient_add_place`). -/
theorem finiteDimensional_L_add_place {k : Type u} [Field k] (C : Curve k) {D : C.Div}
    (Q : C.Place) (hD : FiniteDimensional k (C.L D)) :
    FiniteDimensional k (C.L (D + Curve.Div.place Q)) := by
  have hle : C.L D ≤ C.L (D + Curve.Div.place Q) :=
    C.L_mono (Curve.Div.le_iff.mpr fun Q' => by
      rw [Finsupp.add_apply]
      exact le_add_of_nonneg_right (by
        rw [Curve.Div.place, Finsupp.single_apply]
        split <;> simp))
  have hiso : ↥(Submodule.comap (C.L (D + Curve.Div.place Q)).subtype (C.L D)) ≃ₗ[k] ↥(C.L D) :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, hle y.2⟩, y.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext; rfl
      map_add' := fun x y => by ext; rfl
      map_smul' := fun c x => by ext; rfl }
  haveI : FiniteDimensional k ↥(Submodule.comap (C.L (D + Curve.Div.place Q)).subtype (C.L D)) :=
    FiniteDimensional.of_injective hiso.toLinearMap hiso.injective
  have hquot := (finrank_quotient_add_place C D Q).1
  exact Module.Finite.of_submodule_quotient
    (Submodule.comap (C.L (D + Curve.Div.place Q)).subtype (C.L D))

/-- The positive part `D⁺` of a divisor: `D⁺ Q = max 0 (D Q)`. -/
noncomputable def Curve.Div.pos {k : Type u} [Field k] {C : Curve k} (D : C.Div) : C.Div :=
  D.mapRange (fun n : ℤ => max 0 n) (by simp)

@[simp]
theorem Curve.Div.pos_apply {k : Type u} [Field k] {C : Curve k} (D : C.Div) (Q : C.Place) :
    Curve.Div.pos D Q = max 0 (D Q) :=
  Finsupp.mapRange_apply

theorem Curve.Div.le_pos {k : Type u} [Field k] {C : Curve k} (D : C.Div) :
    Curve.Div.le D (Curve.Div.pos D) :=
  Curve.Div.le_iff.mpr fun Q => by rw [Curve.Div.pos_apply]; exact le_max_right 0 (D Q)

theorem Curve.Div.isEffective_pos {k : Type u} [Field k] {C : Curve k} (D : C.Div) :
    Curve.Div.IsEffective (Curve.Div.pos D) := fun Q => by
  rw [Curve.Div.pos_apply]; exact le_max_left 0 (D Q)

/-- **Effective divisors have finite dimensional Riemann–Roch space**, by induction on
`∑_Q D Q`, adding one place at a time using `finiteDimensional_L_add_place`. -/
theorem finiteDimensional_L_of_isEffective' {k : Type u} [Field k] (C : Curve k)
    (h0 : FiniteDimensional k (C.L 0)) :
    ∀ E : C.Div, Curve.Div.IsEffective E → FiniteDimensional k (C.L E) := by
  intro E
  refine Finsupp.induction₂ (motive := fun E : C.Div =>
    Curve.Div.IsEffective E → FiniteDimensional k (C.L E)) E ?_ ?_
  · intro _
    simpa using h0
  · intro a b f ha hb hf heff
    have hfeff : Curve.Div.IsEffective f := by
      intro Q
      by_cases hQ : Q = a
      · subst hQ
        rw [Finsupp.notMem_support_iff] at ha
        rw [ha]
      · have h1 : (f + Finsupp.single a b) Q = f Q := by
          rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hQ, add_zero]
        rw [← h1]
        exact heff Q
    have hb0 : 0 ≤ b := by
      have h1 : (f + Finsupp.single a b) a = b := by
        rw [Finsupp.add_apply, Finsupp.single_eq_same]
        rw [Finsupp.notMem_support_iff] at ha
        rw [ha, zero_add]
      rw [← h1]
      exact heff a
    have hfin : FiniteDimensional k (C.L f) := hf hfeff
    have hunit : ∀ n : ℕ, FiniteDimensional k (C.L (f + n • Curve.Div.place a)) := by
      intro n
      induction n with
      | zero =>
        rw [zero_smul, add_zero]
        exact hfin
      | succ n ih =>
        have heq : f + (n + 1) • Curve.Div.place a =
            (f + n • Curve.Div.place a) + Curve.Div.place a := by
          rw [add_smul, one_smul, add_assoc]
        exact heq ▸ finiteDimensional_L_add_place C a ih
    have heq : f + b.toNat • Curve.Div.place a = f + Finsupp.single a b := by
      congr 1
      rw [Curve.Div.place, Finsupp.smul_single]
      simp [Int.toNat_of_nonneg hb0]
    rw [← heq]
    exact hunit b.toNat

open Work.CurveBasics in
theorem finiteDimensional_L {k : Type*} [Field k] (C : Curve k) (D : C.Div) :
    FiniteDimensional k (C.L D) := by
  haveI : FiniteDimensional k ↥(C.L (Curve.Div.pos D)) :=
    finiteDimensional_L_of_isEffective' C (finiteDimensional_L_zero C) (Curve.Div.pos D)
      (Curve.Div.isEffective_pos D)
  exact Submodule.finiteDimensional_of_le (C.L_mono (Curve.Div.le_pos D))

end Work.CurveBasics.Linear

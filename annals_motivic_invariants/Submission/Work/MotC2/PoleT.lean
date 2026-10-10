/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotC2

# The ring of functions with no pole at the point at infinity

Let `E` be a Weierstrass curve over a field `L`, `L(E) = Func E` its function field,
`x = genX E`, `y = genY E` and `w = infW E = y/x²` the uniformizer of the point at infinity `O`.
This file introduces the `L`-subalgebra

`T E = L[1/x]_{(1/x)} + L[1/x]_{(1/x)}·w ⊆ L(E)`,

i.e. the functions whose `(1, w)`-coordinates are fractions `P(x)/Q(x)` with `deg P ≤ deg Q`:
the functions regular at the point at infinity of the `x`-line.  Its main properties are

* `mem_T_iff`: the defining property, in terms of `Tgen`;
* `infCoordRing_le_T`: the chart-at-infinity coordinate ring is contained in `T E`;
* `infPlace_le_T`: the local ring of `O` is contained in `T E` (this uses
  `Work.MotC2.PoleAux.infPlace_mem_iff` and `Work.MotC2.inv_Tgen_of_u_poly`);
* `T_unique`: the `(1, w)`-decomposition over the field `L(x)` of rational functions of `x` is
  unique (this uses `Work.MotC2.genY_not_ratFunc_genX`).

## Tags

elliptic curve, function field, pole order, chart at infinity
-/

import Mathlib
import Submission.Work.MotC2.PoleSetup
import Submission.Work.MotC2.PoleTgen
import Submission.Work.MotC2.genY_not_ratFunc_genX
import Submission.Work.MotC2.Tgen_mul_witness
import Submission.Work.MotC2.Tgen_mul_degree_bounds
import Submission.Work.MotC2.algebraMap_smul_eq_aeval
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve.Affine

set_option maxHeartbeats 1000000

namespace Work.MotC2

variable {L : Type*} [Field L]

/-- **The subalgebra of functions with no pole at the point at infinity.**  An element of `L(E)`
lies in `T E` if it is of the form `P(x)/Q(x) + (P'(x)/Q'(x))·w` with `deg P ≤ deg Q` and
`deg P' ≤ deg Q'`.  These are exactly the functions regular at `O`. -/
noncomputable def T (E : WeierstrassCurve L) : Subalgebra L (Func E) where
  carrier := {f | ∃ P Q P' Q' : Polynomial L, Q ≠ 0 ∧ Q' ≠ 0 ∧
      P.degree ≤ Q.degree ∧ P'.degree ≤ Q'.degree ∧
      f = Tgen E P Q + Tgen E P' Q' * infW E}
  zero_mem' := by
    refine ⟨0, 1, 0, 1, one_ne_zero, one_ne_zero, ?_, ?_, ?_⟩
    · simp
    · simp
    · rw [Tgen_zero_left, zero_mul, add_zero]
  one_mem' := by
    refine ⟨1, 1, 0, 1, one_ne_zero, one_ne_zero, ?_, ?_, ?_⟩
    · simp
    · simp
    · rw [Tgen_one, Tgen_zero_left, zero_mul, add_zero]
  add_mem' := by
    rintro f g ⟨P₁, Q₁, P₁', Q₁', h₁, h₁', d₁, d₁', rfl⟩
      ⟨P₂, Q₂, P₂', Q₂', h₂, h₂', d₂, d₂', rfl⟩
    refine ⟨P₁ * Q₂ + P₂ * Q₁, Q₁ * Q₂, P₁' * Q₂' + P₂' * Q₁', Q₁' * Q₂',
      mul_ne_zero h₁ h₂, mul_ne_zero h₁' h₂', degree_add_le_mul d₁ d₂, degree_add_le_mul d₁' d₂',
      ?_⟩
    rw [show (Tgen E P₁ Q₁ + Tgen E P₁' Q₁' * infW E) +
        (Tgen E P₂ Q₂ + Tgen E P₂' Q₂' * infW E) =
        (Tgen E P₁ Q₁ + Tgen E P₂ Q₂) + (Tgen E P₁' Q₁' + Tgen E P₂' Q₂') * infW E from by ring,
      Tgen_add E h₁ h₂, Tgen_add E h₁' h₂']
  mul_mem' := by
    rintro f g ⟨P₁, Q₁, P₁', Q₁', h₁, h₁', d₁, d₁', rfl⟩
      ⟨P₂, Q₂, P₂', Q₂', h₂, h₂', d₂, d₂', rfl⟩
    refine ⟨P₁ * P₂ * (Q₁' * Q₂' * X ^ 4) + P₁' * P₂' * cubicPoly E * (Q₁ * Q₂),
      Q₁ * Q₂ * (Q₁' * Q₂' * X ^ 4),
      P₁ * P₂' * (Q₂ * Q₁' * X ^ 2) + P₂ * P₁' * (Q₁ * Q₂' * X ^ 2) -
        P₁' * P₂' * linPoly E * (Q₁ * Q₂),
      Q₁ * Q₂ * (Q₁' * Q₂' * X ^ 2),
      mul_ne_zero (mul_ne_zero h₁ h₂) (mul_ne_zero (mul_ne_zero h₁' h₂') (pow_ne_zero 4 X_ne_zero)),
      mul_ne_zero (mul_ne_zero h₁ h₂) (mul_ne_zero (mul_ne_zero h₁' h₂') (pow_ne_zero 2 X_ne_zero)),
      (Tgen_mul_degree_bounds L E P₁ Q₁ P₁' Q₁' P₂ Q₂ P₂' Q₂' d₁ d₁' d₂ d₂').1,
      (Tgen_mul_degree_bounds L E P₁ Q₁ P₁' Q₁' P₂ Q₂ P₂' Q₂' d₁ d₁' d₂ d₂').2,
      ?_⟩
    rw [Tgen_mul_witness L E P₁ Q₁ P₁' Q₁' P₂ Q₂ P₂' Q₂' h₁ h₁' h₂ h₂']
  algebraMap_mem' := by
    intro c
    refine ⟨Polynomial.C c, 1, 0, 1, one_ne_zero, one_ne_zero, ?_, ?_, ?_⟩
    · rw [Polynomial.degree_one]; exact Polynomial.degree_C_le
    · simp
    · rw [Tgen_C, Tgen_zero_left, zero_mul, add_zero]

lemma mem_T_iff (E : WeierstrassCurve L) (f : Func E) :
    f ∈ T E ↔ ∃ P Q P' Q' : Polynomial L, Q ≠ 0 ∧ Q' ≠ 0 ∧
      P.degree ≤ Q.degree ∧ P'.degree ≤ Q'.degree ∧
      f = Tgen E P Q + Tgen E P' Q' * infW E :=
  Iff.rfl

/-- `w = y/x²` lies in `T E`. -/
lemma infW_mem_T (E : WeierstrassCurve L) : infW E ∈ T E := by
  refine ⟨0, 1, 1, 1, one_ne_zero, one_ne_zero, ?_, ?_, ?_⟩
  · simp
  · simp
  · rw [Tgen_zero_left, Tgen_one, zero_add, one_mul]

/-- `u = 1/x` lies in `T E`. -/
lemma infU_mem_T (E : WeierstrassCurve L) : infU E ∈ T E := by
  have hx : (X : Polynomial L) ≠ 0 := X_ne_zero
  refine ⟨1, X, 0, 1, hx, one_ne_zero, ?_, ?_, ?_⟩
  · simp
  · simp
  · rw [Tgen_zero_left, zero_mul, add_zero, Tgen_def, aeval_X, map_one, one_mul]
    rfl

/-- The chart-at-infinity coordinate ring is contained in `T E`. -/
lemma infCoordRing_le_T (E : WeierstrassCurve L) : infCoordRing E ≤ T E := by
  rw [infCoordRing]
  refine Algebra.adjoin_le_iff.mpr ?_
  rintro f (rfl | rfl)
  · exact infU_mem_T E
  · exact infW_mem_T E

/-! ## The field of rational functions of `x` and the uniqueness of the `(1, w)`-decomposition -/

/-- An element of `L(E)` is a rational function of `x` if it is a fraction `P(x)/Q(x)`. -/
def InLx (E : WeierstrassCurve L) (f : Func E) : Prop :=
  ∃ P Q : Polynomial L, Q ≠ 0 ∧ f = Tgen E P Q

lemma InLx.zero (E : WeierstrassCurve L) : InLx E 0 :=
  ⟨0, 1, one_ne_zero, by rw [Tgen_zero_left]⟩

lemma InLx.one (E : WeierstrassCurve L) : InLx E 1 :=
  ⟨1, 1, one_ne_zero, (Tgen_one E).symm⟩

lemma InLx.algebraMap (E : WeierstrassCurve L) (c : L) : InLx E (algebraMap L (Func E) c) :=
  ⟨Polynomial.C c, 1, one_ne_zero, (Tgen_C E c).symm⟩

lemma InLx.add (E : WeierstrassCurve L) {f g : Func E} (hf : InLx E f) (hg : InLx E g) :
    InLx E (f + g) := by
  obtain ⟨P₁, Q₁, h₁, rfl⟩ := hf
  obtain ⟨P₂, Q₂, h₂, rfl⟩ := hg
  exact ⟨P₁ * Q₂ + P₂ * Q₁, Q₁ * Q₂, mul_ne_zero h₁ h₂, Tgen_add E h₁ h₂⟩

lemma InLx.mul (E : WeierstrassCurve L) {f g : Func E} (hf : InLx E f) (hg : InLx E g) :
    InLx E (f * g) := by
  obtain ⟨P₁, Q₁, h₁, rfl⟩ := hf
  obtain ⟨P₂, Q₂, h₂, rfl⟩ := hg
  exact ⟨P₁ * P₂, Q₁ * Q₂, mul_ne_zero h₁ h₂, Tgen_mul E h₁ h₂⟩

lemma InLx.neg (E : WeierstrassCurve L) {f : Func E} (hf : InLx E f) : InLx E (-f) := by
  obtain ⟨P, Q, hQ, rfl⟩ := hf
  exact ⟨-P, Q, hQ, by rw [Tgen_def, Tgen_def, map_neg, neg_mul]⟩

lemma InLx.sub (E : WeierstrassCurve L) {f g : Func E} (hf : InLx E f) (hg : InLx E g) :
    InLx E (f - g) := by
  rw [sub_eq_add_neg]
  exact InLx.add E hf (InLx.neg E hg)

lemma InLx.inv (E : WeierstrassCurve L) {f : Func E} (hf : InLx E f) : InLx E f⁻¹ := by
  obtain ⟨P, Q, hQ, rfl⟩ := hf
  by_cases hP : P = 0
  · rw [hP, Tgen_zero_left, inv_zero]
    exact ⟨(0 : Polynomial L), 1, one_ne_zero, by rw [Tgen_zero_left]⟩
  · refine ⟨Q, P, hP, ?_⟩
    rw [Tgen_def, Tgen_def, mul_inv, inv_inv]
    first | refl_ring1 | ring

lemma InLx.div (E : WeierstrassCurve L) {f g : Func E} (hf : InLx E f) (hg : InLx E g) :
    InLx E (f / g) := by
  rw [div_eq_mul_inv]
  exact InLx.mul E hf (InLx.inv E hg)

lemma InLx.genX (E : WeierstrassCurve L) : InLx E (genX E) := by
  refine ⟨X, 1, one_ne_zero, ?_⟩
  rw [Tgen_def, map_one, inv_one, mul_one, aeval_X]


/-- The element `y = genY E` is **not** a rational function of `x`. -/
lemma not_InLx_genY (E : WeierstrassCurve L) [E.IsElliptic] : ¬ InLx E (genY E) := by
  rintro ⟨P, Q, hQ, hPQ⟩
  have hQ' : Polynomial.aeval (genX E) Q ≠ 0 := aeval_genX_ne_zero E hQ
  refine genY_not_ratFunc_genX L E ⟨P, Q, hQ, ?_⟩
  rw [algebraMap_polynomial_eq_aeval_genX E P, algebraMap_polynomial_eq_aeval_genX E Q, hPQ,
    Tgen_def]
  field_simp

/-- **Uniqueness of the `(1, w)`-decomposition over the field `L(x)`.** -/
theorem T_unique (E : WeierstrassCurve L) {A B A' B' : Func E} (hA : InLx E A) (hB : InLx E B)
    (hA' : InLx E A') (hB' : InLx E B') (h : A + B * infW E = A' + B' * infW E) [E.IsElliptic] :
    A = A' ∧ B = B' := by
  have h1 : (A - A') + (B - B') * infW E = 0 := by
    linear_combination (norm := first | refl_ring1 | ring1) h
  have hBne : B - B' = 0 := by
    by_contra hne
    have hw : infW E = -(A - A') / (B - B') := by
      field_simp at h1 ⊢
      linear_combination (norm := first | refl_ring1 | ring1) h1
    have hwx : infW E * (genX E) ^ 2 = genY E := infW_mul_genX_sq E
    have h2 : InLx E (-(A - A') / (B - B')) :=
      InLx.div E (InLx.neg E (InLx.sub E hA hA')) (InLx.sub E hB hB')
    have h3 : InLx E ((genX E) ^ 2) := by
      simpa [pow_two] using InLx.mul E (InLx.genX E) (InLx.genX E)
    have : InLx E (genY E) := by
      rw [← hwx, hw]
      exact InLx.mul E h2 h3
    exact not_InLx_genY E this
  refine ⟨?_, sub_eq_zero.mp hBne⟩
  have : A - A' = 0 := by
    rw [hBne, zero_mul, add_zero] at h1
    exact h1
  exact sub_eq_zero.mp this

end Work.MotC2

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotC2

# The ring of functions with no pole at infinity: generators

Let `E` be a Weierstrass curve over a field `L`, `L(E) = Func E` its function field,
`x = genX E`, `y = genY E`, `w = infW E = y/x²` the uniformizer of the point at infinity `O`.

The local ring `infPlace E` of `O` is contained in the subalgebra `T` of `L(E)` generated over `L`
by the fractions `P(x)/Q(x)` with `deg P ≤ deg Q` (the functions regular at the point at infinity
of the `x`-line) and by `w`.  This file provides the basic fractions

* `Tgen E P Q = P(x)/Q(x)`,

their first properties, and the fact that `x` is transcendental over `L` (`P(x) = 0 ↔ P = 0`).

## Tags

elliptic curve, function field, pole order, chart at infinity
-/

import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.PoleSetup
import Submission.Work.MotC2.TranslationDefs

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

/-- The fraction `P(x)/Q(x)` of the function field, for `x = genX E`. -/
noncomputable def Tgen (E : WeierstrassCurve L) (P Q : Polynomial L) : Func E :=
  Polynomial.aeval (genX E) P * (Polynomial.aeval (genX E) Q)⁻¹

lemma Tgen_def (E : WeierstrassCurve L) (P Q : Polynomial L) :
    Tgen E P Q = Polynomial.aeval (genX E) P * (Polynomial.aeval (genX E) Q)⁻¹ := rfl

/-- `x = genX E` is transcendental over `L`: a polynomial in `x` vanishes only if it is zero. -/
lemma aeval_genX_eq_zero_iff (E : WeierstrassCurve L) (P : Polynomial L) :
    Polynomial.aeval (genX E) P = 0 ↔ P = 0 :=
  ⟨fun h => (transcendental_iff.mp (transcendental_genX E)) P h,
    fun h => by rw [h, map_zero]⟩

lemma aeval_genX_ne_zero (E : WeierstrassCurve L) {P : Polynomial L} (hP : P ≠ 0) :
    Polynomial.aeval (genX E) P ≠ 0 :=
  fun h => hP ((aeval_genX_eq_zero_iff E P).mp h)

lemma Tgen_zero_left (E : WeierstrassCurve L) (Q : Polynomial L) : Tgen E 0 Q = 0 := by
  simp [Tgen]

lemma Tgen_one (E : WeierstrassCurve L) : Tgen E 1 1 = 1 := by
  simp [Tgen]

lemma Tgen_C (E : WeierstrassCurve L) (c : L) : Tgen E (Polynomial.C c) 1 = algebraMap L (Func E) c := by
  simp [Tgen, aeval_def]

lemma Tgen_add (E : WeierstrassCurve L) {P₁ P₂ Q₁ Q₂ : Polynomial L} (h₁ : Q₁ ≠ 0)
    (h₂ : Q₂ ≠ 0) :
    Tgen E P₁ Q₁ + Tgen E P₂ Q₂ = Tgen E (P₁ * Q₂ + P₂ * Q₁) (Q₁ * Q₂) := by
  have h1 : Polynomial.aeval (genX E) Q₁ ≠ 0 := aeval_genX_ne_zero E h₁
  have h2 : Polynomial.aeval (genX E) Q₂ ≠ 0 := aeval_genX_ne_zero E h₂
  simp only [Tgen, map_add, map_mul]
  field_simp

lemma Tgen_mul (E : WeierstrassCurve L) {P₁ P₂ Q₁ Q₂ : Polynomial L} (h₁ : Q₁ ≠ 0)
    (h₂ : Q₂ ≠ 0) :
    Tgen E P₁ Q₁ * Tgen E P₂ Q₂ = Tgen E (P₁ * P₂) (Q₁ * Q₂) := by
  have h1 : Polynomial.aeval (genX E) Q₁ ≠ 0 := aeval_genX_ne_zero E h₁
  have h2 : Polynomial.aeval (genX E) Q₂ ≠ 0 := aeval_genX_ne_zero E h₂
  simp only [Tgen, map_mul]
  field_simp

lemma Tgen_neg (E : WeierstrassCurve L) {P P' Q Q' : Polynomial L} (h₁ : Q ≠ 0) (h₂ : Q' ≠ 0) :
    Tgen E P Q - Tgen E P' Q' = Tgen E (P * Q' - P' * Q) (Q * Q') := by
  have h1 : Polynomial.aeval (genX E) Q ≠ 0 := aeval_genX_ne_zero E h₁
  have h2 : Polynomial.aeval (genX E) Q' ≠ 0 := aeval_genX_ne_zero E h₂
  simp only [Tgen, map_sub, map_mul]
  field_simp

/-- A fraction `P(x)/P'(x)` whose denominator has smaller degree than the numerator is a
polynomial in `x`; here we only need the degree bookkeeping for the closure of `T`. -/
lemma degree_add_le_mul {P₁ P₂ Q₁ Q₂ : Polynomial L} (h₁ : P₁.degree ≤ Q₁.degree)
    (h₂ : P₂.degree ≤ Q₂.degree) :
    (P₁ * Q₂ + P₂ * Q₁).degree ≤ (Q₁ * Q₂).degree := by
  rw [degree_mul]
  refine le_trans (degree_add_le _ _) (max_le ?_ ?_)
  · rw [degree_mul]; exact add_le_add h₁ le_rfl
  · rw [degree_mul]
    rw [add_comm (Q₁.degree) (Q₂.degree)]
    exact add_le_add h₂ le_rfl

lemma degree_mul_le_mul {P₁ P₂ Q₁ Q₂ : Polynomial L} (h₁ : P₁.degree ≤ Q₁.degree)
    (h₂ : P₂.degree ≤ Q₂.degree) : (P₁ * P₂).degree ≤ (Q₁ * Q₂).degree := by
  rw [degree_mul, degree_mul]; exact add_le_add h₁ h₂

lemma degree_mul_X_pow_le {P Q : Polynomial L} (h : P.degree ≤ Q.degree) (n : ℕ) :
    (P * Polynomial.X ^ n).degree ≤ (Q * Polynomial.X ^ n).degree := by
  rw [degree_mul, degree_mul]; exact add_le_add h le_rfl

end Work.MotC2

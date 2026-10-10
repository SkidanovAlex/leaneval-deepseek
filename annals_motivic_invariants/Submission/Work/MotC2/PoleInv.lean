/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotC2

# Inverses of elements of the chart at infinity are regular at infinity

Let `E` be a Weierstrass curve over a field `L`, `L(E) = Func E`, `u = 1/x`, `w = y/x²`, and let
`r = P₀(u) + P₁(u)·w` with `P₀, P₁ ∈ L[X]` and `P₀.coeff 0 ≠ 0`.  Then `r` is a unit of the local
ring of the point at infinity and its inverse again lies in `T E`, i.e. is of the form
`P(x)/Q(x) + (P'(x)/Q'(x))·w` with `deg P ≤ deg Q` and `deg P' ≤ deg Q'`.

The proof is the norm computation.  With `ν = infNum E = X + a₂X² + a₄X³ + a₆X⁴` and
`δ = infDen E = -(a₁X + a₃X²)` one has `w² = ν(u) + δ(u)·w`, and the conjugate
`r̄ = P₀(u) + P₁(u)δ(u) - P₁(u)w` satisfies

`r·r̄ = P₀(u)² + P₀(u)P₁(u)δ(u) - P₁(u)²ν(u) = N(u)`

for the polynomial `N = invNum E P₀ P₁ ∈ L[X]`, whose constant term is `(P₀.coeff 0)² ≠ 0`.  Hence
`r⁻¹ = r̄·N(u)⁻¹`; `r̄` is manifestly regular at infinity, and `N(u)⁻¹` is too, because
`N(1/x) = N.reverse(x)/xⁿ` with `deg N.reverse = n = deg Xⁿ` (the constant term of `N` being
nonzero means `N.reverse` has degree exactly `n`).

## Tags

elliptic curve, function field, pole order, chart at infinity
-/

import Mathlib
import Submission.Work.MotC2.PoleSetup
import Submission.Work.MotC2.PoleTgen
import Submission.Work.MotC2.PoleT
import Submission.Work.MotC2.exists_aeval_add_mul_infW
import Submission.Work.MotC2.aeval_infU_mul_pow_eq_aeval_reverse
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

/-- The numerator `N` of the norm of `P₀(u) + P₁(u)·w`. -/
noncomputable def invNum (E : WeierstrassCurve L) (P₀ P₁ : Polynomial L) : Polynomial L :=
  P₀ ^ 2 + P₀ * P₁ * infDen E - P₁ ^ 2 * infNum E

/-- The conjugate of `P₀(u) + P₁(u)·w`: the other root of the quadratic equation whose norm is
`invNum`. -/
noncomputable def invSigma (E : WeierstrassCurve L) (P₀ P₁ : Polynomial L) : Func E :=
  Polynomial.aeval (infU E) P₀ +
    Polynomial.aeval (infU E) P₁ * Polynomial.aeval (infU E) (infDen E) -
    Polynomial.aeval (infU E) P₁ * infW E

lemma eval_zero_infNum (E : WeierstrassCurve L) : (infNum E).eval 0 = 0 := by
  simp [infNum]

lemma eval_zero_infDen (E : WeierstrassCurve L) : (infDen E).eval 0 = 0 := by
  simp [infDen]

/-- The norm identity: `r·r̄ = N(u)`. -/
lemma mul_invSigma (E : WeierstrassCurve L) (P₀ P₁ : Polynomial L) :
    (Polynomial.aeval (infU E) P₀ + Polynomial.aeval (infU E) P₁ * infW E) *
        invSigma E P₀ P₁ = Polynomial.aeval (infU E) (invNum E P₀ P₁) := by
  have hrel := infW_sq_decomp E
  rw [invSigma, invNum]
  simp only [map_mul, map_add, map_sub, map_pow]
  linear_combination (norm := first | refl_ring1 | ring1) (-((Polynomial.aeval (infU E)) P₁) ^ 2) * hrel

lemma invNum_eval_zero (E : WeierstrassCurve L) (P₀ P₁ : Polynomial L) :
    (invNum E P₀ P₁).eval 0 = (P₀.eval 0) ^ 2 := by
  rw [invNum]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    eval_zero_infNum, eval_zero_infDen]
  first | refl_ring1 | ring

lemma invNum_coeff_zero (E : WeierstrassCurve L) (P₀ P₁ : Polynomial L) :
    (invNum E P₀ P₁).coeff 0 = (P₀.coeff 0) ^ 2 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, invNum_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero]

lemma invNum_ne_zero (E : WeierstrassCurve L) {P₀ P₁ : Polynomial L} (h₀ : P₀.coeff 0 ≠ 0) :
    invNum E P₀ P₁ ≠ 0 := by
  intro h
  have h2 : (P₀.coeff 0) ^ 2 = 0 := by rw [← invNum_coeff_zero E P₀ P₁, h]; simp
  exact h₀ (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h2)

lemma invNum_reverse_natDegree (E : WeierstrassCurve L) {P₀ P₁ : Polynomial L}
    (h₀ : P₀.coeff 0 ≠ 0) : (invNum E P₀ P₁).reverse.natDegree = (invNum E P₀ P₁).natDegree := by
  have hne : invNum E P₀ P₁ ≠ 0 := invNum_ne_zero E h₀
  rw [Polynomial.reverse_natDegree]
  have htd : (invNum E P₀ P₁).natTrailingDegree = 0 := by
    rw [Polynomial.natTrailingDegree_eq_zero]
    exact Or.inr (by rw [invNum_coeff_zero E P₀ P₁]; exact pow_ne_zero 2 h₀)
  rw [htd, tsub_zero]

/-- `N(u)⁻¹` is regular at infinity: it is `xⁿ / N.reverse(x)`, and `deg xⁿ = deg N.reverse`. -/
lemma inv_aeval_infU_mem_T (E : WeierstrassCurve L) {P₀ P₁ : Polynomial L}
    (h₀ : P₀.coeff 0 ≠ 0) :
    (Polynomial.aeval (infU E) (invNum E P₀ P₁))⁻¹ ∈ T E := by
  have hne : invNum E P₀ P₁ ≠ 0 := invNum_ne_zero E h₀
  have hrev : (invNum E P₀ P₁).reverse ≠ 0 := fun h =>
    hne ((Polynomial.reverse_eq_zero).mp h)
  have hrepr : Polynomial.aeval (infU E) (invNum E P₀ P₁) =
      Tgen E (invNum E P₀ P₁).reverse (X ^ (invNum E P₀ P₁).natDegree) := by
    have hx : genX E ≠ 0 := genX_ne_zero E
    rw [Tgen_def]
    simp only [map_pow, aeval_X, ← aeval_infU_mul_pow_eq_aeval_reverse]
    field_simp
  rw [hrepr]
  refine (mem_T_iff E _).mpr ⟨X ^ (invNum E P₀ P₁).natDegree, (invNum E P₀ P₁).reverse, 0, 1,
    hrev, one_ne_zero, ?_, ?_, ?_⟩
  · rw [Polynomial.degree_X_pow, ← invNum_reverse_natDegree E h₀]
    exact le_of_eq (Polynomial.degree_eq_natDegree hrev).symm
  · simp
  · rw [Tgen_zero_left, zero_mul, add_zero, Tgen_def, Tgen_def, mul_inv, inv_inv]
    first | refl_ring1 | ring

/-- `P(u)` is regular at infinity for every `P ∈ L[X]`: it equals `P.reverse(x)/xⁿ`. -/
lemma aeval_infU_mem_T (E : WeierstrassCurve L) (P : Polynomial L) :
    Polynomial.aeval (infU E) P ∈ T E := by
  by_cases hP : P = 0
  · rw [hP, map_zero]; exact Subalgebra.zero_mem _
  have hrepr : Polynomial.aeval (infU E) P = Tgen E P.reverse (X ^ P.natDegree) := by
    have hx : genX E ≠ 0 := genX_ne_zero E
    rw [Tgen_def]
    simp only [map_pow, aeval_X, ← aeval_infU_mul_pow_eq_aeval_reverse]
    field_simp
  rw [hrepr]
  refine (mem_T_iff E _).mpr ⟨P.reverse, X ^ P.natDegree, 0, 1, pow_ne_zero _ X_ne_zero,
    one_ne_zero, ?_, ?_, ?_⟩
  · rw [Polynomial.degree_X_pow]
    exact (Polynomial.natDegree_le_iff_degree_le).mp (Polynomial.reverse_natDegree_le P)
  · simp
  · rw [Tgen_zero_left, zero_mul, add_zero]

/-- An element `P₀(u) + P₁(u)·w` of the chart at infinity with `P₀.coeff 0 ≠ 0` is a unit of
`T E`. -/
lemma aeval_add_mul_infW_inv_mem_T (E : WeierstrassCurve L) {P₀ P₁ : Polynomial L}
    (h₀ : P₀.coeff 0 ≠ 0) :
    (Polynomial.aeval (infU E) P₀ + Polynomial.aeval (infU E) P₁ * infW E)⁻¹ ∈ T E := by
  have hsig : invSigma E P₀ P₁ ∈ T E := by
    refine Subalgebra.sub_mem _ (Subalgebra.add_mem _ (aeval_infU_mem_T E P₀) ?_) ?_
    · exact mul_mem (aeval_infU_mem_T E P₁) (aeval_infU_mem_T E (infDen E))
    · exact mul_mem (aeval_infU_mem_T E P₁) (infW_mem_T E)
  have hn : (Polynomial.aeval (infU E) (invNum E P₀ P₁))⁻¹ ∈ T E := inv_aeval_infU_mem_T E h₀
  have hnorm : (Polynomial.aeval (infU E) P₀ + Polynomial.aeval (infU E) P₁ * infW E) *
      invSigma E P₀ P₁ = Polynomial.aeval (infU E) (invNum E P₀ P₁) := mul_invSigma E P₀ P₁
  have hN0 : Polynomial.aeval (infU E) (invNum E P₀ P₁) ≠ 0 := by
    intro h
    have hne : invNum E P₀ P₁ ≠ 0 := invNum_ne_zero E h₀
    have hzero : Polynomial.aeval (infU E) (invNum E P₀ P₁) *
        (genX E) ^ (invNum E P₀ P₁).natDegree = 0 := by rw [h, zero_mul]
    rw [aeval_infU_mul_pow_eq_aeval_reverse] at hzero
    exact hne ((Polynomial.reverse_eq_zero).mp ((aeval_genX_eq_zero_iff E _).mp hzero))
  have hinv : (Polynomial.aeval (infU E) P₀ + Polynomial.aeval (infU E) P₁ * infW E)⁻¹ =
      invSigma E P₀ P₁ * (Polynomial.aeval (infU E) (invNum E P₀ P₁))⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← mul_assoc, hnorm, mul_inv_cancel₀ hN0]
  rw [hinv]
  exact mul_mem hsig hn

/-- **The inverse of `P₀(u) + P₁(u)·w` (with `P₀.coeff 0 ≠ 0`) lies in `T E`**, in the explicit
form of the defining property of `T E`. -/
theorem inv_Tgen_of_u_poly' (L : Type*) [Field L] (E : WeierstrassCurve L)
    {P₀ P₁ : Polynomial L} {r : Func E}
    (h : r = Polynomial.aeval (Work.MotC2.infU E) P₀ +
      Polynomial.aeval (Work.MotC2.infU E) P₁ * Work.MotC2.infW E)
    (h₀ : P₀.coeff 0 ≠ 0) (hr : r ≠ 0) :
    ∃ P Q P' Q' : Polynomial L, Q ≠ 0 ∧ Q' ≠ 0 ∧ P.degree ≤ Q.degree ∧ P'.degree ≤ Q'.degree ∧
      r⁻¹ = Work.MotC2.Tgen E P Q + Work.MotC2.Tgen E P' Q' * Work.MotC2.infW E := by
  rw [h]
  exact (mem_T_iff E _).mp (aeval_add_mul_infW_inv_mem_T E h₀)

end Work.MotC2

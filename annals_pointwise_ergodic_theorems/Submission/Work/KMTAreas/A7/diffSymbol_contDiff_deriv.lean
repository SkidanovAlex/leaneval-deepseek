/-
Copyright (c) 2026 The AnnalsChallenge authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Smoothness and derivatives of the finite "difference symbol"

For a finite family of frequencies `σ i`, coefficients `c i`, weights `ε i` and a two times
continuously differentiable `η : ℝ → ℂ`, consider the finite sum

`ξ ↦ ∑_{i ∈ D} ε i * (η (σ i * ξ) * (exp (2 π i c i ξ) - 1))`.

This file proves `Work.KMTAreas.A7.diffSymbol_contDiff_deriv`: the sum is `C²`, its first
derivative is obtained from the product rule, and its second derivative is obtained from the
product rule applied to the first derivative.  The only inputs are the pointwise `HasDerivAt`
facts for `η` and `deriv η` (`hηd`, `hηd2`) and the `C²` regularity of `η`.
-/

namespace Work.KMTAreas.A7

/-- The chain rule for `η` composed with `x ↦ σ * x`, in the form needed below. -/
lemma hasDerivAt_eta_comp {η : ℝ → ℂ} (hηd : ∀ y : ℝ, HasDerivAt η (deriv η y) y)
    (σ ξ : ℝ) : HasDerivAt (fun x : ℝ => η (σ * x)) (σ * deriv η (σ * ξ)) ξ := by
  have hL : HasDerivAt (fun x : ℝ => σ * x) σ ξ := by
    simpa using (hasDerivAt_id ξ).const_mul σ
  simpa [Function.comp_def, smul_eq_mul] using (hηd (σ * ξ)).scomp ξ hL

/-- The chain rule for `deriv η` composed with `x ↦ σ * x`. -/
lemma hasDerivAt_derivEta_comp {η : ℝ → ℂ}
    (hηd2 : ∀ y : ℝ, HasDerivAt (deriv η) (iteratedDeriv 2 η y) y) (σ ξ : ℝ) :
    HasDerivAt (fun x : ℝ => σ * deriv η (σ * x))
      (σ * (σ * iteratedDeriv 2 η (σ * ξ))) ξ := by
  have hL : HasDerivAt (fun x : ℝ => σ * x) σ ξ := by
    simpa using (hasDerivAt_id ξ).const_mul σ
  have h : HasDerivAt (fun x : ℝ => deriv η (σ * x)) (σ * iteratedDeriv 2 η (σ * ξ)) ξ := by
    simpa [Function.comp_def, smul_eq_mul] using (hηd2 (σ * ξ)).scomp ξ hL
  have h2 : HasDerivAt (fun x : ℝ => (σ : ℂ) * deriv η (σ * x))
      ((σ : ℂ) * (σ * iteratedDeriv 2 η (σ * ξ))) ξ := h.const_mul (σ : ℂ)
  simpa [mul_comm, mul_left_comm, mul_assoc] using h2

/-- The derivative of the exponential factor `x ↦ exp (2 π i c x)`. -/
lemma hasDerivAt_expLin (c ξ : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * (c * x)))
      ((2 * Real.pi * Complex.I * (c : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (c * ξ))) ξ := by
  have hL : HasDerivAt (fun x : ℝ => (2 * Real.pi * Complex.I * (c : ℂ)) * (x : ℂ))
      (2 * Real.pi * Complex.I * (c : ℂ)) ξ := by
    simpa using ((ContinuousLinearMap.hasDerivAt Complex.ofRealCLM :
      HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) ξ).const_mul
        (2 * Real.pi * Complex.I * (c : ℂ)))
  simpa [mul_comm, mul_left_comm, mul_assoc] using hL.cexp

/-- The derivative of the factor `x ↦ exp (2 π i c x) - 1`. -/
lemma hasDerivAt_wLin (c ξ : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * (c * x)) - 1)
      ((2 * Real.pi * Complex.I * (c : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (c * ξ))) ξ :=
  (hasDerivAt_expLin c ξ).sub_const 1

/-- The derivative of the factor `x ↦ (2 π i c) * exp (2 π i c x)`. -/
lemma hasDerivAt_expLin_mul (c ξ : ℝ) :
    HasDerivAt (fun x : ℝ =>
        (2 * Real.pi * Complex.I * (c : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * (c * x)))
      ((2 * Real.pi * Complex.I * (c : ℂ)) *
        ((2 * Real.pi * Complex.I * (c : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * (c * ξ)))) ξ :=
  (hasDerivAt_expLin c ξ).const_mul _

/-- `C²`-regularity of `η` composed with `x ↦ σ * x`. -/
lemma contDiff_eta_comp {η : ℝ → ℂ} (hηcd : ContDiff ℝ 2 η) (σ : ℝ) :
    ContDiff ℝ 2 (fun x : ℝ => η (σ * x)) :=
  hηcd.comp (contDiff_const.mul contDiff_id)

/-- `C²`-regularity of the factor `x ↦ exp (2 π i c x) - 1`. -/
lemma contDiff_wLin (c : ℝ) :
    ContDiff ℝ 2 (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * (c * x)) - 1) := by
  have h : ContDiff ℝ 2 (fun x : ℝ => (2 * Real.pi * Complex.I * (c : ℂ)) * (x : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  have h2 : ContDiff ℝ 2
      (fun x : ℝ => Complex.exp ((2 * Real.pi * Complex.I * (c : ℂ)) * (x : ℂ))) :=
    Complex.contDiff_exp.comp h
  have h3 : ContDiff ℝ 2
      (fun x : ℝ => Complex.exp ((2 * Real.pi * Complex.I * (c : ℂ)) * (x : ℂ)) - 1) :=
    h2.sub (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => (1 : ℂ)))
  simpa [Complex.ofReal_mul, mul_assoc] using h3

/-- The derivative of a finite pointwise sum of complex-valued functions is the sum of the
derivatives, in the lambda-calculus form used in the target statement. -/
lemma hasDerivAt_sum_lambda {ι : Type*} (D : Finset ι) (A : ι → ℝ → ℂ) (A' : ι → ℂ)
    (ξ : ℝ) (h : ∀ i ∈ D, HasDerivAt (A i) (A' i) ξ) :
    HasDerivAt (fun x : ℝ => ∑ i ∈ D, A i x) (∑ i ∈ D, A' i) ξ := by
  convert HasDerivAt.sum h using 1
  funext x
  rw [Finset.sum_apply]

/-- Smoothness and the first two derivatives of the finite difference symbol
`ξ ↦ ∑_{i ∈ D} ε i * (η (σ i * ξ) * (exp (2 π i c i ξ) - 1))`. -/
theorem diffSymbol_contDiff_deriv (η : ℝ → ℂ) (hηcd : ContDiff ℝ 2 η)
    (hηd : ∀ y : ℝ, HasDerivAt η (deriv η y) y)
    (hηd2 : ∀ y : ℝ, HasDerivAt (deriv η) (iteratedDeriv 2 η y) y)
    {ι : Type*} (D : Finset ι) (σ c : ι → ℝ) (ε : ι → ℂ) :
    ContDiff ℝ 2 (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1))) ∧
    (∀ ξ : ℝ, HasDerivAt (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)))
      (∑ i ∈ D, ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
        + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) ξ) ∧
    (∀ ξ : ℝ, HasDerivAt
      (fun ξ : ℝ => ∑ i ∈ D, ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
        + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))
      (∑ i ∈ D, ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
        + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
        + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
        + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))) ξ) := by
  -- First derivative of the symbol.
  have hG : ∀ ξ : ℝ, HasDerivAt
      (fun ξ : ℝ => ∑ i ∈ D, ε i * (η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)))
      (∑ i ∈ D, ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
        + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) ξ := by
    intro ξ
    refine hasDerivAt_sum_lambda D
      (fun i x => ε i * (η (σ i * x) * (Complex.exp (2 * Real.pi * Complex.I * (c i * x)) - 1)))
      (fun i => ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
        + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ))))) ξ ?_
    intro i _
    exact ((hasDerivAt_eta_comp hηd (σ i) ξ).mul (hasDerivAt_wLin (c i) ξ)).const_mul (ε i)
  -- First derivative of the first derivative.
  have hG' : ∀ ξ : ℝ, HasDerivAt
      (fun ξ : ℝ => ∑ i ∈ D, ε i * (σ i * deriv η (σ i * ξ) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
        + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))
      (∑ i ∈ D, ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
        + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
        + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
        + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))) ξ := by
    intro ξ
    refine hasDerivAt_sum_lambda D
      (fun i x => ε i * (σ i * deriv η (σ i * x) * (Complex.exp (2 * Real.pi * Complex.I * (c i * x)) - 1)
        + η (σ i * x) * ((2 * Real.pi * Complex.I * (c i : ℂ)) * Complex.exp (2 * Real.pi * Complex.I * (c i * x)))))
      (fun i => ε i * (σ i * (σ i * iteratedDeriv 2 η (σ i * ξ)) * (Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)) - 1)
        + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
        + (σ i * deriv η (σ i * ξ)) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))
        + η (σ i * ξ) * ((2 * Real.pi * Complex.I * c i) * ((2 * Real.pi * Complex.I * c i) * Complex.exp (2 * Real.pi * Complex.I * (c i * ξ)))))) ξ ?_
    intro i _
    have hA := hasDerivAt_derivEta_comp hηd2 (σ i) ξ
    have hB := hasDerivAt_expLin_mul (c i) ξ
    have h1 := hasDerivAt_eta_comp hηd (σ i) ξ
    have h2 := hasDerivAt_wLin (c i) ξ
    have hT1 := hA.mul h2
    have hT2 := h1.mul hB
    exact ((hT1.add hT2).const_mul (ε i)).congr_deriv (by ring)
  refine ⟨?_, hG, hG'⟩
  -- `C²`-regularity.
  refine ContDiff.sum (fun i _ => ?_)
  exact ContDiff.const_smul (ε i)
    ((contDiff_eta_comp hηcd (σ i)).mul (contDiff_wLin (c i)))

end Work.KMTAreas.A7

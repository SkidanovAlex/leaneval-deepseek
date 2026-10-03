import Mathlib

set_option linter.unusedVariables false

namespace Work.KMTAreas.A7rand

/-- The symbol `ξ ↦ ∑_k D k * η (2^{s k} ξ)` of a lacunary (dyadic) sum: its first and second
derivatives are obtained by differentiating termwise, the factor `2^{s k}` appearing once for the
first derivative and twice for the second. -/
theorem symbol_deriv_formulas (η : ℝ → ℂ) (hηcd : ContDiff ℝ 2 η)
    (hηd : ∀ y : ℝ, HasDerivAt η (deriv η y) y)
    (hηd2 : ∀ y : ℝ, HasDerivAt (deriv η) (iteratedDeriv 2 η y) y)
    (s : ℕ → ℕ) (K : ℕ) (D : ℕ → ℂ) :
    (∀ ξ : ℝ, deriv (fun ξ : ℝ => ∑ k ∈ Finset.range K, D k * η ((2 : ℝ) ^ (s k) * ξ)) ξ
      = ∑ k ∈ Finset.range K, D k * ((2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ))) ∧
    (∀ ξ : ℝ, iteratedDeriv 2 (fun ξ : ℝ => ∑ k ∈ Finset.range K, D k * η ((2 : ℝ) ^ (s k) * ξ)) ξ
      = ∑ k ∈ Finset.range K,
          D k * ((2 : ℝ) ^ (s k) * ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ)))) := by
  -- the first derivative, termwise
  have hfirst : ∀ (ξ : ℝ),
      HasDerivAt (fun ξ : ℝ => ∑ k ∈ Finset.range K, D k * η ((2 : ℝ) ^ (s k) * ξ))
        (∑ k ∈ Finset.range K, D k * ((2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ))) ξ := by
    intro ξ
    apply HasDerivAt.fun_sum
    intro k hk
    have h1 : HasDerivAt (fun ξ : ℝ => η ((2 : ℝ) ^ (s k) * ξ))
        ((2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)) ξ := by
      have := HasDerivAt.scomp ξ (hηd ((2 : ℝ) ^ (s k) * ξ))
        (hasDerivAt_const_mul (c := (2 : ℝ) ^ (s k)))
      simpa [Function.comp_def, Complex.real_smul] using this
    simpa using h1.const_mul (D k)
  -- the derivative of the termwise first derivative: the second derivative
  have hsecond : ∀ (ξ : ℝ),
      HasDerivAt
        (fun ξ : ℝ => ∑ k ∈ Finset.range K, D k * ((2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)))
        (∑ k ∈ Finset.range K,
          D k * ((2 : ℝ) ^ (s k) * ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ)))) ξ := by
    intro ξ
    apply HasDerivAt.fun_sum
    intro k hk
    have h1 : HasDerivAt (fun ξ : ℝ => deriv η ((2 : ℝ) ^ (s k) * ξ))
        ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ)) ξ := by
      have := HasDerivAt.scomp ξ (hηd2 ((2 : ℝ) ^ (s k) * ξ))
        (hasDerivAt_const_mul (c := (2 : ℝ) ^ (s k)))
      simpa [Function.comp_def, Complex.real_smul] using this
    have h2 : HasDerivAt (fun ξ : ℝ => (2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ))
        ((2 : ℝ) ^ (s k) * ((2 : ℝ) ^ (s k) * iteratedDeriv 2 η ((2 : ℝ) ^ (s k) * ξ))) ξ := by
      simpa using h1.const_mul (((2 : ℝ) ^ (s k)) : ℂ)
    simpa using h2.const_mul (D k)
  constructor
  · intro ξ
    exact (hfirst ξ).deriv
  · intro ξ
    have hd : deriv (fun ξ : ℝ => ∑ k ∈ Finset.range K, D k * η ((2 : ℝ) ^ (s k) * ξ))
        = fun ξ : ℝ => ∑ k ∈ Finset.range K, D k * ((2 : ℝ) ^ (s k) * deriv η ((2 : ℝ) ^ (s k) * ξ)) :=
      funext fun ξ => (hfirst ξ).deriv
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd]
    exact (hsecond ξ).deriv

end Work.KMTAreas.A7rand

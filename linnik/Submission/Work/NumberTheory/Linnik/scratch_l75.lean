import Mathlib
import Submission.Commons.Analysis.Integral.extremal_cosine_integral
import Submission.Commons.Analysis.Integral.extremal_cosh_integral
import Submission.Commons.Analysis.Integral.extremal_cosine_reflected_integral
import Submission.Commons.Analysis.Integral.extremal_polynomial_integral
import Submission.Commons.Analysis.Integral.extremal_quadratic_form_cos
import Submission.Commons.Analysis.Integral.extremal_quadratic_form_cosh

open Real MeasureTheory intervalIntegral

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.Linnik

/-- **Heath-Brown Lemma 7.5, `0 < k < 3` (the `cos` family of Lemma 7.1).**

If `sin²θ = k(1 - θ cot θ)` with `0 < θ < π/2`, then the extremal function `f` of Lemma 7.1
satisfies `F(-lam) - k F(0) = -lam⁻¹ f(0) cos²θ`.  This is the identity that §8 uses (with `k = 2`) to
convert Lemma 6.4 into a lower bound for `lam'`. -/
theorem extremal_cosine_lemma75 {θ lam k : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hk0 : 0 < k) (hk3 : k < 3) (hlam : 0 < lam)
    (hcon : Real.sin θ ^ 2 = k * (1 - θ * (Real.cos θ / Real.sin θ))) :
    let ζ : ℝ := lam * Real.tan θ
    let γ : ℝ := θ / ζ
    let f : ℝ → ℝ := fun x => lam * (1 + Real.tan θ ^ 2) *
      (lam * (1 + Real.tan θ ^ 2) * (γ - x / 2) * Real.cos (ζ * x) + lam * (2 * γ - x)
        + Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ)
        - 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ))
    (∫ x in (0:ℝ)..(2 * γ), Real.exp (lam * x) * f x)
      - k * (∫ x in (0:ℝ)..(2 * γ), f x) = -(lam⁻¹) * f 0 * Real.cos θ ^ 2 := by
  have h := Commons.Analysis.Integral.extremal_cosine_integral hθ0 hθ1 hlam
  have hq := Commons.Analysis.Integral.extremal_quadratic_form_cos hθ0 hθ1 hk0 hk3 hcon
  obtain ⟨h1, h2, h3⟩ := h
  simp only [h1, h2, h3]
  rw [hq]
  field_simp

/-- **Heath-Brown Lemma 7.5, `k > 3` (the `cosh` family of Lemma 7.3).**

If `sinh²θ = k(θ coth θ - 1)`, then the extremal function `f` of Lemma 7.3 satisfies
`F(-lam) - k F(0) = -lam⁻¹ f(0) cosh²θ`. -/
theorem extremal_cosh_lemma75 {θ lam k : ℝ} (hθ0 : 0 < θ)
    (hk3 : 3 < k) (hlam : 0 < lam)
    (hcon : Real.sinh θ ^ 2 = k * (θ * (Real.cosh θ / Real.sinh θ) - 1)) :
    let ρ : ℝ := lam * Real.tanh θ
    let γ : ℝ := θ / ρ
    let f : ℝ → ℝ := fun x => lam * (1 - Real.tanh θ ^ 2) *
      (lam * (1 - Real.tanh θ ^ 2) * (γ - x / 2) * Real.cosh (ρ * x) + lam * (2 * γ - x)
        + Real.sinh (2 * θ - ρ * x) / Real.sinh (2 * θ)
        - 2 * (1 + Real.sinh (θ - ρ * x) / Real.sinh θ))
    (∫ x in (0:ℝ)..(2 * γ), Real.exp (lam * x) * f x)
      - k * (∫ x in (0:ℝ)..(2 * γ), f x) = -(lam⁻¹) * f 0 * Real.cosh θ ^ 2 := by
  have h := Commons.Analysis.Integral.extremal_cosh_integral hθ0 hlam
  have hq := Commons.Analysis.Integral.extremal_quadratic_form_cosh hθ0 hk3 hcon
  obtain ⟨h1, h2, h3⟩ := h
  simp only [h1, h2, h3]
  rw [hq]
  field_simp

/-- **Heath-Brown Lemma 7.5, `k = 3` (the polynomial family of Lemma 7.2).**

The extremal function `f(x) = (lam/30)(2-lamx)³(4+6lamx+lam²x²)` of Lemma 7.2 satisfies
`F(-lam) - 3 F(0) = -lam⁻¹ f(0)`. -/
theorem extremal_polynomial_lemma75 {lam : ℝ} (hlam : 0 < lam) :
    let f : ℝ → ℝ := fun x => (lam/30) * (2 - lam*x)^3 * (4 + 6*lam*x + (lam*x)^2)
    (∫ x in (0:ℝ)..(2/lam), Real.exp (lam * x) * f x)
      - 3 * (∫ x in (0:ℝ)..(2/lam), f x) = -(lam⁻¹) * f 0 := by
  have h := Commons.Analysis.Integral.extremal_polynomial_integral hlam
  obtain ⟨h1, h2⟩ := h
  simp only [h1, h2]
  have hf0 : (lam/30) * (2 - lam*0)^3 * (4 + 6*lam*0 + (lam*0)^2) = 16*lam/15 := by ring
  rw [hf0]
  field_simp
  ring

end Commons.NumberTheory.Linnik

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Commons.NumberTheory.Linnik.Ksum_positivity

namespace Commons.NumberTheory.Linnik

theorem lemma6_2_assembly {q : ℕ} [NeZero q] {f : ℝ → ℝ} {x₀ L β₁ γ₁ γ₂ lam₁ lam₂ ε : ℝ}
    (hf : ∀ t, 0 ≤ f t) (hx₀ : 0 < x₀) (hL : 0 < L)
    (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0) (χ₁ χ₂ : DirichletCharacter ℂ q)
    (h0 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ (β₁ : ℂ)).re
              * f (Real.log n / L))
          ≤ L * (∫ t in (0:ℝ)..x₀, Real.exp (lam₁ * t) * f t) + f 0 * ε * L)
    (h1 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            (χ₁ (n : ZMod q) / (n : ℂ) ^ ((β₁ : ℂ) + (γ₁ : ℂ) * Complex.I)).re
              * f (Real.log n / L))
          ≤ -L * (∫ t in (0:ℝ)..x₀, f t) + f 0 * ((1:ℝ)/6 + ε) * L)
    (h2 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            (χ₂ (n : ZMod q) / (n : ℂ) ^ ((β₁ : ℂ) + (γ₂ : ℂ) * Complex.I)).re
              * f (Real.log n / L))
          ≤ -L * (∫ t in (0:ℝ)..x₀, Real.exp (-(lam₂ - lam₁) * t) * f t)
              + f 0 * ((1:ℝ)/6 + ε) * L)
    (h3 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₁ * χ₂) (n : ZMod q) /
              (n : ℂ) ^ ((β₁ : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I)).re
              * f (Real.log n / L))
          ≤ f 0 * ((1:ℝ)/6 + ε) * L)
    (h4 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ₁ * χ₂⁻¹) (n : ZMod q) /
              (n : ℂ) ^ ((β₁ : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I)).re
              * f (Real.log n / L))
          ≤ f 0 * ((1:ℝ)/6 + ε) * L) :
    0 ≤ (∫ t in (0:ℝ)..x₀, Real.exp (lam₁ * t) * f t) - (∫ t in (0:ℝ)..x₀, f t)
      - (∫ t in (0:ℝ)..x₀, Real.exp (-(lam₂ - lam₁) * t) * f t) + f 0 * ((1:ℝ)/2 + 4 * ε) := by
  -- The five-term combination of §6 is non-negative (HB (6.3)/(6.4)).
  have hK := Ksum_positivity (q := q) (x₀ := x₀) (L := L) (β := β₁)
    (γ₁ := γ₁) (γ₂ := γ₂) hf hx₀ hL hsupp χ₁ χ₂
  -- Each term is bounded above by the corresponding hypothesis; summing:
  have hmain : 0 ≤ L * ((∫ t in (0:ℝ)..x₀, Real.exp (lam₁ * t) * f t)
        - (∫ t in (0:ℝ)..x₀, f t)
        - (∫ t in (0:ℝ)..x₀, Real.exp (-(lam₂ - lam₁) * t) * f t)
        + f 0 * ((1:ℝ)/2 + 4 * ε)) := by
    linarith [hK, h0, h1, h2, h3, h4]
  exact (mul_nonneg_iff_of_pos_left hL).mp hmain

end Commons.NumberTheory.Linnik
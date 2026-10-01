import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_wsmem_ne

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory
open scoped Real Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Commons.NumberTheory.Linnik

/-- **HB (6.13), the window half.**  With `f ≥ 0` on `[0,x₀]` and `β'` maximal for the zeros of
`L(·,χ)` of imaginary part `≤ 10L`, the window sum at `s = β'` dominates the single contribution of
the zero `ρ₁ = β₁`:
`ℜF((β'-β₁)L) ≤ Σ_{|1-ρ|≤δ} D(ρ) ℜF((β'-ρ)L)`.
Here `ρ₁ = β₁` is **real**, so `(β'-β₁)L ≤ 0` is real and the single term is non-negative — this is
not a consequence of Condition 2 (which only applies at `Re z ≥ 0`). -/
theorem windowSum_ge_single_real {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {f : ℝ → ℝ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hfnn : ∀ t ∈ Set.Icc (0:ℝ) x₀, 0 ≤ f t)
    (hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
    {L δ β₁ β' : ℝ} (hL : 0 ≤ L) (hβ'β₁ : β' ≤ β₁)
    (hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) (β₁ : ℂ) ≠ 0)
    (hwin : ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - (β₁ : ℂ)‖ ≤ δ)
    (hzero : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ (β₁ : ℂ) → u.re ≤ β') :
    ((∫ t in (0:ℝ)..x₀,
        Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ then
          ((∫ t in (0:ℝ)..x₀,
            Complex.exp (-((((β' : ℂ) - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) else 0) := by
  have hρnn : 0 ≤ ((∫ t in (0:ℝ)..x₀,
      Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) := by
    have hpt : ∀ t : ℝ, Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * L) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)
        = ((Real.exp (-(((β' - β₁) * L) * t)) * f t : ℝ) : ℂ) := by
      intro t
      have h1 : -((((β' : ℂ) - (β₁ : ℂ)) * L) * (t : ℂ)) = ((-(((β' - β₁) * L) * t) : ℝ) : ℂ) := by
        push_cast; ring
      rw [h1, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
    simp only [hpt]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
    apply intervalIntegral.integral_nonneg hx₀.le
    intro t ht
    exact mul_nonneg (Real.exp_nonneg _) (hfnn t ht)
  have hzero' : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ (β₁ : ℂ) → u.re ≤ (β' : ℂ).re := by
    intro u hu hw hne
    simpa using hzero u hu hw hne
  exact le_windowSum_of_mem_ne χ hχ hL hF hdiv hwin hρnn hzero'

end Commons.NumberTheory.Linnik

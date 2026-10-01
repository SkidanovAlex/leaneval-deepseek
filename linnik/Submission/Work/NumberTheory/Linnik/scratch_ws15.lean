import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_wsadd
import Submission.Work.NumberTheory.Linnik.scratch_l63

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory
open scoped Real Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Commons.NumberTheory.Linnik

/-- **HB (6.14)+(6.15).**  With `ρ' = β' + iγ'` a window zero of multiplicity one at `s = ρ'`,
`ρ₁ = β₁` a zero with `Re ρ₁ ≥ Re ρ'`, `D(ρ₁) = 1`, and every other window zero to the left of `s`:
if the (6.14) decay `|ℜF((s-ρ₁)L)| ≤ f(0)ε` holds whenever `ρ₁` misses the window, then
`ℜF(0) + ℜF((s-ρ₁)L) - f(0)ε ≤ W(s)`. -/
theorem windowSum_ge_pair {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {f : ℝ → ℝ} {x₀ L : ℝ} (hx₀ : 0 < x₀) (hfnn : ∀ t ∈ Set.Icc (0:ℝ) x₀, 0 ≤ f t)
    (hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
    {δ ε β₁ β' γ' : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hβ' : |1 - β'| ≤ δ) (hne : ((β' : ℂ) + (γ' : ℂ) * Complex.I) ≠ (β₁ : ℂ))
    (hf0 : 0 ≤ f 0)
    (hdiv₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2))) (β₁ : ℂ) ≠ 0)
    (hdiv' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2)))
        ((β' : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0)
    (hmult₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2))) (β₁ : ℂ) = 1)
    (h0nn : 0 ≤ (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) -
          ((β' : ℂ) + (γ' : ℂ) * Complex.I)) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
    (h614 : ‖(1:ℂ) + (((β' : ℂ) + (γ' : ℂ) * Complex.I).im : ℂ) * Complex.I - (β₁ : ℂ)‖ ≤ δ ∨
      (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) * L) * (t : ℂ))) *
        ((f t : ℝ) : ℂ)).re ≤ f 0 * ε)
    (hzero : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (((β' : ℂ) + (γ' : ℂ) * Complex.I).im : ℂ) * Complex.I - u‖ ≤ δ →
        u ≠ ((β' : ℂ) + (γ' : ℂ) * Complex.I) → u ≠ (β₁ : ℂ) → u.re ≤ β') :
    (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) -
          ((β' : ℂ) + (γ' : ℂ) * Complex.I)) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
      + (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) * L) * (t : ℂ))) *
        ((f t : ℝ) : ℂ)).re - f 0 * ε
      ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (((β' : ℂ) + (γ' : ℂ) * Complex.I).im : ℂ) * Complex.I - u‖ ≤ δ then
          ((∫ t in (0:ℝ)..x₀,
            Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - u) * L) * (t : ℂ))) *
            ((f t : ℝ) : ℂ)).re) else 0) := by
  have hρ'win : ‖(1:ℂ) + (((β' : ℂ) + (γ' : ℂ) * Complex.I).im : ℂ) * Complex.I -
      ((β' : ℂ) + (γ' : ℂ) * Complex.I)‖ ≤ δ := by
    have h1 : (1:ℂ) + (((β' : ℂ) + (γ' : ℂ) * Complex.I).im : ℂ) * Complex.I -
        ((β' : ℂ) + (γ' : ℂ) * Complex.I) = ((1 - β' : ℝ) : ℂ) := by
      simp
    rw [h1, norm_real, Real.norm_eq_abs]
    exact hβ'
  have hmain := le_windowSum_of_mem_add χ hχ (f := f) (x₀ := x₀) (L := L) (C := f 0 * ε)
    (s := (β' : ℂ) + (γ' : ℂ) * Complex.I) (ρ := (β' : ℂ) + (γ' : ℂ) * Complex.I)
    (σ := (β₁ : ℂ)) (δ := δ)
    hL hF hne (mul_nonneg hf0 hε) hdiv' hρ'win
    (by simpa only [sub_self, zero_mul, neg_zero, Complex.exp_zero, one_mul] using h0nn)
    hmult₁ h614 (fun u hu hw h1 h2 => by
      have := hzero u hu hw h1 h2
      simpa using this)
  simpa only [sub_self, zero_mul, neg_zero, Complex.exp_zero, one_mul] using hmain

end Commons.NumberTheory.Linnik

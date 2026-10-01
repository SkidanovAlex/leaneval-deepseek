import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound

namespace Commons.NumberTheory.Linnik

open Complex

/-- **Nonnegativity of the windowed divisor sum (non-principal case).**

If `χ` is a non-principal Dirichlet character, the completed `L`-function
`Λ = completedLFunction χ` is entire, so every coefficient
`MeromorphicOn.divisor Λ (closedBall 0 (|s.im| + 2)) u` is a *nonnegative* integer.
Consequently every summand of the window sum `∑ᶠ u, D u · g u` is `≥ 0`: the factor
`g u` vanishes outside the window `‖1 + s.im·i - u‖ ≤ δ`, and inside the window
`hzero` puts `u` to the left of `s`, so `Re ((s - u) L) ≥ 0` and `hF` gives
`Re ∫₀^{x₀} e^{-((s-u)L)t} f t dt ≥ 0`. -/
theorem windowSum_nonneg_nonPrincipal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {f : ℝ → ℝ} {x₀ L : ℝ} {s : ℂ} {δ : ℝ} (hL : 0 ≤ L)
    (hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
    (hzero : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ s.re) :
    0 ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
        else 0) := by
  classical
  -- `Λ` is entire, hence the divisor on the closed ball is nonnegative
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (|s.im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  set F : ℂ → ℝ := fun u =>
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
          ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
          else 0) with hFdef
  change 0 ≤ ∑ᶠ u : ℂ, F u
  apply finsum_nonneg
  intro u
  simp only [hFdef]
  by_cases hDu : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|s.im| + 2))) u = 0
  · simp [hDu]
  by_cases hwin : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
  · rw [if_pos hwin]
    have hre : u.re ≤ s.re := hzero u hDu hwin
    have hDnn : (0 : ℝ) ≤ (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) : ℝ) :=
      Commons.Analysis.Complex.divisor_nonneg_on_closedBall han u
    have hz : 0 ≤ (((s - u) * L : ℂ)).re := by
      rw [Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      have : 0 ≤ (s - u).re := by rw [Complex.sub_re]; linarith
      exact mul_nonneg this hL
    exact mul_nonneg hDnn (hF ((s - u) * L) hz)
  · rw [if_neg hwin, mul_zero]

end Commons.NumberTheory.Linnik
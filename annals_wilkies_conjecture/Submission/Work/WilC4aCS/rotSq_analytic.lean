import Mathlib
import Submission.Work.WilC4aCS.Defs

namespace Work.WilC4aCS

/-- The directional derivatives `ddir ψ v = fun x => fderiv ℝ ψ x v` are analytic whenever `ψ` is. -/
lemma ddir_analytic {m : ℕ} {ψ : (Fin m → ℝ) → ℝ} {x₀ : Fin m → ℝ} (h : AnalyticAt ℝ ψ x₀)
    (v : Fin m → ℝ) : AnalyticAt ℝ (ddir ψ v) x₀ :=
  ((ContinuousLinearMap.apply ℝ ℝ v).analyticAt (fderiv ℝ ψ x₀)).comp h.fderiv

theorem rotSq_analytic {m : ℕ} {ψ : (Fin m → ℝ) → ℝ} {x₀ : Fin m → ℝ} (h : AnalyticAt ℝ ψ x₀) :
    AnalyticAt ℝ (Work.WilC4aCS.rotSq ψ) x₀ := by
  -- `rotSq ψ` is a finite sum of squares of analytic functions: each summand is
  -- `(x_a · ∂_b ψ − x_b · ∂_a ψ)²`, a product/difference of the coordinate functions
  -- `x ↦ x_i` (continuous linear, hence analytic) and the analytic directional derivatives.
  have hkey : rotSq ψ = ∑ p : Fin m × Fin m, fun x : Fin m → ℝ =>
      (x p.1 * ddir ψ (Pi.single p.2 1) x - x p.2 * ddir ψ (Pi.single p.1 1) x) ^ 2 := by
    funext x; simp [rotSq]
  rw [hkey]
  refine Finset.analyticAt_sum Finset.univ (fun p _ => ?_)
  have h1 : AnalyticAt ℝ
      (fun x : Fin m → ℝ => x p.1 * ddir ψ (Pi.single p.2 1) x) x₀ :=
    ((ContinuousLinearMap.proj p.1).analyticAt x₀).mul (ddir_analytic h _)
  have h2 : AnalyticAt ℝ
      (fun x : Fin m → ℝ => x p.2 * ddir ψ (Pi.single p.1 1) x) x₀ :=
    ((ContinuousLinearMap.proj p.2).analyticAt x₀).mul (ddir_analytic h _)
  exact (h1.sub h2).pow 2

end Work.WilC4aCS

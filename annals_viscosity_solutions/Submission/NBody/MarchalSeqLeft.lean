import Submission.NBody.MarchalSeqWindow
import Submission.NBody.MarchalBumpTwoSided

/-!
# The left window

`seq_action_window_bound` (`MarchalSeqWindow`) controls the window `[t₀, t₀ + λT]` to the *right* of
the collision.  The left window `[t₀ - λT, t₀]` is handled by reflecting the curve about `t₀`:
with `γL := reflectCurve γ t₀` (`γL u = γ (t₀ - u)`) and the collision moved to the origin,

  `∫_{t₀-λT}^{t₀} (L(γ̃) - L(γ)) = ∫_0^{λT} (L(γ̃_L) - L(γ_L))`

where `γ̃_L` is the bump of `γ_L` at `t₀ = 0`.  The pointwise identity on the integrands is
`bumpCurve_reflect` + `deriv_bumpCurve_reflect` + `deriv_reflectCurve` + the parity `lagR_neg`.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- The pointwise identity between the left bump integrand at `t₀ - u` and the reflected bump
integrand at `u`. -/
lemma lagR_bumpCurve_reflect_eq {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (h : ℝ)
    {k : Finset (Fin N)} {i₀ : Fin N} (δ : E) (T lam t₀ : ℝ) (γ : ℝ → EN E N) (u : ℝ) :
    (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ (t₀ - u))
        (deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ - u))
      - lagR m h (γ (t₀ - u)) (deriv γ (t₀ - u)))
    = (lagR m h (bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀) u)
        (deriv (bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀)) u)
      - lagR m h (reflectCurve γ t₀ u) (deriv (reflectCurve γ t₀) u)) := by
  have h1 : deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ - u)
      = -deriv (bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀)) u := by
    rw [deriv_bumpCurve_reflect δ T lam t₀ γ u, neg_neg]
  have h2 : deriv γ (t₀ - u) = -deriv (reflectCurve γ t₀) u := by
    rw [deriv_reflectCurve γ t₀ u, neg_neg]
  have h3 : bumpCurve m k i₀ δ T lam t₀ γ (t₀ - u)
      = bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀) u :=
    (bumpCurve_reflect δ T lam t₀ γ u).symm
  have h4 : γ (t₀ - u) = reflectCurve γ t₀ u := rfl
  rw [h3, h4, h1, h2, lagR_neg m hm h, lagR_neg m hm h]

/-- **The left window is the reflected window.** -/
lemma left_window_eq {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (h : ℝ)
    {k : Finset (Fin N)} {i₀ : Fin N} (δ : E) (T lam t₀ : ℝ) (γ : ℝ → EN E N) :
    (∫ t in (t₀ - lam * T)..t₀, (lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
        (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t)))
      = ∫ u in (0:ℝ)..(lam * T),
          (lagR m h (bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀) u)
              (deriv (bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀)) u)
            - lagR m h (reflectCurve γ t₀ u) (deriv (reflectCurve γ t₀) u)) := by
  rw [intervalIntegral_reflect
    (fun t => lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
      (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t) - lagR m h (γ t) (deriv γ t)) t₀ lam T]
  refine intervalIntegral.integral_congr fun u _ => ?_
  exact lagR_bumpCurve_reflect_eq hm h δ T lam t₀ γ u

end Submission.NBody

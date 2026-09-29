import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Analysis.Analytic

/-!
# Geometric growth of the Taylor coefficients of an analytic function

If `f : ℝ → ℝ` is analytic at `0`, then the coefficients
`aₙ = f⁽ⁿ⁾(0) / n!` of its Taylor series at `0` grow at most
geometrically: there are `C > 0` and `ρ > 0` with
`|aₙ| ≤ C * ρⁿ` for every `n`.

The proof is by attaching to `f` its Taylor formal power series
`p = FormalMultilinearSeries.ofScalars ℝ (fun n ↦ f⁽ⁿ⁾(0) / n!)`.
Analyticity gives `HasFPowerSeriesAt f p 0` (this is the standard
fact that an analytic function agrees with its Taylor series in a
neighbourhood, over a real-closed-like field), hence `0 < p.radius`;
the general coefficient-growth lemma for formal multilinear series
(`le_mul_pow_of_radius_pos`) then gives the desired geometric bound.
-/

theorem coeff_growth_of_analyticAt {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧
      ∀ n : ℕ, |iteratedDeriv n f 0 / (n.factorial : ℝ)| ≤ C * ρ ^ n := by
  classical
  let p : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ
      (fun n => iteratedDeriv n f 0 / (n.factorial : ℝ))
  have hfp : HasFPowerSeriesAt f p 0 := by
    simpa [p] using (AnalyticAt.hasFPowerSeriesAt (𝕜 := ℝ) hf)
  have hp_radius : 0 < p.radius := hfp.radius_pos
  rcases p.le_mul_pow_of_radius_pos hp_radius with ⟨C, ρ, hC, hρ, hnorm⟩
  refine ⟨C, ρ, hC, hρ, ?_⟩
  intro n
  have hc : p.coeff n = iteratedDeriv n f 0 / (n.factorial : ℝ) := by
    simp [p]
  calc
    |iteratedDeriv n f 0 / (n.factorial : ℝ)| = ‖p.coeff n‖ := by
      rw [← hc]
      rfl
    _ = ‖p n‖ := by
      rw [FormalMultilinearSeries.norm_apply_eq_norm_coef]
    _ ≤ C * ρ ^ n := hnorm n

end Commons.Analysis.Analytic
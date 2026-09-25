import Mathlib
import Submission.Work.BourgainPlan.Oscillation.commons_deps
import Submission.Work.BourgainPlan.Oscillation.trigP_dense
import Submission.Work.BourgainPlan.Oscillation.lacunary_truncated_maximal_l2_density

/-!
# The all-scales truncated maximal estimate for `L²` multipliers

`lacunary_truncated_maximal_l2_gen_via_density` is the `L²(mu01)`-form of the truncated maximal
estimate along one-sided lacunary scales.  It is obtained from the finitely supported
(trigonometric polynomial) version `lacunary_truncated_maximal_l2` by the density of trigonometric
polynomials (`trigP_dense`) and Fatou's lemma (`lacunary_truncated_maximal_l2_density`).
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Work.BourgainPlan.Oscillation

open Lacunary

theorem lacunary_truncated_maximal_l2_gen_via_density (ρ : ℝ) (hρ : 1 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ → ℂ), MemLp h 2 Lacunary.mu01 →
      (∫⁻ x : ℤ, (⨆ i : ℕ, ‖∫ θ, (if |θ| ≤ Lacunary.cc ρ i then (1:ℂ) else 0) * h θ
          * Lacunary.Echar x θ ∂Lacunary.mu01‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
      ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ θ : ℝ, ‖h θ‖ₑ ^ (2 : ℝ) ∂Lacunary.mu01 := by
  obtain ⟨C, hCpos, hC⟩ := lacunary_truncated_maximal_l2 ρ hρ
  refine ⟨C, hCpos, fun h hh => ?_⟩
  have hbound : ∀ (f : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → f n = 0) →
      (∫⁻ x : ℤ, (⨆ i : ℕ, ‖∫ θ in (0:ℝ)..1,
          (if |θ| ≤ Lacunary.cc ρ i then (1:ℂ) else 0) * Lacunary.trigP s f θ
            * Lacunary.Echar x θ‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ x : ℤ, ‖f x‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.Measure.count := by
    intro f s hf
    have h := hC f s hf
    exact h
  have h2 := lacunary_truncated_maximal_l2_density ρ hρ C hCpos hbound h hh
  simpa only [Lacunary.intervalIntegral_eq_mu01] using h2

end Work.BourgainPlan.Oscillation

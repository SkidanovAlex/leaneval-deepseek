import Mathlib
import Submission.Unif.Commons.Analysis.Complex.Koebe.weak_koebe_of_landau
import Submission.Unif.Commons.Analysis.Complex.Koebe.growth_bound
import Submission.Unif.Commons.Analysis.Complex.Landau.landau_theorem
import Submission.Unif.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn
import Submission.Work.FatouCH.twoSidedAux
import Submission.Work.FatouCH.derivNormLeOfAbel
import Submission.Work.FatouCH.derivNormGeOfAbel

namespace Work.FatouCH

/-- Two-sided Koebe-type bound (Shishikura Lemma A.2.4(i), first step). For `Φ` univalent on `ball z₀ R`, `v` holomorphic there with `‖v z - 1‖ < 1/4` and the Abel relation `Φ (z + v z) = Φ z + 1` on `ball z₀ R`, the derivative of `Φ` is bounded above and below on `ball z₀ (R-2)` by universal constants. To prove it, import `Submission.Unif.Commons.Analysis.Complex.Koebe.weak_koebe_of_landau`, `Submission.Unif.Commons.Analysis.Complex.Koebe.growth_bound`, `Submission.Unif.Commons.Analysis.Complex.Landau.landau_theorem`, `Submission.Unif.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn`. Upper bound: for `z ∈ ball z₀ (R-2)` put `G w = (Φ (z + (3/4)w) - Φ z)/((3/4) * deriv Φ z)`, univalent on the unit disc with `G 0 = 0`, `deriv G 0 = 1`; `weak_koebe_of_landau` (with `c₀ = 1/100`) gives `ball (Φ z) ((3/4)(c₀/π)‖deriv Φ z‖) ⊆ Φ '' ball z (3/4)`; if the radius exceeds `1` this contains `Φ z + 1 = Φ (z + v z)` with `z + v z ∈ ball z₀ R` but `‖v z‖ > 3/4`, contradicting injectivity. Lower bound: apply `growth_bound` to `u ↦ (Φ (z+2u) - Φ z)/(2 deriv Φ z)` at `u = v z / 2`. -/
theorem koebeTwoSided :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Φ v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ),
        DifferentiableOn ℂ Φ (Metric.ball z₀ R) → Set.InjOn Φ (Metric.ball z₀ R) →
        DifferentiableOn ℂ v (Metric.ball z₀ R) →
        (∀ z ∈ Metric.ball z₀ R, ‖v z - 1‖ < 1 / 4) →
        (∀ z ∈ Metric.ball z₀ R, z + v z ∈ Metric.ball z₀ R → Φ (z + v z) = Φ z + 1) →
        ∀ z ∈ Metric.ball z₀ (R - 2), c ≤ ‖deriv Φ z‖ ∧ ‖deriv Φ z‖ ≤ C := by
  -- Landau's theorem gives a Landau constant `c₀ > 0`; through the weak Koebe inequality
  -- (`Commons.Analysis.Complex.Koebe.weak_koebe_of_landau`) it becomes a Koebe-type constant
  -- `ρ = c₀/π` for the unit disc, which is exactly the hypothesis of the two halves.
  obtain ⟨c₀, hc₀, hlandau⟩ := Commons.Analysis.Complex.Landau.landau_theorem
  have hkoebe := Commons.Analysis.Complex.Koebe.weak_koebe_of_landau hc₀ hlandau
  have hρ : 0 < c₀ / Real.pi := div_pos hc₀ Real.pi_pos
  have h13 : (1 : ℝ) < 13 / 3 := by norm_num
  have h1ρ : 0 < 1 / (c₀ / Real.pi) := one_div_pos.mpr hρ
  have hbig : 1 < (13 / 3 : ℝ) ^ (1 / (c₀ / Real.pi)) := Real.one_lt_rpow h13 h1ρ
  refine ⟨1 / (2 * ((13 / 3 : ℝ) ^ (1 / (c₀ / Real.pi)) - 1)), 4 / (3 * (c₀ / Real.pi)),
    ?_, ?_, ?_⟩
  · exact one_div_pos.mpr (by linarith)
  · exact div_pos (by norm_num) (by positivity)
  · intro Φ v z₀ R hΦ hinj hv hnear habel z hz
    exact ⟨derivNormGeOfAbel hρ hkoebe Φ v z₀ R hΦ hinj hv hnear habel z hz,
      derivNormLeOfAbel hρ hkoebe Φ v z₀ R hΦ hinj hv hnear habel z hz⟩

end Work.FatouCH

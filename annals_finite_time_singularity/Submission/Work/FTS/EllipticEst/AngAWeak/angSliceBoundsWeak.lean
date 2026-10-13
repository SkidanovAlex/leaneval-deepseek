import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.HonestBddOfSecondSq
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

open MeasureTheory Set Filter

theorem angSliceBoundsWeak : ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn f (Set.Icc 0 (Real.pi / 2)) →
      f 0 = 0 → f (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      ∃ C : ℝ, 0 < C ∧
        (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ C * θ) ∧
        (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ C * (Real.pi / 2 - θ)) ∧
        (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ C) := by
  intro f hsm hcont h0 hpi hint
  -- `C²` on the open interval plus the weighted square-integrability of `f''` bounds
  -- `f` and `f'` by a constant on `(0, π/2)`.
  obtain ⟨C₀, hC₀nn, hC₀⟩ :=
    Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta hsm hint
  have hdiff : DifferentiableOn ℝ f (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.differentiableOn (by norm_num)
  refine ⟨C₀ + 1, by linarith, ?_, ?_, ?_⟩
  · -- linear vanishing at `0`, by the mean value theorem on `[0, θ]`
    intro θ hθ
    obtain ⟨c, hc, hder⟩ := exists_deriv_eq_slope f hθ.1
      (hcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 hθ.2.le⟩))
      (hdiff.mono (fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hθ.2.le⟩))
    have hcI : c ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hc.1, lt_trans hc.2 hθ.2⟩
    have hthis : f θ = deriv f c * θ := by
      rw [hder, h0, sub_zero, sub_zero, div_mul_cancel₀]
      exact hθ.1.ne'
    rw [hthis, abs_mul, abs_of_pos hθ.1]
    refine mul_le_mul_of_nonneg_right ?_ hθ.1.le
    have hc' := (hC₀ c hcI).2
    linarith
  · -- linear vanishing at `π/2`, by the mean value theorem on `[θ, π/2]`
    intro θ hθ
    obtain ⟨c, hc, hder⟩ := exists_deriv_eq_slope f hθ.2
      (hcont.mono (fun x hx => ⟨le_trans hθ.1.le hx.1, hx.2⟩))
      (hdiff.mono (fun x hx => ⟨lt_trans hθ.1 hx.1, hx.2⟩))
    have hcI : c ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨lt_trans hθ.1 hc.1, hc.2⟩
    have hpos : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hder2 : deriv f c = -(f θ / (Real.pi / 2 - θ)) := by
      rw [hder, hpi, zero_sub, neg_div]
    have hthis : f θ = -(deriv f c) * (Real.pi / 2 - θ) := by
      rw [hder2, neg_neg, div_mul_cancel₀]
      exact hpos.ne'
    rw [hthis, abs_mul, abs_neg, abs_of_pos hpos]
    refine mul_le_mul_of_nonneg_right ?_ hpos.le
    have hc' := (hC₀ c hcI).2
    linarith
  · -- the derivative bound
    intro θ hθ
    have hc' := (hC₀ θ hθ).2
    linarith

end Work.FTS.EllipticEst.AngAWeak

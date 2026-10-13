import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

/-- On the interval `(π/4, π/2)` the square of the sine is bounded below by `1/2`. -/
theorem one_half_le_sin_sq {θ : ℝ} (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    (1 : ℝ) / 2 ≤ (Real.sin θ) ^ 2 := by
  have h3 : Real.pi / 4 ≤ θ := hθ.1.le
  have h2 : θ ≤ Real.pi / 2 := hθ.2.le
  have hs : Real.sin (Real.pi / 4) ≤ Real.sin θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h2 h3
  rw [Real.sin_pi_div_four] at hs
  have hnn : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
  have hmul := mul_self_le_mul_self hnn hs
  have hsq : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (1 : ℝ) / 2 := by
    rw [← sq, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  nlinarith [hmul, hsq]

/-- If `sin²θ · f θ` is integrable on `(0, π/2)` and `f` is nonnegative (and measurable) on
`(π/4, π/2)`, then `f` itself is integrable on `(π/4, π/2)`: there `sin²θ ≥ 1/2`, so
`f ≤ 2 · (sin²θ · f)` and the subinterval inherits integrability. -/
theorem integrableOn_of_sin_sq_mul {f : ℝ → ℝ} (hf : Measurable f)
    (hf0 : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), 0 ≤ f θ)
    (hY : MeasureTheory.IntegrableOn (fun θ => (Real.sin θ) ^ 2 * f θ)
      (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn f (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  have hsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro θ hθ
    exact ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hY' : MeasureTheory.Integrable (fun θ => (Real.sin θ) ^ 2 * f θ)
      (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :=
    hY.mono_set hsub
  have hg : MeasureTheory.Integrable (fun θ => 2 * ((Real.sin θ) ^ 2 * f θ))
      (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :=
    hY'.const_mul 2
  refine MeasureTheory.Integrable.mono' (g := fun θ => 2 * ((Real.sin θ) ^ 2 * f θ)) hg ?_ ?_
  · exact hf.aestronglyMeasurable.restrict
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with θ hθ
    have hfnn : 0 ≤ f θ := hf0 θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
    nlinarith [one_half_le_sin_sq hθ, hfnn, sq_nonneg (Real.sin θ)]

end Work.FTS.EllipticEst.Honest

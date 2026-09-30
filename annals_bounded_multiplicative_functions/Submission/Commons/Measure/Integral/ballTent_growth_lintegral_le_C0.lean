import Submission.Commons.Measure.Integral.ballTent_growth_lintegral_le_fixed_C0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Measure.Integral

/-- Growth bound for the ball tent kernel: for exponents `A > B + n` and `B ≥ 0`
there is a constant `C ≥ 0` bounding, uniformly over the radius `R > 0`, the
`L¹` norm of the (normalised) ball tent integrand
`(1 + d(w, B_R)/R)^{-A} (1 + C₀‖w‖/R)^B`.

This is the statement requested for the Vinogradov mean value development; it
coincides with the already-published commons lemma
`ballTent_growth_lintegral_le_fixed_C0`. -/
theorem ballTent_growth_lintegral_le_C0 {n : ℕ} {A B : ℝ} (hB : 0 ≤ B)
    (hAB : B + (n : ℝ) < A) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      MeasureTheory.lintegral MeasureTheory.volume
        (fun w : EuclideanSpace ℝ (Fin n) =>
          (ENNReal.ofReal (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal)⁻¹
          * ENNReal.ofReal ((1 + Metric.infDist w (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) / R) ^ (-A))
          * ENNReal.ofReal ((1 + C₀ * ‖w‖ / R) ^ B))
      ≤ ENNReal.ofReal C :=
  ballTent_growth_lintegral_le_fixed_C0 hB hAB C₀ hC₀

end Commons.Measure.Integral

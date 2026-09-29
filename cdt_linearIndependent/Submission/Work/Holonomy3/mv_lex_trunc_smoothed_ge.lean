import Mathlib
import Submission.Work.Holonomy3.mv_lex_general_defs
import Submission.Work.Holonomy3.mv_lex_null_zero

/-!
# The smoothing comparison for truncated character sums

For a nonzero polynomial character sum `f = pevalF (truncF a N)` on the `d`-torus and any
`δ > 0`,

  `∫ log ‖f‖  ≤  ∫ log (‖f‖ + δ)`,

both integrals being taken against the normalised torus measure `torMeasure d`.

The point is that the inequality `log x ≤ log (x + δ)` is *not* valid at `x = 0`, where
`log 0 = 0` while `log δ < 0` for `δ < 1`. It does however hold at every point at which
`f` does not vanish, and the zero set of a nonzero character sum is null
(`Work.Holonomy3.mv_lex_null_zero`). So the two integrands agree `torMeasure d`-almost
everywhere in the relevant direction, and the integral inequality follows from
`MeasureTheory.integral_mono_ae` together with the two integrability hypotheses.
-/

namespace Work.Holonomy3

open MeasureTheory

noncomputable section

theorem mv_lex_trunc_smoothed_ge {d : ℕ} (a : (Fin d →₀ ℕ) → ℂ) (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hne : truncF a N ≠ 0)
    (hint : MeasureTheory.Integrable (fun t : Fin d → ℝ => Real.log ‖pevalF (truncF a N) (tor t)‖) (torMeasure d))
    (hintδ : MeasureTheory.Integrable (fun t : Fin d → ℝ => Real.log (‖pevalF (truncF a N) (tor t)‖ + δ)) (torMeasure d)) :
    ∫ t : Fin d → ℝ, Real.log ‖pevalF (truncF a N) (tor t)‖ ∂(torMeasure d)
      ≤ ∫ t : Fin d → ℝ, Real.log (‖pevalF (truncF a N) (tor t)‖ + δ) ∂(torMeasure d) := by
  -- The two integrands only differ on the null set where the character sum vanishes.
  refine MeasureTheory.integral_mono_ae hint hintδ ?_
  have hZ : torMeasure d {t : Fin d → ℝ | pevalF (truncF a N) (tor t) = 0} = 0 :=
    mv_lex_null_zero (truncF a N) hne
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hZ] with t ht
  -- Off the zero set the value is strictly positive, and `log` is monotone there.
  have hpos : 0 < ‖pevalF (truncF a N) (tor t)‖ := norm_pos_iff.mpr ht
  exact Real.log_le_log hpos (by linarith)

end

end Work.Holonomy3

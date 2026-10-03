import Mathlib
import Submission.Work.Repel.deriv_lower_aux
import Submission.Work.Repel.bieberbach_two_aux
import Submission.Work.Repel.koebeT_iteratedDeriv_two
import Submission.Work.Motion.koebe_distortion

/-!
# Logarithmic-derivative (distortion) inequality on the unit disc

For `g` holomorphic and injective on the unit disc, the second derivative of `g` is controlled by
the first: `‖g''(w)‖ ≤ ((4 + 2‖w‖)/(1 - ‖w‖²)) ‖g'(w)‖` for all `w` in the disc.

The route is the classical Koebe-transform reduction of the second-coefficient (Bieberbach)
estimate:

* at a point `w` in the disc with `g'(w) ≠ 0`, the Koebe transform
  `koebeT g w ζ = (g ((ζ+w)/(1 + conj w ζ)) - g w) / ((1 - ‖w‖²) g'(w))` is again a normalised
  univalent function on the disc, so Bieberbach's inequality
  (`Work.Repel.bieberbach_two_aux`, from Grönwall's area theorem) gives
  `‖(koebeT g w)''(0)‖ ≤ 4`;
* the classical second-order expansion of the Koebe transform
  (`Work.Repel.koebeT_iteratedDeriv_two`) identifies
  `(koebeT g w)''(0) = (1 - ‖w‖²) g''(w)/g'(w) - 2 conj w`;
* the triangle inequality then yields
  `‖g''(w)/g'(w)‖ ≤ (4 + 2‖w‖)/(1 - ‖w‖²)`.
-/

namespace Work.Repel

open scoped ComplexConjugate

/-- **Logarithmic-derivative (distortion) inequality on the unit disc.**  For `g` holomorphic and
injective on the unit disc, the second derivative of `g` is controlled by the first:
`‖g''(w)‖ ≤ ((4 + 2‖w‖)/(1 - ‖w‖²)) ‖g'(w)‖` for all `w` in the disc. -/
theorem log_deriv_bound_unit {g : ℂ → ℂ}
    (han : ∀ w ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ g w)
    (hinj : Set.InjOn g (Metric.ball (0 : ℂ) 1)) :
    ∀ w ∈ Metric.ball (0 : ℂ) 1,
      ‖deriv (deriv g) w‖ ≤ (4 + 2 * ‖w‖) / (1 - ‖w‖ ^ 2) * ‖deriv g w‖ := by
  intro w hw
  have hwn : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hpos : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hgw : deriv g w ≠ 0 := by
    refine Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn
      (by linarith : (0 : ℝ) < 1 - ‖w‖) (han w hw) (hinj.mono ?_)
    intro a ha
    have ha' : ‖a - w‖ < 1 - ‖w‖ := by simpa [Metric.mem_ball, dist_eq_norm] using ha
    have h1 : ‖a‖ ≤ ‖a - w‖ + ‖w‖ := by
      calc ‖a‖ = ‖(a - w) + w‖ := by ring_nf
        _ ≤ ‖a - w‖ + ‖w‖ := norm_add_le _ _
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero]
    linarith
  obtain ⟨hkan, hkinj, hk0, hk1⟩ := Work.Motion.koebeT_normalized han hinj hw hgw
  have hB : ‖iteratedDeriv 2 (Work.Motion.koebeT g w) 0‖ ≤ 4 :=
    bieberbach_two_aux hkan hkinj hk0 hk1
  have hform : iteratedDeriv 2 (Work.Motion.koebeT g w) 0
      = (1 - ‖w‖ ^ 2) * deriv (deriv g) w / deriv g w - 2 * conj w :=
    koebeT_iteratedDeriv_two hw han hgw
  rw [hform] at hB
  have hstep : ‖(1 - (‖w‖ : ℂ) ^ 2) * deriv (deriv g) w / deriv g w‖ ≤ 4 + 2 * ‖w‖ := by
    have h2 : ‖(2 : ℂ) * conj w‖ = 2 * ‖w‖ := by
      rw [norm_mul, Complex.norm_conj]; norm_num
    calc ‖(1 - (‖w‖ : ℂ) ^ 2) * deriv (deriv g) w / deriv g w‖
        = ‖((1 - (‖w‖ : ℂ) ^ 2) * deriv (deriv g) w / deriv g w - 2 * conj w) + 2 * conj w‖ := by
          congr 1; ring
      _ ≤ ‖(1 - (‖w‖ : ℂ) ^ 2) * deriv (deriv g) w / deriv g w - 2 * conj w‖ + ‖2 * conj w‖ :=
          norm_add_le _ _
      _ ≤ 4 + 2 * ‖w‖ := by rw [h2]; linarith
  have hgn : 0 < ‖deriv g w‖ := norm_pos_iff.mpr hgw
  have hnorm : ‖((1 - ‖w‖ ^ 2 : ℝ) : ℂ)‖ = 1 - ‖w‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  have hc : ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) = 1 - (‖w‖ : ℂ) ^ 2 := by push_cast; ring
  have h1 : (1 - ‖w‖ ^ 2) * ‖deriv (deriv g) w‖ ≤ (4 + 2 * ‖w‖) * ‖deriv g w‖ := by
    rw [← hc, norm_div, norm_mul, hnorm] at hstep
    rw [div_le_iff₀ hgn] at hstep
    exact hstep
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  rw [mul_comm (‖deriv (deriv g) w‖) (1 - ‖w‖ ^ 2)]
  exact h1


end Work.Repel

import Mathlib
import Submission.Commons.Analysis.Complex.exists_two_preimages_near_of_deriv_eq_zero

namespace Commons.Analysis.Complex.Analytic

/-- If a function `f : ℂ → ℂ` is complex analytic at `c` and injective on a ball around `c`,
then its derivative at `c` does not vanish.

Proof sketch: WLOG `c = 0`, `f 0 = 0`.  If `deriv f 0 = 0` then `f` has analytic order `n ≥ 2`
at `0`, so `f =ᶠ[𝓝 0] fun z => z ^ n * g z` with `g` analytic at `0` and `g 0 ≠ 0`
(`AnalyticAt.analyticOrderAt_eq_natCast`).  Since `g 0 ≠ 0`, `g` has an analytic `n`-th root `r`
near `0`; then `z ↦ z * r z` has nonzero derivative at `0`, hence is a local biholomorphism, and
`f = (z * r z) ^ n` near `0`.  Taking `ζ` a nontrivial `n`-th root of unity and `z ≠ 0` small with
`z * r z ≠ 0`, the two points `z` and the preimage of `(z * r z) * ζ` are distinct and have the
same `f`-value, contradicting injectivity. -/
theorem deriv_ne_zero_of_injOn {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticAt ℂ f c) (hinj : Set.InjOn f (Metric.ball c r)) : deriv f c ≠ 0 := by
  by_contra hderiv
  by_cases hconst : ∀ᶠ z in nhds c, f z = f c
  · -- `f` is locally constant near `c`, so it cannot be injective on the ball
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hconst
    have hmin : 0 < min δ r := lt_min hδpos hr
    set t : ℂ := c + (((min δ r / 2 : ℝ)) : ℂ) with ht
    have htc : t - c = (((min δ r / 2 : ℝ)) : ℂ) := by rw [ht]; ring
    have hdt : dist t c < min δ r := by
      rw [dist_eq_norm, htc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < min δ r / 2)]
      linarith
    have htne : t ≠ c := by
      intro h
      have h0 : (((min δ r / 2 : ℝ)) : ℂ) = 0 := by
        rw [← htc, h, sub_self]
      have h0' : min δ r / 2 = 0 := Complex.ofReal_eq_zero.mp h0
      linarith
    have hcball : c ∈ Metric.ball c r := by simp [Metric.mem_ball, hr]
    have htball : t ∈ Metric.ball c r := by
      rw [Metric.mem_ball]
      exact lt_of_lt_of_le hdt (min_le_right _ _)
    have htval : f t = f c := hδ (y := t) (lt_of_lt_of_le hdt (min_le_left _ _))
    exact htne (hinj htball hcball htval)
  · -- otherwise two nearby distinct preimages of the same value exist
    obtain ⟨w, -, -, a, b, hab, ha, hb, hfa, hfb⟩ :=
      Commons.Analysis.Complex.exists_two_preimages_near_of_deriv_eq_zero hf hderiv hconst hr
    exact hab (hinj (by rw [Metric.mem_ball, dist_eq_norm]; exact ha)
      (by rw [Metric.mem_ball, dist_eq_norm]; exact hb) (hfa.trans hfb.symm))

end Commons.Analysis.Complex.Analytic

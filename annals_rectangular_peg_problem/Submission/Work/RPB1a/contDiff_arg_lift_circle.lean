import Mathlib
import Submission.Work.RPB.B1.argument_lift_aux

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real Topology
open MeasureTheory

/-- A smooth `ℂ`-valued loop that is everywhere unimodular has a smooth argument lift:
`∃ σ : ℝ → ℝ, ContDiff ℝ ∞ σ ∧ ∀ t, g t = Complex.exp ((σ t : ℂ) * I)`.

Suggested route: the workspace already contains the one-dimensional lift lemma
`Work.RPB.B1.argument_lift_oneDim` in `Submission/Work/RPB/B1/argument_lift_aux.lean`, which states
(for `ContDiff ℝ 1 g`, `∀ s, g s ≠ 0`, and an initial phase `θ` with `g 0 = ‖g 0‖ * exp (θ * I)`)
that `g s = ‖g s‖ * exp ((θ + ∫ τ in 0..s, (deriv g τ / g τ).im) * I)` for all `s`; importing that
module and applying it with `‖g 0‖ = 1` finishes the job, taking
`σ t = θ + ∫ τ in 0..t, (deriv g τ / g τ).im`, which is `ContDiff ℝ ∞` because the integrand is
smooth and nowhere-vanishing (`ContDiff.intervalIntegral`, or
`intervalIntegral.contDiff_integral_of_continuous`-style lemmas).  Alternatively repeat the
classical argument directly: `σ t := θ₀ + ∫₀ᵗ Im (g' / g)` and show `u := g * exp (-(σ ·) * I)` is
constant with `u 0 = 1`, using `‖g‖ ≡ 1 ⟹ Re (g' * conj g) ≡ 0` and hence `g' = (Im (g' / g)) * I * g`. -/
theorem contDiff_arg_lift_circle {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (h1 : ∀ t, ‖g t‖ = 1) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ ∞ σ ∧ ∀ t, g t = Complex.exp ((σ t : ℂ) * I) := by
  -- `g` is nowhere vanishing, being unimodular.
  have hne : ∀ s, g s ≠ 0 := fun s hs => by
    have h := h1 s
    rw [hs, norm_zero] at h
    norm_num at h
  -- an initial phase for the value at `0`
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff (g 0)).mp (h1 0)
  have h0 : g 0 = (‖g 0‖ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [h1 0, Complex.ofReal_one, one_mul]
    exact hθ.symm
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
  -- the logarithmic derivative's imaginary part is smooth
  have hq_smooth : ContDiff ℝ ∞ (fun τ : ℝ => (deriv g τ / g τ).im) := by
    have hd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
    have hdiv : ContDiff ℝ ∞ (fun τ : ℝ => deriv g τ / g τ) := by
      simpa only [Pi.inv_apply, div_eq_mul_inv] using hd.mul (hg.inv hne)
    exact Complex.imCLM.contDiff.comp hdiv
  have hq_cont : Continuous (fun τ : ℝ => (deriv g τ / g τ).im) := hq_smooth.continuous
  -- its primitive is smooth
  have hQ_deriv : ∀ s : ℝ, HasDerivAt (fun t : ℝ => ∫ τ in (0 : ℝ)..t, (deriv g τ / g τ).im)
      ((deriv g s / g s).im) s := fun s =>
    intervalIntegral.integral_hasDerivAt_right
      (hq_cont.intervalIntegrable 0 s)
      (hq_cont.stronglyMeasurableAtFilter volume (nhds s))
      hq_cont.continuousAt
  have hQ_smooth : ContDiff ℝ ∞ (fun t : ℝ => ∫ τ in (0 : ℝ)..t, (deriv g τ / g τ).im) := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun s => (hQ_deriv s).differentiableAt, ?_⟩
    have hderiv : deriv (fun t : ℝ => ∫ τ in (0 : ℝ)..t, (deriv g τ / g τ).im)
        = fun τ : ℝ => (deriv g τ / g τ).im := by
      funext s
      exact (hQ_deriv s).deriv
    rw [hderiv]
    exact hq_smooth
  refine ⟨fun t : ℝ => θ + ∫ τ in (0 : ℝ)..t, (deriv g τ / g τ).im, ?_, ?_⟩
  · exact contDiff_const.add hQ_smooth
  · intro t
    have hp := Work.RPB.B1.argument_lift_oneDim (g := g) (θ := θ) hg1 hne h0 t
    refine hp.trans ?_
    rw [h1 t, Complex.ofReal_one, one_mul]
    push_cast
    ring

end Work.RPB1a

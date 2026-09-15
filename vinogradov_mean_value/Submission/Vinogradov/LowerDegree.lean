/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.PolarContain
import Submission.Vinogradov.AsymRefine
import Submission.Vinogradov.LocalisedDecoupling

/-!
# GLYZ Lemma 3.8 (lower degree decoupling): the analytic assembly

This module hosts the proof of `AsymDecFine` (`Submission.Vinogradov.AsymRefine`), i.e. of
Guo–Li–Yung–Zorin-Kranich, arXiv:1912.09798, (3.10)/Lemma 3.8.  The proof has five steps
(see `ROADMAP.lean`, session 49, section (C)):

1. moving-ball Fubini (`Commons.Measure.Integral.lintegral_mul_le_moving_ball`);
2. the sup comparison for the `I'`-factor (`PolarContain.gauge_plateGaugeLin_projEmbed_le`
   plus `TentShift.phiPlate_shift_le`);
3. the convolution swap (this file: `lintegral_ball_convPow_swap`), which lifts the `H`-ball
   average onto the bump;
4. the localised decoupling on each translate
   (`LocalisedDecoupling.curveDecLoc_of_curveDec` + the class transport of `Projection`);
5. Minkowski and the two tent comparisons (paper Lemmas A.1, A.2, 3.3).

This module currently contains step 3, the pure Fubini identity.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Submission.Vinogradov

/-- **The convolution swap of GLYZ (3.11)**:  the average of `(|g|^{p} ∗ Φ)` over the ball
`z + Ψ '' B(0,r)` equals the integral of `Φ` against the ball averages of `|g|` centred at
`z - t`:

  `∫_{w ∈ B(0,r)} (|g|^{p} ∗ Φ)(z + Ψ w) = ∫_t Φ(t) (∫_{w ∈ B(0,r)} ‖g((z-t) + Ψ w)‖^{p})`.

No translation invariance and no isometry property of `Ψ` is needed: this is pure Fubini, the
point being that the ball average is lifted onto the *bump* `Φ` (the inner integral has the
argument `(z - t) + Ψ w`, whose centre runs over all of `E k` as `t` does). -/
theorem lintegral_ball_convPow_swap {k l : ℕ} (Ψ : E l →ₗ[ℝ] E k)
    {r : ℝ} (hr : 0 < r) (s : ℝ) {g : E k → ℂ} (hg : Measurable g)
    {ΦI : E k → ℝ≥0∞} (hΦI : Measurable ΦI) (z : E k) :
    (∫⁻ w in Metric.ball (0 : E l) r, convPow k s g ΦI (z + Ψ w))
      = ∫⁻ t, ΦI t
          * (∫⁻ w in Metric.ball (0 : E l) r, (‖g ((z - t) + Ψ w)‖₊ : ℝ≥0∞) ^ s) := by
  set ν : Measure (E l) := volume.restrict (Metric.ball (0 : E l) r) with hν
  have hΨc : Continuous (fun w : E l => z + Ψ w) :=
    continuous_const.add (Ψ.continuous_of_finiteDimensional.comp continuous_id)
  have hpt : ∀ w : E l, convPow k s g ΦI (z + Ψ w)
      = ∫⁻ t, ((‖g ((z - t) + Ψ w)‖₊ : ℝ≥0∞) ^ s) * ΦI t := by
    intro w
    rw [convPow]
    refine lintegral_congr (fun t => ?_)
    have harg : z + Ψ w - t = (z - t) + Ψ w := by abel
    rw [harg, mul_comm]
  calc ∫⁻ w, convPow k s g ΦI (z + Ψ w) ∂ν
      = ∫⁻ w, ∫⁻ t, ((‖g ((z - t) + Ψ w)‖₊ : ℝ≥0∞) ^ s) * ΦI t ∂volume ∂ν :=
        lintegral_congr hpt
    _ = ∫⁻ t, ∫⁻ w, ((‖g ((z - t) + Ψ w)‖₊ : ℝ≥0∞) ^ s) * ΦI t ∂ν ∂volume := by
        refine lintegral_lintegral_swap ?_
        have hcont : Continuous (fun p : E l × E k => (z - p.2) + Ψ p.1) := by fun_prop
        have hmeas : Measurable (fun p : E l × E k =>
            (‖g ((z - p.2) + Ψ p.1)‖₊ : ℝ≥0∞) ^ s * ΦI p.2) :=
          ((hg.comp hcont.measurable).nnnorm.coe_nnreal_ennreal.pow_const s).mul
            (hΦI.comp measurable_snd)
        exact hmeas.aemeasurable
    _ = ∫⁻ t, ΦI t
          * (∫⁻ w, (‖g ((z - t) + Ψ w)‖₊ : ℝ≥0∞) ^ s ∂ν) := by
        refine lintegral_congr (fun t => ?_)
        have hcont : Continuous (fun w : E l => (z - t) + Ψ w) := by fun_prop
        have hmeas : Measurable (fun w : E l => (‖g ((z - t) + Ψ w)‖₊ : ℝ≥0∞) ^ s) :=
          (hg.comp hcont.measurable).nnnorm.coe_nnreal_ennreal.pow_const s
        rw [lintegral_mul_const (ΦI t) hmeas, mul_comm]

end Submission.Vinogradov

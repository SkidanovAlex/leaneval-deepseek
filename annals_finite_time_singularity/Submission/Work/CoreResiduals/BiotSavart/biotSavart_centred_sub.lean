import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_centered
import Submission.Work.CoreResiduals.BiotSavart.constant_vec_integral_ball_bsK_eq_zero
import Submission.Work.LWP.BiotSavart.nearField_bound
import Submission.Work.LWP.BiotSavart.farField_decay_fderiv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric

/-! ## Two elementary facts about the Biot–Savart kernel at a constant vorticity

The regularisation `ω ↦ ω - ω x` inside the Biot–Savart integral replaces the integrand
`bsK ω x` by its difference with the integrand of the *constant* vorticity `ω x`.  The latter
is not globally integrable (the constant vorticity is not supported in any ball), but it is
locally integrable, and the only integrability information the subtraction
`∫ (f - g) = ∫ f - ∫ g` needs is that of `g` on the ball `B(x,ρ)`.  We provide it here: the
kernel of a constant vorticity is dominated by `‖v‖·‖x-a‖⁻²`, which is integrable on any ball
of `ℝ³` (the borderline case `2 < 3 = dim`). -/

/-- Pointwise size of the Biot–Savart integrand of a *constant* vorticity: the cross-product
factor is controlled by `‖v‖·‖x-a‖` and the kernel weight `‖x-a‖⁻³` then improves it to
`‖v‖·‖x-a‖⁻²`.  This is `Work.LWP.BiotSavart.bsIntegrand_norm_le` at the constant field. -/
lemma norm_bsK_const_le (v x a : Work.LWP.R3) :
    ‖Work.LWP.BiotSavart.bsK (fun _ : Work.LWP.R3 => v) x a‖
      ≤ ‖v‖ * (‖x - a‖ ^ (2 : ℕ))⁻¹ :=
  Work.LWP.BiotSavart.bsIntegrand_norm_le (norm_nonneg v) (fun _ => le_refl ‖v‖) x a

/-- **Local integrability of the Biot–Savart kernel of a constant vorticity.**  For every
`v x : ℝ³` and radius `ρ` the function `a ↦ bsK (fun _ => v) x a` is integrable on `B(x,ρ)`.

The dominating function is `‖v‖·(‖x-a‖⁻²)` on the ball `B(x, max ρ 0)` (which contains
`B(x,ρ)`); its `lintegral` is finite by the radial computation
`Work.LWP.BiotSavart.inv_sq_lintegral_closedBall_shifted_le`. -/
lemma integrable_indicator_bsK_const (v x : Work.LWP.R3) (ρ : ℝ) :
    Integrable ((Metric.ball x ρ).indicator (Work.LWP.BiotSavart.bsK (fun _ : Work.LWP.R3 => v) x))
      MeasureTheory.volume := by
  set R' : ℝ := max ρ 0 with hR'def
  have hR' : 0 ≤ R' := by rw [hR'def]; exact le_max_right _ _
  -- `B(x,ρ)` is contained in the closed ball `B(x,R')` with `R' = max ρ 0 ≥ 0`.
  have hsub : Metric.ball x ρ ⊆ Metric.closedBall x R' := by
    intro a ha
    rw [Metric.mem_ball] at ha
    rw [Metric.mem_closedBall, hR'def]
    rcases lt_or_ge ρ 0 with h | h
    · exact le_trans (le_trans (le_of_lt ha) (le_of_lt h)) (le_max_right _ _)
    · exact le_trans (le_of_lt ha) (le_max_left _ _)
  -- `‖x-a‖⁻²` is integrable on the closed ball centred at `x`.
  have hbase : Integrable
      ((Metric.closedBall x R').indicator (fun a : Work.LWP.R3 => (‖x - a‖ ^ (2 : ℕ))⁻¹))
      MeasureTheory.volume := by
    rw [MeasureTheory.integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
    rw [MeasureTheory.IntegrableOn]
    refine ⟨?_, ?_⟩
    · apply Measurable.aestronglyMeasurable
      measurability
    · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
      calc ∫⁻ y in Metric.closedBall x R', ENNReal.ofReal ‖(‖x - y‖ ^ (2 : ℕ))⁻¹‖
          = ∫⁻ y in Metric.closedBall x R', ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹) := by
            apply lintegral_congr; intro y
            rw [Real.norm_of_nonneg (by positivity)]
        _ = ∫⁻ y in Metric.closedBall x R', ENNReal.ofReal ((‖y - x‖ ^ (2 : ℕ))⁻¹) := by
            apply lintegral_congr; intro y; rw [norm_sub_rev]
        _ ≤ ENNReal.ofReal (4 * Real.pi * R') :=
            Work.LWP.BiotSavart.inv_sq_lintegral_closedBall_shifted_le x hR'
        _ < ⊤ := ENNReal.ofReal_lt_top
  refine Integrable.mono'
    (g := fun a => ‖v‖ * ((Metric.closedBall x R').indicator
      (fun a : Work.LWP.R3 => (‖x - a‖ ^ (2 : ℕ))⁻¹) a)) ?_ ?_ ?_
  · exact hbase.const_mul ‖v‖
  · exact (Work.LWP.BiotSavart.aestronglyMeasurable_bsK aestronglyMeasurable_const x).indicator
      measurableSet_ball
  · filter_upwards with a
    by_cases ha : a ∈ Metric.ball x ρ
    · have ha' : a ∈ Metric.closedBall x R' := hsub ha
      rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha']
      exact norm_bsK_const_le v x a
    · rw [Set.indicator_of_notMem ha]
      simp only [norm_zero]
      exact mul_nonneg (norm_nonneg v)
        (Set.indicator_nonneg (fun a _ => inv_nonneg.mpr (by positivity)) a)

/-- **The regularised (centred, subtracted) form of the Biot–Savart integral.**  Combining the centred form
`biotSavart_centered` (the integrand is supported in `B(x,ρ)` when the vorticity is supported in
`B(0,R)` and `R + ‖x‖ ≤ ρ`) with the odd-kernel cancellation
`constant_vec_integral_ball_bsK_eq_zero` (the integral of the kernel against the *constant* vector
`ω x` vanishes), one may replace `ω y` by `ω y - ω x` inside the integral.

This is the form in which the Calderón–Zygmund estimate for the `x`-derivative of `biotSavart` is
carried out: the integrand `bsK (ω - ω x) x a` is dominated by `C‖x-a‖^{c-2}` for an
`x`-Hölder vorticity of exponent `c`, whose `x`-derivative is dominated by `C‖x-a‖^{c-3}` —
integrable near the diagonal exactly when `c > 0`. -/
theorem biotSavart_centred_sub {ω : Work.LWP.R3 → Work.LWP.R3} {R M ρ : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ a, ‖ω a‖ ≤ M) (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume) {x : Work.LWP.R3}
    (hρ : R + ‖x‖ ≤ ρ) :
    Work.LWP.biotSavart ω x
      = (4 * Real.pi)⁻¹ • ∫ a in Metric.ball x ρ,
          Work.LWP.BiotSavart.bsK (fun y => ω y - ω x) x a := by
  -- First restrict the full integral to the ball `B(x,ρ)` (`biotSavart_centered`).
  rw [biotSavart_centered hM hbdd hs hm hρ]
  -- Abbreviate the two integrands: that of `ω` and that of the constant field `ω x`.
  let F : Work.LWP.R3 → Work.LWP.R3 := Work.LWP.BiotSavart.bsK ω x
  let K : Work.LWP.R3 → Work.LWP.R3 := Work.LWP.BiotSavart.bsK (fun _ : Work.LWP.R3 => ω x) x
  -- Pointwise, `bsK (ω - ω x)` is the difference `F - K` (linearity of the cross product).
  have hpt : ∀ a, Work.LWP.BiotSavart.bsK (fun y => ω y - ω x) x a = F a - K a := by
    intro a
    exact Work.StabilityFar.Decay.bsK_sub ω (fun _ : Work.LWP.R3 => ω x) x a
  -- Both integrands are integrable on the ball: `F` is integrable on all of `ℝ³`, while the
  -- constant part `K` is only locally integrable (`integrable_indicator_bsK_const`).
  have hFi : Integrable F (volume.restrict (Metric.ball x ρ)) :=
    (Work.StabilityFar.Decay.integrable_bsK_supported hM hbdd hs hm x).integrableOn
  have hKi : Integrable K (volume.restrict (Metric.ball x ρ)) :=
    (MeasureTheory.integrable_indicator_iff measurableSet_ball).mp
      (integrable_indicator_bsK_const (ω x) x ρ)
  -- The integral of the constant part over the ball vanishes (odd kernel about `x`).
  have hKzero : ∫ a in Metric.ball x ρ, K a = 0 :=
    constant_vec_integral_ball_bsK_eq_zero (ω x) x ρ
  -- Hence the two restricted integrals agree.
  have hmain : ∫ a in Metric.ball x ρ, Work.LWP.BiotSavart.bsK (fun y => ω y - ω x) x a
      = ∫ a in Metric.ball x ρ, F a := by
    rw [show (fun a => Work.LWP.BiotSavart.bsK (fun y => ω y - ω x) x a)
        = (fun a => F a - K a) from funext hpt]
    rw [MeasureTheory.integral_sub hFi hKi, hKzero, sub_zero]
  rw [hmain]

end Work.CoreResiduals.BiotSavart

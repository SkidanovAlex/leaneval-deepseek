import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.BiotSavart.setIntegral_norm_sub_rpow_le
import Submission.Work.FTS.BSSwirl.residualIntegralBound
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.LWP.BiotSavart.nearField_bound
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.integral_crossL_kf_split =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set

-- The interface of this lemma carries the hypotheses `hM`, `hΔ`, `hx` (the bound on the vorticity
-- slice, the radius of the cut-off ball and the location of the centre) because callers use them to
-- control the two pieces; the *splitting identity* itself needs only that the integrand be
-- integrable on the bounded ball `B(0,ρ)` — which is `integrableOn_crossL_kf_ball`, proved by a
-- single domination — while `hΔ` and `hx` enter the two-piece estimates (the outer piece being
-- bounded by `M * (Δ/2)⁻²`), not the identity.  Hence they are deliberately not referenced here.
set_option linter.unusedVariables false

/-- **Splitting the Biot–Savart integral at a fixed centre.**

For a vorticity slice bounded by `M ≥ 0` and `x ∈ B(x₀,Δ/2)` with `Δ > 0`, the integral of the
Biot–Savart integrand over the fixed ball `B(0,ρ)` is the sum of its parts over
`B(0,ρ) ∩ B(x₀,Δ)` and over `B(0,ρ) \ B(x₀,Δ)`.

The two pieces are integrable (which is what makes the split legitimate): on the inner piece the
integrand is dominated by `M ‖x - ·‖⁻²` (an integrable singular weight on a bounded set, cf.
`Work.CoreResiduals.BiotSavart.integral_ball_sub_norm_rpow`), and on the outer piece by the
constant `M * (Δ/2)⁻²` on the finite-measure set `B(0,ρ)` (using `‖x - a‖ ≥ Δ/2`, which is where
`hx` is used). Measurability of the integrand comes from
`Work.LWP.BiotSavart.aestronglyMeasurable_bsK` together with
`Work.StabilityFar.Decay.bsK_eq_crossL`. -/
theorem integral_crossL_kf_split {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {M ρ Δ : ℝ} {x₀ x : Work.LWP.R3} {t : ℝ}
    (hM : 0 ≤ M) (hbdd : ∀ y : Work.LWP.R3, ‖ω y t‖ ≤ M)
    (hmeas : MeasureTheory.AEStronglyMeasurable (ω · t) MeasureTheory.volume)
    (hΔ : 0 < Δ) (hx : ‖x - x₀‖ ≤ Δ / 2) :
    (∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
        Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a)))
      = (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
            Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a)))
        + (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
            Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a))) := by
  -- The integrand is Bochner-integrable on the bounded ball `B(0,ρ)`: the weight
  -- `‖kf (x - a)‖ = ‖x - a‖⁻²` has a singularity of order `2 < 3` in dimension three, so it may be
  -- integrated across `a = x`.
  have hf_int : MeasureTheory.IntegrableOn
      (fun a : Work.LWP.R3 =>
        Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a)))
      (Metric.ball (0 : Work.LWP.R3) ρ) MeasureTheory.volume :=
    integrableOn_crossL_kf_ball hM hbdd hmeas
  -- `B(0,ρ) = (B(0,ρ) ∩ B(x₀,Δ)) ⊔ (B(0,ρ) \ B(x₀,Δ))` is a partition into measurable sets, so
  -- the integral over `B(0,ρ)` is the sum of the integrals over the two parts.
  exact (MeasureTheory.integral_inter_add_sdiff₀
    (s := Metric.ball (0 : Work.LWP.R3) ρ) (t := Metric.ball x₀ Δ)
    measurableSet_ball.nullMeasurableSet hf_int).symm

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.FTS.BSSwirl.hasFDerivAt_newtonPotential =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter Set
open scoped Topology ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-! ## The main theorem -/

theorem hasFDerivAt_newtonPotential {ω : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3} {R M : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hbdd : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (x : Work.FTS.BSSwirl.R3) :
    HasFDerivAt (Work.FTS.BSSwirl.newtonPotential ω) (Work.FTS.BSSwirl.potDeriv ω x) x := by
  classical
  -- the candidate derivative, as a Bochner integral of operators
  set A : R3 →L[ℝ] R3 := ∫ y, (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ •
    (innerSL ℝ (y - x)).smulRight (ω y) with hA
  have hintK : Integrable (fun y => (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ •
      (innerSL ℝ (y - x)).smulRight (ω y)) volume :=
    integrable_potDeriv_kernel' hM hbdd hsupp hmeas x
  have hint1 : ∀ u : R3, Integrable (fun y => (‖u - y‖)⁻¹ • ω y) volume :=
    fun u => integrable_inv_norm_smul hM hbdd hsupp hmeas u
  have hint3 : ∀ h : R3, Integrable
      (fun y => ((‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y) volume :=
    fun h => integrable_inv_cube_inner_smul' hM hbdd hsupp hmeas x h
  -- the derivative, tested on a vector
  have hAapply : ∀ h : R3, A h = -∫ y, ((‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y := by
    intro h
    rw [hA, ContinuousLinearMap.integral_apply hintK h]
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hsub : inner ℝ (y - x) h = -inner ℝ (x - y) h := by
      rw [inner_sub_left, inner_sub_left]
      ring
    show (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ • ((innerSL ℝ (y - x)).smulRight (ω y)) h
      = -(((‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y)
    rw [ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, hsub, neg_smul, smul_neg, smul_smul]
  -- the residual identity
  have hkey : ∀ h : R3, (∫ y, (‖(x + h) - y‖)⁻¹ • ω y)
      - (∫ y, (‖x - y‖)⁻¹ • ω y) - A h
      = ∫ y, ((‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
          + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y := by
    intro h
    have h1 := hint1 (x + h)
    have h2 := hint1 x
    have h3 := hint3 h
    have e1 : (∫ y, (‖(x + h) - y‖)⁻¹ • ω y) - (∫ y, (‖x - y‖)⁻¹ • ω y)
        = ∫ y, ((‖(x + h) - y‖)⁻¹ • ω y - (‖x - y‖)⁻¹ • ω y) :=
      (integral_sub h1 h2).symm
    have e2 : (∫ y, ((‖(x + h) - y‖)⁻¹ • ω y - (‖x - y‖)⁻¹ • ω y))
        + (∫ y, ((‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y)
        = ∫ y, (((‖(x + h) - y‖)⁻¹ • ω y - (‖x - y‖)⁻¹ • ω y)
            + ((‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y) :=
      (integral_add (h1.sub h2) h3).symm
    rw [hAapply h, sub_neg_eq_add, e1, e2]
    congr 1
    funext y
    rw [add_smul, sub_smul]
  -- the little-o estimate
  set D : ℝ := |R| + ‖x‖ + 1 with hDD
  have hDnn : 0 ≤ D := by rw [hDD]; positivity
  have hbd : ∀ h : R3, ‖(∫ y, (‖(x + h) - y‖)⁻¹ • ω y)
      - (∫ y, (‖x - y‖)⁻¹ • ω y) - A h‖
      ≤ M * (34 * Real.pi * ‖h‖ ^ 2
          + 80000 * Real.pi * Real.sqrt D * ‖h‖ ^ ((3 : ℝ) / 2)) := by
    intro h
    rw [hkey h]
    exact residual_integral_bound hM hbdd hsupp hmeas x h
  have hbigO : (fun h : R3 => (∫ y, (‖(x + h) - y‖)⁻¹ • ω y)
      - (∫ y, (‖x - y‖)⁻¹ • ω y) - A h)
      =O[𝓝 0] (fun h : R3 => ‖h‖ ^ ((3 : ℝ) / 2)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨M * (34 * Real.pi + 80000 * Real.pi * Real.sqrt D), ?_⟩
    filter_upwards [Metric.ball_mem_nhds (0 : R3) one_pos] with h hh
    have hnorm : ‖h‖ < 1 := by simpa [dist_eq_norm] using hh
    have hr0 : 0 ≤ ‖h‖ := norm_nonneg h
    have h2 : ‖h‖ ^ 2 ≤ ‖h‖ ^ ((3 : ℝ) / 2) := by
      rcases eq_or_lt_of_le hr0 with h0 | hpos
      · rw [← h0]
        norm_num
      · have h3h : ‖h‖ ^ ((3 : ℝ) / 2) = ‖h‖ * Real.sqrt ‖h‖ := by
          rw [Real.sqrt_eq_rpow, show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num,
            Real.rpow_add hpos, Real.rpow_one]
        have hsq : ‖h‖ ^ 2 = ‖h‖ * ‖h‖ := by ring
        rw [h3h, hsq]
        refine mul_le_mul_of_nonneg_left ?_ hr0
        rw [Real.le_sqrt hr0 hr0]
        calc ‖h‖ ^ 2 = ‖h‖ * ‖h‖ := by ring
          _ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right hnorm.le hr0
          _ = ‖h‖ := by rw [one_mul]
    have hrow : (‖h‖ ^ ((3 : ℝ) / 2)) = ‖‖h‖ ^ ((3 : ℝ) / 2)‖ :=
      (Real.norm_of_nonneg (Real.rpow_nonneg hr0 _)).symm
    rw [← hrow]
    calc ‖(∫ y, (‖(x + h) - y‖)⁻¹ • ω y) - (∫ y, (‖x - y‖)⁻¹ • ω y) - A h‖
        ≤ M * (34 * Real.pi * ‖h‖ ^ 2
            + 80000 * Real.pi * Real.sqrt D * ‖h‖ ^ ((3 : ℝ) / 2)) := hbd h
      _ ≤ M * ((34 * Real.pi + 80000 * Real.pi * Real.sqrt D) * ‖h‖ ^ ((3 : ℝ) / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hM
          calc 34 * Real.pi * ‖h‖ ^ 2 + 80000 * Real.pi * Real.sqrt D * ‖h‖ ^ ((3 : ℝ) / 2)
              ≤ 34 * Real.pi * ‖h‖ ^ ((3 : ℝ) / 2)
                + 80000 * Real.pi * Real.sqrt D * ‖h‖ ^ ((3 : ℝ) / 2) := by
                linarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 34 * Real.pi)]
            _ = (34 * Real.pi + 80000 * Real.pi * Real.sqrt D) * ‖h‖ ^ ((3 : ℝ) / 2) := by ring
      _ = M * (34 * Real.pi + 80000 * Real.pi * Real.sqrt D) * ‖h‖ ^ ((3 : ℝ) / 2) := by ring
  have hstep : HasFDerivAt (fun z : R3 => ∫ y, (‖z - y‖)⁻¹ • ω y) A x := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    exact hbigO.trans_isLittleO littleO_norm_rpow_three_halves
  -- multiply by the normalisation constant and identify the potential and the derivative
  have hstep2 : HasFDerivAt ((4 * Real.pi)⁻¹ • fun z : R3 => ∫ y, (‖z - y‖)⁻¹ • ω y)
      ((4 * Real.pi)⁻¹ • A) x := hstep.const_smul _
  have hfun : ((4 * Real.pi)⁻¹ • fun z : R3 => ∫ y, (‖z - y‖)⁻¹ • ω y) = newtonPotential ω := by
    funext z
    rfl
  rw [hfun] at hstep2
  have hderiv : (4 * Real.pi)⁻¹ • A = potDeriv ω x := by
    rw [hA, potDeriv]
  rw [hderiv] at hstep2
  exact hstep2

end

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.lintegral_inv_norm_mul_ball_indicator_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Riesz-kernel `lintegral` over a ball, in indicator form

For `x ∈ ℝ³`, `r ≥ 0` and `‖x‖ ≤ A`,

`∫⁻ y, ‖x - y‖⁻¹ · 1_{B(0,r)}(y) ≤ 2π (r + A + 1)²`.

This is the `lintegral` (indicator) form of `setIntegral_norm_sub_rpow_le` at the exponent
`-1 = -2 - α` with `α = -1 < 1`: the ball `B(0,r)` is contained in `B(x, ‖x‖ + r + 1)`, the
integrand is a radial power of the distance to its own singularity, and
`∫⁻_{B(0,ρ)} ‖z‖^{-1} = ofReal (4π ρ²/2) = ofReal (2π ρ²)` by `lintegral_ball_norm_rpow`
(with `s = -1`, so `s + 3 = 2`) and translation invariance `lintegral_ball_sub_eq`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Work.FTS.BSSwirl

theorem lintegral_inv_norm_mul_ball_indicator_le (x : Work.FTS.BSSwirl.R3) {r A : ℝ}
    (hr : 0 ≤ r) (hx : ‖x‖ ≤ A) :
    ∫⁻ y : Work.FTS.BSSwirl.R3, ENNReal.ofReal ((‖x - y‖)⁻¹) *
        ENNReal.ofReal
          ((Metric.closedBall (0 : Work.FTS.BSSwirl.R3) r).indicator (fun _ => (1 : ℝ)) y)
      ≤ ENNReal.ofReal (2 * Real.pi * (r + A + 1) ^ 2) := by
  classical
  -- The product with the `ℝ`-valued indicator is the `ℝ≥0∞`-valued indicator of the ball.
  have hcongr : (fun y : R3 => ENNReal.ofReal ((‖x - y‖)⁻¹) *
        ENNReal.ofReal ((Metric.closedBall (0 : R3) r).indicator (fun _ => (1 : ℝ)) y))
      = fun y : R3 => (Metric.closedBall (0 : R3) r).indicator
          (fun y => ENNReal.ofReal ((‖x - y‖)⁻¹)) y := by
    funext y
    by_cases hy : y ∈ Metric.closedBall (0 : R3) r
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      simp
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
      simp
  rw [hcongr, lintegral_indicator Metric.isClosed_closedBall.measurableSet
    (fun y => ENNReal.ofReal ((‖x - y‖)⁻¹))]
  set ρ : ℝ := ‖x‖ + r + 1 with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; linarith [norm_nonneg x, hr]
  have hρpos : 0 < ρ := by rw [hρ]; linarith [norm_nonneg x, hr]
  -- The ball `B(0,r)` sits inside `B(x,ρ)`.
  have hsub : Metric.closedBall (0 : R3) r ⊆ Metric.ball x ρ := by
    intro a ha
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at ha
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : ‖a - x‖ ≤ ‖a‖ + ‖x‖ := norm_sub_le a x
    calc ‖a - x‖ ≤ ‖a‖ + ‖x‖ := h1
      _ ≤ r + ‖x‖ := by linarith
      _ < ρ := by rw [hρ]; linarith
  have hchain : ∫⁻ y in Metric.closedBall (0 : R3) r, ENNReal.ofReal ((‖x - y‖)⁻¹)
      ≤ ENNReal.ofReal (2 * Real.pi * (r + A + 1) ^ 2) := by
    calc ∫⁻ y in Metric.closedBall (0 : R3) r, ENNReal.ofReal ((‖x - y‖)⁻¹)
        ≤ ∫⁻ y in Metric.ball x ρ, ENNReal.ofReal ((‖x - y‖)⁻¹) := lintegral_mono_set hsub
      _ = ∫⁻ y in Metric.ball x ρ, ENNReal.ofReal (‖x - y‖ ^ (-1:ℝ)) := by
            apply lintegral_congr; intro y; rw [Real.rpow_neg_one]
      _ = ∫⁻ y in Metric.ball x ρ, ENNReal.ofReal (‖y - x‖ ^ (-1:ℝ)) := by
            apply lintegral_congr; intro y; rw [norm_sub_rev]
      _ = ∫⁻ z in Metric.ball (0 : R3) ρ, ENNReal.ofReal (‖z‖ ^ (-1:ℝ)) :=
            Work.CoreResiduals.BiotSavart.lintegral_ball_sub_eq x ρ
              (fun z => ENNReal.ofReal (‖z‖ ^ (-1:ℝ)))
      _ = ENNReal.ofReal (4 * Real.pi * ρ ^ ((-1:ℝ) + 3) / ((-1:ℝ) + 3)) :=
            Work.CoreResiduals.BiotSavart.lintegral_ball_norm_rpow (-1) (by norm_num) ρ hρpos
      _ = ENNReal.ofReal (2 * Real.pi * ρ ^ 2) := by
            congr 1
            rw [show ((-1:ℝ) + 3) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            ring
      _ ≤ ENNReal.ofReal (2 * Real.pi * (r + A + 1) ^ 2) := by
            apply ENNReal.ofReal_le_ofReal
            have hρle : ρ ≤ r + A + 1 := by rw [hρ]; linarith
            have hsq : ρ ^ 2 ≤ (r + A + 1) ^ 2 := pow_le_pow_left₀ hρ0 hρle 2
            nlinarith [Real.pi_pos, hsq]
  exact hchain

end Work.FTS.BSSwirl
end

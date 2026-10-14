import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.LWP.BiotSavart.nearField_bound
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.decay_aux
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
import Submission.Work.StabilityFar.Defs
import Submission.Work.StabilityFar.Holder.holderOnWith_of_norm_le
import Submission.Work.StabilityFar.St5
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.IntegrandDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay

/-- The integrand of the candidate derivative `bsDerivCLM ω ρ x` of the Biot–Savart field at `x`:
`a ↦ (crossL (ω a - ω x)).comp (kDerivCLM (x - a))`. -/
noncomputable def bsIntegrand (ω : R3 → R3) (x a : R3) : R3 →L[ℝ] R3 :=
  (crossL (ω a - ω x)).comp (kDerivCLM (x - a))

@[simp]
theorem bsIntegrand_apply (ω : R3 → R3) (x a v : R3) :
    bsIntegrand ω x a v = crossL (ω a - ω x) (kDerivCLM (x - a) v) := rfl

/-- `crossL 0 = 0`. -/
theorem crossL_zero : crossL (0 : R3) = (0 : R3 →L[ℝ] R3) := by
  have h := crossL_sub (0 : R3) 0
  simpa using h

/-- **Pointwise bound for the derivative integrand.**  For a `c`-Hölder vorticity with constant
`C ≥ 0` one has `‖bsIntegrand ω x a‖ ≤ 4 C ‖x - a‖^{c-3}`; the exponent `c - 3 > -3` makes this
absolutely integrable in `a` over any bounded set. -/
theorem norm_bsIntegrand_le {ω : R3 → R3} {C c : ℝ} (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c) (x a : R3) :
    ‖bsIntegrand ω x a‖ ≤ 4 * C * (‖x - a‖ : ℝ) ^ (c - 3) := by
  by_cases hxa : x = a
  · have hzero : bsIntegrand ω x a = 0 := by
      simp only [bsIntegrand, hxa, sub_self, crossL_zero, ContinuousLinearMap.zero_comp]
    rw [hzero, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg (norm_nonneg _) _)
  · have hpos : 0 < ‖x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxa)
    have h1 : ‖bsIntegrand ω x a‖ ≤ ‖ω a - ω x‖ * (4 / ‖x - a‖ ^ (3 : ℕ)) := by
      calc ‖bsIntegrand ω x a‖
          ≤ ‖crossL (ω a - ω x)‖ * ‖kDerivCLM (x - a)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖ω a - ω x‖ * (4 / ‖x - a‖ ^ (3 : ℕ)) := by
            exact mul_le_mul (norm_crossL_le _)
              (norm_kDerivCLM_le (x - a) ‖x - a‖ hpos le_rfl)
              (norm_nonneg _) (norm_nonneg _)
    have h2 : ‖ω a - ω x‖ ≤ C * ‖x - a‖ ^ c := by
      simpa only [norm_sub_rev] using hhold a x
    have h3 : (C * ‖x - a‖ ^ c) * (4 / ‖x - a‖ ^ (3 : ℕ))
        = 4 * C * (‖x - a‖ : ℝ) ^ (c - 3) := by
      have hsub : (‖x - a‖ : ℝ) ^ (c - 3) = (‖x - a‖ : ℝ) ^ c / (‖x - a‖ : ℝ) ^ (3 : ℝ) :=
        Real.rpow_sub hpos c 3
      rw [hsub, Real.rpow_ofNat]
      ring
    calc ‖bsIntegrand ω x a‖
        ≤ (C * ‖x - a‖ ^ c) * (4 / ‖x - a‖ ^ (3 : ℕ)) :=
          le_trans h1 (mul_le_mul_of_nonneg_right h2 (by positivity))
      _ = 4 * C * (‖x - a‖ : ℝ) ^ (c - 3) := h3

/-- The derivative integrand is ae-strongly-measurable in `a` whenever the vorticity is
continuous. -/
theorem aestronglyMeasurable_bsIntegrand {ω : R3 → R3} (hω : Continuous ω) (x : R3) :
    AEStronglyMeasurable (bsIntegrand ω x) volume := by
  have hω' : AEStronglyMeasurable (fun a : R3 => ω a - ω x) volume :=
    (hω.sub continuous_const).aestronglyMeasurable
  have h := aestronglyMeasurable_bsDerivIntegrand hω' x
  exact h

/-- The derivative integrand is continuous in `x` at every point `x₀ ≠ a`. -/
theorem continuousAt_bsIntegrand {ω : R3 → R3} (hω : Continuous ω) {x₀ a : R3} (ha : a ≠ x₀) :
    ContinuousAt (fun x : R3 => bsIntegrand ω x a) x₀ := by
  have h1 : ContinuousAt (fun x : R3 => crossL (ω a - ω x)) x₀ :=
    continuous_crossL.continuousAt.comp (continuousAt_const.sub hω.continuousAt)
  have hsub : ContinuousAt (fun x : R3 => x - a) x₀ := continuousAt_id.sub continuousAt_const
  have h2 : ContinuousAt (fun x : R3 => kDerivCLM (x - a)) x₀ :=
    ContinuousAt.comp (f := fun y : R3 => y - a) (x := x₀) (g := kDerivCLM)
      (continuousAt_kDerivCLM (b := x₀ - a) (show x₀ - a ≠ 0 from sub_ne_zero.mpr (Ne.symm ha)))
      hsub
  simpa only [bsIntegrand] using h1.clm_comp h2

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.KfBall.integrableOn_kf_ball =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter
open scoped Topology

set_option autoImplicit false

namespace Work.CoreResiduals.BiotSavart.KfBall

theorem integrableOn_kf_ball (z : Work.LWP.R3) (ρ : ℝ) :
    MeasureTheory.IntegrableOn (Work.StabilityFar.Decay.kf) (Metric.ball z ρ) := by
  -- `kf` is Borel measurable (it is `b ↦ (‖b‖³)⁻¹ • b`).
  have hmeas : MeasureTheory.AEStronglyMeasurable Work.StabilityFar.Decay.kf
      (volume : Measure Work.LWP.R3) := by
    unfold Work.StabilityFar.Decay.kf
    measurability
  have hfin : Module.finrank ℝ Work.LWP.R3 = 3 := by
    simp [Work.LWP.R3, finrank_euclideanSpace]
  -- Local integrability around the origin via the `2 < 3` layer-cake bound.
  refine (MeasureTheory.integrableOn_ball_of_norm_le_rpow
      (μ := (volume : Measure Work.LWP.R3))
      (f := Work.StabilityFar.Decay.kf) (C := 1) (α := 2) (r := ‖z‖ + ρ)
      ?_ ?_ ?_ hmeas).mono_set ?_
  · -- `1 ≤ finrank ℝ ℝ³`
    rw [hfin]; norm_num
  · -- `2 < finrank ℝ ℝ³`
    rw [hfin]; norm_num
  · -- `‖kf x‖ ≤ 1 * ‖x‖^(-2)`
    filter_upwards with x
    rw [Work.CoreResiduals.BiotSavart.norm_kf_eq x]
    simp
  · -- `B(z,ρ) ⊆ B(0, ‖z‖ + ρ)`
    intro a ha
    rw [Metric.mem_ball] at ha ⊢
    have h1 : dist a 0 ≤ dist a z + dist z 0 := dist_triangle a z 0
    rw [dist_zero_right, dist_zero_right] at h1
    rw [dist_zero_right]
    linarith

end Work.CoreResiduals.BiotSavart.KfBall
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.bsField_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric

/-- **Additivity of the `bsField` integral under a shift of the evaluation point.**

`bsField ω ρ` is the Bochner integral over the fixed ball `B(0,ρ)` of the integrand
`a ↦ crossL (ω a) (kf (· - a))`.  The Bochner integral is additive in the integrand, so the
difference of the two integrals at `x + h` and at `x` is the integral of the difference — the
only content being that both shifted integrands are absolutely integrable, which is
`Work.StabilityFar.Decay.integrable_bsK_supported` transported along
`Work.StabilityFar.Decay.bsK_eq_crossL`. -/
theorem bsField_sub {ω : Work.LWP.R3 → Work.LWP.R3} {R M : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ a, ‖ω a‖ ≤ M) (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume) (ρ : ℝ) (x h : Work.LWP.R3) :
    Work.CoreResiduals.BiotSavart.bsField ω ρ (x + h) - Work.CoreResiduals.BiotSavart.bsField ω ρ x
      = ∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
          Work.StabilityFar.Decay.crossL (ω a)
            (Work.StabilityFar.Decay.kf (x + h - a) - Work.StabilityFar.Decay.kf (x - a)) := by
  -- The integrand `a ↦ crossL (ω a) (kf (y - a))` is `bsK ω y`, hence absolutely integrable on
  -- all of `ℝ³` for `y = x` and `y = x + h`.
  have hI1 : MeasureTheory.Integrable
      (fun a => Work.StabilityFar.Decay.crossL (ω a) (Work.StabilityFar.Decay.kf (x + h - a)))
      MeasureTheory.volume :=
    (Work.StabilityFar.Decay.integrable_bsK_supported hM hbdd hs hm (x + h)).congr
      (Filter.Eventually.of_forall fun a =>
        Work.StabilityFar.Decay.bsK_eq_crossL ω (x + h) a)
  have hI2 : MeasureTheory.Integrable
      (fun a => Work.StabilityFar.Decay.crossL (ω a) (Work.StabilityFar.Decay.kf (x - a)))
      MeasureTheory.volume :=
    (Work.StabilityFar.Decay.integrable_bsK_supported hM hbdd hs hm x).congr
      (Filter.Eventually.of_forall fun a =>
        Work.StabilityFar.Decay.bsK_eq_crossL ω x a)
  -- Restricting to the ball `B(0,ρ)` preserves integrability.
  have h1 : MeasureTheory.Integrable
      (fun a => Work.StabilityFar.Decay.crossL (ω a) (Work.StabilityFar.Decay.kf (x + h - a)))
      (MeasureTheory.volume.restrict (Metric.ball (0 : Work.LWP.R3) ρ)) := hI1.integrableOn
  have h2 : MeasureTheory.Integrable
      (fun a => Work.StabilityFar.Decay.crossL (ω a) (Work.StabilityFar.Decay.kf (x - a)))
      (MeasureTheory.volume.restrict (Metric.ball (0 : Work.LWP.R3) ρ)) := hI2.integrableOn
  -- Unfold the two `bsField`s into the corresponding restricted Bochner integrals.
  rw [Work.CoreResiduals.BiotSavart.bsField.eq_def, Work.CoreResiduals.BiotSavart.bsField.eq_def]
  -- Move the linear map `crossL (ω a)` inside the difference, pointwise in `a`.
  rw [show (∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
        Work.StabilityFar.Decay.crossL (ω a)
          (Work.StabilityFar.Decay.kf (x + h - a) - Work.StabilityFar.Decay.kf (x - a)))
      = ∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
          (Work.StabilityFar.Decay.crossL (ω a) (Work.StabilityFar.Decay.kf (x + h - a))
            - Work.StabilityFar.Decay.crossL (ω a) (Work.StabilityFar.Decay.kf (x - a))) by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with a
        exact map_sub (Work.StabilityFar.Decay.crossL (ω a)) _ _]
  -- Split the integral of the difference using integrability of both pieces.
  rw [MeasureTheory.integral_sub h1 h2]

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.continuousAt_integral_crossL_kf_diff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter Topology
open scoped Topology

set_option maxHeartbeats 1000000

namespace Work.CoreResiduals.BiotSavart

/-- **Continuity of the parametrised Biot–Savart integral over a fixed set avoiding a ball.**

For a spacetime vorticity `ω` obeying the uniform bound `‖ω a t‖ ≤ M` on the window
`|t - t₀| < δ`, with ae-strongly-measurable slices there and continuous in `t` at `t₀` for every
fixed `a`, the map

`(x,t) ↦ ∫ a in B(0,ρ) \ B(x₀,Δ), crossL (ω a t) (kf (x - a))`

is continuous at `(x₀,t₀)`, for any `ρ` and any `Δ > 0`.

This is the "outer piece" of the peel-off argument: the integration set is *fixed* (it does not
depend on `x`), and for `x ∈ B(x₀,Δ/2)` the integrand is bounded on it by the constant
`M * (Δ/2)⁻²`, since `a ∉ B(x₀,Δ)` gives `‖x - a‖ ≥ Δ/2`; so dominated convergence
(`MeasureTheory.continuousAt_of_dominated`) applies, the dominating function being the
`B(0,ρ)`-indicator of that constant. For fixed `a ≠ x₀` the integrand
`(x,t) ↦ crossL (ω a t) (kf (x - a))` is continuous at `(x₀,t₀)` (continuity of `crossL`, of `kf`
away from `0`, and `htcont a`).

Useful identifications: `Work.StabilityFar.Decay.bsK_eq_crossL` rewrites
`crossL (ω a t) (kf (x - a))` as `Work.LWP.BiotSavart.bsK (fun y => ω y t) x a`, and
`Work.LWP.BiotSavart.norm_bsK_le` gives the pointwise bound
`‖bsK ω x a‖ ≤ (‖x-a‖^3)⁻¹ * ‖ω a‖ * ‖x-a‖`, while
`Work.LWP.BiotSavart.aestronglyMeasurable_bsK` gives the measurability in `a`. -/
theorem continuousAt_integral_crossL_kf_diff {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {δ M ρ Δ : ℝ} {x₀ : Work.LWP.R3} {t₀ : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hΔ : 0 < Δ)
    (hbdd : ∀ t : ℝ, |t - t₀| < δ → ∀ y : Work.LWP.R3, ‖ω y t‖ ≤ M)
    (hmeas : ∀ t : ℝ, |t - t₀| < δ →
      MeasureTheory.AEStronglyMeasurable (ω · t) MeasureTheory.volume)
    (htcont : ∀ a : Work.LWP.R3, ContinuousAt (fun t : ℝ => ω a t) t₀) :
    ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
      ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
        Work.StabilityFar.Decay.crossL (ω a q.2) (Work.StabilityFar.Decay.kf (q.1 - a)))
      (x₀, t₀) := by
  classical
  set S : Set Work.LWP.R3 := Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball x₀ Δ with hSdef
  have hSmeas : MeasurableSet S := by
    rw [hSdef]; exact measurableSet_ball.diff measurableSet_ball
  have hballfin : volume (Metric.closedBall (0 : Work.LWP.R3) ρ) ≠ ⊤ :=
    (isCompact_closedBall (0 : Work.LWP.R3) ρ).measure_lt_top.ne
  have hSfin : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top hballfin
      (measure_mono (by rw [hSdef]; exact fun a ha => Metric.ball_subset_closedBall ha.1))
  have hbi : Integrable (fun _ : Work.LWP.R3 => M * ((Δ / 2) ^ (2 : ℕ))⁻¹)
      (volume.restrict S) :=
    integrableOn_const hSfin
  have hmain : ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
      ∫ a, Work.StabilityFar.Decay.crossL (ω a q.2) (Work.StabilityFar.Decay.kf (q.1 - a))
        ∂(volume.restrict S)) (x₀, t₀) := by
    apply MeasureTheory.continuousAt_of_dominated (bound := fun _ : Work.LWP.R3 =>
      M * ((Δ / 2) ^ (2 : ℕ))⁻¹)
    · -- a.e. strong measurability of the integrand in `a`
      filter_upwards [Metric.ball_mem_nhds (x₀, t₀) hδ] with q hq
      have hqt : |q.2 - t₀| < δ := by
        have h1 : dist q.2 t₀ ≤ dist q (x₀, t₀) := by
          rw [Prod.dist_eq]; exact le_max_right _ _
        rw [Real.dist_eq] at h1
        exact lt_of_le_of_lt h1 (Metric.mem_ball.mp hq)
      refine MeasureTheory.AEStronglyMeasurable.mono_measure (ν := volume.restrict S) ?_
        MeasureTheory.Measure.restrict_le_self
      rw [show (fun a => Work.StabilityFar.Decay.crossL (ω a q.2)
            (Work.StabilityFar.Decay.kf (q.1 - a)))
          = (fun a => Work.LWP.BiotSavart.bsK (fun y => ω y q.2) q.1 a) from
        funext (fun a => (Work.StabilityFar.Decay.bsK_eq_crossL (fun y => ω y q.2) q.1 a).symm)]
      exact Work.LWP.BiotSavart.aestronglyMeasurable_bsK (hmeas q.2 hqt) q.1
    · -- the constant dominating function
      have hε : (0 : ℝ) < min (Δ / 2) δ := lt_min (by linarith) hδ
      filter_upwards [Metric.ball_mem_nhds (x₀, t₀) hε] with q hq
      have hdq : dist q (x₀, t₀) < min (Δ / 2) δ := Metric.mem_ball.mp hq
      have hd1 : dist q.1 x₀ < Δ / 2 := by
        have h1 : dist q.1 x₀ ≤ dist q (x₀, t₀) := by
          rw [Prod.dist_eq]; exact le_max_left _ _
        exact lt_of_lt_of_le (lt_of_le_of_lt h1 hdq) (min_le_left _ _)
      have hqt : |q.2 - t₀| < δ := by
        have h1 : dist q.2 t₀ ≤ dist q (x₀, t₀) := by
          rw [Prod.dist_eq]; exact le_max_right _ _
        rw [Real.dist_eq] at h1
        exact lt_of_lt_of_le (lt_of_le_of_lt h1 hdq) (min_le_right _ _)
      refine MeasureTheory.ae_restrict_of_forall_mem hSmeas (fun a ha => ?_)
      rw [hSdef] at ha
      have hax : a ≠ x₀ := by
        intro h
        exact ha.2 (by rw [h]; exact Metric.mem_ball_self hΔ)
      have hna : Δ ≤ ‖a - x₀‖ := by
        have h : Δ ≤ dist a x₀ := by
          simpa only [Metric.mem_ball, not_lt] using ha.2
        simpa only [dist_eq_norm] using h
      have hxq : Δ / 2 < ‖q.1 - a‖ := by
        have h1 : ‖a - x₀‖ ≤ ‖a - q.1‖ + ‖q.1 - x₀‖ := by
          have h := norm_add_le (a - q.1) (q.1 - x₀)
          rwa [sub_add_sub_cancel] at h
        have h2 : ‖q.1 - x₀‖ < Δ / 2 := by simpa only [dist_eq_norm] using hd1
        have h3 : ‖a - q.1‖ = ‖q.1 - a‖ := norm_sub_rev _ _
        linarith
      have hpos : 0 < ‖q.1 - a‖ := by linarith
      have hkey : (‖q.1 - a‖ ^ (3 : ℕ))⁻¹ * ‖q.1 - a‖ = (‖q.1 - a‖ ^ (2 : ℕ))⁻¹ := by
        have h3 : ‖q.1 - a‖ ^ (3 : ℕ) = ‖q.1 - a‖ ^ (2 : ℕ) * ‖q.1 - a‖ := by ring
        rw [h3, mul_inv, mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), mul_one]
      have hbsK : ‖Work.StabilityFar.Decay.crossL (ω a q.2)
            (Work.StabilityFar.Decay.kf (q.1 - a))‖
          ≤ (‖q.1 - a‖ ^ (3 : ℕ))⁻¹ * ‖ω a q.2‖ * ‖q.1 - a‖ := by
        rw [← Work.StabilityFar.Decay.bsK_eq_crossL (fun y => ω y q.2) q.1 a]
        exact Work.LWP.BiotSavart.norm_bsK_le _ _ _
      have hstep1 : (‖q.1 - a‖ ^ (3 : ℕ))⁻¹ * ‖ω a q.2‖ * ‖q.1 - a‖
          = ‖ω a q.2‖ * ((‖q.1 - a‖ ^ (2 : ℕ))⁻¹) := by
        rw [show (‖q.1 - a‖ ^ (3 : ℕ))⁻¹ * ‖ω a q.2‖ * ‖q.1 - a‖
            = ‖ω a q.2‖ * ((‖q.1 - a‖ ^ (3 : ℕ))⁻¹ * ‖q.1 - a‖) by ring, hkey]
      have hinv : (‖q.1 - a‖ ^ (2 : ℕ))⁻¹ ≤ ((Δ / 2) ^ (2 : ℕ))⁻¹ := by
        rw [inv_le_inv₀ (by positivity) (by positivity)]
        exact pow_le_pow_left₀ (by positivity) (le_of_lt hxq) 2
      calc ‖Work.StabilityFar.Decay.crossL (ω a q.2) (Work.StabilityFar.Decay.kf (q.1 - a))‖
          ≤ (‖q.1 - a‖ ^ (3 : ℕ))⁻¹ * ‖ω a q.2‖ * ‖q.1 - a‖ := hbsK
        _ = ‖ω a q.2‖ * ((‖q.1 - a‖ ^ (2 : ℕ))⁻¹) := hstep1
        _ ≤ M * ((Δ / 2) ^ (2 : ℕ))⁻¹ :=
            mul_le_mul (hbdd q.2 hqt a) hinv (by positivity) hM
    · exact hbi
    · -- pointwise continuity of the integrand at `(x₀,t₀)` for `a ∈ S`
      refine MeasureTheory.ae_restrict_of_forall_mem hSmeas (fun a ha => ?_)
      rw [hSdef] at ha
      have hax : a ≠ x₀ := by
        intro h
        exact ha.2 (by rw [h]; exact Metric.mem_ball_self hΔ)
      have hne : x₀ - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hax)
      have h1 : ContinuousAt (fun q : Work.LWP.R3 × ℝ => ω a q.2) (x₀, t₀) :=
        (htcont a).comp continuous_snd.continuousAt
      have hsub : ContinuousAt (fun q : Work.LWP.R3 × ℝ => q.1 - a) (x₀, t₀) :=
        ContinuousAt.sub (continuous_fst.continuousAt :
          ContinuousAt (fun q : Work.LWP.R3 × ℝ => q.1) (x₀, t₀))
          (continuousAt_const :
            ContinuousAt (fun _ : Work.LWP.R3 × ℝ => a) (x₀, t₀))
      have h2 : ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
          Work.StabilityFar.Decay.kf (q.1 - a)) (x₀, t₀) :=
        ContinuousAt.comp (x := (x₀, t₀)) (g := Work.StabilityFar.Decay.kf)
          (f := fun q : Work.LWP.R3 × ℝ => q.1 - a)
          ((Work.StabilityFar.Decay.kf_hasFDerivAt (x₀ - a) hne).continuousAt) hsub
      have h3 : ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
          Work.StabilityFar.Decay.crossL (ω a q.2)) (x₀, t₀) :=
        Work.StabilityFar.Decay.continuous_crossL.continuousAt.comp h1
      exact h3.clm_apply h2
  exact hmain

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.integrable_indicator_kDerivCLM_annulus =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric

namespace Work.CoreResiduals.BiotSavart

/-- The derivative of the Newtonian kernel is Bochner-integrable on the annulus
`r < ‖b‖ < ρ`, provided `r > 0`: there the kernel is bounded by the constant `4 r⁻³` and the
annulus has finite volume. -/
theorem integrable_indicator_kDerivCLM_annulus {r ρ : ℝ} (hr : 0 < r) :
    MeasureTheory.Integrable
      ((Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r).indicator
        (fun b => Work.StabilityFar.Decay.kDerivCLM b)) MeasureTheory.volume := by
  classical
  have hmeasSet : MeasurableSet
      (Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r) :=
    Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet
  have hfin : volume (Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r) < ⊤ := by
    calc volume (Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r)
        ≤ volume (Metric.ball (0 : Work.LWP.R3) ρ) := measure_mono Set.sdiff_subset
      _ < ⊤ := measure_ball_lt_top
  -- On the annulus, `b` stays at distance at least `r` from the origin.
  have hb2 : ∀ b ∈ (Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r),
      r ≤ ‖b‖ := by
    intro b hb
    have h := hb.2
    simp only [Metric.mem_ball, dist_zero_right, not_lt] at h
    exact h
  have key : MeasureTheory.IntegrableOn
      (fun b : Work.LWP.R3 => Work.StabilityFar.Decay.kDerivCLM b)
      (Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r) MeasureTheory.volume := by
    refine MeasureTheory.IntegrableOn.of_bound hfin ?_ (4 / r ^ 3) ?_
    · -- measurability: `kDerivCLM` is continuous at every point of the annulus
      apply ContinuousOn.aestronglyMeasurable _ hmeasSet
      intro b hb
      have hb0 : b ≠ 0 := by
        have : 0 < ‖b‖ := lt_of_lt_of_le hr (hb2 b hb)
        exact norm_pos_iff.mp this
      exact (Work.StabilityFar.Decay.continuousAt_kDerivCLM hb0).continuousWithinAt
    · -- the uniform bound `‖kDerivCLM b‖ ≤ 4 / r³`
      filter_upwards [ae_restrict_mem hmeasSet] with b hb
      exact Work.StabilityFar.Decay.norm_kDerivCLM_le b r hr (hb2 b hb)
  exact (MeasureTheory.integrable_indicator_iff
    (f := fun b : Work.LWP.R3 => Work.StabilityFar.Decay.kDerivCLM b) hmeasSet).mpr key

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.lintegral_ball_shift_inv_sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory

/-- **The shifted inverse-square bound.**  For `h : ℝ³`,
`∫⁻_{B(0,2‖h‖)} ‖y+h‖⁻² ≤ 12π‖h‖`.

The singularity `y = -h` sits inside the ball of radius `2‖h‖`, so the estimate is the
borderline `(dim = 3)` case.  It is obtained by translating the centre: every
`y ∈ B(0, 2‖h‖)` satisfies `‖y + h‖ ≤ ‖y‖ + ‖h‖ < 3‖h‖`, i.e. `B(0,2‖h‖) ⊆ B(-h, 3‖h‖)`,
and the inverse-square weight is exactly integrable on a ball about its own singularity
(`Work.LWP.BiotSavart.inv_sq_lintegral_closedBall_le`, `12π‖h‖ = 4π·(3‖h‖)`).

The exponent `-2` is the real power `Real.rpow`, converted to `(‖·‖^2)⁻¹` pointwise by
`inv_natPow_eq_rpow_neg`; the shift `y ↦ y + h` is undone with the translation-invariance
`Work.LWP.BiotSavart.lintegral_closedBall_sub_eq`. -/
theorem lintegral_ball_shift_inv_sq (h : Work.LWP.R3) :
    ∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (‖y + h‖ ^ (-2:ℝ))
      ≤ ENNReal.ofReal (12 * Real.pi * ‖h‖) := by
  -- Pointwise: `‖z‖ ^ (-2 : ℝ) = (‖z‖ ^ 2)⁻¹`.
  have hpt : ∀ z : Work.LWP.R3, ENNReal.ofReal (‖z‖ ^ (-2:ℝ))
      = ENNReal.ofReal ((‖z‖ ^ (2 : ℕ))⁻¹) := by
    intro z
    congr 1
    rw [show (-2 : ℝ) = -(((2 : ℕ)) : ℝ) by norm_num, Real.rpow_neg (norm_nonneg z),
      Real.rpow_natCast]
  -- The ball `B(0, 2‖h‖)` is contained in the ball `B(-h, 3‖h‖)` around the singularity.
  have hsub : Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖) ⊆ Metric.closedBall (-h) (3 * ‖h‖) := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hy
    rw [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add]
    have h1 : ‖y + h‖ ≤ ‖y‖ + ‖h‖ := norm_add_le y h
    linarith
  calc ∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (‖y + h‖ ^ (-2:ℝ))
      = ∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖),
          ENNReal.ofReal ((‖y + h‖ ^ (2 : ℕ))⁻¹) :=
        lintegral_congr (fun y => hpt (y + h))
    _ ≤ ∫⁻ y in Metric.closedBall (-h) (3 * ‖h‖), ENNReal.ofReal ((‖y + h‖ ^ (2 : ℕ))⁻¹) :=
        lintegral_mono_set hsub
    _ = ∫⁻ y in Metric.closedBall (-h) (3 * ‖h‖),
          ENNReal.ofReal ((‖y - (-h)‖ ^ (2 : ℕ))⁻¹) := by
        apply lintegral_congr; intro y; rw [sub_neg_eq_add]
    _ = ∫⁻ z in Metric.closedBall (0 : Work.LWP.R3) (3 * ‖h‖),
          ENNReal.ofReal ((‖z‖ ^ (2 : ℕ))⁻¹) :=
        Work.LWP.BiotSavart.lintegral_closedBall_sub_eq (-h) (3 * ‖h‖)
          (fun z => ENNReal.ofReal ((‖z‖ ^ (2 : ℕ))⁻¹))
    _ ≤ ENNReal.ofReal (4 * Real.pi * (3 * ‖h‖)) :=
        Work.LWP.BiotSavart.inv_sq_lintegral_closedBall_le (3 * ‖h‖)
          (by positivity)
    _ = ENNReal.ofReal (12 * Real.pi * ‖h‖) := by congr 1; ring

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.norm_resid_le_far =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay (kf kDerivCLM)

/-! ## Two general ingredients -/

/-- **The far part of a small segment stays away from the origin.**  If `2‖h‖ ≤ ‖y‖` then every
point `x` of the segment `[y, y+h]` satisfies `‖y‖/2 ≤ ‖x‖`. -/
lemma half_norm_le_norm_of_mem_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y h x : E} (hy : 2 * ‖h‖ ≤ ‖y‖) (hx : x ∈ segment ℝ y (y + h)) : ‖y‖ / 2 ≤ ‖x‖ := by
  have hsub : ‖x - y‖ ≤ ‖h‖ := by
    have := norm_sub_le_of_mem_segment (x := y) (z := y + h) hx
    simpa using this
  have hsplit : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
    have := norm_add_le (y - x) x
    simpa using this
  rw [norm_sub_rev] at hsplit
  linarith

/-- **Second-order Taylor estimate from a Lipschitz bound on the derivative.**  If `f` is
differentiable on the segment `[y, y+h]` with derivative `f'`, and `f'` is `L`-Lipschitz on that
segment (`‖f' x - f' y‖ ≤ L ‖x - y‖`, `L ≥ 0`), then the Taylor residual of order two is
quadratic:

  `‖f (y + h) - f y - f' y h‖ ≤ L ‖h‖²`.

This is the mean value inequality with the subtracted linear map `f' y`. -/
lemma norm_taylor_second_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {f' : E → E →L[ℝ] F} {y h : E} {L : ℝ} (hL : 0 ≤ L)
    (hdiff : ∀ x ∈ segment ℝ y (y + h), HasFDerivWithinAt f (f' x) (segment ℝ y (y + h)) x)
    (hlip : ∀ x ∈ segment ℝ y (y + h), ‖f' x - f' y‖ ≤ L * ‖x - y‖) :
    ‖f (y + h) - f y - f' y h‖ ≤ L * ‖h‖ ^ 2 := by
  have hmain := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f := f) (f' := f') (φ := f' y) (C := L * ‖h‖) (s := segment ℝ y (y + h))
      (x := y) (y := y + h) hdiff
      (fun x hx => by
        have hb : ‖x - y‖ ≤ ‖h‖ := by
          have := norm_sub_le_of_mem_segment (x := y) (z := y + h) hx
          simpa using this
        calc ‖f' x - f' y‖ ≤ L * ‖x - y‖ := hlip x hx
          _ ≤ L * ‖h‖ := by gcongr)
      (convex_segment y (y + h)) (left_mem_segment ℝ y (y + h)) (right_mem_segment ℝ y (y + h))
  simpa [add_sub_cancel_left, pow_two, mul_assoc] using hmain

/-! ## The far-field bound for the kernel residual -/

/-- **Far-field bound for the second-order Taylor residual of the Newtonian kernel.**  If the
increment is small compared with the base point (`2‖h‖ ≤ ‖y‖`), then

  `‖resid h y‖ ≤ 1024 ‖h‖² ‖y‖^{-4}`.

The constant comes from `‖kDerivCLM x - kDerivCLM y‖ ≤ 64 (‖y‖/2)⁻⁴ ‖x - y‖` on the segment. -/
theorem norm_resid_le_far (h y : Work.LWP.R3) (hy : 2 * ‖h‖ ≤ ‖y‖) :
    ‖Work.CoreResiduals.BiotSavart.resid h y‖ ≤ 1024 * ‖h‖ ^ (2:ℕ) * ‖y‖ ^ (-4:ℝ) := by
  by_cases hh : h = 0
  · subst hh
    simp [Work.CoreResiduals.BiotSavart.resid]
  · have hposh : 0 < ‖h‖ := norm_pos_iff.mpr hh
    have hposy : 0 < ‖y‖ := by linarith
    have hhalf : ∀ x ∈ segment ℝ y (y + h), ‖y‖ / 2 ≤ ‖x‖ :=
      fun x hx => half_norm_le_norm_of_mem_segment hy hx
    -- the kernel is differentiable on the segment, since `0` is at distance `‖y‖/2` from it
    have hdiff : ∀ x ∈ segment ℝ y (y + h),
        HasFDerivWithinAt kf (kDerivCLM x) (segment ℝ y (y + h)) x := by
      intro x hx
      have hx0 : x ≠ 0 := by
        have h1 : 0 < ‖y‖ / 2 := by linarith
        exact norm_pos_iff.mp (by linarith [hhalf x hx])
      exact (Work.StabilityFar.Decay.kf_hasFDerivAt x hx0).hasFDerivWithinAt
    -- the derivative is `64 (‖y‖/2)⁻⁴`-Lipschitz on the segment
    have hlip : ∀ x ∈ segment ℝ y (y + h),
        ‖kDerivCLM x - kDerivCLM y‖ ≤ 64 / (‖y‖ / 2) ^ 4 * ‖x - y‖ := by
      intro x hx
      exact Work.StabilityFar.Decay.norm_kDerivCLM_sub_le x y (‖y‖ / 2) (by linarith)
        (hhalf x hx) (by linarith)
    have hkey : ‖Work.CoreResiduals.BiotSavart.resid h y‖
        ≤ 64 / (‖y‖ / 2) ^ 4 * ‖h‖ ^ 2 :=
      norm_taylor_second_le (by positivity) hdiff hlip
    refine hkey.trans_eq ?_
    have h64 : (64:ℝ) / (‖y‖ / 2) ^ 4 = 1024 / ‖y‖ ^ 4 := by
      field_simp
      ring
    rw [h64, div_eq_mul_inv,
      Work.CoreResiduals.BiotSavart.inv_natPow_eq_rpow_neg ‖y‖ (norm_nonneg y) 4]
    ring_nf

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.norm_resid_mul_rpow_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- Weighted form of the crude residual bound `norm_resid_le_crude`: multiplying by the
homogeneous weight `‖y‖ ^ c` converts the two `‖y‖ ^ (-2)`, `‖y‖ ^ (-3)` factors into
`‖y‖ ^ (c - 2)`, `‖y‖ ^ (c - 3)` (the case `y = 0` being immediate). -/
theorem norm_resid_mul_rpow_le {c : ℝ} (hc : 0 < c) (h y : Work.LWP.R3) :
    ‖y‖ ^ c * ‖Work.CoreResiduals.BiotSavart.resid h y‖
      ≤ ‖y‖ ^ c * ‖y + h‖ ^ (-2:ℝ) + ‖y‖ ^ (c - 2) + 4 * ‖h‖ * ‖y‖ ^ (c - 3) := by
  by_cases hy : ‖y‖ = 0
  · rw [hy, Real.zero_rpow (ne_of_gt hc), zero_mul, zero_mul, zero_add]
    have h1 : 0 ≤ (0:ℝ) ^ (c - 2) := Real.rpow_nonneg le_rfl _
    have h2 : 0 ≤ 4 * ‖h‖ * (0:ℝ) ^ (c - 3) := by positivity
    linarith
  · have hypos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy)
    have hcrude := norm_resid_le_crude h y
    have hmul := mul_le_mul_of_nonneg_left hcrude (Real.rpow_nonneg (norm_nonneg y) c)
    have h2 : ‖y‖ ^ c * ‖y‖ ^ (-2:ℝ) = ‖y‖ ^ (c - 2) := by
      rw [← Real.rpow_add hypos, show c + (-2:ℝ) = c - 2 by ring]
    have h3 : ‖y‖ ^ c * ‖y‖ ^ (-3:ℝ) = ‖y‖ ^ (c - 3) := by
      rw [← Real.rpow_add hypos, show c + (-3:ℝ) = c - 3 by ring]
    calc ‖y‖ ^ c * ‖resid h y‖
        ≤ ‖y‖ ^ c * (‖y + h‖ ^ (-2:ℝ) + ‖y‖ ^ (-2:ℝ) + 4 * ‖y‖ ^ (-3:ℝ) * ‖h‖) := hmul
      _ = ‖y‖ ^ c * ‖y + h‖ ^ (-2:ℝ) + ‖y‖ ^ (c - 2) + 4 * ‖h‖ * ‖y‖ ^ (c - 3) := by
          have h4 : ‖y‖ ^ c * (4 * ‖y‖ ^ (-3:ℝ) * ‖h‖) = 4 * ‖h‖ * ‖y‖ ^ (c - 3) := by
            rw [← h3]; ring
          rw [mul_add, mul_add, h2, h4]

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.norm_setIntegral_crossL_kf_inter_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set

/-- Integrability of the inverse-square weight `‖· - x‖⁻²` on a ball centred at `x`.

The exponent `-2 > -3 = -finrank ℝ ℝ³` is sub-critical, so the singularity is absolutely
integrable: the value of the integral is `4π R` by `integral_ball_sub_norm_rpow`, hence the
integral is not the `0` of a non-integrable function. -/
private lemma integrableOn_norm_sub_rpow_neg_two (x : Work.LWP.R3) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun a : Work.LWP.R3 => (‖a - x‖ : ℝ) ^ (-2 : ℝ)) (Metric.ball x R) volume := by
  have hval := integral_ball_sub_norm_rpow x R (-2) (by norm_num) hR
  have hpos : 0 < 4 * Real.pi * R ^ ((-2 : ℝ) + 3) / ((-2 : ℝ) + 3) := by
    rw [show (-2 : ℝ) + 3 = 1 by norm_num, Real.rpow_one, div_one]
    positivity
  by_contra hcon
  have h0 := integral_undef hcon
  rw [hval] at h0
  exact absurd h0 (ne_of_gt hpos)

/-- **The inner piece of the Biot–Savart integral is uniformly small.**

For a vorticity slice bounded by `M ≥ 0`, the integral of the Biot–Savart integrand over the
*disc* `B(0,ρ) ∩ B(x₀,Δ)` centred at the fixed point `x₀` is bounded, uniformly in
`x ∈ B(x₀,Δ/2)`, by `M * (4π * (3Δ/2))`: the integrand is dominated by the singular weight
`M ‖x - ·‖⁻²` (`norm_bsK_le`), the set is contained in `B(x,3Δ/2)`, and the radial integral
`∫_{B(x,r)}‖x - a‖⁻² da = 4π r` comes from
`Work.CoreResiduals.BiotSavart.integral_ball_sub_norm_rpow` at `s = -2`.

No measurability hypothesis is needed: `MeasureTheory.norm_integral_le_of_norm_le` only requires
the dominating function to be integrable. -/
theorem norm_setIntegral_crossL_kf_inter_le {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {M ρ Δ : ℝ} {x₀ x : Work.LWP.R3} {t : ℝ}
    (hM : 0 ≤ M) (hbdd : ∀ y : Work.LWP.R3, ‖ω y t‖ ≤ M)
    (hΔ : 0 < Δ) (hx : ‖x - x₀‖ ≤ Δ / 2) :
    ‖∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
        Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a))‖
      ≤ M * (4 * Real.pi * (3 * Δ / 2)) := by
  have h3Δ : 0 < 3 * Δ / 2 := by linarith
  have hxx₀ : dist x₀ x ≤ Δ / 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hx
  -- The relevant disc is contained in the ball `B(x, 3Δ/2)` around the singularity.
  have hsub : (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ)
      ⊆ Metric.ball x (3 * Δ / 2) := by
    intro a ha
    rw [Metric.mem_ball]
    have ha2 : dist a x₀ < Δ := by
      simpa only [Metric.mem_ball] using ha.2
    calc dist a x ≤ dist a x₀ + dist x₀ x := dist_triangle a x₀ x
      _ < Δ + Δ / 2 := add_lt_add_of_lt_of_le ha2 hxx₀
      _ = 3 * Δ / 2 := by ring
  -- The dominating weight is integrable on `B(x, 3Δ/2)`, hence on the disc.
  have hIntX : IntegrableOn (fun a : Work.LWP.R3 => M * (‖a - x‖ : ℝ) ^ (-2 : ℝ))
      (Metric.ball x (3 * Δ / 2)) volume :=
    (integrableOn_norm_sub_rpow_neg_two x h3Δ).const_mul M
  have hInts : IntegrableOn (fun a : Work.LWP.R3 => M * (‖a - x‖ : ℝ) ^ (-2 : ℝ))
      ((Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ)) volume :=
    hIntX.mono_set hsub
  calc ‖∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
        Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a))‖
      ≤ ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
          M * (‖a - x‖ : ℝ) ^ (-2 : ℝ) :=
        MeasureTheory.norm_integral_le_of_norm_le hInts
          (Filter.Eventually.of_forall fun a => by
            calc ‖Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a))‖
                ≤ ‖Work.StabilityFar.Decay.crossL (ω a t)‖
                    * ‖Work.StabilityFar.Decay.kf (x - a)‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ ≤ ‖ω a t‖ * ‖Work.StabilityFar.Decay.kf (x - a)‖ :=
                  mul_le_mul_of_nonneg_right (Work.StabilityFar.Decay.norm_crossL_le _)
                    (norm_nonneg _)
              _ ≤ M * ‖Work.StabilityFar.Decay.kf (x - a)‖ :=
                  mul_le_mul_of_nonneg_right (hbdd a) (norm_nonneg _)
              _ = M * (‖a - x‖ : ℝ) ^ (-2 : ℝ) := by
                  rw [Work.CoreResiduals.BiotSavart.norm_kf_eq, norm_sub_rev])
    _ ≤ ∫ a in Metric.ball x (3 * Δ / 2), M * (‖a - x‖ : ℝ) ^ (-2 : ℝ) :=
        setIntegral_mono_set hIntX
          (Filter.Eventually.of_forall fun a =>
            mul_nonneg hM (Real.rpow_nonneg (norm_nonneg _) _))
          (Filter.Eventually.of_forall fun a ha => hsub ha)
    _ = M * (4 * Real.pi * (3 * Δ / 2)) := by
        rw [integral_const_mul]
        congr 1
        rw [integral_ball_sub_norm_rpow x (3 * Δ / 2) (-2) (by norm_num) h3Δ,
          show (-2 : ℝ) + 3 = 1 by norm_num, Real.rpow_one, div_one]

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.setIntegral_eq_lintegral_of_nonneg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- For a pointwise nonnegative function on `ℝ³`, the Bochner set integral over a measurable set
`s` agrees with the `toReal` of the set Lebesgue integral of `ENNReal.ofReal f`.

Both sides are the Bochner/`lintegral` over the restricted measure `volume.restrict s`, so this is
Mathlib's `integral_eq_lintegral_of_nonneg_ae` applied to `μ = volume.restrict s`; measurability of
`s` is not needed for the identity (but is part of the requested interface). -/
theorem setIntegral_eq_lintegral_of_nonneg {f : Work.LWP.R3 → ℝ} {s : Set Work.LWP.R3}
    (hs : MeasurableSet s) (hmeas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hnn : 0 ≤ f) :
    ∫ y in s, f y = (∫⁻ y in s, ENNReal.ofReal (f y)).toReal := by
  exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
    hmeas.restrict

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.taylor_bound_arith =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- Scalar bookkeeping behind the far-field Taylor bound: the four terms on the left are
each exactly of the form `(coefficient) * r ^ (1 + c)`, so the inequality is an equality
(with `hc`, `hc1` used only to guarantee that the divisions are by nonzero reals, as in the
paper's setting). -/
theorem taylor_bound_arith {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (r : ℝ) (hr : 0 < r) :
    (2 * r) ^ c * (12 * Real.pi * r) + 4 * Real.pi * (2 * r) ^ (c + 1) / (c + 1)
        + 4 * r * (4 * Real.pi * (2 * r) ^ c / c)
        + 1024 * r ^ (2:ℕ) * (4 * Real.pi * (2 * r) ^ (c - 1) / (1 - c))
      ≤ (12 * Real.pi * 2 ^ c + 4 * Real.pi * 2 ^ (c + 1) / (c + 1)
          + 16 * Real.pi * 2 ^ c / c + 4096 * Real.pi * 2 ^ (c - 1) / (1 - c))
        * r ^ (1 + c) := by
  have h2nn : (0:ℝ) ≤ 2 := by norm_num
  have hrnn : (0:ℝ) ≤ r := le_of_lt hr
  -- Term 1: `(2r)^c * (12πr) = 12π·2^c·r^{1+c}`.
  have h1 : (2 * r) ^ c * (12 * Real.pi * r) = 12 * Real.pi * 2 ^ c * r ^ (1 + c) := by
    rw [Real.mul_rpow h2nn hrnn]
    rw [show (1:ℝ) + c = c + 1 by ring, Real.rpow_add_one hr.ne' c]
    ring
  -- Term 2: `4π(2r)^{c+1}/(c+1) = (4π·2^{c+1}/(c+1))·r^{1+c}`.
  have h2 : 4 * Real.pi * (2 * r) ^ (c + 1) / (c + 1)
      = 4 * Real.pi * 2 ^ (c + 1) / (c + 1) * r ^ (1 + c) := by
    rw [show (1:ℝ) + c = c + 1 by ring]
    rw [Real.mul_rpow h2nn hrnn]
    ring
  -- Term 3: `4r·(4π(2r)^c/c) = (16π·2^c/c)·r^{1+c}`.
  have h3 : 4 * r * (4 * Real.pi * (2 * r) ^ c / c)
      = 16 * Real.pi * 2 ^ c / c * r ^ (1 + c) := by
    rw [show (1:ℝ) + c = c + 1 by ring, Real.rpow_add_one hr.ne' c]
    rw [Real.mul_rpow h2nn hrnn]
    ring
  -- Term 4: `1024·r^2·(4π(2r)^{c-1}/(1-c)) = (4096π·2^{c-1}/(1-c))·r^{1+c}`.
  have h4 : 1024 * r ^ (2:ℕ) * (4 * Real.pi * (2 * r) ^ (c - 1) / (1 - c))
      = 4096 * Real.pi * 2 ^ (c - 1) / (1 - c) * r ^ (1 + c) := by
    rw [show (1:ℝ) + c = c + 1 by ring]
    rw [Real.mul_rpow h2nn hrnn]
    have hrpow : r ^ (2:ℕ) * r ^ (c - 1) = r ^ (c + 1) := by
      rw [show r ^ (2:ℕ) = r ^ (2:ℝ) from (Real.rpow_natCast r 2).symm]
      rw [← Real.rpow_add hr 2 (c - 1)]
      congr 1
      ring
    calc 1024 * r ^ (2:ℕ) * (4 * Real.pi * (2 ^ (c - 1) * r ^ (c - 1)) / (1 - c))
        = 1024 * 4 * Real.pi * 2 ^ (c - 1) * (r ^ (2:ℕ) * r ^ (c - 1)) / (1 - c) := by ring
      _ = 1024 * 4 * Real.pi * 2 ^ (c - 1) * r ^ (c + 1) / (1 - c) := by rw [hrpow]
      _ = 4096 * Real.pi * 2 ^ (c - 1) / (1 - c) * r ^ (c + 1) := by ring
  rw [h1, h2, h3, h4]
  exact le_of_eq (by ring)

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.taylor_integrand_measurable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay

/-- A map satisfying the norm form of a Hölder estimate with exponent `c > 0` (and any constant
`C`, nonnegative or not) is continuous: the right-hand side tends to `0` at every point. -/
theorem continuous_of_norm_holder {ω : Work.LWP.R3 → Work.LWP.R3} {c C : ℝ}
    (hc : 0 < c) (hhold : ∀ a b : Work.LWP.R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c) :
    Continuous ω := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun a => norm_nonneg _) (fun a => hhold a x) ?_
  have h1 : Filter.Tendsto (fun a : Work.LWP.R3 => ‖a - x‖) (nhds x) (nhds 0) := by
    have h := (continuous_id.sub continuous_const :
      Continuous fun a : Work.LWP.R3 => a - x).tendsto x
    simpa using h.norm
  have h2 : Filter.Tendsto (fun a : Work.LWP.R3 => ‖a - x‖ ^ c) (nhds x) (nhds 0) := by
    have h := h1.rpow tendsto_const_nhds (Or.inr hc)
    simpa [Real.zero_rpow hc.ne'] using h
  simpa using h2.const_mul C

theorem taylor_integrand_measurable {ω : Work.LWP.R3 → Work.LWP.R3} {c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ a b : Work.LWP.R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c) (x h : Work.LWP.R3) :
    MeasureTheory.AEStronglyMeasurable (fun a : Work.LWP.R3 =>
      ‖Work.StabilityFar.Decay.crossL (ω a - ω x)
        (Work.CoreResiduals.BiotSavart.resid h (x - a))‖) MeasureTheory.volume := by
  have hωc : Continuous ω := continuous_of_norm_holder hc hhold
  have hωm : MeasureTheory.AEStronglyMeasurable (fun a : Work.LWP.R3 => ω a - ω x)
      MeasureTheory.volume := (hωc.sub continuous_const).aestronglyMeasurable
  have hres : MeasureTheory.AEStronglyMeasurable
      (fun a : Work.LWP.R3 => resid h (x - a)) MeasureTheory.volume := by
    apply Measurable.aestronglyMeasurable
    unfold resid Work.StabilityFar.Decay.kf Work.StabilityFar.Decay.kDerivCLM
    measurability
  have hpair : MeasureTheory.AEStronglyMeasurable
      (fun a : Work.LWP.R3 => (ω a - ω x, resid h (x - a))) MeasureTheory.volume :=
    hωm.prodMk hres
  have hcont : Continuous (fun p : Work.LWP.R3 × Work.LWP.R3 => crossL p.1 p.2) :=
    (continuous_crossL.comp continuous_fst).clm_apply continuous_snd
  exact (hcont.comp_aestronglyMeasurable hpair).norm

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.FstarInt_smoothNbhd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert.FstarSmooth


end Work.FTS.EllipticEst.Cert.FstarSmooth
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeWAux.i4SliceIneq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.AeWAux

theorem i4SliceIneq : Work.FTS.EllipticEst.Honest.SliceIneq := by
  intro Φ hsm hA hB
  have hbnd : Filter.Tendsto
      (fun θ => Real.sin θ / (Real.cos θ) ^ 3
        * ((Real.cos θ) ^ 2 * deriv (fun θ' => Φ θ' / Real.cos θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    Work.FTS.EllipticEst.Honest.I4BoundaryVanish
      (fun θ => Φ θ / Real.cos θ)
      (Work.FTS.EllipticEst.Honest.contDiffOn_I4psi Φ hsm)
      (hA.mono_set Set.Ioo_subset_Icc_self)
      (Work.FTS.EllipticEst.Honest.I4SliceDivIntegrable Φ hsm hA hB)
  exact Work.FTS.EllipticEst.Honest.I4SliceBound Φ hsm hA hB
    (Work.FTS.EllipticEst.I4SliceAlgebra Φ hsm) hbnd

end Work.FTS.EllipticEst.H2W.AeWAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.SlicePsiMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AngBW.S3

open Work.FTS.EllipticEst.Honest

set_option autoImplicit false


open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Plumbing: gluing two half-open pieces -/

/-- **Gluing**: integrability on the two open halves gives integrability on the whole open
interval. -/
theorem integrableOn_Ioo_union_Ioo {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : MeasureTheory.IntegrableOn f (Set.Ioo a b))
    (h2 : MeasureTheory.IntegrableOn f (Set.Ioo b c)) :
    MeasureTheory.IntegrableOn f (Set.Ioo a c) := by
  have h1' : MeasureTheory.IntegrableOn f (Set.Ioc a b) :=
    h1.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (a := a) (b := b)).symm
  have h2' : MeasureTheory.IntegrableOn f (Set.Ioc b c) :=
    h2.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (a := b) (b := c)).symm
  have hu : MeasureTheory.IntegrableOn f (Set.Ioc a b ∪ Set.Ioc b c) := h1'.union h2'
  rw [Set.Ioc_union_Ioc_eq_Ioc hab hbc] at hu
  exact hu.mono_set Set.Ioo_subset_Ioc_self

set_option linter.unusedVariables false in
theorem slice_psi_mem (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hu0 : u 0 = 0) (hu1 : u (Real.pi / 2) = 0)
    (hB : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hX : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hY : MeasureTheory.IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) ∧
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have h0 : (0 : ℝ) ≤ Real.pi / 4 := by linarith [Real.pi_pos]
  have h1 : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨hA1, hA1'⟩ := slice_psi_near_zero u hu hB hX
  obtain ⟨hA2', hA2⟩ := slice_psi_near_pi2 u hu hY
  exact ⟨integrableOn_Ioo_union_Ioo h0 h1 hA1 hA2,
    integrableOn_Ioo_union_Ioo h0 h1 hA1' hA2'⟩


end Work.FTS.EllipticEst.H2W.AngBW.S3
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.I4Open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! ## The global `I₄` estimate out of the slicewise one

`sliceI4Open` (the honest, open-quadrant form of the `I₄`-term of Step 2 of `prop:H2`) gives,
for every `z > 0`,

  `∫_θ ∂_θ(tan θ Ψ) · ∂_θθΨ · w²σ - ∫_θ Ψ · ∂_θθΨ · w²σ ≤ (1-η)·∫_θ Ψ² · w²σ`,

so integrating in `z` (the three `IPMem` hypotheses make the three `z`-slice functions
integrable, and `w 0 = 0` makes `z = 0` harmless) gives the stated weighted `L²` inequality with
`C = 1 - η = 1/100`. -/
theorem I4Open : ∃ C : ℝ, 0 < C ∧ ∀ (Ψ : ℝ → ℝ → ℝ),
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
    (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (Real.pi / 2) = 0) →
    (Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ)) →
    (Work.FTS.EllipticEst.AngSecond.IPMem Ψ (Work.Spaces.pthIter 2 Ψ)) →
    (Work.FTS.EllipticEst.AngSecond.IPMem Ψ Ψ) →
    (∀ z, 0 < z → MeasureTheory.IntegrableOn (fun θ => (Ψ z θ / Real.cos θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) →
    (∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) →
    (∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) →
    (∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (Real.sin θ) ^ 2
        * (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) →
    - Work.FTS.EllipticEst.AngSecond.IP Ψ (Work.Spaces.pthIter 2 Ψ)
        - C * Work.FTS.EllipticEst.AngSecond.IP Ψ Ψ
      ≤ - Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
          (Work.Spaces.pthIter 2 Ψ) := by
  refine ⟨1 - Work.Spaces.eta, by rw [Work.Spaces.eta]; norm_num, ?_⟩
  intro Ψ hsm h0 hpi hM1 hM2 hM3 hB hBD hB2 hBD2
  set u : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ with hu
  set b : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ with hb
  set FA : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    u z θ * b z θ * AngSecond.w2 z * AngSecond.sig θ with hFA
  set FB : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    Ψ z θ * b z θ * AngSecond.w2 z * AngSecond.sig θ with hFB
  set FN : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    Ψ z θ * Ψ z θ * AngSecond.w2 z * AngSecond.sig θ with hFN
  -- the three `z`-slice functions are integrable, by the three `IPMem` hypotheses
  have hAint : IntegrableOn FA Work.Spaces.Iz := hM1.2
  have hBint : IntegrableOn FB Work.Spaces.Iz := hM2.2
  have hNint : IntegrableOn FN Work.Spaces.Iz := hM3.2
  have hGint : IntegrableOn (fun z => FB z + (1 - Work.Spaces.eta) * FN z) Work.Spaces.Iz :=
    hBint.add (hNint.const_mul _)
  -- the slicewise inequality, with the harmless point `z = 0` handled separately
  have hpoint : ∀ z ∈ Work.Spaces.Iz, FA z ≤ FB z + (1 - Work.Spaces.eta) * FN z := by
    intro z hz
    rcases eq_or_lt_of_le (show 0 ≤ z from hz) with hz0 | hzpos
    · subst hz0
      have hw0 : AngSecond.w2 0 = 0 := by rw [AngSecond.w2, Work.Spaces.w]; norm_num
      have hFA0 : FA 0 = 0 := by rw [hFA]; simp [hw0]
      have hFB0 : FB 0 = 0 := by rw [hFB]; simp [hw0]
      have hFN0 : FN 0 = 0 := by rw [hFN]; simp [hw0]
      rw [hFA0, hFB0, hFN0]; simp
    · have hsl := sliceI4Open Ψ hsm h0 hpi hzpos hM1 hM2 hM3
        (hB z hzpos) (hBD z hzpos) (hB2 z hzpos) (hBD2 z hzpos)
      have hsl' : FA z - FB z ≤ (1 - Work.Spaces.eta) * FN z := hsl
      linarith
  -- integrate the slicewise inequality in `z`
  have hmono : ∫ z in Work.Spaces.Iz, FA z
      ≤ ∫ z in Work.Spaces.Iz, (FB z + (1 - Work.Spaces.eta) * FN z) :=
    MeasureTheory.setIntegral_mono_on hAint hGint measurableSet_Ici (fun z hz => hpoint z hz)
  have hsplit : ∫ z in Work.Spaces.Iz, (FB z + (1 - Work.Spaces.eta) * FN z)
      = (∫ z in Work.Spaces.Iz, FB z)
        + (1 - Work.Spaces.eta) * (∫ z in Work.Spaces.Iz, FN z) := by
    rw [MeasureTheory.integral_add hBint (hNint.const_mul _), MeasureTheory.integral_const_mul]
  -- the pairings are the three `z`-integrals
  have hIP1 : AngSecond.IP
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ) = ∫ z in Work.Spaces.Iz, FA z := rfl
  have hIP2 : AngSecond.IP Ψ (Work.Spaces.pthIter 2 Ψ)
      = ∫ z in Work.Spaces.Iz, FB z := rfl
  have hIP3 : AngSecond.IP Ψ Ψ = ∫ z in Work.Spaces.Iz, FN z := rfl
  rw [hIP1, hIP2, hIP3]
  linarith

end

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.SliceA.lzero1SliceGrowthQuant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `SliceA/lzero1SliceGrowthQuant`

The quantitative two-sided growth bound for an angular slice `u` of class `C²` on `(0, π/2)`:
the size of `u` at any interior point is controlled by the weighted `L²` size
`‖Lzero1 u‖_{L²(sEta)}` of the source together with the two values of `u` at the reference
point `π/4`, times the endpoint function `1/θ + 1/(π/2 - θ)`.

The proof follows the Wronskian-functional route of `H2W/lzeroGrowthSlice` (the
`C²` chain of which is recorded in `H2W/Rfun_bound_two`):

* `D u θ = cos θ (u θ · 2cos 2θ - u' θ sin 2θ)` has `(D u)' = 2 (Lzero1 u) sinθcos²θ`, so its
  oscillation is at most twice the weighted `L¹` mass `M u = ∫ sinθcos²θ |Lzero1 u|` of the
  source;
* `R u θ = u θ / sin 2θ` has `(R u)' = -D u /(cos θ sin²2θ)`, which turns the bound on `D u`
  into the two growth bounds for `R u`;
* the weighted `L¹` mass is bounded by the weighted `L²` mass through Cauchy–Schwarz with the
  companion weight `1/√sEta ≤ 1`;
* the two explicit kernels `1/(cos s sin²2s)` are evaluated against `sin 2θ`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.SliceA

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.EllipticEst.H2W.LzeroGrowth

/-! ## Elementary preparation -/


/-- Almost every point of `Iθ` (for the restricted measure) lies in the open interval. -/
theorem ae_mem_Ioo_restrict_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have h1 : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ae_restrict_mem measurableSet_Ioo
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))] at h1
  simpa only [Work.Spaces.Iθ] using h1




theorem real_univ_restrict_Iθ : (volume.restrict Work.Spaces.Iθ).real univ = Real.pi / 2 := by
  have hvol : (volume.restrict Work.Spaces.Iθ) univ = ENNReal.ofReal (Real.pi / 2) := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Work.Spaces.Iθ,
      Real.volume_Icc, sub_zero]
  show ((volume.restrict Work.Spaces.Iθ) univ).toReal = Real.pi / 2
  rw [hvol, ENNReal.toReal_ofReal (by positivity)]



/-- The angular weight `sinθcos²θ` is at most `1` on `Iθ`. -/
theorem sinCos2_le_one_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Elliptic.sinCos2 θ ≤ 1 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have h1 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2])
  have h2 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h3 : Real.cos θ ^ 2 ≤ 1 := by have := Real.cos_sq_le_one θ; linarith
  have h4 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  rw [Work.Elliptic.sinCos2]
  calc Real.sin θ * Real.cos θ ^ 2 ≤ 1 * 1 := mul_le_mul h2 h3 h4 (by linarith)
    _ = 1 := by ring

/-! ## The weighted `L¹` mass is controlled by the weighted `L²` mass

Cauchy–Schwarz with the companion weight `(√sEta)⁻¹`, which is bounded by `1` on `Iθ`. -/


/-! ## From the two `Rfun` bounds to the quantitative growth of `u` -/



/-! ## The values of the two functionals at the reference point `π/4` -/



/-! ## The quantitative slice growth bound -/


end Work.FTS.EllipticEst.H2W.SliceA
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.CutoffPieces.FstarEqIntegralFstarIntOfSmoothInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine.CutoffPieces

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false



end Work.FTS.EllipticEst.Mine.CutoffPieces
end
-- ===== merged: Submission.Work.FTS.H2.HhardZibp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-! ## The radial integration-by-parts proof of the hard-part bound -/





theorem Thard_smoothNbhd {g : ℝ → ℝ → ℝ} (hsmg : Spaces.SmoothNbhd g) (k : Fin 5) :
    Spaces.SmoothNbhd (Thard g k) := by
  rw [Thard_eq_mixed]
  exact Spaces.smoothNbhd_mixed hsmg (4 - k.val) k.val




theorem hasDerivAt_zw2 {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' => z' * (Spaces.w z') ^ 2)
      ((Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : (1 : ℝ) + z ≠ 0 := by linarith
  refine ((hasDerivAt_id z).mul ((Work.Coercivity.hasDerivAt_w hz0).pow 2)).congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply, id_eq, one_mul]
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  simp only [Spaces.w]
  field_simp
  ring

theorem abs_ratio_le_three (z : ℝ) (hz : 0 < z) : |(z - 3) / (1 + z)| ≤ 3 := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_of_pos hz1, div_le_iff₀ hz1, abs_le]
  constructor <;> linarith



/-! ## The bound on the correction term -/


/-! ## Integrability of the model angular weights -/

theorem integrableOn_sin_two_rpow {a : ℝ} (ha : -1 < a) (ha1 : a ≤ 1) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ a) Spaces.Iθ := by
  rcases lt_or_ge (0 : ℝ) a with hpos | hle
  · refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (s := Spaces.Iθ) (C := (1 : ℝ))
        (by rw [Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) ?_ ?_
    · exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const a)
        |>.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Spaces.Iθ from measurableSet_Icc)] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Spaces.sin_two_nonneg_of_Iθ hθ) a)]
      exact Real.rpow_le_one (Spaces.sin_two_nonneg_of_Iθ hθ) (Real.sin_le_one _) hpos.le
  · exact (Spaces.sin_two_rpow a ha hle).1

/-- The angular dominator of the hard slots. -/
def ZD (α θ : ℝ) : ℝ :=
  (Real.sin (2 * θ)) ^ (-(Spaces.eta)) + (Real.sin (2 * θ)) ^ (1 - Spaces.gam α)
    + (Real.sin (2 * θ)) ^ (2 - Spaces.gam α)

theorem ZD_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) : 0 ≤ ZD α θ :=
  add_nonneg (add_nonneg (Real.rpow_nonneg (Spaces.sin_two_nonneg_of_Iθ hθ) _)
    (Real.rpow_nonneg (Spaces.sin_two_nonneg_of_Iθ hθ) _))
    (Real.rpow_nonneg (Spaces.sin_two_nonneg_of_Iθ hθ) _)


/-! ## The structural `sin(2θ)`-bounds for the slots -/

theorem slot0_bound {g : ℝ → ℝ → ℝ} (hsmg : Spaces.SmoothNbhd g) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Set.Icc 0 R, ∀ θ ∈ Spaces.Iθ,
      |Thard g 0 z θ| ≤ C ∧ |Spaces.pz (Thard g 0) z θ| ≤ C := by
  have hsmA : Spaces.SmoothNbhd (Thard g 0) := Thard_smoothNbhd hsmg 0
  have hb1 : BddAbove (Spaces.boxSet R (Thard g 0)) :=
    Spaces.bddAbove_boxSup_of_continuousOn (Spaces.continuousOn_box_of_contDiffOn hsmA)
  have hb2 : BddAbove (Spaces.boxSet R (Spaces.pz (Thard g 0))) :=
    Spaces.bddAbove_boxSup_of_continuousOn (Spaces.continuousOn_box_of_contDiffOn hsmA.pz)
  have h1 : 0 ≤ Spaces.boxSup R (Thard g 0) := Spaces.boxSup_nonneg hR hb1
  have h2 : 0 ≤ Spaces.boxSup R (Spaces.pz (Thard g 0)) := Spaces.boxSup_nonneg hR hb2
  refine ⟨Spaces.boxSup R (Thard g 0) + Spaces.boxSup R (Spaces.pz (Thard g 0)),
    add_nonneg h1 h2, ?_⟩
  intro z hz θ hθ
  exact ⟨le_trans (Spaces.le_boxSup hb1 hz hθ) (le_add_of_nonneg_right h2),
    le_trans (Spaces.le_boxSup hb2 hz hθ) (le_add_of_nonneg_left h1)⟩

theorem slotN_bound {g : ℝ → ℝ → ℝ} (hsmg : Spaces.SmoothNbhd g) {R : ℝ} (hR : 0 ≤ R)
    (k : Fin 5) (hk : k.val ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Set.Icc 0 R, ∀ θ ∈ Spaces.Iθ,
      |Thard g k z θ| ≤ C * Real.sin (2 * θ) ∧
        |Spaces.pz (Thard g k) z θ| ≤ C * Real.sin (2 * θ) := by
  set i' : ℕ := k.val - 1 with hi'
  have hkv : k.val = i' + 1 := by omega
  set X : ℝ → ℝ → ℝ :=
    Spaces.DzIter (4 - (i' + 1)) (Spaces.pth (Spaces.DthIter i' g)) with hX
  have hsmX : Spaces.SmoothNbhd X := by
    rw [hX]
    exact Spaces.smoothNbhd_DzIter
      (Spaces.SmoothNbhd.pth (Spaces.smoothNbhd_DthIter hsmg i')) (4 - (i' + 1))
  have hbX : BddAbove (Spaces.boxSet R X) :=
    Spaces.bddAbove_boxSup_of_continuousOn (Spaces.continuousOn_box_of_contDiffOn hsmX)
  have hbXp : BddAbove (Spaces.boxSet R (Spaces.pz X)) :=
    Spaces.bddAbove_boxSup_of_continuousOn (Spaces.continuousOn_box_of_contDiffOn hsmX.pz)
  have h1 : 0 ≤ Spaces.boxSup R X := Spaces.boxSup_nonneg hR hbX
  have h2 : 0 ≤ Spaces.boxSup R (Spaces.pz X) := Spaces.boxSup_nonneg hR hbXp
  refine ⟨Spaces.boxSup R X + Spaces.boxSup R (Spaces.pz X), add_nonneg h1 h2, ?_⟩
  have hTh : Thard g k = Spaces.mixed (4 - (i' + 1)) (i' + 1) g := by
    funext z θ
    rw [Thard_eq_mixed, hkv]
  intro z hz θ hθ
  have hsin : 0 ≤ Real.sin (2 * θ) := Spaces.sin_two_nonneg_of_Iθ hθ
  have hXb : |X z θ| ≤ Spaces.boxSup R X := Spaces.le_boxSup hbX hz hθ
  have hXpb : |Spaces.pz X z θ| ≤ Spaces.boxSup R (Spaces.pz X) := Spaces.le_boxSup hbXp hz hθ
  have hfac : Thard g k z θ = Real.sin (2 * θ) * X z θ := by
    rw [hTh, Work.FTS.H2.mixed_sin_factor (4 - (i' + 1)) i' g, hX]
  have hfacp : Spaces.pz (Thard g k) z θ = Real.sin (2 * θ) * Spaces.pz X z θ := by
    rw [hTh, Work.FTS.H2.pz_mixed_sin_factor (4 - (i' + 1)) i' g z θ, hX]
  constructor
  · rw [hfac, abs_mul, abs_of_nonneg hsin]
    calc Real.sin (2 * θ) * |X z θ|
        ≤ Real.sin (2 * θ) * (Spaces.boxSup R X + Spaces.boxSup R (Spaces.pz X)) :=
          mul_le_mul_of_nonneg_left (le_trans hXb (le_add_of_nonneg_right h2)) hsin
      _ = (Spaces.boxSup R X + Spaces.boxSup R (Spaces.pz X)) * Real.sin (2 * θ) := by ring
  · rw [hfacp, abs_mul, abs_of_nonneg hsin]
    calc Real.sin (2 * θ) * |Spaces.pz X z θ|
        ≤ Real.sin (2 * θ) * (Spaces.boxSup R X + Spaces.boxSup R (Spaces.pz X)) :=
          mul_le_mul_of_nonneg_left (le_trans hXpb (le_add_of_nonneg_left h1)) hsin
      _ = (Spaces.boxSup R X + Spaces.boxSup R (Spaces.pz X)) * Real.sin (2 * θ) := by ring

/-! ## A cruder dominator and the master bound for `ZU` -/




theorem slot_bound {g : ℝ → ℝ → ℝ} (hsmg : Spaces.SmoothNbhd g) {R : ℝ} (hR : 0 ≤ R)
    (k : Fin 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Set.Icc 0 R, ∀ θ ∈ Spaces.Iθ,
      |Thard g k z θ| ≤ C * (Real.sin (2 * θ)) ^ (if k.val = 0 then (0:ℝ) else 1) ∧
      |Spaces.pz (Thard g k) z θ|
        ≤ C * (Real.sin (2 * θ)) ^ (if k.val = 0 then (0:ℝ) else 1) := by
  by_cases hk : k.val = 0
  · obtain ⟨C, hC, hb⟩ := slot0_bound hsmg hR
    have hk0 : k = 0 := Fin.ext hk
    subst hk0
    refine ⟨C, hC, fun z hz θ hθ => ?_⟩
    rw [if_pos (show (0 : Fin 5).val = 0 from rfl), Real.rpow_zero, mul_one]
    exact ⟨(hb z hz θ hθ).1, (hb z hz θ hθ).2⟩
  · obtain ⟨C, hC, hb⟩ := slotN_bound hsmg hR k hk
    refine ⟨C, hC, fun z hz θ hθ => ?_⟩
    rw [if_neg hk, Real.rpow_one]
    exact ⟨(hb z hz θ hθ).1, (hb z hz θ hθ).2⟩


/-! ## The `θ`-integrability of the slots -/




end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.SupThetaInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Small interface lemmas -/

/-- The angular slice of a function smooth on a neighbourhood of the closed quadrant is
smooth on `(-1, π/2 + 1)`. -/
theorem contDiffOn_theta_slice {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.SmoothNbhd g)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ContDiffOn ℝ ⊤ (fun θ => g z θ) (Set.Ioo (-1) (π / 2 + 1)) := by
  have hz1 : (-1 : ℝ) < z := by
    simp only [Work.Spaces.Iz, Set.mem_Ici] at hz
    linarith
  have hp : ContDiffOn ℝ ⊤ (fun θ : ℝ => (z, θ)) (Set.Ioo (-1) (π / 2 + 1)) :=
    contDiffOn_const.prodMk contDiffOn_id
  have h := hg.comp hp (fun θ hθ => ⟨hz1, hθ⟩)
  simpa [Function.comp_def, Function.uncurry] using h





end

end Work.FTS.H2
end
-- ===== merged: Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.StabilityFar.Decay

theorem hasDerivAt_biotSavart {ω : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3}
    {R M M₁ ε t : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hε : 0 < ε)
    (hbdd : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y, ‖ω y s‖ ≤ M)
    (hbdd' : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y,
      ‖FiniteTimeSingularity.timeDeriv ω y s‖ ≤ M₁)
    (hdc : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y,
      HasDerivAt (fun s' => ω y s') (FiniteTimeSingularity.timeDeriv ω y s) s)
    (hsupp : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y, ω y s ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : ∀ s ∈ Set.Ioo (t - ε) (t + ε),
      MeasureTheory.AEStronglyMeasurable (ω · s) volume)
    (x : Work.StabilityFar.R3) :
    HasDerivAt (fun s => Work.LWP.biotSavart (ω · s) x)
      (Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y t) x) t := by
  -- `t` lies in the open window, which is therefore a neighbourhood of `t`.
  have hmem : t ∈ Set.Ioo (t - ε) (t + ε) := ⟨by linarith, by linarith⟩
  have hnhds : Set.Ioo (t - ε) (t + ε) ∈ 𝓝 t := isOpen_Ioo.mem_nhds hmem
  -- The common dominating function: `C·‖x-y‖⁻²` on the support ball, with `C = max M M₁`.
  let bd : Work.StabilityFar.R3 → ℝ := fun y =>
    (Metric.closedBall (0 : Work.StabilityFar.R3) R).indicator
      (fun y => max M M₁ * ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y
  have hbd_int : Integrable bd volume :=
    integrable_indicator_inv_sq x (le_trans hM (le_max_left _ _))
  -- Measurability of the derivative slice `∂ₜω(·,t)`.
  have hmeas_dt : AEStronglyMeasurable (fun y => FiniteTimeSingularity.timeDeriv ω y t) volume :=
    aestronglyMeasurable_timeDeriv_slice hε hdc hmeas
  -- The integrand is ae strongly measurable near `t`.
  have hF_meas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun y => Work.LWP.BiotSavart.bsK (fun z => ω z s) x y) volume := by
    filter_upwards [hnhds] with s hs
    exact Work.LWP.BiotSavart.aestronglyMeasurable_bsK (hmeas s hs) x
  -- The integrand at the base point is integrable: dominated by `bd`.
  have hF_int : Integrable (fun y => Work.LWP.BiotSavart.bsK (fun z => ω z t) x y) volume := by
    refine Integrable.mono' (g := bd) hbd_int
      (Work.LWP.BiotSavart.aestronglyMeasurable_bsK (hmeas t hmem) x) ?_
    filter_upwards with y
    exact norm_bsK_le_indicator (le_trans hM (le_max_left _ _))
      (fun z => le_trans (hbdd t hmem z) (le_max_left _ _)) (hsupp t hmem) x y
  -- The derivative integrand is ae strongly measurable.
  have hF'_meas : AEStronglyMeasurable
      (fun y => Work.LWP.BiotSavart.bsK (fun z => FiniteTimeSingularity.timeDeriv ω z t) x y)
      volume :=
    Work.LWP.BiotSavart.aestronglyMeasurable_bsK hmeas_dt x
  -- The derivative integrand is dominated by `bd` on the whole window.
  have h_bound : ∀ᵐ a ∂volume, ∀ s ∈ Set.Ioo (t - ε) (t + ε),
      ‖Work.LWP.BiotSavart.bsK (fun z => FiniteTimeSingularity.timeDeriv ω z s) x a‖ ≤ bd a := by
    filter_upwards with a s hs
    have hsupp_dt : ∀ y, FiniteTimeSingularity.timeDeriv ω y s ≠ 0 →
        y ∈ Metric.closedBall (0 : Work.StabilityFar.R3) R := by
      intro y hy
      by_contra hyy
      exact hy (timeDeriv_eq_zero_of_notMem_closedBall hdc hsupp hs hyy)
    exact norm_bsK_le_indicator (le_trans hM (le_max_left _ _))
      (fun z => le_trans (hbdd' s hs z) (le_max_right _ _)) hsupp_dt x a
  -- Pointwise differentiation of the integrand (chain rule in the first cross-product slot).
  have h_diff : ∀ᵐ a ∂volume, ∀ s ∈ Set.Ioo (t - ε) (t + ε),
      HasDerivAt (fun s' => Work.LWP.BiotSavart.bsK (fun z => ω z s') x a)
        (Work.LWP.BiotSavart.bsK (fun z => FiniteTimeSingularity.timeDeriv ω z s) x a) s := by
    filter_upwards with a s hs
    exact hasDerivAt_bsK (hdc s hs a)
  -- Differentiate under the integral.
  obtain ⟨-, hkey⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun n y => Work.LWP.BiotSavart.bsK (fun z => ω z n) x y)
    (F' := fun n y => Work.LWP.BiotSavart.bsK (fun z => FiniteTimeSingularity.timeDeriv ω z n) x y)
    (bound := bd) hnhds hF_meas hF_int hF'_meas h_bound hbd_int h_diff
  -- Transport the constant factor `(4π)⁻¹` across the derivative and read off `biotSavart`.
  have hfin : HasDerivAt (fun s => (4 * Real.pi)⁻¹ • ∫ y,
        Work.LWP.BiotSavart.bsK (fun z => ω z s) x y)
      ((4 * Real.pi)⁻¹ • ∫ y,
        Work.LWP.BiotSavart.bsK (fun z => FiniteTimeSingularity.timeDeriv ω z t) x y) t :=
    hkey.const_smul ((4 * Real.pi)⁻¹)
  simpa only [Work.LWP.BiotSavart.biotSavart_apply] using hfin

end Work.StabilityFar.Decay
end

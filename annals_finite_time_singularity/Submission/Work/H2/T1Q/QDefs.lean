import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.continuousAt_bsIntegrand_outer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter Topology
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.CoreResiduals.BiotSavart

/-- **Continuity of the outer part of the parametrised Biot–Savart derivative integral.**

For a spacetime vorticity that is `c`-Hölder in `x` with a constant `C ≥ 0` uniform on the time
window `|t - t₀| < δ`, jointly continuous at `(x₀,t₀)` and continuous in `t` at `t₀` for every
fixed `x`, the map `(x,t) ↦ ∫_{B(0,ρ) \ B(x₀,Δ)} bsIntegrand (ω(·,t)) x a da` is continuous at
`(x₀,t₀)`, for `0 < Δ ≤ 2`.

Proof route: use `MeasureTheory.continuousAt_of_dominated` with the *constant* (integrable)
dominating function `bound a = B(0,ρ).indicator (fun a => K * (1 + ‖a‖^{c-3})) a`, where
`exists_rpow_dom_bound (C := C) (c := c) (X := ‖x₀‖+1) (δ := Δ/2)` supplies `K`; the pointwise
bound on `B(0,ρ) \ B(x₀,Δ)` is `bsIntegrand_indicator_le` (from `continuous_bsDerivCLM`), whose
hypotheses `‖x - x₀‖ ≤ Δ/2`, `|t - t₀| < δ` hold eventually near `(x₀,t₀)`; measurability is
`aestronglyMeasurable_bsIntegrand` composed with `continuous_of_holder`; and for fixed
`a ∈ B(0,ρ) \ B(x₀,Δ)` (so `a ≠ x₀`) continuity in `(x,t)` is
`continuousAt_bsIntegrand_param` (imported). -/
theorem continuousAt_bsIntegrand_outer {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {δ c C ρ Δ : ℝ} {x₀ : Work.LWP.R3} {t₀ : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ t : ℝ, |t - t₀| < δ →
      ∀ a b : Work.LWP.R3, ‖ω a t - ω b t‖ ≤ C * ‖a - b‖ ^ c)
    (hjoint : ContinuousAt (fun q : Work.LWP.R3 × ℝ => ω q.1 q.2) (x₀, t₀))
    (htcont : ∀ a : Work.LWP.R3, ContinuousAt (fun t : ℝ => ω a t) t₀)
    (hΔ : 0 < Δ) (hΔ2 : Δ ≤ 2) :
    ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
      ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
        Work.CoreResiduals.BiotSavart.bsIntegrand (fun y => ω y q.2) q.1 a) (x₀, t₀) := by
  -- The dominating constant `K` for the outer region, from `exists_rpow_dom_bound`.
  obtain ⟨K, hK0, hK⟩ := exists_rpow_dom_bound (C := C) (c := c) (X := ‖x₀‖ + 1) (δ := Δ / 2)
    hc hC (by positivity) (by linarith)
  have hmeas : MeasurableSet ((Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ)) :=
    measurableSet_ball.diff measurableSet_ball
  -- The dominating function is integrable: an indicator of a ball times `1 + ‖·‖^{c-3}`.
  have hbdint : Integrable ((Metric.ball (0 : Work.LWP.R3) ρ).indicator
      (fun a : Work.LWP.R3 => K * (1 + (‖a‖ : ℝ) ^ (c - 3)))) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr
      ((integrableOn_one_add_norm_rpow_ball (c - 3) ρ (by linarith)).const_mul K)
  -- Near `(x₀,t₀)` both remaining hypotheses of the pointwise bound hold.
  have hnhds : Metric.ball x₀ (Δ / 2) ×ˢ Metric.ball t₀ δ ∈ 𝓝 (x₀, t₀) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (Metric.ball_mem_nhds x₀ (by linarith)) (Metric.ball_mem_nhds t₀ hδ)
  -- The truncated integrand and the dominating function, as local definitions (unification on
  -- the large integrand would otherwise be slow).
  let F : (Work.LWP.R3 × ℝ) → Work.LWP.R3 → (Work.LWP.R3 →L[ℝ] Work.LWP.R3) := fun q a =>
    ((Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ)).indicator
      (bsIntegrand (fun y => ω y q.2) q.1) a
  let bd : Work.LWP.R3 → ℝ := (Metric.ball (0 : Work.LWP.R3) ρ).indicator
      (fun a : Work.LWP.R3 => K * (1 + (‖a‖ : ℝ) ^ (c - 3)))
  have hmain : ContinuousAt (fun q : Work.LWP.R3 × ℝ => ∫ a, F q a) (x₀, t₀) := by
    refine MeasureTheory.continuousAt_of_dominated (F := F) (bound := bd) ?_ ?_ ?_ ?_
    · -- Measurability in `a`, for `q` near `(x₀,t₀)` (where `ω(·,q.2)` is Hölder, hence continuous).
      filter_upwards [hnhds] with q hq
      have hω : Continuous (fun y : Work.LWP.R3 => ω y q.2) :=
        continuous_of_holder hc hC (hhold q.2 (by
          have := hq.2
          rw [Metric.mem_ball, Real.dist_eq] at this
          exact this))
      exact (aestronglyMeasurable_bsIntegrand hω q.1).indicator hmeas
    · -- The pointwise domination, for `q` near `(x₀,t₀)`.
      filter_upwards [hnhds] with q hq
      filter_upwards with a
      have hx : ‖q.1 - x₀‖ ≤ Δ / 2 := by
        have := hq.1
        rw [Metric.mem_ball, dist_eq_norm] at this
        exact le_of_lt this
      have ht : |q.2 - t₀| < δ := by
        have := hq.2
        rwa [Metric.mem_ball, Real.dist_eq] at this
      exact bsIntegrand_indicator_le (K := K) (ρ := ρ) (Δ := Δ) (x₀ := x₀) hC
        (hhold q.2 ht) hK hK0 hΔ2 hx a
    · exact hbdint
    · -- For a fixed `a` the integrand is continuous in `q`: either `a` is in the outer region
      -- (then `a ≠ x₀` and the parametrised continuity applies), or the indicator vanishes.
      refine Filter.Eventually.of_forall fun a => ?_
      by_cases ha : a ∈ (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ)
      · have hax : a ≠ x₀ := by
          intro h; rw [h] at ha; exact ha.2 (Metric.mem_ball_self hΔ)
        have hc' : ContinuousAt (fun q : Work.LWP.R3 × ℝ =>
            bsIntegrand (fun y => ω y q.2) q.1 a) (x₀, t₀) :=
          continuousAt_bsIntegrand_param hjoint htcont hax
        exact hc'.congr (Filter.Eventually.of_forall fun q =>
          (Set.indicator_of_mem ha (bsIntegrand (fun y => ω y q.2) q.1)).symm)
      · refine ContinuousAt.congr
          (continuousAt_const (y := (0 : Work.LWP.R3 →L[ℝ] Work.LWP.R3)))
          (Filter.Eventually.of_forall fun q => ?_)
        show (0 : Work.LWP.R3 →L[ℝ] Work.LWP.R3) = ((Metric.ball (0 : Work.LWP.R3) ρ) \
          (Metric.ball x₀ Δ)).indicator (bsIntegrand (fun y => ω y q.2) q.1) a
        rw [Set.indicator_of_notMem ha]
  -- Rewrite the restricted integral as the integral of the truncated integrand over the whole space.
  exact hmain.congr (Filter.Eventually.of_forall fun q => by
    show (∫ a, ((Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ)).indicator
          (bsIntegrand (fun y => ω y q.2) q.1) a)
        = ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
            bsIntegrand (fun y => ω y q.2) q.1 a
    rw [MeasureTheory.integral_indicator hmeas])

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.integral_kDerivCLM_annulus_eq_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

-- The hypothesis `hrρ : r < ρ` of the statement below is not needed by the argument (the
-- polar-coordinate computation covers the degenerate case `ρ ≤ r` just as well); silence the
-- unused-variable linter so that the requested statement can be kept verbatim.
set_option linter.unusedVariables false

/-- **The exact kernel-mass identity on a centred annulus.**

The derivative of the Newtonian kernel, `Work.StabilityFar.Decay.kDerivCLM b = ‖b‖⁻³ • Id − 3‖b‖⁻⁵ • (innerSL ℝ b).smulRight b`, has zero Bochner integral over any annulus `r < ‖b‖ < ρ` centred at the origin.

In polar coordinates `b = s ν` the integrand is `s⁻³ (Id − 3 ν⊗ν)` and `db = s² ds dσ`, so the integral is `(∫_r^ρ s⁻¹ ds) • ∫_{S²}(Id − 3ν⊗ν) dσ`, and the angular factor has zero spherical mean: `4π • Id − 3 • (4π/3) • Id = 0` (the second moment identity, as used in `Work.CoreResiduals.BiotSavart.KfBall.sphere_integral_inner_smul`).  The hypothesis `0 < r` is what makes the radial factor finite; the integrand is continuous on the closed annulus, hence Bochner integrable.

This identity is what kills the logarithmic divergence of the kernel masses in Calderón–Zygmund difference estimates: it lets one replace `ω a - ω x` by `ω a - V` for any constant `V` inside a peeled integral over a centred annulus, and bounds the far-field kernel mass by a constant instead of a logarithm. -/
theorem integral_kDerivCLM_annulus_eq_zero {r ρ : ℝ} (hr : 0 < r) (hrρ : r < ρ) :
    ∫ b in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball (0 : Work.LWP.R3) r),
      Work.StabilityFar.Decay.kDerivCLM b = 0 := by
  classical
  -- The Bochner integral of the `R3 →L[ℝ] R3`-valued integrand goes through
  -- `MeasureTheory.integral_smul_const` (pulling out the angular factor), which needs the
  -- codomain to be complete; here it is even finite dimensional.
  have hComplete : CompleteSpace (Work.LWP.R3 →L[ℝ] Work.LWP.R3) :=
    FiniteDimensional.complete ℝ (Work.LWP.R3 →L[ℝ] Work.LWP.R3)
  set A : Set Work.LWP.R3 := Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r
  have hmeas : MeasurableSet A := measurableSet_ball.diff measurableSet_ball
  -- Integrability of the integrand on the annulus (the content of the hypothesis `0 < r`).
  have hint : Integrable (A.indicator (fun b => Work.StabilityFar.Decay.kDerivCLM b)) volume :=
    integrable_indicator_kDerivCLM_annulus (ρ := ρ) hr
  -- Write the set integral as the integral of the indicator against Lebesgue measure ...
  rw [← integral_indicator hmeas (f := fun b => Work.StabilityFar.Decay.kDerivCLM b)]
  -- ... and pass to polar coordinates: `ℝ³ ≃ S² × (0,∞)`, `(ω,s) ↦ s • ω`.
  rw [integral_polar hint]
  -- On each ray the annulus is the interval `[r,ρ)` and the integrand separates into a radial
  -- factor and the fixed angular factor `Id − 3 ν⊗ν`.
  have hinner : ∀ ω : Metric.sphere (0 : Work.LWP.R3) 1,
      (∫ s : Set.Ioi (0 : ℝ),
          A.indicator (fun b => Work.StabilityFar.Decay.kDerivCLM b)
            ((s : ℝ) • (ω : Work.LWP.R3))
          ∂(Measure.volumeIoiPow 2))
        = (∫ s : Set.Ioi (0 : ℝ),
              (if r ≤ (s : ℝ) ∧ (s : ℝ) < ρ then (((s : ℝ)) ^ 3)⁻¹ else 0)
              ∂(Measure.volumeIoiPow 2))
            • (ContinuousLinearMap.id ℝ Work.LWP.R3
                - (3 : ℝ) • (innerSL ℝ (ω : Work.LWP.R3)).smulRight
                    (ω : Work.LWP.R3)) := by
    intro ω
    have hcongr : (fun s : Set.Ioi (0 : ℝ) => A.indicator
          (fun b => Work.StabilityFar.Decay.kDerivCLM b) ((s : ℝ) • (ω : Work.LWP.R3)))
        = fun s : Set.Ioi (0 : ℝ) =>
            (if r ≤ (s : ℝ) ∧ (s : ℝ) < ρ then (((s : ℝ)) ^ 3)⁻¹ else 0)
              • (ContinuousLinearMap.id ℝ Work.LWP.R3
                  - (3 : ℝ) • (innerSL ℝ (ω : Work.LWP.R3)).smulRight
                      (ω : Work.LWP.R3)) := by
      funext s
      exact ray_indicator_kDerivCLM s ω
    rw [hcongr, integral_smul_const]
  simp_rw [hinner]
  -- The radial factor is a constant, and the angular factor integrates to zero.
  rw [integral_smul, sphere_integral_kDerivCLM_angular, smul_zero]

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.norm_bsDerivCLM_le_of_bdd_holder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric
open Work.StabilityFar.Decay

theorem norm_bsDerivCLM_le_of_bdd_holder {α A H ρ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hA : 0 ≤ A) (hH : 0 ≤ H) (hρ : 0 ≤ ρ)
    {g : Work.LWP.R3 → Work.LWP.R3}
    (hbdd : ∀ a, ‖g a‖ ≤ A)
    (hhold : ∀ a b : Work.LWP.R3, ‖g a - g b‖ ≤ 2 * H * ‖a - b‖ ^ α)
    (x : Work.LWP.R3) :
    ‖Work.CoreResiduals.BiotSavart.bsDerivCLM g ρ x‖ ≤
      4 * (2 * A) ^ α * (2 * H) ^ (1 - α) *
        (4 * Real.pi * (ρ + ‖x‖) ^ (α * (1 - α)) / (α * (1 - α)))
      + (4 * Real.pi / 3) * A := by
  have hspos : 0 < α * (1 - α) := mul_pos hα (by linarith)
  have hs : (-3 : ℝ) < α * (1 - α) - 3 := by linarith
  have hKnn : 0 ≤ 4 * (2 * A) ^ α * (2 * H) ^ (1 - α) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) α))
      (Real.rpow_nonneg (by linarith) (1 - α))
  -- pointwise interpolation bound for the integrand
  have hpt : ∀ a, ‖bsIntegrand g x a‖ ≤
      4 * (2 * A) ^ α * (2 * H) ^ (1 - α) * ‖x - a‖ ^ (α * (1 - α) - 3) :=
    fun a => norm_bsIntegrand_le_interp hα hα1 hA hH hbdd hhold x a
  -- integrability of the dominating function on `B(0,ρ)`
  have hInt : IntegrableOn (fun a : Work.LWP.R3 =>
      4 * (2 * A) ^ α * (2 * H) ^ (1 - α) * ‖x - a‖ ^ (α * (1 - α) - 3))
      (Metric.ball (0 : Work.LWP.R3) ρ) volume := by
    rcases eq_or_lt_of_le hρ with hρ0 | hρpos
    · rw [← hρ0, Metric.ball_zero]
      exact integrableOn_empty
    · have hRpos : 0 < ρ + ‖x‖ := by linarith [norm_nonneg x]
      have hsub : Metric.ball (0 : Work.LWP.R3) ρ ⊆ Metric.ball x (ρ + ‖x‖) := by
        intro a ha
        rw [Metric.mem_ball, dist_zero_right] at ha
        rw [Metric.mem_ball, dist_eq_norm]
        calc ‖a - x‖ ≤ ‖a‖ + ‖x‖ := norm_sub_le a x
          _ < ρ + ‖x‖ := by linarith
      have hbase : IntegrableOn (fun a : Work.LWP.R3 => ‖x - a‖ ^ (α * (1 - α) - 3))
          (Metric.ball (0 : Work.LWP.R3) ρ) volume := by
        have h1 :=
          (integrableOn_norm_sub_rpow_ball x (c := α * (1 - α)) hspos hRpos).mono_set hsub
        simpa only [norm_sub_rev] using h1
      exact hbase.const_mul _
  -- the integral term is bounded by the radial estimate
  have hIntBound : ‖∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand g x a‖ ≤
      4 * (2 * A) ^ α * (2 * H) ^ (1 - α) *
        (4 * Real.pi * (ρ + ‖x‖) ^ (α * (1 - α)) / (α * (1 - α))) := by
    have h1 := MeasureTheory.norm_integral_le_of_norm_le hInt (Filter.Eventually.of_forall hpt)
    calc ‖∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand g x a‖
        ≤ ∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
            4 * (2 * A) ^ α * (2 * H) ^ (1 - α) * ‖x - a‖ ^ (α * (1 - α) - 3) := h1
      _ = 4 * (2 * A) ^ α * (2 * H) ^ (1 - α) *
            ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, ‖x - a‖ ^ (α * (1 - α) - 3) := by
          rw [integral_const_mul]
      _ ≤ 4 * (2 * A) ^ α * (2 * H) ^ (1 - α) *
            (4 * Real.pi * (ρ + ‖x‖) ^ ((α * (1 - α) - 3) + 3)
              / ((α * (1 - α) - 3) + 3)) :=
          mul_le_mul_of_nonneg_left (setIntegral_ball_zero_norm_sub_rpow_le x hρ hs) hKnn
      _ = 4 * (2 * A) ^ α * (2 * H) ^ (1 - α) *
            (4 * Real.pi * (ρ + ‖x‖) ^ (α * (1 - α)) / (α * (1 - α))) := by
          rw [show α * (1 - α) - 3 + 3 = α * (1 - α) from by ring]
  -- the shape term
  have hshape : ‖(4 * Real.pi / 3) • crossL (g x)‖ ≤ (4 * Real.pi / 3) * A := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc (4 * Real.pi / 3) * ‖crossL (g x)‖ ≤ (4 * Real.pi / 3) * ‖g x‖ :=
          mul_le_mul_of_nonneg_left (norm_crossL_le _) (by positivity)
      _ ≤ (4 * Real.pi / 3) * A := mul_le_mul_of_nonneg_left (hbdd x) (by positivity)
  have hLHS : Work.CoreResiduals.BiotSavart.bsDerivCLM g ρ x
      = (∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand g x a)
        + (4 * Real.pi / 3) • crossL (g x) := rfl
  rw [hLHS]
  calc ‖(∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand g x a)
        + (4 * Real.pi / 3) • crossL (g x)‖
      ≤ ‖∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand g x a‖
        + ‖(4 * Real.pi / 3) • crossL (g x)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hIntBound hshape

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.FTS.BSSwirl.abs_inv_norm_taylor_residual_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl

/-- Pure real-variable arithmetic: if `0 < a ≤ b` then

`6 * a ^ 2 / b ^ 3 ≤ 10000 * a ^ (3/2) * b ^ (-(5/2))`.

The two sides differ by the factor `(a/b)^{1/2} ≤ 1`. -/
private lemma rpow_six_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    6 * a ^ (2:ℕ) / b ^ (3:ℕ) ≤ 10000 * a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2) := by
  have ha2 : a ^ (2:ℕ) = a ^ ((3:ℝ)/2) * a ^ ((1:ℝ)/2) := by
    rw [← Real.rpow_natCast a 2, show (((2:ℕ)):ℝ) = (3:ℝ)/2 + 1/2 by norm_num,
      Real.rpow_add ha]
  have hb3 : b ^ (3:ℕ) = b ^ ((5:ℝ)/2) * b ^ ((1:ℝ)/2) := by
    rw [← Real.rpow_natCast b 3, show (((3:ℕ)):ℝ) = (5:ℝ)/2 + 1/2 by norm_num,
      Real.rpow_add hb]
  have hkey : a ^ ((1:ℝ)/2) * b ^ (-(1:ℝ)/2) ≤ 1 := by
    have h1 : b ^ (-(1:ℝ)/2) = (b ^ ((1:ℝ)/2))⁻¹ := by
      rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (le_of_lt hb)]
    rw [h1, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hb _)]
    exact Real.rpow_le_rpow (le_of_lt ha) hab (by norm_num)
  have hmain : a ^ (2:ℕ) / b ^ (3:ℕ) ≤ a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2) := by
    calc a ^ (2:ℕ) / b ^ (3:ℕ)
        = (a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2)) * (a ^ ((1:ℝ)/2) * b ^ (-(1:ℝ)/2)) := by
          rw [ha2, hb3, show (-(5:ℝ)/2) = -((5:ℝ)/2) by ring, Real.rpow_neg (le_of_lt hb),
              show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (le_of_lt hb)]
          field_simp
      _ ≤ (a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2)) * 1 :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2) := by ring
  have h6 : 6 * (a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2))
      ≤ 10000 * (a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2)) :=
    by nlinarith [(by positivity : (0:ℝ) ≤ a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2))]
  calc 6 * a ^ (2:ℕ) / b ^ (3:ℕ) = 6 * (a ^ (2:ℕ) / b ^ (3:ℕ)) := by ring
    _ ≤ 6 * (a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2)) := by linarith [hmain]
    _ ≤ 10000 * (a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2)) := h6
    _ = 10000 * a ^ ((3:ℝ)/2) * b ^ (-(5:ℝ)/2) := by ring

/-- **Second-order Taylor expansion of the Newtonian kernel `x ↦ ‖x‖⁻¹`.**

For `2 ‖h‖ ≤ ‖z‖` the remainder of the first-order expansion
`‖z + h‖⁻¹ = ‖z‖⁻¹ - ⟪kf z, h⟫ + O(‖h‖^{3/2} ‖z‖^{-5/2})` is bounded by
`10⁴ ‖h‖^{3/2} ‖z‖^{-5/2}`, where `kf z = ‖z‖⁻³ • z` is the gradient of `‖·‖⁻¹`
(`⟪kf z, h⟫ = ⟪z, h⟫ / ‖z‖³`).

The proof is the exact identity (`s = ‖z‖`, `w = ‖z + h‖`, `A = ⟪z, h⟫`, `T = s³ w (s+w)`)

`(w⁻¹ - s⁻¹ + A/s³) · T = A (w (s+w) - 2 s²) - s² ‖h‖²`,

following from `w² = s² + 2A + ‖h‖²`, together with the bounds
`|A| ≤ s ‖h‖`, `|w (s+w) - 2 s²| = |3 s (w-s) + (w-s)²| ≤ (7/2) s ‖h‖` (using
`|w - s| ≤ ‖h‖` and `‖h‖ ≤ s/2`) and `T ≥ (3/4) s⁵` (using `s/2 ≤ w ≤ 3s/2`).
This gives the bound `6 ‖h‖² / ‖z‖³`, which is at most
`6 ‖h‖^{3/2} ‖z‖^{-5/2} ≤ 10⁴ ‖h‖^{3/2} ‖z‖^{-5/2}` (`rpow_six_le`). -/
theorem abs_inv_norm_taylor_residual_le {z h : Work.FTS.BSSwirl.R3} (hz : 2 * ‖h‖ ≤ ‖z‖) :
    |(‖z + h‖)⁻¹ - (‖z‖)⁻¹ + inner ℝ (Work.StabilityFar.Decay.kf z) h|
      ≤ 10000 * ‖h‖ ^ ((3 : ℝ) / 2) * ‖z‖ ^ (-(5 : ℝ) / 2) := by
  rcases eq_or_lt_of_le (norm_nonneg h) with hh0 | hhpos
  · -- degenerate case `h = 0`
    have h0 : h = 0 := by rw [← norm_eq_zero]; exact hh0.symm
    rw [h0]
    simp [Real.zero_rpow (by norm_num : ((3:ℝ)/2) ≠ 0)]
  · -- main case
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by linarith) hz
    set s : ℝ := ‖z‖ with hsdef
    set w : ℝ := ‖z + h‖ with hwdef
    set A : ℝ := inner ℝ z h with hAdef
    have hs : 0 < s := by rw [hsdef]; exact hzpos
    have hhle : ‖h‖ ≤ s / 2 := by rw [hsdef]; linarith
    have hAle : |A| ≤ s * ‖h‖ := by
      rw [hAdef, hsdef]; exact abs_real_inner_le_norm z h
    have hwsub : |w - s| ≤ ‖h‖ := by
      have hd : (z + h) - z = h := by abel
      have h := abs_norm_sub_norm_le (z + h) z
      rw [hd] at h
      simpa [hwdef, hsdef] using h
    have hw : 0 < w := by
      have h1 : s - w ≤ ‖h‖ := by
        have := (abs_le.mp hwsub).1; linarith
      linarith [hhle, hs]
    have hwlow : s/2 ≤ w := by
      have h1 : s - w ≤ ‖h‖ := by
        have := (abs_le.mp hwsub).1; linarith
      linarith [hhle]
    -- the exact second-order identity
    have hR : (w)⁻¹ - (s)⁻¹ + (s^3)⁻¹ * A
        = (A * (w*(s+w) - 2*s^2) - s^2 * ‖h‖^2) / (s^3 * w * (s+w)) := by
      rw [hsdef, hwdef, hAdef]
      have hw2 : ‖z + h‖^2 = ‖z‖^2 + 2 * (inner ℝ z h) + ‖h‖^2 := norm_add_sq_real z h
      have hzn : ‖z‖ ≠ 0 := by rw [← hsdef]; exact ne_of_gt hs
      have hwn : ‖z + h‖ ≠ 0 := by rw [← hwdef]; exact ne_of_gt hw
      have hsw : ‖z‖ + ‖z+h‖ ≠ 0 := by positivity
      field_simp
      ring_nf
      rw [hw2]
      ring
    -- the two elementary bounds on the numerator
    have hD : |w * (s + w) - 2 * s^2| ≤ 7/2 * s * ‖h‖ := by
      have hfac : w * (s + w) - 2 * s^2 = 3 * s * (w - s) + (w - s)^2 := by ring
      rw [hfac]
      have h1 : |3 * s * (w - s)| ≤ 3 * s * ‖h‖ := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3), abs_of_pos hs]
        exact mul_le_mul_of_nonneg_left hwsub (by positivity)
      have h2 : |(w - s)^2| ≤ (s/2) * ‖h‖ := by
        have h3 : |w - s| ≤ s/2 := le_trans hwsub hhle
        rw [abs_sq, ← sq_abs]
        nlinarith [abs_nonneg (w - s), h3, hwsub]
      calc |3 * s * (w - s) + (w - s)^2| ≤ |3 * s * (w - s)| + |(w - s)^2| :=
            abs_add_le _ _
        _ ≤ 3 * s * ‖h‖ + (s/2) * ‖h‖ := by linarith
        _ = 7/2 * s * ‖h‖ := by ring
    have hnum : |A * (w*(s+w) - 2*s^2) - s^2 * ‖h‖^2| ≤ 9/2 * s^2 * ‖h‖^2 := by
      have h1 : |A * (w*(s+w) - 2*s^2)| ≤ 7/2 * s^2 * ‖h‖^2 := by
        rw [abs_mul]
        calc |A| * |w*(s+w) - 2*s^2| ≤ (s * ‖h‖) * (7/2 * s * ‖h‖) :=
              mul_le_mul hAle hD (abs_nonneg _) (by positivity)
          _ = 7/2 * s^2 * ‖h‖^2 := by ring
      have htri : |A * (w*(s+w) - 2*s^2) - s^2 * ‖h‖^2|
          ≤ |A * (w*(s+w) - 2*s^2)| + |s^2 * ‖h‖^2| := by
        rw [sub_eq_add_neg, ← abs_neg (s^2 * ‖h‖^2)]
        exact abs_add_le _ _
      have h2 : |s^2 * ‖h‖^2| = s^2 * ‖h‖^2 := abs_of_nonneg (by positivity)
      calc |A * (w*(s+w) - 2*s^2) - s^2 * ‖h‖^2|
          ≤ |A * (w*(s+w) - 2*s^2)| + |s^2 * ‖h‖^2| := htri
        _ = |A * (w*(s+w) - 2*s^2)| + s^2 * ‖h‖^2 := by rw [h2]
        _ ≤ 7/2 * s^2 * ‖h‖^2 + s^2 * ‖h‖^2 := by linarith [h1]
        _ = 9/2 * s^2 * ‖h‖^2 := by ring
    -- the lower bound for the denominator
    have hT : 0 < s^3 * w * (s+w) := by positivity
    have hTlow : 3/4 * s^5 ≤ s^3 * w * (s+w) := by
      have h2 : 3*s/2 ≤ s + w := by linarith
      calc 3/4 * s^5 = s^3 * (s/2) * (3*s/2) := by ring
        _ ≤ s^3 * w * (s+w) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hwlow (by positivity)) h2
              (by positivity) (by positivity)
    have hRbound : |(w)⁻¹ - (s)⁻¹ + (s^3)⁻¹ * A| ≤ 6 * ‖h‖^2 / s^3 := by
      rw [hR, abs_div, abs_of_pos hT]
      have h1 : |A * (w*(s+w) - 2*s^2) - s^2 * ‖h‖^2| / (s^3 * w * (s+w))
          ≤ (9/2 * s^2 * ‖h‖^2) / (s^3 * w * (s+w)) :=
        div_le_div_of_nonneg_right hnum (le_of_lt hT)
      have h2 : (9/2 * s^2 * ‖h‖^2) / (s^3 * w * (s+w))
          ≤ (9/2 * s^2 * ‖h‖^2) / (3/4 * s^5) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hTlow
      have h3 : (9/2 * s^2 * ‖h‖^2) / (3/4 * s^5) = 6 * ‖h‖^2 / s^3 := by
        field_simp
        ring
      linarith [h1, h2, h3.le, h3.ge]
    -- turn `inner ℝ (kf z) h` into `(s^3)⁻¹ * A`
    have hinner : inner ℝ (Work.StabilityFar.Decay.kf z) h = (s^3)⁻¹ * A := by
      rw [hsdef, hAdef, Work.StabilityFar.Decay.kf, inner_smul_left]
      simp
    rw [hinner]
    exact hRbound.trans (rpow_six_le ‖h‖ s hhpos hs (by linarith [hhle]))

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.weakSliceLimits =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open MeasureTheory Set Filter
open scoped Real Topology

/-! # The endpoint behaviour of a weighted-`H²` angular slice

This module proves `Work.FTS.EllipticEst.H2W.weakSliceLimits`: a function `u` of class `C^n` on
`(0, π/2)` for every `n`, vanishing at both endpoints, whose second derivative satisfies

  `∫_{Iθ} (u'')² · sEta < ∞`,   `∫_{Iθ} (Lzero1 u)² · sEta < ∞`,   `sEta θ = sin(2θ)^{-η}`,

has a finite limit and a finite limit of `u'` at `0⁺`, tends to `0` at `(π/2)⁻`, and has a
(Lebesgue) integrable second derivative on `Iθ`.

The argument:
* the weight satisfies `sEta ≥ 1` on `(0, π/2)`, so the first hypothesis is at least as strong as
  `u'' ∈ L²(0, π/2) ⊂ L¹(0, π/2)`, and (by Newton–Leibniz) `u'`, `u` are bounded near every
  endpoint;
* the existence of the limits at `0⁺` is then exactly
  `exists_tendsto_nhdsGT_zero_of_integrableOn_deriv` applied to `u` and to `u'`;
* at the right endpoint we integrate the identity `(tan θ · u)' = Lzero1 u + u'' + 6u`
  (`Lzero1 u = -u'' + (tan θ · u)' - 6u`): the right-hand side is integrable on `(π/4, π/2)`, so
  `tan θ · u θ` has a finite limit at `(π/2)⁻`; since `u θ = (tan θ · u θ) · (cos θ / sin θ)` and
  `cos θ / sin θ → 0`, we get `u θ → 0`.
-/

/-- **Right endpoint limit of a function with integrable derivative.**  If `f` is differentiable
with derivative `f'` on the open interval `(a, b)` and `f'` is Lebesgue integrable there, then
`f` has a finite limit at `b` from the left.  (Mirror image of
`Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv`.) -/
theorem exists_tendsto_nhdsLT_of_integrableOn_deriv {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hint : MeasureTheory.IntegrableOn f' (Set.Ioo a b)) :
    ∃ L : ℝ, Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds L) := by
  set c : ℝ := (a + b) / 2 with hcdef
  have hac : a < c := by rw [hcdef]; linarith
  have hcb : c < b := by rw [hcdef]; linarith
  have hIoo_cb : IntegrableOn f' (Set.Ioo c b) :=
    hint.mono_set (Set.Ioo_subset_Ioo_left hac.le)
  have hIcc : IntegrableOn f' (Set.Icc c b) volume :=
    hIoo_cb.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc (a := c) (b := b)).symm
  have hcont_u : ContinuousOn (fun x => ∫ t in c..x, f' t) (Set.uIcc c b) :=
    intervalIntegral.continuousOn_primitive_interval (by
      rw [Set.uIcc_of_le hcb.le]; exact hIcc)
  have hcont : ContinuousOn (fun x => ∫ t in c..x, f' t) (Set.Icc c b) := by
    rwa [Set.uIcc_of_le hcb.le] at hcont_u
  refine ⟨f c + ∫ t in c..b, f' t, ?_⟩
  have hg : Tendsto (fun x => f c + ∫ t in c..x, f' t) (nhdsWithin b (Set.Iio b))
      (nhds (f c + ∫ t in c..b, f' t)) := by
    have hcw : ContinuousWithinAt (fun x => ∫ t in c..x, f' t) (Set.Icc c b) b :=
      hcont.continuousWithinAt (Set.right_mem_Icc.mpr hcb.le)
    have hle : nhdsWithin b (Set.Iio b) ≤ nhdsWithin b (Set.Icc c b) := by
      rw [← nhdsWithin_Ioo_eq_nhdsLT hcb]
      exact nhdsWithin_mono b Set.Ioo_subset_Icc_self
    exact (hcw.mono_left hle).const_add (f c)
  refine hg.congr' ?_
  have hmem : Set.Ioo c b ∈ nhdsWithin b (Set.Iio b) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hcb]
    exact self_mem_nhdsWithin
  filter_upwards [hmem] with x hx
  have hcx : c ≤ x := hx.1.le
  have hFTC : ∫ t in c..x, f' t = f x - f c :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy => hderiv y (by
        rw [Set.uIcc_of_le hcx] at hy
        exact ⟨lt_of_lt_of_le hac hy.1, lt_of_le_of_lt hy.2 hx.2⟩))
      ((show IntegrableOn f' (Set.uIcc c x) volume from by
          rw [Set.uIcc_of_le hcx]
          exact hIcc.mono_set (Set.Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable)
  linarith [hFTC]

/-- **Squeeze at the right endpoint.**  If `tan θ · u θ` has a finite limit at `(π/2)⁻`, then
`u θ → 0`: near `π/2` one has `u θ = (tan θ · u θ) · (cos θ / sin θ)` and `cos θ / sin θ → 0`. -/
theorem tendsto_zero_right_of_tan_mul_tendsto {u : ℝ → ℝ} {M : ℝ}
    (h : Filter.Tendsto (fun θ : ℝ => Real.tan θ * u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds M)) :
    Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have h1 : Filter.Tendsto (fun θ : ℝ => Real.cos θ / Real.sin θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hc : ContinuousAt (fun θ : ℝ => Real.cos θ / Real.sin θ) (Real.pi / 2) :=
      Real.continuous_cos.continuousAt.div Real.continuous_sin.continuousAt
        (by simp [Real.sin_pi_div_two])
    have hle : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤ nhds (Real.pi / 2) :=
      nhdsWithin_le_nhds
    have := hc.tendsto.mono_left hle
    simpa [Real.cos_pi_div_two, Real.sin_pi_div_two] using this
  have h2 : Filter.Tendsto (fun θ : ℝ => Real.tan θ * u θ * (Real.cos θ / Real.sin θ))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have := h.mul h1
    simpa using this
  refine h2.congr' ?_
  have hmem : Set.Ioo (Real.pi / 4) (Real.pi / 2)
      ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT (a := Real.pi / 4) (b := Real.pi / 2)
      (by linarith [Real.pi_pos])]
    exact self_mem_nhdsWithin
  filter_upwards [hmem] with θ hθ
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hsin : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
      (by linarith [hθ.2, Real.pi_pos]))
  rw [Real.tan_eq_sin_div_cos]
  field_simp

/-- **Derivative of `θ ↦ tan θ · u θ` in the shape used by the right-endpoint integral.**  On the
open interval this derivative is `Lzero1 u + u'' + 6u` by the definition of `Lzero1`. -/
theorem hasDerivAt_tan_mul_Lzero1 {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun t : ℝ => Real.tan t * u t)
      (Work.FTS.EllipticEst.Lzero1 u θ + deriv (fun t : ℝ => deriv u t) θ + 6 * u θ) θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hu2 : ContDiffAt ℝ 2 u θ := hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have hdiff : DifferentiableAt ℝ (fun t : ℝ => Real.tan t * u t) θ :=
    (Real.differentiableAt_tan.mpr hcos).mul (hu2.differentiableAt (by norm_num))
  have h := hdiff.hasDerivAt
  convert h using 1
  simp only [Work.FTS.EllipticEst.Lzero1]
  ring

/-- **Boundedness of `u` and of `u'` on the right half of the slice.**  On `(π/4, π/2)` both
`u` and `u'` are bounded, with an explicit constant obtained from Newton–Leibniz applied to
`u'` (whose derivative `u''` is integrable on the right half because `sEta ≥ 1` there). -/
theorem abs_deriv_and_abs_le_right {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    ∃ C : ℝ, 0 < C ∧ (∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), |deriv u θ| ≤ C)
      ∧ (∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), |u θ| ≤ C) := by
  have hU : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hq : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hsq : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (fun t => deriv u t) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta u h2
  have hD2abs : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t => deriv u t) θ|)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq u hsq
  have hD2tailAbs : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t => deriv u t) θ|)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    hD2abs.mono_set (Set.Ioo_subset_Ioo_left hU.le)
  have hD2tail : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv (fun t => deriv u t) θ)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    rw [MeasureTheory.IntegrableOn]
    refine (MeasureTheory.integrable_norm_iff ?_).mp ?_
    · exact (measurable_deriv (fun t : ℝ => deriv u t)).aestronglyMeasurable
    · rw [MeasureTheory.IntegrableOn] at hD2tailAbs
      simpa [Real.norm_eq_abs] using hD2tailAbs
  have hderiv2 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t : ℝ => deriv u t) x) x := by
    intro x hx
    have h2' : ContDiffAt ℝ 2 u x := hu.contDiffAt (isOpen_Ioo.mem_nhds hx)
    have hd1 : ContDiffAt ℝ 1 (deriv u) x := h2'.derivWithin (by norm_num)
    exact (hd1.differentiableAt (by norm_num)).hasDerivAt
  have hu1 : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)) := hu.of_le (by norm_num)
  have hderiv1 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt u (deriv u x) x := by
    intro x hx
    exact ((hu1.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
  have hcd : ContinuousOn (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    fun x hx => (hderiv2 x hx).continuousAt.continuousWithinAt
  set K : ℝ := ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) θ| with hK
  have hKnn : 0 ≤ K := by
    rw [hK]; exact integral_nonneg fun _ => abs_nonneg _
  set M : ℝ := |deriv u (Real.pi / 4)| + K with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]; linarith [abs_nonneg (deriv u (Real.pi / 4)), hKnn]
  -- bound on `u'` on the right half
  have hud : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), |deriv u θ| ≤ M := by
    intro θ hθ
    have hle : Real.pi / 4 ≤ θ := hθ.1.le
    have hFTC : ∫ s in (Real.pi / 4)..θ, deriv (fun t => deriv u t) s
        = deriv u θ - deriv u (Real.pi / 4) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_
      · rw [Set.uIcc_of_le hle] at hx
        exact hderiv2 x ⟨lt_of_lt_of_le hU hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
        exact hD2tail.mono_set (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hθ.2⟩)
    have hb : |deriv u θ - deriv u (Real.pi / 4)| ≤ K := by
      have h1 : |∫ s in (Real.pi / 4)..θ, deriv (fun t => deriv u t) s|
          ≤ ∫ s in (Real.pi / 4)..θ, |deriv (fun t => deriv u t) s| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (μ := volume) hle
            (f := fun s => deriv (fun t => deriv u t) s)
      have h2' : ∫ s in (Real.pi / 4)..θ, |deriv (fun t => deriv u t) s| ≤ K := by
        rw [hK, intervalIntegral.integral_of_le hle]
        exact MeasureTheory.setIntegral_mono_set hD2abs
          (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (Filter.Eventually.of_forall fun x hx =>
            ⟨lt_trans hU hx.1, lt_of_le_of_lt hx.2 hθ.2⟩)
      rw [← hFTC]
      exact h1.trans h2'
    have htri : |deriv u θ| ≤ |deriv u (Real.pi / 4)| + |deriv u θ - deriv u (Real.pi / 4)| := by
      have := abs_add_le (deriv u (Real.pi / 4)) (deriv u θ - deriv u (Real.pi / 4))
      simpa using this
    rw [hMdef]; linarith [htri, hb]
  -- bound on `u` on the right half
  have huBd : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |u θ| ≤ |u (Real.pi / 4)| + M * (Real.pi / 2) := by
    intro θ hθ
    have hle : Real.pi / 4 ≤ θ := hθ.1.le
    have hFTC : ∫ s in (Real.pi / 4)..θ, deriv u s = u θ - u (Real.pi / 4) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_
      · rw [Set.uIcc_of_le hle] at hx
        exact hderiv1 x ⟨lt_of_lt_of_le hU hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
      · have hsub : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
          rw [Set.uIcc_of_le hle]
          exact fun x hx => ⟨lt_of_lt_of_le hU hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
        exact (hcd.mono hsub).intervalIntegrable
    have h1 : |∫ s in (Real.pi / 4)..θ, deriv u s| ≤ M * (Real.pi / 2) := by
      have h2' : |∫ s in (Real.pi / 4)..θ, deriv u s| ≤ M * |θ - Real.pi / 4| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_of_norm_le_const (f := deriv u) (C := M)
            (a := Real.pi / 4) (b := θ) (fun s hs => by
              rw [Set.uIoc, Set.mem_Ioc, min_eq_left hθ.1.le, max_eq_right hθ.1.le] at hs
              rw [Real.norm_eq_abs]
              exact hud s ⟨hs.1, lt_of_le_of_lt hs.2 hθ.2⟩)
      have h3 : |θ - Real.pi / 4| ≤ Real.pi / 2 := by
        rw [abs_of_pos (by linarith [hθ.1])]
        linarith [hθ.2, Real.pi_pos]
      exact h2'.trans (mul_le_mul_of_nonneg_left h3 hMnn)
    have htri : |u θ| ≤ |u (Real.pi / 4)| + |u θ - u (Real.pi / 4)| := by
      have := abs_add_le (u (Real.pi / 4)) (u θ - u (Real.pi / 4))
      simpa using this
    have h4 : |u θ - u (Real.pi / 4)| ≤ M * (Real.pi / 2) := by
      rw [← hFTC]; exact h1
    linarith [htri, h4]
  refine ⟨max 1 (|u (Real.pi / 4)| + M * (Real.pi / 2)),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_, ?_⟩
  · intro θ hθ
    have h1 : |deriv u θ| ≤ M := hud θ hθ
    have h3 : M ≤ M * (Real.pi / 2) := by nlinarith [hMnn, Real.pi_gt_three]
    have h2' : M ≤ |u (Real.pi / 4)| + M * (Real.pi / 2) := by
      linarith [h3, abs_nonneg (u (Real.pi / 4))]
    exact h1.trans (h2'.trans (le_max_right _ _))
  · intro θ hθ
    exact (huBd θ hθ).trans (le_max_right _ _)

theorem weakSliceLimits (u : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (h0 : u 0 = 0) (h1 : u (Real.pi / 2) = 0)
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ)
    (hA : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    (∃ U : ℝ, Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds U)) ∧
      (∃ L : ℝ, Filter.Tendsto (deriv u) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) ∧
      Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) ∧
      MeasureTheory.IntegrableOn (fun θ => deriv (fun t => deriv u t) θ) Work.Spaces.Iθ := by
  have hU : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hq : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) := hu 2
  -- ## Differentiability of `u` and of `u'` on the open interval
  have hderiv2 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t : ℝ => deriv u t) x) x := by
    intro x hx
    have h2' : ContDiffAt ℝ 2 u x := hu2.contDiffAt (isOpen_Ioo.mem_nhds hx)
    have hd1 : ContDiffAt ℝ 1 (deriv u) x := h2'.derivWithin (by norm_num)
    exact (hd1.differentiableAt (by norm_num)).hasDerivAt
  -- ## Integrability of `(u'')²`, of `|u''|` and of `u''` on `Iθ`
  have hsq : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (fun t => deriv u t) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta u h2
  have hD2absIoo : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t => deriv u t) θ|)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq u hsq
  have hD2abs : MeasureTheory.IntegrableOn (fun θ : ℝ => |deriv (fun t => deriv u t) θ|)
      Work.Spaces.Iθ :=
    hD2absIoo.congr_set_ae
      (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)).symm
  have hD2mem : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => deriv (fun t => deriv u t) θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (measurable_deriv (fun t : ℝ => deriv u t)).aestronglyMeasurable
  have hD2int : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv (fun t => deriv u t) θ)
      Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn]
    refine (MeasureTheory.integrable_norm_iff hD2mem).mp ?_
    rw [MeasureTheory.IntegrableOn] at hD2abs
    simpa [Real.norm_eq_abs] using hD2abs
  refine ⟨?_, ?_, ?_, hD2int⟩
  · -- ## The limit of `u` at `0⁺`
    exact Work.FTS.EllipticEst.sliceLimitLeftExists u hu h2
  · -- ## The limit of `u'` at `0⁺`
    refine Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
      (f := deriv u) (f' := fun θ : ℝ => deriv (fun t => deriv u t) θ) hU ?_ ?_
    · intro x hx
      exact hderiv2 x ⟨hx.1, by linarith [hx.2]⟩
    · exact hD2int.mono_set (fun x hx => ⟨le_of_lt hx.1, le_of_lt (by linarith [hx.2])⟩)
  · -- ## The limit of `u` at `(π/2)⁻`
    obtain ⟨C, hC0, -, hCb⟩ := abs_deriv_and_abs_le_right hu2 h2
    have hcontL : ContinuousOn (Work.FTS.EllipticEst.Lzero1 u) (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS.EllipticEst.SliceLocal.continuousOn_Lzero1_of_contDiffOn_two u hu2
    have hLabs : MeasureTheory.IntegrableOn (fun θ : ℝ => |Work.FTS.EllipticEst.Lzero1 u θ|)
        Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.integrableAbsOfSqSeta hcontL hA
    have hsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Work.Spaces.Iθ := fun x hx =>
      ⟨le_of_lt (lt_trans hU hx.1), le_of_lt hx.2⟩
    -- integrability of the three summands on the right tail
    have hLtail : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 u θ)
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
      rw [MeasureTheory.IntegrableOn]
      refine (MeasureTheory.integrable_norm_iff ?_).mp ?_
      · exact (hcontL.mono (Set.Ioo_subset_Ioo_left hU.le)).aestronglyMeasurable
          measurableSet_Ioo
      · have h := hLabs.mono_set hsub
        rw [MeasureTheory.IntegrableOn] at h
        simpa [Real.norm_eq_abs] using h
    have hD2tail : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv (fun t => deriv u t) θ)
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := hD2int.mono_set hsub
    have hutail : MeasureTheory.IntegrableOn u (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
      refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ C ?_
      · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
      · exact (hu2.continuousOn.mono (Set.Ioo_subset_Ioo_left hU.le)).aestronglyMeasurable
          measurableSet_Ioo
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => ?_)
        rw [Real.norm_eq_abs]
        exact hCb x hx
    have hsumtail : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 u θ + deriv (fun t => deriv u t) θ + 6 * u θ)
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      (hLtail.add hD2tail).add (hutail.const_mul 6)
    -- integrate `(tan θ · u)'` on the right tail and squeeze
    obtain ⟨M, hM⟩ := exists_tendsto_nhdsLT_of_integrableOn_deriv hq
      (fun x hx => hasDerivAt_tan_mul_Lzero1 hu2 ⟨lt_trans hU hx.1, hx.2⟩) hsumtail
    exact tendsto_zero_right_of_tan_mul_tendsto hM

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.H2.T1Q.QDefs =====
section

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

set_option autoImplicit false
set_option maxHeartbeats 800000

open Work.FTS.H2



end Work.H2.T1Q
end
end

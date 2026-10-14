import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.kf_ball_integral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

set_option autoImplicit false

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay (kf)

noncomputable section

/-- The surface measure on the unit sphere of `ℝ³`, i.e. `Measure.toSphere volume`
(this is the unnormalised spherical measure, of total mass `4π`). -/
abbrev sphMeasure : Measure (Metric.sphere (0 : Work.LWP.R3) 1) :=
  Measure.toSphere (volume : Measure Work.LWP.R3)

/-- The radius at which the ray in direction `ω` leaves the ball `B(z,ρ)`, for `‖z‖ < ρ`:
the positive root of `r² - 2⟪z,ω⟫r + ‖z‖² - ρ² = 0`, i.e.
`⟪z,ω⟫ + √(⟪z,ω⟫² + ρ² - ‖z‖²)`. -/
noncomputable def rPlus (z : Work.LWP.R3) (ρ : ℝ)
    (ω : Metric.sphere (0 : Work.LWP.R3) 1) : ℝ :=
  inner ℝ z (ω : Work.LWP.R3)
    + Real.sqrt ((inner ℝ z (ω : Work.LWP.R3)) ^ 2 + (ρ ^ 2 - ‖z‖ ^ 2))

/-! ## Polar coordinates in `ℝ³` -/

/-- `Module.finrank ℝ ℝ³ = 3`. -/
lemma finrank_R3_eq_three : Module.finrank ℝ Work.LWP.R3 = 3 := by
  simp [Work.LWP.R3, finrank_euclideanSpace]

/-- The polar (spherical) decomposition of Lebesgue measure on `ℝ³`, in the product form:
integration over `ℝ³` is integration over the unit sphere `S²` and the radial measure
`volumeIoiPow 2` (which has density `r ↦ r²` w.r.t. Lebesgue measure on `(0,∞)`), with the
point `(ω,r)` corresponding to `r • ω`.  This is the vector-valued version of
`Work.CoreResiduals.BiotSavart.polar_decomposition`. -/
theorem polar_decomposition_vec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Work.LWP.R3 → E) :
    ∫ x, F x ∂(volume : Measure Work.LWP.R3)
      = ∫ p : Metric.sphere (0 : Work.LWP.R3) 1 × Set.Ioi (0 : ℝ),
          F (p.2.1 • (p.1.1 : Work.LWP.R3))
          ∂((volume : Measure Work.LWP.R3).toSphere.prod (Measure.volumeIoiPow 2)) := by
  have hmp := Measure.measurePreserving_homeomorphUnitSphereProd
    (μ := (volume : Measure Work.LWP.R3))
  rw [finrank_R3_eq_three] at hmp
  conv_lhs => rw [← restrict_compl_singleton (μ := (volume : Measure Work.LWP.R3))
    (0 : Work.LWP.R3)]
  rw [← integral_subtype_comap (measurableSet_singleton (0 : Work.LWP.R3)).compl F]
  have hcongr : ∀ x : ({0}ᶜ : Set Work.LWP.R3),
      (fun p : Metric.sphere (0 : Work.LWP.R3) 1 × Set.Ioi (0 : ℝ) =>
          F (p.2.1 • (p.1.1 : Work.LWP.R3)))
        (homeomorphUnitSphereProd Work.LWP.R3 x) = F ↑x := by
    intro x
    have h := homeomorphUnitSphereProd_symm_apply_coe Work.LWP.R3
      (homeomorphUnitSphereProd Work.LWP.R3 x)
    rw [Homeomorph.symm_apply_apply] at h
    exact congrArg F h.symm
  rw [show (∫ x : ({0}ᶜ : Set Work.LWP.R3),
              F ↑x ∂(Measure.comap Subtype.val (volume : Measure Work.LWP.R3)))
        = ∫ x, (fun p : Metric.sphere (0 : Work.LWP.R3) 1 × Set.Ioi (0 : ℝ) =>
              F (p.2.1 • (p.1.1 : Work.LWP.R3)))
            (homeomorphUnitSphereProd Work.LWP.R3 x)
            ∂(Measure.comap Subtype.val (volume : Measure Work.LWP.R3))
        from integral_congr_ae (Filter.Eventually.of_forall fun x => (hcongr x).symm)]
  exact hmp.integral_comp (Homeomorph.measurableEmbedding _)
    (fun p : Metric.sphere (0 : Work.LWP.R3) 1 × Set.Ioi (0 : ℝ) =>
      F (p.2.1 • (p.1.1 : Work.LWP.R3)))

/-- Integrability is preserved by the polar decomposition: for `F` integrable on `ℝ³` the
function `p ↦ F (p.2 • p.1)` is integrable for the product of the spherical measure and the
radial measure `volumeIoiPow 2`. -/
theorem integrable_prod_polar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Work.LWP.R3 → E} (hF : Integrable F (volume : Measure Work.LWP.R3)) :
    Integrable (fun p : Metric.sphere (0 : Work.LWP.R3) 1 × Set.Ioi (0 : ℝ) =>
        F (p.2.1 • (p.1.1 : Work.LWP.R3)))
      ((volume : Measure Work.LWP.R3).toSphere.prod (Measure.volumeIoiPow 2)) := by
  have hmp := Measure.measurePreserving_homeomorphUnitSphereProd
    (μ := (volume : Measure Work.LWP.R3))
  rw [finrank_R3_eq_three] at hmp
  rw [← hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)]
  have hcomp : ((fun p : Metric.sphere (0 : Work.LWP.R3) 1 × Set.Ioi (0 : ℝ) =>
      F (p.2.1 • (p.1.1 : Work.LWP.R3))) ∘ (homeomorphUnitSphereProd Work.LWP.R3))
      = fun x : ({0}ᶜ : Set Work.LWP.R3) => F ↑x := by
    funext x
    have h := homeomorphUnitSphereProd_symm_apply_coe Work.LWP.R3
      (homeomorphUnitSphereProd Work.LWP.R3 x)
    rw [Homeomorph.symm_apply_apply] at h
    exact congrArg F h.symm
  rw [hcomp]
  refine (integrableOn_iff_comap_subtypeVal (f := F) (s := ({0}ᶜ : Set Work.LWP.R3))
    (measurableSet_singleton (0 : Work.LWP.R3)).compl).mp ?_
  show Integrable F ((volume : Measure Work.LWP.R3).restrict ({0}ᶜ : Set Work.LWP.R3))
  rw [restrict_compl_singleton (μ := (volume : Measure Work.LWP.R3)) (0 : Work.LWP.R3)]
  exact hF

/-- Polar coordinates in the iterated form: for an integrable `F : ℝ³ → E`,
`∫_ℝ³ F = ∫_{S²} ∫_{(0,∞)} F (r • ω) d(volumeIoiPow 2)(r) dσ(ω)`. -/
theorem integral_polar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Work.LWP.R3 → E} (hF : Integrable F (volume : Measure Work.LWP.R3)) :
    ∫ x, F x ∂(volume : Measure Work.LWP.R3)
      = ∫ ω, (∫ r : Set.Ioi (0 : ℝ), F ((r : ℝ) • (ω : Work.LWP.R3))
          ∂(Measure.volumeIoiPow 2)) ∂sphMeasure := by
  rw [polar_decomposition_vec F, integral_prod _ (integrable_prod_polar hF)]

/-! ## Elementary facts -/

/-- `kf (r • ω) r² = ω` for `r > 0` and `ω` a unit vector. -/
theorem smul_sq_kf_smul (r : ℝ) (hr : 0 < r) (ω : Metric.sphere (0 : Work.LWP.R3) 1) :
    r ^ 2 • kf (r • (ω : Work.LWP.R3)) = (ω : Work.LWP.R3) := by
  have hω : ‖(ω : Work.LWP.R3)‖ = 1 := by
    simpa [dist_eq_norm] using ω.2
  have hnorm : ‖r • (ω : Work.LWP.R3)‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hr.le, hω, mul_one]
  have hne : r ≠ 0 := ne_of_gt hr
  rw [Work.StabilityFar.Decay.kf, hnorm, smul_smul, smul_smul]
  have h3 : r ^ 2 * (r ^ 3)⁻¹ * r = 1 := by
    field_simp
  rw [h3, one_smul]

/-! ## The peak/even decomposition of `rPlus` -/

theorem rPlus_smul_eq (z : Work.LWP.R3) (ρ : ℝ) (ω : Metric.sphere (0 : Work.LWP.R3) 1) :
    rPlus z ρ ω • (ω : Work.LWP.R3)
      = inner ℝ z (ω : Work.LWP.R3) • (ω : Work.LWP.R3)
        + Real.sqrt ((inner ℝ z (ω : Work.LWP.R3)) ^ 2 + (ρ ^ 2 - ‖z‖ ^ 2))
            • (ω : Work.LWP.R3) := by
  rw [rPlus, add_smul]

theorem kf_ball_integral (ρ : ℝ) (hρ : 0 < ρ) (z : Work.LWP.R3) (hz : ‖z‖ < ρ) :
    ∫ b in Metric.ball z ρ, Work.StabilityFar.Decay.kf b = (4 * Real.pi / 3) • z := by
  have hωnorm : ∀ ω : Metric.sphere (0 : Work.LWP.R3) 1, ‖(ω : Work.LWP.R3)‖ = 1 :=
    fun ω => by simpa [dist_eq_norm] using ω.2
  -- The inner radial integral: only the ray up to `rPlus z ρ ω` is seen.
  have hinner : ∀ ω : Metric.sphere (0 : Work.LWP.R3) 1,
      (∫ r : Set.Ioi (0 : ℝ),
          (Metric.ball z ρ).indicator (fun b => kf b) ((r : ℝ) • (ω : Work.LWP.R3))
          ∂(Measure.volumeIoiPow 2)) = rPlus z ρ ω • (ω : Work.LWP.R3) := by
    intro ω
    rw [KfBall.integral_volumeIoiPow_two
      (fun r : ℝ => (Metric.ball z ρ).indicator (fun b => kf b) (r • (ω : Work.LWP.R3)))]
    -- Pointwise, the radial integrand is the indicator of the interval `(0, rPlus z ρ ω)`.
    have hpt : ∀ r ∈ Set.Ioi (0 : ℝ),
        r ^ 2 • (Metric.ball z ρ).indicator (fun b => kf b) (r • (ω : Work.LWP.R3))
          = (Set.Iio (rPlus z ρ ω)).indicator (fun _ => (ω : Work.LWP.R3)) r := by
      intro r hr
      have hr' : (0 : ℝ) < r := hr
      by_cases hmem : r • (ω : Work.LWP.R3) ∈ Metric.ball z ρ
      · rw [Set.indicator_of_mem hmem]
        have hlt : r < rPlus z ρ ω := by
          simpa [rPlus] using (KfBall.mem_ball_smul_sphere_iff z hz ω hr').mp hmem
        rw [Set.indicator_of_mem (Set.mem_Iio.mpr hlt)]
        exact smul_sq_kf_smul r hr' ω
      · rw [Set.indicator_of_notMem hmem]
        have hnc : r ∉ Set.Iio (rPlus z ρ ω) := fun h =>
          hmem (by simpa [rPlus] using (KfBall.mem_ball_smul_sphere_iff z hz ω hr').mpr h)
        rw [Set.indicator_of_notMem hnc]
        simp
    rw [setIntegral_congr_fun measurableSet_Ioi hpt]
    -- The remaining integral of a constant over `(0, rPlus z ρ ω)`.
    have hpos : 0 < rPlus z ρ ω := by
      simpa [rPlus] using KfBall.inner_add_sqrt_pos z hz ω
    have hval : (∫ r in Set.Ioi (0 : ℝ),
          (Set.Iio (rPlus z ρ ω)).indicator (fun _ => (ω : Work.LWP.R3)) r)
        = rPlus z ρ ω • (ω : Work.LWP.R3) := by
      calc ∫ r in Set.Ioi (0 : ℝ),
              (Set.Iio (rPlus z ρ ω)).indicator (fun _ => (ω : Work.LWP.R3)) r
          = ∫ r, (Set.Ioi (0 : ℝ)).indicator
              ((Set.Iio (rPlus z ρ ω)).indicator (fun _ => (ω : Work.LWP.R3))) r :=
            (integral_indicator measurableSet_Ioi (f := (Set.Iio (rPlus z ρ ω)).indicator
              (fun _ => (ω : Work.LWP.R3)))).symm
        _ = ∫ r, (Set.Ioi (0 : ℝ) ∩ Set.Iio (rPlus z ρ ω)).indicator
              (fun _ => (ω : Work.LWP.R3)) r := by rw [Set.indicator_indicator]
        _ = (volume : Measure ℝ).real (Set.Ioi (0 : ℝ) ∩ Set.Iio (rPlus z ρ ω))
              • (ω : Work.LWP.R3) :=
            integral_indicator_const _ (measurableSet_Ioi.inter measurableSet_Iio)
        _ = rPlus z ρ ω • (ω : Work.LWP.R3) := by
            rw [Set.Ioi_inter_Iio, Measure.real_def, Real.volume_Ioo, sub_zero,
              ENNReal.toReal_ofReal (le_of_lt hpos)]
    rw [hval]

  -- The polar reduction.
  have hstep1 : ∫ b in Metric.ball z ρ, kf b
      = ∫ ω, rPlus z ρ ω • (ω : Work.LWP.R3) ∂sphMeasure := by
    rw [← integral_indicator measurableSet_ball (f := fun b : Work.LWP.R3 => kf b)]
    rw [integral_polar ((integrable_indicator_iff measurableSet_ball).mpr
      (KfBall.integrableOn_kf_ball z ρ))]
    exact integral_congr_ae (Filter.Eventually.of_forall hinner)
  -- Integrability of the two parts on the sphere (a finite measure space).
  have hf : Integrable (fun ω : Metric.sphere (0 : Work.LWP.R3) 1 =>
      inner ℝ z (ω : Work.LWP.R3) • (ω : Work.LWP.R3)) sphMeasure := by
    refine Integrable.of_bound (f := fun ω : Metric.sphere (0 : Work.LWP.R3) 1 =>
        inner ℝ z (ω : Work.LWP.R3) • (ω : Work.LWP.R3)) ?_ ‖z‖ ?_
    · change AEStronglyMeasurable ((fun ω : Metric.sphere (0 : Work.LWP.R3) 1 =>
        inner ℝ z (ω : Work.LWP.R3)) • (Subtype.val : Metric.sphere (0 : Work.LWP.R3) 1 →
        Work.LWP.R3)) sphMeasure
      exact (Continuous.smul (continuous_const.inner continuous_subtype_val : Continuous
        (fun ω : Metric.sphere (0 : Work.LWP.R3) 1 => inner ℝ z (ω : Work.LWP.R3)))
        continuous_subtype_val).aestronglyMeasurable
    · filter_upwards with ω
      rw [norm_smul, hωnorm ω, mul_one]
      have h := norm_inner_le_norm (𝕜 := ℝ) z (ω : Work.LWP.R3)
      rw [hωnorm ω, mul_one] at h
      exact h
  have hg : Integrable (fun ω : Metric.sphere (0 : Work.LWP.R3) 1 =>
      Real.sqrt ((inner ℝ z (ω : Work.LWP.R3)) ^ 2 + (ρ ^ 2 - ‖z‖ ^ 2))
        • (ω : Work.LWP.R3)) sphMeasure := by
    refine Integrable.of_bound (f := fun ω : Metric.sphere (0 : Work.LWP.R3) 1 =>
        Real.sqrt ((inner ℝ z (ω : Work.LWP.R3)) ^ 2 + (ρ ^ 2 - ‖z‖ ^ 2))
          • (ω : Work.LWP.R3)) ?_ ρ ?_
    · change AEStronglyMeasurable ((fun ω : Metric.sphere (0 : Work.LWP.R3) 1 =>
        Real.sqrt ((inner ℝ z (ω : Work.LWP.R3)) ^ 2 + (ρ ^ 2 - ‖z‖ ^ 2))) •
        (Subtype.val : Metric.sphere (0 : Work.LWP.R3) 1 → Work.LWP.R3)) sphMeasure
      exact (Continuous.smul (Continuous.sqrt
        (((continuous_const.inner continuous_subtype_val).pow 2).add continuous_const))
        continuous_subtype_val).aestronglyMeasurable
    · filter_upwards with ω
      rw [norm_smul, hωnorm ω, mul_one, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc Real.sqrt ((inner ℝ z (ω : Work.LWP.R3)) ^ 2 + (ρ ^ 2 - ‖z‖ ^ 2))
          ≤ Real.sqrt (ρ ^ 2) := by
            refine Real.sqrt_le_sqrt ?_
            have habs : |inner ℝ z (ω : Work.LWP.R3)| ≤ ‖z‖ := by
              have h := norm_inner_le_norm (𝕜 := ℝ) z (ω : Work.LWP.R3)
              rw [hωnorm ω, mul_one, Real.norm_eq_abs] at h
              exact h
            have h2 : (inner ℝ z (ω : Work.LWP.R3)) ^ 2 ≤ ‖z‖ ^ 2 := by
              nlinarith [abs_nonneg (inner ℝ z (ω : Work.LWP.R3)),
                sq_abs (inner ℝ z (ω : Work.LWP.R3)), habs]
            linarith
        _ = ρ := Real.sqrt_sq hρ.le
  -- Assembly.
  rw [hstep1]
  have hdec : (fun ω : Metric.sphere (0 : Work.LWP.R3) 1 => rPlus z ρ ω • (ω : Work.LWP.R3))
      = fun ω : Metric.sphere (0 : Work.LWP.R3) 1 =>
          inner ℝ z (ω : Work.LWP.R3) • (ω : Work.LWP.R3)
            + Real.sqrt ((inner ℝ z (ω : Work.LWP.R3)) ^ 2 + (ρ ^ 2 - ‖z‖ ^ 2))
                • (ω : Work.LWP.R3) := by
    funext ω
    exact rPlus_smul_eq z ρ ω
  rw [hdec, integral_add hf hg,
    KfBall.sphere_integral_inner_smul z,
    KfBall.sphere_integral_even_smul_eq_zero (fun t => Real.sqrt (t ^ 2 + (ρ ^ 2 - ‖z‖ ^ 2)))
      (fun t => by rw [neg_sq]) z]
  simp

end

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.norm_resid_mul_rpow_le_far =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- **Weighted far-field residual bound.**  In the far regime `2‖h‖ ≤ ‖y‖` the second-order
Taylor residual of the Newtonian kernel satisfies

  `‖y‖ ^ c ‖resid h y‖ ≤ 1024 ‖h‖² ‖y‖ ^ (c - 4)`

for *every* real exponent `c` (no sign restriction: the case `‖y‖ = 0` is degenerate and both
sides vanish). -/
theorem norm_resid_mul_rpow_le_far {c : ℝ} (h y : Work.LWP.R3) (hy : 2 * ‖h‖ ≤ ‖y‖) :
    ‖y‖ ^ c * ‖Work.CoreResiduals.BiotSavart.resid h y‖
      ≤ 1024 * ‖h‖ ^ (2:ℕ) * ‖y‖ ^ (c - 4) := by
  rcases eq_or_lt_of_le (norm_nonneg y) with hy0 | hypos
  · -- `y = 0`: the hypothesis forces `h = 0` and both sides vanish
    have hh0 : h = 0 := by
      rw [← norm_eq_zero]
      have h2 : 2 * ‖h‖ ≤ 0 := by
        have h2' := hy
        rw [← hy0] at h2'
        exact h2'
      linarith [norm_nonneg h]
    have hy00 : y = 0 := norm_eq_zero.mp hy0.symm
    rw [hh0, hy00]
    simp [Work.CoreResiduals.BiotSavart.resid]
  · -- `y ≠ 0`: multiply the unweighted far bound by the nonnegative weight `‖y‖ ^ c`
    have hfar := norm_resid_le_far h y hy
    have h4 : ‖y‖ ^ c * ‖y‖ ^ (-4:ℝ) = ‖y‖ ^ (c - 4) := by
      rw [← Real.rpow_add hypos]
      ring_nf
    calc ‖y‖ ^ c * ‖Work.CoreResiduals.BiotSavart.resid h y‖
        ≤ ‖y‖ ^ c * (1024 * ‖h‖ ^ (2:ℕ) * ‖y‖ ^ (-4:ℝ)) :=
          mul_le_mul_of_nonneg_left hfar (Real.rpow_nonneg (norm_nonneg y) c)
      _ = 1024 * ‖h‖ ^ (2:ℕ) * (‖y‖ ^ c * ‖y‖ ^ (-4:ℝ)) := by ring
      _ = 1024 * ‖h‖ ^ (2:ℕ) * ‖y‖ ^ (c - 4) := by rw [h4]

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-!
## The two-dimensional radial self-pairing bound `dzSelf2d`

Given the one-dimensional self-pairing bound `h1d` (for every admissible `Y`,
`|∫_0^∞ w² (z Y') Y| ≤ 2 ∫_0^∞ w² Y²`), and an angular weight `θw > 0` on `(0, π/2)`,
the same bound holds for the two-dimensional pairing against `θw θ dθ`:

`|∫_z ∫_θ w(z)² θw(θ) (z ∂_z V)(z,θ) V(z,θ)| ≤ 2 ∫_z ∫_θ w(z)² θw(θ) V(z,θ)²`.

The proof applies `h1d` slicewise in `θ` (for a.e. `θ`, using the slice integrability that
`hF`/`hD` supply by Fubini), multiplies by `θw θ ≥ 0`, and integrates in `θ`; Fubini
(`integral_integral`, `integral_integral_swap`) converts between the two orders.

The only non-routine point is that the cross term has to be *jointly* a.e.-measurable before
Fubini can be applied: `hF`/`hD` only give joint measurability of `w² V² θw` and
`w² (z ∂_zV)² θw`, not of the cross term.  The missing piece is supplied by
`aemeasurable_deriv_fst` (the derivative in `z` of an a.e.-measurable function whose
`z`-slices are differentiable is again a.e.-measurable), applied to the a.e.-measurable
weighted square `Φ(z,θ) = θw θ · V(z,θ)²`, whose `z`-derivative is `2 θw θ V ∂_z V`; the
square-integrability of `V` and `∂_z V` supplies the finite-integral part by AM–GM.

The index sets are `Iz = [0,∞)` and `Iθ = [0,π/2]`; they differ from `(0,∞)` resp.
`(0,π/2)` by null sets, which is what lets `h1d` (stated on `(0,∞)`) be applied to the
`Iθ`-slices (`hθw_nn`/`hθw_pos` are only assumed on the open interval).
-/

noncomputable section

/-- `[0,∞)` and `(0,∞)` agree a.e. for Lebesgue measure. -/
theorem dzSelf2d_Iz_ae : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0:ℝ) := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine measure_mono_null ?_ (measure_singleton (0:ℝ))
    intro x hx
    simp only [Work.Spaces.Iz, Set.mem_sdiff, Set.mem_Ici, Set.mem_Ioi,
      Set.mem_singleton_iff] at hx ⊢
    exact le_antisymm (not_lt.mp hx.2) hx.1
  · rw [show Work.Spaces.Iz = Set.Ici (0:ℝ) from rfl,
      Set.sdiff_eq_empty.mpr Set.Ioi_subset_Ici_self, measure_empty]

/-- `[0,π/2]` and `(0,π/2)` agree a.e. for Lebesgue measure. -/
theorem dzSelf2d_Ith_ae : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0:ℝ) (π/2) := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine measure_mono_null ?_ (measure_union_null (measure_singleton (0:ℝ))
      (measure_singleton (π/2)))
    intro x hx
    simp only [Work.Spaces.Iθ, Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioo, Set.mem_union,
      Set.mem_singleton_iff] at hx ⊢
    rcases hx with ⟨⟨h0, hc⟩, hnot⟩
    rcases not_and_or.mp hnot with h | h
    · left; exact le_antisymm (not_lt.mp h) h0
    · right; exact le_antisymm hc (not_lt.mp h)
  · rw [show Work.Spaces.Iθ = Set.Icc (0:ℝ) (π/2) from rfl,
      Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self, measure_empty]

/-- **The Fubini reduction.**  From the 1-D bound `h1d`, the slice integrability of the two
quadratic forms, and the product-integrability of the cross term `F` and of the `V²` term,
the 2-D bound follows. -/
theorem dzSelf2d_main {θw : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h1d : ∀ (Y : ℝ → ℝ), ContDiffOn ℝ 1 Y (Set.Ioi 0) →
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) (Set.Ioi 0) →
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv Y z) ^ 2)
        (Set.Ioi 0) →
      |∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z)|
        ≤ 2 * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2)
    (hθw_nn : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ θw θ)
    (hθw_pos : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 < θw θ)
    (hV : ∀ θ ∈ Set.Ioo 0 (π / 2), ContDiffOn ℝ 1 (fun z => V z θ) (Set.Ioi 0))
    (hF : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (V p.1 p.2) ^ 2 * θw p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hD : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (p.1 * Work.Spaces.pz V p.1 p.2) ^ 2 * θw p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hIntF : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * θw p.2
        * ((p.1 * Work.Spaces.pz V p.1 p.2) * V p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hIntG : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * θw p.2 * (V p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * ((z * Work.Spaces.pz V z θ) * V z θ)|
      ≤ 2 * ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * (V z θ) ^ 2 := by
  have hΛz : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) :=
    Measure.restrict_congr_set dzSelf2d_Iz_ae
  have hΛθ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) (π / 2)) :=
    Measure.restrict_congr_set dzSelf2d_Ith_ae
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0:ℝ) (π / 2) := by
    have h := MeasureTheory.ae_restrict_mem (μ := (MeasureTheory.volume : Measure ℝ))
      (s := Set.Ioo (0:ℝ) (π / 2)) measurableSet_Ioo
    rwa [← hΛθ] at h
  -- slice integrability for a.e. `θ`
  have hsliceF : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) (Set.Ioi 0) := by
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2 * θw θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Integrable.prod_left_ae hF
    filter_upwards [h1, haeθ] with θ hθ hmem
    have hne : θw θ ≠ 0 := ne_of_gt (hθw_pos θ hmem)
    have h2 : MeasureTheory.Integrable
        (fun z => θw θ * ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hθ
    have h3 : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hne)
        (fun z => (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)).mp h2
    rw [hΛz] at h3
    exact h3
  have hsliceD : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2)
        (Set.Ioi 0) := by
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.Integrable
          (fun z => (Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2 * θw θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Integrable.prod_left_ae hD
    filter_upwards [h1, haeθ] with θ hθ hmem
    have hne : θw θ ≠ 0 := ne_of_gt (hθw_pos θ hmem)
    have h2 : MeasureTheory.Integrable
        (fun z => θw θ * ((Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hθ
    have h3 : MeasureTheory.Integrable
        (fun z => (Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hne)
        (fun z => (Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2)).mp h2
    rw [hΛz] at h3
    exact h3
  -- the a.e.-`θ` slicewise 1-D bound, multiplied by `θw θ ≥ 0`
  have hkey : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * θw θ * ((z * Work.Spaces.pz V z θ) * V z θ)|
        ≤ 2 * (θw θ * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) := by
    filter_upwards [haeθ, hsliceF, hsliceD] with θ hmem hsf hsd
    have h1 := h1d (fun z => V z θ) (hV θ hmem) hsf hsd
    have hL : (∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * θw θ * ((z * Work.Spaces.pz V z θ) * V z θ))
        = θw θ * (∫ z in Set.Ioi 0,
            (Work.Spaces.w z) ^ 2 * ((z * Work.Spaces.pz V z θ) * V z θ)) := by
      rw [setIntegral_congr_set dzSelf2d_Iz_ae]
      rw [← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun z => by ring)
    rw [hL, abs_mul, abs_of_nonneg (hθw_nn θ hmem)]
    calc θw θ * |∫ z in Set.Ioi 0,
            (Work.Spaces.w z) ^ 2 * ((z * Work.Spaces.pz V z θ) * V z θ)|
        ≤ θw θ * (2 * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (hθw_nn θ hmem)
      _ = 2 * (θw θ * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) := by ring
  -- integrability of the upper bound `θ ↦ 2 * (θw θ * ∫_z w²V²)`
  have hψ : MeasureTheory.Integrable
      (fun θ => θw θ * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := MeasureTheory.Integrable.integral_prod_right hF
    have hfun : (fun θ => ∫ z, (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2 * θw θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        = fun θ => θw θ * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2 := by
      funext θ
      rw [show (fun z => (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2 * θw θ)
          = fun z => θw θ * ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) from by funext z; ring]
      rw [MeasureTheory.integral_const_mul]
      rw [setIntegral_congr_set dzSelf2d_Iz_ae]
    rwa [hfun] at h
  have hψ2 : MeasureTheory.Integrable
      (fun θ => 2 * (θw θ * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hψ.const_mul 2
  have hLHS : MeasureTheory.Integrable
      (fun θ => |∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * θw θ * ((z * Work.Spaces.pz V z θ) * V z θ)|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := MeasureTheory.Integrable.integral_prod_right hIntF
    exact h.abs
  -- Fubini and the comparison
  have hswap : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * ((z * Work.Spaces.pz V z θ) * V z θ))
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * θw θ * ((z * Work.Spaces.pz V z θ) * V z θ) :=
    integral_integral_swap hIntF
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * ((z * Work.Spaces.pz V z θ) * V z θ)|
      = |∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * θw θ * ((z * Work.Spaces.pz V z θ) * V z θ)| := by
        rw [hswap]
    _ ≤ ∫ θ in Work.Spaces.Iθ,
          |∫ z in Work.Spaces.Iz,
            (Work.Spaces.w z) ^ 2 * θw θ * ((z * Work.Spaces.pz V z θ) * V z θ)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ θ in Work.Spaces.Iθ,
          2 * (θw θ * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) :=
        integral_mono_ae hLHS hψ2 hkey
    _ = 2 * ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * θw θ * (V z θ) ^ 2 := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        rw [integral_integral_swap hIntG]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with θ
        rw [show (fun z => (Work.Spaces.w z) ^ 2 * θw θ * (V z θ) ^ 2)
            = fun z => θw θ * ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) from by funext z; ring]
        rw [MeasureTheory.integral_const_mul, setIntegral_congr_set dzSelf2d_Iz_ae]

/-- The weighted square `θw θ · V(z,θ)²` is a.e.-measurable.  (Obtained from the
product-integrability of `w²V²θw` by dividing by the `z`-weight `w²`, which is Borel
measurable and non-zero on the support of the measure.) -/
theorem dzSelf2d_thwVsq_aemeasurable {θw : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hF : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (V p.1 p.2) ^ 2 * θw p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    AEMeasurable
      (fun p : ℝ × ℝ => θw p.2 * (V p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hΛz : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) :=
    Measure.restrict_congr_set dzSelf2d_Iz_ae
  have hF' := hF
  rw [hΛz] at hF'
  have hG : AEMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (V p.1 p.2) ^ 2 * θw p.2)
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hF'.aemeasurable
  have hw : AEMeasurable (fun p : ℝ × ℝ => ((Work.Spaces.w p.1) ^ 2)⁻¹)
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have hw1 : Measurable (fun z : ℝ => Work.Spaces.w z) := by
      have : (Work.Spaces.w : ℝ → ℝ) = fun z => (1 + z) ^ 2 * (z ^ 2)⁻¹ := rfl
      rw [this]
      exact ((measurable_const.add measurable_id).pow_const 2).mul
        ((measurable_id.pow_const 2).inv)
    exact ((hw1.comp measurable_fst).pow_const 2).inv.aemeasurable
  refine (hG.mul hw).congr ?_
  -- a.e. `p.1 > 0`
  have hp1 : ∀ᵐ p ∂((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 < p.1 := by
    refine (Measure.ae_prod_iff_ae_ae ?_).mpr ?_
    · exact measurableSet_lt measurable_const measurable_fst
    · filter_upwards [MeasureTheory.ae_restrict_mem (μ := (MeasureTheory.volume : Measure ℝ))
        (s := Set.Ioi (0:ℝ)) measurableSet_Ioi] with x hx
      exact Eventually.of_forall fun y => hx
  filter_upwards [hp1] with p hp1'
  have hw0 : Work.Spaces.w p.1 ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 (by linarith : (1 + p.1) ≠ 0))
      (pow_ne_zero 2 (by linarith : p.1 ≠ 0))
  simp only [Pi.mul_apply]
  rw [show (Work.Spaces.w p.1) ^ 2 * (V p.1 p.2) ^ 2 * θw p.2
        * ((Work.Spaces.w p.1) ^ 2)⁻¹
      = ((Work.Spaces.w p.1) ^ 2 * ((Work.Spaces.w p.1) ^ 2)⁻¹)
        * ((V p.1 p.2) ^ 2 * θw p.2) from by ring]
  rw [mul_inv_cancel₀ (pow_ne_zero 2 hw0), one_mul]
  ring

/-- **A.e.-measurability of the cross term** `w(z)² θw(θ) (z ∂_zV)(z,θ) V(z,θ)`.

`hF` supplies joint a.e.-measurability of `θw(θ)·V(z,θ)²`; its `z`-slice is differentiable
for every `θ` (after redefining it outside `(0,π/2)`, where its values are irrelevant), so
`aemeasurable_deriv_fst` gives joint a.e.-measurability of the `z`-derivative
`2 θw(θ) V ∂_zV`; multiplying by the Borel function `w(z)² z / 2` gives the cross term. -/
theorem dzSelf2d_cross_aemeasurable {θw : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hV : ∀ θ ∈ Set.Ioo 0 (π / 2), ContDiffOn ℝ 1 (fun z => V z θ) (Set.Ioi 0))
    (hF : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (V p.1 p.2) ^ 2 * θw p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    AEMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * θw p.2
        * ((p.1 * Work.Spaces.pz V p.1 p.2) * V p.1 p.2))
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  set Φ : ℝ × ℝ → ℝ :=
    fun p => if p.2 ∈ Set.Ioo (0:ℝ) (π / 2) then θw p.2 * V p.1 p.2 ^ 2 else 0 with hΦdef
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0:ℝ) (π / 2) := by
    have h := MeasureTheory.ae_restrict_mem (μ := (MeasureTheory.volume : Measure ℝ))
      (s := Set.Ioo (0:ℝ) (π / 2)) measurableSet_Ioo
    rwa [← Measure.restrict_congr_set dzSelf2d_Ith_ae] at h
  have hp2 : ∀ᵐ p ∂((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Set.Ioo (0:ℝ) (π / 2) := by
    refine (Measure.ae_prod_iff_ae_ae (p := fun z : ℝ × ℝ => z.2 ∈ Set.Ioo (0:ℝ) (π / 2))
      (measurableSet_Ioo.preimage measurable_snd)).mpr ?_
    exact Eventually.of_forall fun x => haeθ
  have hp1 : ∀ᵐ p ∂((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 < p.1 := by
    refine (Measure.ae_prod_iff_ae_ae (p := fun z : ℝ × ℝ => 0 < z.1)
      (measurableSet_lt measurable_const measurable_fst)).mpr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := (MeasureTheory.volume : Measure ℝ))
      (s := Set.Ioi (0:ℝ)) measurableSet_Ioi] with x hx
    exact Eventually.of_forall fun y => hx
  -- a.e.-measurability of `Φ`
  have hAEMΦ : AEMeasurable Φ ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have hV2 := dzSelf2d_thwVsq_aemeasurable (θw := θw) (V := V) hF
    refine hV2.congr ?_
    filter_upwards [hp2] with p hp
    simp only [hΦdef, hp, ite_true]
  -- differentiability of the slices of `Φ`
  have hdiff : ∀ θ : ℝ, DifferentiableOn ℝ (fun z => Φ (z, θ)) (Set.Ioi (0:ℝ)) := by
    intro θ
    by_cases hθ : θ ∈ Set.Ioo (0:ℝ) (π / 2)
    · have hfun : (fun z => Φ (z, θ)) = fun z => θw θ * V z θ ^ 2 := by
        funext z; simp only [hΦdef, hθ, ite_true]
      rw [hfun]
      exact (((hV θ hθ).differentiableOn one_ne_zero).pow 2).const_mul (θw θ)
    · have hfun : (fun z => Φ (z, θ)) = fun _ => (0 : ℝ) := by
        funext z; simp only [hΦdef, hθ, ite_false]
      rw [hfun]
      exact differentiableOn_const 0
  have hderiv : AEMeasurable (fun p : ℝ × ℝ => deriv (fun z => Φ (z, p.2)) p.1)
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    aemeasurable_deriv_fst hAEMΦ hdiff
  have hfac : AEMeasurable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (p.1 / 2))
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have hw1 : Measurable (fun z : ℝ => Work.Spaces.w z) := by
      have : (Work.Spaces.w : ℝ → ℝ) = fun z => (1 + z) ^ 2 * (z ^ 2)⁻¹ := rfl
      rw [this]
      exact ((measurable_const.add measurable_id).pow_const 2).mul
        ((measurable_id.pow_const 2).inv)
    exact (((hw1.comp measurable_fst).pow_const 2).mul (measurable_fst.div_const 2)).aemeasurable
  refine (hfac.mul hderiv).congr ?_
  filter_upwards [hp1, hp2] with p hp1' hp2'
  simp only [Pi.mul_apply]
  have hΦeq : (fun z => Φ (z, p.2)) = fun z => θw p.2 * V z p.2 ^ 2 := by
    funext z; simp only [hΦdef, hp2', ite_true]
  have hdV : DifferentiableAt ℝ (fun z => V z p.2) p.1 :=
    ((hV p.2 hp2').differentiableOn one_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds hp1')
  have hstep1 : deriv (fun z => θw p.2 * V z p.2 ^ 2) p.1
      = θw p.2 * deriv (fun z => V z p.2 ^ 2) p.1 :=
    deriv_const_mul (θw p.2) (hdV.pow 2)
  have hstep2 : deriv (fun z => V z p.2 ^ 2) p.1
      = 2 * V p.1 p.2 * deriv (fun z => V z p.2) p.1 := by
    rw [deriv_fun_pow hdV 2]
    norm_num
  rw [hΦeq, hstep1, hstep2]
  simp only [Work.Spaces.pz]
  ring

/-- The cross term has finite integral (AM–GM against the two quadratic forms, both of which
are product-integrable by `hF`/`hD`). -/
theorem dzSelf2d_cross_hasFiniteIntegral {θw : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hF : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (V p.1 p.2) ^ 2 * θw p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hD : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (p.1 * Work.Spaces.pz V p.1 p.2) ^ 2 * θw p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    HasFiniteIntegral
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * θw p.2
        * ((p.1 * Work.Spaces.pz V p.1 p.2) * V p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  have hpt : ∀ p : ℝ × ℝ,
      ‖(Work.Spaces.w p.1) ^ 2 * θw p.2 * ((p.1 * Work.Spaces.pz V p.1 p.2) * V p.1 p.2)‖
        ≤ ‖(Work.Spaces.w p.1) ^ 2 * (V p.1 p.2) ^ 2 * θw p.2‖
          + ‖(Work.Spaces.w p.1) ^ 2 * (p.1 * Work.Spaces.pz V p.1 p.2) ^ 2 * θw p.2‖ := by
    intro p
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    have h6 : |(Work.Spaces.w p.1) ^ 2 * θw p.2
          * ((p.1 * Work.Spaces.pz V p.1 p.2) * V p.1 p.2)|
        = (Work.Spaces.w p.1) ^ 2 * |θw p.2|
          * (|p.1 * Work.Spaces.pz V p.1 p.2| * |V p.1 p.2|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_sq] <;> ring
    have h4 : |(Work.Spaces.w p.1) ^ 2 * (V p.1 p.2) ^ 2 * θw p.2|
        = (Work.Spaces.w p.1) ^ 2 * |θw p.2| * (V p.1 p.2) ^ 2 := by
      rw [abs_mul, abs_mul, abs_sq, abs_sq] <;> ring
    have h5 : |(Work.Spaces.w p.1) ^ 2 * (p.1 * Work.Spaces.pz V p.1 p.2) ^ 2 * θw p.2|
        = (Work.Spaces.w p.1) ^ 2 * |θw p.2| * (p.1 * Work.Spaces.pz V p.1 p.2) ^ 2 := by
      rw [abs_mul, abs_mul, abs_sq, abs_sq] <;> ring
    rw [h6, h4, h5]
    have hAB : |p.1 * Work.Spaces.pz V p.1 p.2| * |V p.1 p.2|
        ≤ |p.1 * Work.Spaces.pz V p.1 p.2| ^ 2 + |V p.1 p.2| ^ 2 := by
      nlinarith [sq_nonneg (|p.1 * Work.Spaces.pz V p.1 p.2| - |V p.1 p.2|)]
    have hWt : 0 ≤ (Work.Spaces.w p.1) ^ 2 * |θw p.2| :=
      mul_nonneg (sq_nonneg _) (abs_nonneg _)
    calc (Work.Spaces.w p.1) ^ 2 * |θw p.2|
          * (|p.1 * Work.Spaces.pz V p.1 p.2| * |V p.1 p.2|)
        ≤ (Work.Spaces.w p.1) ^ 2 * |θw p.2|
          * (|p.1 * Work.Spaces.pz V p.1 p.2| ^ 2 + |V p.1 p.2| ^ 2) :=
          mul_le_mul_of_nonneg_left hAB hWt
      _ = (Work.Spaces.w p.1) ^ 2 * |θw p.2| * (V p.1 p.2) ^ 2
          + (Work.Spaces.w p.1) ^ 2 * |θw p.2|
            * (p.1 * Work.Spaces.pz V p.1 p.2) ^ 2 := by
          rw [sq_abs, sq_abs] <;> ring
  have hfin : (∫⁻ p, (‖(Work.Spaces.w p.1) ^ 2 * (V p.1 p.2) ^ 2 * θw p.2‖ₑ
      + ‖(Work.Spaces.w p.1) ^ 2 * (p.1 * Work.Spaces.pz V p.1 p.2) ^ 2 * θw p.2‖ₑ)
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) < ⊤ := by
    rw [MeasureTheory.lintegral_enorm_add_left hF.1]
    exact ENNReal.add_lt_top.mpr ⟨hF.2, hD.2⟩
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono_ae ?_) hfin
  filter_upwards with p
  have h1 : ‖(Work.Spaces.w p.1) ^ 2 * (V p.1 p.2) ^ 2 * θw p.2‖ₑ
        + ‖(Work.Spaces.w p.1) ^ 2 * (p.1 * Work.Spaces.pz V p.1 p.2) ^ 2 * θw p.2‖ₑ
      = ENNReal.ofReal (‖(Work.Spaces.w p.1) ^ 2 * (V p.1 p.2) ^ 2 * θw p.2‖
          + ‖(Work.Spaces.w p.1) ^ 2 * (p.1 * Work.Spaces.pz V p.1 p.2) ^ 2 * θw p.2‖) := by
    rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm, ofReal_norm]
  rw [h1, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hpt p)

theorem dzSelf2d {θw : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h1d : ∀ (Y : ℝ → ℝ), ContDiffOn ℝ 1 Y (Set.Ioi 0) →
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) (Set.Ioi 0) →
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv Y z) ^ 2)
        (Set.Ioi 0) →
      |∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ((z * deriv Y z) * Y z)|
        ≤ 2 * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2)
    (hθw_nn : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ θw θ)
    (hθw_pos : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 < θw θ)
    (hV : ∀ θ ∈ Set.Ioo 0 (π / 2), ContDiffOn ℝ 1 (fun z => V z θ) (Set.Ioi 0))
    (hF : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (V p.1 p.2) ^ 2 * θw p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hD : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (p.1 * Work.Spaces.pz V p.1 p.2) ^ 2 * θw p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * ((z * Work.Spaces.pz V z θ) * V z θ)|
      ≤ 2 * ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * (V z θ) ^ 2 := by
  have hΛz : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) :=
    Measure.restrict_congr_set dzSelf2d_Iz_ae
  have hIntG : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * θw p.2 * (V p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hF
  have hF' := hF
  rw [hΛz] at hF'
  have hAEM0 : AEMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * θw p.2
        * ((p.1 * Work.Spaces.pz V p.1 p.2) * V p.1 p.2))
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    dzSelf2d_cross_aemeasurable hV hF
  have hAEM : AEMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * θw p.2
        * ((p.1 * Work.Spaces.pz V p.1 p.2) * V p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rwa [← hΛz] at hAEM0
  have hfin := dzSelf2d_cross_hasFiniteIntegral hF hD
  have hIntF : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * θw p.2
        * ((p.1 * Work.Spaces.pz V p.1 p.2) * V p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    ⟨hAEM.aestronglyMeasurable, hfin⟩
  exact dzSelf2d_main h1d hθw_nn hθw_pos hV hF hD hIntF hIntG

end

end Work.FTS.StrongPersist.H6Pair6Aux
end

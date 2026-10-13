/-
# `Work.CoreResiduals.BiotSavart.kf_ball_integral` — the ball-potential identity for the
Newtonian kernel `b ↦ ‖b‖⁻³ • b`

For `‖z‖ < ρ` the integral of the Biot–Savart kernel `kf b = ‖b‖⁻³ • b` over the ball
`B(z,ρ)` — a ball which *contains the singularity* `b = 0` in its interior — equals
`(4π/3) • z`.  This is the elementary elliptic identity that produces the *shape term*
`(4π/3) • crossL (ω x)` in the derivative of the Biot–Savart field.

## Proof

Write the integral over `B(z,ρ)` in polar coordinates about the origin (which lies in the
interior of `B(z,ρ)` as `‖z‖ < ρ`):

`∫_{B(z,ρ)} kf = ∫_{S²} (∫_0^{r₊(ω)} kf (r • ω) r² dr) dω = ∫_{S²} r₊(ω) • ω dω`,

where `r₊(ω) = ⟪z,ω⟫ + √(⟪z,ω⟫² + ρ² - ‖z‖²)` is the (unique) positive radius at which the
ray `r ↦ r • ω` leaves the ball: indeed `r • ω ∈ B(z,ρ) ↔ r < r₊(ω)` for `r > 0`, and
`kf (r • ω) r² = ω` there.  The function `r₊` splits into the *odd* part `⟪z,·⟫` and the
*even* part `√(⟪z,·⟫² + ρ² - ‖z‖²)`; the even part is annihilated by the antipodal symmetry
of the sphere measure, and the odd part is the second moment
`∫_{S²} ⟪z,ω⟫ • ω dω = (4π/3) • z`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.CoreResiduals.BiotSavart.KfBall.integral_volumeIoiPow_two
import Submission.Work.CoreResiduals.BiotSavart.KfBall.inner_add_sqrt_pos
import Submission.Work.CoreResiduals.BiotSavart.KfBall.mem_ball_smul_sphere_iff
import Submission.Work.CoreResiduals.BiotSavart.KfBall.sphere_integral_inner_smul
import Submission.Work.CoreResiduals.BiotSavart.KfBall.sphere_integral_even_smul_eq_zero
import Submission.Work.CoreResiduals.BiotSavart.KfBall.integrableOn_kf_ball

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

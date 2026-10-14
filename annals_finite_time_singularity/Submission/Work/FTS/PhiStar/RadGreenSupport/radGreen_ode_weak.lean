import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.DerivLikeBasic
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.scoef_sum_shift
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.thD_reindex
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.KfBall.sphere_integral_inner_smul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart.KfBall

open MeasureTheory Set
open scoped Topology

noncomputable section

/-! ## Elementary coordinates facts for `ℝ³` -/

/-- `⟪x, y⟫ = ∑ i, y i * x i` in `ℝ³`. -/
lemma inner_eq_sum (x y : Work.LWP.R3) : inner ℝ x y = ∑ i, y i * x i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [RCLike.inner_apply]; simp

/-- `⟪x, y⟫ = ∑ i, x i * y i` in `ℝ³`. -/
lemma inner_eq_sum' (x y : Work.LWP.R3) : inner ℝ x y = ∑ i, x i * y i := by
  rw [inner_eq_sum]
  exact Finset.sum_congr rfl (fun i _ => mul_comm (y i) (x i))

/-- `‖x‖² = ∑ i, (x i)²` in `ℝ³`. -/
lemma norm_sq_eq_sum (x : Work.LWP.R3) : ‖x‖ ^ 2 = ∑ i : Fin 3, (x i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-! ## Invariance of the ball integral under isometries -/

/-- Change of variables in the unit-ball integral under a linear isometry of `ℝ³`. -/
lemma ball_integral_comp_isometry (f : Work.LWP.R3 ≃ₗᵢ[ℝ] Work.LWP.R3)
    (g : Work.LWP.R3 → ℝ) :
    ∫ x in Metric.ball (0 : Work.LWP.R3) 1, g (f x)
      = ∫ x in Metric.ball (0 : Work.LWP.R3) 1, g x := by
  classical
  have hpre : f ⁻¹' Metric.ball (0 : Work.LWP.R3) 1 = Metric.ball 0 1 := by
    rw [LinearIsometryEquiv.preimage_ball]; simp
  have hiff : ∀ x, (f x ∈ Metric.ball (0 : Work.LWP.R3) 1) ↔ (x ∈ Metric.ball 0 1) :=
    fun x => by rw [← Set.mem_preimage, hpre]
  have hfun : (fun x => (Metric.ball (0 : Work.LWP.R3) 1).indicator (fun x => g (f x)) x)
      = (fun x => (Metric.ball (0 : Work.LWP.R3) 1).indicator g (f x)) := by
    funext x
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : x ∈ Metric.ball (0 : Work.LWP.R3) 1
    · rw [if_pos h, if_pos ((hiff x).mpr h)]
    · rw [if_neg h, if_neg (fun hf => h ((hiff x).mp hf))]
  conv_lhs => rw [← integral_indicator measurableSet_ball]
  conv_rhs => rw [← integral_indicator measurableSet_ball]
  rw [hfun]
  exact MeasureTheory.integral_comp f ((Metric.ball (0 : Work.LWP.R3) 1).indicator g)

/-- Any continuous function on `ℝ³` is integrable on the unit ball. -/
lemma integrable_of_continuous_ball {f : Work.LWP.R3 → ℝ} (hf : Continuous f) :
    Integrable f (volume.restrict (Metric.ball (0 : Work.LWP.R3) 1)) :=
  (ContinuousOn.integrableOn_compact (μ := volume) (isCompact_closedBall (0 : Work.LWP.R3) 1)
    hf.continuousOn).mono_set Metric.ball_subset_closedBall

/-- The isometry of `ℝ³` negating the `i`-th coordinate. -/
def flipCoord (i : Fin 3) : Work.LWP.R3 ≃ₗᵢ[ℝ] Work.LWP.R3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun j : Fin 3 => if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

lemma flipCoord_apply (i k : Fin 3) (x : Work.LWP.R3) :
    (flipCoord i x) k = if k = i then -x k else x k := by
  show (LinearIsometryEquiv.piLpCongrRight 2 _ x) k = _
  rw [LinearIsometryEquiv.piLpCongrRight_apply]
  split <;> simp_all

/-- The isometry of `ℝ³` swapping the `i`-th and `j`-th coordinates. -/
def swapCoord (i j : Fin 3) : Work.LWP.R3 ≃ₗᵢ[ℝ] Work.LWP.R3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)

lemma swapCoord_apply (i j k : Fin 3) (x : Work.LWP.R3) :
    (swapCoord i j x) k = x (Equiv.swap i j k) := by
  show (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j) x) k = _
  rw [show (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j) x) k
        = ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j) x).ofLp) k from rfl]
  rw [LinearIsometryEquiv.piLpCongrLeft_apply]
  simp [Equiv.piCongrLeft']

/-! ## Coordinate moments of the unit ball -/

/-- The off-diagonal coordinate moments of the unit ball vanish. -/
lemma moment_off (i j : Fin 3) (hij : i ≠ j) :
    ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x i) * (x j) = 0 := by
  have h1 : ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x i) * (x j)
      = ∫ x in Metric.ball (0 : Work.LWP.R3) 1,
          ((flipCoord j x) i) * ((flipCoord j x) j) := by
    rw [ball_integral_comp_isometry (flipCoord j) (fun x => (x i) * (x j))]
  have h2 : ∫ x in Metric.ball (0 : Work.LWP.R3) 1,
          ((flipCoord j x) i) * ((flipCoord j x) j)
      = - ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x i) * (x j) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    rw [flipCoord_apply, flipCoord_apply, if_neg hij, if_pos rfl]
    ring
  linarith [h1, h2]

/-- The diagonal coordinate moments of the unit ball are all equal. -/
lemma moment_sq_eq (i j : Fin 3) :
    ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x i) ^ 2
      = ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x j) ^ 2 := by
  have h1 : ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x j) ^ 2
      = ∫ x in Metric.ball (0 : Work.LWP.R3) 1, ((swapCoord i j x) j) ^ 2 := by
    rw [ball_integral_comp_isometry (swapCoord i j) (fun x => (x j) ^ 2)]
  rw [h1]
  apply integral_congr_ae
  filter_upwards with x
  rw [swapCoord_apply, Equiv.swap_apply_right]

/-- `∫_{B} ‖x‖² = 4π/5`. -/
lemma norm_sq_ball_integral :
    ∫ x in Metric.ball (0 : Work.LWP.R3) 1, ‖x‖ ^ 2 = 4 * Real.pi / 5 := by
  have h := radial_rpow_integral 2 (by norm_num) 1 (by norm_num)
  norm_num at h
  exact h

/-- Every diagonal coordinate moment of the unit ball equals `4π/15`. -/
lemma moment_sq (i : Fin 3) :
    ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x i) ^ 2 = 4 * Real.pi / 15 := by
  have hsplit : ∫ x in Metric.ball (0 : Work.LWP.R3) 1, ‖x‖ ^ 2
      = (∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x 0) ^ 2)
        + (∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x 1) ^ 2)
        + (∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x 2) ^ 2) := by
    rw [show (fun x : Work.LWP.R3 => ‖x‖ ^ 2)
        = (fun x => (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2) from
          funext (fun x => by rw [norm_sq_eq_sum, Fin.sum_univ_three])]
    have ha : Integrable (fun x : Work.LWP.R3 => (x 0) ^ 2 + (x 1) ^ 2)
        (volume.restrict (Metric.ball (0 : Work.LWP.R3) 1)) :=
      (integrable_of_continuous_ball (by fun_prop)).add (integrable_of_continuous_ball (by fun_prop))
    rw [integral_add ha (integrable_of_continuous_ball (by fun_prop)),
        integral_add (integrable_of_continuous_ball (by fun_prop))
          (integrable_of_continuous_ball (by fun_prop))]
  rw [norm_sq_ball_integral] at hsplit
  rw [moment_sq_eq 0 i, moment_sq_eq 1 i, moment_sq_eq 2 i] at hsplit
  have h3 : (4 : ℝ) * Real.pi / 5 = 3 * (4 * Real.pi / 15) := by ring_nf
  linarith [hsplit, h3]

/-- All coordinate moments of the unit ball: `∫_B x_i x_j = (4π/15) δ_ij`. -/
lemma moment_ij (i j : Fin 3) :
    ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x i) * (x j)
      = (4 * Real.pi / 15) * (if i = j then 1 else 0) := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, mul_one]
    simpa [pow_two] using moment_sq i
  · rw [if_neg hij, mul_zero]
    exact moment_off i j hij

/-! ## The second moment of the ball and of the sphere -/

/-- Second moment of the unit ball: `∫_B ⟪x,h⟫⟪x,w⟫ = (4π/15) ⟪h,w⟫`. -/
lemma ball_moment (h w : Work.LWP.R3) :
    ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (inner ℝ x h) * (inner ℝ x w)
      = (4 * Real.pi / 15) * inner ℝ h w := by
  have hpoint : (fun x : Work.LWP.R3 => (inner ℝ x h) * (inner ℝ x w))
      = fun x => ∑ i : Fin 3, ∑ j : Fin 3, (h i * w j) * ((x i) * (x j)) := by
    funext x
    rw [inner_eq_sum x h, inner_eq_sum x w, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  rw [hpoint]
  have step1 : ∫ x in Metric.ball (0 : Work.LWP.R3) 1,
        (∑ i : Fin 3, ∑ j : Fin 3, (h i * w j) * ((x i) * (x j)))
      = ∑ i : Fin 3, ∫ x in Metric.ball (0 : Work.LWP.R3) 1,
          (∑ j : Fin 3, (h i * w j) * ((x i) * (x j))) :=
    integral_finset_sum (μ := volume.restrict (Metric.ball (0 : Work.LWP.R3) 1)) Finset.univ
      (f := fun i x => ∑ j : Fin 3, (h i * w j) * ((x i) * (x j)))
      (fun i _ => integrable_of_continuous_ball (by fun_prop))
  rw [step1]
  have step2 : ∀ i : Fin 3, ∫ x in Metric.ball (0 : Work.LWP.R3) 1,
        (∑ j : Fin 3, (h i * w j) * ((x i) * (x j)))
      = ∑ j : Fin 3, (h i * w j)
          * ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x i) * (x j) := by
    intro i
    rw [integral_finset_sum (μ := volume.restrict (Metric.ball (0 : Work.LWP.R3) 1)) Finset.univ
      (f := fun j x => (h i * w j) * ((x i) * (x j)))
      (fun j _ => integrable_of_continuous_ball (by fun_prop))]
    exact Finset.sum_congr rfl (fun j _ => integral_const_mul _ _)
  rw [Finset.sum_congr rfl (fun i _ => step2 i)]
  have step3 : ∑ i : Fin 3, ∑ j : Fin 3,
        (h i * w j) * ∫ x in Metric.ball (0 : Work.LWP.R3) 1, (x i) * (x j)
      = ∑ i : Fin 3, ∑ j : Fin 3,
          (h i * w j) * ((4 * Real.pi / 15) * (if i = j then 1 else 0)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [moment_ij]
  rw [step3]
  have hinner : ∀ i : Fin 3,
        ∑ j : Fin 3, (h i * w j) * ((4 * Real.pi / 15) * (if i = j then 1 else 0))
      = (4 * Real.pi / 15) * (h i * w i) := by
    intro i
    rw [Finset.sum_congr rfl (fun j _ => show
        (h i * w j) * ((4 * Real.pi / 15) * (if i = j then 1 else 0))
          = (4 * Real.pi / 15) * ((h i * w j) * (if i = j then 1 else 0)) by ring)]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_congr rfl (fun j _ => show (h i * w j) * (if i = j then 1 else 0)
        = if i = j then h i * w j else 0 by split <;> ring)]
    rw [Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  rw [← Finset.mul_sum, ← inner_eq_sum' h w]

/-- Second moment of the unit sphere: `∫_{S²} ⟪u,h⟫⟪u,w⟫ dσ = (4π/3) ⟪h,w⟫`. -/
lemma sphere_moment (h w : Work.LWP.R3) :
    ∫ u : Metric.sphere (0 : Work.LWP.R3) 1,
        (inner ℝ (u : Work.LWP.R3) h) * (inner ℝ (u : Work.LWP.R3) w)
        ∂(volume : Measure Work.LWP.R3).toSphere = (4 * Real.pi / 3) * inner ℝ h w := by
  rw [sphere_ball_polar h w, ball_moment h w]
  ring_nf

/-! ## The vector-valued second moment -/

theorem sphere_integral_inner_smul (z : Work.LWP.R3) :
    ∫ ω, inner ℝ z (ω : Work.LWP.R3) • (ω : Work.LWP.R3)
      ∂(MeasureTheory.Measure.toSphere (MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3))
      = (4 * Real.pi / 3) • z := by
  apply ext_inner_left ℝ
  intro w
  have hint : Integrable (fun ω : Metric.sphere (0 : Work.LWP.R3) 1 =>
      inner ℝ z (ω : Work.LWP.R3) • (ω : Work.LWP.R3))
      (MeasureTheory.Measure.toSphere (volume : Measure (Work.LWP.R3))) := by
    refine Integrable.of_bound ?_ ‖z‖ ?_
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with ω
      rw [norm_smul, mem_sphere_zero_iff_norm.mp ω.2, mul_one, Real.norm_eq_abs]
      simpa using abs_real_inner_le_norm z (ω : Work.LWP.R3)
  have hconv : (∫ u : Metric.sphere (0 : Work.LWP.R3) 1,
        (inner ℝ z (u : Work.LWP.R3)) * (inner ℝ w (u : Work.LWP.R3))
        ∂(volume : Measure Work.LWP.R3).toSphere) = (4 * Real.pi / 3) * inner ℝ z w := by
    rw [show (∫ u : Metric.sphere (0 : Work.LWP.R3) 1,
          (inner ℝ z (u : Work.LWP.R3)) * (inner ℝ w (u : Work.LWP.R3))
          ∂(volume : Measure Work.LWP.R3).toSphere)
        = (∫ u : Metric.sphere (0 : Work.LWP.R3) 1,
          (inner ℝ (u : Work.LWP.R3) z) * (inner ℝ (u : Work.LWP.R3) w)
          ∂(volume : Measure Work.LWP.R3).toSphere) from by
          apply integral_congr_ae; filter_upwards with u
          rw [real_inner_comm (u : Work.LWP.R3) z, real_inner_comm (u : Work.LWP.R3) w]]
    exact sphere_moment z w
  rw [← innerSL_apply_apply ℝ w, ← ContinuousLinearMap.integral_comp_comm (innerSL ℝ w) hint]
  simp only [innerSL_apply_apply, real_inner_smul_right]
  rw [hconv, real_inner_comm z w]

end

end Work.CoreResiduals.BiotSavart.KfBall
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.gain_step =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FourierTransform TemperedDistribution MeasureTheory Filter LineDeriv ENNReal
open scoped SchwartzMap BesselPotentialSpace ENNReal Topology LineDeriv

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.EllipticEst.InteriorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## Young's inequality in `eLpNorm` form

The form of Young's convolution inequality `L¹ ∗ L² → L²` needed for the Fourier-side estimate:
a function `f` that is pointwise dominated (in `enorm`) by the `ℝ≥0∞`-integral of
`F (x - y) * u y`, with `F ∈ L¹` nonnegative and `u ∈ L²` nonnegative, has
`eLpNorm f 2 ≤ (∫ F) · eLpNorm u 2`.

The proof is that of `young_l1_l2` (same directory) with the convolution replaced by an arbitrary
dominated function; it is the only ingredient of the Fourier estimate that is not covered by
`young_l1_l2`. -/

/-- Young's inequality in `eLpNorm` form, with a pointwise `enorm` domination hypothesis. -/
theorem gainStep_young_eLpNorm {F u : E → ℝ} {f : E → ℂ}
    (hF : ∀ x, 0 ≤ F x) (hu : ∀ x, 0 ≤ u x)
    (hFi : Integrable F (volume : Measure E)) (huM : MemLp u 2 (volume : Measure E))
    (hfm : AEStronglyMeasurable f (volume : Measure E))
    (hpt : ∀ x, ‖f x‖ₑ ≤ ∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) :
    eLpNorm f 2 (volume : Measure E)
      ≤ ENNReal.ofReal (∫ z, F z) * eLpNorm u 2 (volume : Measure E) := by
  have hFm : AEMeasurable F (volume : Measure E) := hFi.aemeasurable
  have hum : AEMeasurable u (volume : Measure E) := huM.aemeasurable
  have hAeq : ENNReal.ofReal (∫ z, F z) = ∫⁻ z, ENNReal.ofReal (F z) :=
    ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ hF)
  have hAlt : (∫⁻ z, ENNReal.ofReal (F z)) ≠ ∞ := by
    rw [← hAeq]; exact ENNReal.ofReal_ne_top
  -- Cauchy–Schwarz in `y` with weight `√(F (x - y))`, for each `x`
  have hcs : ∀ x : E, (∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) ^ (2:ℝ)
      ≤ (∫⁻ y, ENNReal.ofReal (F (x - y)))
        * (∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2)) := by
    intro x
    have hFmeas : AEMeasurable (fun y : E => F (x - y)) (volume : Measure E) :=
      hFm.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
    set phi : E → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.sqrt (F (x - y))) with hphidef
    set psi : E → ℝ≥0∞ := fun y => phi y * ENNReal.ofReal (u y) with hsidef
    have hphim : AEMeasurable phi (volume : Measure E) := by
      rw [hphidef]
      exact ((ENNReal.measurable_ofReal.comp Real.continuous_sqrt.measurable).comp_aemeasurable
        hFmeas)
    have humeas : AEMeasurable (fun y : E => ENNReal.ofReal (u y)) (volume : Measure E) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hum
    have hpsim : AEMeasurable psi (volume : Measure E) := by
      rw [hsidef]; exact hphim.mul humeas
    have hphiphi : ∀ y, phi y * phi y = ENNReal.ofReal (F (x - y)) := by
      intro y
      rw [hphidef]; simp only
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.mul_self_sqrt (hF _)]
    have hpsipsi : ∀ y, psi y * psi y = ENNReal.ofReal (F (x - y) * u y ^ 2) := by
      intro y
      have h1 : psi y = phi y * ENNReal.ofReal (u y) := rfl
      calc psi y * psi y
          = (phi y * phi y) * (ENNReal.ofReal (u y) * ENNReal.ofReal (u y)) := by
            rw [h1]; ring
        _ = ENNReal.ofReal (F (x - y)) * (ENNReal.ofReal (u y) * ENNReal.ofReal (u y)) := by
            rw [hphiphi y]
        _ = ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2) := by
            rw [← pow_two, ← ENNReal.ofReal_pow (hu y) 2]
        _ = ENNReal.ofReal (F (x - y) * u y ^ 2) := by rw [← ENNReal.ofReal_mul (hF _)]
    have hphis : ∀ y, phi y * psi y = ENNReal.ofReal (F (x - y) * u y) := by
      intro y
      have h1 : psi y = phi y * ENNReal.ofReal (u y) := rfl
      calc phi y * psi y = (phi y * phi y) * ENNReal.ofReal (u y) := by rw [h1]; ring
        _ = ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y) := by rw [hphiphi y]
        _ = ENNReal.ofReal (F (x - y) * u y) := by rw [← ENNReal.ofReal_mul (hF _)]
    have hHold := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure E) (p := 2) (q := 2)
      (⟨by norm_num, by norm_num, by norm_num⟩ : (2:ℝ).HolderConjugate 2) hphim hpsim
    have hH : (∫⁻ y, ENNReal.ofReal (F (x - y) * u y))
        ≤ (∫⁻ y, ENNReal.ofReal (F (x - y))) ^ ((1:ℝ)/2)
          * (∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2)) ^ ((1:ℝ)/2) := by
      have h1 : (∫⁻ y, phi y * psi y) = ∫⁻ y, ENNReal.ofReal (F (x - y) * u y) :=
        lintegral_congr (fun y => hphis y)
      have h2 : (∫⁻ y, phi y ^ (2:ℝ)) = ∫⁻ y, ENNReal.ofReal (F (x - y)) :=
        lintegral_congr (fun y => by rw [ENNReal.rpow_two, pow_two, hphiphi y])
      have h3 : (∫⁻ y, psi y ^ (2:ℝ)) = ∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2) :=
        lintegral_congr (fun y => by rw [ENNReal.rpow_two, pow_two, hpsipsi y])
      rw [show (∫⁻ a : E, (phi * psi) a) = ∫⁻ y, phi y * psi y from rfl, h1, h2, h3] at hHold
      exact hHold
    have hH2 := ENNReal.rpow_le_rpow hH (by norm_num : (0:ℝ) ≤ 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)] at hH2
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hH2
    norm_num at hH2
    simpa using hH2
  -- translation invariance in `x`
  have htrans : ∀ x : E, (∫⁻ y, ENNReal.ofReal (F (x - y))) = ∫⁻ z, ENNReal.ofReal (F z) := by
    intro x
    exact lintegral_sub_left_eq_self (μ := (volume : Measure E))
      (fun z : E => ENNReal.ofReal (F z)) x
  -- Tonelli + translation invariance, computing the double integral of the `u ^ 2`-term
  have hK : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2))
      = (∫⁻ z, ENNReal.ofReal (F z)) * (∫⁻ y, ENNReal.ofReal (u y ^ 2)) := by
    have hFm' : AEMeasurable (fun z : E => ENNReal.ofReal (F z)) (volume : Measure E) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hFm
    have hMm : AEMeasurable (fun y : E => ENNReal.ofReal (u y ^ 2)) (volume : Measure E) :=
      ENNReal.measurable_ofReal.comp_aemeasurable (hum.pow_const 2)
    have h1 : AEMeasurable (fun w : E × E => ENNReal.ofReal (F w.1))
        ((volume : Measure E).prod volume) := hFm'.comp_fst
    have h2 : AEMeasurable (fun w : E × E => ENNReal.ofReal (u w.2 ^ 2))
        ((volume : Measure E).prod volume) := hMm.comp_snd
    have h3 : AEMeasurable
        (fun w : E × E => ENNReal.ofReal (F w.1) * ENNReal.ofReal (u w.2 ^ 2))
        ((volume : Measure E).prod volume) := h1.mul h2
    -- the shear `(x,y) ↦ (x-y,y)` is measure preserving, which gives the joint measurability
    have hS : Measure.QuasiMeasurePreserving (fun z : E × E => (z.1 - z.2, z.2))
        ((volume : Measure E).prod volume) ((volume : Measure E).prod volume) :=
      (measurePreserving_sub_prod (volume : Measure E) volume).quasiMeasurePreserving
    have hjoint : AEMeasurable
        (fun p : E × E => ENNReal.ofReal (F (p.1 - p.2)) * ENNReal.ofReal (u p.2 ^ 2))
        ((volume : Measure E).prod volume) := by
      have hcomp : (fun p : E × E =>
            ENNReal.ofReal (F (p.1 - p.2)) * ENNReal.ofReal (u p.2 ^ 2))
          = (fun w : E × E => ENNReal.ofReal (F w.1) * ENNReal.ofReal (u w.2 ^ 2))
            ∘ (fun z : E × E => (z.1 - z.2, z.2)) := by
        funext p; simp
      rw [hcomp]; exact h3.comp_quasiMeasurePreserving hS
    rw [show (∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2))
        = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2) from
          lintegral_congr (fun x => lintegral_congr (fun y => ENNReal.ofReal_mul (hF _)))]
    have hjoint' : AEMeasurable (Function.uncurry fun x y : E =>
        ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2))
        ((volume : Measure E).prod volume) := hjoint
    rw [lintegral_lintegral_swap (μ := (volume : Measure E)) (ν := (volume : Measure E))
      (f := fun x y : E => ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2)) hjoint']
    have hinner : ∀ y : E, (∫⁻ x, ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2))
        = (∫⁻ z, ENNReal.ofReal (F z)) * ENNReal.ofReal (u y ^ 2) := by
      intro y
      calc (∫⁻ x, ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2))
          = ∫⁻ x, (fun z => ENNReal.ofReal (F z) * ENNReal.ofReal (u y ^ 2)) (x - y) := rfl
        _ = ∫⁻ x, ENNReal.ofReal (F x) * ENNReal.ofReal (u y ^ 2) :=
              lintegral_sub_right_eq_self (μ := (volume : Measure E))
                (fun z : E => ENNReal.ofReal (F z) * ENNReal.ofReal (u y ^ 2)) y
        _ = (∫⁻ z, ENNReal.ofReal (F z)) * ENNReal.ofReal (u y ^ 2) :=
              lintegral_mul_const'' _ hFm'
    rw [show (∫⁻ y, ∫⁻ x, ENNReal.ofReal (F (x - y)) * ENNReal.ofReal (u y ^ 2))
        = ∫⁻ y, (∫⁻ z, ENNReal.ofReal (F z)) * ENNReal.ofReal (u y ^ 2) from
          lintegral_congr hinner]
    exact lintegral_const_mul'' _ hMm
  -- the `L²` (squared) mass of `f`
  have hkey : (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ))
      ≤ (∫⁻ z, ENNReal.ofReal (F z))
        * ((∫⁻ z, ENNReal.ofReal (F z)) * ∫⁻ y, ENNReal.ofReal (u y ^ 2)) := by
    calc (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ))
        ≤ ∫⁻ x, (∫⁻ y, ENNReal.ofReal (F (x - y) * u y)) ^ (2:ℝ) :=
          lintegral_mono (fun x => ENNReal.rpow_le_rpow (hpt x) (by norm_num))
      _ ≤ ∫⁻ x, (∫⁻ y, ENNReal.ofReal (F (x - y)))
            * (∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2)) :=
          lintegral_mono (fun x => hcs x)
      _ = ∫⁻ x, (∫⁻ z, ENNReal.ofReal (F z))
            * (∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2)) := by
          refine lintegral_congr (fun x => ?_)
          rw [htrans x]
      _ = (∫⁻ z, ENNReal.ofReal (F z)) * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (F (x - y) * u y ^ 2) :=
          lintegral_const_mul' _ _ hAlt
      _ = (∫⁻ z, ENNReal.ofReal (F z))
            * ((∫⁻ z, ENNReal.ofReal (F z)) * ∫⁻ y, ENNReal.ofReal (u y ^ 2)) := by
          rw [hK]
  have hfnorm : eLpNorm f (2:ℝ≥0∞) (volume : Measure E)
      = (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
    rw [eLpNorm_eq_eLpNorm' (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num) hfm,
      eLpNorm'_eq_lintegral_enorm]
    norm_num
  have hunorm : eLpNorm u (2:ℝ≥0∞) (volume : Measure E)
      = (∫⁻ y, ENNReal.ofReal (u y ^ 2)) ^ ((1:ℝ)/2) := by
    rw [eLpNorm_eq_eLpNorm' (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num)
        huM.aestronglyMeasurable,
      eLpNorm'_eq_lintegral_enorm]
    norm_num
    congr 1
    refine lintegral_congr (fun y => ?_)
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hu y)]
    exact (ENNReal.ofReal_pow (hu y) 2).symm
  rw [hfnorm, hAeq, hunorm]
  calc (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)
      ≤ ((∫⁻ z, ENNReal.ofReal (F z))
          * ((∫⁻ z, ENNReal.ofReal (F z)) * ∫⁻ y, ENNReal.ofReal (u y ^ 2))) ^ ((1:ℝ)/2) :=
        ENNReal.rpow_le_rpow hkey (by norm_num)
    _ = (∫⁻ z, ENNReal.ofReal (F z)) * (∫⁻ y, ENNReal.ofReal (u y ^ 2)) ^ ((1:ℝ)/2) := by
        rw [← mul_assoc, ← pow_two, ← ENNReal.rpow_natCast,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (1:ℝ)/2),
          ← ENNReal.rpow_mul]
        norm_num

/-! ## The analytic estimate: `Λ^s ∘ M_γ ∘ Λ^{-s}` is bounded on `L²`

This is the missing estimate in the classical proof that multiplication by a compactly supported
smooth function preserves `H^s = MemSobolev s 2` (Mathlib has no product machinery for Sobolev
spaces). -/

/-- **The key estimate.**  The Schwartz-level operator `Λ^s ∘ M_γ ∘ Λ^{-s}` is bounded for the
`L²` norm, with the constant `∫ ξ, ‖2^{|s|/2} ⟨ξ⟩^{|s|} 𝓕γ(ξ)‖`. -/
theorem gainStep_phiEstimate (s : ℝ) (γS k : 𝓢(E, ℂ)) :
    ‖(mms_Phi s γS k).toLp 2 (volume : Measure E)‖
      ≤ (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
            (mms_wfun (E := E) |s| ξ * (𝓕 γS) ξ)‖) *
          ‖k.toLp 2 (volume : Measure E)‖ := by
  have hFnn : ∀ z : E, 0 ≤ ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| z * FourierTransform.fourier γS z)‖ := fun _ => norm_nonneg _
  have hun : ∀ y : E, 0 ≤ ‖FourierTransform.fourier k y‖ := fun _ => norm_nonneg _
  have hFi : Integrable (fun z : E => ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| z * FourierTransform.fourier γS z)‖) (volume : Measure E) := by
    have hSint : Integrable (fun z : E =>
        ‖⇑(SchwartzMap.smulLeftCLM ℂ (mms_wfun (E := E) |s|)
          (FourierTransform.fourier γS : 𝓢(E, ℂ))) z‖) (volume : Measure E) :=
      (SchwartzMap.integrable _).norm
    refine (hSint.mul_const (2 ^ (|s| / 2))).congr (Eventually.of_forall fun z => ?_)
    dsimp only
    rw [SchwartzMap.smulLeftCLM_apply_apply (mms_wfun_temperate (E := E) |s|), smul_eq_mul,
      norm_mul, norm_mul, norm_mul, norm_ofReal_complex,
      abs_of_nonneg (Real.rpow_nonneg (by norm_num) (|s| / 2))]
    ring
  have huM : MemLp (fun y : E => ‖FourierTransform.fourier k y‖) 2 (volume : Measure E) :=
    (SchwartzMap.memLp (FourierTransform.fourier k) 2 (volume : Measure E)).norm
  have hfm : AEStronglyMeasurable
      (⇑(FourierTransform.fourier (mms_Phi s γS k))) (volume : Measure E) :=
    (SchwartzMap.memLp (FourierTransform.fourier (mms_Phi s γS k)) 2
      (volume : Measure E)).aestronglyMeasurable
  have hpt : ∀ ξ : E, ‖(⇑(FourierTransform.fourier (mms_Phi s γS k))) ξ‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal ((‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
          (mms_wfun (E := E) |s| (ξ - y) * FourierTransform.fourier γS (ξ - y))‖) *
          ‖FourierTransform.fourier k y‖) ∂(volume : Measure E) :=
    fun ξ => mms_Phi_enorm_le s γS k ξ
  have hmain := gainStep_young_eLpNorm
    (F := fun z : E => ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| z * FourierTransform.fourier γS z)‖)
    (u := fun y : E => ‖FourierTransform.fourier k y‖)
    (f := ⇑(FourierTransform.fourier (mms_Phi s γS k))) hFnn hun hFi huM hfm hpt
  have hPhi : ‖(mms_Phi s γS k).toLp 2 (volume : Measure E)‖
      = (eLpNorm (⇑(FourierTransform.fourier (mms_Phi s γS k))) 2
          (volume : Measure E)).toReal := by
    have h1 : ‖(mms_Phi s γS k).toLp 2 (volume : Measure E)‖
        = ‖(FourierTransform.fourier (mms_Phi s γS k)).toLp 2 (volume : Measure E)‖ := by
      rw [← MeasureTheory.Lp.norm_fourier_eq ((mms_Phi s γS k).toLp 2 (volume : Measure E)),
        SchwartzMap.toLp_fourier_eq]
    rw [h1, SchwartzMap.norm_toLp]
  have hk : ‖k.toLp 2 (volume : Measure E)‖
      = (eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E)).toReal := by
    have h1 : ‖k.toLp 2 (volume : Measure E)‖
        = ‖(FourierTransform.fourier k).toLp 2 (volume : Measure E)‖ := by
      rw [← MeasureTheory.Lp.norm_fourier_eq (k.toLp 2 (volume : Measure E)),
        SchwartzMap.toLp_fourier_eq]
    rw [h1, SchwartzMap.norm_toLp]
  have hnormu : eLpNorm (fun y : E => ‖FourierTransform.fourier k y‖) 2 (volume : Measure E)
      = eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E) :=
    eLpNorm_norm _ (SchwartzMap.memLp (FourierTransform.fourier k) 2
      (volume : Measure E)).aestronglyMeasurable
  have hne : ENNReal.ofReal (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
        (mms_wfun (E := E) |s| ξ * FourierTransform.fourier γS ξ)‖)
        * eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt (SchwartzMap.memLp
      (FourierTransform.fourier k) 2 (volume : Measure E)).eLpNorm_lt_top)
  rw [hPhi, hk]
  calc (eLpNorm (⇑(FourierTransform.fourier (mms_Phi s γS k))) 2
          (volume : Measure E)).toReal
      ≤ (ENNReal.ofReal (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
            (mms_wfun (E := E) |s| ξ * FourierTransform.fourier γS ξ)‖)
          * eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E)).toReal :=
        ENNReal.toReal_mono hne (by rw [← hnormu]; exact hmain)
    _ = (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
            (mms_wfun (E := E) |s| ξ * FourierTransform.fourier γS ξ)‖)
          * (eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]

/-! ## Extension from Schwartz functions to `L²`

If `Λ^s u = U ∈ L²` then `Λ^s(γu) ∈ L²`, i.e. `γu ∈ H^s`: approximate `U` in `L²` by Schwartz
functions; the images under `Λ^s ∘ M_γ ∘ Λ^{-s}` form a Cauchy sequence in `L²` by the estimate,
and the limit agrees with `Λ^s(γu)` because that operator is continuous on `𝓢'`.
-/

theorem gainStep_main {s : ℝ} (γS : 𝓢(E, ℂ)) (u : 𝓢'(E, ℂ)) (U : Lp ℂ 2 (volume : Measure E))
    (hU : besselPotential E ℂ s u = (U : 𝓢'(E, ℂ))) :
    MemSobolev s 2 (smulLeftCLM ℂ (⇑γS) u) := by
  set C : ℝ := ∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| ξ * (𝓕 γS) ξ)‖ with hCdef
  have hC_nonneg : 0 ≤ C := by
    rw [hCdef]
    exact integral_nonneg fun ξ => norm_nonneg _
  have hu_eq : u = besselPotential E ℂ (-s) (U : 𝓢'(E, ℂ)) := by
    rw [← mms_bessel_neg_bessel s u, hU]
  -- the embedding of Schwartz functions into `L²`
  let e : 𝓢(E, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure E) := SchwartzMap.toLpCLM ℂ ℂ 2 volume
  have hdense : DenseRange e := by
    show DenseRange fun f : 𝓢(E, ℂ) => f.toLp 2 (volume : Measure E)
    have h := SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := E) (p := 2)
      (μ := (volume : Measure E)) (by norm_num)
    have hfe : (fun f : 𝓢(E, ℂ) => f.toLp 2 (volume : Measure E)) =
        ⇑(SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure E)) := by
      funext f
      rw [SchwartzMap.toLpCLM_apply]
    rw [hfe]
    exact h
  have hseq : ∀ n : ℕ, ∃ k : 𝓢(E, ℂ), dist U (e k) < 1 / ((n : ℝ) + 1) := by
    intro n
    exact (Metric.denseRange_iff.mp hdense) U _ (by positivity)
  choose f hf using hseq
  have hnorm : ∀ n : ℕ, ‖U - e (f n)‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have h := hf n
    rw [dist_eq_norm] at h
    exact le_of_lt h
  have hzero : Tendsto (fun n : ℕ => U - e (f n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have hh := Nat.add_le_add_right hn 1
      exact_mod_cast hh
    have h2 : 1 / ((N : ℝ) + 1) < ε := by
      have h3 : (1 : ℝ) < ((N : ℝ) + 1) * ε := by
        have hN' : (1 : ℝ) / ε < (N : ℝ) + 1 := by
          have : (N : ℝ) < (N : ℝ) + 1 := by linarith
          linarith
        exact (div_lt_iff₀ hε).mp hN'
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      nlinarith [h3]
    calc dist (U - e (f n)) 0 = ‖U - e (f n)‖ := by rw [dist_zero_right]
      _ ≤ 1 / ((n : ℝ) + 1) := hnorm n
      _ ≤ 1 / ((N : ℝ) + 1) := h1
      _ < ε := h2
  have hftend : Tendsto (fun n : ℕ => e (f n)) atTop (𝓝 U) := by
    have h1 : Tendsto (fun n : ℕ => U - (U - e (f n))) atTop (𝓝 (U - 0)) := hzero.const_sub U
    simpa using h1
  -- the images in `L²`
  let v : ℕ → Lp ℂ 2 (volume : Measure E) := fun n => (mms_Phi s γS (f n)).toLp 2 volume
  have hv_lip : ∀ m n : ℕ, dist (v m) (v n) ≤ C * dist (e (f m)) (e (f n)) := by
    intro m n
    have hL : mms_Phi s γS (f m) - mms_Phi s γS (f n) = mms_Phi s γS (f m - f n) := by
      simp only [mms_Phi, map_sub]
    have hA' : v m - v n = (mms_Phi s γS (f m - f n)).toLp 2 (volume : Measure E) := by
      rw [show v m = (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)) (mms_Phi s γS (f m))
            from rfl,
        show v n = (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)) (mms_Phi s γS (f n))
            from rfl,
        ← map_sub (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)), hL]
      rfl
    have hB' : e (f m) - e (f n) = (f m - f n).toLp 2 (volume : Measure E) := by
      show e (f m) - e (f n) = _
      rw [← map_sub e]
      rfl
    rw [dist_eq_norm, dist_eq_norm, hA', hB', hCdef]
    exact gainStep_phiEstimate s γS (f m - f n)
  have hv_cauchy : CauchySeq v := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hce : CauchySeq fun n : ℕ => e (f n) := hftend.cauchySeq
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hce) (ε / (C + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hC1 : 0 < C + 1 := by linarith
    have h1 := hv_lip m n
    have h2 := hN m hm n hn
    have h3 : C * dist (e (f m)) (e (f n)) ≤ (C + 1) * dist (e (f m)) (e (f n)) := by
      have hd : 0 ≤ dist (e (f m)) (e (f n)) := dist_nonneg
      nlinarith
    have h4 : (C + 1) * dist (e (f m)) (e (f n)) < (C + 1) * (ε / (C + 1)) :=
      mul_lt_mul_of_pos_left h2 hC1
    have h5 : (C + 1) * (ε / (C + 1)) = ε := by
      field_simp
    linarith [h1, h3, h4, h5.le, h5.ge]
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete hv_cauchy
  -- the limiting distribution: apply the (continuous) operator to the `L²` limit
  let A : Lp ℂ 2 (volume : Measure E) →L[ℂ] 𝓢'(E, ℂ) :=
    (besselPotential E ℂ s).comp ((smulLeftCLM ℂ (⇑γS)).comp
      ((besselPotential E ℂ (-s)).comp (Lp.toTemperedDistributionCLM (F := ℂ) (μ := volume) 2)))
  have hAapply : ∀ W : Lp ℂ 2 (volume : Measure E), A W = besselPotential E ℂ s
      (smulLeftCLM ℂ (⇑γS) (besselPotential E ℂ (-s) (W : 𝓢'(E, ℂ)))) := by
    intro W
    rfl
  have hA : ∀ n : ℕ, A (e (f n)) = (v n : 𝓢'(E, ℂ)) := by
    intro n
    rw [hAapply]
    have h1 : ((e (f n) : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) = (f n : 𝓢'(E, ℂ)) :=
      Lp.toTemperedDistribution_toLp_eq (f n)
    rw [h1, ← mms_Phi_toTempered s γS (f n)]
    exact (Lp.toTemperedDistribution_toLp_eq (mms_Phi s γS (f n))).symm
  have hAU : A U = besselPotential E ℂ s (smulLeftCLM ℂ (⇑γS) u) := by
    rw [hAapply, ← hU, mms_bessel_neg_bessel]
  have h1 : Tendsto (fun n : ℕ => (v n : 𝓢'(E, ℂ))) atTop
      (𝓝 (besselPotential E ℂ s (smulLeftCLM ℂ (⇑γS) u))) := by
    have hcomp : Tendsto (fun n : ℕ => A (e (f n))) atTop (𝓝 (A U)) :=
      (A.continuous.tendsto U).comp hftend
    rw [← hAU]
    simpa only [hA] using hcomp
  have h2 : Tendsto (fun n : ℕ => (v n : 𝓢'(E, ℂ))) atTop (𝓝 (V : 𝓢'(E, ℂ))) :=
    ((Lp.toTemperedDistributionCLM (F := ℂ) (μ := volume) 2).continuous.tendsto V).comp hV
  exact ⟨V, tendsto_nhds_unique h1 h2⟩

/-! ## Multiplication preserves `H^s` -/

/-- Multiplication by a compactly supported `C^∞` function preserves every Bessel potential
space `H^s = MemSobolev s 2`, `s ∈ ℝ`. -/
theorem gainStep_smul_memSobolev {s : ℝ} {γ : E → ℂ} (hγc : HasCompactSupport γ)
    (hγs : ∀ n : ℕ, ContDiff ℝ n γ) {u : 𝓢'(E, ℂ)} (hu : MemSobolev s 2 u) :
    MemSobolev s 2 (smulLeftCLM ℂ γ u) := by
  have hγS_smooth : ContDiff ℝ (⊤ : ℕ∞) γ := contDiff_infty.mpr hγs
  let γS : 𝓢(E, ℂ) := hγc.toSchwartzMap hγS_smooth
  obtain ⟨U, hU⟩ := hu
  exact gainStep_main γS u U hU

/-! ## The gain step -/

theorem gain_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {σ : ℝ} {u G : 𝓢'(E, ℂ)} {b b' c : E → ℂ} (e e' : E)
    (hb : HasCompactSupport b) (hbs : ∀ n : ℕ, ContDiff ℝ n b)
    (hb' : HasCompactSupport b') (hb's : ∀ n : ℕ, ContDiff ℝ n b')
    (hc : HasCompactSupport c) (hcs : ∀ n : ℕ, ContDiff ℝ n c)
    (hG : TemperedDistribution.MemSobolev σ 2 G)
    (hu : TemperedDistribution.MemSobolev σ 2 u)
    (heq : Laplacian.laplacian u
      = G + TemperedDistribution.smulLeftCLM ℂ b (LineDeriv.lineDerivOp e u)
        + TemperedDistribution.smulLeftCLM ℂ b' (LineDeriv.lineDerivOp e' u)
        + TemperedDistribution.smulLeftCLM ℂ c u) :
    TemperedDistribution.MemSobolev (σ+2) 2 u := by
  -- ## Round 1: the right-hand side lies in `H^{σ-1}`
  have hde : MemSobolev (σ - 1) 2 (LineDeriv.lineDerivOp e u) :=
    MemSobolev.lineDerivOp (m := e) hu
  have hde' : MemSobolev (σ - 1) 2 (LineDeriv.lineDerivOp e' u) :=
    MemSobolev.lineDerivOp (m := e') hu
  have hb1 : MemSobolev (σ - 1) 2 (smulLeftCLM ℂ b (LineDeriv.lineDerivOp e u)) :=
    gainStep_smul_memSobolev hb hbs hde
  have hb1' : MemSobolev (σ - 1) 2 (smulLeftCLM ℂ b' (LineDeriv.lineDerivOp e' u)) :=
    gainStep_smul_memSobolev hb' hb's hde'
  have hu1 : MemSobolev (σ - 1) 2 u := hu.mono (by linarith)
  have hc1 : MemSobolev (σ - 1) 2 (smulLeftCLM ℂ c u) := gainStep_smul_memSobolev hc hcs hu1
  have hG1 : MemSobolev (σ - 1) 2 G := hG.mono (by linarith)
  have hΔ1 : MemSobolev (σ - 1) 2 (Laplacian.laplacian u) := by
    rw [heq]
    exact ((hG1.add hb1).add hb1').add hc1
  have hu2 : MemSobolev (σ + 1) 2 u :=
    (gain_two (σ - 1) u hu1 hΔ1).mono (by linarith)
  -- ## Round 2: the right-hand side lies in `H^σ`
  have hde2 : MemSobolev σ 2 (LineDeriv.lineDerivOp e u) :=
    (MemSobolev.lineDerivOp (m := e) hu2).mono (by linarith)
  have hde2' : MemSobolev σ 2 (LineDeriv.lineDerivOp e' u) :=
    (MemSobolev.lineDerivOp (m := e') hu2).mono (by linarith)
  have hb2 : MemSobolev σ 2 (smulLeftCLM ℂ b (LineDeriv.lineDerivOp e u)) :=
    gainStep_smul_memSobolev hb hbs hde2
  have hb2' : MemSobolev σ 2 (smulLeftCLM ℂ b' (LineDeriv.lineDerivOp e' u)) :=
    gainStep_smul_memSobolev hb' hb's hde2'
  have hc2 : MemSobolev σ 2 (smulLeftCLM ℂ c u) := gainStep_smul_memSobolev hc hcs hu
  have hΔ2 : MemSobolev σ 2 (Laplacian.laplacian u) := by
    rw [heq]
    exact ((hG.add hb2).add hb2').add hc2
  exact gain_two σ u hu hΔ2

end Work.EllipticEst.InteriorRegularity
end
end
-- ===== merged: Submission.Work.FTS.BSSwirl.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

/-- `ℝ³`, the Euclidean space with the standard basis indexed by `Fin 3`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

noncomputable section

/-! ## The swirl field -/

/-- **The swirl (purely azimuthal) vector field** `ω x = f (r x) (z x) • e_θ(x)`, where `r` is the
distance to the `x₃`-axis (`Work.Cyl.radial`) and `z` the axial coordinate (`Work.Cyl.axial`).
`Work.Cyl.eTheta` vanishes on the axis, so `swirlField f` vanishes on the axis for every `f`; in
particular no regularity of `f` at `r = 0` is needed. -/
def swirlField (f : ℝ → ℝ → ℝ) (x : R3) : R3 :=
  f (Work.Cyl.radial x) (Work.Cyl.axial x) • Work.Cyl.eTheta x

@[simp] theorem swirlField_apply (f : ℝ → ℝ → ℝ) (x : R3) :
    swirlField f x = f (Work.Cyl.radial x) (Work.Cyl.axial x) • Work.Cyl.eTheta x := rfl



/-- The angular unit vector has norm at most one (it vanishes on the axis). -/
theorem norm_eTheta_le_one (x : R3) : ‖Work.Cyl.eTheta x‖ ≤ 1 := by
  rw [Work.Cyl.eTheta]
  by_cases hr : Work.Cyl.radial x = 0
  · rw [hr, one_div, _root_.inv_zero, zero_smul, norm_zero]
    norm_num
  · have hpos : 0 < 1 / Work.Cyl.radial x :=
      one_div_pos.mpr (lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hr))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos, Work.Cyl.norm_angularVec x,
      div_mul_cancel₀ _ hr]



/-! ## The Newtonian potential and the weak divergence-free condition -/

/-- **The vector Newtonian potential** `A ω x = (4π)⁻¹ ∫ ‖x-y‖⁻¹ • ω y dy`.  Its curl is the
Biot–Savart field `Work.LWP.biotSavart ω` (`biotSavart_eq_vorticity_newtonPotential`), so that the
Biot–Savart law becomes the classical pair of identities `ΔA = -ω` and `∇·A = 0` for the
potential. -/
def newtonPotential (ω : R3 → R3) (x : R3) : R3 :=
  (4 * Real.pi)⁻¹ • ∫ y, (‖x - y‖)⁻¹ • ω y


@[simp] theorem newtonPotential_apply (ω : R3 → R3) (x : R3) :
    newtonPotential ω x = (4 * Real.pi)⁻¹ • ∫ y, (‖x - y‖)⁻¹ • ω y := rfl

/-- **The candidate Fréchet derivative of the Newtonian potential**, namely

  `h ↦ (4π)⁻¹ ∫ ‖x-y‖⁻³ • (⟪y-x,h⟫ • ω y) dy`.

It is the derivative of `newtonPotential ω` wherever `ω` is bounded and compactly supported
(`Work.FTS.BSSwirl.hasFDerivAt_newtonPotential`). -/
def potDeriv (ω : R3 → R3) (x : R3) : R3 →L[ℝ] R3 :=
  (4 * Real.pi)⁻¹ • ∫ y, (‖x - y‖ ^ (3 : ℕ))⁻¹ •
    (innerSL ℝ (y - x)).smulRight (ω y)

/-- **Weak (distributional) divergence-free condition.**  `ω` has zero distributional divergence:
`∫ ⟪ω x, ∇k x⟫ dx = 0` for every smooth compactly supported scalar test function `k`.  This is the
exact form of `div ω = 0` needed by the integration-by-parts proof of the curl half of the
Biot–Savart law.  For the physical application `ω` is a swirl field, for which it is proved in
`Work.FTS.BSSwirl.SwirlWeak`. -/
def WeakDivFree (ω : R3 → R3) : Prop :=
  ∀ k : R3 → ℝ, (∀ n : ℕ, ContDiff ℝ n k) → HasCompactSupport k →
    ∫ x, inner ℝ (ω x) (∇ k x) = 0

/-- The weak divergence-free condition, in the equivalent `fderiv` form. -/
theorem weakDivFree_iff (ω : R3 → R3) :
    WeakDivFree ω ↔ ∀ k : R3 → ℝ, (∀ n : ℕ, ContDiff ℝ n k) → HasCompactSupport k →
      ∫ x, (fderiv ℝ k x) (ω x) = 0 := by
  constructor
  · intro h k hk hsupp
    have h' := h k hk hsupp
    rw [← h']
    apply integral_congr_ae
    filter_upwards with x
    rw [inner_gradient_right]
    simp
  · intro h k hk hsupp
    have h' := h k hk hsupp
    rw [← h']
    apply integral_congr_ae
    filter_upwards with x
    rw [inner_gradient_right]
    simp

/-! ## The statement of item 7a -/

/-- **Item 7a of the lead's design (`FTS_PHYS_BRIDGE.md` §1).**  For every compactly supported
`α`-Hölder swirl vorticity `ω = f(r,z) • e_θ` with `0 < α < 1`, the Biot–Savart velocity inverts
the curl and is divergence-free everywhere:

  `∇ × (BS ω) = ω`   and   `div (BS ω) = 0`   on `ℝ³`.

The proof is `Work.FTS.BSSwirl.biotSavartSwirl`. -/
def BiotSavartSwirl : Prop :=
  ∀ (f : ℝ → ℝ → ℝ) (C α : ℝ≥0) (R : ℝ), 0 < (α : ℝ) → (α : ℝ) < 1 →
    let ω := swirlField f
    HolderWith C α ω → (∀ x, ω x ≠ 0 → ‖x‖ ≤ R) →
    (∀ x, vorticity (Work.LWP.biotSavart ω) x = ω x) ∧
      ∀ x, div (Work.LWP.biotSavart ω) x = 0

end

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.ClassC.eFam_deriv_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open scoped Real

/-- `eFam m = cos · (gC (2m+1) ∘ sin)` is `C^3`, being a product of `C^3` functions. -/
theorem contDiff_three_eFam (m : ℕ) : ContDiff ℝ 3 (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  have h1 : ContDiff ℝ 3 (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) :=
    Work.FTS.PhiStar.Gegenbauer.contDiff_gC _
  exact Real.contDiff_cos.mul (h1.comp Real.contDiff_sin)

theorem eFam_deriv_bound (m : ℕ) : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
    |deriv (Work.FTS.PhiStar.Gegenbauer.eFam m) θ| ≤ Q := by
  have hcont : Continuous (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) := by
    have h : ContDiffOn ℝ 2 (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) Set.univ :=
      (contDiff_three_eFam m).contDiffOn.deriv_of_isOpen isOpen_univ
        (by norm_num : ((2 : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((3 : ℕ∞) : WithTop ℕ∞))
    exact continuousOn_univ.mp h.continuousOn
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (Real.pi / 2))) hcont.continuousOn
  refine ⟨C, le_trans (norm_nonneg _) (hC 0 ⟨le_refl 0, by linarith [Real.pi_pos]⟩), ?_⟩
  intro θ hθ
  simpa [Real.norm_eq_abs] using hC θ hθ

end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassC.lintegral_psiSeries_le_of_trunc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real BigOperators ENNReal
open MeasureTheory Filter

namespace Work.FTS.ClassC

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The angular weight `sEta θ = sin(2θ)^{-η}` is measurable. -/
theorem lplst_sEta_measurable : Measurable Work.FTS.EllipticEst.sEta := by
  show Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _

/-- The `N`-th partial sum `psiTrunc α F N z ·` is continuous in `θ`, being a finite linear
combination of the (continuous) eigenfunctions `eFam m`. -/
theorem lplst_psiTrunc_continuous (α : ℝ) (F : ℝ → ℝ → ℝ) (N : ℕ) (z : ℝ) :
    Continuous (fun θ : ℝ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ) := by
  unfold Work.FTS.PhiStar.Series.psiTrunc
  refine continuous_finsetSum _ (fun m _ => ?_)
  exact continuous_const.mul (Work.FTS.PhiStar.Series.continuous_eFam m)

/-- The `θ`-integrand of the truncated energy is (a.e.) measurable in `θ`.  This is what lets
Fatou's lemma be applied in the angular variable, pointwise in `z`. -/
theorem lplst_theta_integrand_aemeasurable (α : ℝ) (F : ℝ → ℝ → ℝ) (N : ℕ) (z : ℝ) :
    AEMeasurable (fun θ : ℝ => ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have h1 : Measurable (fun θ : ℝ => (Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2) :=
    (lplst_psiTrunc_continuous α F N z).measurable.pow_const 2
  have h2 : Measurable (fun θ : ℝ => (Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
      * (Work.Spaces.w z) ^ 2) := h1.mul measurable_const
  have h3 : Measurable (fun θ : ℝ => (Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
      * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    h2.mul lplst_sEta_measurable
  exact h3.ennreal_ofReal.aemeasurable



end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.radGreen_deriv1_form =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

/-- The first derivative of `radGreen`, written with the named pieces of
`Work.FTS.EllExist.RadGreenDefs`: for `z > 0`,

  `z · ∂_z radGreen α m c z = rgK α m · (rgP α m · rgG2 α m c z - rgQ α m · rgG1 α m c z)`.

The explicit first derivative `rgiD1` of the sibling `radGreenI` (`PhiStar.Series`) is
`rgK α m · (-(rgQ α m) · z^{-(rgQ α m) - 1} · rgA z + rgP α m · z^{rgP α m - 1} · rgB z)`,
and multiplying by `z` combines the powers `z^{-(rgQ)-1}·z = z^{-(rgQ)}` and
`z^{rgP-1}·z = z^{rgP}` (`Real.rpow_add`), leaving exactly
`rgP · z^{rgP} rgB - rgQ · z^{-(rgQ)} rgA = rgP · rgG2 - rgQ · rgG1`. -/
theorem radGreen_deriv1_form {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z →
      z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
        = Work.FTS.EllExist.rgK α m
          * (Work.FTS.EllExist.rgP α m * Work.FTS.EllExist.rgG2 α m c z
            - Work.FTS.EllExist.rgQ α m * Work.FTS.EllExist.rgG1 α m c z) := by
  intro z hz
  -- `HasDerivAt` for `radGreen` (definitionally the same function as `radGreenI`).
  have hAt : HasDerivAt (Work.FTS.PhiStar.Radial.radGreen α m c)
      (Work.FTS.PhiStar.Series.rgiD1 α m c z) z :=
    Work.FTS.PhiStar.Series.hasDerivAt_radGreenI (α := α) (m := m) (c := c) hc h0 hinf z hz
  -- hence `deriv radGreen z = rgD1 α m c z`
  have hderiv : deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
      = Work.FTS.EllExist.rgD1 α m c z := by
    rw [hAt.deriv]
    simp only [Work.FTS.PhiStar.Series.rgiD1, Work.FTS.EllExist.rgD1,
      Work.FTS.PhiStar.Series.rgiK, Work.FTS.EllExist.rgK,
      Work.FTS.PhiStar.Series.rgiSn, Work.FTS.PhiStar.Series.rgiSp,
      Work.FTS.EllExist.rgQ, Work.FTS.EllExist.rgP,
      Work.FTS.PhiStar.Series.rgiA, Work.FTS.PhiStar.Series.rgiB,
      Work.FTS.EllExist.rgA, Work.FTS.EllExist.rgB,
      Work.FTS.PhiStar.Series.rgiF1, Work.FTS.PhiStar.Series.rgiF2,
      Work.FTS.EllExist.rgF1, Work.FTS.EllExist.rgF2, neg_div]
  rw [hderiv]
  simp only [Work.FTS.EllExist.rgD1, Work.FTS.EllExist.rgG1, Work.FTS.EllExist.rgG2]
  -- the two `rpow` combination identities
  have hz1 : z ^ (-(Work.FTS.EllExist.rgQ α m) - 1) * z = z ^ (-(Work.FTS.EllExist.rgQ α m)) := by
    rw [← Real.rpow_add_one (ne_of_gt hz) (-(Work.FTS.EllExist.rgQ α m) - 1),
      show -(Work.FTS.EllExist.rgQ α m) - 1 + 1
      = -(Work.FTS.EllExist.rgQ α m) from by ring]
  have hz2 : z ^ (Work.FTS.EllExist.rgP α m - 1) * z = z ^ (Work.FTS.EllExist.rgP α m) := by
    rw [← Real.rpow_add_one (ne_of_gt hz) (Work.FTS.EllExist.rgP α m - 1),
      show Work.FTS.EllExist.rgP α m - 1 + 1
      = Work.FTS.EllExist.rgP α m from by ring]
  rw [show z * (Work.FTS.EllExist.rgK α m
        * (-(Work.FTS.EllExist.rgQ α m) * z ^ (-(Work.FTS.EllExist.rgQ α m) - 1)
              * Work.FTS.EllExist.rgA α m c z
          + Work.FTS.EllExist.rgP α m * z ^ (Work.FTS.EllExist.rgP α m - 1)
              * Work.FTS.EllExist.rgB α m c z))
      = Work.FTS.EllExist.rgK α m
        * (-(Work.FTS.EllExist.rgQ α m) * (z ^ (-(Work.FTS.EllExist.rgQ α m) - 1) * z)
              * Work.FTS.EllExist.rgA α m c z
          + Work.FTS.EllExist.rgP α m * (z ^ (Work.FTS.EllExist.rgP α m - 1) * z)
              * Work.FTS.EllExist.rgB α m c z) from by ring]
  rw [hz1, hz2]
  ring

end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassC.radGreen_smooth_of_contDiffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open MeasureTheory Set Filter


/-- The power function `z ↦ z ^ p` is `C^n` on `(0,∞)` for every real exponent `p`. -/
theorem contDiffOn_rpow_Ioi (p : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun z : ℝ => z ^ p) (Set.Ioi 0) :=
  (isOpen_Ioi.contDiffOn_iff).mpr (by
    intro a ha
    exact Real.contDiffAt_rpow_const_of_ne (ne_of_gt ha))







end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.sliceCSMass =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slice Cauchy–Schwarz mass bound `(∫_{θ₁}^{θ} u)² ≤ (π/2) ∫_{Iθ} u² sin(2θ)^{-η}`

The proof is the plain Cauchy–Schwarz inequality on the subinterval `[θ₁,θ] ⊆ (0,π/2)`
(`(∫_a^b u)² ≤ (b-a) ∫_a^b u²`, obtained from Hölder with `p = q = 2` for the pair
`(|u|,1)` on `volume.restrict (Ioc a b)`), together with the two elementary facts

* `θ - θ₁ ≤ π/2`, and
* `u² ≤ u² sin(2θ)^{-η}` on `(θ₁,θ)`, because `sin(2θ)^{-η} ≥ 1` there
  (`Work.FTS.EllSol.one_le_sEta_of_mem_Ioo`).
-/

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllSol.FlatFT

noncomputable section

set_option autoImplicit false

/-- **Cauchy–Schwarz for interval integrals.**  For `a ≤ b` and `u` continuous on `[a,b]`,

`(∫_a^b u)² ≤ (b - a) ∫_a^b u²`.

This is Hölder with `p = q = 2` applied to the pair `(|u|, 1)` on the finite measure
`volume.restrict (Ioc a b)` (whose total mass is `b - a`), followed by `|∫ u| ≤ ∫ |u|`. -/
private lemma sq_intervalIntegral_le {a b : ℝ} (hab : a ≤ b) {u : ℝ → ℝ}
    (hu : ContinuousOn u (Set.Icc a b)) :
    (∫ t in a..b, u t) ^ 2 ≤ (b - a) * ∫ t in a..b, u t ^ 2 := by
  have hIoc : MeasurableSet (Set.Ioc a b) := measurableSet_Ioc
  have hvol : volume.real (Set.Ioc a b) = b - a := by
    rw [MeasureTheory.measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  have huIoc : ContinuousOn u (Set.Ioc a b) := hu.mono Set.Ioc_subset_Icc_self
  -- square-integrability of the two factors of the Hölder pair
  have hInt2 : IntegrableOn (fun t : ℝ => |u t| ^ 2) (Set.Ioc a b) := by
    have h : IntegrableOn (fun t : ℝ => u t ^ 2) (Set.Ioc a b) :=
      ((hu.pow 2).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    exact h.congr (Eventually.of_forall (fun t => (sq_abs (u t)).symm))
  have hInt1 : IntegrableOn (fun _ : ℝ => (1 : ℝ) ^ 2) (Set.Ioc a b) := by
    simpa only [one_pow] using (MeasureTheory.integrableOn_const
      (μ := volume) (s := Set.Ioc a b) (C := (1 : ℝ))
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (by norm_num))
  -- Hölder
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict (Set.Ioc a b))
    (f := fun t : ℝ => |u t|) (g := fun _ : ℝ => (1 : ℝ))
    (by simpa [Real.norm_eq_abs] using (huIoc.aestronglyMeasurable hIoc).norm)
    aestronglyMeasurable_const hInt2 hInt1
  have hleft : (∫ x, |u x| * 1 ∂(volume.restrict (Set.Ioc a b))) = ∫ t in a..b, |u t| := by
    simp only [mul_one]
    exact (intervalIntegral.integral_of_le hab).symm
  have hright1 : (∫ x, |u x| ^ 2 ∂(volume.restrict (Set.Ioc a b))) = ∫ t in a..b, u t ^ 2 := by
    rw [intervalIntegral.integral_of_le hab]
    exact MeasureTheory.integral_congr_ae (Eventually.of_forall (fun x => sq_abs (u x)))
  have hright2 : (∫ x, (1 : ℝ) ^ 2 ∂(volume.restrict (Set.Ioc a b))) = b - a := by
    rw [MeasureTheory.setIntegral_const, hvol]
    norm_num
  have hMnn : 0 ≤ ∫ x, |u x| ^ 2 ∂(volume.restrict (Set.Ioc a b)) :=
    MeasureTheory.setIntegral_nonneg hIoc (fun x _ => sq_nonneg _)
  have hNnn : 0 ≤ ∫ x, (1 : ℝ) ^ 2 ∂(volume.restrict (Set.Ioc a b)) := by
    rw [hright2]; linarith
  have h1 : (∫ x, |u x| * 1 ∂(volume.restrict (Set.Ioc a b))) ^ 2 ≤
      (∫ x, |u x| ^ 2 ∂(volume.restrict (Set.Ioc a b))) *
        (∫ x, (1 : ℝ) ^ 2 ∂(volume.restrict (Set.Ioc a b))) := by
    calc (∫ x, |u x| * 1 ∂(volume.restrict (Set.Ioc a b))) ^ 2
        = |∫ x, |u x| * 1 ∂(volume.restrict (Set.Ioc a b))| ^ 2 := by rw [sq_abs]
      _ ≤ (Real.sqrt (∫ x, |u x| ^ 2 ∂(volume.restrict (Set.Ioc a b))) *
            Real.sqrt (∫ x, (1 : ℝ) ^ 2 ∂(volume.restrict (Set.Ioc a b)))) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hcs 2
      _ = (∫ x, |u x| ^ 2 ∂(volume.restrict (Set.Ioc a b))) *
            (∫ x, (1 : ℝ) ^ 2 ∂(volume.restrict (Set.Ioc a b))) := by
          rw [mul_pow, Real.sq_sqrt hMnn, Real.sq_sqrt hNnn]
  calc (∫ t in a..b, u t) ^ 2 ≤ (∫ t in a..b, |u t|) ^ 2 := by
        have h0 := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := u) hab
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h0 2
    _ = (∫ x, |u x| * 1 ∂(volume.restrict (Set.Ioc a b))) ^ 2 := by rw [hleft]
    _ ≤ (∫ x, |u x| ^ 2 ∂(volume.restrict (Set.Ioc a b))) *
        (∫ x, (1 : ℝ) ^ 2 ∂(volume.restrict (Set.Ioc a b))) := h1
    _ = (b - a) * ∫ t in a..b, u t ^ 2 := by rw [hright1, hright2, mul_comm]

/-- The mass bound in the ordered case `θ₀ ≤ θ`. -/
private lemma sliceCSMass_aux {u : ℝ → ℝ} {θ₀ θ : ℝ}
    (hθ₀ : θ₀ ∈ Set.Ioo 0 (Real.pi / 2)) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hle : θ₀ ≤ θ) (hu : ContinuousOn u (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (fun t : ℝ => u t ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ) :
    (∫ t in θ₀..θ, u t) ^ 2 ≤ (Real.pi / 2) *
      (∫ t in Work.Spaces.Iθ, u t ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))) := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- the subinterval is contained in `Iθ`
  have hsub : Set.Ioc θ₀ θ ⊆ Work.Spaces.Iθ := fun x hx =>
    ⟨le_of_lt (lt_of_lt_of_le hθ₀.1 hx.1.le), le_of_lt (lt_of_le_of_lt hx.2 hθ.2)⟩
  -- `u` is continuous on the closed subinterval
  have huIcc : ContinuousOn u (Set.Icc θ₀ θ) :=
    hu.mono (fun x hx => ⟨lt_of_lt_of_le hθ₀.1 hx.1, lt_of_le_of_lt hx.2 hθ.2⟩)
  -- Cauchy–Schwarz on the subinterval
  have hcs := sq_intervalIntegral_le hle huIcc
  have hlen : θ - θ₀ ≤ Real.pi / 2 := by linarith [hθ₀.1, hθ.2]
  -- comparing the weighted mass on `(θ₀,θ)` with the one on `Iθ`
  have hInt1 : IntegrableOn (fun t : ℝ => u t ^ 2) (Set.Ioc θ₀ θ) :=
    ((huIcc.pow 2).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hInt2 : IntegrableOn (fun t : ℝ => u t ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)))
      (Set.Ioc θ₀ θ) := hint.mono_set hsub
  have hstep : (∫ t in θ₀..θ, u t ^ 2) ≤
      ∫ t in Work.Spaces.Iθ, u t ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by
    rw [intervalIntegral.integral_of_le hle]
    refine (MeasureTheory.setIntegral_mono_on hInt1 hInt2 measurableSet_Ioc ?_).trans
      (MeasureTheory.setIntegral_mono_set hint ?_ ?_)
    · intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hx.1, hθ₀.1], by linarith [hx.2, hθ.2]⟩
      have h1 : 1 ≤ (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) :=
        Work.FTS.EllSol.one_le_sEta_of_mem_Ioo hx'
      calc u x ^ 2 = u x ^ 2 * 1 := by ring
        _ ≤ u x ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    · filter_upwards [ae_restrict_mem hIθ_meas] with x hx
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.sEta_nonneg_of_mem_Iθ hx)
    · exact Eventually.of_forall (fun x hx => hsub hx)
  have hMnn : 0 ≤ ∫ t in Work.Spaces.Iθ, u t ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) :=
    MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun x hx => mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.sEta_nonneg_of_mem_Iθ hx))
  have hlennn : 0 ≤ ∫ t in θ₀..θ, u t ^ 2 :=
    intervalIntegral.integral_nonneg hle (fun x _ => sq_nonneg _)
  calc (∫ t in θ₀..θ, u t) ^ 2 ≤ (θ - θ₀) * ∫ t in θ₀..θ, u t ^ 2 := hcs
    _ ≤ (Real.pi / 2) *
        (∫ t in Work.Spaces.Iθ, u t ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul hlen hstep hlennn (by positivity)

theorem sliceCSMass {u : ℝ → ℝ} {θ₁ θ : ℝ}
    (hθ₁ : θ₁ ∈ Set.Ioo 0 (Real.pi / 2)) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hu : ContinuousOn u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ =>
      u t ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ) :
    (∫ t in θ₁..θ, u t) ^ 2
      ≤ (Real.pi / 2) * (∫ t in Work.Spaces.Iθ,
          u t ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))) := by
  rcases le_total θ₁ θ with hle | hle
  · exact sliceCSMass_aux hθ₁ hθ hle hu hint
  · -- the reversed order: the integral changes sign, the square does not
    have h := sliceCSMass_aux hθ hθ₁ hle hu hint
    have h2 : (∫ t in θ₁..θ, u t) ^ 2 = (∫ t in θ..θ₁, u t) ^ 2 := by
      rw [intervalIntegral.integral_symm]
      ring
    rw [h2]
    exact h

end

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.sliceIntegralPointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

/-- **A bounded slice against a nonnegative weight.**

If `u` is a.e. strongly measurable for the restriction of Lebesgue measure to `Iθ`, if the
weight `σ` is integrable and nonnegative on `Iθ`, and if `u θ ^ 2 ≤ B` for every interior angle
`θ ∈ (0, π/2)`, then `u θ ^ 2 * σ θ` is integrable on `Iθ` and its integral is at most
`B ∫_{Iθ} σ`.

The point is that the hypothesis on `u` is only assumed on the *open* interval, whereas the
integral runs over the closed `Iθ`; the two differ by the null set `{0, π/2}`, which is handled
by `ae_restrict_Icc_of_forall_Ioo`.  The bound `‖u θ ^ 2 * σ θ‖ ≤ B * σ θ` then follows from
`u θ ^ 2 ≥ 0` and `σ θ ≥ 0`. -/
private lemma slice_integral_le_of_pointwise {u σ : ℝ → ℝ} {B : ℝ}
    (hu : MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hσ : MeasureTheory.IntegrableOn σ Work.Spaces.Iθ)
    (hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ)
    (hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), u θ ^ 2 ≤ B) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => u θ ^ 2 * σ θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, u θ ^ 2 * σ θ) ≤ B * (∫ θ in Work.Spaces.Iθ, σ θ) := by
  -- interior angles belong to the closed interval
  have hmem : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), θ ∈ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- the pointwise domination, a.e. on `Iθ`
  have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖u θ ^ 2 * σ θ‖ ≤ B * σ θ := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    have hσn : 0 ≤ σ θ := hσnn θ (hmem θ hθ)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hσn)]
    exact mul_le_mul_of_nonneg_right (hpt θ hθ) hσn
  -- hence integrability, against the integrable majorant `B * σ`
  have hInt : MeasureTheory.IntegrableOn (fun θ : ℝ => u θ ^ 2 * σ θ) Work.Spaces.Iθ :=
    (hσ.const_mul B).mono' ((hu.pow 2).mul hσ.aestronglyMeasurable) hbound
  refine ⟨hInt, ?_⟩
  have hle : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      u θ ^ 2 * σ θ ≤ B * σ θ := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    exact mul_le_mul_of_nonneg_right (hpt θ hθ) (hσnn θ (hmem θ hθ))
  calc (∫ θ in Work.Spaces.Iθ, u θ ^ 2 * σ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, B * σ θ :=
        MeasureTheory.integral_mono_ae hInt (hσ.const_mul B) hle
    _ = B * (∫ θ in Work.Spaces.Iθ, σ θ) := MeasureTheory.integral_const_mul B σ

/-- **A pointwise bound on a slice bounds the weighted slice integral.**

If `u θ ^ 2 ≤ C` on the interior of the angular interval and `u` is a.e. strongly measurable
there, then the zero-th angular slot `u θ ^ 2 * sin(2θ)^{-η}` is integrable on `Iθ` and its
integral is at most `C` times the integral of the weight `sin(2θ)^{-η}` itself (which is finite
by `Work.Spaces.sin_two_rpow`).

The hypothesis `0 ≤ C` is used at the very end to replace the a priori bound `|C|` by `C`. -/
theorem sliceIntegralPointwise {u : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hu : MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), u θ ^ 2 ≤ C) :
    MeasureTheory.IntegrableOn (fun θ : ℝ =>
        u θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, u θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ C * (∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  obtain ⟨hInt, hineq⟩ := slice_integral_le_of_pointwise
    (σ := fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) hu
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
      (by norm_num [Work.Spaces.eta])).1
    (fun θ hθ => Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc (x := 2 * θ)
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _)
    (fun θ hθ => hpt θ hθ)
  refine ⟨hInt, ?_⟩
  calc (∫ θ in Work.Spaces.Iθ, u θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ |C| * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
        le_trans hineq (le_of_eq (by rw [abs_of_nonneg hC]))
    _ = C * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
        by rw [abs_of_nonneg hC]

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.hardySinTwoFin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `sin (2θ)`-weighted Hardy inequality on `Iθ = [0, π/2]` (finite exponent)

`Work.FTS.EllSol.hardySinTwoFin`: there is a universal constant `K > 0` such that for every
`h` of class `C¹` on `(0, π/2)` with `h → 0` at both endpoints and whose `sin(2θ)^{-η}`-weighted
squared derivative is integrable on `Iθ`, the function `θ ↦ h(θ)² sin(2θ)^{-(2+η)}` is integrable
on `Iθ` and
  `∫_{Iθ} h² sin(2θ)^{-(2+η)} ≤ K ∫_{Iθ} (h')² sin(2θ)^{-η}`,   `η = Work.Spaces.eta = 99/100`.

The proof splits `Iθ` at its midpoint `π/4`.  On each half `sin (2θ)` is comparable with the
distance to the corresponding endpoint (`sin (2θ) ≈ 2θ` for `θ ≤ π/4`, and
`sin (2θ) = sin (2(π/2 − θ))` on the right half), so Jordan's inequality
`sin x ≥ (2/π) x` turns the `sin`-weighted Hardy inequality into the power-weight Hardy
inequality `Work.FTS.EllSol.powerHardyAll` (`∫₀^a h² t^{-(2+η)} ≤ 4 ∫₀^a (h')² t^{-η}`);
the right half is mapped to the left one by the reflection `θ ↦ π/2 − θ`
(`mirrorIooIntegrableOn`, `mirrorIooIntegral`).

The stronger statement `hardySigmaFin` below (every exponent `0 ≤ λ ≤ 2` in place of `η`) is
proved in the same way; the requested lemma is its instance `λ = η`.
-/

set_option autoImplicit false
open MeasureTheory Real Set Filter
open scoped Topology

namespace Work.FTS.EllSol

/-! ## Elementary comparison lemmas on `(0, π/4)` -/





/-- `sin (2θ) ^ (-(2+λ)) ≤ θ ^ (-(2+λ))` on `(0, π/4)`, for `λ ≥ 0`. -/
private lemma sin_rpow_le_theta_rpow {lam θ : ℝ} (hlam0 : 0 ≤ lam)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    (Real.sin (2 * θ)) ^ (-(2 + lam)) ≤ θ ^ (-(2 + lam)) := by
  have h2θ : 0 ≤ 2 * θ := by linarith [hθ.1]
  have h2θ' : 2 * θ ≤ Real.pi / 2 := by linarith [hθ.2, Real.pi_pos]
  have hsin : 2 / Real.pi * (2 * θ) ≤ Real.sin (2 * θ) := Real.mul_le_sin h2θ h2θ'
  have h4 : (1 : ℝ) ≤ 4 / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    linarith [Real.pi_lt_four]
  have hθle : θ ≤ Real.sin (2 * θ) := by
    have h : 2 / Real.pi * (2 * θ) = (4 / Real.pi) * θ := by ring
    rw [h] at hsin
    exact le_trans (le_mul_of_one_le_left (le_of_lt hθ.1) h4) hsin
  exact Real.rpow_le_rpow_of_nonpos hθ.1 hθle (by linarith)


/-- Pointwise domination of the `sin`-weighted value by the power-weighted one. -/
private lemma sq_mul_le_sq_mul {a θ lam : ℝ} (hlam0 : 0 ≤ lam)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    a ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)) ≤ a ^ 2 * θ ^ (-(2 + lam)) :=
  mul_le_mul_of_nonneg_left (sin_rpow_le_theta_rpow hlam0 hθ) (sq_nonneg a)

/-! ## The half-interval `sin`-weighted Hardy inequality -/


/-! ## The main theorem -/



end Work.FTS.EllSol
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.SliceEtaFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

/-!
## Elementary facts about the angular weight `sEta θ = sin(2θ)^{-η}`

`sEta` is the `i = 0` (purely radial) angular weight of the `ℋ^k` norm of the Elgindi project,
`Work.FTS.EllipticEst.sEta θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))` with
`η = 99/100`.  On the angular interval `Iθ = [0, π/2]` it is a nonnegative function which is
integrable with a fixed universal bound on its integral (`10^4`, which is in fact sharp:
`100 / (1 - η) = 10^4`), equals at least `1` on the open interval `(0, π/2)`, and is continuous
there.  These are the facts needed whenever one compares the weighted slice functional with a
plain slice integral.
-/

/-- `sEta` is nonnegative on the angular interval `Iθ = [0, π/2]`: there `2θ ∈ [0, π]`, so
`sin(2θ) ≥ 0`, and a nonnegative base has a nonnegative real power. -/
theorem sEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  refine Real.rpow_nonneg ?_ _
  refine Real.sin_nonneg_of_mem_Icc ⟨?_, ?_⟩
  · linarith [hθ.1]
  · have := Real.pi_pos; linarith [hθ.2]

/-- `1 ≤ sEta θ` on the open interval `(0, π/2)`: there `0 < sin(2θ) ≤ 1` and the exponent
`-η` is negative, so `sin(2θ)^{-η} ≥ 1`. -/
theorem one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have h0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_exponent_ge h0 hle1
    (show -(Work.Spaces.eta) ≤ (0 : ℝ) by have := Work.Spaces.eta_pos; linarith)
  simpa [Work.FTS.EllipticEst.sEta, Real.rpow_zero] using h

/-- `sEta` is continuous at every point of the open interval `(0, π/2)`, where its base
`sin(2θ)` is strictly positive. -/
theorem continuousAt_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousAt Work.FTS.EllipticEst.sEta θ := by
  have h0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hcont : ContinuousAt (fun θ : ℝ => Real.sin (2 * θ)) θ :=
    Real.continuous_sin.continuousAt.comp (continuous_const.mul continuous_id).continuousAt
  have h := ContinuousAt.rpow hcont
    (continuousAt_const : ContinuousAt (fun _ : ℝ => -(Work.Spaces.eta)) θ)
    (Or.inl (ne_of_gt h0))
  change ContinuousAt (fun t : ℝ => Real.sin (2 * t) ^ (-(Work.Spaces.eta))) θ
  exact h

/-- Integrability of `sEta` on `Iθ`, with the universal bound `∫_{Iθ} sEta ≤ 10^4` on its
integral.  Both come from `Work.Spaces.sin_two_rpow` at the exponent `p = -η ∈ (-1, 0)`:
`100 / (1 - η) = 10^4`, so the stated constant is exactly the one produced by the general
β-integral estimate. -/
theorem integrableOn_sEta_and_integral_le :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) ≤ 10 ^ 4 := by
  have hmain := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])
  refine ⟨hmain.1, ?_⟩
  calc ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ
      = ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) := rfl
    _ ≤ 100 / (-(Work.Spaces.eta) + 1) := hmain.2
    _ = 10 ^ 4 := by norm_num [Work.Spaces.eta]

theorem SliceEtaFacts :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) ≤ 10 ^ 4 ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 1 ≤ Work.FTS.EllipticEst.sEta θ) ∧
      (∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.EllipticEst.sEta θ) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContinuousAt Work.FTS.EllipticEst.sEta θ) :=
  ⟨integrableOn_sEta_and_integral_le.1, integrableOn_sEta_and_integral_le.2,
    fun _ hθ => one_le_sEta hθ, fun _ hθ => sEta_nonneg_of_mem_Iθ hθ,
    fun _ hθ => continuousAt_sEta hθ⟩

end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonSelfDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest


end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.I4BoundaryVanish =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

/-- **The vanishing of the `I₄` boundary term.**

Let `ψ` be a function of the angular variable, of class `C²` on the open interval `(0, π/2)`,
whose weighted square `∫_θ ψ² (sin 2θ)^{-η}` is finite (`η = 99/100`), and for which
`P := fun θ => cos²θ · ψ'(θ)` satisfies `∫_θ (P'(θ)/cos θ)² (sin 2θ)^{-η} < ∞`.
Then the boundary quantity `(sin θ / cos³θ) · P(θ)² · (sin 2θ)^{-η}` tends to `0` as
`θ → π/2⁻`.

Proof route: (1) `∫ (P'/c)²σ < ∞` and `∫_θ^{π/2} c²σ^{-1} ≤ C(π/2-θ)^{3+η}` (from the
elementary pointwise bound `cos²θ·(sin 2θ)^η ≤ 2^η(π/2-θ)^{2+η}`) give `P' ∈ L¹`, hence by
the Cauchy criterion `|P(θ)-P(θ')| ≤ (∫_θ^{θ'}(P'/c)²σ)^{1/2}(∫_θ^{θ'}c²σ^{-1})^{1/2}
≤ C(π/2-θ)^{(3+η)/2}√(V θ)` with `V θ = ∫_θ^{π/2}(P'/c)²σ`, that `L := lim_{θ→π/2}P(θ)`
exists and `|P(θ)-L| ≤ C(π/2-θ)^{(3+η)/2}√(V θ)`; (2) `L = 0`, since `L ≠ 0` forces
`|ψ'| ≥ (|L|/2)cos^{-2}θ ≥ (|L|/2)(π/2-θ)^{-2}` and hence `|ψ| ≥ (|L|/4)(π/2-θ)^{-1}` near
`π/2`, so `∫ψ²σ ≥ (|L|²/16)∫(π/2-θ)^{-2}dθ = ∞` because `σ = (sin 2θ)^{-η} ≥ 1`, contradicting
the hypothesis; (3) `V θ → 0`, so `P(θ)²(π/2-θ)^{-3-η} ≤ C²·V θ → 0`, and
`(sin θ/cos³θ)·σ ≤ C(π/2-θ)^{-3-η}` (`sin θ ≤ 1`, `cos θ ≥ (2/π)(π/2-θ)`,
`sin(2θ) ≥ (4/π)(π/2-θ)`) finishes the proof. -/
theorem I4BoundaryVanish (ψ : ℝ → ℝ)
    (hsm : ContDiffOn ℝ 2 ψ (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn
      (fun θ => ψ θ ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) (Set.Ioo 0 (Real.pi / 2)))
    (hB : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') θ / Real.cos θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) (Set.Ioo 0 (Real.pi / 2))) :
    Filter.Tendsto
      (fun θ => Real.sin θ / (Real.cos θ) ^ 3 * ((Real.cos θ) ^ 2 * deriv ψ θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hquarter : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hhalf : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
  have hneghalf : -(Real.pi / 2) < (0 : ℝ) := by linarith [Real.pi_pos]
  have hPderiv : ∀ x ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ')
        (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x) x := by
    intro x hx
    have h2 : ContDiffAt ℝ 2 ψ x := hsm.contDiffAt (isOpen_Ioo.mem_nhds hx)
    have hd1 : ContDiffAt ℝ 1 (deriv ψ) x := h2.derivWithin (by norm_num)
    have hdψ : DifferentiableAt ℝ (deriv ψ) x := hd1.differentiableAt (by norm_num)
    have hP : DifferentiableAt ℝ (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x := by
      fun_prop
    exact hP.hasDerivAt
  obtain ⟨L, hLtend, hLrate⟩ :=
    I4BV.i4_rate_alt (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') hPderiv hB
  have hL0 : L = 0 := I4BV.i4_limit_eq_zero ψ L hsm hA hLtend
  have hVtend : Filter.Tendsto
      (fun t => ∫ x in Set.Ioo t (Real.pi / 2),
        (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x / Real.cos x) ^ 2
          * (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    I4BV.tail_setIntegral_tendsto_zero (a := 0) (b := Real.pi / 2) hpi2 hB
  have hmem : Set.Ioo (Real.pi / 4) (Real.pi / 2) ∈
      nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT (a := Real.pi / 4) hquarter]
    exact self_mem_nhdsWithin
  have hkey : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      Real.sin θ / (Real.cos θ) ^ 3 * ((Real.cos θ) ^ 2 * deriv ψ θ) ^ 2 * I4BV.s4 θ
      ≤ (I4BV.K4 * 2 ^ (99 / 100 : ℝ))
        * ∫ x in Set.Ioo θ (Real.pi / 2),
            (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x / Real.cos x) ^ 2
              * (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)) := by
    intro θ hθ
    have hI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨lt_trans hpi4 hθ.1, hθ.2⟩
    have hu : 0 < Real.pi / 2 - θ := sub_pos.mpr hθ.2
    have h1 := I4BV.coef_le hθ
    have h2 := hLrate θ hI
    rw [hL0] at h2
    calc Real.sin θ / (Real.cos θ) ^ 3 * ((Real.cos θ) ^ 2 * deriv ψ θ) ^ 2 * I4BV.s4 θ
        = (Real.sin θ / (Real.cos θ) ^ 3 * I4BV.s4 θ)
          * ((Real.cos θ) ^ 2 * deriv ψ θ) ^ 2 := by ring
      _ ≤ (I4BV.K4 * (Real.pi / 2 - θ) ^ (-(3 + 99 / 100 : ℝ)))
          * (2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ)
            * ∫ x in Set.Ioo θ (Real.pi / 2),
                (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x / Real.cos x) ^ 2
                  * (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ))) := by
          apply mul_le_mul h1 ?_ (sq_nonneg _) ?_
          · simpa using h2
          · rw [I4BV.K4]; positivity
      _ = I4BV.K4 * 2 ^ (99 / 100 : ℝ)
          * ((Real.pi / 2 - θ) ^ (-(3 + 99 / 100 : ℝ))
            * (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ))
          * ∫ x in Set.Ioo θ (Real.pi / 2),
              (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x / Real.cos x) ^ 2
                * (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)) := by ring
      _ = (I4BV.K4 * 2 ^ (99 / 100 : ℝ))
          * ∫ x in Set.Ioo θ (Real.pi / 2),
              (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x / Real.cos x) ^ 2
                * (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)) := by
          have hc : (Real.pi / 2 - θ) ^ (-(3 + 99 / 100 : ℝ))
              * (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ) = 1 := by
            rw [← Real.rpow_add hu,
              show -(3 + 99 / 100 : ℝ) + (3 + 99 / 100 : ℝ) = 0 by ring, Real.rpow_zero]
          rw [hc]; ring
  change Filter.Tendsto
      (fun θ => Real.sin θ / (Real.cos θ) ^ 3 * ((Real.cos θ) ^ 2 * deriv ψ θ) ^ 2
        * I4BV.s4 θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)
  have hbound : Filter.Tendsto
      (fun t => (I4BV.K4 * 2 ^ (99 / 100 : ℝ))
        * ∫ x in Set.Ioo t (Real.pi / 2),
            (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x / Real.cos x) ^ 2
              * (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    simpa using hVtend.const_mul (I4BV.K4 * 2 ^ (99 / 100 : ℝ))
  refine squeeze_zero_norm' (a := fun t => (I4BV.K4 * 2 ^ (99 / 100 : ℝ))
        * ∫ x in Set.Ioo t (Real.pi / 2),
            (deriv (fun θ' => (Real.cos θ') ^ 2 * deriv ψ θ') x / Real.cos x) ^ 2
              * (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)))
    ?_ hbound
  filter_upwards [hmem] with θ hθ
  have hI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨lt_trans hpi4 hθ.1, hθ.2⟩
  have hsinnn : 0 ≤ Real.sin θ :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi hI.1 (lt_trans hI.2 hhalf))
  have hcosnn : 0 ≤ Real.cos θ :=
    le_of_lt (Real.cos_pos_of_mem_Ioo ⟨lt_trans hneghalf hI.1, hI.2⟩)
  have hs4nn : 0 ≤ I4BV.s4 θ := by
    rw [I4BV.s4]
    exact Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hI.1])
      (by linarith [hI.2, Real.pi_pos]))) _
  have hnn : 0 ≤ Real.sin θ / (Real.cos θ) ^ 3 * ((Real.cos θ) ^ 2 * deriv ψ θ) ^ 2
      * I4BV.s4 θ :=
    mul_nonneg (mul_nonneg (div_nonneg hsinnn (by positivity)) (sq_nonneg _)) hs4nn
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hkey θ hθ

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.SelfAux.SliceAntiderivDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.SelfAux

/-- **Pointwise antiderivative identity for the self-pairing of `Lzero1`.**  For `u : ℝ → ℝ`
which is `C²` at `θ ∈ (0, π/2)`, the function `s ↦ -(deriv u s) * u s + (1/2) * tan s * (u s)^2`
has derivative `Lzero1 u θ * u θ - (deriv u θ)^2 - (1/2) * (u θ / cos θ)^2 + 6 * (u θ)^2` at `θ`.

This is a two-line wrapper: apply the already-proved
`Work.FTS.EllipticEst.hasDerivAt_self_antideriv` (in
`Submission/Work/FTS/EllipticEst/hasDerivAt_self_antideriv.lean`), which gives the same
`HasDerivAt` with `Work.Elliptic.Lzero (fun _ s => u s) 0 θ` in place of `Lzero1 u θ`, and
rewrite with `Work.FTS.EllipticEst.Lzero1_eq_Lzero u 0 θ` (in
`Submission/Work/FTS/EllipticEst/StraightDefs.lean`).

Please declare it at the ROOT namespace (no `namespace` wrapper), so that its name is exactly
`SliceAntiderivDeriv`. -/
theorem SliceAntiderivDeriv (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (h2 : ContDiffAt ℝ 2 u θ) :
    HasDerivAt (fun s => -(deriv u s) * u s + (1 / 2) * Real.tan s * (u s) ^ 2)
      (Work.FTS.EllipticEst.Lzero1 u θ * u θ - (deriv u θ) ^ 2
        - (1 / 2) * (u θ / Real.cos θ) ^ 2 + 6 * (u θ) ^ 2) θ := by
  -- The already-proved `L₀`-version of the identity, at `z = 0`.
  have h := Work.FTS.EllipticEst.hasDerivAt_self_antideriv u θ hθ h2
  -- `Lzero1` is the `θ`-slice of `Work.Elliptic.Lzero`, so the derivative values agree.
  have hL : Work.Elliptic.Lzero (fun _ s => u s) 0 θ = Work.FTS.EllipticEst.Lzero1 u θ := by
    rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero u 0]
  exact h.congr_deriv (by rw [hL])

end Work.FTS.EllipticEst.Honest.SelfAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Lzero_self_form =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Two functions which agree on the open interval `(0, π/2)` agree almost everywhere on the
closed interval, since the two endpoints are a null set. -/
private lemma ae_eq_restrict_of_eqOn_Ioo {g h : ℝ → ℝ}
    (hgh : ∀ θ ∈ Ioo (0 : ℝ) (π / 2), g θ = h θ) :
    g =ᵐ[volume.restrict (Icc (0 : ℝ) (π / 2))] h := by
  show ∀ᵐ θ ∂(volume.restrict (Icc (0 : ℝ) (π / 2))), g θ = h θ
  rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
  refine measure_mono_null (t := ({0, π / 2} : Set ℝ)) ?_ ?_
  · intro θ hθ
    simp only [mem_ofPred_eq, not_imp, mem_Icc] at hθ
    obtain ⟨hθs, hne⟩ := hθ
    rcases eq_or_lt_of_le hθs.1 with h | h
    · exact Or.inl h.symm
    · rcases eq_or_lt_of_le hθs.2 with h2 | h2
      · exact Or.inr h2
      · exact absurd (hgh θ ⟨h, h2⟩) hne
  · rw [show ({0, π / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {π / 2} from by
      ext x; simp only [mem_insert_iff, mem_singleton_iff, mem_union]]
    exact measure_union_null (measure_singleton 0) (measure_singleton (π / 2))

/-- The main workhorse: the angular integration by parts for a single function `f`. -/
private lemma Lzero_self_form_aux (f : ℝ → ℝ)
    (hs : ContDiffOn ℝ 2 f (Icc (0 : ℝ) (π / 2))) (h0 : f 0 = 0) (h1 : f (π / 2) = 0) :
    (∫ θ in Icc (0 : ℝ) (π / 2), Work.Elliptic.Lzero (fun _ θ' => f θ') 0 θ * f θ)
      = (∫ θ in Icc (0 : ℝ) (π / 2), (deriv f θ) ^ 2)
        + (1 / 2) * (∫ θ in Icc (0 : ℝ) (π / 2), (f θ / Real.cos θ) ^ 2)
        - 6 * (∫ θ in Icc (0 : ℝ) (π / 2), (f θ) ^ 2) := by
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  have hlt : (0 : ℝ) < π / 2 := by positivity
  set dW : ℝ → ℝ := derivWithin f (Icc (0 : ℝ) (π / 2)) with hdW
  set ps : ℝ → ℝ := derivWithin dW (Icc (0 : ℝ) (π / 2)) with hps
  set FW : ℝ → ℝ := fun θ => -(dW θ) * f θ + (1 / 2) * Real.tan θ * (f θ) ^ 2 with hFW
  set R0 : ℝ → ℝ := fun θ => (-(ps θ)) * f θ - (dW θ) ^ 2 + (1 / 2) * (f θ / Real.cos θ) ^ 2
    + Real.sin θ * (f θ / Real.cos θ) * dW θ with hR0
  -- continuity of the auxiliary functions
  have hdW_cont : ContinuousOn dW (Icc (0 : ℝ) (π / 2)) := by
    rw [hdW]
    exact hs.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) (by norm_num)
  have hdW_cd : ContDiffOn ℝ 1 dW (Icc (0 : ℝ) (π / 2)) := by
    rw [hdW]
    exact hs.derivWithin (uniqueDiffOn_Icc hlt) (by norm_num)
  have hps_cont : ContinuousOn ps (Icc (0 : ℝ) (π / 2)) := by
    rw [hps]
    exact hdW_cd.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) (by norm_num)
  have hf_cont : ContinuousOn f (Icc (0 : ℝ) (π / 2)) := hs.continuousOn
  -- the pointwise facts relating `deriv f` to `dW`, `deriv (deriv f)` to `ps`
  have hcos_ne : ∀ θ ∈ Ioo (0 : ℝ) (π / 2), Real.cos θ ≠ 0 := by
    intro θ hθ
    have hmem : θ ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo hmem)
  have hdf : ∀ θ ∈ Ioo (0 : ℝ) (π / 2), deriv f θ = dW θ := by
    intro θ hθ
    rw [hdW]
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds hθ.1 hθ.2)).symm
  have hddf : ∀ θ ∈ Ioo (0 : ℝ) (π / 2), deriv (deriv f) θ = ps θ := by
    intro θ hθ
    have hev : deriv f =ᶠ[𝓝 θ] dW := by
      filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
      rw [hdW]
      exact (derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)).symm
    rw [hev.deriv_eq, hps]
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds hθ.1 hθ.2)).symm
  -- the pointwise derivative identity, via the delegated lemma
  have hderiv_FW : ∀ θ ∈ Ioo (0 : ℝ) (π / 2),
      deriv FW θ = Work.Elliptic.Lzero (fun _ s => f s) 0 θ * f θ
        - (deriv f θ) ^ 2 - (1 / 2) * (f θ / Real.cos θ) ^ 2 + 6 * (f θ) ^ 2 := by
    intro θ hθ
    have h2 : ContDiffAt ℝ 2 f θ := hs.contDiffAt (Icc_mem_nhds hθ.1 hθ.2)
    have hA := hasDerivAt_self_antideriv f θ hθ h2
    have hev : FW =ᶠ[𝓝 θ]
        (fun s => -(deriv f s) * f s + (1 / 2) * Real.tan s * (f s) ^ 2) := by
      filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
      simp only [hFW, hdW, derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)]
    exact (hA.congr_of_eventuallyEq hev).deriv
  -- the a.e. identity for `Lzero · f`
  have hA_ae : (fun θ => Work.Elliptic.Lzero (fun _ θ' => f θ') 0 θ * f θ)
      =ᵐ[volume.restrict (Icc (0 : ℝ) (π / 2))]
      (fun θ => deriv FW θ + (deriv f θ) ^ 2 + (1 / 2) * (f θ / Real.cos θ) ^ 2
        - 6 * (f θ) ^ 2) := by
    refine ae_eq_restrict_of_eqOn_Ioo (fun θ hθ => ?_)
    rw [hderiv_FW θ hθ]
    ring
  -- the explicit computation of `deriv FW`
  have hFW_deriv : ∀ θ ∈ Ioo (0 : ℝ) (π / 2),
      deriv FW θ = (-(ps θ)) * f θ - (dW θ) ^ 2 + (1 / 2) * (f θ / Real.cos θ) ^ 2
        + Real.tan θ * dW θ * f θ := by
    intro θ hθ
    have hcos : Real.cos θ ≠ 0 := hcos_ne θ hθ
    have h2 : ContDiffAt ℝ 2 f θ := hs.contDiffAt (Icc_mem_nhds hθ.1 hθ.2)
    have hfd : HasDerivAt f (dW θ) θ :=
      ((h2.differentiableAt (by norm_num)).hasDerivAt).congr_deriv (hdf θ hθ)
    have hev : dW =ᶠ[𝓝 θ] deriv f := by
      filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
      rw [hdW]
      exact derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)
    have hdW_d : HasDerivAt dW (ps θ) θ :=
      ((((h2.derivWithin (m := 1) (by norm_num)).differentiableAt (n := 1)
        (by norm_num)).hasDerivAt).congr_deriv (hddf θ hθ)).congr_of_eventuallyEq hev
    have h1 : HasDerivAt (fun y => (-(dW y)) * f y)
        ((-(ps θ)) * f θ + (-(dW θ)) * dW θ) θ := hdW_d.neg.mul hfd
    have h2p : HasDerivAt (fun y => (f y) ^ 2) (2 * f θ ^ (2 - 1) * dW θ) θ := hfd.pow 2
    have h3 : HasDerivAt (fun y => Real.tan y * (f y) ^ 2)
        ((1 / Real.cos θ ^ 2) * (f θ) ^ 2 + Real.tan θ * (2 * f θ ^ (2 - 1) * dW θ)) θ :=
      (Real.hasDerivAt_tan hcos).mul h2p
    have h4 : HasDerivAt (fun y => (1 / 2) * (Real.tan y * (f y) ^ 2))
        ((1 / 2) * ((1 / Real.cos θ ^ 2) * (f θ) ^ 2
          + Real.tan θ * (2 * f θ ^ (2 - 1) * dW θ))) θ := h3.const_mul (1 / 2)
    have h5 := (h1.add h4).congr_of_eventuallyEq
      (show FW =ᶠ[𝓝 θ] ((fun y => (-(dW y)) * f y)
        + (fun y => (1 / 2) * (Real.tan y * (f y) ^ 2))) from by
        filter_upwards with y
        simp only [Pi.add_apply, hFW]
        ring)
    have h21 : (2 : ℕ) - 1 = 1 := by norm_num
    rw [h5.deriv, h21, pow_one, div_pow]
    ring
  -- the a.e. identity for the derivative of `FW`, in a form with bounded pieces
  have hE_ae : (fun θ => deriv FW θ) =ᵐ[volume.restrict (Icc (0 : ℝ) (π / 2))] R0 := by
    refine ae_eq_restrict_of_eqOn_Ioo (fun θ hθ => ?_)
    rw [hFW_deriv θ hθ, hR0]
    change (-(ps θ)) * f θ - (dW θ) ^ 2 + (1 / 2) * (f θ / Real.cos θ) ^ 2
        + Real.tan θ * dW θ * f θ
      = (-(ps θ)) * f θ - (dW θ) ^ 2 + (1 / 2) * (f θ / Real.cos θ) ^ 2
        + Real.sin θ * (f θ / Real.cos θ) * dW θ
    rw [Real.tan_eq_sin_div_cos]
    ring
  -- bounds
  obtain ⟨Cb, hCb0, hCb⟩ := exists_bound_div_cos f hs h1
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn hdW_cont
  -- measurability
  have hf_aem : AEMeasurable f (volume.restrict (Icc (0 : ℝ) (π / 2))) :=
    hf_cont.aemeasurable measurableSet_Icc
  have hdiv_aem : AEMeasurable (fun θ => f θ / Real.cos θ)
      (volume.restrict (Icc (0 : ℝ) (π / 2))) :=
    hf_aem.div Real.measurable_cos.aemeasurable
  have hdW_aem : AEMeasurable dW (volume.restrict (Icc (0 : ℝ) (π / 2))) :=
    hdW_cont.aemeasurable measurableSet_Icc
  -- integrability of the pieces
  have hD_int : IntegrableOn (fun θ => (f θ) ^ 2) (Icc (0 : ℝ) (π / 2)) :=
    (hf_cont.pow 2).integrableOn_compact isCompact_Icc
  have hC_int : IntegrableOn (fun θ => (f θ / Real.cos θ) ^ 2) (Icc (0 : ℝ) (π / 2)) := by
    refine IntegrableOn.of_bound isCompact_Icc.measure_lt_top ?_ (Cb ^ 2) ?_
    · have heq : (fun θ => (f θ / Real.cos θ) ^ 2)
          = (fun θ => f θ / Real.cos θ) * (fun θ => f θ / Real.cos θ) := by
        funext θ; simp only [Pi.mul_apply, sq]
      rw [heq]
      exact (hdiv_aem.mul hdiv_aem).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Icc]
      refine Eventually.of_forall (fun θ hθ => ?_)
      have hx := hCb θ hθ
      have h2 : (f θ / Real.cos θ) ^ 2 ≤ Cb ^ 2 := by
        rw [← sq_abs (f θ / Real.cos θ)]
        exact pow_le_pow_left₀ (abs_nonneg _) hx 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h2
  have hBsq_int : IntegrableOn (fun θ => (dW θ) ^ 2) (Icc (0 : ℝ) (π / 2)) :=
    (hdW_cont.pow 2).integrableOn_compact isCompact_Icc
  have hB_int : IntegrableOn (fun θ => (deriv f θ) ^ 2) (Icc (0 : ℝ) (π / 2)) := by
    have h := ae_eq_restrict_of_eqOn_Ioo (g := fun θ => deriv f θ) (h := dW)
      (fun θ hθ => hdf θ hθ)
    refine hBsq_int.congr_fun_ae ?_
    filter_upwards [h.symm] with θ hθ
    rw [hθ]
  have hA4_int : IntegrableOn (fun θ => Real.sin θ * (f θ / Real.cos θ) * dW θ)
      (Icc (0 : ℝ) (π / 2)) := by
    refine IntegrableOn.of_bound isCompact_Icc.measure_lt_top ?_ (Cb * M1) ?_
    · have heq : (fun θ => Real.sin θ * (f θ / Real.cos θ) * dW θ)
          = (Real.sin * (fun θ => f θ / Real.cos θ)) * dW := by
        funext θ; simp only [Pi.mul_apply]
      rw [heq]
      exact ((Real.continuous_sin.measurable.aemeasurable.mul hdiv_aem).mul
        hdW_aem).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Icc]
      refine Eventually.of_forall (fun θ hθ => ?_)
      have hx := hCb θ hθ
      have hy' : |dW θ| ≤ M1 := by simpa only [Real.norm_eq_abs] using hM1 θ hθ
      have hs1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |Real.sin θ| * |f θ / Real.cos θ| * |dW θ|
          ≤ 1 * Cb * M1 := by gcongr
        _ = Cb * M1 := by ring
  have hA1_int : IntegrableOn (fun θ => (-(ps θ)) * f θ) (Icc (0 : ℝ) (π / 2)) :=
    ((continuous_neg.comp_continuousOn hps_cont).mul hf_cont).integrableOn_compact
      isCompact_Icc
  have hR0_int : IntegrableOn R0 (Icc (0 : ℝ) (π / 2)) := by
    have hsum := (hA1_int.sub hBsq_int).add
      ((Integrable.const_mul hC_int (1 / 2)).add hA4_int)
    refine hsum.congr_fun_ae ?_
    refine Eventually.of_forall (fun θ => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hR0]
    ring
  have hE_int : IntegrableOn (fun θ => deriv FW θ) (Icc (0 : ℝ) (π / 2)) :=
    hR0_int.congr_fun_ae hE_ae.symm
  -- the fundamental theorem of calculus for the antiderivative
  have hFW_cont : ContinuousOn FW (Icc (0 : ℝ) (π / 2)) := by
    rw [hFW, hdW]
    exact continuousOn_antideriv f hs h1
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) (π / 2), HasDerivAt FW (deriv FW x) x := by
    intro x hx
    have h2 : ContDiffAt ℝ 2 f x := hs.contDiffAt (Icc_mem_nhds hx.1 hx.2)
    have hA := hasDerivAt_self_antideriv f x hx h2
    have hev : FW =ᶠ[𝓝 x]
        (fun s => -(deriv f s) * f s + (1 / 2) * Real.tan s * (f s) ^ 2) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      simp only [hFW, hdW, derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)]
    have hA' := hA.congr_of_eventuallyEq hev
    rw [hA'.deriv]
    exact hA'
  have hint : IntervalIntegrable (fun θ => deriv FW θ) volume (0 : ℝ) (π / 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr hE_int
  have hFTC : ∫ θ in (0 : ℝ)..(π / 2), deriv FW θ = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hFW_cont hderiv hint, hFW]
    simp only [h0, h1, mul_zero, Real.tan_zero]
    norm_num
  have hFTC' : (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ) = 0 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
    exact hFTC
  -- assemble
  have hF1 : IntegrableOn ((fun θ => deriv FW θ) : ℝ → ℝ) (Icc (0 : ℝ) (π / 2)) := hE_int
  have hF2 : IntegrableOn ((fun θ => (deriv f θ) ^ 2) : ℝ → ℝ) (Icc (0 : ℝ) (π / 2)) := hB_int
  have hF3 : IntegrableOn ((fun θ => (1 / 2) * (f θ / Real.cos θ) ^ 2) : ℝ → ℝ)
      (Icc (0 : ℝ) (π / 2)) := Integrable.const_mul hC_int (1 / 2)
  have hF4 : IntegrableOn ((fun θ => 6 * (f θ) ^ 2) : ℝ → ℝ) (Icc (0 : ℝ) (π / 2)) :=
    Integrable.const_mul hD_int 6
  have hF12 := hF1.add hF2
  have hF123 := hF12.add hF3
  have hsp1 : (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ + (deriv f θ) ^ 2
        + (1 / 2) * (f θ / Real.cos θ) ^ 2 - 6 * (f θ) ^ 2)
      = (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ + (deriv f θ) ^ 2
          + (1 / 2) * (f θ / Real.cos θ) ^ 2)
        - (∫ θ in Icc (0 : ℝ) (π / 2), 6 * (f θ) ^ 2) :=
    integral_sub hF123 hF4
  have hsp2 : (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ + (deriv f θ) ^ 2
        + (1 / 2) * (f θ / Real.cos θ) ^ 2)
      = (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ + (deriv f θ) ^ 2)
        + (∫ θ in Icc (0 : ℝ) (π / 2), (1 / 2) * (f θ / Real.cos θ) ^ 2) :=
    integral_add hF12 hF3
  have hsp3 : (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ + (deriv f θ) ^ 2)
      = (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ)
        + (∫ θ in Icc (0 : ℝ) (π / 2), (deriv f θ) ^ 2) :=
    integral_add hF1 hF2
  have hsp4 : (∫ θ in Icc (0 : ℝ) (π / 2), (1 / 2) * (f θ / Real.cos θ) ^ 2)
      = (1 / 2) * (∫ θ in Icc (0 : ℝ) (π / 2), (f θ / Real.cos θ) ^ 2) :=
    integral_const_mul (1 / 2) (fun θ => (f θ / Real.cos θ) ^ 2)
  have hsp5 : (∫ θ in Icc (0 : ℝ) (π / 2), 6 * (f θ) ^ 2)
      = 6 * (∫ θ in Icc (0 : ℝ) (π / 2), (f θ) ^ 2) :=
    integral_const_mul 6 (fun θ => (f θ) ^ 2)
  rw [integral_congr_ae hA_ae, hsp1, hsp2, hsp3, hsp4, hsp5, hFTC']
  ring

/-- The angular integration by parts against the function itself: for a `C²` slice `θ ↦ v z θ`
vanishing at `θ = 0, π/2`, the pairing of `Lzero` with `v` is the quadratic form
`∫ v_θ² + (1/2) ∫ (v/cos)² - 6 ∫ v²`.  (The antiderivative is `-v' v + (1/2) tan θ · v²`; at the
endpoints it vanishes, at `π/2` because `v` vanishes to first order there.) -/
theorem Lzero_self_form (v : ℝ → ℝ → ℝ) (z : ℝ)
    (hs : ContDiffOn ℝ 2 (fun θ => v z θ) (Set.Icc 0 (π / 2))) (h0 : v z 0 = 0)
    (h1 : v z (π / 2) = 0) :
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero v z θ * v z θ)
      = (∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => v z θ') θ) ^ 2)
        + (1 / 2) * (∫ θ in Work.Spaces.Iθ, (v z θ / Real.cos θ) ^ 2)
        - 6 * (∫ θ in Work.Spaces.Iθ, (v z θ) ^ 2) := by
  have hL : ∀ θ : ℝ,
      Work.Elliptic.Lzero v z θ = Work.Elliptic.Lzero (fun _ θ' => v z θ') 0 θ := by
    intro θ
    rw [Work.Elliptic.Lzero_eq_deriv, Work.Elliptic.Lzero_eq_deriv]
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
  simp only [hL]
  exact Lzero_self_form_aux (fun θ => v z θ) hs h0 h1

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.cs_interval_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Cauchy–Schwarz for the interval integral against the angular energy

The angular weight `sEta θ = sin(2θ)^{-η}` (`η = 99/100`, `Iθ = [0, π/2]`) satisfies `sEta ≥ 1`
on the open interval `(0, π/2)` (and the two endpoints are null), so the weighted energy
`∫_{Iθ} g² sEta` dominates the *unweighted* energy `∫_[a,b] g²` for every subinterval
`[a,b] ⊆ Iθ`.  Combined with the elementary Cauchy–Schwarz inequality for interval integrals
(`Work.FTS.H2.DivQ.sqIntervalIntegralLe`) and `b - a ≤ π/2`, this gives

  `(∫_a^b g)² ≤ (π/2) · ∫_{Iθ} g² sEta`.

The hypothesis `IntegrableOn (g² sEta) Iθ` forces `g²` (hence `g`) itself to be integrable on
`Iθ`, because `sEta ≥ 1` a.e. there: this is what makes all the interval integrals below the
honest ones (no junk value `0`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Mine

set_option autoImplicit false
set_option linter.style.haveILetI false

/-- On the open angular interval `(0, π/2)` the weight `sEta = sin(2θ)^{-η}` is at least `1`. -/
private theorem one_le_sEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  show 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h := Real.rpow_le_rpow_of_nonpos hs (Real.sin_le_one (2 * θ))
    (neg_nonpos.mpr Work.Spaces.eta_nonneg)
  rw [Real.one_rpow] at h
  exact h

/-- `sEta` is nonnegative on `Iθ`. -/
private theorem sEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _

theorem cs_interval_le {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ Real.pi / 2) (hab : a ≤ b) :
    (∫ x in a..b, g x) ^ 2
      ≤ (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  -- ## Step 0: the sub-intervals of `[0, π/2]` sit inside `Iθ`, resp. `(0, π/2)`
  have hsub : Set.Ioc a b ⊆ Work.Spaces.Iθ := fun x hx =>
    ⟨le_trans ha (le_of_lt hx.1), le_trans hx.2 hb⟩
  have hIoo_sub : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩
  -- ## Step 1: `sEta ≥ 1` off the two null endpoints
  have haeIθ : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      1 ≤ Work.FTS.EllipticEst.sEta θ := by
    have h1 : ∀ᵐ θ ∂(volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)),
        1 ≤ Work.FTS.EllipticEst.sEta θ := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
      exact one_le_sEta_of_mem_Ioo hθ
    rw [MeasureTheory.restrict_Ioo_eq_restrict_Icc] at h1
    simpa only [Work.Spaces.Iθ] using h1
  have haeIoc : ∀ᵐ θ ∂(volume : Measure ℝ).restrict (Set.Ioc a b),
      1 ≤ Work.FTS.EllipticEst.sEta θ := by
    have h1 : ∀ᵐ θ ∂(volume : Measure ℝ).restrict (Set.Ioo a b),
        1 ≤ Work.FTS.EllipticEst.sEta θ := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
      exact one_le_sEta_of_mem_Ioo (hIoo_sub hθ)
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)) (a := a) (b := b))] at h1
    exact h1
  -- ## Step 2: `g²` is integrable on `Iθ`
  have hg2Iθ : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2) Work.Spaces.Iθ := by
    have hAESM : AEStronglyMeasurable (fun θ => (g θ) ^ 2)
        ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
      have h1 : AEStronglyMeasurable (fun θ => (g θ) ^ 2)
          ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
        (hg.aestronglyMeasurable measurableSet_Ioo).pow 2
      rw [MeasureTheory.restrict_Ioo_eq_restrict_Icc] at h1
      simpa only [Work.Spaces.Iθ] using h1
    refine MeasureTheory.Integrable.mono' hint hAESM ?_
    filter_upwards [haeIθ] with θ hθ
    have h2 : ‖(g θ) ^ 2‖ = (g θ) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [h2]
    exact le_mul_of_one_le_right (sq_nonneg _) hθ
  -- ## Step 3: `g²` and `g` are integrable on `Ioc a b`
  have hg2Ioc : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2) (Set.Ioc a b) :=
    hg2Iθ.mono_set hsub
  have hAESM_Ioc : AEStronglyMeasurable g ((volume : Measure ℝ).restrict (Set.Ioc a b)) := by
    have h1 : AEStronglyMeasurable g ((volume : Measure ℝ).restrict (Set.Ioo a b)) :=
      (hg.mono hIoo_sub).aestronglyMeasurable measurableSet_Ioo
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)) (a := a) (b := b))] at h1
    exact h1
  have hgIoc : MeasureTheory.IntegrableOn g (Set.Ioc a b) := by
    haveI : MeasureTheory.IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioc a b)) :=
      ⟨by
        rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top⟩
    have hmem : MemLp g 2 ((volume : Measure ℝ).restrict (Set.Ioc a b)) :=
      (MeasureTheory.memLp_two_iff_integrable_sq hAESM_Ioc).mpr hg2Ioc
    have hmem1 : MemLp g 1 ((volume : Measure ℝ).restrict (Set.Ioc a b)) :=
      hmem.mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)
    exact MeasureTheory.memLp_one_iff_integrable.mp hmem1
  -- ## Step 4: Cauchy–Schwarz on `[a,b]`
  have hf : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hgIoc
  have hf2 : IntervalIntegrable (fun x => g x ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hg2Ioc
  have hCS := Work.FTS.H2.DivQ.sqIntervalIntegralLe g hab hf hf2
  -- ## Step 5: `∫_a^b g² ≤ ∫_{Iθ} g² sEta`
  have hcmp : (∫ x in a..b, g x ^ 2)
      ≤ (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    rw [intervalIntegral.integral_of_le hab]
    have hstep1 : (∫ x in Set.Ioc a b, g x ^ 2)
        ≤ ∫ x in Set.Ioc a b, g x ^ 2 * Work.FTS.EllipticEst.sEta x := by
      refine MeasureTheory.integral_mono_ae hg2Ioc (hint.mono_set hsub) ?_
      filter_upwards [haeIoc] with θ hθ
      exact le_mul_of_one_le_right (sq_nonneg _) hθ
    have hstep2 : (∫ x in Set.Ioc a b, g x ^ 2 * Work.FTS.EllipticEst.sEta x)
        ≤ (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
      · filter_upwards [MeasureTheory.self_mem_ae_restrict
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ)
      · filter_upwards with x hx using hsub hx
    linarith
  -- ## Step 6: assemble
  have hba : b - a ≤ Real.pi / 2 := by linarith
  have hnn : 0 ≤ ∫ x in a..b, g x ^ 2 :=
    intervalIntegral.integral_nonneg hab fun u _ => sq_nonneg _
  have hpi : 0 ≤ Real.pi / 2 := by positivity
  calc (∫ x in a..b, g x) ^ 2 ≤ (b - a) * (∫ x in a..b, g x ^ 2) := hCS
    _ ≤ (Real.pi / 2) * (∫ x in a..b, g x ^ 2) := mul_le_mul_of_nonneg_right hba hnn
    _ ≤ (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
        mul_le_mul_of_nonneg_left hcmp hpi

end Work.FTS.EllipticEst.Mine
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.HardyFin.divSinPrimitiveDeriv_fin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.HardyFin

open scoped Topology

/-- The inductive core of `divSinPrimitiveDeriv_fin`, stated for an abstract function `H` that
agrees with `f / ·` on `(0,x₁)` and is `C^{N+2}` there.  Finite-order version of
`Work.FTS.H2.DivQ.divSinPrimitiveDeriv_aux`. -/
lemma divSinPrimitiveDeriv_aux_fin (x₁ : ℝ) (f H : ℝ → ℝ) (N : ℕ)
    (hf : ContDiffOn ℝ ((N + 2 : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁))
    (hHs : ContDiffOn ℝ ((N + 2 : ℕ) : WithTop ℕ∞) H (Set.Ioo 0 x₁))
    (hHv : ∀ y ∈ Set.Ioo 0 x₁, H y = f y / y) :
    ∀ j : ℕ, j ≤ N →
      (∀ x ∈ Set.Ioo 0 x₁,
        HasDerivAt (fun t : ℝ => t ^ (j + 1) * iteratedDeriv j H t)
          (x ^ j * iteratedDeriv (j + 1) f x) x) ∧
      (∀ y ∈ Set.Ioo 0 x₁,
        y ^ (j + 2) * iteratedDeriv (j + 1) H y
          = y ^ (j + 1) * iteratedDeriv (j + 1) f y
            - (j + 1) * (y ^ (j + 1) * iteratedDeriv j H y)) := by
  have hfI : ContDiffOn ℝ ((N + 2 : ℕ) : WithTop ℕ∞) f (Set.Ioo 0 x₁) :=
    hf.mono Set.Ioo_subset_Ioc_self
  have hfAt : ∀ x ∈ Set.Ioo 0 x₁, ContDiffAt ℝ ((N + 2 : ℕ) : WithTop ℕ∞) f x :=
    fun x hx => hfI.contDiffAt (isOpen_Ioo.mem_nhds hx)
  have hHAt : ∀ x ∈ Set.Ioo 0 x₁, ContDiffAt ℝ ((N + 2 : ℕ) : WithTop ℕ∞) H x :=
    fun x hx => hHs.contDiffAt (isOpen_Ioo.mem_nhds hx)
  have hlt : ∀ n : ℕ, n ≤ N → (n : WithTop ℕ∞) < ((N + 2 : ℕ) : WithTop ℕ∞) :=
    fun n hn => by exact_mod_cast (by omega : n < N + 2)
  have hdf : ∀ (n : ℕ) (x : ℝ), n ≤ N → x ∈ Set.Ioo 0 x₁ →
      HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f x) x :=
    fun n x hn hx =>
      Work.FTS.H2.DivQ.hasDerivAt_iteratedDeriv_of_contDiffAt (hfAt x hx) (hlt n hn)
  have hdH : ∀ (n : ℕ) (x : ℝ), n ≤ N → x ∈ Set.Ioo 0 x₁ →
      HasDerivAt (iteratedDeriv n H) (iteratedDeriv (n + 1) H x) x :=
    fun n x hn hx =>
      Work.FTS.H2.DivQ.hasDerivAt_iteratedDeriv_of_contDiffAt (hHAt x hx) (hlt n hn)
  intro j
  induction j with
  | zero =>
    intro _
    have hbase : ∀ x ∈ Set.Ioo 0 x₁,
        HasDerivAt (fun t : ℝ => t * H t) (iteratedDeriv 1 f x) x := by
      intro x hx
      have hfe : HasDerivAt f (iteratedDeriv 1 f x) x := by
        simpa using hdf 0 x (Nat.zero_le N) hx
      have hcongr : (fun t : ℝ => t * H t) =ᶠ[𝓝 x] f := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
        rw [hHv t ht]
        exact mul_div_cancel₀ (f t) (ne_of_gt ht.1)
      exact (hcongr.hasDerivAt_iff).mpr hfe
    constructor
    · intro x hx; simpa using hbase x hx
    · intro y hy
      have hA0 := hbase y hy
      have hHd : HasDerivAt H (iteratedDeriv 1 H y) y := by
        simpa using hdH 0 y (Nat.zero_le N) hy
      have hmul : HasDerivAt (fun t : ℝ => t * H t) (1 * H y + y * iteratedDeriv 1 H y) y := by
        have := (hasDerivAt_id y).mul hHd
        exact this
      have heq : 1 * H y + y * iteratedDeriv 1 H y = iteratedDeriv 1 f y := hmul.unique hA0
      have hgoal : y ^ 2 * iteratedDeriv 1 H y = y * iteratedDeriv 1 f y - 1 * (y * H y) := by
        linear_combination (y : ℝ) * heq
      simpa using hgoal
  | succ j ih =>
    intro hj
    obtain ⟨hAj, hBj⟩ := ih (by omega)
    have hA1 : ∀ x ∈ Set.Ioo 0 x₁,
        HasDerivAt (fun t : ℝ => t ^ ((j + 1) + 1) * iteratedDeriv (j + 1) H t)
          (x ^ (j + 1) * iteratedDeriv ((j + 1) + 1) f x) x := by
      intro x hx
      have hp : HasDerivAt (fun t : ℝ => t ^ (j + 1)) (((j : ℝ) + 1) * x ^ j) x := by
        have h := hasDerivAt_pow (j + 1) x
        rw [show (j + 1) - 1 = j from by omega] at h
        push_cast at h
        exact h
      have hd : HasDerivAt (iteratedDeriv (j + 1) f) (iteratedDeriv ((j + 1) + 1) f x) x :=
        hdf (j + 1) x hj hx
      have h1 : HasDerivAt (fun t : ℝ => t ^ (j + 1) * iteratedDeriv (j + 1) f t)
          (((j : ℝ) + 1) * x ^ j * iteratedDeriv (j + 1) f x
            + x ^ (j + 1) * iteratedDeriv ((j + 1) + 1) f x) x := by
        exact hp.mul hd
      have hVj : HasDerivAt (fun t : ℝ => ((j : ℝ) + 1) * (t ^ (j + 1) * iteratedDeriv j H t))
          (((j : ℝ) + 1) * (x ^ j * iteratedDeriv (j + 1) f x)) x :=
        (hAj x hx).const_mul ((j : ℝ) + 1)
      have hW : HasDerivAt
          (fun t : ℝ => t ^ (j + 1) * iteratedDeriv (j + 1) f t
            - ((j : ℝ) + 1) * (t ^ (j + 1) * iteratedDeriv j H t))
          (x ^ (j + 1) * iteratedDeriv ((j + 1) + 1) f x) x := by
        have hsub := h1.sub hVj
        convert hsub using 1
        ring
      have hev : (fun t : ℝ => t ^ ((j + 1) + 1) * iteratedDeriv (j + 1) H t)
          =ᶠ[𝓝 x]
          (fun t : ℝ => t ^ (j + 1) * iteratedDeriv (j + 1) f t
            - ((j : ℝ) + 1) * (t ^ (j + 1) * iteratedDeriv j H t)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
        simpa using hBj t ht
      exact hW.congr_of_eventuallyEq hev
    constructor
    · intro x hx; exact hA1 x hx
    · intro y hy
      have hAj1 := hA1 y hy
      have hDH1 : HasDerivAt (iteratedDeriv (j + 1) H) (iteratedDeriv ((j + 1) + 1) H y) y :=
        hdH (j + 1) y hj hy
      have hp1 : HasDerivAt (fun t : ℝ => t ^ ((j + 1) + 1)) (((j : ℝ) + 2) * y ^ (j + 1)) y := by
        have h := hasDerivAt_pow ((j + 1) + 1) y
        rw [show ((j + 1) + 1) - 1 = j + 1 from by omega] at h
        push_cast at h
        convert h using 1
        ring
      have hmul : HasDerivAt (fun t : ℝ => t ^ ((j + 1) + 1) * iteratedDeriv (j + 1) H t)
          (((j : ℝ) + 2) * y ^ (j + 1) * iteratedDeriv (j + 1) H y
            + y ^ ((j + 1) + 1) * iteratedDeriv ((j + 1) + 1) H y) y := by
        exact hp1.mul hDH1
      have heq := hmul.unique hAj1
      push_cast
      linear_combination (y : ℝ) * heq

/-- Finite-order version of `Work.FTS.H2.DivQ.divSinPrimitiveDeriv`
(`Submission/Work/FTS/H2/DivQ/divSinPrimitiveDeriv.lean`), where the `C^∞` hypothesis
`ContDiffOn ℝ (⊤ : ℕ∞) f (Ioc 0 x₁)` is replaced by `ContDiffOn ℝ ((N+2 : ℕ) : WithTop ℕ∞) f (Ioc 0 x₁)`
for a *finite* order `N + 2`, and the two conclusions are asserted only for levels `j ≤ N`.

Adaptation instructions: copy `divSinPrimitiveDeriv_aux` and `divSinPrimitiveDeriv` from the
original file `Submission/Work/FTS/H2/DivQ/divSinPrimitiveDeriv.lean` (import it: it contains the
helper `Work.FTS.H2.DivQ.hasDerivAt_iteratedDeriv_of_contDiffAt`, which is already stated for an
arbitrary order `N : WithTop ℕ∞` and is to be reused unchanged). Replace
`hfAt x hx : ContDiffAt ℝ (⊤ : ℕ∞) f x` by
`ContDiffAt ℝ (((N+2 : ℕ)) : WithTop ℕ∞) f x` (obtained from
`(hf.mono Set.Ioo_subset_Ioc_self).contDiffAt (isOpen_Ioo.mem_nhds hx)`) and the analogous `hHAt`
for `H = fun y => f y / y` (which is `C^{N+2}` on `Ioo 0 x₁` as a quotient of two such functions,
`ContDiffOn.div` with `contDiffOn_id`), and replace the proof
`hlt n : (n : WithTop ℕ∞) < (↑(⊤ : ℕ∞) : WithTop ℕ∞)` by
`hlt n (hn : n ≤ N) : (n : WithTop ℕ∞) < ((N+2 : ℕ) : WithTop ℕ∞)` proved by
`exact_mod_cast (by omega : n < N + 2)`. The induction on `j` becomes an induction with the extra
hypothesis `j ≤ N`, `ih : j ≤ N → P j`, and every use of `hdf`/`hdH` at level `n` must be
accompanied by `n ≤ N`. Formally, `P j` is the conjunction of

* `∀ x ∈ Set.Ioo 0 x₁, HasDerivAt (fun t : ℝ => t ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) t) (x ^ j * iteratedDeriv (j + 1) f x) x`
* `∀ y ∈ Set.Ioo 0 x₁, y ^ (j + 2) * iteratedDeriv (j + 1) (fun y : ℝ => f y / y) y = y ^ (j + 1) * iteratedDeriv (j + 1) f y - (j + 1) * (y ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) y)`

and the step from `j` to `j+1` uses `hdf (j+1)` (needing `j + 1 ≤ N`) and `hdH (j+1)`
(needing `j + 1 ≤ N`). -/
theorem divSinPrimitiveDeriv_fin (x₁ : ℝ) (hx₁ : 0 < x₁) (N : ℕ) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ ((N + 2 : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁) →
      (∀ (j : ℕ) (x : ℝ), j ≤ N → x ∈ Set.Ioo 0 x₁ →
        HasDerivAt (fun t : ℝ => t ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) t)
          (x ^ j * iteratedDeriv (j + 1) f x) x) ∧
      (∀ (j : ℕ) (y : ℝ), j ≤ N → y ∈ Set.Ioo 0 x₁ →
        y ^ (j + 2) * iteratedDeriv (j + 1) (fun y : ℝ => f y / y) y
          = y ^ (j + 1) * iteratedDeriv (j + 1) f y
            - (j + 1) * (y ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) y)) := by
  intro f hf
  set H : ℝ → ℝ := fun y : ℝ => f y / y with hHdef
  have hfm : ContDiffOn ℝ ((N + 2 : ℕ) : WithTop ℕ∞) f (Set.Ioo 0 x₁) :=
    hf.mono Set.Ioo_subset_Ioc_self
  have hHs : ContDiffOn ℝ ((N + 2 : ℕ) : WithTop ℕ∞) H (Set.Ioo 0 x₁) := by
    rw [hHdef]
    have hid : ContDiffOn ℝ ((N + 2 : ℕ) : WithTop ℕ∞) (fun y : ℝ => y) (Set.Ioo 0 x₁) :=
      contDiffOn_id
    have hdiv := hfm.div hid
      (fun x hx => by simp only [Set.mem_Ioo] at hx; exact ne_of_gt hx.1)
    have hfun : (f / fun y : ℝ => y) = fun y : ℝ => f y / y := by
      funext y; rw [Pi.div_apply]
    rw [hfun] at hdiv
    exact hdiv
  have hHv : ∀ y ∈ Set.Ioo 0 x₁, H y = f y / y := by
    intro y hy; rw [hHdef]
  have hmain := divSinPrimitiveDeriv_aux_fin x₁ f H N hf hHs hHv
  constructor
  · intro j x hj hx; exact (hmain j hj).1 x hx
  · intro j y hj hy; exact (hmain j hj).2 y hy

end Work.FTS.EllipticEst.remov.HardyFin
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.HardyFin.divSinPrimitiveVanish_fin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.HardyFin

open MeasureTheory Filter Set
open scoped Topology

/-- Finite-order version of the private base case `Work.FTS.H2.DivQ.van_baseCase` of
`Submission/Work/FTS/H2/DivQ/divSinPrimitiveVanish.lean`: the `C^∞` hypothesis is replaced by
`ContDiffOn ℝ (N : ℕ∞ω) f (Ioc 0 x₁)`, and the order `N` is assumed `≥ k + 1`.  The smoothness is
used only at `iteratedDeriv (k+1) f`, through `continuousOn_iteratedDeriv_Icc_fin` and
`intervalIntegral_iteratedDeriv_succ_fin`. -/
private lemma van_baseCase_fin (k : ℕ) (hk : 1 ≤ k) {γ x₁ : ℝ} (hx₁ : 0 < x₁) (hγ : -1 < γ)
    {N : ℕ} (hN : k + 1 ≤ N) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁))
    (hB : IntegrableOn (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    Filter.Tendsto (fun x : ℝ => x ^ k * iteratedDeriv k f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  -- the tail of the weighted integral is small for small `δ`
  have hΨ : Filter.Tendsto
      (fun δ : ℝ => ∫ y in Set.Ioc 0 δ, y ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f y) ^ 2)
      (nhds 0) (nhds 0) := Work.FTS.H2.DivQ.hardyIter_tendsto_zero hx₁ hB
  have hEv₁ : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (∫ y in Set.Ioc 0 δ, y ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f y) ^ 2) < ε / 4 :=
    Filter.Tendsto.eventually_lt (hΨ.mono_left nhdsWithin_le_nhds) tendsto_const_nhds
      (by linarith)
  have hEv₂ : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ := self_mem_nhdsWithin
  have hEv₃ : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ < x₁ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hx₁)
  obtain ⟨δ, hδpos, hδx, hδsmall⟩ := (hEv₂.and (hEv₃.and hEv₁)).exists
  -- the two decay inputs at the level of `x`
  have hq : 0 < ((2 * k : ℕ) : ℝ) + (γ - 2 * (k : ℝ)) + 1 := by
    have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
    rw [hcast]; linarith
  have hA : Filter.Tendsto
      (fun x : ℝ => (x ^ (2 * k) / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 := Work.FTS.H2.DivQ.van_powMul_rpow_integral (2 * k) (γ - 2 * (k : ℝ))
      (by omega) hq hδpos
    have h := h0.const_mul (1 / 2 : ℝ)
    refine Filter.Tendsto.congr' ?_ (by simpa using h)
    filter_upwards with x
    ring
  have hA' : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (x ^ (2 * k) / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ))) < ε / 2 :=
    Filter.Tendsto.eventually_lt hA tendsto_const_nhds (by linarith)
  have hC : Filter.Tendsto (fun x : ℝ => x ^ k * |iteratedDeriv k f δ|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hid : Filter.Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have h := (hid.pow k).mul_const |iteratedDeriv k f δ|
    simpa [zero_pow (by omega : k ≠ 0)] using h
  have hC' : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
      x ^ k * |iteratedDeriv k f δ| < ε / 4 :=
    Filter.Tendsto.eventually_lt hC tendsto_const_nhds (by linarith)
  filter_upwards [Ioo_mem_nhdsGT hδpos, hA', hC'] with x hx hxA hxC
  have hxk : 0 < x ^ k := pow_pos hx.1 k
  have hxδ : x ≤ δ := hx.2.le
  -- fundamental theorem of calculus
  have hFTC : iteratedDeriv k f x
      = iteratedDeriv k f δ - ∫ s in x..δ, iteratedDeriv (k + 1) f s := by
    have h := intervalIntegral_iteratedDeriv_succ_fin hf (j := k) hN hx.1 hxδ hδx
    linarith
  have hI : |∫ s in x..δ, iteratedDeriv (k + 1) f s|
      ≤ ∫ s in x..δ, |iteratedDeriv (k + 1) f s| :=
    intervalIntegral.abs_integral_le_integral_abs hxδ
  have hFx : |iteratedDeriv k f x|
      ≤ |iteratedDeriv k f δ| + ∫ s in x..δ, |iteratedDeriv (k + 1) f s| := by
    have h := abs_add_le (iteratedDeriv k f δ) (-(∫ s in x..δ, iteratedDeriv (k + 1) f s))
    rw [hFTC]
    calc |iteratedDeriv k f δ - ∫ s in x..δ, iteratedDeriv (k + 1) f s|
        ≤ |iteratedDeriv k f δ| + |∫ s in x..δ, iteratedDeriv (k + 1) f s| := by
          simpa [sub_eq_add_neg, abs_neg] using h
      _ ≤ |iteratedDeriv k f δ| + ∫ s in x..δ, |iteratedDeriv (k + 1) f s| := by linarith [hI]
  -- the weighted AM–GM bound
  have hcontG : ContinuousOn (iteratedDeriv (k + 1) f) (Set.Icc x δ) :=
    continuousOn_iteratedDeriv_Icc_fin hf (j := k + 1) hN hx.1 hδx
  have hamgm := Work.FTS.H2.DivQ.van_amgm_integral (iteratedDeriv (k + 1) f)
    (e := γ - 2 * (k : ℝ)) (a := x ^ k) hxk hx.1 hxδ hcontG
  simp only [show -(γ - 2 * (k : ℝ)) = 2 * (k : ℝ) - γ from by ring] at hamgm
  -- the bound on the last term of the displayed estimate
  have hTle : (1 / 2) * (∫ s in x..δ,
        s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2)
      ≤ (1 / 2) * (∫ y in Set.Ioc 0 δ,
        y ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f y) ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [intervalIntegral.integral_of_le hxδ]
    exact Work.FTS.H2.DivQ.van_setIntegral_mono_Ioc hx.1
      (hB.mono_set (Set.Ioc_subset_Ioc le_rfl hδx.le))
      fun y hy => mul_nonneg (Real.rpow_nonneg (le_of_lt hy.1) _) (sq_nonneg _)
  -- assemble
  have hstep : x ^ k * |iteratedDeriv k f x|
      ≤ x ^ k * |iteratedDeriv k f δ|
        + (x ^ (2 * k) / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ)))
        + (1 / 2) * (∫ s in x..δ,
            s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2) := by
    have h1 : x ^ k * |iteratedDeriv k f x|
        ≤ x ^ k * (|iteratedDeriv k f δ| + ∫ s in x..δ, |iteratedDeriv (k + 1) f s|) :=
      mul_le_mul_of_nonneg_left hFx (le_of_lt hxk)
    have h2 : x ^ k * (|iteratedDeriv k f δ| + ∫ s in x..δ, |iteratedDeriv (k + 1) f s|)
        ≤ x ^ k * (|iteratedDeriv k f δ|
          + ((x ^ k / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ)))
            + (1 / (2 * x ^ k)) * (∫ s in x..δ,
                s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2))) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hxk)
      linarith [hamgm]
    have h3 : x ^ k * (|iteratedDeriv k f δ|
          + ((x ^ k / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ)))
            + (1 / (2 * x ^ k)) * (∫ s in x..δ,
                s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2)))
        = x ^ k * |iteratedDeriv k f δ|
          + (x ^ (2 * k) / 2) * (∫ s in x..δ, s ^ (γ - 2 * (k : ℝ)))
          + (1 / 2) * (∫ s in x..δ,
              s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2) := by
      have hkk : x ^ (2 * k) = x ^ k * x ^ k := by
        rw [show 2 * k = k + k by omega, pow_add]
      rw [hkk]
      have hxne : x ^ k ≠ 0 := ne_of_gt hxk
      field_simp
      ring
    linarith [h1, h2, le_of_eq h3]
  have hTsmall : (1 / 2) * (∫ y in Set.Ioc 0 δ,
      y ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f y) ^ 2) < ε / 8 := by
    linarith
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg (le_of_lt hxk)]
  linarith [hstep, hxA, hxC, hTle, hTsmall]

/-- Finite-order version of the private induction step `Work.FTS.H2.DivQ.van_step` of
`Submission/Work/FTS/H2/DivQ/divSinPrimitiveVanish.lean`: the `C^∞` hypothesis is replaced by
`ContDiffOn ℝ (N : ℕ∞ω) f (Ioc 0 x₁)`, and the order `N` is assumed `≥ j + 1`.  The smoothness is
used only at `iteratedDeriv (j+1) f`. -/
private lemma van_step_fin (j : ℕ) (hj : 1 ≤ j) {N : ℕ} (hjN : j + 1 ≤ N) {f : ℝ → ℝ}
    {x₁ : ℝ} (hx₁ : 0 < x₁)
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁))
    (h : Filter.Tendsto (fun t : ℝ => t ^ (j + 1) * iteratedDeriv (j + 1) f t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto (fun x : ℝ => x ^ j * iteratedDeriv j f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hjn : ((j : ℝ) ≠ 0) := by positivity
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  -- the limit hypothesis, in interval form
  have hεj : (0 : ℝ) < ε * (j : ℝ) / 2 := by positivity
  have hev := Metric.tendsto_nhds.mp h (ε * (j : ℝ) / 2) hεj
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hev
  set δ : ℝ := min (δ₀ / 2) (x₁ / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδlt₀ : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδx : δ < x₁ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- the tail bound against the model integral `∫_x^δ t^{-(j+1)}`
  have htail : ∀ x : ℝ, 0 < x → x ≤ δ →
      x ^ j * (∫ s in x..δ, |iteratedDeriv (j + 1) f s|) ≤ ε / 2 := by
    intro x hxpos hxδ
    have hxj : 0 < x ^ j := pow_pos hxpos j
    -- pointwise bound from the limit hypothesis
    have hbd : ∀ t ∈ Set.Icc x δ,
        |iteratedDeriv (j + 1) f t| ≤ (ε * (j : ℝ) / 2) * (t : ℝ) ^ (-((j : ℝ) + 1)) := by
      intro t ht
      have htpos : 0 < t := lt_of_lt_of_le hxpos ht.1
      have htδ₀ : t ∈ Set.Ioo (0 : ℝ) δ₀ := ⟨htpos, lt_of_le_of_lt ht.2 hδlt₀⟩
      have h1 := hδ₀ htδ₀
      rw [Real.dist_eq, sub_zero] at h1
      have h2 : |iteratedDeriv (j + 1) f t| * (t : ℝ) ^ (j + 1) < ε * (j : ℝ) / 2 := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt htpos) (j + 1)),
          mul_comm ((t : ℝ) ^ (j + 1))] at h1
        exact h1
      have h3 := mul_lt_mul_of_pos_right h2 (inv_pos.mpr (pow_pos htpos (j + 1)))
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos htpos (j + 1))), mul_one] at h3
      have hbase : (t : ℝ) ^ ((j : ℝ) + 1) = (t : ℝ) ^ (j + 1) := by
        have hcast : ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
        rw [hcast, Real.rpow_natCast]
      have hpow : (t : ℝ) ^ (-((j : ℝ) + 1)) = ((t : ℝ) ^ (j + 1))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt htpos) ((j : ℝ) + 1), hbase]
      rw [hpow]
      exact h3.le
    have hint1 : IntervalIntegrable (fun s : ℝ => |iteratedDeriv (j + 1) f s|) volume x δ :=
      ((continuousOn_iteratedDeriv_Icc_fin hf (j := j + 1) hjN hxpos hδx).abs).intervalIntegrable_of_Icc
        (μ := volume) hxδ
    have hcontw : ContinuousOn (fun s : ℝ => (ε * (j : ℝ) / 2) * s ^ (-((j : ℝ) + 1)))
        (Set.Icc x δ) :=
      continuousOn_const.mul (continuousOn_id.rpow_const fun s hs =>
        Or.inl (ne_of_gt (lt_of_lt_of_le hxpos hs.1)))
    have hint2 : IntervalIntegrable (fun s : ℝ => (ε * (j : ℝ) / 2) * s ^ (-((j : ℝ) + 1)))
        volume x δ := hcontw.intervalIntegrable_of_Icc (μ := volume) hxδ
    have hmono := intervalIntegral.integral_mono_on hxδ hint1 hint2 hbd
    rw [intervalIntegral.integral_const_mul] at hmono
    -- evaluate the model integral
    have hnozero : (0 : ℝ) ∉ Set.uIcc x δ := by
      rw [Set.uIcc_of_le hxδ]
      intro hmem
      exact absurd hmem.1 (not_le.mpr hxpos)
    have hne : -((j : ℝ) + 1) ≠ -1 := by
      intro hc
      exact hjn (by linarith)
    have hval : (∫ s in x..δ, s ^ (-((j : ℝ) + 1)))
        = ((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ))) / (j : ℝ) := by
      rw [integral_rpow (Or.inr ⟨hne, hnozero⟩)]
      have hr : (-((j : ℝ) + 1) + 1) = -(j : ℝ) := by ring
      rw [hr]
      ring
    rw [hval] at hmono
    -- multiply by `x ^ j`
    have hxd : x ^ j * ((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ))) ≤ 1 := by
      rw [Real.rpow_neg (le_of_lt hxpos) (j : ℝ), Real.rpow_neg (le_of_lt hδpos) (j : ℝ),
        Real.rpow_natCast, Real.rpow_natCast]
      have hδj : 0 < δ ^ j := pow_pos hδpos j
      have hxinv : x ^ j * (x ^ j)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hxj)
      have hnonneg : 0 ≤ x ^ j * (δ ^ j)⁻¹ := mul_nonneg hxj.le (inv_nonneg.mpr hδj.le)
      nlinarith [hxinv, hnonneg]
    have hstep1 : x ^ j * ((ε * (j : ℝ) / 2) * (((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ)))
        / (j : ℝ))) ≤ ε / 2 := by
      have hrw : x ^ j * ((ε * (j : ℝ) / 2) * (((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ)))
          / (j : ℝ))) = (ε / 2) * (x ^ j * ((x : ℝ) ^ (-(j : ℝ)) - (δ : ℝ) ^ (-(j : ℝ)))) := by
        field_simp
      rw [hrw]
      nlinarith [hxd, hε]
    exact (mul_le_mul_of_nonneg_left hmono hxj.le).trans hstep1
  -- eventually the `δ`-term is small
  have hfin : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
      x ^ j * |iteratedDeriv j f δ| < ε / 2 := by
    have hid : Filter.Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hh := (hid.pow j).mul_const |iteratedDeriv j f δ|
    have hh' : Filter.Tendsto (fun x : ℝ => x ^ j * |iteratedDeriv j f δ|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa [zero_pow (by omega : j ≠ 0)] using hh
    exact Filter.Tendsto.eventually_lt hh' tendsto_const_nhds (by linarith)
  filter_upwards [Ioo_mem_nhdsGT hδpos, hfin] with x hx hxfin
  have hxpos : 0 < x := hx.1
  have hxδ : x ≤ δ := hx.2.le
  have hxj : 0 < x ^ j := pow_pos hxpos j
  have hFTC : iteratedDeriv j f x
      = iteratedDeriv j f δ - ∫ s in x..δ, iteratedDeriv (j + 1) f s := by
    have hh := intervalIntegral_iteratedDeriv_succ_fin hf (j := j) hjN hxpos hxδ hδx
    linarith
  have hI : |∫ s in x..δ, iteratedDeriv (j + 1) f s|
      ≤ ∫ s in x..δ, |iteratedDeriv (j + 1) f s| :=
    intervalIntegral.abs_integral_le_integral_abs hxδ
  have hFx : |iteratedDeriv j f x|
      ≤ |iteratedDeriv j f δ| + ∫ s in x..δ, |iteratedDeriv (j + 1) f s| := by
    have hh := abs_add_le (iteratedDeriv j f δ) (-(∫ s in x..δ, iteratedDeriv (j + 1) f s))
    rw [hFTC]
    calc |iteratedDeriv j f δ - ∫ s in x..δ, iteratedDeriv (j + 1) f s|
        ≤ |iteratedDeriv j f δ| + |∫ s in x..δ, iteratedDeriv (j + 1) f s| := by
          simpa [sub_eq_add_neg, abs_neg] using hh
      _ ≤ |iteratedDeriv j f δ| + ∫ s in x..δ, |iteratedDeriv (j + 1) f s| := by linarith [hI]
  have htail' := htail x hxpos hxδ
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg hxj.le]
  linarith [mul_le_mul_of_nonneg_left hFx hxj.le, htail', hxfin]

/-- Finite-order version of `Work.FTS.H2.DivQ.divSinPrimitiveVanish`
(`Submission/Work/FTS/H2/DivQ/divSinPrimitiveVanish.lean`), where the `C^∞` hypothesis
`ContDiffOn ℝ (⊤ : ℕ∞) f (Ioc 0 x₁)` is replaced by `ContDiffOn ℝ ((N:ℕ) : WithTop ℕ∞) f (Ioc 0 x₁)`
for a *finite* order `N`, assumed `≥ k+1`.

Adaptation instructions: the original file's proof goes through verbatim. Only two of its
ingredients need finite-order replacements (available in
`Submission/Work/FTS/EllipticEst/remov/HardyFin/Basic.lean`, namespace
`Work.FTS.EllipticEst.remov.HardyFin`):

* `Work.FTS.H2.DivQ.continuousOn_iteratedDeriv_Icc`  ⟶ `continuousOn_iteratedDeriv_Icc_fin`
  (`hf : ContDiffOn ℝ ((N:ℕ) : WithTop ℕ∞) f (Ioc 0 x₁)`, `{j} (hj : j ≤ N)`, `ha : 0 < a`,
   `hb : b < x₁`);
* `Work.FTS.H2.DivQ.intervalIntegral_iteratedDeriv_succ` ⟶ `intervalIntegral_iteratedDeriv_succ_fin`
  (same conventions, with `(hj : j + 1 ≤ N)`).

Reusable verbatim (no smoothness hypothesis): `Work.FTS.H2.DivQ.van_powMul_rpow_integral`,
`Work.FTS.H2.DivQ.van_amgm_integral`, `Work.FTS.H2.DivQ.van_setIntegral_mono_Ioc`,
`Work.FTS.H2.DivQ.hardyIter_tendsto_zero`, `Work.FTS.H2.DivQ.two_mul_le_mul_sq_add_div_sq`.
The two private lemmas `van_baseCase` and `van_step` of the original file are to be copied with
`ContDiffOn ℝ (⊤ : ℕ∞) f (Ioc 0 x₁)` replaced by `ContDiffOn ℝ ((N:ℕ) : WithTop ℕ∞) f (Ioc 0 x₁)`
together with the extra `hN : k + 1 ≤ N` (in `van_baseCase`) and `hjN : j + 1 ≤ N` (in `van_step`),
and each call of the two ⊤-lemmas replaced by its `_fin` counterpart. In `van_baseCase` the
smoothness is used at `iteratedDeriv (k+1) f` only; in `van_step` at `iteratedDeriv (j+1) f`.
The hypothesis `hN`/`hjN` should be derived from `1 ≤ j` and `j ≤ k` when the lemmas are called
from the main downward induction (`key`), so that the main induction needs no changes. -/
theorem divSinPrimitiveVanish_fin (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ)
    (N : ℕ) (hN : k + 1 ≤ N) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁) →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
        (Set.Ioc 0 x₁) →
      ∀ j : ℕ, 1 ≤ j → j ≤ k →
        Filter.Tendsto (fun x : ℝ => x ^ j * iteratedDeriv j f x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro f hf hB j hj1 hjk
  have key : ∀ n : ℕ, ∀ j : ℕ, k - j ≤ n → 1 ≤ j → j ≤ k →
      Filter.Tendsto (fun x : ℝ => x ^ j * iteratedDeriv j f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro n
    induction n with
    | zero =>
      intro j hle hj1 hjk
      have hjk' : j = k := by omega
      subst j
      exact van_baseCase_fin k hj1 hx₁ hγ hN hf hB
    | succ n ih =>
      intro j hle hj1 hjk
      rcases Nat.lt_or_ge (k - j) (n + 1) with hlt | hge
      · exact ih j (Nat.lt_succ_iff.mp hlt) hj1 hjk
      · exact van_step_fin j hj1 (by omega) hx₁ hf (ih (j + 1) (by omega) (by omega) (by omega))
  exact key k j (Nat.sub_le k j) hj1 hjk

end Work.FTS.EllipticEst.remov.HardyFin
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.SliceLzeroHonest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

open scoped Real Topology
open MeasureTheory Set Filter


end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.integrableOn_DzIter_sq_mul_sEta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

theorem integrableOn_DzIter_sq_mul_sEta {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k g) (i : ℕ) (hi : i ≤ k) {z : ℝ} (hz : 0 < z)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => (Work.Spaces.DzIter i g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter i g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  -- the radial weight is positive, so its square is invertible
  have hwpos : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]; positivity
  have hw2ne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hwpos)
  set c : ℝ := ((Work.Spaces.w z) ^ 2)⁻¹ with hc
  have hcnonneg : 0 ≤ c := by rw [hc]; positivity
  -- dominate by `c · HkIntegrand`, which is integrable on the angular slice
  refine MeasureTheory.Integrable.mono' ((hmem.1 z hzI).const_mul c) haesm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
  have hE : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
    rw [Work.FTS.EllipticEst.sEta]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hE)]
  -- the weighted summand is a nonnegative summand of `HkIntegrand`
  have hT := Work.Spaces.sq_le_HkIntegrand_z α k g z θ i hi
  rw [Work.FTS.EllipticEst.mul_w_sin_rpow_sq (Work.Spaces.DzIter i g z θ) (Work.Spaces.w z) hθ]
    at hT
  have hcW : c * (Work.Spaces.w z) ^ 2 = 1 := by rw [hc]; exact inv_mul_cancel₀ hw2ne
  calc (Work.Spaces.DzIter i g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (c * (Work.Spaces.w z) ^ 2)
          * ((Work.Spaces.DzIter i g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
        rw [hcW, one_mul]
    _ = c * ((Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ) := by ring
    _ ≤ c * Work.Spaces.HkIntegrand α k g z θ := mul_le_mul_of_nonneg_left hT hcnonneg

end Work.FTS.EllipticEst.remov.SourceBound
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.abs_le_tail_of_bounded_double_primitive =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory intervalIntegral

namespace Work.FTS.EllipticEst.remov

/-- Local version of the fundamental-theorem-of-calculus tail bound for a function whose
`abs` is known to be integrable. -/
theorem abs_sub_le_tail_of_primitive_local {T b θ t : ℝ} (hTb : T < b)
    {Q q : ℝ → ℝ} (hQ : ∀ x ∈ Set.Ioo T b, HasDerivAt Q (q x) x)
    (hq : MeasureTheory.IntegrableOn (fun x => |q x|) (Set.Ioc T b))
    (hθ : θ ∈ Set.Ioo T b) (ht : t ∈ Set.Ioo θ b) :
    |Q t - Q θ| ≤ ∫ x in Set.Ioc θ b, |q x| := by
  have hθt : θ ≤ t := le_of_lt ht.1
  have hsub1 : Set.Ioc θ t ⊆ Set.Ioc T b := fun x hx =>
    ⟨lt_trans hθ.1 hx.1, le_of_lt (lt_of_le_of_lt hx.2 ht.2)⟩
  have hsub2 : Set.Ioc θ b ⊆ Set.Ioc T b := fun x hx => ⟨lt_trans hθ.1 hx.1, hx.2⟩
  have hint1 : MeasureTheory.IntegrableOn (fun x => |q x|) (Set.Ioc θ t) := hq.mono_set hsub1
  have hint2 : MeasureTheory.IntegrableOn (fun x => |q x|) (Set.Icc θ t) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr hint1
  have hmem : ∀ x ∈ Set.Icc θ t, x ∈ Set.Ioo T b := fun x hx =>
    ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 ht.2⟩
  have hcont : ContinuousOn Q (Set.Icc θ t) := fun x hx =>
    (hQ x (hmem x hx)).continuousAt.continuousWithinAt
  have h1 : Q t - Q θ ≤ ∫ y in θ..t, |q y| :=
    intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hθt hcont
      (fun x hx => (hQ x (hmem x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)).hasDerivWithinAt)
      hint2 (fun x hx => le_abs_self _)
  have h2 : Q θ - Q t ≤ ∫ y in θ..t, |q y| := by
    have hh := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hθt hcont.neg
      (fun x hx => (hQ x (hmem x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)).neg.hasDerivWithinAt)
      hint2 (fun x hx => neg_le_abs _)
    simp only [Pi.neg_apply] at hh
    linarith [hh]
  have h3 : |Q t - Q θ| ≤ ∫ y in θ..t, |q y| := abs_sub_le_iff.mpr ⟨h1, h2⟩
  have h4 : (∫ y in θ..t, |q y|) = ∫ y in Set.Ioc θ t, |q y| := integral_of_le hθt
  have h5 : (∫ y in Set.Ioc θ t, |q y|) ≤ ∫ y in Set.Ioc θ b, |q y| :=
    MeasureTheory.setIntegral_mono_set (hq.mono_set hsub2)
      (Filter.Eventually.of_forall (fun x => abs_nonneg _))
      (Filter.Eventually.of_forall (fun x hx => ⟨hx.1, le_of_lt (lt_of_le_of_lt hx.2 ht.2)⟩))
  linarith [h3, h4, h5]

lemma hasDerivAt_log_const_sub {b y : ℝ} (hy : y < b) :
    HasDerivAt (fun z : ℝ => Real.log (b - z)) (-(b - y)⁻¹) y := by
  have h1 : HasDerivAt (fun z : ℝ => b - z) (-1) y := (hasDerivAt_id y).const_sub b
  exact (h1.log (ne_of_gt (sub_pos.mpr hy))).congr_deriv (by simp only [one_div, neg_div])

lemma hasDerivAt_inv_const_sub {b y : ℝ} (hy : y < b) :
    HasDerivAt (fun z : ℝ => (b - z)⁻¹) ((b - y) ^ 2)⁻¹ y := by
  have h0 := ((hasDerivAt_id y).const_sub b).inv (ne_of_gt (sub_pos.mpr hy))
  exact h0.congr_deriv (by simp only [id_eq, one_div, neg_div, neg_neg])

/-- **A bounded function with a "good quotient" second derivative has vanishing quotient.**

Let `T < b`, `2 ≤ p`, `Q, q, F` with `Q' = q` on `(T,b)`, `F` twice differentiable on `(T,b)`
with `F'' = Q / cos^p` there, and `|F| ≤ K` on `[T,b)`. Suppose `cos t > 0` and `cos t ≤ b - t`
on `[T,b)`. Then for every `θ ∈ (T,b)`, `|Q θ| ≤ ∫_{t ∈ (θ,b]} |q t|`.

Proof (contrapositive): if `A := ∫_{θ₀}^b |q| < |Q θ₀|` then (FTC for `Q`) `Q` keeps its sign
`s` on `(θ₀,b)` with `|Q t| ≥ μ := |Q θ₀| - A > 0` there.  Hence `s F'' = |Q|/cos^p ≥
μ (b-t)^{-p}` is positive, so `s F'` is monotone increasing with
`s F'(t) - s F'(θ₀) = ∫_{θ₀}^t s F'' ≥ μ((b-t)^{1-p} - (b-θ₀)^{1-p})/(p-1) =: w t → ∞`, and for
`t` close enough to `b` one has `w t ≥ 2|F' θ₀|`, so on `(t₁,b)` the function `F'` has constant
sign and `|F'| ≥ w/2 ≥ (μ/2)(b-t)^{-1-p...}`; since `∫_{t₁}^b (b-u)^{-p} du = ∞` (as `p ≥ 2`),
`|F(t) - F(t₁)| = ∫_{t₁}^t |F'| → ∞`, contradicting `|F| ≤ K`.  (Integrability of `F'' = Q/cos^p`
on subintervals `[θ, c]`, `c < b`, follows from the bound `|Q| ≤ |Q θ₀| + A` there.) -/
theorem abs_le_tail_of_bounded_double_primitive
    {T b K p : ℝ} (hTb : T < b) (hp : 2 ≤ p)
    (hcos_pos : ∀ t ∈ Set.Ico T b, 0 < Real.cos t)
    (hcos_le : ∀ t ∈ Set.Ico T b, Real.cos t ≤ b - t)
    {Q q F : ℝ → ℝ}
    (hQ : ∀ t ∈ Set.Ioo T b, HasDerivAt Q (q t) t)
    (hq : MeasureTheory.IntegrableOn (fun t => |q t|) (Set.Ioc T b))
    (hF1 : ∀ t ∈ Set.Ioo T b, HasDerivAt F (deriv F t) t)
    (hF2 : ∀ t ∈ Set.Ioo T b, HasDerivAt (deriv F) (deriv (deriv F) t) t)
    (hF2eq : ∀ t ∈ Set.Ioo T b, deriv (deriv F) t = Q t / (Real.cos t) ^ p)
    (hFbd : ∀ t ∈ Set.Ico T b, |F t| ≤ K) :
    ∀ θ ∈ Set.Ioo T b, |Q θ| ≤ ∫ t in Set.Ioc θ b, |q t| := by
  intro θ hθ
  by_contra hcon
  have hAsmall : (∫ t in Set.Ioc θ b, |q t|) < |Q θ| := not_le.mp hcon
  have hTθ : T < θ := hθ.1
  have hθb : θ < b := hθ.2
  set A : ℝ := ∫ t in Set.Ioc θ b, |q t| with hA
  have hμ : 0 < |Q θ| - A := by rw [hA]; linarith
  -- (1) tail bound
  have htail : ∀ t ∈ Set.Ioo θ b, |Q θ| - A ≤ |Q t| := by
    intro t ht
    have h1 : |Q t - Q θ| ≤ A := by
      rw [hA]
      exact abs_sub_le_tail_of_primitive_local hTb hQ hq hθ ht
    have h2 : |Q θ| ≤ |Q θ - Q t| + |Q t| := by
      have h := abs_add_le (Q θ - Q t) (Q t)
      simpa using h
    have h3 : |Q θ - Q t| = |Q t - Q θ| := abs_sub_comm _ _
    linarith
  -- (2) sign
  obtain ⟨s, hs, hsQ⟩ := Work.RemovSign.exists_sign_mul_eq_abs_of_abs_lower_bound hTb
      (fun x hx => (hQ x hx).differentiableAt) hθ hμ htail
  -- (3) choose a
  set a : ℝ := (max θ (b - 1/2) + b) / 2 with ha
  have hθa : θ < a := by
    rw [ha]
    have h : θ ≤ max θ (b - 1/2) := le_max_left _ _
    linarith
  have hab : a < b := by
    rw [ha]
    have h : max θ (b - 1/2) < b := max_lt hθb (by linarith)
    linarith
  have hba : b - a ≤ 1/4 := by
    rw [ha]
    have h : b - 1/2 ≤ max θ (b - 1/2) := le_max_right _ _
    linarith
  -- (4) W and G
  set W : ℝ → ℝ := fun y => s * F y + (|Q θ| - A) * Real.log (b - y) with hW
  set G : ℝ → ℝ := fun y => s * deriv F y - (|Q θ| - A) * (b - y)⁻¹ with hG
  have hWd : ∀ y ∈ Set.Ioo T b, DifferentiableAt ℝ W y := by
    intro y hy
    have h1 : DifferentiableAt ℝ (fun z : ℝ => s * F z) y := ((hF1 y hy).differentiableAt).const_mul s
    have h2 : DifferentiableAt ℝ (fun z : ℝ => (|Q θ| - A) * Real.log (b - z)) y :=
      (hasDerivAt_log_const_sub hy.2).differentiableAt.const_mul (|Q θ| - A)
    rw [hW]
    exact h1.add h2
  have hWderiv : ∀ y ∈ Set.Ioo T b, deriv W y = G y := by
    intro y hy
    have h1 : HasDerivAt (fun z : ℝ => s * F z) (s * deriv F y) y := (hF1 y hy).const_mul s
    have h2 : HasDerivAt (fun z : ℝ => (|Q θ| - A) * Real.log (b - z))
        ((|Q θ| - A) * (-(b - y)⁻¹)) y := (hasDerivAt_log_const_sub hy.2).const_mul (|Q θ| - A)
    have h3 := (h1.add h2).deriv
    rw [hW, hG]
    rw [show (fun z : ℝ => s * F z + (|Q θ| - A) * Real.log (b - z))
        = ((fun z : ℝ => s * F z) + fun z : ℝ => (|Q θ| - A) * Real.log (b - z)) from rfl]
    rw [h3]
    ring
  have hGd : ∀ y ∈ Set.Ioo T b, DifferentiableAt ℝ G y := by
    intro y hy
    have h1 : DifferentiableAt ℝ (fun z : ℝ => s * deriv F z) y :=
      ((hF2 y hy).differentiableAt).const_mul s
    have h2 : DifferentiableAt ℝ (fun z : ℝ => (b - z)⁻¹) y :=
      (hasDerivAt_inv_const_sub hy.2).differentiableAt
    rw [hG]
    exact h1.sub (h2.const_mul (|Q θ| - A))
  have hGderiv : ∀ y ∈ Set.Ioo T b, deriv G y
      = s * deriv (deriv F) y - (|Q θ| - A) * ((b - y) ^ 2)⁻¹ := by
    intro y hy
    have h1 : HasDerivAt (fun z : ℝ => s * deriv F z) (s * deriv (deriv F) y) y :=
      (hF2 y hy).const_mul s
    have h3 : HasDerivAt (fun z : ℝ => (|Q θ| - A) * (b - z)⁻¹)
        ((|Q θ| - A) * ((b - y) ^ 2)⁻¹) y :=
      (hasDerivAt_inv_const_sub hy.2).const_mul (|Q θ| - A)
    have h4 := (h1.sub h3).deriv
    rw [hG]
    rw [show (fun z : ℝ => s * deriv F z - (|Q θ| - A) * (b - z)⁻¹)
        = ((fun z : ℝ => s * deriv F z) - fun z : ℝ => (|Q θ| - A) * (b - z)⁻¹) from rfl]
    rw [h4]
  -- (5) the key pointwise bound
  have hbound : ∀ y ∈ Set.Ioo a b, (|Q θ| - A) * ((b - y) ^ 2)⁻¹ ≤ s * deriv (deriv F) y := by
    intro y hy
    have hyθ : y ∈ Set.Ioo θ b := ⟨lt_trans hθa hy.1, hy.2⟩
    have hyT : y ∈ Set.Ioo T b := ⟨lt_trans hTθ hyθ.1, hyθ.2⟩
    have hyIco : y ∈ Set.Ico T b := ⟨le_of_lt hyT.1, hyT.2⟩
    have hby : 0 < b - y := by linarith [hyθ.2]
    have hkey : s * deriv (deriv F) y = |Q y| / (Real.cos y) ^ p := by
      rw [hF2eq y hyT, mul_div_assoc', hsQ y hyθ]
    have hcosy : 0 < Real.cos y := hcos_pos y hyIco
    have hcosle : Real.cos y ≤ b - y := hcos_le y hyIco
    have hcosp : (Real.cos y) ^ p ≤ (b - y) ^ p :=
      Real.rpow_le_rpow (le_of_lt hcosy) hcosle (by linarith)
    have hcosp2 : (Real.cos y) ^ p ≤ (b - y) ^ 2 := by
      have hbyle : b - y ≤ 1 := by linarith [hy.1, hy.2, hba]
      have h2r : (b - y) ^ p ≤ (b - y) ^ (2:ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hby hbyle hp
      rw [Real.rpow_two] at h2r
      exact le_trans hcosp h2r
    have hpos : 0 < (Real.cos y) ^ p := Real.rpow_pos_of_pos hcosy p
    have hmuQ : |Q θ| - A ≤ |Q y| := htail y hyθ
    have hxnonneg : 0 ≤ |Q θ| - A := le_of_lt hμ
    calc (|Q θ| - A) * ((b - y) ^ 2)⁻¹
        = (|Q θ| - A) / (b - y) ^ 2 := by rw [div_eq_mul_inv]
      _ ≤ (|Q θ| - A) / (Real.cos y) ^ p :=
            div_le_div_of_nonneg_left hxnonneg hpos hcosp2
      _ ≤ |Q y| / (Real.cos y) ^ p :=
            div_le_div_of_nonneg_right hmuQ (le_of_lt hpos)
      _ = s * deriv (deriv F) y := hkey.symm
  -- (6) monotonicity
  have hGdiff : DifferentiableOn ℝ G (Set.Ioo a b) := by
    intro y hy
    exact (hGd y ⟨lt_trans hTθ (lt_trans hθa hy.1), hy.2⟩).differentiableWithinAt
  have hmono : MonotoneOn G (Set.Ioo a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo a b) hGdiff.continuousOn ?_ ?_
    · rw [interior_Ioo]; exact hGdiff
    · intro y hy
      rw [interior_Ioo] at hy
      rw [hGderiv y ⟨lt_trans hTθ (lt_trans hθa hy.1), hy.2⟩]
      linarith [hbound y hy]
  -- (7) auxiliary point a2 in (a,b)
  set a2 : ℝ := (a + b) / 2 with ha2
  have haa2 : a < a2 := by rw [ha2]; linarith
  have ha2b : a2 < b := by rw [ha2]; linarith
  obtain ⟨t, htIoo, htlt⟩ := Work.RemovLog.exists_lt_log_combination (a := a2) (b := b) (K := K)
      (μ := |Q θ| - A) (M := W a2 - |G a2| * (b - a2)) ha2b hμ
  have hmid : W a2 - |G a2| * (b - a2) ≤ W a2 + G a2 * (t - a2) := by
    have ht1 : t - a2 ≤ b - a2 := by linarith [htIoo.2]
    rcases lt_or_ge (G a2) 0 with hg | hg
    · have h1 : G a2 * (t - a2) ≥ G a2 * (b - a2) := by nlinarith [ht1, hg]
      have h2 : G a2 * (b - a2) = -|G a2| * (b - a2) := by rw [abs_of_neg hg]; ring
      linarith
    · have h1 : 0 ≤ G a2 * (t - a2) := mul_nonneg hg (by linarith [htIoo.1])
      have h2 : -|G a2| * (b - a2) ≤ 0 := by
        nlinarith [abs_nonneg (G a2), htIoo.1, htIoo.2]
      linarith
  -- (8) MVT on [a2, t]
  have hcontW : ContinuousOn W (Set.Icc a2 t) := by
    refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
    exact (hWd x ⟨lt_of_lt_of_le (lt_trans hTθ (lt_trans hθa haa2)) hx.1,
      lt_of_le_of_lt hx.2 htIoo.2⟩).continuousAt
  have hdiffW : DifferentiableOn ℝ W (Set.Ioo a2 t) := by
    intro x hx
    exact (hWd x ⟨lt_of_lt_of_le (lt_trans hTθ (lt_trans hθa haa2)) (le_of_lt hx.1),
      lt_of_lt_of_le hx.2 (le_of_lt htIoo.2)⟩).differentiableWithinAt
  obtain ⟨c, hcIoo, hcder⟩ := exists_deriv_eq_slope' W htIoo.1 hcontW hdiffW
  have hcT : c ∈ Set.Ioo T b :=
    ⟨lt_trans hTθ (lt_trans hθa (lt_trans haa2 hcIoo.1)), lt_trans hcIoo.2 htIoo.2⟩
  have hcG : G c = (W t - W a2) / (t - a2) := by
    rw [← hWderiv c hcT, hcder, slope_def_field]
  have hGaGc : G a2 ≤ G c :=
    hmono ⟨haa2, ha2b⟩ ⟨lt_trans haa2 hcIoo.1, lt_trans hcIoo.2 htIoo.2⟩ (le_of_lt hcIoo.1)
  have htangent : W a2 + G a2 * (t - a2) ≤ W t := by
    have h1 : G a2 ≤ (W t - W a2) / (t - a2) := by rw [← hcG]; exact hGaGc
    have htpos : 0 < t - a2 := by linarith [htIoo.1]
    have h2 := (le_div_iff₀ htpos).mp h1
    linarith
  -- (9) W is bounded above
  have hWt : W t ≤ K + (|Q θ| - A) * Real.log (b - t) := by
    rw [hW]
    have hsF : s * F t ≤ |F t| := by
      rcases hs with h | h
      · rw [h]; simpa using le_abs_self (F t)
      · rw [h]; simpa using neg_le_abs (F t)
    have hbdt : |F t| ≤ K :=
      hFbd t ⟨le_of_lt (lt_trans hTθ (lt_trans hθa (lt_trans haa2 htIoo.1))), htIoo.2⟩
    linarith
  linarith


end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.sliceUdivCosUniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

/-!
# A uniform-in-`γ` bound for `(u / cos θ)² sin(2θ)^{2-γ}`

`Work.FTS.EllipticEst.remov.slice_u_div_cos_sq_le` proves, for each fixed `γ ∈ [1, 3/2]`, the
slice inequality

`∫_{Iθ} (u/cos θ)² sin(2θ)^{2-γ} ≤ C(γ) (∫_{Iθ} (u')² + ∫_{Iθ} u²)`

with a constant `C(γ)` that a priori depends on `γ`.  The quantifier placement is however
immaterial, because `Iθ = [0, π/2]` is exactly the set on which `0 ≤ sin(2θ) ≤ 1`: there the
weight `sin(2θ)^{2-γ}` is a *decreasing* function of `γ`, so the single instance `γ = 3/2` — the
worst case — dominates all the others,

`sin(2θ)^{2-γ} ≤ sin(2θ)^{1/2}`  for `γ ≤ 3/2`, `θ ∈ Iθ`.

Hence one may take `C := C(3/2)`: integrability of the general integrand is supplied by the
`γ`-instance of the sibling theorem, and the integral comparison follows from
`MeasureTheory.integral_mono_ae` between two integrable functions.
-/

/-- On `Iθ = [0, π/2]` the weight `sin(2θ)^{2-γ}` is decreasing in `γ`: for `γ ≤ 3/2` it is
bounded by the exponent-`1/2` weight. -/
private lemma sin_rpow_two_sub_mono {γ : ℝ} (hγ : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ Real.rpow (Real.sin (2 * θ)) (2 - (3 / 2 : ℝ)) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rcases eq_or_lt_of_le hs0 with h0 | hpos
  · have h1 : Real.rpow (Real.sin (2 * θ)) (2 - γ) = 0 := by
      rw [← h0]
      exact Real.zero_rpow (by linarith : (2 : ℝ) - γ ≠ 0)
    have h2 : Real.rpow (Real.sin (2 * θ)) (2 - (3 / 2 : ℝ)) = 0 := by
      rw [← h0]
      exact Real.zero_rpow (by norm_num : (2 : ℝ) - 3 / 2 ≠ 0)
    rw [h1, h2]
  · exact Real.rpow_le_rpow_of_exponent_ge hpos (Real.sin_le_one _) (by linarith)

/-- Pointwise monotonicity of the whole integrand in `γ` on `Iθ`. -/
private lemma integrand_le_of_gamma_le {γ : ℝ} (hγ : γ ≤ 3 / 2) (u : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - (3 / 2 : ℝ)) :=
  mul_le_mul_of_nonneg_left (sin_rpow_two_sub_mono hγ hθ) (sq_nonneg _)

theorem sliceUdivCosUniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u : ℝ → ℝ), 1 ≤ γ → γ ≤ 3 / 2 →
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      (MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 - γ))
          ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))) := by
  -- the worst case `γ = 3/2` supplies both the constant and the dominating integrand
  obtain ⟨C, hCpos, H⟩ := slice_u_div_cos_sq_le (3 / 2) (by norm_num) (by norm_num)
  refine ⟨C, hCpos, ?_⟩
  intro γ u hγ1 hγ2 hC3 hcont hu0 hpi hIntd hIntu
  obtain ⟨_, _, Hγ⟩ := slice_u_div_cos_sq_le γ hγ1 hγ2
  obtain ⟨hIntγ, _⟩ := Hγ u hC3 hcont hu0 hpi hIntd hIntu
  obtain ⟨hInt32, hle32⟩ := H u hC3 hcont hu0 hpi hIntd hIntu
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact measurableSet_Icc
  have hmono : (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ))
      ≤ (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - (3 / 2 : ℝ))) := by
    refine MeasureTheory.integral_mono_ae hIntγ hInt32 ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with θ hθ
    exact integrand_le_of_gamma_le hγ2 u hθ
  exact ⟨hIntγ, le_trans hmono hle32⟩

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_left_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The left-half slice estimate for `(u / cos)''`

We prove that on the left half `[0, π/4]` of the angular slice the second derivative of the
quotient `u / cos` is dominated by the three quantities appearing in the energy:

  `∫_{[0,π/4]} ((u/cos)'')² · sin(2θ)^{2-γ} ≤ C (∫_{Iθ} (u'')² sin(2θ)^{-η} + ∫_{Iθ} (u')² + ∫_{Iθ} u²)`.

Since `cos ≥ 1/2` on `[0, π/4]` and `|sin| ≤ 1`, the quotient rule gives the pointwise
identity

  `(u/cos)'' = u''/cos + 2 u' sin/cos² + u (1 + sin²)/cos³`,

whose right-hand side is bounded by `1728 (u''² + u'² + u²)` pointwise on `[0, π/4]`
(eight times the reciprocal of `cos³ ≥ 1/8`, Cauchy–Schwarz for three terms).  The weight
`sin(2θ)^{2-γ}` is at most `1` there and `sin(2θ)^{-η}` is at least `1`, which yields the
claim.  No use is made of the equation `L₀u = g` or of the boundary conditions.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-! ## Elementary real arithmetic -/

/-- Cauchy–Schwarz for three terms: `(x+y+z)² ≤ 3(x²+y²+z²)`. -/
private lemma sq_three (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y + z)]

/-- Arithmetic core of the pointwise bound: if `c ∈ [1/2, 1]`, `s² ≤ 1`, `se ≥ 1`,
`w ∈ [0,1]` and `a c³ = U₂ c² + 2 U₁ s c + U₀ (1 + s²)`, then
`a² w ≤ 2000 (U₂² se + U₁² + U₀²)`. -/
private lemma quarter_arith {c s w se a U2 U1 U0 : ℝ}
    (hc1 : 1 / 2 ≤ c) (hc2 : c ≤ 1) (hs : s ^ 2 ≤ 1) (hse : 1 ≤ se)
    (_hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (ha : a * c ^ 3 = U2 * c ^ 2 + 2 * U1 * s * c + U0 * (1 + s ^ 2)) :
    a ^ 2 * w ≤ 2000 * (U2 ^ 2 * se + U1 ^ 2 + U0 ^ 2) := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc1
  have hc2sq : c ^ 2 ≤ 1 := pow_le_one₀ hc0.le hc2
  have hc4le : c ^ 4 ≤ 1 := pow_le_one₀ hc0.le hc2
  have hc6 : (1 : ℝ) / 64 ≤ c ^ 6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hc1 6
    norm_num at h
    linarith
  have hsc : s ^ 2 * c ^ 2 ≤ 1 := by
    calc s ^ 2 * c ^ 2 ≤ 1 * 1 := mul_le_mul hs hc2sq (sq_nonneg c) (by norm_num)
      _ = 1 := by ring
  have h1s2 : (1 + s ^ 2) ^ 2 ≤ 4 := by
    have h : (1 + s ^ 2) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    norm_num at h
    exact h
  have hN : (U2 * c ^ 2 + 2 * U1 * s * c + U0 * (1 + s ^ 2)) ^ 2
      ≤ 3 * (U2 ^ 2 + 4 * U1 ^ 2 + 4 * U0 ^ 2) := by
    have h0 := sq_three (U2 * c ^ 2) (2 * U1 * s * c) (U0 * (1 + s ^ 2))
    have e1 : (U2 * c ^ 2) ^ 2 ≤ U2 ^ 2 := by nlinarith [hc4le, sq_nonneg U2]
    have e2 : (2 * U1 * s * c) ^ 2 ≤ 4 * U1 ^ 2 := by nlinarith [hsc, sq_nonneg U1]
    have e3 : (U0 * (1 + s ^ 2)) ^ 2 ≤ 4 * U0 ^ 2 := by nlinarith [h1s2, sq_nonneg U0]
    nlinarith [h0, e1, e2, e3]
  have ha2 : a ^ 2 * c ^ 6 = (U2 * c ^ 2 + 2 * U1 * s * c + U0 * (1 + s ^ 2)) ^ 2 := by
    have h : (a * c ^ 3) ^ 2 = (U2 * c ^ 2 + 2 * U1 * s * c + U0 * (1 + s ^ 2)) ^ 2 := by
      rw [ha]
    nlinarith [h]
  have ha_le : a ^ 2 ≤ 64 * (U2 * c ^ 2 + 2 * U1 * s * c + U0 * (1 + s ^ 2)) ^ 2 := by
    have h : a ^ 2 * ((1 : ℝ) / 64) ≤ a ^ 2 * c ^ 6 :=
      mul_le_mul_of_nonneg_left hc6 (sq_nonneg a)
    nlinarith [h, ha2]
  calc a ^ 2 * w ≤ a ^ 2 * 1 := mul_le_mul_of_nonneg_left hw1 (sq_nonneg a)
    _ = a ^ 2 := by ring
    _ ≤ 64 * (U2 * c ^ 2 + 2 * U1 * s * c + U0 * (1 + s ^ 2)) ^ 2 := ha_le
    _ ≤ 64 * (3 * (U2 ^ 2 + 4 * U1 ^ 2 + 4 * U0 ^ 2)) := by
        have h := mul_le_mul_of_nonneg_left hN (by norm_num : (0 : ℝ) ≤ 64)
        linarith
    _ ≤ 2000 * (U2 ^ 2 * se + U1 ^ 2 + U0 ^ 2) := by
        nlinarith [hse, sq_nonneg U2, sq_nonneg U1, sq_nonneg U0]

/-- `cos θ ≥ 1/2` on `[0, π/4]`. -/
private lemma cos_ge_half {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4)) :
    (1 : ℝ) / 2 ≤ Real.cos θ := by
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := Real.pi / 3) hθ.1
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos, hθ.2])
  rwa [Real.cos_pi_div_three] at h

/-! ## The derivative identities for `u / cos` -/

/-- First derivative of `u / cos`: `(u/cos)' = u'/cos + u sin/cos²`. -/
private lemma deriv_div_cos (u : ℝ → ℝ) (h3 : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun s => u s / Real.cos s) θ
      = deriv u θ / Real.cos θ + u θ * Real.sin θ / (Real.cos θ) ^ 2 := by
  have hdu : DifferentiableAt ℝ u θ :=
    (h3.differentiableOn (by norm_num : (3 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  rw [deriv_fun_div hdu Real.differentiableAt_cos hcos, Real.deriv_cos]
  field_simp
  ring

/-- Second derivative of `u / cos`:
`(u/cos)'' = u''/cos + 2 u' sin/cos² + u (1 + sin²)/cos³`. -/
private lemma deriv_deriv_div_cos (u : ℝ → ℝ) (h3 : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
      = deriv (deriv u) θ / Real.cos θ + 2 * deriv u θ * Real.sin θ / (Real.cos θ) ^ 2
        + u θ * (1 + (Real.sin θ) ^ 2) / (Real.cos θ) ^ 3 := by
  have hdu : DifferentiableAt ℝ u θ :=
    (h3.differentiableOn (by norm_num : (3 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have h2 : ContDiffOn ℝ 2 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    h3.deriv_of_isOpen isOpen_Ioo (m := 2) (by norm_num)
  have hdd : DifferentiableAt ℝ (deriv u) θ :=
    (h2.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hev : (fun t : ℝ => deriv (fun s => u s / Real.cos s) t) =ᶠ[nhds θ]
      (fun t => deriv u t / Real.cos t + u t * Real.sin t / (Real.cos t) ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact deriv_div_cos u h3 ht
  rw [hev.deriv_eq]
  have h1' : HasDerivAt (fun t => deriv u t / Real.cos t)
      (deriv (deriv u) θ / Real.cos θ + deriv u θ * Real.sin θ / (Real.cos θ) ^ 2) θ := by
    have h := hdd.hasDerivAt.div (Real.hasDerivAt_cos θ) hcos
    convert h using 1
    field_simp
    ring
  have h2' : HasDerivAt (fun t => u t * Real.sin t / (Real.cos t) ^ 2)
      (deriv u θ * Real.sin θ / (Real.cos θ) ^ 2
        + u θ * (1 + (Real.sin θ) ^ 2) / (Real.cos θ) ^ 3) θ := by
    have hA : HasDerivAt (fun t => u t * Real.sin t)
        (deriv u θ * Real.sin θ + u θ * Real.cos θ) θ :=
      hdu.hasDerivAt.mul (Real.hasDerivAt_sin θ)
    have hB : HasDerivAt (fun t : ℝ => (Real.cos t) ^ 2) (2 * Real.cos θ * (-Real.sin θ)) θ := by
      have h := (Real.hasDerivAt_cos θ).pow 2
      convert h using 1
      ring
    have h := hA.div hB (pow_ne_zero 2 hcos)
    convert h using 1
    rw [← Real.sin_sq_add_cos_sq θ]
    field_simp
    ring
  have hsum : HasDerivAt (fun t => deriv u t / Real.cos t + u t * Real.sin t / (Real.cos t) ^ 2)
      (deriv (deriv u) θ / Real.cos θ + deriv u θ * Real.sin θ / (Real.cos θ) ^ 2
        + (deriv u θ * Real.sin θ / (Real.cos θ) ^ 2
            + u θ * (1 + (Real.sin θ) ^ 2) / (Real.cos θ) ^ 3)) θ :=
    h1'.add h2'
  rw [hsum.deriv]
  ring

/-! ## The pointwise bound on `[0, π/4]` -/

/-- Pointwise domination on `[0, π/4]`: the integrand of the left slice is bounded by
`2000` times the sum of the three energy densities. -/
private lemma sec_second_deriv_le (u : ℝ → ℝ) (γ : ℝ) (_hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (h3 : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4),
      (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ 2000 * ((deriv (deriv u) θ) ^ 2 * sEta θ + (deriv u θ) ^ 2 + (u θ) ^ 2) := by
  intro θ hθ
  have hpi : 0 < Real.pi := Real.pi_pos
  rcases eq_or_lt_of_le hθ.1 with h0 | hpos
  · rw [← h0]
    have hz : Real.rpow (Real.sin (2 * 0)) (2 - γ) = 0 := by
      rw [show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
      exact Real.zero_rpow (by linarith : (2 : ℝ) - γ ≠ 0)
    rw [hz, mul_zero]
    have hsE : 0 ≤ sEta (0 : ℝ) := by
      rw [sEta]
      rw [show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
      exact Real.rpow_nonneg le_rfl _
    have h1 : 0 ≤ (deriv (deriv u) 0) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (deriv u 0) ^ 2 := sq_nonneg _
    have h4 : 0 ≤ (u 0) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg h1 hsE]
  · have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hpos, by linarith [hθ.2, hpi]⟩
    have hid := deriv_deriv_div_cos u h3 hθIoo
    have hc1 : (1 : ℝ) / 2 ≤ Real.cos θ := cos_ge_half hθ
    have hc2 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hs : (Real.sin θ) ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    have hsin2nn : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.2, hpi])
    have hse : 1 ≤ sEta θ := by
      rw [sEta]
      refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos ?_ ?_ ?_
      · exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ.2, hpi])
      · exact Real.sin_le_one _
      · have := Work.Spaces.eta_pos
        linarith
    have hw0 : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) := Real.rpow_nonneg hsin2nn _
    have hw1 : Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 :=
      Real.rpow_le_one hsin2nn (Real.sin_le_one _) (by linarith)
    have ha : deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ * (Real.cos θ) ^ 3
        = deriv (deriv u) θ * (Real.cos θ) ^ 2 + 2 * deriv u θ * Real.sin θ * Real.cos θ
          + u θ * (1 + (Real.sin θ) ^ 2) := by
      rw [hid]
      have hcne : Real.cos θ ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hc1)
      field_simp
    exact quarter_arith hc1 hc2 hs hse hw0 hw1 ha

/-! ## Two measure theory helpers -/

/-- If `G` is a.e. strongly measurable on `s`, nonnegative there, and dominated there by an
integrable `H`, then `G` is integrable on `s`. -/
private lemma integrableOn_of_le {G H : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hH : MeasureTheory.IntegrableOn H s) (hG0 : ∀ x ∈ s, 0 ≤ G x)
    (hG : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume.restrict s))
    (hle : ∀ x ∈ s, G x ≤ H x) : MeasureTheory.IntegrableOn G s := by
  refine MeasureTheory.Integrable.mono' hH hG ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) hs] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hG0 x hx)]
  exact hle x hx

/-- Integral comparison across an inclusion of sets, for a nonnegative majorant. -/
private lemma setIntegral_le_of_pointwise {G H : ℝ → ℝ} {s t : Set ℝ} (hst : s ⊆ t)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hG : MeasureTheory.IntegrableOn G s)
    (hH : MeasureTheory.IntegrableOn H t) (hle : ∀ x ∈ s, G x ≤ H x)
    (hH0 : ∀ x ∈ t, 0 ≤ H x) : ∫ x in s, G x ≤ ∫ x in t, H x := by
  have h1 : ∫ x in s, G x ≤ ∫ x in s, H x :=
    MeasureTheory.setIntegral_mono_on hG (hH.mono_set hst) hs hle
  have h2 : ∫ x in s, H x ≤ ∫ x in t, H x := by
    refine MeasureTheory.setIntegral_mono_set hH ?_
      (Filter.Eventually.of_forall (fun x hx => hst hx))
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) ht] with x hx
    exact hH0 x hx
  linarith

/-! ## The slice estimate -/


end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.sin_integrals =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real
open MeasureTheory Set

namespace Work.FTS.EllipticEst

/-! ## The elementary angular integrals of the elliptic estimates

The four integrals of `Work.FTS.EllipticEst.sin_integrals` are reduced to the standard interval
integrals of Mathlib (`integral_sin_sq`, `integral_cos_sq`, `integral_cos_pow`) by

* the substitution `θ ↦ 2θ` (`intervalIntegral.integral_comp_mul_left`) and the double-angle
  identities `Real.sin_sq_eq_half_sub`, `Real.cos_sq` for the first two integrals;
* the identities `sin²θ cos⁴θ = cos⁴θ - cos⁶θ` (from `Real.sin_sq`) together with the reduction
  formulae for `∫ cos⁴`, `∫ cos⁶` for the third;
* the already delivered `Work.Elliptic.integral_sin_two_mul_sinCos2` for the fourth.
-/

/-- `∫_0^{π/2} cos⁴θ dθ = 3π/16`, by the reduction formula for `∫ cos^n`. -/
private lemma integral_cos_four : (∫ θ in (0:ℝ)..(π/2), Real.cos θ ^ 4) = 3 * π / 16 := by
  rw [integral_cos_pow (a := (0:ℝ)) (b := π/2) (n := 2), integral_cos_sq]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero]
  ring

/-- `∫_0^{π/2} cos⁶θ dθ = 5π/32`, by the reduction formula for `∫ cos^n` and `integral_cos_four`. -/
private lemma integral_cos_six : (∫ θ in (0:ℝ)..(π/2), Real.cos θ ^ 6) = 5 * π / 32 := by
  rw [integral_cos_pow (a := (0:ℝ)) (b := π/2) (n := 4), integral_cos_four]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero]
  ring

/-- `∫_0^{π/2} sin²(2θ) dθ = π/4`: substitute `u = 2θ` and use `integral_sin_sq`. -/
private lemma integral_sin_two_sq : (∫ θ in (0:ℝ)..(π/2), (Real.sin (2 * θ)) ^ 2) = π / 4 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.sin x ^ 2)
    (by norm_num : (2:ℝ) ≠ 0)]
  rw [show (2:ℝ) * 0 = 0 by ring, show (2:ℝ) * (π/2) = π by ring]
  simp only [smul_eq_mul]
  rw [integral_sin_sq, Real.sin_zero, Real.cos_zero, Real.sin_pi, Real.cos_pi]
  ring

/-- `∫_0^{π/2} (2cos(2θ))² dθ = π`: substitute `u = 2θ` and use `integral_cos_sq`. -/
private lemma integral_two_cos_two_sq :
    (∫ θ in (0:ℝ)..(π/2), (2 * Real.cos (2 * θ)) ^ 2) = π := by
  have hpt : ∀ θ : ℝ, (2 * Real.cos (2 * θ)) ^ 2 = 4 * Real.cos (2 * θ) ^ 2 := by
    intro θ; ring
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.cos x ^ 2)
    (by norm_num : (2:ℝ) ≠ 0)]
  rw [show (2:ℝ) * 0 = 0 by ring, show (2:ℝ) * (π/2) = π by ring]
  simp only [smul_eq_mul]
  rw [integral_cos_sq, Real.cos_pi, Real.sin_pi, Real.cos_zero, Real.sin_zero]
  ring

/-- `∫_0^{π/2} (sinθcos²θ)² dθ = π/32`: since `sin²θ cos⁴θ = cos⁴θ - cos⁶θ`, this is
`3π/16 - 5π/32`. -/
private lemma integral_sinCos2_sq :
    (∫ θ in (0:ℝ)..(π/2), (Work.Elliptic.sinCos2 θ) ^ 2) = π / 32 := by
  have hpt : ∀ θ : ℝ, (Work.Elliptic.sinCos2 θ) ^ 2 = Real.cos θ ^ 4 - Real.cos θ ^ 6 := by
    intro θ
    simp only [Work.Elliptic.sinCos2]
    rw [show (Real.sin θ * Real.cos θ ^ 2) ^ 2 = Real.sin θ ^ 2 * (Real.cos θ ^ 2) ^ 2 by
      ring, Real.sin_sq]
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  have hsub : (∫ x in (0:ℝ)..(π/2), Real.cos x ^ 4 - Real.cos x ^ 6)
      = (∫ x in (0:ℝ)..(π/2), Real.cos x ^ 4) - (∫ x in (0:ℝ)..(π/2), Real.cos x ^ 6) :=
    intervalIntegral.integral_sub ((Real.continuous_cos.pow 4).intervalIntegrable _ _)
      ((Real.continuous_cos.pow 6).intervalIntegrable _ _)
  rw [hsub, integral_cos_four, integral_cos_six]
  ring

/-- `∫_0^{π/2} sinθcos²θ · sin2θ dθ = 4/15`, transported from the delivered set-integral form
`Work.Elliptic.integral_sin_two_mul_sinCos2` over `Work.Spaces.Iθ`. -/
private lemma integral_sinCos2_mul_sin_two :
    (∫ θ in (0:ℝ)..(π/2), Work.Elliptic.sinCos2 θ * Real.sin (2 * θ)) = 4 / 15 := by
  have hIθ : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * Real.sin (2 * θ))
      = ∫ θ in (0:ℝ)..(π/2), Work.Elliptic.sinCos2 θ * Real.sin (2 * θ) := by
    change ∫ θ in Set.Icc 0 (π/2), Work.Elliptic.sinCos2 θ * Real.sin (2 * θ) = _
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ π/2)]
  have hcomm : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * Real.sin (2 * θ))
      = ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ :=
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  rw [← hIθ, hcomm, Work.Elliptic.integral_sin_two_mul_sinCos2]

theorem sin_integrals :
    (∫ θ in (0:ℝ)..(π / 2), (Real.sin (2 * θ)) ^ 2 = π / 4) ∧
    (∫ θ in (0:ℝ)..(π / 2), (2 * Real.cos (2 * θ)) ^ 2 = π) ∧
    (∫ θ in (0:ℝ)..(π / 2), (Work.Elliptic.sinCos2 θ) ^ 2 = π / 32) ∧
    (∫ θ in (0:ℝ)..(π / 2), Work.Elliptic.sinCos2 θ * Real.sin (2 * θ) = 4 / 15) :=
  ⟨integral_sin_two_sq, integral_two_cos_two_sq, integral_sinCos2_sq,
    integral_sinCos2_mul_sin_two⟩

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.Rop_Uop_Vop_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

/-- Additivity of the three numerical operators of `Work.Construction` in their argument, at a
point where both summands are differentiable in `z` (for the `z ∂_z` in `Uop` and `Rop`) and in `θ`
(for the `∂_θ` in `Vop` and `Rop`).  This is the algebraic input of the block decomposition
`PhiTil α f (Φs + E f) = PhiTil α f (E f) + PhiTil α F_* Φs + Theta α F_*`: it turns the *sum* of
three profiles into the sum of the three operators, whose pieces are then bounded separately. -/
theorem Rop_Uop_Vop_add {α : ℝ} {Ψ₁ Ψ₂ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz₁ : DifferentiableAt ℝ (fun z' => Ψ₁ z' θ) z)
    (hz₂ : DifferentiableAt ℝ (fun z' => Ψ₂ z' θ) z)
    (hθ₁ : DifferentiableAt ℝ (fun θ' => Ψ₁ z θ') θ)
    (hθ₂ : DifferentiableAt ℝ (fun θ' => Ψ₂ z θ') θ) :
    (Work.Construction.Rop α (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
        = Work.Construction.Rop α Ψ₁ z θ + Work.Construction.Rop α Ψ₂ z θ) ∧
    (Work.Construction.Uop α (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
        = Work.Construction.Uop α Ψ₁ z θ + Work.Construction.Uop α Ψ₂ z θ) ∧
    (Work.Construction.Vop (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
        = Work.Construction.Vop Ψ₁ z θ + Work.Construction.Vop Ψ₂ z θ) := by
  -- `pz` and `pth` are plain `deriv`s of the `z`- resp. `θ`-slices, so they are additive
  -- under the pointwise differentiability hypotheses; the three operator identities are
  -- then linear algebra in the ring `ℝ`.
  have hpz : Work.Spaces.pz (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Spaces.pz Ψ₁ z θ + Work.Spaces.pz Ψ₂ z θ := by
    simp only [Work.Spaces.pz]
    exact deriv_add hz₁ hz₂
  have hpt : Work.Spaces.pth (fun z θ => Ψ₁ z θ + Ψ₂ z θ) z θ
      = Work.Spaces.pth Ψ₁ z θ + Work.Spaces.pth Ψ₂ z θ := by
    simp only [Work.Spaces.pth]
    exact deriv_add hθ₁ hθ₂
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Work.Construction.Rop, Work.Construction.Uop, Work.Construction.Vop,
      hpz, hpt] <;>
    ring

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.FinalClock.L12LinearSub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Work.FTS.FinalClock

/-- `L₁₂`-density of a pointwise negation is the negation of the density.  The angular integral is
`MeasureTheory.integral_neg`, which needs no integrability (the Bochner integral is total). -/
theorem L12dens_neg' {K : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {s : ℝ} :
    Work.FM.L12dens K (fun s' θ => -f s' θ) s = -(Work.FM.L12dens K f s) := by
  have h : (fun θ : ℝ => K θ * (-f s θ) / s) = fun θ : ℝ => -(K θ * f s θ / s) := by
    funext θ
    ring
  rw [Work.FM.L12dens, Work.FM.L12dens, h]
  exact MeasureTheory.integral_neg (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (f := fun θ : ℝ => K θ * f s θ / s)

/-- `L₁₂` of a pointwise negation is the negation of `L₁₂`. -/
theorem L12_neg' {K : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z : ℝ} :
    Work.FM.L12 K (fun s θ => -f s θ) z = -(Work.FM.L12 K f z) := by
  rw [Work.FM.L12, Work.FM.L12]
  simp only [L12dens_neg']
  exact MeasureTheory.integral_neg (μ := MeasureTheory.volume.restrict (Set.Ioi z))
    (f := fun s : ℝ => Work.FM.L12dens K f s)

theorem L12LinearSub {f₁ f₂ : ℝ → ℝ → ℝ} {z : ℝ}
    (h1 : ∀ s : ℝ, MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f₁ s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ s : ℝ, MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f₂ s θ / s) Work.Spaces.Iθ)
    (hF1 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f₁) (Set.Ioi z))
    (hF2 : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f₂) (Set.Ioi z)) :
    Work.Construction.L12 f₁ z - Work.Construction.L12 f₂ z
      = Work.Construction.L12 (fun s θ => f₁ s θ - f₂ s θ) z := by
  have h2' : ∀ s : ℝ,
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * (-f₂ s θ) / s) Work.Spaces.Iθ := by
    intro s
    refine ((h2 s).neg).congr ?_
    filter_upwards with θ
    rw [Pi.neg_apply]
    ring
  have hF2' : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (fun s θ => -f₂ s θ)) (Set.Ioi z) := by
    refine (MeasureTheory.IntegrableOn.neg hF2).congr ?_
    filter_upwards with s
    exact (L12dens_neg' (K := Work.Spaces.K) (f := f₂) (s := s)).symm
  have hadd := Work.FM.L12_add (K := Work.Spaces.K) (f := f₁)
    (g := fun s θ => -f₂ s θ) h1 h2' hF1 hF2'
  rw [Work.Construction.L12, Work.Construction.L12, Work.Construction.L12]
  have hsub : (fun s θ => f₁ s θ - f₂ s θ) = fun s θ => f₁ s θ + -f₂ s θ := rfl
  rw [hsub, hadd, L12_neg']
  ring

end Work.FTS.FinalClock
end
end
-- ===== merged: Submission.Work.FTS.FinalClock.ZopIterLeibniz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.FTS.FinalClock

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {U : Set ℝ}

/-! ## `Zop`-calculus on an open set -/

/-- The derivative of a `C^{n+1}` function on an open set is `C^n` there. -/
theorem contDiffOn_deriv_of_succ_open {u : ℝ → ℝ} (hU : IsOpen U) (n : ℕ)
    (hu : ContDiffOn ℝ (((n + 1 : ℕ)) : ℕ∞ω) u U) :
    ContDiffOn ℝ (((n : ℕ)) : ℕ∞ω) (deriv u) U := by
  have hfd : ContDiffOn ℝ (((n : ℕ)) : ℕ∞ω) (fderiv ℝ u) U :=
    hu.fderiv_of_isOpen hU (by push_cast; exact le_rfl)
  have hev : ContDiffOn ℝ (((n : ℕ)) : ℕ∞ω) (fun z : ℝ => (fderiv ℝ u z) 1) U :=
    hfd.clm_apply contDiffOn_const
  refine hev.congr (fun z _ => ?_)
  rw [fderiv_apply_one_eq_deriv]

/-- A `C^{b+k}` function has `C^k` `Zop`-iterates of order `b`. -/
theorem Zop_contDiffOn_iter {u : ℝ → ℝ} (hU : IsOpen U) (b k : ℕ)
    (hu : ContDiffOn ℝ (((b + k : ℕ)) : ℕ∞ω) u U) :
    ContDiffOn ℝ (((k : ℕ)) : ℕ∞ω) (Work.Spaces.Zop^[b] u) U := by
  induction b generalizing k with
  | zero => simpa [Nat.zero_add] using hu
  | succ b ih =>
    have hu' : ContDiffOn ℝ (((b + (k + 1) : ℕ)) : ℕ∞ω) u U :=
      hu.of_le (by exact_mod_cast (by omega : b + (k + 1) ≤ (b + 1) + k))
    have h1 : ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞ω) (Work.Spaces.Zop^[b] u) U := ih (k + 1) hu'
    have h2 : ContDiffOn ℝ (((k : ℕ)) : ℕ∞ω) (deriv (Work.Spaces.Zop^[b] u)) U :=
      contDiffOn_deriv_of_succ_open hU k h1
    have h3 : ContDiffOn ℝ (((k : ℕ)) : ℕ∞ω)
        (fun z : ℝ => z * deriv (Work.Spaces.Zop^[b] u) z) U :=
      (contDiff_id.contDiffOn).mul h2
    rw [Function.iterate_succ_apply']
    change ContDiffOn ℝ (((k : ℕ)) : ℕ∞ω)
      (fun z : ℝ => z * deriv (Work.Spaces.Zop^[b] u) z) U
    exact h3

/-- `Zop` respects `EqOn` on an open set. -/
theorem Zop_congr_open {A B : ℝ → ℝ} (hU : IsOpen U) (h : Set.EqOn A B U) :
    Set.EqOn (Work.Spaces.Zop A) (Work.Spaces.Zop B) U := by
  intro z hz
  show Work.Spaces.Zop A z = Work.Spaces.Zop B z
  simp only [Work.Spaces.Zop]
  rw [h.deriv hU hz]



/-- The combined product/scalar rule needed for the summands of the Leibniz sum. -/
theorem Zop_const_mul_mul_open (c : ℝ) {X Y : ℝ → ℝ} {z : ℝ}
    (hX : DifferentiableAt ℝ X z) (hY : DifferentiableAt ℝ Y z) :
    Work.Spaces.Zop (fun w => c * (X w * Y w)) z
      = c * (Work.Spaces.Zop X z * Y z + X z * Work.Spaces.Zop Y z) := by
  have hXY : DifferentiableAt ℝ (fun w : ℝ => X w * Y w) z := hX.mul hY
  have h1 : deriv (fun w : ℝ => c * (X w * Y w)) z
      = c * deriv (fun w : ℝ => X w * Y w) z :=
    deriv_const_mul c hXY
  have h2 : deriv (fun w : ℝ => X w * Y w) z = deriv X z * Y z + X z * deriv Y z :=
    deriv_mul hX hY
  simp only [Work.Spaces.Zop]
  rw [h1, h2]
  ring

/-- `Zop` is linear over finite sums of differentiable functions. -/
theorem Zop_sum_range_open (K : ℕ) (A : ℕ → ℝ → ℝ) {z : ℝ}
    (hA : ∀ b ≤ K, DifferentiableAt ℝ (A b) z) :
    Work.Spaces.Zop (fun w => ∑ b ∈ Finset.range (K + 1), A b w) z
      = ∑ b ∈ Finset.range (K + 1), Work.Spaces.Zop (A b) z := by
  have hd : ∀ b ∈ Finset.range (K + 1), DifferentiableAt ℝ (A b) z :=
    fun b hb => hA b (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))
  simp only [Work.Spaces.Zop]
  rw [deriv_fun_sum hd, Finset.mul_sum]

/-! ## The Leibniz sum and the induction -/

/-- The binomial Leibniz sum for `Zop^[N]`. -/
def Zsum (N : ℕ) (u v : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∑ b ∈ Finset.range (N + 1),
    (N.choose b : ℝ) * (Work.Spaces.Zop^[b] u z * Work.Spaces.Zop^[N - b] v z)

/-- The iterated Leibniz rule for `Zop` on an open set, at finite order `N`. -/
theorem Zop_iter_mul_open (hU : IsOpen U) (N : ℕ) :
    ∀ {u v : ℝ → ℝ}, ContDiffOn ℝ N u U → ContDiffOn ℝ N v U →
      Set.EqOn (Work.Spaces.Zop^[N] (u * v)) (Zsum N u v) U := by
  induction N with
  | zero =>
    intro u v _ _ z _
    show (u * v) z = Zsum 0 u v z
    simp [Zsum]
  | succ N ih =>
    intro u v hu hv z hz
    have huN : ContDiffOn ℝ N u U := hu.of_le (by exact_mod_cast Nat.le_succ N)
    have hvN : ContDiffOn ℝ N v U := hv.of_le (by exact_mod_cast Nat.le_succ N)
    have hIH : Set.EqOn (Work.Spaces.Zop^[N] (u * v)) (Zsum N u v) U := ih huN hvN
    -- differentiability of the individual iterates
    have hdiff_u : ∀ b ≤ N, DifferentiableAt ℝ (Work.Spaces.Zop^[b] u) z := by
      intro b hb
      have hcast : (((b + (N + 1 - b) : ℕ)) : ℕ∞ω) = (((N + 1 : ℕ)) : ℕ∞ω) := by
        rw [show b + (N + 1 - b) = N + 1 from by omega]
      have hu'' : ContDiffOn ℝ (((b + (N + 1 - b) : ℕ)) : ℕ∞ω) u U := by
        rw [hcast]; exact hu
      have h1 : ContDiffOn ℝ (((N + 1 - b : ℕ)) : ℕ∞ω) (Work.Spaces.Zop^[b] u) U :=
        Zop_contDiffOn_iter hU b (N + 1 - b) hu''
      have h2 : (1 : ℕ) ≤ N + 1 - b := by omega
      exact ((h1.of_le (by exact_mod_cast h2)).differentiableOn_one).differentiableAt
        (hU.mem_nhds hz)
    have hdiff_v : ∀ b ≤ N, DifferentiableAt ℝ (Work.Spaces.Zop^[N - b] v) z := by
      intro b hb
      have hcast : ((((N - b) + (b + 1) : ℕ)) : ℕ∞ω) = (((N + 1 : ℕ)) : ℕ∞ω) := by
        rw [show (N - b) + (b + 1) = N + 1 from by omega]
      have hv'' : ContDiffOn ℝ ((((N - b) + (b + 1) : ℕ)) : ℕ∞ω) v U := by
        rw [hcast]; exact hv
      have h1 : ContDiffOn ℝ (((b + 1 : ℕ)) : ℕ∞ω) (Work.Spaces.Zop^[N - b] v) U :=
        Zop_contDiffOn_iter hU (N - b) (b + 1) hv''
      have h2 : (1 : ℕ) ≤ b + 1 := by omega
      exact ((h1.of_le (by exact_mod_cast h2)).differentiableOn_one).differentiableAt
        (hU.mem_nhds hz)
    have hdiff_XY : ∀ b ≤ N, DifferentiableAt ℝ
        (fun w => Work.Spaces.Zop^[b] u w * Work.Spaces.Zop^[N - b] v w) z :=
      fun b hb => (hdiff_u b hb).mul (hdiff_v b hb)
    have hdiff_A : ∀ b ≤ N, DifferentiableAt ℝ
        (fun w => (N.choose b : ℝ)
          * (Work.Spaces.Zop^[b] u w * Work.Spaces.Zop^[N - b] v w)) z :=
      fun b hb => (hdiff_XY b hb).const_mul _
    calc Work.Spaces.Zop^[N + 1] (u * v) z
        = Work.Spaces.Zop (Work.Spaces.Zop^[N] (u * v)) z := by
          rw [Function.iterate_succ_apply']
      _ = Work.Spaces.Zop (Zsum N u v) z := by
          show z * deriv (Work.Spaces.Zop^[N] (u * v)) z = z * deriv (Zsum N u v) z
          rw [hIH.deriv hU hz]
      _ = ∑ b ∈ Finset.range (N + 1), Work.Spaces.Zop
            (fun w => (N.choose b : ℝ)
              * (Work.Spaces.Zop^[b] u w * Work.Spaces.Zop^[N - b] v w)) z := by
          exact Zop_sum_range_open N
            (fun b w => (N.choose b : ℝ)
              * (Work.Spaces.Zop^[b] u w * Work.Spaces.Zop^[N - b] v w))
            (z := z) hdiff_A
      _ = ∑ b ∈ Finset.range (N + 1), (N.choose b : ℝ)
            * (Work.Spaces.Zop^[b + 1] u z * Work.Spaces.Zop^[N - b] v z
              + Work.Spaces.Zop^[b] u z * Work.Spaces.Zop^[N - b + 1] v z) := by
          apply Finset.sum_congr rfl
          intro b hb
          have hbN : b ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
          have hstep : Work.Spaces.Zop
              (fun w => (N.choose b : ℝ)
                * (Work.Spaces.Zop^[b] u w * Work.Spaces.Zop^[N - b] v w)) z
              = (N.choose b : ℝ)
                * (Work.Spaces.Zop^[b + 1] u z * Work.Spaces.Zop^[N - b] v z
                  + Work.Spaces.Zop^[b] u z * Work.Spaces.Zop^[N - b + 1] v z) := by
            rw [Zop_const_mul_mul_open (N.choose b : ℝ) (hdiff_u b hbN) (hdiff_v b hbN),
              ← Function.iterate_succ_apply' Work.Spaces.Zop b u,
              ← Function.iterate_succ_apply' Work.Spaces.Zop (N - b) v]
          exact hstep
      _ = ∑ b ∈ Finset.range (N + 1 + 1), ((N + 1).choose b : ℝ)
            * (Work.Spaces.Zop^[b] u z * Work.Spaces.Zop^[N + 1 - b] v z) :=
          Work.Spaces.leibniz_step N (fun i => Work.Spaces.Zop^[i] u z)
            (fun i => Work.Spaces.Zop^[i] v z)
      _ = Zsum (N + 1) u v z := by
          simp only [Zsum]

/-- **The iterated Leibniz rule for `Zop u = z·u'`.**  For `u, v` of class `C^N` on an open
set `U`, the `N`-th iterate of `Zop` of the product is the binomial convolution of the
iterates. -/
theorem ZopIterLeibniz {N : ℕ} {U : Set ℝ} (hU : IsOpen U) {u v : ℝ → ℝ}
    (hu : ContDiffOn ℝ N u U) (hv : ContDiffOn ℝ N v U) :
    Set.EqOn (Work.Spaces.Zop^[N] (u * v))
      (fun z => ∑ b ∈ Finset.range (N + 1),
        (N.choose b : ℝ) * (Work.Spaces.Zop^[b] u z * Work.Spaces.Zop^[N - b] v z)) U := by
  intro z hz
  have hz' := Zop_iter_mul_open hU N hu hv hz
  show Work.Spaces.Zop^[N] (u * v) z = ∑ b ∈ Finset.range (N + 1),
    (N.choose b : ℝ) * (Work.Spaces.Zop^[b] u z * Work.Spaces.Zop^[N - b] v z)
  rw [hz']
  simp only [Zsum]

end Work.FTS.FinalClock
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.GalDense.Xmb =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.Xmb

open scoped Real Topology ContDiff
open Set Filter

open Work.FTS.EllipticEst.remov.selfdth (dthCoef DthIter_expansion_of_contDiffOn
  DthCoef_sin_pow_bound)

noncomputable section

set_option autoImplicit false

/-! ## Smoothness of the curried partial derivatives, at a finite order

The `ℋ^k`-machinery of the project uses `ContDiffOn ℝ ⊤` on the fixed sets of
`Work.Spaces`; here the data is only `C⁶` on an arbitrary rectangle, so the
partial-derivative calculus is re-stated at a finite order on an arbitrary open set.
-/

/-- The `z`-partial derivative lowers the order of differentiability by one. -/
theorem contDiffOn_uncurry_pz_le {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V) :
    ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (by simp)
  have hcomp : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply
      (contDiffOn_const : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun _ : ℝ × ℝ => ((1, 0) : ℝ × ℝ)) V)
  exact hcomp.congr hchain

/-- The `θ`-partial derivative lowers the order of differentiability by one. -/
theorem contDiffOn_uncurry_pth_le {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V) :
    ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (by simp)
  have hcomp : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply
      (contDiffOn_const : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun _ : ℝ × ℝ => ((0, 1) : ℝ × ℝ)) V)
  exact hcomp.congr hchain

/-- The iterated `z`-partial `∂_z^i` costs `i` orders of differentiability. -/
theorem contDiffOn_uncurry_pzIter_le {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) V) :
    ∀ i k : ℕ, i + k ≤ N →
      ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pzIter i G)) V := by
  intro i
  induction i with
  | zero => intro k hk; simpa using h.of_le (Nat.cast_le.mpr (show k ≤ N by omega))
  | succ i ih =>
      intro k hik
      have h2 : ContDiffOn ℝ (((k + 1 : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.pzIter i G)) V := ih (k + 1) (by omega)
      simpa [Work.Spaces.pzIter_succ] using contDiffOn_uncurry_pz_le hV h2

/-- The iterated `θ`-partial `∂_θ^i` costs `i` orders of differentiability. -/
theorem contDiffOn_uncurry_pthIter_le {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) V) :
    ∀ i k : ℕ, i + k ≤ N →
      ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pthIter i G)) V := by
  intro i
  induction i with
  | zero => intro k hk; simpa using h.of_le (Nat.cast_le.mpr (show k ≤ N by omega))
  | succ i ih =>
      intro k hik
      have h2 : ContDiffOn ℝ (((k + 1 : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.pthIter i G)) V := ih (k + 1) (by omega)
      simpa [Work.Spaces.pthIter_succ] using contDiffOn_uncurry_pth_le hV h2

/-- The `z`-slice of a function that is `C^N` on an open set is `C^N` at the point. -/
theorem contDiffAt_slice_fst_of_uncurry {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {N : ℕ} (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) V)
    {z θ : ℝ} (hz : (z, θ) ∈ V) :
    ContDiffAt ℝ ((N : ℕ) : WithTop ℕ∞) (fun z' => G z' θ) z := by
  have hc : ContDiffAt ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) (z, θ) :=
    h.contDiffAt (hV.mem_nhds hz)
  have hlin : ContDiffAt ℝ ((N : ℕ) : WithTop ℕ∞) (fun z' : ℝ => (z', θ)) z := by fun_prop
  simpa [Function.comp_def, Function.uncurry] using hc.comp z hlin

/-- Differentiability of the `z`-slice of an iterated `z`-partial, at a point of an open
set where the function is smooth enough. -/
theorem differentiableAt_slice_pzIter {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {N : ℕ} (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) V)
    {i : ℕ} (hi : i + 1 ≤ N) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter i G z' θ) z := by
  have h1 : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.pzIter i G)) V :=
    contDiffOn_uncurry_pzIter_le hV h i 1 (by omega)
  have h2 : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun z' => Work.Spaces.pzIter i G z' θ) z :=
    contDiffAt_slice_fst_of_uncurry hV h1 hz
  exact h2.differentiableAt (by simp)

/-- Smoothness of the `z`-slice of an iterated `θ`-partial. -/
theorem contDiffAt_slice_pthIter {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) V)
    {i k : ℕ} (hi : i + k ≤ N) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) (fun z' => Work.Spaces.pthIter i G z' θ) z :=
  contDiffAt_slice_fst_of_uncurry hV (contDiffOn_uncurry_pthIter_le hV h i k hi) hz

/-! ## The expansion of `D_z^n = (z∂_z)^n` in Stirling numbers -/

/-- The derivative of `z ↦ z^k`. -/
private theorem deriv_zpow (k : ℕ) (z : ℝ) :
    deriv (fun z' : ℝ => z' ^ k) z = (k : ℝ) * z ^ (k - 1) := by
  have h := deriv_pow (f := fun z' : ℝ => z') (x := z) differentiableAt_id k
  rw [show (fun z' : ℝ => z') ^ k = (fun z' : ℝ => z' ^ k) from rfl] at h
  have h1 : deriv (fun z' : ℝ => z') z = 1 := deriv_id z
  rw [h, h1]
  ring

/-- The elementary algebra of one term of the induction step. -/
private theorem z_mul_term (k : ℕ) (z A B : ℝ) :
    z * ((k : ℝ) * z ^ (k - 1) * A + z ^ k * B) = (k : ℝ) * z ^ k * A + z ^ (k + 1) * B := by
  rcases k with _ | m
  · ring
  · rw [pow_succ]; push_cast; ring

/-- **The Stirling expansion of `D_z^n`**, at a point where the `z`-slice of `h` is
`C^{n+1}` on an open set contained in the domain:
`D_z^n h = ∑_{k ≤ n} S(n,k) z^k ∂_z^k h`. -/
theorem DzIter_eq_sum_scoef_of_contDiffOn (h : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (hU : IsOpen U) :
    ∀ n : ℕ, ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry h) U →
      ∀ z θ, (z, θ) ∈ U →
        Work.Spaces.DzIter n h z θ =
          ∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ) * (z ^ k * Work.Spaces.pzIter k h z θ) := by
  intro n
  induction n with
  | zero =>
      intro hsm z θ hzθ
      rw [Finset.sum_range_one, show Work.Spaces.scoef 0 0 = 1 from rfl]
      norm_num
  | succ n ih =>
      intro hsm z θ hzθ
      have hsm' : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry h) U :=
        hsm.of_le (Nat.cast_le.mpr (show n + 1 ≤ n + 2 by omega))
      have hdiff : ∀ k : ℕ, k ≤ n →
          DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k h z' θ) z := fun k hk =>
        differentiableAt_slice_pzIter hU hsm (i := k) (by omega) hzθ
      have hd1 : ∀ k : ℕ, DifferentiableAt ℝ (fun z' : ℝ => z' ^ k) z := fun k =>
        differentiableAt_pow k
      have hd3 : ∀ k ∈ Finset.range (n + 1),
          DifferentiableAt ℝ (fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ) z :=
        fun k hk => (hd1 k).mul (hdiff k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
      have hsl : {z' : ℝ | (z', θ) ∈ U} ∈ 𝓝 z := by
        have hopen : IsOpen {z' : ℝ | (z', θ) ∈ U} :=
          hU.preimage (by fun_prop : Continuous fun z' : ℝ => (z', θ))
        exact hopen.mem_nhds hzθ
      have hev : (fun z' => Work.Spaces.DzIter n h z' θ)
          =ᶠ[𝓝 z] (fun z' => ∑ k ∈ Finset.range (n + 1),
              (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
        filter_upwards [hsl] with z' hz'
        exact ih hsm' z' θ hz'
      have hterm : ∀ k : ℕ, k ≤ n →
          deriv (fun z' : ℝ => (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ)) z
            = (Work.Spaces.scoef n k : ℝ)
                * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                    + z ^ k * Work.Spaces.pzIter (k + 1) h z θ) := by
        intro k hk
        rw [deriv_const_mul (d := fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ)
          (Work.Spaces.scoef n k : ℝ) ((hd1 k).mul (hdiff k hk))]
        congr 1
        rw [show (fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ)
              = (fun z' : ℝ => z' ^ k) * (fun z' : ℝ => Work.Spaces.pzIter k h z' θ) from rfl,
          deriv_mul (hd1 k) (hdiff k hk), deriv_zpow]
        rfl
      have hderiv : deriv (fun z' => Work.Spaces.DzIter n h z' θ) z
          = ∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ)
              * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                  + z ^ k * Work.Spaces.pzIter (k + 1) h z θ) := by
        rw [hev.deriv_eq]
        have hsumfun : (fun z' => ∑ k ∈ Finset.range (n + 1),
              (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ))
            = (∑ k ∈ Finset.range (n + 1),
                fun z' => (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
          funext z'
          simp [Finset.sum_apply]
        rw [hsumfun, deriv_sum (fun k hk => (hd3 k hk).const_mul (Work.Spaces.scoef n k : ℝ))]
        exact Finset.sum_congr rfl fun k hk =>
          hterm k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      calc Work.Spaces.DzIter (n + 1) h z θ
          = z * deriv (fun z' => Work.Spaces.DzIter n h z' θ) z := by
            simp [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
        _ = z * (∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ)
              * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                  + z ^ k * Work.Spaces.pzIter (k + 1) h z θ)) := by rw [hderiv]
        _ = ∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ)
              * ((k : ℝ) * z ^ k * Work.Spaces.pzIter k h z θ
                  + z ^ (k + 1) * Work.Spaces.pzIter (k + 1) h z θ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [show z * ((Work.Spaces.scoef n k : ℝ)
                  * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                      + z ^ k * Work.Spaces.pzIter (k + 1) h z θ))
                = (Work.Spaces.scoef n k : ℝ)
                  * (z * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                      + z ^ k * Work.Spaces.pzIter (k + 1) h z θ)) from by ring,
              z_mul_term]
        _ = ∑ j ∈ Finset.range (n + 2),
              (Work.Spaces.scoef (n + 1) j : ℝ) * (z ^ j * Work.Spaces.pzIter j h z θ) :=
            Work.Spaces.scoef_sum_shift n (fun k => Work.Spaces.pzIter k h z θ) z

/-- **The angular expansion commutes with `∂_z^k`**: on an open set where `F` is smooth
enough, the `k`-th `z`-derivative of the exact expansion of `D_θ^b` is the expansion of the
`k`-th `z`-derivative. -/
theorem pzIter_DthIter_expansion {F : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {N : ℕ}
    (hF : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry F) U)
    {b k : ℕ} (hb1 : b + 1 ≤ N) (hbk : b + k ≤ N) {z θ : ℝ} (hzθ : (z, θ) ∈ U) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter b F) z θ
      = ∑ r ∈ Finset.range (b + 1), dthCoef b r θ * Work.Spaces.pzIter k (Work.Spaces.pthIter r F) z θ := by
  have hexp : ∀ z' θ' : ℝ, (z', θ') ∈ U →
      Work.Spaces.DthIter b F z' θ'
        = ∑ r ∈ Finset.range (b + 1), dthCoef b r θ' * Work.Spaces.pthIter r F z' θ' :=
    fun z' θ' h => DthIter_expansion_of_contDiffOn b F U hU
      (hF.of_le (Nat.cast_le.mpr hb1)) z' θ' h
  have hsl : {z' : ℝ | (z', θ) ∈ U} ∈ 𝓝 z := by
    have hopen : IsOpen {z' : ℝ | (z', θ) ∈ U} :=
      hU.preimage (by fun_prop : Continuous fun z' : ℝ => (z', θ))
    exact hopen.mem_nhds hzθ
  have hev : (fun z' => Work.Spaces.DthIter b F z' θ)
      =ᶠ[𝓝 z] (fun z' => ∑ r ∈ Finset.range (b + 1),
          dthCoef b r θ * Work.Spaces.pthIter r F z' θ) := by
    filter_upwards [hsl] with z' hz'
    exact hexp z' θ hz'
  calc Work.Spaces.pzIter k (Work.Spaces.DthIter b F) z θ
      = iteratedDeriv k (fun z' => Work.Spaces.DthIter b F z' θ) z :=
        Work.Spaces.pzIter_eq_iteratedDeriv k _ z θ
    _ = iteratedDeriv k (fun z' => ∑ r ∈ Finset.range (b + 1),
          dthCoef b r θ * Work.Spaces.pthIter r F z' θ) z := hev.iteratedDeriv_eq k
    _ = ∑ r ∈ Finset.range (b + 1),
          dthCoef b r θ * iteratedDeriv k (fun z' => Work.Spaces.pthIter r F z' θ) z :=
        Work.Spaces.iteratedDeriv_sum_const_mul _ (fun r => dthCoef b r θ)
          (fun r z' => Work.Spaces.pthIter r F z' θ) k z
          (fun r hr => contDiffAt_slice_pthIter hU hF
            (i := r) (k := k) (by
              have hr' : r ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
              omega) hzθ)
    _ = ∑ r ∈ Finset.range (b + 1),
          dthCoef b r θ * Work.Spaces.pzIter k (Work.Spaces.pthIter r F) z θ := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Work.Spaces.pzIter_eq_iteratedDeriv]

/-! ## The main bound

`D_z^a D_θ^b F` is a *finite linear combination*, with coefficients bounded on the box, of the
plain derivatives `∂_z^k ∂_θ^r F = pzIter k (pthIter r F)` with `k ≤ a`, `r ≤ b`:

* `D_z^a = ∑_{k≤a} S(a,k) z^k ∂_z^k` (Stirling numbers of the second kind,
  `DzIter_eq_sum_scoef_of_contDiffOn`);
* `∂_z^k (D_θ^b F) = ∑_{r≤b} a_{b,r}(θ) · ∂_z^k∂_θ^r F` (`pzIter_DthIter_expansion`, from the
  exact expansion `D_θ^b = ∑_r a_{b,r} ∂_θ^r` of `DthIter_expansion_of_contDiffOn` and the fact
  that the coefficients `a_{b,r}` do not depend on `z`),
* and `|a_{b,r}(θ)| ≤ K_{b,r} |sin 2θ|^r ≤ K_{b,r}` (`DthCoef_sin_pow_bound`), while
  `|z| ≤ max |A| |B|` on `[A,B]`.

Every `pzIter k (pthIter r F)` occurring has `k + r ≤ a + b ≤ 4`, so the hypothesis bounds it by
`M`, giving `|D_z^a D_θ^b F| ≤ K M` with
`K = (∑_{k≤a} S(a,k) (max |A| |B|)^k) · (∑_{r≤b} K_{b,r})`. -/


end

end Work.FTS.GalBasis.Xmb
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS

/-- On the angular interval `Iθ = [0, π/2]` the open interval `(0, π/2)` is of full
measure: the two excluded points are singletons. -/
lemma ae_mem_Ioo_of_mem_Iθ_gal :
    ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Work.Spaces.Iθ → 0 < θ ∧ θ < Real.pi / 2 := by
  have hne : (volume : Measure ℝ) ({0, Real.pi / 2} : Set ℝ) = 0 := by
    have hf : ({0, Real.pi / 2} : Set ℝ).Finite :=
      (Set.finite_singleton (Real.pi / 2)).insert 0
    exact hf.measure_zero volume
  have hset : {θ : ℝ | ¬ (θ ∉ ({0, Real.pi / 2} : Set ℝ))} = ({0, Real.pi / 2} : Set ℝ) := by
    ext θ
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, not_not]
  have hmem : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({0, Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff, hset]
    exact hne
  filter_upwards [hmem] with θ hθ hθI
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hθ
  simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθI
  exact ⟨lt_of_le_of_ne hθI.1 (fun hh => hθ.1 hh.symm), lt_of_le_of_ne hθI.2 hθ.2⟩

/-- `L₁₂` sees a profile only through its values on the open quadrant `z > 0`,
`0 < θ < π/2`; consequently `L12f` depends only on those values. -/
theorem L12f_congr_of_agreeOnQ {a b : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 ≤ z)
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → a z θ = b z θ) :
    Work.Coercivity.L12f a z = Work.Coercivity.L12f b z := by
  have hinner : ∀ s ∈ Set.Ioi z,
      Work.FM.L12dens Work.Spaces.K a s = Work.FM.L12dens Work.Spaces.K b s := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt hz hs
    simp only [Work.FM.L12dens]
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [ae_mem_Ioo_of_mem_Iθ_gal] with θ hθ hθI
    obtain ⟨h1, h2⟩ := hθ hθI
    rw [h s θ hs0 h1 h2]
  simp only [Work.Coercivity.L12f, Work.FM.L12]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hinner

end Work.FTS.GalFields.RHS
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.hardyA_le_W =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set Filter
open scoped Topology

/-! ## Elementary helpers -/

/-- `x ^ p * (x ^ m * A) ^ 2 = x ^ (p + 2m) * A ^ 2` for `x > 0` and a natural power `m`. -/
private lemma rpow_natpow_mul_sq {x A : ℝ} (hx : 0 < x) (p : ℝ) (m : ℕ) :
    x ^ p * (x ^ m * A) ^ 2 = x ^ (p + 2 * (m : ℝ)) * A ^ 2 := by
  have hm : (x ^ m) ^ 2 = x ^ (2 * (m : ℝ)) := by
    rw [← pow_mul, ← Real.rpow_natCast x (m * 2)]
    congr 1
    push_cast
    ring
  rw [mul_pow, hm, Real.rpow_add hx]
  ring

/-- The rpow rearrangement used at the top level `k + 1`. -/
private lemma rpow_shift1 (k : ℕ) {γ x A : ℝ} (hx : 0 < x) :
    x ^ (-γ - 2) * (x ^ (k + 1) * A) ^ 2 = x ^ (2 * (k : ℝ) - γ) * A ^ 2 := by
  have h := rpow_natpow_mul_sq (A := A) hx (-γ - 2) (k + 1)
  have e : -γ - 2 + 2 * ((k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) - γ := by push_cast; ring
  rw [e] at h
  exact h

/-- The rpow rearrangement of the boundary term `ε ^ (-γ-1) G(ε)²`. -/
private lemma rpow_shift2 (k : ℕ) {γ x A : ℝ} (hx : 0 < x) :
    x ^ (-γ - 1) * (x ^ (k + 1) * A) ^ 2 = x ^ (2 * (k : ℝ) + 1 - γ) * A ^ 2 := by
  have h := rpow_natpow_mul_sq (A := A) hx (-γ - 1) (k + 1)
  have e : -γ - 1 + 2 * ((k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 1 - γ := by push_cast; ring
  rw [e] at h
  exact h

/-- The rpow rearrangement of the weight `t ^ (-γ) * ψ(t)²`. -/
private lemma rpow_shift3 (k : ℕ) {γ x A : ℝ} (hx : 0 < x) :
    x ^ (-γ) * (x ^ k * A) ^ 2 = x ^ (2 * (k : ℝ) - γ) * A ^ 2 := by
  have h := rpow_natpow_mul_sq (A := A) hx (-γ) k
  have e : -γ + 2 * ((k : ℕ) : ℝ) = 2 * (k : ℝ) - γ := by ring
  rw [e] at h
  exact h

/-- Pointwise AM–GM with the Hardy weights: for `x > 0` and `1 + γ > 0`,
`2 x^{-γ-1} A B ≤ ((1+γ)/2) x^{-γ-2} A² + (2/(1+γ)) x^{-γ} B²`. -/
private lemma amgm_hardy {γ x A B : ℝ} (hx : 0 < x) (hc : 0 < 1 + γ) :
    2 * (x ^ (-γ - 1) * A * B)
      ≤ (1 + γ) / 2 * (x ^ (-γ - 2) * A ^ 2) + (2 / (1 + γ)) * (x ^ (-γ) * B ^ 2) := by
  have h1 : (x ^ ((-γ - 2) / 2) * A) ^ 2 = x ^ (-γ - 2) * A ^ 2 := by
    rw [mul_pow, pow_two, ← Real.rpow_add hx]
    congr 1
    ring
  have h2 : (x ^ (-γ / 2) * B) ^ 2 = x ^ (-γ) * B ^ 2 := by
    rw [mul_pow, pow_two, ← Real.rpow_add hx]
    congr 1
    ring
  have hdiv : ((x ^ (-γ / 2) * B) ^ 2) / ((1 + γ) / 2)
      = (2 / (1 + γ)) * (x ^ (-γ) * B ^ 2) := by
    rw [h2]
    field_simp
  have hxx : x ^ ((-γ - 2) / 2) * x ^ (-γ / 2) = x ^ (-γ - 1) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hL : 2 * ((x ^ ((-γ - 2) / 2) * A) * (x ^ (-γ / 2) * B))
      = 2 * (x ^ (-γ - 1) * A * B) := by
    rw [← hxx]
    ring
  have ham := two_mul_le_mul_sq_add_div_sq (a := (1 + γ) / 2)
    (u := x ^ ((-γ - 2) / 2) * A) (v := x ^ (-γ / 2) * B) (by linarith)
  rw [hL, h1, hdiv] at ham
  exact ham

/-- Every iterated derivative of a function of class `C^∞` on the open interval `(0,x₁)` is
continuous there. -/
private theorem iteratedDeriv_continuousOn_Ioo' {g : ℝ → ℝ} {x₁ : ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Set.Ioo 0 x₁)) (m : ℕ) :
    ContinuousOn (fun x : ℝ => iteratedDeriv m g x) (Set.Ioo 0 x₁) := by
  have hs : UniqueDiffOn ℝ (Set.Ioo (0 : ℝ) x₁) := isOpen_Ioo.uniqueDiffOn
  have hcont : ContinuousOn (iteratedDerivWithin m g (Set.Ioo (0 : ℝ) x₁)) (Set.Ioo 0 x₁) :=
    hg.continuousOn_iteratedDerivWithin (by simp) hs
  exact hcont.congr fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm

/-- Continuity of a weighted product on a compact subinterval. -/
private lemma contOn_rpow_mul {a b p : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hF : ContinuousOn F (Set.Icc a b)) :
    ContinuousOn (fun t : ℝ => t ^ p * F t) (Set.Icc a b) :=
  (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le ha ht.1))).mul hF

/-! ## The truncated Hardy bound -/

/-- **The core estimate.** -/
private theorem hardyA_trunc_bound (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁))
    (hf0 : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hB : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    ∀ y x : ℝ, 0 < y → y < x → x < x₁ →
      (∫ t in y..x,
          t ^ (2 * (k : ℝ) - γ) * (iteratedDeriv k (fun z : ℝ => f z / z) t) ^ 2)
        ≤ 6 * (∫ t in (0 : ℝ)..x₁,
            t ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f t) ^ 2) / (1 + γ) ^ 2 := by
  intro y x hy hyx hxx₁
  set v : ℝ → ℝ := fun s => iteratedDeriv k (fun z : ℝ => f z / z) s with hv
  set ψ : ℝ → ℝ := fun s => s ^ k * iteratedDeriv (k + 1) f s with hψ
  set G : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, ψ s with hG
  set u : ℝ → ℝ := fun s => s ^ (2 * (k : ℝ) - γ) * v s ^ 2 with hu
  set w : ℝ → ℝ := fun s => s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2 with hw
  set Btot : ℝ := ∫ t in (0 : ℝ)..x₁, w t with hBtot
  have hc : 0 < 1 + γ := by linarith
  -- § continuity of `v` and `ψ` on the open interval
  have hgm : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ => f z / z) (Set.Ioo 0 x₁) :=
    (hf.mono Set.Ioo_subset_Ioc_self).div contDiffOn_id fun z hz => ne_of_gt hz.1
  have hvcont : ContinuousOn v (Set.Ioo 0 x₁) := by
    rw [hv]
    exact iteratedDeriv_continuousOn_Ioo' hgm k
  have hψcont : ContinuousOn ψ (Set.Ioo 0 x₁) := by
    rw [hψ]
    exact (continuousOn_id.pow k).mul
      (iteratedDeriv_continuousOn_Ioo' (hf.mono Set.Ioo_subset_Ioc_self) (k + 1))
  -- § primitive data
  obtain ⟨_, hGcont, hGderiv⟩ := primitiveDerivData k γ x₁ hx₁ hγ f hf hB
  have hGcont' : ContinuousOn G (Set.Icc 0 x₁) := hGcont
  have hGderiv' : ∀ t ∈ Set.Ioo (0 : ℝ) x₁, HasDerivAt G (ψ t) t := hGderiv
  -- § the two ingredients coming from `divSinPrimitive`
  obtain ⟨hident, hbnd⟩ := divSinPrimitive k γ x₁ hx₁ hγ f hf hf0 hB
  have hident' : ∀ t ∈ Set.Ioo (0 : ℝ) x₁, t ^ (k + 1) * v t = G t :=
    fun t ht => hident t ht
  have hbnd' : ∀ t ∈ Set.Ioo (0 : ℝ) x₁,
      t ^ (2 * (k : ℝ) + 1 - γ) * v t ^ 2 ≤ 1 / (1 + γ) * (∫ s in (0 : ℝ)..t, w s) :=
    fun t ht => hbnd t ht
  -- § continuity of the integrands on `[y,x]`
  have hGcx : ContinuousOn G (Set.Icc y x) :=
    hGcont'.mono fun t ht => ⟨le_trans (le_of_lt hy) ht.1, le_trans ht.2 (le_of_lt hxx₁)⟩
  have hψcx : ContinuousOn ψ (Set.Icc y x) :=
    hψcont.mono fun t ht => ⟨lt_of_lt_of_le hy ht.1, lt_of_le_of_lt ht.2 hxx₁⟩
  have hdG : ∀ t ∈ Set.Ioo y x, HasDerivAt G (ψ t) t :=
    fun t ht => hGderiv' t ⟨lt_trans hy ht.1, lt_trans ht.2 hxx₁⟩
  -- § the integration by parts
  have hibp := rpowSq_ibp (γ := γ) hy hyx.le hGcx hdG hψcx
  -- § identification of the left-hand integral
  have hEq1 : (∫ t in y..x, t ^ (-γ - 2) * G t ^ 2) = ∫ t in y..x, u t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hyx.le] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hy ht.1
    have htI : t ∈ Set.Ioo (0 : ℝ) x₁ := ⟨ht0, lt_of_le_of_lt ht.2 hxx₁⟩
    rw [← hident' t htI]
    simp only [hu]
    exact rpow_shift1 k ht0
  rw [hEq1] at hibp
  -- § AM–GM
  have hAM1 : 2 * (∫ t in y..x, t ^ (-γ - 1) * G t * ψ t)
      ≤ (1 + γ) / 2 * (∫ t in y..x, u t)
        + (2 / (1 + γ)) * (∫ t in y..x, t ^ (-γ) * ψ t ^ 2) := by
    have hpt : ∀ t ∈ Set.Icc y x,
        2 * (t ^ (-γ - 1) * G t * ψ t)
          ≤ (1 + γ) / 2 * (t ^ (-γ - 2) * G t ^ 2)
            + (2 / (1 + γ)) * (t ^ (-γ) * ψ t ^ 2) :=
      fun t ht => amgm_hardy (lt_of_lt_of_le hy ht.1) hc
    have hca : ContinuousOn (fun t : ℝ => t ^ (-γ - 2) * G t ^ 2) (Set.Icc y x) :=
      contOn_rpow_mul hy (hGcx.pow 2)
    have hcb : ContinuousOn (fun t : ℝ => t ^ (-γ) * ψ t ^ 2) (Set.Icc y x) :=
      contOn_rpow_mul hy (hψcx.pow 2)
    have hcf : ContinuousOn (fun t : ℝ => 2 * (t ^ (-γ - 1) * G t * ψ t)) (Set.Icc y x) :=
      ((contOn_rpow_mul hy (hGcx.mul hψcx)).const_mul 2).congr fun t _ => by
        simp only [Pi.mul_apply]
        ring
    have hcg : ContinuousOn
        (fun t : ℝ => (1 + γ) / 2 * (t ^ (-γ - 2) * G t ^ 2)
          + (2 / (1 + γ)) * (t ^ (-γ) * ψ t ^ 2)) (Set.Icc y x) :=
      (hca.const_mul _).add (hcb.const_mul _)
    have hif : IntervalIntegrable (fun t : ℝ => 2 * (t ^ (-γ - 1) * G t * ψ t))
        volume y x := hcf.intervalIntegrable_of_Icc hyx.le
    have hig : IntervalIntegrable
        (fun t : ℝ => (1 + γ) / 2 * (t ^ (-γ - 2) * G t ^ 2)
          + (2 / (1 + γ)) * (t ^ (-γ) * ψ t ^ 2)) volume y x :=
      hcg.intervalIntegrable_of_Icc hyx.le
    have hmono := intervalIntegral.integral_mono_on hyx.le hif hig hpt
    have hif1 : IntervalIntegrable (fun t : ℝ => (1 + γ) / 2 * (t ^ (-γ - 2) * G t ^ 2))
        volume y x := (hca.const_mul _).intervalIntegrable_of_Icc hyx.le
    have hif2 : IntervalIntegrable (fun t : ℝ => (2 / (1 + γ)) * (t ^ (-γ) * ψ t ^ 2))
        volume y x := (hcb.const_mul _).intervalIntegrable_of_Icc hyx.le
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hif1 hif2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
    rw [hEq1] at hmono
    exact hmono
  -- § the `ψ²` integral is dominated by `Btot`
  have hK : (∫ t in y..x, t ^ (-γ) * ψ t ^ 2) ≤ Btot := by
    have heq : (∫ t in y..x, t ^ (-γ) * ψ t ^ 2) = ∫ t in y..x, w t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hyx.le] at ht
      have ht0 : 0 < t := lt_of_lt_of_le hy ht.1
      simp only [hψ, hw]
      exact rpow_shift3 k ht0
    rw [heq, hBtot, intervalIntegral.integral_of_le hx₁.le,
      intervalIntegral.integral_of_le hyx.le]
    refine setIntegral_mono_set hB ?_ ?_
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun t ht => by
        simp only [hw]
        exact mul_nonneg (Real.rpow_pos_of_pos ht.1 _).le (sq_nonneg _)
    · exact Eventually.of_forall fun t ht =>
        ⟨lt_trans hy ht.1, le_of_lt (lt_of_le_of_lt ht.2 hxx₁)⟩
  -- § the boundary bound at `y`
  have hybd : y ^ (-γ - 1) * G y ^ 2 ≤ Btot / (1 + γ) := by
    have hyI : y ∈ Set.Ioo (0 : ℝ) x₁ := ⟨hy, lt_trans hyx hxx₁⟩
    have hb := hbnd' y hyI
    have hInt : (∫ s in (0 : ℝ)..y, w s) ≤ Btot := by
      rw [hBtot, intervalIntegral.integral_of_le hx₁.le,
        intervalIntegral.integral_of_le hy.le]
      refine setIntegral_mono_set hB ?_ ?_
      · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        exact Eventually.of_forall fun t ht => by
          simp only [hw]
          exact mul_nonneg (Real.rpow_pos_of_pos ht.1 _).le (sq_nonneg _)
      · exact Eventually.of_forall fun t ht =>
          ⟨ht.1, le_trans ht.2 (le_of_lt (lt_trans hyx hxx₁))⟩
    rw [← hident' y hyI, rpow_shift2 k hy]
    calc y ^ (2 * (k : ℝ) + 1 - γ) * v y ^ 2
        ≤ 1 / (1 + γ) * (∫ s in (0 : ℝ)..y, w s) := hb
      _ ≤ 1 / (1 + γ) * Btot := mul_le_mul_of_nonneg_left hInt (by positivity)
      _ = Btot / (1 + γ) := by ring
  -- § assembling
  have hxterm : 0 ≤ x ^ (-γ - 1) * G x ^ 2 :=
    mul_nonneg (Real.rpow_pos_of_pos (lt_trans hy hyx) _).le (sq_nonneg _)
  have hAM1' : 2 * (∫ t in y..x, t ^ (-γ - 1) * G t * ψ t)
      ≤ (1 + γ) / 2 * (∫ t in y..x, u t)
        + (2 / (1 + γ)) * (∫ t in y..x, t ^ (-γ) * ψ t ^ 2) := hAM1
  have hK' : (2 / (1 + γ)) * (∫ t in y..x, t ^ (-γ) * ψ t ^ 2)
      ≤ (2 / (1 + γ)) * Btot := mul_le_mul_of_nonneg_left hK (by positivity)
  have hstep : (1 + γ) * (∫ t in y..x, u t)
      ≤ y ^ (-γ - 1) * G y ^ 2 + (1 + γ) / 2 * (∫ t in y..x, u t)
        + (2 / (1 + γ)) * Btot := by
    linarith [hibp, hAM1', hK', hxterm]
  -- § final arithmetic
  have hmult := mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ 2 * (1 + γ))
  have eL : 2 * (1 + γ) * ((1 + γ) * (∫ t in y..x, u t))
      = 2 * (1 + γ) ^ 2 * (∫ t in y..x, u t) := by ring
  have e4 : 2 * (1 + γ) * (2 / (1 + γ) * Btot) = 4 * Btot := by
    field_simp
    ring
  have eR : 2 * (1 + γ) * (y ^ (-γ - 1) * G y ^ 2 + (1 + γ) / 2 * (∫ t in y..x, u t)
        + (2 / (1 + γ)) * Btot)
      = 2 * (1 + γ) * (y ^ (-γ - 1) * G y ^ 2) + (1 + γ) ^ 2 * (∫ t in y..x, u t)
        + 4 * Btot := by
    rw [mul_add, mul_add, e4]
    ring
  rw [eL, eR] at hmult
  have hP2 : 2 * (1 + γ) * (y ^ (-γ - 1) * G y ^ 2) ≤ 2 * Btot := by
    have h3 := mul_le_mul_of_nonneg_left hybd (by positivity : (0 : ℝ) ≤ 2 * (1 + γ))
    have e : 2 * (1 + γ) * (Btot / (1 + γ)) = 2 * Btot := by
      field_simp
    rwa [e] at h3
  have h4 : (1 + γ) ^ 2 * (∫ t in y..x, u t) ≤ 6 * Btot := by
    linarith [hmult, hP2]
  have hgoal : (∫ t in y..x, u t)
      ≤ 6 * Btot / (1 + γ) ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + γ) ^ 2)]
    linarith [h4]
  exact hgoal

/-- The target theorem (development copy). -/
theorem hardyA_le_W :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (γ x₁ : ℝ), 0 < x₁ → -1 < γ → ∀ f : ℝ → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁) →
      Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2) (Set.Ioc 0 x₁) →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (2 * (k : ℝ) - γ)
          * (iteratedDeriv k (fun y : ℝ => f y / y) x) ^ 2) (Set.Ioc 0 x₁) ∧
      (∫ x in (0 : ℝ)..x₁,
          x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv k (fun y : ℝ => f y / y) x) ^ 2)
        ≤ C / (1 + γ) ^ 2 *
          (∫ x in (0 : ℝ)..x₁,
            x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2) := by
  refine ⟨6, by norm_num, ?_⟩
  intro k γ x₁ hx₁ hγ f hf hf0 hB
  set v : ℝ → ℝ := fun x => iteratedDeriv k (fun y : ℝ => f y / y) x with hv
  set u : ℝ → ℝ := fun x => x ^ (2 * (k : ℝ) - γ) * v x ^ 2 with hu
  set ua : ℝ → ℝ := fun x => |u x| with hua
  set w : ℝ → ℝ := fun x => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2 with hw
  set Btot : ℝ := ∫ x in (0 : ℝ)..x₁, w x with hBtot
  have hgm : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ => f z / z) (Set.Ioo 0 x₁) :=
    (hf.mono Set.Ioo_subset_Ioc_self).div contDiffOn_id fun z hz => ne_of_gt hz.1
  have hvcont : ContinuousOn v (Set.Ioo 0 x₁) := by
    rw [hv]
    exact iteratedDeriv_continuousOn_Ioo' hgm k
  have hucont : ContinuousOn u (Set.Ioo 0 x₁) := by
    rw [hu]
    exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))).mul (hvcont.pow 2)
  have huacont : ContinuousOn ua (Set.Ioo 0 x₁) := by
    rw [hua]
    exact hucont.abs
  have htrunc0 := hardyA_trunc_bound k γ x₁ hx₁ hγ f hf hf0 hB
  have htrunc : ∀ y x : ℝ, 0 < y → y < x → x < x₁ →
      (∫ t in y..x, ua t) ≤ 6 * Btot / (1 + γ) ^ 2 := by
    intro y x hy hyx hxx₁
    have heq : (∫ t in y..x, ua t) = ∫ t in y..x, u t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hyx.le] at ht
      have ht0 : 0 < t := lt_of_lt_of_le hy ht.1
      simp only [hua]
      exact abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos ht0 _).le (sq_nonneg _))
    rw [heq]
    exact htrunc0 y x hy hyx hxx₁
  obtain ⟨hua_int, hua_bound⟩ :=
    integrableOn_Ioc_of_trunc hx₁ (fun t => abs_nonneg (u t)) huacont htrunc
  have hu_int : MeasureTheory.IntegrableOn u (Set.Ioc 0 x₁) := by
    refine hua_int.congr_fun (fun t ht => ?_) measurableSet_Ioc
    have ht0 : 0 < t := ht.1
    exact abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos ht0 _).le (sq_nonneg _))
  refine ⟨?_, ?_⟩
  · exact hu_int
  · have heq_final : (∫ t in (0 : ℝ)..x₁, u t) = ∫ t in (0 : ℝ)..x₁, ua t := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with t
      intro ht
      rw [Set.uIoc_of_le hx₁.le] at ht
      simp only [hua]
      exact (abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos ht.1 _).le (sq_nonneg _))).symm
    calc (∫ t in (0 : ℝ)..x₁, u t) = ∫ t in (0 : ℝ)..x₁, ua t := heq_final
      _ ≤ 6 * Btot / (1 + γ) ^ 2 := hua_bound
      _ = 6 / (1 + γ) ^ 2 * Btot := by ring

end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.H2.HeasyBlocksId =====
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

/-! ## Auxiliary facts for `HeasyBlocksId`

The identity is purely combinatorial: expanding `Heasy = H4PairInt - Hhard` and
splitting off the "top" (`D_z⁴` and `i + j = 4`) slots leaves exactly the block
products of `EasyZ · GblkZ` and `EasyM · GblkM`.  The only analytic input is the two
`rpow` identities squaring the weights of the flat pairing, which need
`sin(2θ) > 0`, i.e. precisely the hypothesis `θ ∈ (0, π/2)`.
-/




/-- `Whz z θ ^ 2 = w z ^ 2 · sin(2θ)^{-η}` for `sin(2θ) ≥ 0`. -/
theorem hbi_Whz_sq (z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    Whz z θ ^ 2 = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
  have h1 : Whz z θ
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
    rw [Whz_eq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta / 2)]
  have h2 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
    rw [pow_two, ← Real.rpow_add' hs (by rw [Work.Spaces.eta]; norm_num)]
    congr 1
    ring
  rw [h1, mul_pow, h2]

/-- `Wm α z θ ^ 2 = w z ^ 2 · sin(2θ)^{-γ}` for `sin(2θ) ≥ 0`. -/
theorem hbi_Wm_sq (α : ℝ) (z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    Wm α z θ ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have h1 : Wm α z θ
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    rw [Wm_eq, Work.Spaces.Wt, Work.Spaces.wTheta]
  rcases eq_or_ne (Work.Spaces.gam α) 0 with hg | hg
  · have hy : -(Work.Spaces.gam α / 2) = 0 := by rw [hg]; ring
    have hz : -(Work.Spaces.gam α) = 0 := by rw [hg]; ring
    rw [h1, hy, hz, Real.rpow_zero]
    ring
  · have h2 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [pow_two, ← Real.rpow_add' hs (by
        intro h
        exact hg (by linarith))]
      congr 1
      ring
    rw [h1, mul_pow, h2]


end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.RGWeak.AB_continuous =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR.RGWeak

open MeasureTheory Set

/-- Continuity of the lower antiderivative `z ↦ ∫_0^z f` on `[a,b]`, `0 < a`, for `f`
integrable on `(0,b]`.  (A general-purpose fact, isolated because it is used twice.) -/
lemma continuousOn_intervalIntegral_zero {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf : IntegrableOn f (Ioc 0 b)) :
    ContinuousOn (fun z => ∫ t in (0 : ℝ)..z, f t) (Icc a b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hInt : IntervalIntegrable f volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).2 hf
  have hcont : ContinuousOn (fun z => ∫ t in (0 : ℝ)..z, f t) (uIcc 0 b) :=
    intervalIntegral.continuousOn_primitive_interval' hInt left_mem_uIcc
  rw [uIcc_of_le hb.le] at hcont
  exact hcont.mono fun z hz => ⟨le_trans ha.le hz.1, hz.2⟩

/-- Continuity of the tail integral `z ↦ ∫_z^∞ f` on `[a,b]`, `0 < a`, for `f` integrable
on `(a,∞)`. -/
lemma continuousOn_setIntegral_Ioi {f : ℝ → ℝ} {a b : ℝ} (hf : IntegrableOn f (Ioi a)) :
    ContinuousOn (fun z => ∫ t in Ioi z, f t) (Icc a b) :=
  hf.continuousOn_Ici_primitive_Ioi.mono fun _ hz => hz.1

theorem AB_continuous {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun z => ∫ t in (0 : ℝ)..z,
        Work.EllipticEst.ModalSolution.RadGreenWeak.srcM α m c t) (Set.Icc a b) ∧
      ContinuousOn (fun z => ∫ t in Set.Ioi z,
        Work.EllipticEst.ModalSolution.RadGreenWeak.srcP α m c t) (Set.Icc a b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  refine ⟨continuousOn_intervalIntegral_zero ha hab ?_, continuousOn_setIntegral_Ioi ?_⟩
  · exact Work.EllipticEst.ModalSolution.RGW.srcM_integrable hα hα1 m hc hcm hb
  · exact Work.EllipticEst.ModalSolution.RGW.srcP_integrable hα hα1 m hc hcm ha

end Work.FTS.H2.ModalSolR.RGWeak
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.RGWeakAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR.RGWeak

open Work.EllipticEst.ModalSolution.RadGreenWeak

/-- `Fgen α s ψ z = pwt α z · (z^s ψ'(z) − s z^{s−1} ψ(z))` — the (negated) antiderivative
produced by the Lagrange identity with `v = z^s`. -/
def Fgen (α : ℝ) (s : ℝ) (ψ : ℝ → ℝ) (z : ℝ) : ℝ :=
  pwt α z * (z ^ s * deriv ψ z - s * z ^ (s - 1) * ψ z)

/-- `Fgen` vanishes where `ψ` and `ψ'` do. -/
theorem Fgen_eq_zero {α s : ℝ} {ψ : ℝ → ℝ} {z : ℝ} (h0 : ψ z = 0) (h1 : deriv ψ z = 0) :
    Fgen α s ψ z = 0 := by
  simp only [Fgen, h0, h1, mul_zero, sub_zero, mul_zero]

/-- The decaying indicial exponent `s⁻ = -(2m+5)/α` solves `α²s² + 5αs = λ_m`. -/
theorem indicial_sM {α : ℝ} (hα : α ≠ 0) (m : ℕ) :
    α ^ 2 * sM α m ^ 2 + 5 * α * sM α m = Work.FTS.PhiStar.Radial.lamR m := by
  simp only [sM, Work.FTS.PhiStar.Radial.lamR]
  field_simp <;> ring

/-- The growing indicial exponent `s⁺ = 2m/α` solves `α²s² + 5αs = λ_m`. -/
theorem indicial_sP {α : ℝ} (hα : α ≠ 0) (m : ℕ) :
    α ^ 2 * sP α m ^ 2 + 5 * α * sP α m = Work.FTS.PhiStar.Radial.lamR m := by
  simp only [sP, Work.FTS.PhiStar.Radial.lamR]
  field_simp <;> ring

/-- **The derivative of `Fgen`.**  If `s` solves the indicial equation `α²s² + 5αs = λ_m`, then
`(Fgen α s ψ)' = -(z^s (wgt · L ψ) + λ_m z^s wgt ψ)`, i.e. the Lagrange identity for `v = z^s`
reads `z^s · wgt · L ψ = - λ_m z^s wgt ψ - (Fgen α s ψ)'`. -/
theorem Fgen_hasDerivAt {α : ℝ} (hα : 0 < α) {m : ℕ} {s : ℝ}
    (hs : α ^ 2 * s ^ 2 + 5 * α * s = Work.FTS.PhiStar.Radial.lamR m)
    {ψ : ℝ → ℝ} (hψ : ContDiffOn ℝ 2 ψ (Set.Ioi 0)) :
    ∀ z : ℝ, 0 < z →
      HasDerivAt (Fgen α s ψ)
        (-(z ^ s * (wgt α z * Lneg α ψ z)
            + Work.FTS.PhiStar.Radial.lamR m * (z ^ s * wgt α z * ψ z))) z := by
  intro z hz
  have hv : ContDiffOn ℝ 2 (fun t : ℝ => t ^ s) (Set.Ioi 0) := fun t ht =>
    (Real.contDiffAt_rpow_const (p := s) (n := 2) (Or.inl (ne_of_gt ht))).contDiffWithinAt
  have h := Work.EllipticEst.ModalSolution.RGW.hasDerivAt_lagrange α hv hψ z hz
  have hfun : (fun y => pwt α y * (deriv (fun t : ℝ => t ^ s) y * ψ y - y ^ s * deriv ψ y))
      = fun y => - Fgen α s ψ y := by
    funext y
    simp only [Fgen, Real.deriv_rpow_const]
    ring
  rw [hfun] at h
  have hL : Lneg α (fun t : ℝ => t ^ s) z = - Work.FTS.PhiStar.Radial.lamR m * z ^ s :=
    Work.EllipticEst.ModalSolution.RGW.Lneg_rpow α m hz hs
  rw [hL] at h
  have h2 : HasDerivAt (Fgen α s ψ)
      (-(((z ^ s * Lneg α ψ z - (-(Work.FTS.PhiStar.Radial.lamR m) * z ^ s) * ψ z)
        * wgt α z))) z :=
    h.neg.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => by simp))
  exact h2.congr_deriv (by ring)

/-- A set integral over `Ioi 0` of a function vanishing off `(a,b)` (with `0 < a`) is the
interval integral over `[a,b]`. -/
theorem integral_Ioi_eq_intervalIntegral {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf : ∀ z : ℝ, z ∉ Set.Ioo a b → f z = 0) :
    ∫ z in Set.Ioi 0, f z = ∫ z in a..b, f z := by
  have h1 : ∫ z in Set.Ioi (0 : ℝ), f z = ∫ z in Set.Ioo a b, f z :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun z hz => by simp only [mem_Ioo] at hz ⊢; exact lt_trans ha hz.1)
      (fun z hz => hf z hz.2)
  rw [h1, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

end Work.FTS.H2.ModalSolR.RGWeak
end
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.radGreenContinuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

/-- **Continuity of the modal radial Green function on `(0,∞)`.**

`radGreen α m c` is the explicit Green's function of the mode-`m` Euler equation, i.e. the
combination `K·(z^{s⁻}·A(z) + z^{s⁺}·B(z))` of the primitive
`A z = ∫_0^z c t · t^{(2m+5)/α-1} dt` and the tail integral
`B z = ∫_z^∞ c t · t^{-2m/α-1} dt`, with `s⁻ = -(2m+5)/α`, `s⁺ = 2m/α` and
`K = 1/(α(4m+5))`.  Both integrands are integrable — the head weight obeys
`(2m+5)/α - 1 ≥ 4 > -1` because `α ≤ 1`, and the tail weight `-2m/α-1 ≤ -1` with the integral
taken over `(z,∞)`, `z > 0` — so the two integrals are honest and continuous, by
`contOn_primitive_Ioc` and `contOn_tailIoi`, and the prefactors `z^{s±}` are continuous on
`(0,∞)`. -/
theorem radGreenContinuousOn {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    ContinuousOn (Work.FTS.PhiStar.Radial.radGreen α m c) (Set.Ioi 0) := by
  -- The head exponent `(2m+5)/α` is `≥ 1`, the tail exponent `2m/α` is `≥ 0`.
  have hβ1 : (1 : ℝ) ≤ (2 * (m : ℝ) + 5) / α := by
    rw [le_div_iff₀ hα]
    have h5 : (1 : ℝ) ≤ 2 * (m : ℝ) + 5 := by
      have := Nat.cast_nonneg (α := ℝ) m
      linarith
    linarith
  have hβ2 : (0 : ℝ) ≤ 2 * (m : ℝ) / α :=
    div_nonneg (by positivity) (le_of_lt hα)
  -- Integrability of the two integrands, on `(0,z]` resp. `(z,∞)`.
  have hint1 : ∀ z ∈ Set.Ioi 0, MeasureTheory.IntegrableOn
      (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioc 0 z) :=
    fun z hz => integrableOn_Ioc_mul_rpow_sub_one (β := (2 * (m : ℝ) + 5) / α) hc hcm hβ1 hz
  have hint2 : ∀ z ∈ Set.Ioi 0, MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi z) :=
    fun z hz => integrableOn_Ioi_mul_rpow_neg (β := 2 * (m : ℝ) / α) hc hcm hβ2 hz
  -- Continuity of the two integral pieces.
  have hw1 : ContinuousOn (fun t : ℝ => t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
  have hw2 : ContinuousOn (fun t : ℝ => t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
  have hA : ContinuousOn (fun z => ∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioi 0) :=
    contOn_primitive_Ioc (w := fun t : ℝ => t ^ ((2 * (m : ℝ) + 5) / α - 1)) hc hcm hw1 hint1
  have hB : ContinuousOn (fun z => ∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 0) :=
    contOn_tailIoi (w := fun t : ℝ => t ^ (-(2 * (m : ℝ) / α) - 1)) hc hcm hw2 hint2
  -- Continuity of the two power prefactors.
  have hpowN : ContinuousOn (fun z : ℝ => z ^ (-(2 * (m : ℝ) + 5) / α)) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
  have hpowP : ContinuousOn (fun z : ℝ => z ^ (2 * (m : ℝ) / α)) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
  -- Assembly: the value of `radGreen` is *definitionally* this combination.
  have hinner : ContinuousOn (fun z : ℝ =>
      z ^ (-(2 * (m : ℝ) + 5) / α) * (∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
        + z ^ (2 * (m : ℝ) / α) * (∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1)))
      (Set.Ioi 0) :=
    (hpowN.mul hA).add (hpowP.mul hB)
  refine (hinner.const_mul (1 / (α * (4 * (m : ℝ) + 5)))).congr (fun z _ => ?_)
  rfl

end Work.FTS.H2.ModalSolR
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.supBoundOfIntegrals =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.H2.ModalSolR

/-- **Comparison of an integral over `[c,d] ⊆ Iθ` with the `cos`-weighted integral over
`Iθ`.**  If `0 < c < d < π/2`, `F ≥ 0` and `∫_{Iθ} F cos` converges, then
`∫_c^d F ≤ (1/cos d) · ∫_{Iθ} F cos`: the only loss is the factor `1/cos d`, since
`cos t ≥ cos d > 0` for `t ∈ [c,d]` and `[c,d] ⊆ Iθ` with a nonnegative integrand. -/
private lemma intervalIntegral_le_inv_cos_Itheta_aux {c d : ℝ} (hcd : c < d) (hc : 0 < c)
    (hd : d < Real.pi / 2) (F : ℝ → ℝ) (hF0 : ∀ t, 0 ≤ F t)
    (hFi : IntegrableOn (fun t => F t * Real.cos t) Work.Spaces.Iθ) :
    (∫ t in c..d, F t) ≤ (1 / Real.cos d) * ∫ t in Work.Spaces.Iθ, F t * Real.cos t := by
  have hcosd : 0 < Real.cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hc], hd⟩
  have hsub : Set.Ioc c d ⊆ Work.Spaces.Iθ := fun t ht =>
    ⟨(lt_trans hc ht.1).le, (lt_of_le_of_lt ht.2 hd).le⟩
  have hcos_t : ∀ t ∈ Work.Spaces.Iθ, 0 ≤ Real.cos t := by
    intro t ht
    rw [Work.Spaces.Iθ] at ht
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, ht.1],
      by linarith [Real.pi_pos, ht.2]⟩
  have hcos_ge : ∀ t ∈ Set.Ioc c d, Real.cos d ≤ Real.cos t := fun t ht =>
    Real.cos_le_cos_of_nonneg_of_le_pi (lt_trans hc ht.1).le (by linarith [Real.pi_pos, hd])
      ht.2
  have hIntFc : IntegrableOn (fun t => F t * Real.cos t) (Set.Ioc c d) := hFi.mono_set hsub
  -- the pointwise comparison with the weighted integrand, on `(c,d]`
  have hstep1 : (∫ t in Set.Ioc c d, F t)
      ≤ ∫ t in Set.Ioc c d, (1 / Real.cos d) * (F t * Real.cos t) := by
    have hpt : ∀ t ∈ Set.Ioc c d, F t ≤ (1 / Real.cos d) * (F t * Real.cos t) := by
      intro t ht
      have h1 : 1 ≤ Real.cos t / Real.cos d := (one_le_div hcosd).mpr (hcos_ge t ht)
      calc F t = F t * 1 := by ring
        _ ≤ F t * (Real.cos t / Real.cos d) := mul_le_mul_of_nonneg_left h1 (hF0 t)
        _ = (1 / Real.cos d) * (F t * Real.cos t) := by ring
    exact MeasureTheory.setIntegral_mono_of_nonneg (fun t _ => hF0 t) hpt
      (hIntFc.const_mul _)
  -- enlarging the domain from `(c,d]` to `Iθ`
  have hstep2 : (∫ t in Set.Ioc c d, F t * Real.cos t)
      ≤ ∫ t in Work.Spaces.Iθ, F t * Real.cos t := by
    have hnn : 0 ≤ᵐ[volume.restrict (Work.Spaces.Iθ)] (fun t => F t * Real.cos t) := by
      show ∀ᵐ t ∂(volume.restrict (Work.Spaces.Iθ)), 0 ≤ F t * Real.cos t
      rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall (fun t ht => mul_nonneg (hF0 t) (hcos_t t ht))
    exact MeasureTheory.setIntegral_mono_set hFi hnn
      (Filter.Eventually.of_forall (fun t ht => hsub ht))
  rw [intervalIntegral.integral_of_le hcd.le]
  calc (∫ t in Set.Ioc c d, F t)
      ≤ ∫ t in Set.Ioc c d, (1 / Real.cos d) * (F t * Real.cos t) := hstep1
    _ = (1 / Real.cos d) * ∫ t in Set.Ioc c d, F t * Real.cos t := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (1 / Real.cos d) * ∫ t in Work.Spaces.Iθ, F t * Real.cos t :=
        mul_le_mul_of_nonneg_left hstep2 (div_nonneg zero_le_one hcosd.le)

theorem supBoundOfIntegrals {c d : ℝ} (hcd : c < d) (hc : 0 < c) (hd : d < Real.pi / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (v : ℝ → ℝ),
      ContDiffOn ℝ 1 v (Set.Icc 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => v θ ^ 2 * Real.cos θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv v θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ →
      ∀ θ ∈ Set.Icc c d,
        |v θ| ≤ K * Real.sqrt ((∫ θ in Work.Spaces.Iθ, v θ ^ 2 * Real.cos θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv v θ) ^ 2 * Real.cos θ)) := by
  have hcosd : 0 < Real.cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hc], hd⟩
  have hLpos : 0 < d - c := sub_pos.mpr hcd
  have hcosd1 : 0 < 1 / Real.cos d := div_pos one_pos hcosd
  have hcos_t : ∀ t ∈ Work.Spaces.Iθ, 0 ≤ Real.cos t := by
    intro t ht
    rw [Work.Spaces.Iθ] at ht
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, ht.1],
      by linarith [Real.pi_pos, ht.2]⟩
  have hIθmeas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hKpos : 0 < Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)
      + Real.sqrt (d - c) * Real.sqrt (1 / Real.cos d) := by
    have ha : 0 < Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c) :=
      div_pos (Real.sqrt_pos_of_pos hcosd1) (Real.sqrt_pos_of_pos hLpos)
    have hb : 0 ≤ Real.sqrt (d - c) * Real.sqrt (1 / Real.cos d) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    linarith
  refine ⟨Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)
      + Real.sqrt (d - c) * Real.sqrt (1 / Real.cos d), hKpos, ?_⟩
  intro v hv h1 h2 θ hθ
  -- the two weighted integrals over `Iθ`
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, v θ ^ 2 * Real.cos θ with hAdef
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv v θ) ^ 2 * Real.cos θ with hBdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact MeasureTheory.setIntegral_nonneg hIθmeas (fun t ht => mul_nonneg (sq_nonneg _)
      (hcos_t t ht))
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact MeasureTheory.setIntegral_nonneg hIθmeas (fun t ht => mul_nonneg (sq_nonneg _)
      (hcos_t t ht))
  -- comparison of the `[c,d]`-integrals with `A` and `B`
  have hX : (∫ x in c..d, v x ^ 2) ≤ (1 / Real.cos d) * A := by
    rw [hAdef]
    exact intervalIntegral_le_inv_cos_Itheta_aux hcd hc hd (fun t => v t ^ 2)
      (fun t => sq_nonneg _) h1
  have hY : (∫ x in c..d, (deriv v x) ^ 2) ≤ (1 / Real.cos d) * B := by
    rw [hBdef]
    exact intervalIntegral_le_inv_cos_Itheta_aux hcd hc hd (fun t => (deriv v t) ^ 2)
      (fun t => sq_nonneg _) h2
  -- the two square-root bounds
  have hsX : Real.sqrt (∫ x in c..d, v x ^ 2)
      ≤ Real.sqrt (1 / Real.cos d) * Real.sqrt (A + B) := by
    calc Real.sqrt (∫ x in c..d, v x ^ 2)
        ≤ Real.sqrt ((1 / Real.cos d) * A) := Real.sqrt_le_sqrt hX
      _ ≤ Real.sqrt ((1 / Real.cos d) * (A + B)) := by
          refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ hcosd1.le)
          linarith
      _ = Real.sqrt (1 / Real.cos d) * Real.sqrt (A + B) := Real.sqrt_mul hcosd1.le (A + B)
  have hsY : Real.sqrt (∫ x in c..d, (deriv v x) ^ 2)
      ≤ Real.sqrt (1 / Real.cos d) * Real.sqrt (A + B) := by
    calc Real.sqrt (∫ x in c..d, (deriv v x) ^ 2)
        ≤ Real.sqrt ((1 / Real.cos d) * B) := Real.sqrt_le_sqrt hY
      _ ≤ Real.sqrt ((1 / Real.cos d) * (A + B)) := by
          refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ hcosd1.le)
          linarith
      _ = Real.sqrt (1 / Real.cos d) * Real.sqrt (A + B) := Real.sqrt_mul hcosd1.le (A + B)
  -- the one-dimensional Sobolev bound on `[c,d]`
  have hvcd : ContDiffOn ℝ 1 v (Set.Icc c d) :=
    hv.mono fun x hx => ⟨le_trans hc.le hx.1, le_trans hx.2 hd.le⟩
  have habs := _root_.Work.EllipticEst.ModalSolution.abs_le_of_l2_Icc v hcd hθ hvcd
  calc |v θ|
      ≤ Real.sqrt (∫ x in c..d, v x ^ 2) / Real.sqrt (d - c)
          + Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv v x) ^ 2) := habs
    _ ≤ (Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)) * Real.sqrt (A + B)
          + (Real.sqrt (d - c) * Real.sqrt (1 / Real.cos d)) * Real.sqrt (A + B) := by
        refine add_le_add ?_ ?_
        · calc Real.sqrt (∫ x in c..d, v x ^ 2) / Real.sqrt (d - c)
              ≤ (Real.sqrt (1 / Real.cos d) * Real.sqrt (A + B)) / Real.sqrt (d - c) :=
                div_le_div_of_nonneg_right hsX (Real.sqrt_nonneg _)
            _ = (Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)) * Real.sqrt (A + B) := by
                ring
        · calc Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv v x) ^ 2)
              ≤ Real.sqrt (d - c) * (Real.sqrt (1 / Real.cos d) * Real.sqrt (A + B)) :=
                mul_le_mul_of_nonneg_left hsY (Real.sqrt_nonneg _)
            _ = (Real.sqrt (d - c) * Real.sqrt (1 / Real.cos d)) * Real.sqrt (A + B) := by
                ring
    _ = (Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)
          + Real.sqrt (d - c) * Real.sqrt (1 / Real.cos d)) * Real.sqrt (A + B) := by ring

end Work.FTS.H2.ModalSolR
end
end
-- ===== merged: Submission.Work.FTS.H2.StarPkg.LzeroSubst.lzero_sin_cos_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.StarPkg.LzeroSubst

set_option autoImplicit false

/-! ## Two elementary `HasDerivAt` rules

`sin θ cos θ` and `cos²θ - sin²θ` are the two angular factors produced by differentiating
`S C · g` once and twice. -/

/-- First derivative of `sin θ cos θ · g θ`: `∂_θ(sin θ cos θ · g) = (cos²θ - sin²θ) g +
sin θ cos θ · g'`. -/
lemma hasDerivAt_sin_cos_mul {g : ℝ → ℝ} {θ f' : ℝ} (h : HasDerivAt g f' θ) :
    HasDerivAt (fun θ' => Real.sin θ' * Real.cos θ' * g θ')
      ((Real.cos θ ^ 2 - Real.sin θ ^ 2) * g θ + (Real.sin θ * Real.cos θ) * f') θ := by
  have ha : HasDerivAt (fun θ' : ℝ => Real.sin θ' * Real.cos θ')
      (Real.cos θ ^ 2 - Real.sin θ ^ 2) θ := by
    have h0 := (Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_cos θ)
    convert h0 using 1
    ring
  exact ha.mul h

/-- Second derivative of `sin θ cos θ · g θ`:
`∂_θθ(sin θ cos θ · g) = -4 sin θ cos θ · g + 2(cos²θ - sin²θ) g' + sin θ cos θ · g''`. -/
lemma hasDerivAt_snd_sin_cos_mul {g : ℝ → ℝ} {θ f' f'' : ℝ}
    (h : HasDerivAt g f' θ) (h' : HasDerivAt (deriv g) f'' θ) :
    HasDerivAt (fun θ' => (Real.cos θ' ^ 2 - Real.sin θ' ^ 2) * g θ'
        + (Real.sin θ' * Real.cos θ') * deriv g θ')
      (-4 * (Real.sin θ * Real.cos θ) * g θ
        + 2 * (Real.cos θ ^ 2 - Real.sin θ ^ 2) * f'
        + (Real.sin θ * Real.cos θ) * f'') θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => Real.cos θ' ^ 2 - Real.sin θ' ^ 2)
      (-4 * Real.sin θ * Real.cos θ) θ := by
    have hft : (fun θ' : ℝ => Real.cos θ' ^ 2 - Real.sin θ' ^ 2)
        = fun θ' => Real.cos (2 * θ') := by
      funext θ'; rw [Real.cos_two_mul, Real.sin_sq]; ring
    have h0 : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-(2 * Real.sin (2 * θ))) θ := by
      have hlin : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
        simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
      have hh := hlin.cos
      convert hh using 1
      ring
    rw [hft]
    convert h0 using 1
    rw [Real.sin_two_mul]; ring
  have h2 : HasDerivAt (fun θ' : ℝ => Real.sin θ' * Real.cos θ')
      (Real.cos θ ^ 2 - Real.sin θ ^ 2) θ := by
    have h0 : HasDerivAt (fun θ' : ℝ => Real.sin θ' * Real.cos θ')
        (Real.cos θ * Real.cos θ + Real.sin θ * -Real.sin θ) θ :=
      (Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_cos θ)
    convert h0 using 1
    ring
  have hmain := (h1.mul h).add (h2.mul h')
  convert hmain using 1
  rw [h.deriv]; ring

/-! ## The substitution identity -/

theorem lzero_sin_cos_mul (w : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (h1 : DifferentiableOn ℝ (fun θ' => w z θ') (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h2 : DifferentiableOn ℝ (fun θ' => deriv (fun θ'' => w z θ'') θ')
      (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    Work.Elliptic.Lzero (fun z θ => Real.sin θ * Real.cos θ * w z θ) z θ
      = -(Real.sin θ * Real.cos θ) * Work.Spaces.pthIter 2 w z θ
        + (3 * Real.sin θ ^ 2 - 2 * Real.cos θ ^ 2) * Work.Spaces.pth w z θ := by
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  -- the second `θ`-derivative of `sin θ cos θ · w`
  have hA : deriv (fun θ' => deriv (fun θ'' => Real.sin θ'' * Real.cos θ'' * w z θ'') θ') θ
      = -4 * (Real.sin θ * Real.cos θ) * w z θ
        + 2 * (Real.cos θ ^ 2 - Real.sin θ ^ 2) * deriv (fun θ'' => w z θ'') θ
        + (Real.sin θ * Real.cos θ) * deriv (fun θ' => deriv (fun θ'' => w z θ'') θ') θ := by
    have heq : (fun θ' => deriv (fun θ'' => Real.sin θ'' * Real.cos θ'' * w z θ'') θ')
        =ᶠ[𝓝 θ] fun θ' => (Real.cos θ' ^ 2 - Real.sin θ' ^ 2) * (fun θ'' => w z θ'') θ'
            + (Real.sin θ' * Real.cos θ') * deriv (fun θ'' => w z θ'') θ' := by
      filter_upwards [hIoo] with θ' hθ'
      have hd : HasDerivAt (fun θ'' : ℝ => w z θ'') (deriv (fun θ'' : ℝ => w z θ'') θ') θ' :=
        (h1.differentiableAt (isOpen_Ioo.mem_nhds hθ')).hasDerivAt
      exact (hasDerivAt_sin_cos_mul hd).deriv
    rw [heq.deriv_eq]
    exact (hasDerivAt_snd_sin_cos_mul (g := fun θ'' => w z θ'')
      (h1.differentiableAt hIoo).hasDerivAt (h2.differentiableAt hIoo).hasDerivAt).deriv
  -- the first `θ`-derivative of `tan θ · (sin θ cos θ · w)`
  have hB : deriv (fun θ' => Real.tan θ' * (Real.sin θ' * Real.cos θ' * w z θ')) θ
      = 2 * (Real.sin θ * Real.cos θ) * w z θ
        + Real.sin θ ^ 2 * deriv (fun θ'' => w z θ'') θ := by
    have hne : ∀ᶠ θ' in 𝓝 θ, Real.cos θ' ≠ 0 := Real.continuous_cos.continuousAt.eventually_ne hcos
    have heq : (fun θ' => Real.tan θ' * (Real.sin θ' * Real.cos θ' * w z θ'))
        =ᶠ[𝓝 θ] fun θ' => Real.sin θ' ^ 2 * w z θ' := by
      filter_upwards [hne] with θ' h'
      rw [Real.tan_eq_sin_div_cos]
      field_simp
    rw [heq.deriv_eq]
    have hd : HasDerivAt (fun θ' : ℝ => Real.sin θ' ^ 2) (2 * Real.sin θ * Real.cos θ) θ := by
      have h0 := (Real.hasDerivAt_sin θ).pow 2
      convert h0 using 1
      ring
    rw [(show deriv (fun θ' : ℝ => Real.sin θ' ^ 2 * w z θ') θ
          = deriv ((fun θ' : ℝ => Real.sin θ' ^ 2) * fun θ' => w z θ') θ from rfl),
        (hd.mul (h1.differentiableAt hIoo).hasDerivAt).deriv]
    ring
  simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
    Work.Spaces.pth]
  rw [hA, hB]
  ring

end Work.FTS.H2.StarPkg.LzeroSubst
end
end
-- ===== merged: Submission.Work.FTS.H2.StarPkg.Subst =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.StarPkg

set_option autoImplicit false

/-- **`ℛ(sin 2θ · Φ) = 2Φ + 2α sin²θ · D_zΦ + sin 2θ · ∂_θΦ`.**  The two `tan θ` factors of
`ℛ = 2 tan θ·g + α tan θ·D_zg + ∂_θg` cancel against the `sin 2θ` into the bounded quantities
`2 sin²θ` and `2α sin²θ`. -/
theorem Rop_sin_two_mul (α : ℝ) (Φ : ℝ → ℝ → ℝ) (z θ : ℝ) (hcos : Real.cos θ ≠ 0)
    (hθ : DifferentiableAt ℝ (fun θ' => Φ z θ') θ) :
    Work.Construction.Rop α (fun z θ => Real.sin (2 * θ) * Φ z θ) z θ
      = 2 * Φ z θ + 2 * α * Real.sin θ ^ 2 * Work.Spaces.Dz Φ z θ
        + Real.sin (2 * θ) * Work.Spaces.pth Φ z θ := by
  have hpz : Work.Spaces.pz (fun z θ => Real.sin (2 * θ) * Φ z θ) z θ
      = Real.sin (2 * θ) * Work.Spaces.pz Φ z θ := by
    simp only [Work.Spaces.pz]
    exact deriv_const_mul_field (Real.sin (2 * θ))
  have hsin2' : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
    have h2' : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    exact (Real.hasDerivAt_sin (2 * θ)).comp θ h2'
  have hpth : Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * Φ z θ) z θ
      = Real.cos (2 * θ) * 2 * Φ z θ + Real.sin (2 * θ) * Work.Spaces.pth Φ z θ := by
    simp only [Work.Spaces.pth]
    exact (hsin2'.mul hθ.hasDerivAt).deriv
  rw [Work.Construction.Rop, hpz, hpth]
  have hs2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have hc2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  field_simp
  rw [hs2, hc2, Work.Spaces.Dz, Work.Spaces.pz]
  linear_combination (4 * Real.cos θ * Φ z θ) * Real.sin_sq_add_cos_sq θ

/-- **`𝒰(sin 2θ · Φ) = -sin 2θ · (3Φ + α D_zΦ)`**, where
`𝒰(Ψ) = -3Ψ - α z ∂_zΨ`. -/
theorem Uop_sin_two_mul (α : ℝ) (Φ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Construction.Uop α (fun z θ => Real.sin (2 * θ) * Φ z θ) z θ
      = -(Real.sin (2 * θ) * (3 * Φ z θ + α * Work.Spaces.Dz Φ z θ)) := by
  have hpz : Work.Spaces.pz (fun z θ => Real.sin (2 * θ) * Φ z θ) z θ
      = Real.sin (2 * θ) * Work.Spaces.pz Φ z θ := by
    simp only [Work.Spaces.pz]
    exact deriv_const_mul_field (Real.sin (2 * θ))
  rw [Work.Construction.Uop, hpz, Work.Spaces.Dz, Work.Spaces.pz]
  ring

/-- **`𝒱(sin 2θ · Φ) = 2(cos²θ - 2 sin²θ)Φ + sin 2θ · ∂_θΦ`**, where
`𝒱(Ψ) = ∂_θΨ - tan θ · Ψ`. -/
theorem Vop_sin_two_mul (Φ : ℝ → ℝ → ℝ) (z θ : ℝ) (hcos : Real.cos θ ≠ 0)
    (hθ : DifferentiableAt ℝ (fun θ' => Φ z θ') θ) :
    Work.Construction.Vop (fun z θ => Real.sin (2 * θ) * Φ z θ) z θ
      = 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Φ z θ
        + Real.sin (2 * θ) * Work.Spaces.pth Φ z θ := by
  have hsin2' : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
    have h2' : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    exact (Real.hasDerivAt_sin (2 * θ)).comp θ h2'
  have hpth : Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * Φ z θ) z θ
      = Real.cos (2 * θ) * 2 * Φ z θ + Real.sin (2 * θ) * Work.Spaces.pth Φ z θ := by
    simp only [Work.Spaces.pth]
    exact (hsin2'.mul hθ.hasDerivAt).deriv
  rw [Work.Construction.Vop, hpth, Real.tan_eq_sin_div_cos]
  have hs2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have hc2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  rw [hs2, hc2]
  field_simp
  linear_combination (Φ z θ) * Real.sin_sq_add_cos_sq θ


end Work.FTS.H2.StarPkg
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row19Prep.H2bBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open.Row19Prep

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The derivative of an inverse power -/

/-- `∂_z (c·(1+z)^{-N}) = -c·N·(1+z)^{-(N+1)}` for `z > -1`. -/
theorem deriv_inv_pow (N : ℕ) (c z : ℝ) (hz : 0 < 1 + z) :
    deriv (fun t : ℝ => c * ((1 + t)⁻¹) ^ N) z = -c * (N : ℝ) * ((1 + z)⁻¹) ^ (N + 1) := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 z := by
    simpa using (hasDerivAt_id z).const_add (1 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => (1 + t)⁻¹) (-((1 + z)⁻¹) ^ 2) z := by
    have hv := h1.inv (ne_of_gt hz)
    have hval : -(1 : ℝ) / (1 + z) ^ 2 = -((1 + z)⁻¹) ^ 2 := by
      rw [div_eq_mul_inv, ← inv_pow]; ring
    rw [hval] at hv
    exact hv
  have h3 : HasDerivAt (fun t : ℝ => ((1 + t)⁻¹) ^ N)
      ((N : ℝ) * ((1 + z)⁻¹) ^ (N - 1) * (-((1 + z)⁻¹) ^ 2)) z := h2.pow N
  have h4 := h3.const_mul c
  rw [h4.deriv]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have hp : ((1 + z)⁻¹) ^ (N - 1) * ((1 + z)⁻¹) ^ 2 = ((1 + z)⁻¹) ^ (N + 1) := by
      rw [← pow_add, show N - 1 + 2 = N + 1 by omega]
    rw [show (N : ℝ) * ((1 + z)⁻¹) ^ (N - 1) * (-((1 + z)⁻¹) ^ 2)
        = -((N : ℝ) * (((1 + z)⁻¹) ^ (N - 1) * ((1 + z)⁻¹) ^ 2)) by ring, hp]
    ring

/-! ## The partial fractions and the derivative chain -/

/-- `P_k(j) = ∏_{i<j}(k+i)`. -/
def Pk (k j : ℕ) : ℝ := ∏ i ∈ Finset.range j, ((k : ℝ) + i)

theorem Pk_succ (k j : ℕ) : Pk k (j + 1) = Pk k j * ((k : ℝ) + j) := by
  rw [Pk, Pk, Finset.prod_range_succ]

/-- The closed form of `∂_z^j H₂` (as a function): `j`-th derivative of the four-term partial
fraction expansion of `H₂`. -/
def Sfun (j : ℕ) : ℝ → ℝ := fun z =>
  ((Pk 1 j * (-2)) * ((1 + z)⁻¹) ^ (j + 1) + (Pk 2 j * 8) * ((1 + z)⁻¹) ^ (j + 2))
    + ((Pk 3 j * (-10)) * ((1 + z)⁻¹) ^ (j + 3) + (Pk 4 j * 4) * ((1 + z)⁻¹) ^ (j + 4))

/-- The closed form of `∂_z^j H₂`, with the sign of the `j`-th derivative pulled out. -/
def FB (j : ℕ) : ℝ → ℝ := fun z => (-1) ^ j * Sfun j z

/-- The derivative chain `∂_z (FB j) = FB (j+1)` for `z > -1`. -/
theorem deriv_FB (j : ℕ) {z : ℝ} (hz : 0 < 1 + z) : deriv (FB j) z = FB (j + 1) z := by
  have hz1 : (1 + z) ≠ 0 := ne_of_gt hz
  have hsum : Sfun j = ((fun t : ℝ => (Pk 1 j * (-2)) * ((1 + t)⁻¹) ^ (j + 1))
      + (fun t : ℝ => (Pk 2 j * 8) * ((1 + t)⁻¹) ^ (j + 2)))
      + ((fun t : ℝ => (Pk 3 j * (-10)) * ((1 + t)⁻¹) ^ (j + 3))
        + (fun t : ℝ => (Pk 4 j * 4) * ((1 + t)⁻¹) ^ (j + 4))) := rfl
  have hdS : DifferentiableAt ℝ (Sfun j) z := by
    rw [hsum]; fun_prop
  have hD : ∀ (k : ℕ) (C : ℝ), deriv (fun t : ℝ => C * ((1 + t)⁻¹) ^ (j + k)) z
      = -C * ((j + k : ℕ) : ℝ) * ((1 + z)⁻¹) ^ (j + k + 1) := fun k C =>
    deriv_inv_pow (j + k) C z hz
  have hS : deriv (Sfun j) z
      = -(Pk 1 j * (-2)) * ((j + 1 : ℕ) : ℝ) * ((1 + z)⁻¹) ^ (j + 1 + 1)
        + (-(Pk 2 j * 8) * ((j + 2 : ℕ) : ℝ) * ((1 + z)⁻¹) ^ (j + 2 + 1)
        + (-(Pk 3 j * (-10)) * ((j + 3 : ℕ) : ℝ) * ((1 + z)⁻¹) ^ (j + 3 + 1)
        + (-(Pk 4 j * 4) * ((j + 4 : ℕ) : ℝ) * ((1 + z)⁻¹) ^ (j + 4 + 1)))) := by
    rw [hsum, deriv_add (by fun_prop) (by fun_prop),
      deriv_add (by fun_prop) (by fun_prop),
      deriv_add (by fun_prop) (by fun_prop),
      hD 1 (Pk 1 j * (-2)), hD 2 (Pk 2 j * 8), hD 3 (Pk 3 j * (-10)),
      hD 4 (Pk 4 j * 4)]
    ring
  have hFB : deriv (FB j) z = (-1) ^ j * deriv (Sfun j) z := by
    rw [show FB j = fun t : ℝ => (-1) ^ j * Sfun j t from rfl]
    exact deriv_const_mul ((-1) ^ j) hdS
  rw [hFB, hS]
  rw [show (FB (j + 1)) z = (-1) ^ (j + 1) * Sfun (j + 1) z from rfl]
  simp only [Sfun]
  rw [Pk_succ 1 j, Pk_succ 2 j, Pk_succ 3 j, Pk_succ 4 j, pow_succ]
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  push_cast
  ring

/-- `∂_z^j H₂ = FB j` for `z > -1`. -/
theorem deriv_iter_H2b (j : ℕ) {z : ℝ} (hz : 0 < 1 + z) : deriv^[j] H2b z = FB j z := by
  induction j generalizing z with
  | zero =>
      show H2b z = FB 0 z
      rw [H2b]
      simp only [FB, Sfun, Pk, Finset.prod_range_zero]
      norm_num
      by_cases h : 1 + z = 0
      · rw [h]; simp
      · field_simp
        ring
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      have hev : (deriv^[j] H2b) =ᶠ[𝓝 z] (FB j) := by
        filter_upwards [isOpen_Ioi.mem_nhds (show (-1 : ℝ) < z by linarith)] with t ht
        have ht' : (0 : ℝ) < 1 + t := by
          have h := ht; rw [Set.mem_Ioi] at h; linarith
        exact ih ht'
      rw [hev.deriv_eq]
      exact deriv_FB j hz

/-! ## The bound `|∂_z^j H₂| ≤ 10^5·(1+z)^{-(j+1)}` -/

/-- `|P_k(j)| ≤ 8^j` for `k ≤ 4`, `j ≤ 4`. -/
theorem abs_Pk_le {k j : ℕ} (hk : k ≤ 4) (hj : j ≤ 4) : |Pk k j| ≤ (8 : ℝ) ^ j := by
  induction j with
  | zero => simp [Pk]
  | succ j ih =>
      have hj' : j ≤ 4 := by omega
      have h1 : |((k : ℝ) + j)| ≤ 8 := by
        have h2 : k + j ≤ 8 := by omega
        have h3 : (k : ℝ) + j ≤ 8 := by exact_mod_cast h2
        rw [abs_of_nonneg (by positivity)]
        exact h3
      have ih' : |Pk k j| ≤ (8 : ℝ) ^ j := ih hj'
      rw [Pk] at ih' ⊢
      rw [Finset.abs_prod] at ih' ⊢
      rw [Finset.prod_range_succ, pow_succ]
      exact mul_le_mul ih' h1 (abs_nonneg _) (by positivity)

/-- `|∂_z^j H₂(z)| ≤ 10^5·(1+z)^{-(j+1)}` for `j ≤ 4` and `z ≥ 0`. -/
theorem abs_deriv_iter_H2b_le {j : ℕ} (hj : j ≤ 4) {z : ℝ} (hz : 0 ≤ z) :
    |deriv^[j] H2b z| ≤ 10 ^ 6 * ((1 + z)⁻¹) ^ (j + 1) := by
  have hz1 : 0 < 1 + z := by linarith
  have hu0 : 0 ≤ (1 + z)⁻¹ := by positivity
  have hu1 : (1 + z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith : (1:ℝ) ≤ 1 + z)
  have h8 : ∀ k : ℕ, k ≤ 4 → |Pk k j| ≤ 10 ^ 4 := fun k hk =>
    le_trans (abs_Pk_le hk hj)
      (le_trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 8) hj) (by norm_num))
  have hpow : ∀ n : ℕ, 1 ≤ n → ((1 + z)⁻¹) ^ (j + n) ≤ ((1 + z)⁻¹) ^ (j + 1) := fun n hn =>
    pow_le_pow_of_le_one hu0 hu1 (by omega)
  have hp0 : (0:ℝ) ≤ ((1 + z)⁻¹) ^ (j + 1) := pow_nonneg hu0 _
  rw [deriv_iter_H2b j hz1, FB]
  simp only [Sfun]
  have e1 : |Pk 1 j * (-2) * ((1 + z)⁻¹) ^ (j + 1)| ≤ 2 * (10 ^ 4 * ((1 + z)⁻¹) ^ (j + 1)) := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg hp0]
    have h := h8 1 (by norm_num)
    nlinarith [h, hp0]
  have e2 : |Pk 2 j * 8 * ((1 + z)⁻¹) ^ (j + 2)| ≤ 8 * (10 ^ 4 * ((1 + z)⁻¹) ^ (j + 1)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 8),
      abs_of_nonneg (pow_nonneg hu0 (j + 2))]
    have h := h8 2 (by norm_num)
    have h2 := hpow 2 (by norm_num)
    nlinarith [h, h2, hp0, abs_nonneg (Pk 2 j), pow_nonneg hu0 (j + 2)]
  have e3 : |Pk 3 j * (-10) * ((1 + z)⁻¹) ^ (j + 3)| ≤ 10 * (10 ^ 4 * ((1 + z)⁻¹) ^ (j + 1)) := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 10),
      abs_of_nonneg (pow_nonneg hu0 (j + 3))]
    have h := h8 3 (by norm_num)
    have h2 := hpow 3 (by norm_num)
    nlinarith [h, h2, hp0, abs_nonneg (Pk 3 j), pow_nonneg hu0 (j + 3)]
  have e4 : |Pk 4 j * 4 * ((1 + z)⁻¹) ^ (j + 4)| ≤ 4 * (10 ^ 4 * ((1 + z)⁻¹) ^ (j + 1)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4),
      abs_of_nonneg (pow_nonneg hu0 (j + 4))]
    have h := h8 4 (by norm_num)
    have h2 := hpow 4 (by norm_num)
    nlinarith [h, h2, hp0, abs_nonneg (Pk 4 j), pow_nonneg hu0 (j + 4)]
  have e0 : |(-1 : ℝ) ^ j| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
  rw [abs_mul, e0, one_mul]
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add (abs_add_le _ _) (abs_add_le _ _)) ?_
  have hsum : (|Pk 1 j * (-2) * ((1 + z)⁻¹) ^ (j + 1)|
        + |Pk 2 j * 8 * ((1 + z)⁻¹) ^ (j + 2)|)
      + (|Pk 3 j * (-10) * ((1 + z)⁻¹) ^ (j + 3)|
        + |Pk 4 j * 4 * ((1 + z)⁻¹) ^ (j + 4)|)
      ≤ 24 * (10 ^ 4 * ((1 + z)⁻¹) ^ (j + 1)) := by
    have hnn : (0:ℝ) ≤ 10 ^ 4 * ((1 + z)⁻¹) ^ (j + 1) := mul_nonneg (by norm_num) hp0
    nlinarith [e1, e2, e3, e4]
  refine le_trans hsum ?_
  have hnn : (0:ℝ) ≤ 10 ^ 4 * ((1 + z)⁻¹) ^ (j + 1) := mul_nonneg (by norm_num) hp0
  nlinarith [hnn]

/-! ## The value of `∂_z H₂` -/

/-- `∂_z H₂(z) = 2z(2-5z+z²)/(1+z)⁵` for `z > -1`. -/
theorem H2b_deriv {z : ℝ} (hz : 0 < 1 + z) :
    deriv H2b z = 2 * z * (2 - 5 * z + z ^ 2) / (1 + z) ^ 5 := by
  have h := deriv_iter_H2b 1 hz
  rw [Function.iterate_one] at h
  rw [h]
  simp only [FB, Sfun, Pk, Finset.range_one, Finset.prod_singleton]
  norm_num
  field_simp
  ring

/-! ## The weighted bound -/

theorem H2b_weight_le : ∃ C : ℝ, 0 < C ∧ ∀ (m j : ℕ), m ≤ 4 → j ≤ m → ∀ z : ℝ, 0 < z →
    (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j)
      * |deriv^[j] H2b z| ≤ C := by
  refine ⟨10 ^ 7, by norm_num, ?_⟩
  intro m j hm hjm z hz
  have hz1 : 0 < 1 + z := by linarith
  have hWnn : 0 ≤ (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j) := by
    rw [Work.Spaces.w]; positivity
  rcases lt_or_ge m 2 with hm2 | hm2
  · interval_cases m
    · -- `m = 0`, hence `j = 0`
      have hj0 : j = 0 := by omega
      subst hj0
      simp only [pow_zero, Nat.sub_zero, div_one, mul_one, one_mul]
      rw [Function.iterate_zero, id_eq]
      have h2 := one_add_mul_w_mul_abs_H2b_le hz
      linarith
    · -- `m = 1`, so `j ∈ {0,1}`
      interval_cases j
      · -- `m = 1`, `j = 0`
        simp only [pow_one, Nat.sub_zero, div_one, Function.iterate_zero, id_eq]
        have h2 := one_add_mul_w_mul_abs_H2b_le hz
        have hzle : z / (1 + z) ≤ 1 := by rw [div_le_one hz1]; linarith
        have h3 : (1 + z) * Work.Spaces.w z * z / (1 + z) * |H2b z|
            = ((1 + z) * Work.Spaces.w z * |H2b z|) * (z / (1 + z)) := by
          field_simp
          try ring
        rw [h3]
        have h4 : 0 ≤ (1 + z) * Work.Spaces.w z * |H2b z| := by
          rw [Work.Spaces.w]; positivity
        calc ((1 + z) * Work.Spaces.w z * |H2b z|) * (z / (1 + z))
            ≤ ((1 + z) * Work.Spaces.w z * |H2b z|) * 1 :=
              mul_le_mul_of_nonneg_left hzle h4
          _ ≤ 10 ^ 7 := by linarith
      · -- `m = j = 1`
        rw [Function.iterate_one, show (1:ℕ) - 1 = 0 from rfl, pow_zero, div_one, pow_one]
        rw [H2b_deriv hz1, Work.Spaces.w]
        have hnum : |2 - 5 * z + z ^ 2| ≤ 5 * (1 + z) ^ 2 := by
          rw [abs_le]
          constructor <;> nlinarith [sq_nonneg z, hz.le, sq_nonneg (1 + z)]
        have hden : (0:ℝ) < (1 + z) ^ 5 := by positivity
        have hmain : (1 + z) * ((1 + z) ^ 2 / z ^ 2) * z
              * |2 * z * (2 - 5 * z + z ^ 2) / (1 + z) ^ 5|
            = 2 * |2 - 5 * z + z ^ 2| / (1 + z) ^ 2 := by
          rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
            abs_of_pos hz, abs_of_pos hden]
          field_simp
          try ring
        rw [hmain]
        rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 + z) ^ 2)]
        nlinarith [hnum, sq_nonneg (1 + z)]
  · -- `2 ≤ m`
    have hj4 : j ≤ 4 := by omega
    have hkey := abs_deriv_iter_H2b_le hj4 hz.le
    have hId : (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j)
        * ((1 + z)⁻¹) ^ (j + 1) = (z * (1 + z)⁻¹) ^ (m - 2) := by
      have hw : (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j)
          = (1 + z) ^ 3 * (z ^ m / z ^ 2) * ((1 + z)⁻¹) ^ (m - j) := by
        rw [Work.Spaces.w, div_eq_mul_inv, div_eq_mul_inv, ← inv_pow]
        ring
      rw [hw]
      have h1 : ((1 + z)⁻¹) ^ (m - j) * ((1 + z)⁻¹) ^ (j + 1) = ((1 + z)⁻¹) ^ (m + 1) := by
        rw [← pow_add]; congr 1; omega
      have h4 : z ^ m / z ^ 2 = z ^ (m - 2) := by
        rw [div_eq_mul_inv, ← inv_pow, show m = (m - 2) + 2 by omega, pow_add]
        rw [show z ^ (m - 2) * z ^ 2 * z⁻¹ ^ 2 = z ^ (m - 2) by
          rw [mul_assoc,
            show z ^ 2 * z⁻¹ ^ 2 = 1 by
              rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hz), one_pow],
            mul_one]]
        rw [show m - 2 + 2 - 2 = m - 2 by omega]
      have h2 : (1 + z) ^ 3 * ((1 + z)⁻¹) ^ (m + 1) = ((1 + z)⁻¹) ^ (m - 2) := by
        have h3 : (1 + z) ^ 3 * ((1 + z)⁻¹) ^ 3 = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hz1), one_pow]
        rw [show m + 1 = (m - 2) + 3 by omega, pow_add]
        rw [show (1 + z) ^ 3 * (((1 + z)⁻¹) ^ (m - 2) * (1 + z)⁻¹ ^ 3)
            = ((1 + z)⁻¹) ^ (m - 2) * ((1 + z) ^ 3 * (1 + z)⁻¹ ^ 3) by ring, h3, mul_one]
      rw [h4, mul_assoc, h1]
      rw [show (1 + z) ^ 3 * z ^ (m - 2) * (1 + z)⁻¹ ^ (m + 1)
          = z ^ (m - 2) * ((1 + z) ^ 3 * (1 + z)⁻¹ ^ (m + 1)) by ring, h2, mul_pow]
    have hbound : (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j)
        * |deriv^[j] H2b z|
        ≤ (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j)
          * (10 ^ 6 * ((1 + z)⁻¹) ^ (j + 1)) :=
      mul_le_mul_of_nonneg_left hkey hWnn
    refine le_trans hbound ?_
    have h5 : (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j)
          * (10 ^ 6 * ((1 + z)⁻¹) ^ (j + 1)) = 10 ^ 6 * (z * (1 + z)⁻¹) ^ (m - 2) := by
      rw [← hId]; ring
    rw [h5]
    have h6 : (z * (1 + z)⁻¹) ^ (m - 2) ≤ 1 := by
      refine pow_le_one₀ (by positivity) ?_
      rw [← div_eq_mul_inv, div_le_one hz1]
      linarith
    nlinarith [h6]

end Work.FTS.Nonlinear.Open.Row19Prep
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gam_deriv_low_left =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux


end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gam_deriv_low_right =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A lower bound for `|∂_θ Γ|` near `θ = π/2` (the right end of the angular interval)

With `Γ(θ) = (sin θ · cos²θ)^{α/3}` one has
`Γ = sin^{α/3}θ · cos^{2α/3}θ`, hence
`Γ'(θ) = (α/3) sin^{α/3-1}θ · cos^{2α/3-1}θ · (cos²θ - 2 sin²θ)`, and
`cos²θ - 2 sin²θ = -(3 sin²θ - 1) < 0` for `θ ≥ π/3`.

Therefore, for `0 < α ≤ 1` and `θ ∈ [π/3, π/2)`,
`|Γ'(θ)| = (α/3) · (3 sin²θ - 1) · sin^{α/3-1}θ · cos^{2α/3-1}θ`.

On this range `sin θ ∈ [√3/2, 1]`, so (the exponent `α/3 - 1` being `≤ 0`)
`sin^{α/3-1}θ ≥ 1`, while `3 sin²θ - 1 ≥ 5/4`.  Hence

`|Γ'(θ)| ≥ (5/12) · α · cos^{2α/3-1}θ`,

which is the statement below with `c = 5/12` (the `cos`-powers match *exactly*: the
exponent `2α/3 - 1` is precisely the one carried by both sides, which is what makes
the estimate uniform as `cos θ → 0`).
-/

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux


end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gwt_integrableOn_and_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular bookkeeping weight `Gwt` of row 15 is integrable, with `∫_θ Gwt ≤ 2000/α`

`Gwt α θ = Γ(θ)² · (5 sin(2θ)^{-η} + 30 sin(2θ)^{-γ})` with
`Γ(θ) = (sin θ cos²θ)^{α/3}`, `η = 99/100` and `γ = 1 + α/10`.  Both singular
factors are *not* integrable on their own (`sin(2θ)^{-γ}` blows up like `θ^{-1-α/10}`
at `θ = 0`), but the vanishing of `Γ(θ)² ~ θ^{2α/3}` supplies exactly the missing
power.

The route is the already proved `Gam_sq_mul_sin_rpow_le`, which turns `Γ(θ)² sin(2θ)^{-q}`
into the single `rpow` weight `sin(2θ)^{2α/5 - q}` as soon as `q ≥ 2α/5`:

* `q = η`: `Γ² sin^{-η} ≤ sin^{2α/5-η}`, exponent `> -η > -1`, integrable with a
  *constant* integral;
* `q = γ`: `Γ² sin^{-γ} ≤ sin^{2α/5-γ} = sin^{3α/10-1}`, integrable with integral
  `≲ 1/α`.

For the quantitative form we need the sharp constant `π` in the elementary estimate
`∫_θ sin(2θ)^p ≤ π/(p+1)` (`p ∈ (-1,0]`), not the lossy `100` of
`Work.Spaces.sin_two_rpow`: with it the total is
`5π/(2α/5+1/100) + 30π/(3α/10) ≤ 225π/(2α) ≤ 2000/α`.

Everything here is aimed at the row-15 bound `HkSq α 4 f ≤ 10¹² K² (Cs+1)² α⁴`
described in `row15_defs.lean`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false





end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.HkIntegrand_le_of_mixed_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

open scoped Real Topology
open MeasureTheory Set Filter
open Work.Spaces

/-- `(s^{q/2})² = s^q` for `s ≥ 0`. -/
private lemma rpow_half_sq {s q : ℝ} (hs : 0 ≤ s) : (s ^ (q / 2)) ^ 2 = s ^ q := by
  rw [← Real.rpow_natCast (s ^ (q / 2)) 2, ← Real.rpow_mul hs]
  ring

/-- `(s^{-q/2})² = s^{-q}` for `s ≥ 0`. -/
private lemma rpow_neg_half_sq {s q : ℝ} (hs : 0 ≤ s) : (s ^ (-(q / 2))) ^ 2 = s ^ (-q) := by
  rw [← Real.rpow_natCast (s ^ (-(q / 2))) 2, ← Real.rpow_mul hs]
  ring

/-- `(a / s^{q/2})² = a²·s^{-q}` for `s ≥ 0`. -/
private lemma sq_div_rpow_half {a s q : ℝ} (hs : 0 ≤ s) :
    (a / s ^ (q / 2)) ^ 2 = a ^ 2 * s ^ (-q) := by
  rw [div_pow, rpow_half_sq hs, div_eq_mul_inv, ← Real.rpow_neg hs]

/-- `(a·s^{-q/2})² = a²·s^{-q}` for `s ≥ 0`. -/
private lemma sq_mul_rpow_neg_half {a s q : ℝ} (hs : 0 ≤ s) :
    (a * s ^ (-(q / 2))) ^ 2 = a ^ 2 * s ^ (-q) := by
  rw [mul_pow, rpow_neg_half_sq hs]


end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.rlog_sq_integrableOn_and_integral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `z`-integral of the row-15 bookkeeping weight

`∫_0^∞ ((1 + log(1+z))/(1+z))² dz ≤ 100`.  The true value is `5` (substitute `u = 1+z`,
then `u = e^t`: `∫_0^∞ (1+t)²e^{-t} dt = 5`), but for the row-15 bookkeeping any explicit
constant suffices, and a majorant with an elementary `rpow` antiderivative is cheaper to
formalise: for `z ≥ 0`,

`((1 + log(1+z))/(1+z))² ≤ 25 (1+z)^{-3/2}`

(because `log u ≤ 4(u^{1/4} - 1)` for `u ≥ 1` by `Real.log_le_sub_one_of_pos` applied to
`u^{1/4}`), and `∫_0^∞ (1+z)^{-3/2} dz = 2` by the fundamental theorem of calculus, with
antiderivative `-2(1+z)^{-1/2}`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false








end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Lop_iter_mul_of_contDiffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The iterated Leibniz rule for `Lop` at finite smoothness order

`Work.Spaces.Lop` is the derivation `L u θ = sin(2θ) · u'(θ)` (the action of `D_θ` on a
`θ`-slice).  `Work.Spaces.Lop_iter_mul_eqOn` proves the binomial expansion of `L^[i] (u * v)`
on an open set on which `u` and `v` are **analytic** (`⊤ : WithTop ℕ∞` is the analytic order
in this Mathlib).  The statement proved here is the same binomial expansion under the much
weaker finite-order hypothesis `ContDiffOn ℝ (i + 1)`.

The only new ingredients are:

* `Lop_iter_contDiffOn_aux`: if `u` is `C^N` on an open set `V`, then `L^[k] u` is `C^m` there
  whenever `k + m ≤ N` (induction on `k`, using `ContDiffOn.deriv_of_isOpen` and the product
  rule for `ContDiffOn`).  This replaces the analyticity used in `Work.Spaces.Lop_iter_mul_eqOn`
  and supplies the differentiability of the summands in the induction step.
* `Lop_iter_mul_aux`: the induction on `i`, a verbatim adaptation of the proof of
  `Work.Spaces.Lop_iter_mul_eqOn` with the new smoothness source.
-/

open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

/-- Iterating the derivation `Lop` raises the smoothness order: if `u` is `C^N` on the open
set `V` then `Lop^[k] u` is `C^m` on `V` whenever `k + m ≤ N`. -/
lemma Lop_iter_contDiffOn_aux (u : ℝ → ℝ) (V : Set ℝ) (hV : IsOpen V) (N : ℕ) :
    ∀ k m : ℕ, k + m ≤ N → ContDiffOn ℝ (N : WithTop ℕ∞) u V →
      ContDiffOn ℝ (m : WithTop ℕ∞) (Work.Spaces.Lop^[k] u) V := by
  intro k
  induction k with
  | zero =>
      intro m hm hu
      simpa using hu.of_le (Nat.cast_le.mpr (by omega : m ≤ N))
  | succ k ih =>
      intro m hm hu
      have hk : k + (m + 1) ≤ N := by omega
      have hih := ih (m + 1) hk hu
      have hderiv : ContDiffOn ℝ (m : WithTop ℕ∞) (deriv (Work.Spaces.Lop^[k] u)) V :=
        hih.deriv_of_isOpen hV (le_of_eq rfl)
      have hsin : ContDiffOn ℝ (m : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ)) V := by
        fun_prop
      rw [Function.iterate_succ_apply']
      exact hsin.mul hderiv

/-- The iterated Leibniz rule for `Lop`, on an open set where `u` and `v` are only `C^(i+1)`. -/
theorem Lop_iter_mul_aux (i : ℕ) :
    ∀ (u v : ℝ → ℝ) (V : Set ℝ), IsOpen V →
      ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) u V →
      ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) v V →
      Set.EqOn (Work.Spaces.Lop^[i] (u * v))
        (fun θ => ∑ a ∈ Finset.range (i + 1),
          (i.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[i - a] v θ)) V := by
  induction i with
  | zero =>
      intro u v V hV hu hv θ hθ
      simp [Function.iterate_zero_apply]
  | succ i ih =>
      intro u v V hV hu hv θ hθ
      dsimp only
      rw [Function.iterate_succ_apply']
      have hu' : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) u V :=
        hu.of_le (Nat.cast_le.mpr (by omega : i + 1 ≤ i + 2))
      have hv' : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) v V :=
        hv.of_le (Nat.cast_le.mpr (by omega : i + 1 ≤ i + 2))
      have hih := ih u v V hV hu' hv'
      have hFa : ∀ a ≤ i, DifferentiableAt ℝ (Work.Spaces.Lop^[a] u) θ := fun a ha =>
        ((Lop_iter_contDiffOn_aux u V hV (i + 1) a 1 (by omega) hu').contDiffAt
          (hV.mem_nhds hθ)).differentiableAt (by norm_num)
      have hGb : ∀ b ≤ i, DifferentiableAt ℝ (Work.Spaces.Lop^[b] v) θ := fun b hb =>
        ((Lop_iter_contDiffOn_aux v V hV (i + 1) b 1 (by omega) hv').contDiffAt
          (hV.mem_nhds hθ)).differentiableAt (by norm_num)
      have hmem : ∀ a ∈ Finset.range (i + 1), DifferentiableAt ℝ
          (fun θ' => (i.choose a : ℝ)
            * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[i - a] v θ')) θ := by
        intro a ha
        exact (((hFa a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))).mul
          (hGb (i - a) (Nat.sub_le i a))).const_mul _
      have hfun : (fun θ' => ∑ a ∈ Finset.range (i + 1),
            (i.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[i - a] v θ'))
          = ∑ a ∈ Finset.range (i + 1),
            (fun θ' => (i.choose a : ℝ)
              * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[i - a] v θ')) := by
        funext θ'
        rw [Finset.sum_apply]
      have hderiv : deriv (Work.Spaces.Lop^[i] (u * v)) θ
          = deriv (fun θ' => ∑ a ∈ Finset.range (i + 1),
              (i.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[i - a] v θ')) θ :=
        (hih.deriv hV) hθ
      have hkey : Work.Spaces.Lop (Work.Spaces.Lop^[i] (u * v)) θ
          = ∑ a ∈ Finset.range (i + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (i.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[i - a] v θ')) θ := by
        show Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[i] (u * v)) θ
          = ∑ a ∈ Finset.range (i + 1), Real.sin (2 * θ)
              * deriv (fun θ' => (i.choose a : ℝ)
                * (Work.Spaces.Lop^[a] u θ' * Work.Spaces.Lop^[i - a] v θ')) θ
        rw [hderiv, hfun, deriv_sum hmem, Finset.mul_sum]
      rw [hkey]
      trans ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) *
          (Work.Spaces.Lop^[a + 1] u θ * Work.Spaces.Lop^[i - a] v θ
            + Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[i - a + 1] v θ)
      · exact Finset.sum_congr rfl (fun a ha => Work.Spaces.sin_deriv_term u v θ i a
          (hFa a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))) (hGb (i - a) (Nat.sub_le i a)))
      · exact Work.Spaces.leibniz_step i (fun b => Work.Spaces.Lop^[b] u θ)
          (fun b => Work.Spaces.Lop^[b] v θ)

theorem Lop_iter_mul_of_contDiffOn {i : ℕ} {u v : ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V)
    (hu : ContDiffOn ℝ (i + 1) u V) (hv : ContDiffOn ℝ (i + 1) v V) :
    ∀ θ ∈ V, Work.Spaces.Lop^[i] (u * v) θ
      = ∑ a ∈ Finset.range (i + 1),
          (i.choose a : ℝ) * (Work.Spaces.Lop^[a] u θ * Work.Spaces.Lop^[i - a] v θ) :=
  Lop_iter_mul_aux i u v V hV hu hv

end Work.FTS.Nonlinear.Pieces.RNP.row19
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.Fam2Diff.LopExpansion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux.Fam2Diff

theorem LopExpansion (i : ℕ) {g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hg : ContDiffOn ℝ (i + 1) g U) :
    ∀ θ ∈ U, (Work.Spaces.Lop^[i]) g θ
      = ∑ r ∈ Finset.range (i + 1),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv r g θ := by
  intro θ hθ
  -- view `g` as a function of two variables independent of the first
  have hsm : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞)
      (Function.uncurry (fun (_ : ℝ) (θ' : ℝ) => g θ')) (Set.univ ×ˢ U) := by
    change ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => g p.2) (Set.univ ×ˢ U)
    have hsnd : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) (Prod.snd : ℝ × ℝ → ℝ)
        (Set.univ ×ˢ U) :=
      (contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (n := (((i + 1 : ℕ)) : WithTop ℕ∞))).contDiffOn
    have hc := hg.comp hsnd (fun p hp => hp.2)
    simpa [Function.comp_def] using hc
  have hexp := Work.FTS.EllipticEst.remov.selfdth.DthIter_expansion_of_contDiffOn
    i (fun (_ : ℝ) (θ' : ℝ) => g θ') (Set.univ ×ˢ U)
    (isOpen_univ.prod hU) hsm 0 θ ⟨trivial, hθ⟩
  have hslice : (fun θ : ℝ => (fun (_ : ℝ) (θ' : ℝ) => g θ') 0 θ) = g := by
    funext θ'; rfl
  have hL : Work.Spaces.DthIter i (fun (_ : ℝ) (θ' : ℝ) => g θ') 0 θ
      = (Work.Spaces.Lop^[i]) g θ := by
    rw [Work.Spaces.DthIter_eq_iterate_Lop, hslice]
  rw [← hL, hexp]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hpt : Work.Spaces.pthIter r (fun (_ : ℝ) (θ' : ℝ) => g θ') 0 θ
      = iteratedDeriv r g θ := by
    rw [Work.FTS.EllipticEst.remov.selfdth.pthIter_eq_iteratedDeriv_slice, hslice]
  rw [hpt]

end Work.FTS.PhiStar.FlatWAux.Fam2Diff
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.RadGreenSupp.cmp1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.RadGreenSupp

/-- **The head regime `z ≤ a` of the weighted support bound.**

With `K = rgK α m`, `p = rgP α m`, the head estimate of `radGreen_supp_weight_le` compares the
growing-branch contribution `K·z^p·(M·a^{-p}/p)` — which is what `|radGreen|` reduces to for
`z ≤ a` when `c` is supported in `[a,b]` with `|c| ≤ M` — with the two-sided bound
`C α a b · M · z^{2/α}/(1+z)^{7/α}`.

Since `z ≤ a` we have `z^p·a^{-p} = (z/a)^p`, and `K/p = 1/(2m(4m+5)) ≤ 1/18` (`rgK_div_rgP_le`),
so the left side is at most `(M/18)·(z/a)^p`.  Because `p = 2m/α ≥ 2/α` and `z/a ≤ 1` this is at
most `(M/18)·(z/a)^{2/α} = (M/18)·z^{2/α}a^{-2/α}`, while the first summand of `C` alone
(`C_term1_le`) already gives `2·(M/2)·z^{2/α}a^{-2/α} = M·z^{2/α}a^{-2/α} ≥ (M/18)·z^{2/α}a^{-2/α}`,
using `(1+z)^{7/α} ≤ (1+a)^{7/α}` (from `z ≤ a`). -/
theorem cmp1 {α a b M z : ℝ} {m : ℕ} (hα : 0 < α) (ha : 0 < a) (hab : a ≤ b) (hM : 0 ≤ M)
    (hm : 1 ≤ m) (hz : 0 < z) (hza : z ≤ a) :
    Work.FTS.EllExist.rgK α m
        * (z ^ Work.FTS.EllExist.rgP α m
            * (M * a ^ (-(Work.FTS.EllExist.rgP α m)) / Work.FTS.EllExist.rgP α m))
      ≤ Work.FTS.PhiStar.Honesty.RadGreenSupp.C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
  have hza_pos : 0 < z / a := div_pos hz ha
  have hza1 : z / a ≤ 1 := (div_le_one ha).mpr hza
  have h2ap : 2 / α ≤ Work.FTS.EllExist.rgP α m := two_div_alpha_le_rgP hα hm
  have hKp : Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgP α m ≤ 1 / 18 :=
    rgK_div_rgP_le hα hm
  have hdiv : z ^ Work.FTS.EllExist.rgP α m * a ^ (-(Work.FTS.EllExist.rgP α m))
      = (z / a) ^ Work.FTS.EllExist.rgP α m := by
    rw [Real.div_rpow hz.le ha.le, Real.rpow_neg ha.le]
    ring
  have hL : Work.FTS.EllExist.rgK α m
        * (z ^ Work.FTS.EllExist.rgP α m
            * (M * a ^ (-(Work.FTS.EllExist.rgP α m)) / Work.FTS.EllExist.rgP α m))
      = M * (Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgP α m)
          * (z / a) ^ Work.FTS.EllExist.rgP α m := by
    rw [← hdiv]
    ring
  have hXleY : (z / a) ^ Work.FTS.EllExist.rgP α m ≤ (z / a) ^ (2 / α) :=
    Real.rpow_le_rpow_of_exponent_ge hza_pos hza1 h2ap
  have hQ : (z / a) ^ (2 / α) = z ^ (2 / α) * a ^ (-(2 / α)) := by
    rw [Real.div_rpow hz.le ha.le, Real.rpow_neg ha.le]
    ring
  have hden : 0 < (1 + z) ^ (7 / α) := Real.rpow_pos_of_pos (by linarith) _
  have hr1 : 1 ≤ (1 + a) ^ (7 / α) / (1 + z) ^ (7 / α) := by
    rw [one_le_div hden]
    exact Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
  have hCt1 : (1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α) ≤ C α a b :=
    C_term1_le hα ha hab
  have hD : 0 ≤ z ^ (2 / α) / (1 + z) ^ (7 / α) := by positivity
  have hCnonneg : 0 ≤ C α a b := le_of_lt (C_pos hα ha hab)
  have hfac2 : (1 / 2) * a ^ (-(2 / α)) * z ^ (2 / α)
      ≤ ((1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α)) * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
    have h0 : 0 ≤ (1 / 2) * a ^ (-(2 / α)) * z ^ (2 / α) := by
      have h1 : 0 ≤ a ^ (-(2 / α)) := Real.rpow_nonneg ha.le _
      have h2 : 0 ≤ z ^ (2 / α) := Real.rpow_nonneg hz.le _
      positivity
    calc (1 / 2) * a ^ (-(2 / α)) * z ^ (2 / α)
        = (1 / 2) * a ^ (-(2 / α)) * z ^ (2 / α) * 1 := by ring
      _ ≤ (1 / 2) * a ^ (-(2 / α)) * z ^ (2 / α) * ((1 + a) ^ (7 / α) / (1 + z) ^ (7 / α)) :=
            mul_le_mul_of_nonneg_left hr1 h0
      _ = ((1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α)) * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
            ring
  have hmid : M * (1 / 2) * (z / a) ^ (2 / α)
      ≤ C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
    have heq : M * (1 / 2) * (z / a) ^ (2 / α) = M * ((1 / 2) * a ^ (-(2 / α)) * z ^ (2 / α)) := by
      rw [hQ]; ring
    rw [heq]
    refine le_trans (mul_le_mul_of_nonneg_left hfac2 hM) ?_
    have hCM : ((1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α)) * M ≤ C α a b * M :=
      mul_le_mul hCt1 le_rfl hM hCnonneg
    have h := mul_le_mul_of_nonneg_right hCM hD
    have e1 : M * (((1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α))
          * (z ^ (2 / α) / (1 + z) ^ (7 / α)))
        = ((1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α)) * M
            * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by ring
    rw [e1]
    exact h
  calc Work.FTS.EllExist.rgK α m
        * (z ^ Work.FTS.EllExist.rgP α m
            * (M * a ^ (-(Work.FTS.EllExist.rgP α m)) / Work.FTS.EllExist.rgP α m))
      = M * (Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgP α m)
          * (z / a) ^ Work.FTS.EllExist.rgP α m := hL
    _ ≤ M * (1 / 18) * (z / a) ^ Work.FTS.EllExist.rgP α m := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKp hM)
          (Real.rpow_nonneg hza_pos.le _)
    _ ≤ M * (1 / 2) * (z / a) ^ (2 / α) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (by norm_num) hM) hXleY
          (Real.rpow_nonneg hza_pos.le _) (by positivity)
    _ ≤ C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := hmid

end Work.FTS.PhiStar.Honesty.RadGreenSupp
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.RadGreenSupp.cmp2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.RadGreenSupp

set_option autoImplicit false

open Work.FTS.EllExist

/-- The "middle regime" weight comparison: for `0 < a ≤ z ≤ b`,
`a ^ (2/α) / (1+b) ^ (7/α) ≤ z ^ (2/α) / (1+z) ^ (7/α)`. -/
theorem middle_weight_le {α a b z : ℝ} (hα : 0 < α) (ha : 0 < a) (haz : a ≤ z) (hzb : z ≤ b) :
    a ^ (2 / α) / (1 + b) ^ (7 / α) ≤ z ^ (2 / α) / (1 + z) ^ (7 / α) := by
  have hz : 0 < z := lt_of_lt_of_le ha haz
  have hα2 : (0 : ℝ) < 2 / α := by positivity
  have hα7 : (0 : ℝ) < 7 / α := by positivity
  have hnum : a ^ (2 / α) ≤ z ^ (2 / α) := Real.rpow_le_rpow ha.le haz hα2.le
  have hden : (1 + z) ^ (7 / α) ≤ (1 + b) ^ (7 / α) :=
    Real.rpow_le_rpow (by linarith) (by linarith) hα7.le
  have hzden : 0 < (1 + z) ^ (7 / α) := Real.rpow_pos_of_pos (by linarith) _
  have hbden : 0 < (1 + b) ^ (7 / α) := Real.rpow_pos_of_pos (by linarith) _
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul hnum
    (by simpa [one_div] using one_div_le_one_div_of_le hzden hden)
    (inv_nonneg.mpr hbden.le) (Real.rpow_pos_of_pos hz _).le

/-- The `C`-summand `(1/14)·a ^ (-2/α)·(1+b) ^ (7/α)` times the middle-regime weight comparison
is exactly `1/14`. -/
theorem C_term2_mul_middle {α a b : ℝ} (ha : 0 < a) (hb : 0 < 1 + b) :
    ((1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α)) * (a ^ (2 / α) / (1 + b) ^ (7 / α))
      = 1 / 14 := by
  have hbden : (1 + b) ^ (7 / α) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hb _)
  rw [show ((1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α)) * (a ^ (2 / α) / (1 + b) ^ (7 / α))
      = (1 / 14) * (a ^ (-(2 / α)) * a ^ (2 / α)) * ((1 + b) ^ (7 / α) / (1 + b) ^ (7 / α))
      from by ring,
    ← Real.rpow_add ha, show -(2 / α) + 2 / α = 0 from by ring, Real.rpow_zero,
    div_self hbden]
  ring

theorem cmp2 {α a b M z : ℝ} {m : ℕ} (hα : 0 < α) (ha : 0 < a) (hab : a ≤ b) (hM : 0 ≤ M)
    (hm : 1 ≤ m) (hz : 0 < z) (haz : a ≤ z) (hzb : z ≤ b) :
    Work.FTS.EllExist.rgK α m
        * (z ^ (-(Work.FTS.EllExist.rgQ α m))
              * (M * z ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m)
            + z ^ Work.FTS.EllExist.rgP α m
              * (M * z ^ (-(Work.FTS.EllExist.rgP α m)) / Work.FTS.EllExist.rgP α m))
      ≤ Work.FTS.PhiStar.Honesty.RadGreenSupp.C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  -- the two branches collapse to `M/q` and `M/p`
  have h1 : z ^ (-(rgQ α m)) * (M * z ^ (rgQ α m) / rgQ α m) = M / rgQ α m := by
    rw [show z ^ (-(rgQ α m)) * (M * z ^ (rgQ α m) / rgQ α m)
        = M * (z ^ (-(rgQ α m)) * z ^ (rgQ α m)) / rgQ α m from by ring,
      ← Real.rpow_add hz, show -(rgQ α m) + rgQ α m = 0 from by ring, Real.rpow_zero]
    ring
  have h2 : z ^ (rgP α m) * (M * z ^ (-(rgP α m)) / rgP α m) = M / rgP α m := by
    rw [show z ^ (rgP α m) * (M * z ^ (-(rgP α m)) / rgP α m)
        = M * (z ^ (rgP α m) * z ^ (-(rgP α m))) / rgP α m from by ring,
      ← Real.rpow_add hz, show rgP α m + -(rgP α m) = 0 from by ring, Real.rpow_zero]
    ring
  have hL : rgK α m * (z ^ (-(rgQ α m)) * (M * z ^ (rgQ α m) / rgQ α m)
        + z ^ (rgP α m) * (M * z ^ (-(rgP α m)) / rgP α m))
      = M * (rgK α m * (1 / rgQ α m + 1 / rgP α m)) := by
    rw [h1, h2]
    rw [show M / rgQ α m + M / rgP α m = M * (1 / rgQ α m + 1 / rgP α m) from by ring]
    ring
  -- the arithmetic constant of the two indicial exponents
  have hK : rgK α m * (1 / rgQ α m + 1 / rgP α m) ≤ 1 / 14 := rgK_mul_inv_add_le hα hm
  -- the weight on the right is bounded below by its value at `a`, `b`
  have hratio : a ^ (2 / α) / (1 + b) ^ (7 / α) ≤ z ^ (2 / α) / (1 + z) ^ (7 / α) :=
    middle_weight_le hα ha haz hzb
  have hratio1nn : 0 ≤ a ^ (2 / α) / (1 + b) ^ (7 / α) :=
    div_nonneg (Real.rpow_pos_of_pos ha _).le
      (Real.rpow_pos_of_pos (by linarith) _).le
  have hratio2nn : 0 ≤ z ^ (2 / α) / (1 + z) ^ (7 / α) :=
    div_nonneg (Real.rpow_pos_of_pos hz _).le
      (Real.rpow_pos_of_pos (by linarith) _).le
  have hc2 : (1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α) ≤ C α a b := C_term2_le hα ha hab
  have hCnn : 0 ≤ C α a b := (C_pos hα ha hab).le
  have hprod : ((1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α))
        * (M * (a ^ (2 / α) / (1 + b) ^ (7 / α)))
      ≤ C α a b * (M * (z ^ (2 / α) / (1 + z) ^ (7 / α))) :=
    mul_le_mul hc2 (mul_le_mul_of_nonneg_left hratio hM) (mul_nonneg hM hratio1nn) hCnn
  have hleft : ((1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α))
        * (M * (a ^ (2 / α) / (1 + b) ^ (7 / α))) = M / 14 := by
    rw [show ((1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α))
          * (M * (a ^ (2 / α) / (1 + b) ^ (7 / α)))
        = M * (((1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α))
          * (a ^ (2 / α) / (1 + b) ^ (7 / α))) from by ring,
      C_term2_mul_middle ha (by linarith : (0:ℝ) < 1 + b)]
    ring
  have hstep2 : M / 14 ≤ C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
    rw [hleft] at hprod
    rwa [← mul_assoc] at hprod
  rw [hL]
  linarith [mul_le_mul_of_nonneg_left hK hM, hstep2]

end Work.FTS.PhiStar.Honesty.RadGreenSupp
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.RadGreenSupp.cmp3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.RadGreenSupp

theorem cmp3 {α a b M z : ℝ} {m : ℕ} (hα : 0 < α) (ha : 0 < a) (hab : a ≤ b) (hM : 0 ≤ M)
    (hm : 1 ≤ m) (hz : 0 < z) (hbz : b ≤ z) :
    Work.FTS.EllExist.rgK α m
        * (z ^ (-(Work.FTS.EllExist.rgQ α m))
            * (M * b ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m))
      ≤ Work.FTS.PhiStar.Honesty.RadGreenSupp.C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
  -- The whole content is `rgK/q · M · (b/z)^q ≤ C·M·z^{2/α}/(1+z)^{7/α}` for `z ≥ b`: the
  -- factor `(b/z)^q` is dominated by the third summand of `C`, namely
  -- `(1/63)(1+b)^{7/α} b^{-2/α} · z^{2/α}/(1+z)^{7/α} ≥ (1/63)(b/z)^{7/α} ≥ (1/63)(b/z)^q`,
  -- using `z ≥ b` (so `b/z ≤ (1+b)/(1+z)`) and `q ≥ 7/α ≥ 0`.
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hq7 : 7 / α ≤ Work.FTS.EllExist.rgQ α m :=
    Work.FTS.PhiStar.Honesty.RadGreenSupp.seven_div_alpha_le_rgQ hα hm
  have hbz1 : 0 < 1 + z := by linarith
  have hb1 : 0 < 1 + b := by linarith
  have hbz0 : 0 ≤ b / z := div_nonneg hb.le hz.le
  have hbzpos : 0 < b / z := div_pos hb hz
  have hbzle1 : b / z ≤ 1 := (div_le_one hz).mpr hbz
  have hstep1 : Work.FTS.EllExist.rgK α m
        * (z ^ (-(Work.FTS.EllExist.rgQ α m))
            * (M * b ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m))
      = (Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgQ α m) * M
          * (b / z) ^ (Work.FTS.EllExist.rgQ α m) := by
    rw [Real.div_rpow hb.le hz.le, Real.rpow_neg hz.le]
    ring_nf
  have h2 : (b / z) ^ (Work.FTS.EllExist.rgQ α m) ≤ (b / z) ^ (7 / α) :=
    Real.rpow_le_rpow_of_exponent_ge hbzpos hbzle1 hq7
  have hKq : Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgQ α m ≤ 1 / 63 :=
    Work.FTS.PhiStar.Honesty.RadGreenSupp.rgK_div_rgQ_le hα hm
  have h3 : (Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgQ α m)
        * (M * (b / z) ^ (Work.FTS.EllExist.rgQ α m))
      ≤ (1 / 63) * (M * (b / z) ^ (7 / α)) :=
    mul_le_mul hKq (mul_le_mul_of_nonneg_left h2 hM)
      (mul_nonneg hM (Real.rpow_nonneg hbz0 _)) (by norm_num)
  have h4a : b / z ≤ (1 + b) / (1 + z) := by
    rw [div_le_div_iff₀ hz hbz1]; linarith
  have h4 : (b / z) ^ (7 / α) ≤ ((1 + b) / (1 + z)) ^ (7 / α) :=
    Real.rpow_le_rpow hbz0 h4a (by positivity)
  have h4' : (1 / 63) * (M * (b / z) ^ (7 / α))
      ≤ (1 / 63) * (M * ((1 + b) / (1 + z)) ^ (7 / α)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hM) (by norm_num)
  have h5a : (1 : ℝ) ≤ z / b := (one_le_div hb).mpr hbz
  have h5b : (1 : ℝ) ≤ (z / b) ^ (2 / α) := Real.one_le_rpow h5a (by positivity)
  have hXnn : 0 ≤ ((1 + b) / (1 + z)) ^ (7 / α) :=
    Real.rpow_nonneg (by positivity) _
  have h5 : (1 / 63) * (M * ((1 + b) / (1 + z)) ^ (7 / α))
      ≤ (1 / 63) * (M * ((z / b) ^ (2 / α) * ((1 + b) / (1 + z)) ^ (7 / α))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hXnn h5b) hM) (by norm_num)
  have h6eq : (1 / 63) * (M * ((z / b) ^ (2 / α) * ((1 + b) / (1 + z)) ^ (7 / α)))
      = (1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α)) * M
          * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
    rw [Real.div_rpow hz.le hb.le, Real.div_rpow hb1.le hbz1.le, Real.rpow_neg hb.le]
    ring
  have h6 : (1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α)) * M
        * (z ^ (2 / α) / (1 + z) ^ (7 / α))
      ≤ Work.FTS.PhiStar.Honesty.RadGreenSupp.C α a b * M
          * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
    have hnn : 0 ≤ M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) :=
      mul_nonneg hM (div_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hbz1.le _))
    have hc := Work.FTS.PhiStar.Honesty.RadGreenSupp.C_term3_le
      (α := α) (a := a) (b := b) hα ha hab
    calc (1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α)) * M
          * (z ^ (2 / α) / (1 + z) ^ (7 / α))
        = ((1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α)))
            * (M * (z ^ (2 / α) / (1 + z) ^ (7 / α))) := by ring
      _ ≤ Work.FTS.PhiStar.Honesty.RadGreenSupp.C α a b
            * (M * (z ^ (2 / α) / (1 + z) ^ (7 / α))) :=
          mul_le_mul_of_nonneg_right hc hnn
      _ = Work.FTS.PhiStar.Honesty.RadGreenSupp.C α a b * M
            * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by ring
  calc Work.FTS.EllExist.rgK α m
        * (z ^ (-(Work.FTS.EllExist.rgQ α m))
            * (M * b ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m))
      = (Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgQ α m) * M
          * (b / z) ^ (Work.FTS.EllExist.rgQ α m) := hstep1
    _ = (Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgQ α m)
          * (M * (b / z) ^ (Work.FTS.EllExist.rgQ α m)) := by ring
    _ ≤ (1 / 63) * (M * (b / z) ^ (7 / α)) := h3
    _ ≤ (1 / 63) * (M * ((1 + b) / (1 + z)) ^ (7 / α)) := h4'
    _ ≤ (1 / 63) * (M * ((z / b) ^ (2 / α) * ((1 + b) / (1 + z)) ^ (7 / α))) := h5
    _ = (1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α)) * M
          * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := h6eq
    _ ≤ Work.FTS.PhiStar.Honesty.RadGreenSupp.C α a b * M
          * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := h6

end Work.FTS.PhiStar.Honesty.RadGreenSupp
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.WeightedL2Aux.rgB_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.WeightedL2Aux

open MeasureTheory Set Filter

/-- **The `L²`-mass of `d` on the tail `(z,∞)` is controlled by the two-piece weight `M`.**

For `0 < z`, an a.e.-measurable `c` with `c²/t⁴ ∈ L¹(0,1)` and `c² ∈ L¹(1,∞)`: `c²` is
integrable on `(z,∞)` and `∫_{Ioi z} c² ≤ ∫_{Ioo 0 1} c²/t⁴ + ∫_{Ioi 1} c²`.

(The same statement is being proved independently as `WeightedL2Aux.sq_Ioi_le`.) -/
private lemma sq_Ioi_le_aux {c : ℝ → ℝ} {z : ℝ} (hz : 0 < z) (hc : AEMeasurable c)
    (hnear : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Ioo 0 1))
    (hfar : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioi 1)) :
    IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioi z) ∧
      (∫ t in Ioi z, (c t) ^ 2)
        ≤ (∫ t in Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4) + (∫ t in Ioi (1 : ℝ), (c t) ^ 2) := by
  have hA_nn : 0 ≤ ∫ t in Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4 :=
    integral_nonneg (fun t => by positivity)
  rcases le_or_gt 1 z with h1 | h1
  · -- `z ≥ 1`: the tail lies inside `(1,∞)`
    have hsub : Ioi z ⊆ Ioi (1 : ℝ) := Ioi_subset_Ioi h1
    have hInt : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioi z) := hfar.mono_set hsub
    refine ⟨hInt, ?_⟩
    have hmono : (∫ t in Ioi z, (c t) ^ 2) ≤ ∫ t in Ioi (1 : ℝ), (c t) ^ 2 :=
      setIntegral_mono_set hfar (Eventually.of_forall (fun t => sq_nonneg (c t)))
        (Eventually.of_forall (fun t ht => hsub ht))
    linarith
  · -- `0 < z < 1`: split `(z,∞) = (z,1] ∪ (1,∞)`
    have hz1 : z ≤ 1 := h1.le
    have hnear_z : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Ioo z 1) :=
      hnear.mono_set (fun t ht => ⟨lt_trans hz ht.1, ht.2⟩)
    -- on `(z,1]` one has `t⁴ ≤ 1`, hence `(c t)² ≤ (c t)²/t⁴`
    have hle_pt : ∀ t ∈ Ioo z 1, (c t) ^ 2 ≤ (c t) ^ 2 / t ^ 4 := by
      intro t ht
      have ht0 : 0 < t := lt_trans hz ht.1
      have ht1 : t ≤ 1 := ht.2.le
      have h4 : t ^ 4 ≤ 1 := pow_le_one₀ ht0.le ht1
      have h4pos : 0 < t ^ 4 := by positivity
      have hinv : 1 ≤ (t ^ 4)⁻¹ := (one_le_inv₀ h4pos).mpr h4
      rw [div_eq_mul_inv]
      simpa using mul_le_mul_of_nonneg_left hinv (sq_nonneg (c t))
    have hint_Ioo : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioo z 1) :=
      Integrable.mono' hnear_z ((hc.aestronglyMeasurable.restrict).pow 2) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hle_pt t ht)
    have hint_Ioc : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioc z 1) :=
      hint_Ioo.congr_set_ae (Ioo_ae_eq_Ioc (a := z) (b := 1)).symm
    have hInt : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioi z) := by
      have hU := hint_Ioc.union hfar
      rwa [Ioc_union_Ioi_eq_Ioi hz1] at hU
    refine ⟨hInt, ?_⟩
    have hsplit : (∫ t in Ioi z, (c t) ^ 2)
        = (∫ t in Ioc z 1, (c t) ^ 2) + ∫ t in Ioi (1 : ℝ), (c t) ^ 2 := by
      rw [← Ioc_union_Ioi_eq_Ioi hz1]
      exact setIntegral_union (Set.disjoint_left.mpr (fun x hx1 hx2 => not_lt_of_ge hx1.2 hx2))
        measurableSet_Ioi hint_Ioc hfar
    rw [hsplit]
    have hnear_val : (∫ t in Ioc z 1, (c t) ^ 2) ≤ ∫ t in Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4 := by
      rw [integral_Ioc_eq_integral_Ioo]
      calc (∫ t in Ioo z 1, (c t) ^ 2) ≤ ∫ t in Ioo z 1, (c t) ^ 2 / t ^ 4 :=
            setIntegral_mono_of_nonneg (fun t _ => sq_nonneg _) hle_pt hnear_z
        _ ≤ ∫ t in Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4 :=
            setIntegral_mono_set hnear (Eventually.of_forall (fun t => by positivity))
              (Eventually.of_forall (fun t ht => ⟨lt_trans hz ht.1, ht.2⟩))
    linarith

/-- **Cauchy–Schwarz tail bound for the growing-branch integrand** (general exponent
`p > 3/2`): the square of `∫_{Ioi z} c t·t^{-p-1}` is at most the `L²`-mass of `c` on `(z,∞)`
times `z^{-2p-1}/(2p+1)`. -/
theorem rgB_tail_sq_le {c : ℝ → ℝ} {p z : ℝ} (hp : 3 / 2 < p) (hz : 0 < z) (hc : AEMeasurable c)
    (hnear : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Ioo 0 1))
    (hfar : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioi 1)) :
    (∫ t in Ioi z, c t * t ^ (-p - 1)) ^ 2
      ≤ ((∫ t in Ioo (0:ℝ) 1, (c t) ^ 2 / t ^ 4) + (∫ t in Ioi (1:ℝ), (c t) ^ 2))
        * (z ^ (-(2 * p) - 1) / (2 * p + 1)) := by
  obtain ⟨hInt2, hle⟩ := sq_Ioi_le_aux (c := c) hz hc hnear hfar
  -- the second Cauchy–Schwarz factor: `t ↦ t^{-p-1}` is in `L²(z,∞)`
  have hpow : IntegrableOn (fun t : ℝ => (t ^ (-p - 1)) ^ 2) (Ioi z) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := -2 * p - 2) (by linarith) hz).congr_fun_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hz ht
    rw [pow_two, ← Real.rpow_add ht0]
    congr 1
    ring
  have hcs := sq_setIntegral_mul_le (s := Ioi z) measurableSet_Ioi hInt2 hpow
  -- its square integral: `∫_{Ioi z} t^{-2p-2} = z^{-2p-1}/(2p+1)`
  have hval : (∫ t in Ioi z, (t ^ (-p - 1)) ^ 2) = z ^ (-(2 * p) - 1) / (2 * p + 1) := by
    have hcong : (∫ t in Ioi z, (t ^ (-p - 1)) ^ 2) = ∫ t in Ioi z, t ^ (-(2 * p) - 2) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht0 : 0 < t := lt_trans hz ht
      rw [pow_two, ← Real.rpow_add ht0]
      congr 1
      ring
    rw [hcong, integral_Ioi_rpow_of_lt (a := -(2 * p) - 2) (by linarith) hz]
    rw [show -(2 * p) - 2 + 1 = -(2 * p) - 1 by ring]
    rw [show -(2 * p) - 1 = -(2 * p + 1) by ring, neg_div_neg_eq]
  have hbase : 0 ≤ z ^ (-(2 * p) - 1) / (2 * p + 1) :=
    div_nonneg (Real.rpow_nonneg hz.le _) (by linarith)
  calc (∫ t in Ioi z, c t * t ^ (-p - 1)) ^ 2
      ≤ (∫ t in Ioi z, (c t) ^ 2) * (∫ t in Ioi z, (t ^ (-p - 1)) ^ 2) := hcs
    _ = (∫ t in Ioi z, (c t) ^ 2) * (z ^ (-(2 * p) - 1) / (2 * p + 1)) := by rw [hval]
    _ ≤ ((∫ t in Ioo (0:ℝ) 1, (c t) ^ 2 / t ^ 4) + (∫ t in Ioi (1:ℝ), (c t) ^ 2))
          * (z ^ (-(2 * p) - 1) / (2 * p + 1)) := mul_le_mul_of_nonneg_right hle hbase

theorem rgB_sq_le {α : ℝ} {m : ℕ} {d : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hd : AEMeasurable d)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2) (Set.Ioi 1))
    {z : ℝ} (hz : 0 < z) :
    (Work.FTS.EllExist.rgB α m d z) ^ 2
      ≤ ((∫ t in Set.Ioo (0:ℝ) 1, (d t) ^ 2 / t ^ 4)
          + (∫ t in Set.Ioi (1:ℝ), (d t) ^ 2))
        * (z ^ (-(2 * Work.FTS.EllExist.rgP α m) - 1) / (2 * Work.FTS.EllExist.rgP α m + 1)) := by
  have hp32 : (3 : ℝ) / 2 < Work.FTS.EllExist.rgP α m := by
    have h := Work.FTS.EllExist.rgP_ge hα hα4 hm
    linarith
  have h := rgB_tail_sq_le (c := d) (p := Work.FTS.EllExist.rgP α m) (z := z)
    hp32 hz hd hnear hfar
  simpa only [Work.FTS.EllExist.rgB, Work.FTS.EllExist.rgF2] using h

end Work.FTS.PhiStar.Honesty.WeightedL2Aux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.exists_cont_approx_weightedL2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter

noncomputable section

/-! ## Elementary helper lemmas used by the main construction -/

/-- **A continuous cutoff.**  There is a continuous `χ : ℝ → ℝ` with values in `[0,1]` which
vanishes on `(-∞, δ] ∪ [N, ∞)` and equals `1` on `[2δ, N/2]` (the last condition being vacuous
if `2δ > N/2`). -/
theorem exists_continuous_cutoff {δ N : ℝ} (hδ : 0 < δ) (hN : 0 < N) :
    ∃ χ : ℝ → ℝ, Continuous χ ∧ (∀ t : ℝ, χ t ∈ Set.Icc 0 1) ∧
      (∀ t : ℝ, t ≤ δ → χ t = 0) ∧ (∀ t : ℝ, N ≤ t → χ t = 0) ∧
      (∀ t : ℝ, 2 * δ ≤ t → t ≤ N / 2 → χ t = 1) := by
  have hdisj : Disjoint (Set.Iic δ ∪ Set.Ici N) (Set.Icc (2 * δ) (N / 2)) := by
    rw [Set.disjoint_left]
    rintro t (ht | ht) ht'
    · simp only [Set.mem_Iic] at ht
      simp only [Set.mem_Icc] at ht'
      linarith [ht, ht'.1]
    · simp only [Set.mem_Ici] at ht
      simp only [Set.mem_Icc] at ht'
      have hN0 : (0:ℝ) < N := hN
      linarith [ht, ht'.2, hN0]
  obtain ⟨f, hf0, hf1, hfr⟩ :=
    exists_continuous_zero_one_of_isClosed (isClosed_Iic.union isClosed_Ici) isClosed_Icc hdisj
  exact ⟨fun t => f t, f.continuous, fun t => hfr t,
    fun t ht => hf0 (Or.inl ht), fun t ht => hf0 (Or.inr ht),
    fun t ht1 ht2 => hf1 ⟨ht1, ht2⟩⟩

/-- `(c t)^2` is integrable on any compact interval contained in `(0, ∞)`. -/
theorem integrableOn_sq_Icc_of {c : ℝ → ℝ} {α β : ℝ} (hα : 0 < α)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Icc α β) :=
  (sq_integrableOn_Ioi_of (by linarith : (0:ℝ) < α / 2) hnear hfar).mono_set
    (fun t ht => by simp only [Set.mem_Ioi]; linarith [ht.1])

/-- The cross term `u · c · w²` is integrable as soon as `u²w²` and `c²w²` are, provided
`u` and `c` are a.e.-measurable. -/
theorem integrableOn_cross_mul_w_sq {c u : ℝ → ℝ}
    (hu : AEMeasurable u) (hc : AEMeasurable c)
    (hcw : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (Set.Ioi 0))
    (huw : MeasureTheory.IntegrableOn (fun t : ℝ => (u t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => u t * c t * (Work.Spaces.w t) ^ 2)
      (Set.Ioi 0) := by
  have hw2 : Measurable (fun t : ℝ => (Work.Spaces.w t) ^ 2) := by
    unfold Work.Spaces.w; fun_prop
  refine Integrable.mono' (huw.add hcw) ?_ ?_
  · have h1 : AEMeasurable (fun t : ℝ => u t * c t * (Work.Spaces.w t) ^ 2) :=
      (hu.mul hc).mul hw2.aemeasurable
    exact (h1.mono_measure Measure.restrict_le_self).aestronglyMeasurable
  · filter_upwards with t
    have hw : (0:ℝ) ≤ (Work.Spaces.w t) ^ 2 := sq_nonneg _
    have habs : |u t * c t| ≤ (u t) ^ 2 + (c t) ^ 2 := by
      have h := sq_nonneg (|u t| - |c t|)
      rw [abs_mul]
      nlinarith [abs_nonneg (u t), abs_nonneg (c t), sq_abs (u t), sq_abs (c t)]
    show |u t * c t * (Work.Spaces.w t) ^ 2|
      ≤ (u t) ^ 2 * (Work.Spaces.w t) ^ 2 + (c t) ^ 2 * (Work.Spaces.w t) ^ 2
    calc |u t * c t * (Work.Spaces.w t) ^ 2| = |u t * c t| * (Work.Spaces.w t) ^ 2 := by
          rw [abs_mul, abs_of_nonneg hw]
      _ ≤ ((u t) ^ 2 + (c t) ^ 2) * (Work.Spaces.w t) ^ 2 :=
          mul_le_mul_of_nonneg_right habs hw
      _ = (u t) ^ 2 * (Work.Spaces.w t) ^ 2 + (c t) ^ 2 * (Work.Spaces.w t) ^ 2 := by ring

theorem exists_cont_approx_weightedL2 {c : ℝ → ℝ}
    (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∃ c_ : ℕ → ℝ → ℝ,
      (∀ n, ContinuousOn (c_ n) (Set.Ioi 0)) ∧
      (∀ n, ∃ a b : ℝ, 0 < a ∧ ∀ t : ℝ, t ∉ Set.Icc a b → c_ n t = 0) ∧
      (∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2 / t ^ 4)
        (Set.Ioo 0 1)) ∧
      (∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2) (Set.Ioi 1)) ∧
      Filter.Tendsto (fun n => ∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4)
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => ∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2)
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => ∫ t in Set.Ioi (0:ℝ), (c_ n t) ^ 2 * (Work.Spaces.w t) ^ 2)
        Filter.atTop (nhds (∫ t in Set.Ioi (0:ℝ), (c t) ^ 2 * (Work.Spaces.w t) ^ 2)) := by
  classical
  -- ## Step 1: for every `ε > 0` there is a compactly supported continuous `φ` with
  -- `∫_{(0,1)} (φ-c)²/t⁴ ≤ ε` and `∫_{(1,∞)} (φ-c)² ≤ ε`.
  have hmain : ∀ ε : ℝ, 0 < ε → ∃ φ : ℝ → ℝ,
      Continuous φ ∧ (∃ a b : ℝ, 0 < a ∧ ∀ t : ℝ, t ∉ Set.Icc a b → φ t = 0) ∧
      MeasureTheory.IntegrableOn (fun t : ℝ => (φ t - c t) ^ 2 / t ^ 4) (Set.Ioo 0 1) ∧
      MeasureTheory.IntegrableOn (fun t : ℝ => (φ t - c t) ^ 2) (Set.Ioi 1) ∧
      (∫ t in Set.Ioo (0:ℝ) 1, (φ t - c t) ^ 2 / t ^ 4) ≤ ε ∧
      (∫ t in Set.Ioi (1:ℝ), (φ t - c t) ^ 2) ≤ ε := by
    intro ε hε
    -- an error budget
    set T : ℝ := ε / 1000 with hTdef
    have hTpos : 0 < T := by rw [hTdef]; linarith
    -- (1) a small radius where the near weight has small mass
    obtain ⟨δ, hδpos, hδlt1, hδint⟩ := near_integral_abs_lt hnear hTpos
    set r : ℝ := δ / 2 with hrdef
    have hrpos : 0 < r := by rw [hrdef]; linarith
    have hr1 : 2 * r ≤ 1 := by rw [hrdef]; linarith
    have h2r : 2 * r = δ := by rw [hrdef]; ring
    have hη : ∫ t in Set.Ioo 0 (2 * r), (c t) ^ 2 / t ^ 4 ≤ T := by
      have h3 : ∫ t in Set.Ioo (0:ℝ) (2 * r), |(c t) ^ 2 / t ^ 4| < T := by
        rw [h2r]
        exact hδint
      have heq : ∫ t in Set.Ioo (0:ℝ) (2 * r), |(c t) ^ 2 / t ^ 4|
          = ∫ t in Set.Ioo (0:ℝ) (2 * r), (c t) ^ 2 / t ^ 4 :=
        setIntegral_congr_fun measurableSet_Ioo
          (fun t ht => abs_of_nonneg (div_nonneg (sq_nonneg _) (pow_pos ht.1 4).le))
      rw [← heq]
      exact le_of_lt h3
    -- (2) a large truncation radius
    have hev1 : ∀ᶠ n : ℕ in Filter.atTop, (∫ t in Set.Ioi (n : ℝ), (c t) ^ 2) < T :=
      (tail_integral_tendsto_zero hfar).eventually_lt tendsto_const_nhds hTpos
    have hev2 : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ n := eventually_ge_atTop 1
    obtain ⟨n, hnT, hn1⟩ := (hev1.and hev2).exists
    have hn1' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    set N : ℝ := 2 * (n : ℝ) with hNdef
    have hNpos : 0 < N := by rw [hNdef]; linarith
    have hN2 : 2 ≤ N := by rw [hNdef]; linarith
    have hNhalf : N / 2 = (n : ℝ) := by rw [hNdef]; ring
    have hη₃ : ∫ t in Set.Ioi (N / 2), (c t) ^ 2 ≤ T := by
      rw [hNhalf]; exact le_of_lt hnT
    -- (3) the approximation accuracy
    have hK1 : (1:ℝ) ≤ (r⁻¹) ^ 4 := by
      have h1 : r ≤ 1 / 2 := by linarith
      have h2 : (2:ℝ) ≤ r⁻¹ := by
        rw [le_inv_comm₀ (by norm_num : (0:ℝ) < 2) hrpos]
        rw [show (2:ℝ)⁻¹ = 1 / 2 by norm_num]
        linarith
      calc (1:ℝ) ≤ 2 ^ 4 := by norm_num
        _ ≤ (r⁻¹) ^ 4 := pow_le_pow_left₀ (by norm_num) h2 4
    set ε₁ : ℝ := T / (400 * (r⁻¹) ^ 4) with hε₁def
    have hε₁pos : 0 < ε₁ := by rw [hε₁def]; positivity
    have hε₁le : ε₁ ≤ T / 400 := by
      rw [hε₁def]
      exact div_le_div_of_nonneg_left hTpos.le (by norm_num) (by nlinarith [hK1])
    have hKne : (r⁻¹) ^ 4 ≠ 0 := by positivity
    -- (4) the compactly supported continuous approximation on `[r/2, 2N]`
    have hcIcc : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2)
        (Set.Icc (r / 2) (2 * N)) :=
      integrableOn_sq_Icc_of (by linarith) hnear hfar
    obtain ⟨G, hGcont, _hGbdd, hGint0, hGapp0⟩ :=
      approx_on_Icc_boundedContinuous (f := c) (a := r / 2) (b := 2 * N) hc hcIcc hε₁pos
    have hGint : MeasureTheory.IntegrableOn (fun t : ℝ => (G t - c t) ^ 2)
        (Set.Icc (r / 2) (2 * N)) :=
      hGint0.congr_fun (fun t _ => by ring) measurableSet_Icc
    have hGapp : ∫ t in Set.Icc (r / 2) (2 * N), (G t - c t) ^ 2 ≤ ε₁ := by
      rw [setIntegral_congr_fun measurableSet_Icc
        (fun t _ => by ring : ∀ t ∈ Set.Icc (r / 2) (2 * N),
          (G t - c t) ^ 2 = (c t - G t) ^ 2)]
      exact hGapp0
    -- (5) the cutoff
    obtain ⟨χ, hχcont, hχmem, hχ0, hχN, hχ1⟩ :=
      exists_continuous_cutoff (δ := r / 2) (N := N) (by linarith) hNpos
    have hχ1' : ∀ t : ℝ, r ≤ t → t ≤ N / 2 → χ t = 1 := by
      intro t ht1 ht2
      refine hχ1 t ?_ ht2
      rw [show 2 * (r / 2) = r by ring]
      exact ht1
    have hχb : ∀ t : ℝ, |χ t| ≤ 1 := by
      intro t
      have h := hχmem t
      rw [Set.mem_Icc] at h
      rw [abs_le]
      constructor <;> linarith [h.1, h.2]
    -- (6) the approximant and its properties
    have hφcont : Continuous (fun t : ℝ => χ t * G t) := hχcont.mul hGcont
    have hφsupp' : ∀ t : ℝ, t ∉ Set.Icc (r / 2) N → χ t * G t = 0 := by
      intro t ht
      have hcases : t < r / 2 ∨ N < t := by
        by_contra h
        rw [not_or] at h
        exact ht ⟨not_lt.mp h.1, not_lt.mp h.2⟩
      rcases hcases with h | h
      · rw [hχ0 t (le_of_lt h), zero_mul]
      · rw [hχN t (le_of_lt h), zero_mul]
    have hint1 : MeasureTheory.IntegrableOn
        (fun t : ℝ => (χ t * G t - c t) ^ 2 / t ^ 4) (Set.Ioo 0 1) :=
      integrableOn_sq_sub_div_Ioo (a := r / 2) (b := N) (by linarith) hc hφcont hφsupp' hnear
    have hint2 : MeasureTheory.IntegrableOn (fun t : ℝ => (χ t * G t - c t) ^ 2)
        (Set.Ioi 1) :=
      integrableOn_sq_sub_Ioi (a := r / 2) (b := N) hc hφcont hφsupp' hfar
    -- (7) the two estimates
    have hnb := near_bound (c := c) (G := G) (χ := χ) (r := r) (N := N) (ε₁ := ε₁) (η := T)
      hrpos hr1 hN2 hχ0 hχ1' hχb hnear hcIcc hη hGint hGapp hint1
    have hnearε : ∫ t in Set.Ioo (0:ℝ) 1, (χ t * G t - c t) ^ 2 / t ^ 4 ≤ ε := by
      refine le_trans hnb ?_
      have h65 : 65 * (r⁻¹) ^ 4 * ε₁ = 65 * T / 400 := by
        rw [hε₁def]
        field_simp
      rw [h65, hTdef]
      nlinarith
    have hfb := far_bound (c := c) (G := G) (χ := χ) (r := r) (N := N) (ε₁ := ε₁) (η := T)
      hrpos hr1 hN2 hχN hχ1' hχb hfar hη₃ hGint hGapp hint2
    have hfarε : ∫ t in Set.Ioi (1:ℝ), (χ t * G t - c t) ^ 2 ≤ ε := by
      refine le_trans hfb ?_
      have h5 : 5 * ε₁ ≤ 5 * (T / 400) := mul_le_mul_of_nonneg_left hε₁le (by norm_num)
      have h2 : (5:ℝ) * (T / 400) + 7 * T ≤ ε := by rw [hTdef]; linarith
      linarith
    exact ⟨fun t => χ t * G t, hφcont,
      ⟨r / 2, N, by linarith, hφsupp'⟩, hint1, hint2, hnearε, hfarε⟩
  -- ## Step 2: the sequence
  let c_ : ℕ → ℝ → ℝ :=
    fun n => Classical.choose (hmain (1 / ((n : ℝ) + 1)) (by positivity))
  have hspec : ∀ n : ℕ,
      Continuous (c_ n) ∧ (∃ a b : ℝ, 0 < a ∧ ∀ t : ℝ, t ∉ Set.Icc a b → c_ n t = 0) ∧
      MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2 / t ^ 4) (Set.Ioo 0 1) ∧
      MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2) (Set.Ioi 1) ∧
      (∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4) ≤ 1 / ((n : ℝ) + 1) ∧
      (∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2) ≤ 1 / ((n : ℝ) + 1) :=
    fun n => Classical.choose_spec (hmain (1 / ((n : ℝ) + 1)) (by positivity))
  have hlim1 : Filter.Tendsto
      (fun n : ℕ => ∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4)
      Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ?_ ?_
    · filter_upwards with n
      exact setIntegral_nonneg measurableSet_Ioo
        (fun t ht => div_nonneg (sq_nonneg _) (pow_pos ht.1 4).le)
    · filter_upwards with n
      exact (hspec n).2.2.2.2.1
  have hlim2 : Filter.Tendsto
      (fun n : ℕ => ∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2) Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ?_ ?_
    · filter_upwards with n
      exact setIntegral_nonneg measurableSet_Ioi (fun t _ => sq_nonneg _)
    · filter_upwards with n
      exact (hspec n).2.2.2.2.2
  refine ⟨c_, fun n => (hspec n).1.continuousOn, fun n => (hspec n).2.1,
    fun n => (hspec n).2.2.1, fun n => (hspec n).2.2.2.1, hlim1, hlim2, ?_⟩
  -- ## Step 3: the weighted `L²` norm converges
  have hcw : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (Set.Ioi 0) :=
    integrableOn_sq_mul_w_sq_of (u := c) hnear hfar
  have hintw : ∀ n : ℕ, MeasureTheory.IntegrableOn
      (fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi 0) :=
    fun n => integrableOn_sq_mul_w_sq_of (u := fun t : ℝ => c_ n t - c t)
      ((hspec n).2.2.1) ((hspec n).2.2.2.1)
  have hcross : ∀ n : ℕ, MeasureTheory.IntegrableOn
      (fun t : ℝ => (c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2) (Set.Ioi 0) :=
    fun n => integrableOn_cross_mul_w_sq (u := fun t : ℝ => c_ n t - c t)
      (((hspec n).1.aemeasurable).sub hc) hc hcw (hintw n)
  have hconv : Filter.Tendsto
      (fun n : ℕ => ∫ t in Set.Ioi (0:ℝ), (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      Filter.atTop (nhds 0) :=
    tendsto_sq_mul_w_sq_zero (fun n => (hspec n).2.2.1) (fun n => (hspec n).2.2.2.1)
      hlim1 hlim2
  exact tendsto_sq_weighted_of_tendsto_difference hcw hintw hcross hconv

end

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.lintegral_tail_swap_Ioi_one =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

/-- Tonelli/Fubini for the triangular region `1 < z < t` in `ℝ × ℝ`, in the form in which the
`PhiStar` tail estimates need it: the iterated `lintegral` over `(1,∞) × (z,∞)` equals the
iterated `lintegral` over the region `{(z,t) | 1 < z ∧ z < t}`, integrated first in `z`.
Both integrands are the product `P z * Q t`; the hypothesis `P z ≠ ⊤` (resp. `Q t ≠ ⊤`)
is what allows the (possibly non-measurable) factor to be pulled out of the inner integral. -/
theorem lintegral_tail_swap_Ioi_one {P Q : ℝ → ENNReal}
    (hP : AEMeasurable P (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))))
    (hQ : AEMeasurable Q (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))))
    (hPtop : ∀ z, P z ≠ ⊤) (hQtop : ∀ t, Q t ≠ ⊤) :
    ∫⁻ z in Set.Ioi (1 : ℝ), P z * (∫⁻ t in Set.Ioi z, Q t)
      = ∫⁻ t in Set.Ioi (1 : ℝ), Q t * (∫⁻ z in (Set.Ioi (1 : ℝ) ∩ Set.Iio t), P z) := by
  let f : ℝ → ℝ → ENNReal := fun z t => P z * (Set.Ioi z).indicator Q t
  -- `f` is a.e. measurable for the product of the restricted measures
  have hmeas : AEMeasurable (Function.uncurry f)
      ((MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))).prod
       (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))) := by
    have hfun : Function.uncurry f
        = fun p : ℝ × ℝ =>
            P p.1 * (Set.indicator {q : ℝ × ℝ | q.1 < q.2} (fun q => Q q.2)) p := by
      funext p
      by_cases h : p.1 < p.2 <;>
        simp [Function.uncurry, f, Set.indicator_of_mem, Set.indicator_of_notMem,
          Set.mem_Ioi, h]
    rw [hfun]
    exact (AEMeasurable.comp_fst hP).mul
      ((AEMeasurable.comp_snd hQ).indicator (measurableSet_lt measurable_fst measurable_snd))
  have hswap := lintegral_lintegral_swap (μ := MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))
    (ν := MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) (f := f) hmeas
  calc ∫⁻ z in Set.Ioi (1 : ℝ), P z * (∫⁻ t in Set.Ioi z, Q t)
      = ∫⁻ z in Set.Ioi (1 : ℝ),
          (∫⁻ t, f z t ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))) := by
        -- for `z ∈ (1,∞)`: pull `P z` out of the `t`-integral
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro z hz
        have hsub : Set.Ioi z ⊆ Set.Ioi (1 : ℝ) :=
          fun y hy => Set.mem_Ioi.mpr (lt_trans hz (Set.mem_Ioi.mp hy))
        calc P z * (∫⁻ t in Set.Ioi z, Q t)
            = P z * (∫⁻ t in Set.Ioi z, Q t
                ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))) := by
              rw [Measure.restrict_restrict_of_subset hsub]
          _ = P z * ∫⁻ t, (Set.Ioi z).indicator Q t
                ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
              rw [lintegral_indicator measurableSet_Ioi]
          _ = ∫⁻ t, P z * (Set.Ioi z).indicator Q t
                ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
              (lintegral_const_mul' (P z) (fun t => (Set.Ioi z).indicator Q t) (hPtop z)).symm
          _ = ∫⁻ t, f z t ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := rfl
    _ = ∫⁻ z, (∫⁻ t, f z t ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))))
            ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := rfl
    _ = ∫⁻ t, (∫⁻ z, f z t ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))))
            ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := hswap
    _ = ∫⁻ t in Set.Ioi (1 : ℝ),
          (∫⁻ z, f z t ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))) := rfl
    _ = ∫⁻ t in Set.Ioi (1 : ℝ), Q t * (∫⁻ z in (Set.Ioi (1 : ℝ) ∩ Set.Iio t), P z) := by
        -- for `t ∈ (1,∞)`: pull `Q t` out of the `z`-integral
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht
        calc ∫⁻ z, f z t ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))
            = ∫⁻ z in Set.Ioi (1 : ℝ), f z t ∂MeasureTheory.volume := rfl
          _ = ∫⁻ z in Set.Ioi (1 : ℝ), (Set.Iio t).indicator P z * Q t
                ∂MeasureTheory.volume := by
              apply setLIntegral_congr_fun measurableSet_Ioi
              intro z hz
              by_cases h : z < t <;>
                simp [f, Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_Ioi,
                  Set.mem_Iio, h]
          _ = (∫⁻ z in Set.Ioi (1 : ℝ), (Set.Iio t).indicator P z ∂MeasureTheory.volume) * Q t :=
              lintegral_mul_const' (Q t) (fun z => (Set.Iio t).indicator P z) (hQtop t)
          _ = (∫⁻ z in (Set.Iio t ∩ Set.Ioi (1 : ℝ)), P z ∂MeasureTheory.volume) * Q t := by
              rw [setLIntegral_indicator measurableSet_Iio P]
          _ = Q t * (∫⁻ z in (Set.Ioi (1 : ℝ) ∩ Set.Iio t), P z ∂MeasureTheory.volume) := by
              rw [Set.inter_comm (Set.Iio t) (Set.Ioi (1 : ℝ))]
              exact mul_comm _ _

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.lzero1_bdd_on_Ioo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open scoped Real Topology
open MeasureTheory Filter


end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.radGreen_branch_pointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Topology
open MeasureTheory Set Filter
open Work.FTS.EllExist (rgG1 rgG2 rgP rgQ rgQ_ge rgP_pos)

namespace Work.FTS.PhiStar.Honesty

/-!
# `z · (rgG1 z)² → 0` and `z · (rgG2 z)² → 0` at infinity

The two branches of the radial Green function are

  `rgG1 z = z^{-q}·∫_0^z c t·t^{q-1} dt`,   `rgG2 z = z^{p}·∫_z^∞ c t·t^{-p-1} dt`

with `q = rgQ α m = (2m+5)/α ≥ 28` and `p = rgP α m = 2m/α ≥ 8`.  Under the two `L²`-type
hypotheses on `c` (`c²/t⁴ ∈ L¹(0,1)`, `c² ∈ L¹(1,∞)`) both `z·(rgG1 z)²` and `z·(rgG2 z)²`
vanish at `∞`; we package this as the existence of dominating functions tending to `0`.

The estimate (junk-robust: the Bochner integral of a non-integrable function is `0`, so the
`¬Integrable` branches cause no trouble):

* `(∫_0^1 c t t^{q-1})² ≤ M0`,  `M0 = ∫_0^1 c²/t⁴`  (Cauchy–Schwarz, `t^{2q+2} ≤ 1`);
* `(∫_1^w c t t^{q-1})² ≤ P·w^{2q-1}`,  `P = ∫_{Ioi 1} c²`;
* `(∫_w^z c t t^{q-1})² ≤ T(w)·z^{2q-1}`,  `T(w) = ∫_{Ioi w} c²`;
* `(∫_{Ioi z} c t t^{-p-1})² ≤ T(z)·z^{-2p-1}/(2p+1)`.

Splitting `∫_0^z = ∫_0^1 + ∫_1^{√z} + ∫_{√z}^z` (the *tail* information is used only on the
last piece — the crude bound alone would leave a non-vanishing constant) gives

  `z·(rgG1 z)² ≤ 3·(M0·z^{1-2q} + P·z^{1/2-q} + T(√z))`,   `z·(rgG2 z)² ≤ T(z)/(2p+1)`,

and each of the four terms tends to `0` (the last two because `T(w) → 0` as `w → ∞`).
-/

/-! ### elementary real-power and square estimates -/


/-- `(z^a)² = z^{2a}` for `z > 0`. -/
private lemma rpow_sq {z : ℝ} (hz : 0 < z) (a : ℝ) : (z ^ a) ^ 2 = z ^ (2 * a) := by
  rw [sq, ← Real.rpow_add hz]
  congr 1
  ring






/-- `(a+b+c)² ≤ 3(a²+b²+c²)`. -/
private lemma sq_add_three_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]



/-! ### the three constants of the estimate -/








/-! ### the two halves of the pointwise bound -/



/-! ### the two limit computations -/



/-! ### the packaged statement -/


end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.radGreen_zderiv_honest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllExist

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ### the two primitive difference formulas -/





/-! ### the derivative identity -/


end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgA_integral_add_adjacent =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set
open scoped Real

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- AM–GM in the form `|y| ≤ y²/2 + 1/2`. -/
private lemma abs_le_half_sq_add_half (y : ℝ) : |y| ≤ y ^ 2 / 2 + 1 / 2 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1)]

/-- **`c² ∈ L¹(0,1)`.**  On `(0,1)` one has `t⁴ ≤ 1`, hence `(c t)² ≤ (c t)²/t⁴`, so the
near-field hypothesis dominates `c²` pointwise on `(0,1)`. -/
private lemma integrableOn_sq_near {c : ℝ → ℝ}
    (hc : AEMeasurable c)
    (hnear : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Ioo 0 1)) :
    IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioo 0 1) := by
  have hc2 : AEMeasurable (fun t : ℝ => (c t) ^ 2) volume := hc.pow_const 2
  refine Integrable.mono' hnear.norm
    (hc2.restrict (s := Ioo (0 : ℝ) 1)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have ht4pos : (0 : ℝ) < t ^ 4 := by positivity
  have ht4le : t ^ 4 ≤ 1 := pow_le_one₀ ht0.le ht1.le
  have hle : (c t) ^ 2 * t ^ 4 ≤ (c t) ^ 2 * 1 :=
    mul_le_mul_of_nonneg_left ht4le (sq_nonneg _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (c t)),
    abs_of_nonneg (div_nonneg (sq_nonneg (c t)) ht4pos.le)]
  rw [le_div_iff₀ ht4pos]
  simpa using hle

/-- **`rgF1` is interval integrable on `(0,1]`.**  The weight `t^{q-1}` is bounded by `1` on the
unit interval (`q ≥ 28`), so `rgF1` is dominated by `(c t)²/2 + 1/2`, whose two pieces are
integrable on `(0,1]` by `integrableOn_sq_near` and by the integrability of constants. -/
private lemma rgF1_integrableOn_Ioc_zero_one {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Ioo 0 1)) :
    IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Ioc (0 : ℝ) 1) := by
  have hq : (0 : ℝ) ≤ Work.FTS.EllExist.rgQ α m - 1 := by
    have h := Work.FTS.EllExist.rgQ_ge hα hα4 hm
    linarith
  have hpow_cont : Continuous (fun t : ℝ => t ^ (Work.FTS.EllExist.rgQ α m - 1)) :=
    Real.continuous_rpow_const hq
  have hF_aem : AEMeasurable
      (fun t : ℝ => c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)) volume :=
    hc.mul hpow_cont.aemeasurable
  -- `c² ∈ L¹(0,1]`
  have hcsq : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioc (0 : ℝ) 1) :=
    (integrableOn_sq_near hc hnear).congr_set_ae
      (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1)).symm
  -- constants are integrable on the bounded interval
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) 1) := by
    have h : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (0 : ℝ) 1 :=
      intervalIntegrable_const
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
  have hmaj : IntegrableOn (fun t : ℝ => (c t) ^ 2 / 2 + 1 / 2) (Ioc (0 : ℝ) 1) :=
    (hcsq.div_const 2).add (hconst.div_const 2)
  refine Integrable.mono' hmaj
    (hF_aem.restrict (s := Ioc (0 : ℝ) 1)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hpt : t ^ (Work.FTS.EllExist.rgQ α m - 1) ≤ 1 :=
    Real.rpow_le_one (le_of_lt ht0) ht1 hq
  rw [Work.FTS.EllExist.rgF1, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht0) _)]
  calc |c t| * t ^ (Work.FTS.EllExist.rgQ α m - 1)
      ≤ |c t| * 1 := mul_le_mul_of_nonneg_left hpt (abs_nonneg _)
    _ = |c t| := mul_one _
    _ ≤ (c t) ^ 2 / 2 + 1 / 2 := abs_le_half_sq_add_half _

/-- **`rgF1` is interval integrable on `(1,z]` for `z ≥ 1`.**  On `(1,z]` the weight `t^{q-1}` is
dominated by its value `z^{q-1}` at the right endpoint, so `rgF1` is dominated by
`z^{q-1}·((c t)²/2 + 1/2)`; `c²` is controlled by the far-field hypothesis and the constant is
integrable on the bounded interval. -/
private lemma rgF1_integrableOn_Ioc_one {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {z : ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hfar : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioi 1)) (hz : 1 ≤ z) :
    IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Ioc (1 : ℝ) z) := by
  have hq : (0 : ℝ) ≤ Work.FTS.EllExist.rgQ α m - 1 := by
    have h := Work.FTS.EllExist.rgQ_ge hα hα4 hm
    linarith
  have hpow_cont : Continuous (fun t : ℝ => t ^ (Work.FTS.EllExist.rgQ α m - 1)) :=
    Real.continuous_rpow_const hq
  have hF_aem : AEMeasurable
      (fun t : ℝ => c t * t ^ (Work.FTS.EllExist.rgQ α m - 1)) volume :=
    hc.mul hpow_cont.aemeasurable
  have hcsq : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioc (1 : ℝ) z) :=
    hfar.mono_set (Set.Ioc_subset_Ioi_self : Ioc (1 : ℝ) z ⊆ Ioi (1 : ℝ))
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (1 : ℝ) z) := by
    have h : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (1 : ℝ) z :=
      intervalIntegrable_const
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hz] at h
  have hmaj : IntegrableOn
      (fun t : ℝ => z ^ (Work.FTS.EllExist.rgQ α m - 1) * ((c t) ^ 2 / 2 + 1 / 2))
      (Ioc (1 : ℝ) z) :=
    ((hcsq.div_const 2).add (hconst.div_const 2)).const_mul _
  refine Integrable.mono' hmaj
    (hF_aem.restrict (s := Ioc (1 : ℝ) z)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  obtain ⟨ht1, htz⟩ := ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hz0 : (0 : ℝ) ≤ z := by linarith
  have hpt : t ^ (Work.FTS.EllExist.rgQ α m - 1) ≤ z ^ (Work.FTS.EllExist.rgQ α m - 1) :=
    Real.rpow_le_rpow ht0.le htz hq
  have hznn : (0 : ℝ) ≤ z ^ (Work.FTS.EllExist.rgQ α m - 1) := Real.rpow_nonneg hz0 _
  rw [Work.FTS.EllExist.rgF1, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
  calc |c t| * t ^ (Work.FTS.EllExist.rgQ α m - 1)
      ≤ |c t| * z ^ (Work.FTS.EllExist.rgQ α m - 1) :=
        mul_le_mul_of_nonneg_left hpt (abs_nonneg _)
    _ = z ^ (Work.FTS.EllExist.rgQ α m - 1) * |c t| := by ring
    _ ≤ z ^ (Work.FTS.EllExist.rgQ α m - 1) * ((c t) ^ 2 / 2 + 1 / 2) :=
        mul_le_mul_of_nonneg_left (abs_le_half_sq_add_half _) hznn

theorem rgA_integral_add_adjacent {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ z : ℝ, 1 ≤ z →
      Work.FTS.EllExist.rgA α m c z
        = (∫ t in (0 : ℝ)..1, Work.FTS.EllExist.rgF1 α m c t)
          + ∫ t in (1 : ℝ)..z, Work.FTS.EllExist.rgF1 α m c t := by
  intro z hz
  have h0 : IntervalIntegrable (Work.FTS.EllExist.rgF1 α m c) volume (0 : ℝ) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (rgF1_integrableOn_Ioc_zero_one hα hα4 hm hc hnear)
  have h1 : IntervalIntegrable (Work.FTS.EllExist.rgF1 α m c) volume (1 : ℝ) z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hz).mpr
      (rgF1_integrableOn_Ioc_one hα hα4 hm hc hfar hz)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0 h1
  show (∫ t in (0 : ℝ)..z, Work.FTS.EllExist.rgF1 α m c t)
      = (∫ t in (0 : ℝ)..1, Work.FTS.EllExist.rgF1 α m c t)
        + ∫ t in (1 : ℝ)..z, Work.FTS.EllExist.rgF1 α m c t
  exact hadd.symm

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgF1_integrableOn_Ioc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

theorem rgF1_integrableOn_Ioc {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ X : ℝ, 0 < X →
      MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Set.Ioc 0 X) := by
  intro X _
  obtain ⟨h0, h1, -⟩ := rgHonest_aemeas hα hα4 hm hc hnear hfar
  rcases le_or_gt X 1 with hX1 | hX1
  · -- `X ≤ 1`: `(0,X] ⊆ (0,1]`
    exact h0.mono_set (Set.Ioc_subset_Ioc_right hX1)
  · -- `1 < X`: `(0,X] = (0,1] ∪ (1,X]`
    have h2 : MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Set.Ioc 1 X) :=
      h1 X hX1.le
    have hun : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioc (1 : ℝ) X = Set.Ioc (0 : ℝ) X := by
      ext t
      simp only [Set.mem_union, Set.mem_Ioc]
      constructor
      · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
        · exact ⟨ha, le_trans hb hX1.le⟩
        · exact ⟨lt_trans zero_lt_one ha, hb⟩
      · intro ht
        by_cases hc1 : t ≤ 1
        · exact Or.inl ⟨ht.1, hc1⟩
        · exact Or.inr ⟨lt_of_not_ge hc1, ht.2⟩
    rw [← hun]
    exact h0.union h2

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgiA_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

noncomputable section
open MeasureTheory

namespace Work.FTS.PhiStar.Honesty

/-- If `f` is dominated by `M * t ^ (p - 1)` on `[0, y]` (`p > 0`, `y > 0`) then the interval
integral of `f` is bounded by `M * y ^ p / p`.

The hypothesis `0 ≤ M` is not needed separately: the domination hypothesis forces it (for
`t ≥ 0` large enough that `t ^ (p-1) > 0`). -/
theorem rgiA_interval_bound {f : ℝ → ℝ} {M p y : ℝ} (hM : 0 ≤ M) (hp : 0 < p)
    (hb : ∀ t : ℝ, 0 ≤ t → |f t| ≤ M * t ^ (p - 1)) (hy : 0 < y) :
    |∫ t in (0 : ℝ)..y, f t| ≤ M * y ^ p / p := by
  have hq : -1 < p - 1 := by linarith
  -- write the interval integral as an integral against `volume.restrict (Ioc 0 y)`
  have hEq : ∫ t in (0 : ℝ)..y, f t = ∫ t in Set.Ioc (0 : ℝ) y, f t :=
    intervalIntegral.integral_of_le hy.le
  rw [hEq]
  -- integrability of the majorant `M * t ^ (p - 1)` on `Ioc 0 y`
  have hInt1 : MeasureTheory.Integrable (fun t : ℝ => t ^ (p - 1))
      (volume.restrict (Set.Ioc (0 : ℝ) y)) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := y) hq).1
  have hInt2 : MeasureTheory.Integrable (fun t : ℝ => M * t ^ (p - 1))
      (volume.restrict (Set.Ioc (0 : ℝ) y)) := hInt1.const_mul M
  -- the monotone step, a.e. in `Ioc 0 y`
  have hmono : ∫ t in Set.Ioc (0 : ℝ) y, |f t| ≤ ∫ t in Set.Ioc (0 : ℝ) y, M * t ^ (p - 1) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => abs_nonneg _) hInt2 ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    exact hb t ht.1.le
  calc |∫ t in Set.Ioc (0 : ℝ) y, f t|
      ≤ ∫ t in Set.Ioc (0 : ℝ) y, |f t| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) y, M * t ^ (p - 1) := hmono
    _ = M * y ^ p / p := by
        rw [← intervalIntegral.integral_of_le hy.le, intervalIntegral.integral_const_mul]
        have hrpow : ∫ t in (0 : ℝ)..y, t ^ (p - 1) = y ^ p / p := by
          rw [integral_rpow (Or.inl hq)]
          rw [show (p - 1) + 1 = p from by ring, Real.zero_rpow (ne_of_gt hp)]
          simp
        rw [hrpow]
        ring

theorem rgiA_abs_le {α : ℝ} (hα : 0 < α) {m : ℕ} {c : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t : ℝ, |c t| ≤ M) :
    ∀ y : ℝ, 0 < y →
      |Work.FTS.PhiStar.Series.rgiA α m c y|
        ≤ M * y ^ ((2 * (m : ℝ) + 5) / α) / ((2 * (m : ℝ) + 5) / α) := by
  intro y hy
  have hp : 0 < (2 * (m : ℝ) + 5) / α := by
    apply div_pos _ hα
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hpt : ∀ t : ℝ, 0 ≤ t →
      |Work.FTS.PhiStar.Series.rgiF1 α m c t| ≤ M * t ^ ((2 * (m : ℝ) + 5) / α - 1) := by
    intro t ht
    rw [Work.FTS.PhiStar.Series.rgiF1, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht _)]
    exact mul_le_mul_of_nonneg_right (hb t) (Real.rpow_nonneg ht _)
  exact rgiA_interval_bound hM hp hpt hy

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgiB_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

/-
`rgiB α m c y = ∫_{Ioi y} c t · t^{-p-1}` with `p = 2m/α > 0`.  Since `|c t| ≤ M`, the absolute
value of the tail integral is at most `∫_{Ioi y} M t^{-p-1} = M·y^{-p}/p`.
-/
theorem rgiB_abs_le {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) {c : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t : ℝ, |c t| ≤ M) :
    ∀ y : ℝ, 0 < y →
      |Work.FTS.PhiStar.Series.rgiB α m c y|
        ≤ M * y ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α) := by
  intro y hy
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hb0 : 0 < 2 * (m : ℝ) / α := div_pos (by linarith) hα
  have hdef : Work.FTS.PhiStar.Series.rgiB α m c y
      = ∫ t in Set.Ioi y, c t * t ^ (-(2 * (m : ℝ) / α) - 1) := rfl
  -- the dominating function is integrable on `Ioi y` because its exponent is `< -1`
  have hg : MeasureTheory.Integrable (fun t : ℝ => M * t ^ (-(2 * (m : ℝ) / α) - 1))
      (MeasureTheory.volume.restrict (Set.Ioi y)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -(2 * (m : ℝ) / α) - 1) (by linarith) hy).const_mul M
  -- pointwise domination on `Ioi y`
  have hpt : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi y)),
      ‖c t * t ^ (-(2 * (m : ℝ) / α) - 1)‖
        ≤ M * t ^ (-(2 * (m : ℝ) / α) - 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hy ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    exact mul_le_mul_of_nonneg_right (hb t) (Real.rpow_nonneg ht0.le _)
  have hmain := MeasureTheory.norm_integral_le_of_norm_le hg hpt
  -- the value of the dominating integral
  have hInt : ∫ t in Set.Ioi y, M * t ^ (-(2 * (m : ℝ) / α) - 1)
      = M * y ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α) := by
    rw [MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt (a := -(2 * (m : ℝ) / α) - 1) (by linarith) hy]
    have hexp : -(2 * (m : ℝ) / α) - 1 + 1 = -(2 * (m : ℝ) / α) := by ring
    rw [hexp]
    rw [show -y ^ (-(2 * (m : ℝ) / α)) / (-(2 * (m : ℝ) / α))
        = y ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α) from by ring]
    ring
  rw [← hdef, Real.norm_eq_abs] at hmain
  rw [hInt] at hmain
  exact hmain

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgiB_abs_le_small =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

theorem rgiB_abs_le_small {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) {c : ℝ → ℝ} {M a b : ℝ}
    (hM : 0 ≤ M) (ha : 0 < a) (hb : ∀ t : ℝ, |c t| ≤ M)
    (hsupp : ∀ t : ℝ, c t ≠ 0 → t ∈ Set.Icc a b) :
    ∀ y : ℝ, 0 < y → y < a →
      |Work.FTS.PhiStar.Series.rgiB α m c y|
        ≤ M * a ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α) := by
  intro y hy hya
  -- the exponent `p = 2m/α` of the Green kernel is positive
  set p : ℝ := 2 * (m : ℝ) / α with hpdef
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp : 0 < p := by
    rw [hpdef]
    exact div_pos (by linarith) hα
  -- unfold `rgiB` into a set integral
  have hB : Work.FTS.PhiStar.Series.rgiB α m c y
      = ∫ t in Set.Ioi y, c t * t ^ (-p - 1) := by
    unfold Work.FTS.PhiStar.Series.rgiB Work.FTS.PhiStar.Series.rgiF2
    rw [← hpdef]
  rw [hB]
  -- step 1: bound the integral by the integral of the norm
  have h1 : |∫ t in Set.Ioi y, c t * t ^ (-p - 1)|
      ≤ ∫ t in Set.Ioi y, ‖c t * t ^ (-p - 1)‖ := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi y))
        (f := fun t : ℝ => c t * t ^ (-p - 1)))
  -- the majorant: `M t^{-p-1}` on the support `[a,b]` and `0` elsewhere
  set G : ℝ → ℝ := (Set.Icc a b).indicator (fun t => M * t ^ (-p - 1)) with hGdef
  have hpt : ∀ t ∈ Set.Ioi y, ‖c t * t ^ (-p - 1)‖ ≤ G t := by
    intro t ht
    have ht0 : 0 < t := lt_trans hy ht
    by_cases hmem : t ∈ Set.Icc a b
    · have hGt : G t = M * t ^ (-p - 1) := by
        rw [hGdef]; exact Set.indicator_of_mem hmem _
      rw [hGt, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
      exact mul_le_mul_of_nonneg_right (hb t) (Real.rpow_nonneg ht0.le _)
    · have hct : c t = 0 := by
        by_contra hne
        exact hmem (hsupp t hne)
      have hGt : G t = 0 := by
        rw [hGdef]; exact Set.indicator_of_notMem hmem _
      rw [hGt, hct, zero_mul, Real.norm_eq_abs, abs_zero]
  have ha2 : 0 < a / 2 := by linarith
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-p - 1)) (Set.Ioi (a / 2)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -p - 1 < -1) ha2
  have hbaseM : IntegrableOn (fun t : ℝ => M * t ^ (-p - 1)) (Set.Ioi (a / 2)) :=
    hbase.const_mul M
  have hIccsub : Set.Icc a b ∩ Set.Ioi y ⊆ Set.Ioi (a / 2) := by
    intro t ht
    have h1 : a ≤ t := ht.1.1
    exact lt_of_lt_of_le (by linarith) h1
  have hinter : IntegrableOn (fun t : ℝ => M * t ^ (-p - 1)) (Set.Icc a b ∩ Set.Ioi y) :=
    hbaseM.mono_set hIccsub
  have hintG : IntegrableOn G (Set.Ioi y) := by
    rw [hGdef]
    exact (MeasureTheory.integrableOn_indicator_iff measurableSet_Icc).mpr hinter
  -- step 2: monotonicity of the set integral
  have h2 : ∫ t in Set.Ioi y, ‖c t * t ^ (-p - 1)‖ ≤ ∫ t in Set.Ioi y, G t :=
    MeasureTheory.setIntegral_mono_of_nonneg (fun t _ => norm_nonneg _) hpt hintG
  -- step 3: evaluate the majorant
  have h3 : ∫ t in Set.Ioi y, G t ≤ M * a ^ (-p) / p := by
    rw [hGdef, MeasureTheory.setIntegral_indicator measurableSet_Icc]
    have hrow : IntegrableOn (fun t : ℝ => t ^ (-p - 1)) (Set.Ioi a) :=
      integrableOn_Ioi_rpow_of_lt (by linarith : -p - 1 < -1) ha
    have hci : IntegrableOn (fun t : ℝ => t ^ (-p - 1)) (Set.Ici a) :=
      (integrableOn_Ici_iff_integrableOn_Ioi).mpr hrow
    have hciM : IntegrableOn (fun t : ℝ => M * t ^ (-p - 1)) (Set.Ici a) := hci.const_mul M
    have hle : ∫ t in Set.Ioi y ∩ Set.Icc a b, M * t ^ (-p - 1)
        ≤ ∫ t in Set.Ici a, M * t ^ (-p - 1) :=
      MeasureTheory.setIntegral_mono_set hciM
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
          exact mul_nonneg hM (Real.rpow_nonneg (le_trans ha.le ht) _))
        (Filter.Eventually.of_forall (fun t ht => ht.2.1))
    have hval : ∫ t in Set.Ici a, M * t ^ (-p - 1) = M * a ^ (-p) / p := by
      rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
      rw [MeasureTheory.integral_const_mul]
      rw [integral_Ioi_rpow_of_lt (a := -p - 1) (by linarith : -p - 1 < -1) ha]
      rw [show (-p - 1) + 1 = -p from by ring]
      rw [neg_div_neg_eq]
      ring
    linarith [hle, hval]
  exact le_trans (le_trans h1 h2) h3

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.zDerivAux2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Real

namespace Work.FTS.PhiStar.Honesty

set_option maxHeartbeats 1600000

variable {α : ℝ} {m : ℕ} {c : ℝ → ℝ}

/-! ### the a.e. derivative identity for `z * deriv radGreen` -/

/-! ### the a.e. derivative identity for `z * deriv radGreen` -/


end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.LinvFlat.Lop_iter_sin_cos_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Boundedness of the iterates of `Lop` applied to `sin (2θ)` and `cos (2θ)`

`Work.Spaces.Lop u θ = sin (2θ) · u'(θ)` is the action of `D_θ = sin(2θ) ∂_θ` on functions of
`θ` alone.  The functions `θ ↦ sin (2θ)` and `θ ↦ cos (2θ)` are trigonometric polynomials, and
`Lop` multiplies by the trigonometric polynomial `sin (2θ)` and differentiates, so it maps the
`ℝ`-algebra of trigonometric polynomials in `sin (2θ), cos (2θ)` into itself.  Every
trigonometric polynomial is bounded on `ℝ` (indeed bounded in absolute value by the sum of the
absolute values of the coefficients), and only finitely many iterates `r ≤ l` occur, so a
common bound `M` exists.

The formalisation of "trigonometric polynomial" is the inductive closure

`TP := ℝ-span of {sin (2·), cos (2·)} closed under pointwise products`

(`LopTrig.TP` below), together with the three structural facts used in the induction: elements
of `TP` are differentiable everywhere (`LopTrig.TP_differentiable`), bounded
(`LopTrig.TP_bdd`), and `TP` is closed under `deriv` (`LopTrig.TP_deriv`), hence under `Lop`
(`LopTrig.TP_lop`).
-/

open scoped Real

namespace Work.FTS.PhiStar.LinvFlat

namespace LopTrig

/-- The `ℝ`-algebra of trigonometric polynomials in `sin (2θ)` and `cos (2θ)`: the smallest
class of functions `ℝ → ℝ` containing `sin (2·)` and `cos (2·)` and closed under addition,
pointwise multiplication and multiplication by real constants. -/
inductive TP : (ℝ → ℝ) → Prop
  | sin2 : TP (fun θ => Real.sin (2 * θ))
  | cos2 : TP (fun θ => Real.cos (2 * θ))
  | add {f g : ℝ → ℝ} : TP f → TP g → TP (f + g)
  | mul {f g : ℝ → ℝ} : TP f → TP g → TP (f * g)
  | smul (c : ℝ) {f : ℝ → ℝ} : TP f → TP (fun θ => c * f θ)

/-- Every trigonometric polynomial is differentiable everywhere. -/
lemma TP_differentiable : ∀ {f : ℝ → ℝ}, TP f → Differentiable ℝ f
  | _, .sin2 => by fun_prop
  | _, .cos2 => by fun_prop
  | _, .add hf hg => (TP_differentiable hf).add (TP_differentiable hg)
  | _, .mul hf hg => (TP_differentiable hf).mul (TP_differentiable hg)
  | _, .smul c hf => (differentiable_const c).mul (TP_differentiable hf)

/-- Every trigonometric polynomial is bounded in absolute value. -/
lemma TP_bdd : ∀ {f : ℝ → ℝ}, TP f → ∃ M : ℝ, 0 ≤ M ∧ ∀ θ : ℝ, |f θ| ≤ M
  | _, .sin2 => ⟨1, zero_le_one, fun θ => Real.abs_sin_le_one (2 * θ)⟩
  | _, .cos2 => ⟨1, zero_le_one, fun θ => Real.abs_cos_le_one (2 * θ)⟩
  | _, .add hf hg => by
      obtain ⟨M, hM0, hM⟩ := TP_bdd hf
      obtain ⟨N, hN0, hN⟩ := TP_bdd hg
      exact ⟨M + N, add_nonneg hM0 hN0, fun θ => by
        simp only [Pi.add_apply]
        exact le_trans (abs_add_le _ _) (add_le_add (hM θ) (hN θ))⟩
  | _, .mul hf hg => by
      obtain ⟨M, hM0, hM⟩ := TP_bdd hf
      obtain ⟨N, hN0, hN⟩ := TP_bdd hg
      exact ⟨M * N, mul_nonneg hM0 hN0, fun θ => by
        simp only [Pi.mul_apply, abs_mul]
        exact mul_le_mul (hM θ) (hN θ) (abs_nonneg _) hM0⟩
  | _, .smul c hf => by
      obtain ⟨M, hM0, hM⟩ := TP_bdd hf
      exact ⟨|c| * M, mul_nonneg (abs_nonneg c) hM0, fun θ => by
        simp only [abs_mul]
        exact mul_le_mul_of_nonneg_left (hM θ) (abs_nonneg c)⟩

lemma deriv_sin2 : deriv (fun θ : ℝ => Real.sin (2 * θ)) = fun θ => 2 * Real.cos (2 * θ) := by
  funext θ
  rw [deriv_sin (by fun_prop : DifferentiableAt ℝ (fun θ : ℝ => 2 * θ) θ)]
  rw [show deriv (fun θ : ℝ => 2 * θ) θ = 2 from (hasDerivAt_const_mul (2:ℝ) (x := θ)).deriv]
  ring

lemma deriv_cos2 : deriv (fun θ : ℝ => Real.cos (2 * θ)) = fun θ => -2 * Real.sin (2 * θ) := by
  funext θ
  rw [deriv_cos (by fun_prop : DifferentiableAt ℝ (fun θ : ℝ => 2 * θ) θ)]
  rw [show deriv (fun θ : ℝ => 2 * θ) θ = 2 from (hasDerivAt_const_mul (2:ℝ) (x := θ)).deriv]
  ring

lemma deriv_add_TP {f g : ℝ → ℝ} (hf : TP f) (hg : TP g) :
    deriv (f + g) = deriv f + deriv g := by
  funext θ
  rw [deriv_add ((TP_differentiable hf).differentiableAt) ((TP_differentiable hg).differentiableAt)]
  simp only [Pi.add_apply]

lemma deriv_mul_TP {f g : ℝ → ℝ} (hf : TP f) (hg : TP g) :
    deriv (f * g) = deriv f * g + f * deriv g := by
  funext θ
  rw [deriv_mul ((TP_differentiable hf).differentiableAt) ((TP_differentiable hg).differentiableAt)]
  simp only [Pi.add_apply, Pi.mul_apply]

lemma deriv_smul_TP (c : ℝ) {f : ℝ → ℝ} (hf : TP f) :
    deriv (fun θ : ℝ => c * f θ) = fun θ => c * deriv f θ := by
  funext θ
  rw [deriv_const_mul c ((TP_differentiable hf).differentiableAt)]

/-- The class of trigonometric polynomials is closed under differentiation. -/
lemma TP_deriv : ∀ {f : ℝ → ℝ}, TP f → TP (deriv f)
  | _, .sin2 => by
      rw [deriv_sin2]
      exact TP.smul 2 TP.cos2
  | _, .cos2 => by
      rw [deriv_cos2]
      exact TP.smul (-2) TP.sin2
  | _, .add hf hg => by
      rw [deriv_add_TP hf hg]
      exact TP.add (TP_deriv hf) (TP_deriv hg)
  | _, .mul hf hg => by
      rw [deriv_mul_TP hf hg]
      exact TP.add (TP.mul (TP_deriv hf) hg) (TP.mul hf (TP_deriv hg))
  | _, .smul c hf => by
      rw [deriv_smul_TP c hf]
      exact TP.smul c (TP_deriv hf)

/-- The class of trigonometric polynomials is closed under `Lop`. -/
lemma TP_lop {f : ℝ → ℝ} (hf : TP f) : TP (Work.Spaces.Lop f) := by
  change TP (fun θ => Real.sin (2 * θ) * deriv f θ)
  exact TP.mul TP.sin2 (TP_deriv hf)

end LopTrig


end Work.FTS.PhiStar.LinvFlat
end
-- ===== merged: Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadGreenSupport

set_option autoImplicit false

open Work.FTS.PhiStar.Series (rgiK rgiSn rgiSp rgiF1 rgiF2 rgiA rgiB rgiD1
  rgiA_hasDerivAt rgiB_hasDerivAt hasDerivAt_radGreenI radGreenI_eq_rgi)

/-- The second derivative of the radial Green's function `radGreenI α m c`, in explicit form:
the derivative of `rgiD1` (which is the derivative of `radGreenI`). -/
private def rgD2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (y : ℝ) : ℝ :=
  rgiK α m * (((rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y
            + (rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y)
          + ((rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y
            + (rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y))))

/-- **The derivative `rgiD1` of `radGreenI` is differentiable on `(0,∞)`**, with the explicit
derivative `rgD2`; uses only the interval-integral FTC (`h0`) and the tail-integral FTC (`hinf`). -/
private lemma rgD1_hasDerivAt {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (rgiD1 α m c) (rgD2 α m c z) z := by
  intro z hz
  have hzne : z ≠ 0 := ne_of_gt hz
  have hA := rgiA_hasDerivAt (α := α) (m := m) (c := c) hc h0 z hz
  have hB := rgiB_hasDerivAt (α := α) (m := m) (c := c) hc hinf z hz
  have hp1 : HasDerivAt (fun t : ℝ => rgiSn α m * t ^ (rgiSn α m - 1))
      (rgiSn α m * ((rgiSn α m - 1) * z ^ (rgiSn α m - 2))) z := by
    have h := (Real.hasDerivAt_rpow_const (x := z) (p := rgiSn α m - 1)
      (Or.inl hzne)).const_mul (rgiSn α m)
    rwa [show (rgiSn α m - 1) - 1 = rgiSn α m - 2 from by ring] at h
  have hp2 : HasDerivAt (fun t : ℝ => rgiSp α m * t ^ (rgiSp α m - 1))
      (rgiSp α m * ((rgiSp α m - 1) * z ^ (rgiSp α m - 2))) z := by
    have h := (Real.hasDerivAt_rpow_const (x := z) (p := rgiSp α m - 1)
      (Or.inl hzne)).const_mul (rgiSp α m)
    rwa [show (rgiSp α m - 1) - 1 = rgiSp α m - 2 from by ring] at h
  exact ((hp1.mul hA).add (hp2.mul hB)).const_mul (rgiK α m)

theorem radGreen_ode_weak {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ∀ z, 0 < z →
      -α ^ 2 * z ^ 2 * deriv (deriv (Work.FTS.PhiStar.Radial.radGreen α m c)) z
        - α * (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
        + Work.FTS.PhiStar.Radial.lamR m * Work.FTS.PhiStar.Radial.radGreen α m c z = c z := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hG : Work.FTS.PhiStar.Radial.radGreen α m c = Work.FTS.PhiStar.Radial.radGreenI α m c := rfl
  intro z hz
  rw [hG]
  -- First and second derivative of `radGreenI`.
  have hd1 : HasDerivAt (Work.FTS.PhiStar.Radial.radGreenI α m c) (rgiD1 α m c z) z :=
    hasDerivAt_radGreenI (α := α) (m := m) (c := c) hc h0 hinf z hz
  have heq : deriv (Work.FTS.PhiStar.Radial.radGreenI α m c) =ᶠ[𝓝 z] rgiD1 α m c :=
    eventually_of_mem (Ioi_mem_nhds hz)
      (fun y hy => (hasDerivAt_radGreenI (α := α) (m := m) (c := c) hc h0 hinf y hy).deriv)
  have hdd : deriv (deriv (Work.FTS.PhiStar.Radial.radGreenI α m c)) z = rgD2 α m c z := by
    rw [heq.deriv_eq, (rgD1_hasDerivAt (α := α) (m := m) (c := c) hc h0 hinf z hz).deriv]
  have hd1z : deriv (Work.FTS.PhiStar.Radial.radGreenI α m c) z = rgiD1 α m c z := hd1.deriv
  have hgz : Work.FTS.PhiStar.Radial.radGreenI α m c z
      = rgiK α m * (z ^ (rgiSn α m) * rgiA α m c z + z ^ (rgiSp α m) * rgiB α m c z) :=
    congrFun (radGreenI_eq_rgi α m c) z
  rw [hdd, hd1z, hgz]
  -- The `rpow` clearing identities.
  have hzs1 : z * z ^ (rgiSn α m - 1) = z ^ (rgiSn α m) := by
    nth_rewrite 1 [← Real.rpow_one z]
    rw [← Real.rpow_add hz]
    congr 1
    ring
  have hzs2 : z ^ 2 * z ^ (rgiSn α m - 2) = z ^ (rgiSn α m) := by
    rw [← Real.rpow_two z, ← Real.rpow_add hz]
    congr 1
    ring
  have hzp1 : z * z ^ (rgiSp α m - 1) = z ^ (rgiSp α m) := by
    nth_rewrite 1 [← Real.rpow_one z]
    rw [← Real.rpow_add hz]
    congr 1
    ring
  have hzp2 : z ^ 2 * z ^ (rgiSp α m - 2) = z ^ (rgiSp α m) := by
    rw [← Real.rpow_two z, ← Real.rpow_add hz]
    congr 1
    ring
  have hc1 : z ^ 2 * z ^ (rgiSn α m - 1) * rgiF1 α m c z = c z := by
    have he : (2 * (m : ℝ) + 5) / α - 1 = -1 - (-(2 * (m : ℝ) + 5) / α) := by ring
    have hf : rgiF1 α m c z = c z * z ^ (-1 - rgiSn α m) := by
      simp only [rgiF1, rgiSn]; rw [he]
    have h2 : z ^ 2 * z ^ (rgiSn α m - 1) = z ^ (rgiSn α m + 1) := by
      rw [← Real.rpow_two z, ← Real.rpow_add hz]; congr 1; ring
    have hE : (rgiSn α m + 1) + (-1 - rgiSn α m) = 0 := by ring
    have hcomb : z ^ 2 * z ^ (rgiSn α m - 1) * z ^ (-1 - rgiSn α m) = 1 := by
      rw [h2, ← Real.rpow_add hz, hE, Real.rpow_zero]
    calc z ^ 2 * z ^ (rgiSn α m - 1) * rgiF1 α m c z
        = z ^ 2 * z ^ (rgiSn α m - 1) * (c z * z ^ (-1 - rgiSn α m)) := by rw [hf]
      _ = c z * (z ^ 2 * z ^ (rgiSn α m - 1) * z ^ (-1 - rgiSn α m)) := by ring
      _ = c z * 1 := by rw [hcomb]
      _ = c z := by ring
  have hc2 : z ^ 2 * z ^ (rgiSp α m - 1) * rgiF2 α m c z = c z := by
    have he : -(2 * (m : ℝ) / α) - 1 = -1 - (2 * (m : ℝ) / α) := by ring
    have hf : rgiF2 α m c z = c z * z ^ (-1 - rgiSp α m) := by
      simp only [rgiF2, rgiSp]; rw [he]
    have h2 : z ^ 2 * z ^ (rgiSp α m - 1) = z ^ (rgiSp α m + 1) := by
      rw [← Real.rpow_two z, ← Real.rpow_add hz]; congr 1; ring
    have hE : (rgiSp α m + 1) + (-1 - rgiSp α m) = 0 := by ring
    have hcomb : z ^ 2 * z ^ (rgiSp α m - 1) * z ^ (-1 - rgiSp α m) = 1 := by
      rw [h2, ← Real.rpow_add hz, hE, Real.rpow_zero]
    calc z ^ 2 * z ^ (rgiSp α m - 1) * rgiF2 α m c z
        = z ^ 2 * z ^ (rgiSp α m - 1) * (c z * z ^ (-1 - rgiSp α m)) := by rw [hf]
      _ = c z * (z ^ 2 * z ^ (rgiSp α m - 1) * z ^ (-1 - rgiSp α m)) := by ring
      _ = c z * 1 := by rw [hcomb]
      _ = c z := by ring
  have hzA1 : z * rgiD1 α m c z = rgiK α m * (rgiSn α m * (z ^ (rgiSn α m) * rgiA α m c z)
      + rgiSp α m * (z ^ (rgiSp α m) * rgiB α m c z)) := by
    simp only [rgiD1]
    linear_combination (rgiK α m * rgiSn α m * rgiA α m c z) * hzs1
      + (rgiK α m * rgiSp α m * rgiB α m c z) * hzp1
  have hzA2 : z ^ 2 * rgD2 α m c z
      = rgiK α m * (rgiSn α m * (rgiSn α m - 1) * (z ^ (rgiSn α m) * rgiA α m c z)
        + rgiSp α m * (rgiSp α m - 1) * (z ^ (rgiSp α m) * rgiB α m c z)
        + (rgiSn α m - rgiSp α m) * c z) := by
    simp only [rgD2]
    linear_combination (rgiK α m * rgiSn α m * (rgiSn α m - 1) * rgiA α m c z) * hzs2
      + (rgiK α m * rgiSp α m * (rgiSp α m - 1) * rgiB α m c z) * hzp2
      + (rgiK α m * rgiSn α m) * hc1 - (rgiK α m * rgiSp α m) * hc2
  have hind1 : -α ^ 2 * rgiSn α m * (rgiSn α m - 1) - α * (5 + α) * rgiSn α m
      + Work.FTS.PhiStar.Radial.lamR m = 0 := by
    simp only [rgiSn, Work.FTS.PhiStar.Radial.lamR]
    field_simp
    ring
  have hind2 : -α ^ 2 * rgiSp α m * (rgiSp α m - 1) - α * (5 + α) * rgiSp α m
      + Work.FTS.PhiStar.Radial.lamR m = 0 := by
    simp only [rgiSp, Work.FTS.PhiStar.Radial.lamR]
    field_simp
    ring
  have hK : α ^ 2 * rgiK α m * (rgiSp α m - rgiSn α m) = 1 := by
    simp only [rgiK, rgiSp, rgiSn]
    field_simp
    ring
  linear_combination (-(α ^ 2)) * hzA2 - (α * (5 + α)) * hzA1
    + (rgiK α m * (z ^ (rgiSn α m) * rgiA α m c z)) * hind1
    + (rgiK α m * (z ^ (rgiSp α m) * rgiB α m c z)) * hind2 + (c z) * hK

end Work.FTS.PhiStar.RadGreenSupport
end
end

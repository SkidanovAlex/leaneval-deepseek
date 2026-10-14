import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.LWP.VorticityAPI
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.integral_ball_sub_norm_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set

/-- Translation of the radial power integral to an arbitrary centre: for `s > -3` and `r > 0`,
`∫_{B(x,r)} ‖a - x‖^s da = 4π r^{s+3}/(s+3)`.  This is the centred version
`radial_rpow_integral` together with translation invariance of Lebesgue measure. -/
theorem integral_ball_sub_norm_rpow (x : Work.LWP.R3) (r s : ℝ) (hs : -3 < s) (hr : 0 < r) :
    ∫ a in Metric.ball x r, (‖a - x‖ : ℝ) ^ s = 4 * Real.pi * r ^ (s + 3) / (s + 3) := by
  have hshift : ∫ a in Metric.ball x r, (‖a - x‖ : ℝ) ^ s
      = ∫ z in Metric.ball (0 : Work.LWP.R3) r, (‖z‖ : ℝ) ^ s := by
    calc ∫ a in Metric.ball x r, (‖a - x‖ : ℝ) ^ s
        = ∫ a, (Metric.ball x r).indicator (fun a => (‖a - x‖ : ℝ) ^ s) a :=
          (integral_indicator measurableSet_ball).symm
      _ = ∫ z, (Metric.ball x r).indicator (fun a => (‖a - x‖ : ℝ) ^ s) (z + x) :=
          (integral_add_right_eq_self
            (fun a => (Metric.ball x r).indicator (fun a => (‖a - x‖ : ℝ) ^ s) a) x).symm
      _ = ∫ z, (Metric.ball (0 : Work.LWP.R3) r).indicator (fun a => (‖a‖ : ℝ) ^ s) z := by
          apply integral_congr_ae
          filter_upwards with z
          by_cases hz : z ∈ Metric.ball (0 : Work.LWP.R3) r
          · have hz' : ‖z‖ < r := by rwa [Metric.mem_ball, dist_zero_right] at hz
            have hzx : z + x ∈ Metric.ball x r := by
              rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]
              exact hz'
            rw [Set.indicator_of_mem hzx, Set.indicator_of_mem hz, add_sub_cancel_right]
          · have hz' : r ≤ ‖z‖ := by
              rw [Metric.mem_ball, dist_zero_right] at hz
              exact not_lt.mp hz
            have hzx : z + x ∉ Metric.ball x r := by
              rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]
              exact not_lt.mpr hz'
            rw [Set.indicator_of_notMem hzx, Set.indicator_of_notMem hz]
      _ = ∫ z in Metric.ball (0 : Work.LWP.R3) r, (‖z‖ : ℝ) ^ s :=
          integral_indicator measurableSet_ball
  rw [hshift]
  exact radial_rpow_integral s hs r hr

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.lintegral_ball_norm_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set

/-- `‖·‖ ^ s` is integrable on any ball of `ℝ³` when `s > -3`.  This is obtained from
`integrableOn_one_add_norm_rpow_ball` by subtracting the (integrable) constant `1`. -/
lemma integrableOn_norm_rpow_ball (s r : ℝ) (hs : -3 < s) :
    IntegrableOn (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) (Metric.ball (0 : Work.LWP.R3) r)
      volume := by
  classical
  have h1 : IntegrableOn (fun y : Work.LWP.R3 => 1 + (‖y‖ : ℝ) ^ s)
      (Metric.ball (0 : Work.LWP.R3) r) volume := integrableOn_one_add_norm_rpow_ball s r hs
  have h2 : IntegrableOn (fun _ : Work.LWP.R3 => (1 : ℝ)) (Metric.ball (0 : Work.LWP.R3) r)
      volume :=
    integrableOn_const (ne_of_lt (Metric.isBounded_ball).measure_lt_top) (by simp)
  have h3 : IntegrableOn (fun y : Work.LWP.R3 => (1 + (‖y‖ : ℝ) ^ s) - 1)
      (Metric.ball (0 : Work.LWP.R3) r) volume := h1.sub h2
  have h4 : (fun y : Work.LWP.R3 => (1 + (‖y‖ : ℝ) ^ s) - 1)
      = fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s := by
    funext y
    ring
  rwa [h4] at h3

/-- The `lintegral` form of the radial power integral over a ball of `ℝ³`:
`∫⁻_{‖y‖<R} ‖y‖^s = 4π R^{s+3}/(s+3)` for `s > -3`.  Since the integrand is non-negative
and integrable on the ball, the Lebesgue integral `∫⁻` of `ENNReal.ofReal` of it agrees with
`ENNReal.ofReal` of the Bochner integral `∫`, to which `radial_rpow_integral` applies. -/
theorem lintegral_ball_norm_rpow (s : ℝ) (hs : -3 < s) (R : ℝ) (hR : 0 < R) :
    ∫⁻ y in Metric.ball (0 : Work.LWP.R3) R, ENNReal.ofReal (‖y‖ ^ s)
      = ENNReal.ofReal (4 * Real.pi * R ^ (s + 3) / (s + 3)) := by
  have hint : IntegrableOn (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s)
      (Metric.ball (0 : Work.LWP.R3) R) volume := integrableOn_norm_rpow_ball s R hs
  have hInt : Integrable ((Metric.ball (0 : Work.LWP.R3) R).indicator
      (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s)) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr hint
  have hnn : 0 ≤ᵐ[volume] (Metric.ball (0 : Work.LWP.R3) R).indicator
      (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) := by
    classical
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [Set.indicator_apply, Pi.zero_apply]
    split_ifs with hy
    · exact Real.rpow_nonneg (norm_nonneg y) s
    · exact le_rfl
  have hcongr :
      ∫⁻ y, (Metric.ball (0 : Work.LWP.R3) R).indicator
          (fun y : Work.LWP.R3 => ENNReal.ofReal ((‖y‖ : ℝ) ^ s)) y
        = ∫⁻ y, ENNReal.ofReal ((Metric.ball (0 : Work.LWP.R3) R).indicator
            (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) y) := by
    classical
    refine lintegral_congr (fun y => ?_)
    by_cases hy : y ∈ Metric.ball (0 : Work.LWP.R3) R
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, ENNReal.ofReal_zero]
  have hofreal : ENNReal.ofReal (∫ y, (Metric.ball (0 : Work.LWP.R3) R).indicator
        (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) y)
      = ∫⁻ y, ENNReal.ofReal ((Metric.ball (0 : Work.LWP.R3) R).indicator
        (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) y) :=
    ofReal_integral_eq_lintegral_ofReal hInt hnn
  rw [← lintegral_indicator measurableSet_ball
    (fun y : Work.LWP.R3 => ENNReal.ofReal ((‖y‖ : ℝ) ^ s))]
  rw [hcongr, ← hofreal]
  rw [integral_indicator measurableSet_ball]
  rw [radial_rpow_integral s hs R hR]

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.lintegral_exterior_norm_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set

/-- `‖·‖ ^ s` is integrable on the complement of a ball of radius `R > 0` in `ℝ³`,
provided `s < -3` (the threshold at which `‖·‖^s` is integrable at infinity in
dimension `3`).  The proof decomposes the integral radially: by
`integrable_fun_norm_addHaar` integrability of `(Ici R).indicator (·^s) ∘ ‖·‖` is
equivalent to integrability of `y ↦ y ^ 2 * y ^ s = y ^ (s + 2)` on `(R, ∞)`, which
holds exactly when `s + 2 < -1`, i.e. `s < -3`. -/
lemma integrableOn_compl_ball_norm_rpow (s : ℝ) (hs : s < -3) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) (Metric.ball (0 : Work.LWP.R3) R)ᶜ
      volume := by
  have hdim : Module.finrank ℝ Work.LWP.R3 = 3 := by
    simp only [Work.LWP.R3]; exact finrank_euclideanSpace_fin
  rw [← MeasureTheory.integrable_indicator_iff measurableSet_ball.compl]
  -- the indicator of the complement of the ball is the radial profile `(Ici R).indicator (·^s)`
  have hpt : (Metric.ball (0 : Work.LWP.R3) R)ᶜ.indicator (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s)
      = fun x : Work.LWP.R3 => (Set.Ici R).indicator (fun t : ℝ => t ^ s) ‖x‖ := by
    funext y
    by_cases hy : y ∈ Metric.ball (0 : Work.LWP.R3) R
    · have h1 : ¬ (R ≤ ‖y‖) := by
        rw [Metric.mem_ball, dist_zero_right] at hy
        exact not_le.mpr hy
      rw [Set.indicator_of_notMem (by simpa using hy), Set.indicator_of_notMem (by simpa using h1)]
    · have h1 : R ≤ ‖y‖ := by
        rw [Metric.mem_ball, dist_zero_right] at hy
        exact not_lt.mp hy
      rw [Set.indicator_of_mem (by simpa using hy), Set.indicator_of_mem (by simpa using h1)]
  rw [hpt]
  rw [MeasureTheory.integrable_fun_norm_addHaar (μ := (volume : Measure Work.LWP.R3))
      (f := (Set.Ici R).indicator (fun t : ℝ => t ^ s)), hdim]
  norm_num
  -- the radial weight `y ^ 2 * y ^ s` is the indicator of `Ici R` of `y ^ (s + 2)`
  have hfun : (fun y : ℝ => y ^ (2:ℕ) * (Set.Ici R).indicator (fun t : ℝ => t ^ s) y)
      = (Set.Ici R).indicator (fun y : ℝ => y ^ (s + 2)) := by
    funext y
    by_cases hy : R ≤ y
    · have hy0 : (0:ℝ) < y := lt_of_lt_of_le hR hy
      rw [Set.indicator_of_mem (Set.mem_Ici.mpr hy), Set.indicator_of_mem (Set.mem_Ici.mpr hy)]
      rw [← Real.rpow_natCast y 2, ← Real.rpow_add hy0 ((2:ℕ):ℝ) s]
      congr 1
      ring
    · have hy' : y ∉ Set.Ici R := fun h => hy (Set.mem_Ici.mp h)
      rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem hy', mul_zero]
  rw [hfun]
  rw [← MeasureTheory.integrable_indicator_iff measurableSet_Ioi]
  rw [Set.indicator_indicator]
  rw [show Set.Ioi (0:ℝ) ∩ Set.Ici R = Set.Ici R from by
        rw [Set.inter_eq_right]; intro x hx; exact lt_of_lt_of_le hR hx]
  rw [MeasureTheory.integrable_indicator_iff measurableSet_Ici]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact (integrableOn_Ioi_rpow_iff hR).mpr (by linarith)

/-- The Bochner integral of the radial power over the exterior of a ball of `ℝ³`:
`∫_{‖y‖>R} ‖y‖^s dy = 4π R^{s+3}/(-(s+3))` for `s < -3` and `R > 0`.
This is the `s < -3` companion of `radial_rpow_integral` (which covers `s > -3` on a
ball); it is obtained by the polar decomposition `integral_fun_norm_addHaar` in
dimension `3` together with the one-dimensional integral `∫_R^∞ y^{s+2} dy =
-R^{s+3}/(s+3)`. -/
lemma integral_compl_ball_norm_rpow (s : ℝ) (hs : s < -3) (R : ℝ) (hR : 0 < R) :
    ∫ y in (Metric.ball (0 : Work.LWP.R3) R)ᶜ, (‖y‖ : ℝ) ^ s
      = 4 * Real.pi * R ^ (s + 3) / (-(s + 3)) := by
  have hfin : Module.finrank ℝ Work.LWP.R3 = 3 := by
    simp only [Work.LWP.R3]; exact finrank_euclideanSpace_fin
  -- volume of the unit ball of `ℝ³`
  have hvol : volume.real (Metric.ball (0 : Work.LWP.R3) 1) = 4 * Real.pi / 3 := by
    rw [Measure.real_def, EuclideanSpace.volume_ball_fin_three]
    rw [show ENNReal.ofReal (1:ℝ) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)
          = ENNReal.ofReal (Real.pi * 4 / 3) by simp]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  set f : ℝ → ℝ := (Set.Ici R).indicator (fun t : ℝ => t ^ s) with hf
  -- step 1: the exterior integral is the full-space integral of the radial profile `f ∘ ‖·‖`
  have hpt : (Metric.ball (0 : Work.LWP.R3) R)ᶜ.indicator (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s)
      = fun x : Work.LWP.R3 => f ‖x‖ := by
    funext y
    rw [hf]
    by_cases hy : y ∈ Metric.ball (0 : Work.LWP.R3) R
    · have h1 : ¬ (R ≤ ‖y‖) := by
        rw [Metric.mem_ball, dist_zero_right] at hy
        exact not_le.mpr hy
      rw [Set.indicator_of_notMem (by simpa using hy), Set.indicator_of_notMem (by simpa using h1)]
    · have h1 : R ≤ ‖y‖ := by
        rw [Metric.mem_ball, dist_zero_right] at hy
        exact not_lt.mp hy
      rw [Set.indicator_of_mem (by simpa using hy), Set.indicator_of_mem (by simpa using h1)]
  -- step 2: the one-dimensional radial integral `∫_0^∞ y^2 * f y dy = -R^{s+3}/(s+3)`
  have hJ : ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ Work.LWP.R3 - 1) • f y
      = -(R ^ (s + 3)) / (s + 3) := by
    rw [hfin]
    simp only [hf, Nat.reduceSub]
    have key : (fun y : ℝ => y ^ (2:ℕ) • (Set.Ici R).indicator (fun t : ℝ => t ^ s) y)
        = (Set.Ici R).indicator (fun y : ℝ => y ^ (s + 2)) := by
      funext y
      by_cases hy : R ≤ y
      · have hy0 : (0:ℝ) < y := lt_of_lt_of_le hR hy
        rw [Set.indicator_of_mem (Set.mem_Ici.mpr hy)]
        rw [Set.indicator_of_mem (Set.mem_Ici.mpr hy)]
        rw [smul_eq_mul, ← Real.rpow_natCast y 2, ← Real.rpow_add hy0 ((2:ℕ):ℝ) s]
        congr 1
        ring
      · have hy' : y ∉ Set.Ici R := fun h => hy (Set.mem_Ici.mp h)
        rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem hy', smul_zero]
    rw [key]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    rw [Set.indicator_indicator]
    rw [MeasureTheory.integral_indicator (measurableSet_Ioi.inter measurableSet_Ici)]
    rw [show Set.Ioi (0:ℝ) ∩ Set.Ici R = Set.Ici R from by
          rw [Set.inter_eq_right]; intro x hx; exact lt_of_lt_of_le hR hx]
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    rw [integral_Ioi_rpow_of_lt (by linarith : s + 2 < -1) hR]
    rw [show s + 2 + 1 = s + 3 by ring]
  -- step 3: assemble
  rw [← MeasureTheory.integral_indicator measurableSet_ball.compl]
  rw [hpt]
  rw [MeasureTheory.integral_fun_norm_addHaar volume f, hJ, hfin, hvol]
  have hsz : s + 3 ≠ 0 := by linarith
  rw [nsmul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-- The `lintegral` form of the radial power integral over the exterior of a ball of `ℝ³`:
`∫⁻_{‖y‖>R} ‖y‖^s = 4π R^{s+3}/(-(s+3))` for `s < -3`.  Since the integrand is
non-negative and integrable on the exterior (`integrableOn_compl_ball_norm_rpow`), the
Lebesgue integral `∫⁻` of `ENNReal.ofReal` of it agrees with `ENNReal.ofReal` of the
Bochner integral `∫`, to which `integral_compl_ball_norm_rpow` applies. -/
theorem lintegral_exterior_norm_rpow (s : ℝ) (hs : s < -3) (R : ℝ) (hR : 0 < R) :
    ∫⁻ y in (Metric.ball (0 : Work.LWP.R3) R)ᶜ, ENNReal.ofReal (‖y‖ ^ s)
      = ENNReal.ofReal (4 * Real.pi * R ^ (s + 3) / (-(s + 3))) := by
  have hint : IntegrableOn (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s)
      (Metric.ball (0 : Work.LWP.R3) R)ᶜ volume :=
    integrableOn_compl_ball_norm_rpow s hs R hR
  have hInt : Integrable ((Metric.ball (0 : Work.LWP.R3) R)ᶜ.indicator
      (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s)) volume :=
    (integrable_indicator_iff measurableSet_ball.compl).mpr hint
  have hnn : 0 ≤ᵐ[volume] (Metric.ball (0 : Work.LWP.R3) R)ᶜ.indicator
      (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) := by
    classical
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [Set.indicator_apply, Pi.zero_apply]
    split_ifs with hy
    · exact Real.rpow_nonneg (norm_nonneg y) s
    · exact le_rfl
  have hcongr :
      ∫⁻ y, (Metric.ball (0 : Work.LWP.R3) R)ᶜ.indicator
          (fun y : Work.LWP.R3 => ENNReal.ofReal ((‖y‖ : ℝ) ^ s)) y
        = ∫⁻ y, ENNReal.ofReal ((Metric.ball (0 : Work.LWP.R3) R)ᶜ.indicator
            (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) y) := by
    classical
    refine lintegral_congr (fun y => ?_)
    by_cases hy : y ∈ (Metric.ball (0 : Work.LWP.R3) R)ᶜ
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, ENNReal.ofReal_zero]
  have hofreal : ENNReal.ofReal (∫ y, (Metric.ball (0 : Work.LWP.R3) R)ᶜ.indicator
        (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) y)
      = ∫⁻ y, ENNReal.ofReal ((Metric.ball (0 : Work.LWP.R3) R)ᶜ.indicator
        (fun y : Work.LWP.R3 => (‖y‖ : ℝ) ^ s) y) :=
    ofReal_integral_eq_lintegral_ofReal hInt hnn
  rw [← lintegral_indicator measurableSet_ball.compl
    (fun y : Work.LWP.R3 => ENNReal.ofReal ((‖y‖ : ℝ) ^ s))]
  rw [hcongr, ← hofreal]
  rw [integral_indicator measurableSet_ball.compl]
  rw [integral_compl_ball_norm_rpow s hs R hR]

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.sphere_ball_polar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set
open scoped ENNReal NNReal Topology

/-- The radial factor of the polar decomposition of the unit ball:
`∫_{(0,∞)} 1_{r < 1} r ^ 2 d(volumeIoiPow 2) = 1/5`, because `volumeIoiPow 2` has density
`r ↦ r ^ 2` on `(0,∞)`. -/
lemma volumeIoiPow_two_integral_indicator :
    ∫ r : Set.Ioi (0:ℝ), (if (r:ℝ) < 1 then (r:ℝ)^2 else 0) ∂(Measure.volumeIoiPow 2) = 1/5 := by
  rw [Measure.volumeIoiPow]
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun r : Set.Ioi (0:ℝ) => ENNReal.ofReal ((r:ℝ)^2))]
  · have htoReal : ∀ r : Set.Ioi (0:ℝ), (ENNReal.ofReal ((r:ℝ)^2)).toReal = (r:ℝ)^2 :=
      fun r => ENNReal.toReal_ofReal (sq_nonneg (r:ℝ))
    simp only [htoReal, smul_eq_mul]
    rw [integral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Ioi
      (f := fun y : ℝ => y^2 * (if y < 1 then y^2 else 0))]
    have h1 : ∀ x ∈ Ioi (0:ℝ),
        x^2 * (if x < 1 then x^2 else 0) = (Iio (1:ℝ)).indicator (fun y => y^4) x := by
      intro x _
      by_cases hx1 : x < 1
      · rw [if_pos hx1, Set.indicator_of_mem (show x ∈ Iio (1:ℝ) from hx1)]
        ring
      · rw [if_neg hx1, mul_zero, Set.indicator_of_notMem (show x ∉ Iio (1:ℝ) from hx1)]
    rw [setIntegral_congr_fun measurableSet_Ioi h1]
    rw [setIntegral_indicator measurableSet_Iio]
    rw [show Ioi (0:ℝ) ∩ Iio (1:ℝ) = Ioo (0:ℝ) 1 from Ioi_inter_Iio]
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rw [integral_pow]
    norm_num
  · exact (measurable_subtype_coe.pow_const 2).ennreal_ofReal
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top

theorem sphere_ball_polar (h w : Work.LWP.R3) :
    (∫ u : Metric.sphere (0 : Work.LWP.R3) 1,
        (inner ℝ (u : Work.LWP.R3) h) * (inner ℝ (u : Work.LWP.R3) w)
        ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere)
      = 5 * ∫ x in Metric.ball (0 : Work.LWP.R3) 1,
          (inner ℝ x h) * (inner ℝ x w) := by
  classical
  -- The polar-coordinate decomposition turns the unit-ball integral into the product of the
  -- sphere integral and the radial integral `∫_{(0,1)} r ^ 2 · r ^ 2 dr = 1/5`.
  have key : (∫ x in Metric.ball (0 : Work.LWP.R3) 1,
        (inner ℝ x h) * (inner ℝ x w))
      = (1/5) * (∫ u : Metric.sphere (0 : Work.LWP.R3) 1,
        (inner ℝ (u : Work.LWP.R3) h) * (inner ℝ (u : Work.LWP.R3) w)
        ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere) := by
    rw [← integral_indicator measurableSet_ball]
    rw [polar_decomposition]
    have hcongr : ∀ p : Metric.sphere (0 : Work.LWP.R3) 1 × Set.Ioi (0:ℝ),
        (Metric.ball (0 : Work.LWP.R3) 1).indicator
          (fun x => (inner ℝ x h) * (inner ℝ x w)) (p.2.1 • (p.1.1 : Work.LWP.R3))
        = ((inner ℝ (p.1.1 : Work.LWP.R3) h) * (inner ℝ (p.1.1 : Work.LWP.R3) w))
          * (if (p.2.1 : ℝ) < 1 then (p.2.1 : ℝ)^2 else 0) := by
      intro p
      have hnorm : ‖(p.1.1 : Work.LWP.R3)‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
      have hpos : (0:ℝ) < p.2.1 := p.2.2
      have hrsmul : ‖p.2.1 • (p.1.1 : Work.LWP.R3)‖ = p.2.1 := by
        rw [norm_smul, hnorm, mul_one, Real.norm_eq_abs, abs_of_pos hpos]
      have hmem : (p.2.1 • (p.1.1 : Work.LWP.R3)) ∈ Metric.ball (0 : Work.LWP.R3) 1
          ↔ p.2.1 < 1 := by
        rw [Metric.mem_ball, dist_zero_right, hrsmul]
      rw [Set.indicator_apply]
      by_cases hlt : (p.2.1 : ℝ) < 1
      · rw [if_pos (hmem.mpr hlt), if_pos hlt, real_inner_smul_left, real_inner_smul_left]
        ring
      · rw [if_neg (fun hh => hlt (hmem.mp hh)), if_neg hlt, mul_zero]
    simp_rw [hcongr]
    rw [integral_prod_mul
      (f := fun u : Metric.sphere (0 : Work.LWP.R3) 1 =>
        (inner ℝ (u : Work.LWP.R3) h) * (inner ℝ (u : Work.LWP.R3) w))
      (g := fun r : Set.Ioi (0:ℝ) => if (r:ℝ) < 1 then (r:ℝ)^2 else 0)]
    rw [volumeIoiPow_two_integral_indicator]
    ring
  rw [key]
  ring

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.EFP.integrableOn_mul_eFam_cos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution.EFP

theorem integrableOn_mul_eFam_cos (F : ℝ → ℝ → ℝ) (z : ℝ) (m : ℕ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => F z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hz : MeasureTheory.IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      Work.Spaces.Iθ := by
  -- `volume.restrict Iθ` is a finite measure: `Iθ = [0, π/2]` is compact.
  haveI hfin : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact isCompact_Icc.measure_lt_top
  -- The mode `eFam m` is bounded on `Iθ`.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ θ ∈ Work.Spaces.Iθ,
      ‖Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ ≤ C := by
    have hcont : Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
      Real.continuous_cos.mul
        (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
          Real.continuous_sin)
    have hcomp : IsCompact (Work.Spaces.Iθ) := isCompact_Icc
    obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont.continuousOn
    exact ⟨C, fun θ hθ => hC θ hθ⟩
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 Work.Spaces.zero_mem_Iθ)
  -- `F z · * √(cos ·) ∈ L²(Iθ)`.
  have haesmF : AEStronglyMeasurable (fun θ => F z θ * Real.sqrt (Real.cos θ))
      (volume.restrict Work.Spaces.Iθ) :=
    hmeas.mul ((Real.continuous_sqrt.comp Real.continuous_cos).aestronglyMeasurable)
  have hz' : Integrable (fun θ => F z θ ^ 2 * Real.cos θ)
      (volume.restrict Work.Spaces.Iθ) := hz
  have hsqF : Integrable (fun θ => (F z θ * Real.sqrt (Real.cos θ)) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
    refine hz'.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have hcos : 0 ≤ Real.cos θ := by
      apply Real.cos_nonneg_of_mem_Icc
      exact ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    rw [mul_pow, Real.sq_sqrt hcos]
  have hF : MemLp (fun θ => F z θ * Real.sqrt (Real.cos θ)) 2
      (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq haesmF).mpr hsqF
  -- `eFam m · * √(cos ·) ∈ L²(Iθ)`, since `eFam m` is bounded on `Iθ` and `√(cos θ) ≤ 1` there.
  have hcontG : Continuous (fun θ : ℝ =>
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.sqrt (Real.cos θ)) :=
    (Real.continuous_cos.mul
      (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
        Real.continuous_sin)).mul (Real.continuous_sqrt.comp Real.continuous_cos)
  have hG : MemLp (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.sqrt (Real.cos θ)) 2
      (volume.restrict Work.Spaces.Iθ) := by
    refine MemLp.of_bound hcontG.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have hsqrtle : ‖Real.sqrt (Real.cos θ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_one.mpr (Real.cos_le_one θ)
    calc ‖Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.sqrt (Real.cos θ)‖
        = ‖Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ * ‖Real.sqrt (Real.cos θ)‖ := norm_mul _ _
      _ ≤ C * 1 := mul_le_mul (hC θ hθ) hsqrtle (norm_nonneg _) hCnonneg
      _ = C := mul_one C
  -- Hölder: a product of two `L²` functions is `L¹`.
  have hprod : MemLp ((fun θ => F z θ * Real.sqrt (Real.cos θ)) *
      (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.sqrt (Real.cos θ))) 1
      (volume.restrict Work.Spaces.Iθ) := hF.mul hG
  have hint : IntegrableOn ((fun θ => F z θ * Real.sqrt (Real.cos θ)) *
      (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.sqrt (Real.cos θ)))
      Work.Spaces.Iθ := MeasureTheory.memLp_one_iff_integrable.mp hprod
  -- Rewrite the product into the requested shape, using `√(cos θ) * √(cos θ) = cos θ`.
  have heq : ∀ θ ∈ Work.Spaces.Iθ,
      ((fun θ => F z θ * Real.sqrt (Real.cos θ)) *
        (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.sqrt (Real.cos θ))) θ
      = F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
    intro θ hθ
    have hcos : 0 ≤ Real.cos θ := by
      apply Real.cos_nonneg_of_mem_Icc
      exact ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    simp only [Pi.mul_apply]
    rw [mul_mul_mul_comm, Real.mul_self_sqrt hcos]
  exact IntegrableOn.congr_fun hint heq measurableSet_Icc

end Work.EllipticEst.ModalSolution.EFP
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.Aux2.sqIntegralAbsLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The `L²` Cauchy–Schwarz inequality for interval integrals

For `a ≤ b` and a continuous `f : ℝ → ℝ`,

  `(∫_{a}^{b} |f|)² ≤ (b - a) · ∫_{a}^{b} f²`.

This is the `L²` Cauchy–Schwarz inequality applied to the pair of functions `(|f|, 1)` on the
interval `(a, b]`, whose second `L²` norm is `b - a`.  The analytic content is delegated to
`Work.FTS.H2.DivQ.sqIntervalIntegralLe` (Cauchy–Schwarz for the interval integral of a general
interval-integrable function, itself derived from the abstract Cauchy–Schwarz inequality on
`L²`); here we only specialise it to `|f|` and use `|f|² = f²`.

The lemma is the sibling of `gcTail` in this directory, which consumes it to bound
`(Gc N b u t θ)²` by `4N ∫ (∂ₜu - b u)²` off the truncation window.
-/

namespace Work.FTS.EllSol.ShiftFT.Aux2

/-- **Cauchy–Schwarz for the interval integral.**  For `a ≤ b` and continuous `f`,
`(∫_{a}^{b} |f|)² ≤ (b - a) ∫_{a}^{b} f²`. -/
theorem sqIntegralAbsLe (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in a..b, |f x|) ^ 2 ≤ (b - a) * ∫ x in a..b, (f x) ^ 2 := by
  have habs : Continuous fun x : ℝ => |f x| := hf.abs
  have h := Work.FTS.H2.DivQ.sqIntervalIntegralLe (fun x : ℝ => |f x|) hab
    (habs.intervalIntegrable a b) ((habs.pow 2).intervalIntegrable a b)
  have h2 : (∫ x in a..b, (|f x|) ^ 2) = ∫ x in a..b, (f x) ^ 2 :=
    intervalIntegral.integral_congr (fun x _ => sq_abs (f x))
  rwa [h2] at h

end Work.FTS.EllSol.ShiftFT.Aux2
end
-- ===== merged: Submission.Work.FTS.EllSol.powerHardyAll =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The power Hardy inequality on `(0,a)` for every exponent `η ≥ 0`

Main statement `Work.FTS.EllSol.powerHardyAll`: there is a universal constant `C > 0` such
that for every `η ≥ 0`, every `a > 0` and every `h` of class `C¹` on `(0,a)` with
`h → 0` at `0⁺`, whose `t^{-η}`-weighted squared derivative is integrable on `(0,a)`,

  `t ↦ h t ^ 2 * t ^ (-(2+η))` is integrable on `(0,a)`, and
  `∫_0^a h² t^{-(2+η)} ≤ C ∫_0^a (h')² t^{-η}`.

The constant `C = 4` works: the auxiliary `powerHardyFiniteAll` below is the sharp bound
`∫_0^a h² t^{-(2+η)} ≤ 4/(1+η)² ∫_0^a (h')² t^{-η}` (the classical integration-by-parts /
weighted Cauchy–Schwarz proof, exactly as in `Work.FTS.EllipticEst.UopHk.powerHardyFinite`,
noting that the hypothesis `η < 1` of that statement is not used by its argument — only
`0 ≤ η` is), and `4/(1+η)² ≤ 4` for `η ≥ 0`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.EllSol

-- the two general-purpose ingredients of the argument (neither restricts `η`)
open Work.FTS.EllipticEst.UopHk




end Work.FTS.EllSol
end
-- ===== merged: Submission.Work.FTS.EllSol.slice_zero_slot_finite =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ

/-- The angular weight `sin(2θ)^{-η}` (`η = 99/100`) of the zero-th angular slot. -/
def sEta (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- `sEta` is nonnegative on the angular interval. -/
lemma sEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ sEta θ :=
  Real.rpow_nonneg (x := Real.sin (2 * θ)) (y := -(Work.Spaces.eta))
    (Real.sin_nonneg_of_mem_Icc (x := 2 * θ)
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)

/-- `sEta` is positive on the interior of the angular interval. -/
lemma sEta_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 < sEta θ :=
  Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])) _

/-- `sEta ≥ 1` on the interior of the angular interval. -/
lemma one_le_sEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ sEta θ := by
  have h := Real.rpow_le_rpow_of_nonpos (z := -(Work.Spaces.eta))
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
    (Real.sin_le_one (2 * θ)) (by norm_num [Work.Spaces.eta])
  rwa [Real.one_rpow] at h

/-- `sEta` is integrable on the angular interval. -/
lemma sEta_integrableOn : MeasureTheory.IntegrableOn sEta Iθ :=
  (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
    (by norm_num [Work.Spaces.eta])).1

/-- `sEta` is continuous on the interior of the angular interval. -/
lemma continuousOn_sEta : ContinuousOn sEta (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  ContinuousOn.rpow_const
    (Real.continuous_sin.comp_continuousOn (continuousOn_const.mul continuousOn_id))
    (fun x hx => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
      (by linarith [hx.2, Real.pi_pos]))))

/-- A function continuous on the open angle interval is almost everywhere strongly measurable
for the restriction of Lebesgue measure to `Iθ` (the two sets differ by the null set
`{0, π/2}`). -/
lemma aesm_of_continuousOn_Ioo {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable g (volume.restrict Iθ) := by
  have hθ : Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc).symm
  rw [MeasureTheory.Measure.restrict_congr_set hθ]
  exact hg.aestronglyMeasurable measurableSet_Ioo

/-- The elementary pointwise inequality `|x| ≤ x² + 1/4`. -/
lemma abs_le_sq_add_quarter (x : ℝ) : |x| ≤ x ^ 2 + 1 / 4 := by
  nlinarith [sq_nonneg (2 * |x| - 1), sq_abs x]





end Work.FTS.EllSol
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.SliceA.not_integrableOn_sinCos2_of_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.SliceA

open MeasureTheory Set Filter
open scoped Real Topology

/-!
## Non-integrability of `sin θ · cos²θ · |g θ|` at the right endpoint `θ = π/2`

For `N ≥ 2` and `c ≠ 0`, if `θ ↦ (π/2 - θ)^(N+2) · g θ` tends to `c` as `θ → (π/2)⁻`, then
`g` blows up like `c · (π/2 - θ)^{-(N+2)}` near `π/2`.  Since `sin θ → 1` and
`cos²θ = sin²(π/2 - θ) ~ (π/2 - θ)²` there, the integrand behaves like
`|c| · (π/2 - θ)^{-N}`, whose integral diverges at `π/2` for `N ≥ 1`.  Hence it is not
integrable on `Iθ = [0, π/2]`.

The quantitative pointwise bound used below is, for `θ ∈ (π/2 - δ, π/2)`,

`sin θ · cos²θ · |g θ| ≥ (|c| / π²) / (π/2 - θ)^N`,

obtained from `sin θ ≥ 1/2` (for `θ ∈ (π/2 - 1, π/2)`),
`cos²θ ≥ (4/π²)(π/2 - θ)²` (`cos θ = sin(π/2 - θ) ≥ (2/π)(π/2 - θ)`) and
`|g θ| ≥ (|c|/2) / (π/2 - θ)^(N+2)` (from the limit).  The divergence is then supplied by
`Work.FTS.EllipticEst.remov.coerc.not_integrableOn_of_le_div_sub_pow`.
-/




end Work.FTS.EllipticEst.H2W.SliceA
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.sliceWirtinger =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W


/-- The Lebesgue measure of the angular slice `Iθ = [0, π/2]` is `π/2`. -/
private lemma volume_real_Iθ : volume.real Work.Spaces.Iθ = Real.pi / 2 := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [Work.Spaces.Iθ, Real.volume_real_Icc_of_le hle, sub_zero]

/-- The measure `volume.restrict Iθ` equals `volume.restrict (Ioo 0 (π/2))`: the two endpoints
of the slice form a null set. -/
private lemma restrict_Iθ_eq_restrict_Ioo_prv :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact (Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2) (μ := volume))).symm


/-- A constant is integrable over the angular slice. -/
private lemma integrableOn_const_Iθ (c : ℝ) : IntegrableOn (fun _ : ℝ => c) Work.Spaces.Iθ :=
  MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (μ := volume) (C := c)
    (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

/-- A constant is integrable over the open interval. -/
private lemma integrableOn_const_Ioo (c : ℝ) :
    Integrable (fun _ : ℝ => c) (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
  MeasureTheory.integrableOn_const (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (μ := volume) (C := c)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)


/-- **Boundedness criterion.** A function that is continuous on `(0, π/2)` and bounded there by
a constant is integrable over the angular slice `Iθ`. -/
private lemma integrableOn_Iθ_of_bound {g : ℝ → ℝ} {C : ℝ}
    (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hbd : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), |g x| ≤ C) :
    IntegrableOn g Work.Spaces.Iθ := by
  show Integrable g (volume.restrict Work.Spaces.Iθ)
  rw [restrict_Iθ_eq_restrict_Ioo_prv]
  refine Integrable.mono' (integrableOn_const_Ioo C)
    (hg.aestronglyMeasurable measurableSet_Ioo) ?_
  exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
    (Eventually.of_forall (fun x hx => by rw [Real.norm_eq_abs]; exact hbd x hx))


end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonFullWeightIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary facts on the open interval `Iθo = (0, π/2)` -/

private lemma sin_two_pos_Iθo {θ : ℝ} (hθ : θ ∈ Iθo) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma sub_pi_div_two_pos {θ : ℝ} (hθ : θ ∈ Iθo) : 0 < Real.pi / 2 - θ := by
  linarith [hθ.2, Real.pi_pos]

/-- Jordan's inequality in the form `(4/π) min θ (π/2 - θ) ≤ sin (2θ)` on `Iθo`. -/
private lemma four_div_pi_mul_min_le_sin_two {θ : ℝ} (hθ : θ ∈ Iθo) :
    (4 / Real.pi) * min θ (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
  rcases le_total θ (Real.pi / 2 - θ) with h | h
  · rw [min_eq_left h]
    exact sin_two_ge_four_div_pi_mul θ hθ.1.le (by linarith [hθ.2, h])
  · rw [min_eq_right h]
    exact sin_two_ge_four_div_pi_mul_sub θ (by linarith [hθ.1, h]) hθ.2

/-- The singular weight is dominated by the `min` of the two endpoint powers. -/
private lemma sin_two_rpow_le_min {p θ : ℝ} (hp : 0 < p) (hθ : θ ∈ Iθo) :
    (Real.sin (2 * θ)) ^ (-p) ≤ (Real.pi / 4) ^ p * (min θ (Real.pi / 2 - θ)) ^ (-p) := by
  have hm0 : 0 < min θ (Real.pi / 2 - θ) := lt_min hθ.1 (sub_pi_div_two_pos hθ)
  have hbase : 0 < 4 / Real.pi * min θ (Real.pi / 2 - θ) := mul_pos (by positivity) hm0
  have key : (Real.sin (2 * θ)) ^ (-p) ≤ (4 / Real.pi * min θ (Real.pi / 2 - θ)) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hbase (four_div_pi_mul_min_le_sin_two hθ) (by linarith)
  have hcoef : (4 / Real.pi : ℝ) ^ (-p) = (Real.pi / 4) ^ p := by
    have hp4 : (0 : ℝ) < 4 / Real.pi := by positivity
    rw [Real.rpow_neg (le_of_lt hp4), ← Real.inv_rpow (le_of_lt hp4), inv_div]
  rwa [Real.mul_rpow (le_of_lt (by positivity : (0 : ℝ) < 4 / Real.pi)) (le_of_lt hm0),
    hcoef] at key

/-! ## The pointwise majorant -/

/-- The full-weight integrand is dominated by the endpoint majorant. -/
private lemma full_weight_bound (u : ℝ → ℝ) (η C : ℝ) (hη0 : 0 ≤ η) (_hC : 0 ≤ C)
    (hb1 : ∀ θ ∈ Iθo, |u θ| ≤ C * θ)
    (hb2 : ∀ θ ∈ Iθo, |u θ| ≤ C * (Real.pi / 2 - θ)) {θ : ℝ} (hθ : θ ∈ Iθo) :
    |(u θ) ^ 2 / (Real.sin (2 * θ)) ^ (2 + η)| ≤
      (C ^ 2 * (Real.pi / 4) ^ (2 + η)) * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by
  have hδ0 := sub_pi_div_two_pos hθ
  have hs0 := sin_two_pos_Iθo hθ
  have hm0 : 0 < min θ (Real.pi / 2 - θ) := lt_min hθ.1 hδ0
  -- `u² ≤ C² min(θ, δ)²`
  have hu2 : (u θ) ^ 2 ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by
    have h1 : (u θ) ^ 2 ≤ C ^ 2 * θ ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (u θ)) (hb1 θ hθ) 2
      rw [sq_abs] at h
      calc (u θ) ^ 2 ≤ (C * θ) ^ 2 := h
        _ = C ^ 2 * θ ^ 2 := by ring
    have h2 : (u θ) ^ 2 ≤ C ^ 2 * (Real.pi / 2 - θ) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (u θ)) (hb2 θ hθ) 2
      rw [sq_abs] at h
      calc (u θ) ^ 2 ≤ (C * (Real.pi / 2 - θ)) ^ 2 := h
        _ = C ^ 2 * (Real.pi / 2 - θ) ^ 2 := by ring
    rcases le_total θ (Real.pi / 2 - θ) with h | h
    · rw [min_eq_left h]; exact h1
    · rw [min_eq_right h]; exact h2
  -- the singular weight is dominated by `min^{-(2+η)}`
  have hsinp : (Real.sin (2 * θ)) ^ (-(2 + η))
      ≤ (Real.pi / 4) ^ (2 + η) * (min θ (Real.pi / 2 - θ)) ^ (-(2 + η)) :=
    sin_two_rpow_le_min (p := 2 + η) (by linarith) hθ
  -- `min² · min^{-(2+η)} = min^{-η}`
  have hmpow : (min θ (Real.pi / 2 - θ)) ^ 2 * (min θ (Real.pi / 2 - θ)) ^ (-(2 + η))
      = (min θ (Real.pi / 2 - θ)) ^ (-η) := by
    rw [← Real.rpow_natCast (min θ (Real.pi / 2 - θ)) 2, ← Real.rpow_add hm0]
    congr 1
    ring
  have hmle : (min θ (Real.pi / 2 - θ)) ^ (-η)
      ≤ θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η) := by
    rcases le_total θ (Real.pi / 2 - θ) with h | h
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg hδ0.le _)
    · rw [min_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg hθ.1.le _)
  have hsg : 0 ≤ (Real.sin (2 * θ)) ^ (-(2 + η)) := Real.rpow_nonneg hs0.le _
  have hnn : 0 ≤ C ^ 2 * (Real.pi / 4) ^ (2 + η) :=
    mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (by positivity) _)
  have hdiv : (u θ) ^ 2 / (Real.sin (2 * θ)) ^ (2 + η)
      = (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) := by
    rw [div_eq_mul_inv, Real.rpow_neg hs0.le]
  have habs : |(u θ) ^ 2 / (Real.sin (2 * θ)) ^ (2 + η)|
      = (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) := by
    rw [hdiv, abs_of_nonneg (mul_nonneg (sq_nonneg _) hsg)]
  calc |(u θ) ^ 2 / (Real.sin (2 * θ)) ^ (2 + η)|
      = (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) := habs
    _ ≤ (C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2)
          * ((Real.pi / 4) ^ (2 + η) * (min θ (Real.pi / 2 - θ)) ^ (-(2 + η))) :=
        mul_le_mul hu2 hsinp hsg (mul_nonneg (sq_nonneg C) (sq_nonneg _))
    _ = C ^ 2 * (Real.pi / 4) ^ (2 + η)
          * ((min θ (Real.pi / 2 - θ)) ^ 2 * (min θ (Real.pi / 2 - θ)) ^ (-(2 + η))) := by
        ring
    _ = C ^ 2 * (Real.pi / 4) ^ (2 + η) * (min θ (Real.pi / 2 - θ)) ^ (-η) := by rw [hmpow]
    _ ≤ C ^ 2 * (Real.pi / 4) ^ (2 + η) * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
        mul_le_mul_of_nonneg_left hmle hnn

/-! ## Continuity on the open interval -/

private lemma continuousOn_full_weight (u : ℝ → ℝ) (η : ℝ) (hu : ContinuousOn u Iθo) :
    ContinuousOn (fun θ : ℝ => (u θ) ^ 2 / (Real.sin (2 * θ)) ^ (2 + η)) Iθo := by
  have hsin2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Iθo :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hden : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 + η)) Iθo :=
    hsin2.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_Iθo hθ)))
  exact (hu.pow 2).div hden fun θ hθ =>
    (Real.rpow_pos_of_pos (sin_two_pos_Iθo hθ) (2 + η)).ne'

/-! ## The theorem -/

theorem HonFullWeightIntegrable (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (u : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ContinuousOn u Work.FTS.EllipticEst.Honest.Iθo)
    (hb1 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |u θ| ≤ C * θ)
    (hb2 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |u θ| ≤ C * (Real.pi / 2 - θ)) :
    MeasureTheory.IntegrableOn
        (fun θ => (u θ) ^ 2 / (Real.sin (2 * θ)) ^ (2 + η)) Work.FTS.EllipticEst.Honest.Iθo
        MeasureTheory.volume := by
  have hK : 0 ≤ C ^ 2 * (Real.pi / 4) ^ (2 + η) :=
    mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (by positivity) _)
  have h := Work.Elliptic.integrableOn_of_rpow_majorant hη0 hη1 hK
    (continuousOn_full_weight u η hu) (fun θ hθ => by
      rw [Real.norm_eq_abs]
      exact full_weight_bound u η C hη0 hC hb1 hb2 hθ)
  simpa [Iθo] using h.mono_set Ioo_subset_Icc_self

end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.PthCore.mean_zero_poincare =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Interval

namespace Work.FTS.EllipticEst.Honest.PthCore

/-- **Fundamental theorem of calculus between two interior points.**  If `g` has derivative `g'`
on the open interval `(a,b)`, and `g'` is integrable on `[a,b]`, then for any two interior points
`p, q ∈ (a,b)` the increment of `g` is the interval integral of `g'` — note that no endpoint
regularity of `g` (or of `g'`) is assumed. -/
lemma sub_eq_intervalIntegral_Ioo {a b : ℝ} {g g' : ℝ → ℝ}
    (hdiff : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x)
    (hg' : IntegrableOn g' (Set.Icc a b) volume)
    {p q : ℝ} (hp : p ∈ Set.Ioo a b) (hq : q ∈ Set.Ioo a b) :
    g q - g p = ∫ t in p..q, g' t := by
  have hmem : ∀ t ∈ Set.uIcc p q, t ∈ Set.Ioo a b := by
    intro t ht
    rcases le_total p q with hpq | hqp
    · rw [Set.uIcc_of_le hpq] at ht
      exact ⟨lt_of_lt_of_le hp.1 ht.1, lt_of_le_of_lt ht.2 hq.2⟩
    · rw [Set.uIcc_of_ge hqp] at ht
      exact ⟨lt_of_lt_of_le hq.1 ht.1, lt_of_le_of_lt ht.2 hp.2⟩
  have hint : IntervalIntegrable g' volume p q := by
    rcases le_total p q with hpq | hqp
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hpq).mpr
        (hg'.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hp.1.le hq.2.le)))
    · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hqp).mpr
        (hg'.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hq.1.le hp.2.le)))).symm
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hdiff t (hmem t ht)) hint).symm

/-- **Zero-mean sup bound.**  If `f` has derivative `f'` on the open interval `(a,b)`, both `f`
and `f'` are integrable on `[a,b]`, and `f` has vanishing mean, then every interior value of `f`
is bounded by `∫_a^b |f'|`.  This is the elementary "mean-zero Poincaré" sup estimate obtained
from `f x = (b-a)⁻¹ ∫_a^b (f x - f y) dy` and the interior fundamental theorem of calculus. -/
lemma mean_zero_sup_bound {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hi : IntervalIntegrable f volume a b)
    (hi' : IntervalIntegrable f' volume a b)
    (hmean : (∫ x in a..b, f x) = 0) :
    ∀ x ∈ Set.Ioo a b, |f x| ≤ ∫ t in a..b, |f' t| := by
  intro x hx
  set K : ℝ := ∫ t in a..b, |f' t| with hK
  have hfIcc : IntegrableOn f (Set.Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp hi
  have hf'Icc : IntegrableOn f' (Set.Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp hi'
  have hfIoo : Integrable f (volume.restrict (Set.Ioo a b)) :=
    hfIcc.mono_set Set.Ioo_subset_Icc_self
  have hIoo_zero : (∫ y in Set.Ioo a b, f y) = 0 := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
    exact hmean
  have hconst_int : Integrable (fun _ : ℝ => f x) (volume.restrict (Set.Ioo a b)) :=
    MeasureTheory.integrableOn_const (s := Set.Ioo a b) (μ := volume) (C := f x)
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hsplit : (∫ y in Set.Ioo a b, (f x - f y))
      = (∫ y in Set.Ioo a b, f x) - ∫ y in Set.Ioo a b, f y :=
    integral_sub hconst_int hfIoo
  have hcval : (∫ y in Set.Ioo a b, f x) = volume.real (Set.Ioo a b) * f x := by
    rw [setIntegral_const, smul_eq_mul]
  have hpos : 0 < b - a := sub_pos.mpr hab
  have hkey : (b - a) * f x = ∫ y in Set.Ioo a b, (f x - f y) := by
    rw [hsplit, hcval, hIoo_zero, sub_zero, Real.volume_real_Ioo_of_le hab.le]
  have habs_g' : IntegrableOn (fun t => |f' t|) (Set.Icc a b) volume := hf'Icc.abs
  have hint0 : IntervalIntegrable (fun t => |f' t|) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mpr
      (habs_g'.mono_set Set.Ioc_subset_Icc_self)
  have hpt : ∀ y ∈ Set.Ioo a b, |f x - f y| ≤ K := by
    intro y hy
    rcases le_total y x with hyx | hxy
    · have hsub : f x - f y = ∫ t in y..x, f' t := sub_eq_intervalIntegral_Ioo hd hf'Icc hy hx
      have habs : |∫ t in y..x, f' t| ≤ ∫ t in y..x, |f' t| :=
        intervalIntegral.abs_integral_le_integral_abs (f := fun t => f' t) hyx
      have hmono : (∫ t in y..x, |f' t|) ≤ K := by
        rw [hK]
        exact intervalIntegral.integral_mono_interval hy.1.le hyx hx.2.le
          (Filter.Eventually.of_forall (fun t => abs_nonneg (f' t))) hint0
      calc |f x - f y| = |∫ t in y..x, f' t| := by rw [hsub]
        _ ≤ ∫ t in y..x, |f' t| := habs
        _ ≤ K := hmono
    · have hsub : f y - f x = ∫ t in x..y, f' t := sub_eq_intervalIntegral_Ioo hd hf'Icc hx hy
      have habs : |∫ t in x..y, f' t| ≤ ∫ t in x..y, |f' t| :=
        intervalIntegral.abs_integral_le_integral_abs (f := fun t => f' t) hxy
      have hmono : (∫ t in x..y, |f' t|) ≤ K := by
        rw [hK]
        exact intervalIntegral.integral_mono_interval hx.1.le hxy hy.2.le
          (Filter.Eventually.of_forall (fun t => abs_nonneg (f' t))) hint0
      calc |f x - f y| = |f y - f x| := abs_sub_comm _ _
        _ = |∫ t in x..y, f' t| := by rw [hsub]
        _ ≤ ∫ t in x..y, |f' t| := habs
        _ ≤ K := hmono
  have hae : ∀ᵐ y ∂(volume.restrict (Set.Ioo a b)), |f x - f y| ≤ K :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
      (Filter.Eventually.of_forall (fun y hy => hpt y hy))
  have hgcont : ContinuousOn (fun y => f y) (Set.Ioo a b) :=
    fun y hy => (hd y hy).continuousAt.continuousWithinAt
  have hAESM : AEStronglyMeasurable (fun y => |f x - f y|)
      (volume.restrict (Set.Ioo a b)) :=
    ((continuousOn_const.sub hgcont).abs).aestronglyMeasurable measurableSet_Ioo
  have hInt : Integrable (fun _ : ℝ => K) (volume.restrict (Set.Ioo a b)) :=
    MeasureTheory.integrableOn_const (s := Set.Ioo a b) (μ := volume) (C := K)
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hbd : ∀ᵐ y ∂(volume.restrict (Set.Ioo a b)), ‖|f x - f y|‖ ≤ K :=
    hae.mono (fun y hy => by rw [Real.norm_eq_abs, abs_abs]; exact hy)
  have hIntf : Integrable (fun y => |f x - f y|) (volume.restrict (Set.Ioo a b)) :=
    Integrable.mono' hInt hAESM hbd
  have hintegrable := MeasureTheory.integral_mono_ae hIntf hInt hae
  have hval : (∫ y in Set.Ioo a b, K) = volume.real (Set.Ioo a b) * K := by
    rw [setIntegral_const, smul_eq_mul]
  have hfin : (∫ y in Set.Ioo a b, |f x - f y|) ≤ (b - a) * K := by
    rw [hval, Real.volume_real_Ioo_of_le hab.le] at hintegrable
    linarith
  have hnorm : |∫ y in Set.Ioo a b, (f x - f y)| ≤ ∫ y in Set.Ioo a b, |f x - f y| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioo a b)) (fun y : ℝ => f x - f y))
  have hLabs : (b - a) * |f x| = |(b - a) * f x| := by
    rw [abs_mul, abs_of_pos hpos]
  have hchain : (b - a) * |f x| ≤ (b - a) * K := by
    rw [hLabs, hkey]
    exact hnorm.trans hfin
  have hfin2 : |f x| ≤ K := le_of_mul_le_mul_left hchain hpos
  have hgoal : |f x| ≤ ∫ t in a..b, |f' t| := by
    rw [← hK]
    exact hfin2
  exact hgoal



end Work.FTS.EllipticEst.Honest.PthCore
end
-- ===== merged: Submission.Work.FTS.EllipticEst.I4BV.i4_rate_alt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.I4BV

set_option autoImplicit false

theorem i4_rate_alt (F : ℝ → ℝ)
    (hF : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt F (deriv F x) x)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv F θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Ioo 0 (Real.pi / 2))) :
    ∃ L : ℝ,
      Filter.Tendsto F (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L) ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (F θ - L) ^ 2 ≤ 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ)
          * ∫ x in Set.Ioo θ (Real.pi / 2),
              (deriv F x / Real.cos x) ^ 2 * (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)) := by
  let I : Set ℝ := Set.Ioo 0 (Real.pi / 2)
  let A : ℝ → ℝ := fun θ => (deriv F θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
  let B : ℝ → ℝ := fun θ => (Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ)
  have hAnn : ∀ θ ∈ I, 0 ≤ A θ := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := hθ
    have hs : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ'.1])
      (by linarith [hθ'.2, Real.pi_pos])
    show 0 ≤ (deriv F θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
  have hBnn : ∀ θ ∈ I, 0 ≤ B θ := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := hθ
    have hs : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ'.1])
      (by linarith [hθ'.2, Real.pi_pos])
    show 0 ≤ (Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ)
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
  have hAint : MeasureTheory.IntegrableOn A I := by
    show MeasureTheory.IntegrableOn (fun θ => (deriv F θ / Real.cos θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) (Set.Ioo 0 (Real.pi / 2))
    exact hint
  have hBcont : Continuous B := by
    show Continuous (fun θ => (Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ))
    exact (Real.continuous_cos.pow 2).mul
      ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 99 / 100)).comp
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)))
  have hBint : MeasureTheory.IntegrableOn B I := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ hBcont.aestronglyMeasurable
      (2 ^ (99 / 100 : ℝ) * (Real.pi / 2) ^ (2 + 99 / 100 : ℝ)) ?_
    · show MeasureTheory.volume I < ⊤
      rw [show I = Set.Ioo 0 (Real.pi / 2) from rfl, Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have h1 := cos_sq_mul_sin2_rpow_le hθ
      have h2 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
      have h3 : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith [hθ.1]
      have h4 : (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) ≤ (Real.pi / 2) ^ (2 + 99 / 100 : ℝ) :=
        Real.rpow_le_rpow h2 h3 (by norm_num)
      have h5 : 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ)
          ≤ 2 ^ (99 / 100 : ℝ) * (Real.pi / 2) ^ (2 + 99 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      have hBnn' : 0 ≤ (Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _)
      show ‖B θ‖ ≤ 2 ^ (99 / 100 : ℝ) * (Real.pi / 2) ^ (2 + 99 / 100 : ℝ)
      rw [Real.norm_eq_abs]
      show |(Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ)| ≤ _
      rw [abs_of_nonneg hBnn']
      linarith [h1, h5]
  have hAB : ∀ θ ∈ I, A θ * B θ = (deriv F θ) ^ 2 := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := hθ
    have hc : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ'.1, Real.pi_pos], hθ'.2⟩)
    have hs : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ'.1])
      (by linarith [hθ'.2, Real.pi_pos])
    show ((deriv F θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        * ((Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ)) = (deriv F θ) ^ 2
    have hσ : (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
        * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ) = 1 := by
      rw [← Real.rpow_add hs, neg_add_cancel, Real.rpow_zero]
    rw [show ((deriv F θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        * ((Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ))
        = ((deriv F θ) ^ 2 / (Real.cos θ) ^ 2 * (Real.cos θ) ^ 2)
          * ((Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
            * (Real.sin (2 * θ)) ^ (99 / 100 : ℝ)) by ring]
    rw [hσ, mul_one, div_mul_cancel₀ _ (pow_ne_zero 2 hc)]
  have hpt : ∀ θ ∈ I, |deriv F θ| ≤ (A θ + B θ) / 2 := by
    intro θ hθ
    have hAn : 0 ≤ A θ := hAnn θ hθ
    have hBn : 0 ≤ B θ := hBnn θ hθ
    have hAM : Real.sqrt (A θ * B θ) ≤ (A θ + B θ) / 2 := by
      have h1 : Real.sqrt (A θ * B θ) ^ 2 ≤ ((A θ + B θ) / 2) ^ 2 := by
        rw [Real.sq_sqrt (mul_nonneg hAn hBn)]
        nlinarith [sq_nonneg (A θ - B θ)]
      have h2 : 0 ≤ (A θ + B θ) / 2 := by linarith
      nlinarith [h1, Real.sqrt_nonneg (A θ * B θ), h2]
    have habs : |deriv F θ| = Real.sqrt (A θ * B θ) := by
      rw [hAB θ hθ, Real.sqrt_sq_eq_abs]
    rw [habs]
    exact hAM
  have hF'int : MeasureTheory.IntegrableOn (deriv F) I := by
    have hsum : MeasureTheory.IntegrableOn (fun θ => (A θ + B θ) / 2) I :=
      (hAint.add hBint).div_const 2
    refine MeasureTheory.Integrable.mono' hsum (measurable_deriv F).aestronglyMeasurable ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs]
    exact hpt θ hθ
  obtain ⟨L, hL⟩ : ∃ L : ℝ,
      Filter.Tendsto F (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L) := by
    refine exists_tendsto_nhdsLT_of_integrableOn_deriv (f' := deriv F)
      (b := Real.pi / 2) (δ := Real.pi / 2) (by linarith [Real.pi_pos]) ?_ ?_
    · intro x hx
      rw [show Real.pi / 2 - Real.pi / 2 = 0 by ring] at hx
      exact hF x hx
    · show MeasureTheory.IntegrableOn (deriv F) (Set.Ioo (Real.pi / 2 - Real.pi / 2) (Real.pi / 2))
      rw [show Real.pi / 2 - Real.pi / 2 = 0 by ring]
      exact hF'int
  refine ⟨L, hL, ?_⟩
  intro θ hθ
  have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) := hθ
  have hu : 0 < Real.pi / 2 - θ := sub_pos.mpr hθI.2
  have hsub2 : Set.Ioo θ (Real.pi / 2) ⊆ I := fun x hx => ⟨lt_trans hθI.1 hx.1, hx.2⟩
  have hstep : ∀ θ' ∈ Set.Ioo θ (Real.pi / 2),
      (F θ - F θ') ^ 2 ≤ 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ)
        * ∫ x in Set.Ioo θ (Real.pi / 2), A x := by
    intro θ' hθ'
    have hsub : Set.Ioo θ θ' ⊆ I := fun x hx => ⟨lt_trans hθI.1 hx.1, lt_trans hx.2 hθ'.2⟩
    have hFT : ∫ x in Set.Ioo θ θ', deriv F x = F θ' - F θ := by
      have hm : ∫ x in Set.Ioo θ θ', deriv F x = ∫ x in Set.Ioc θ θ', deriv F x :=
        MeasureTheory.setIntegral_congr_set (μ := volume)
          (MeasureTheory.Ioo_ae_eq_Ioc (a := θ) (b := θ'))
      rw [hm, ← intervalIntegral.integral_of_le hθ'.1.le]
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => ?_) ?_
      · rw [Set.uIcc_of_le hθ'.1.le] at hy
        exact hF y ⟨lt_of_lt_of_le hθI.1 hy.1, lt_of_le_of_lt hy.2 hθ'.2⟩
      · have hsub3 : Set.uIcc θ θ' ⊆ I := by
          rw [Set.uIcc_of_le hθ'.1.le]
          exact fun x hx => ⟨lt_of_lt_of_le hθI.1 hx.1, lt_of_le_of_lt hx.2 hθ'.2⟩
        exact (hF'int.mono_set hsub3).intervalIntegrable
    have hAii : MeasureTheory.IntegrableOn A (Set.Ioo θ θ') := hAint.mono_set hsub
    have hBii : MeasureTheory.IntegrableOn B (Set.Ioo θ θ') := hBint.mono_set hsub
    have hFii : MeasureTheory.IntegrableOn (deriv F) (Set.Ioo θ θ') := hF'int.mono_set hsub
    have hpt_s : ∀ x ∈ Set.Ioo θ θ', |deriv F x| ≤ Real.sqrt (A x) * Real.sqrt (B x) := by
      intro x hx
      have hxI : x ∈ I := hsub hx
      have h1 : |deriv F x| = Real.sqrt (A x * B x) := by
        rw [hAB x hxI, Real.sqrt_sq_eq_abs]
      rw [h1, Real.sqrt_mul (hAnn x hxI) (B x)]
    have hcs := Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt hAii hBii hFii
      (fun x hx => hAnn x (hsub hx)) (fun x hx => hBnn x (hsub hx)) hpt_s
    have hAnnInt : 0 ≤ ∫ x in Set.Ioo θ θ', A x :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun x hx => hAnn x (hsub hx))
    have hBnnInt : 0 ≤ ∫ x in Set.Ioo θ θ', B x :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun x hx => hBnn x (hsub hx))
    have hAnnInt2 : 0 ≤ ∫ x in Set.Ioo θ (Real.pi / 2), A x :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun x hx => hAnn x (hsub2 hx))
    have hsq : (F θ - F θ') ^ 2 ≤ (∫ x in Set.Ioo θ θ', A x) * (∫ x in Set.Ioo θ θ', B x) := by
      have heq : (F θ - F θ') ^ 2 = |∫ x in Set.Ioo θ θ', deriv F x| ^ 2 := by
        rw [hFT, sq_abs]; ring
      rw [heq]
      calc |∫ x in Set.Ioo θ θ', deriv F x| ^ 2
          ≤ (Real.sqrt (∫ x in Set.Ioo θ θ', A x) * Real.sqrt (∫ x in Set.Ioo θ θ', B x)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hcs 2
        _ = (∫ x in Set.Ioo θ θ', A x) * (∫ x in Set.Ioo θ θ', B x) := by
            rw [mul_pow, Real.sq_sqrt hAnnInt, Real.sq_sqrt hBnnInt]
    have hAle : ∫ x in Set.Ioo θ θ', A x ≤ ∫ x in Set.Ioo θ (Real.pi / 2), A x :=
      MeasureTheory.setIntegral_mono_set (hAint.mono_set hsub2)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => hAnn x (hsub2 hx)))
        (Filter.Eventually.of_forall (fun x hx => ⟨hx.1, lt_trans hx.2 hθ'.2⟩))
    have hBle : ∫ x in Set.Ioo θ θ', B x
        ≤ 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) * (θ' - θ) := by
      have hconst_int : MeasureTheory.IntegrableOn
          (fun _ : ℝ => 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ))
          (Set.Ioo θ θ') :=
        MeasureTheory.integrableOn_const
          (C := 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ))
          (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      have h1 : ∫ x in Set.Ioo θ θ', B x ≤ ∫ x in Set.Ioo θ θ',
          (fun _ : ℝ => 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ)) x := by
        refine MeasureTheory.setIntegral_mono_on hBii hconst_int measurableSet_Ioo (fun x hx => ?_)
        have hxI : x ∈ I := hsub hx
        have hb1 := cos_sq_mul_sin2_rpow_le hxI
        have hb2 : Real.pi / 2 - x ≤ Real.pi / 2 - θ := by linarith [hx.1]
        have hb3 : 0 ≤ Real.pi / 2 - x := by linarith [hx.2, hθ'.2]
        have hb4 : (Real.pi / 2 - x) ^ (2 + 99 / 100 : ℝ)
            ≤ (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) :=
          Real.rpow_le_rpow hb3 hb2 (by norm_num)
        have hb5 : 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - x) ^ (2 + 99 / 100 : ℝ)
            ≤ 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) :=
          mul_le_mul_of_nonneg_left hb4 (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (99 / 100 : ℝ))
        show (Real.cos x) ^ 2 * (Real.sin (2 * x)) ^ (99 / 100 : ℝ)
          ≤ 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ)
        exact le_trans hb1 hb5
      have h2 : ∫ x in Set.Ioo θ θ',
            (fun _ : ℝ => 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ)) x
          = 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) * (θ' - θ) := by
        rw [MeasureTheory.setIntegral_const, Measure.real_def, Real.volume_Ioo,
          ENNReal.toReal_ofReal (by linarith [hθ'.1]), smul_eq_mul]
        ring
      rw [h2] at h1
      exact h1
    have hkey : 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) * (θ' - θ)
        ≤ 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ) := by
      have h2' : (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (1 : ℝ)
          = (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ) := by
        rw [← Real.rpow_add hu]
        norm_num
      have h1' : (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) * (θ' - θ)
          ≤ (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
        exact mul_le_mul_of_nonneg_left (by linarith [hθ'.2]) (Real.rpow_nonneg (le_of_lt hu) _)
      rw [h2'] at h1'
      have h3 := mul_le_mul_of_nonneg_left h1'
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (99 / 100 : ℝ))
      linarith [h3]
    calc (F θ - F θ') ^ 2
        ≤ (∫ x in Set.Ioo θ θ', A x) * (∫ x in Set.Ioo θ θ', B x) := hsq
      _ ≤ (∫ x in Set.Ioo θ (Real.pi / 2), A x)
            * (2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (2 + 99 / 100 : ℝ) * (θ' - θ)) :=
          mul_le_mul hAle hBle hBnnInt hAnnInt2
      _ ≤ (∫ x in Set.Ioo θ (Real.pi / 2), A x)
            * (2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ)) :=
          mul_le_mul_of_nonneg_left hkey hAnnInt2
      _ = 2 ^ (99 / 100 : ℝ) * (Real.pi / 2 - θ) ^ (3 + 99 / 100 : ℝ)
            * ∫ x in Set.Ioo θ (Real.pi / 2), A x := by ring
  have hmem : Set.Ioo θ (Real.pi / 2) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT (a := θ) (by linarith [hθI.2])]
    exact self_mem_nhdsWithin
  have htend : Filter.Tendsto (fun θ' => (F θ - F θ') ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds ((F θ - L) ^ 2)) := by
    simpa using ((tendsto_const_nhds.sub hL).pow 2)
  refine le_of_tendsto htend ?_
  filter_upwards [hmem] with θ' hθ'
  exact hstep θ' hθ'

end Work.FTS.EllipticEst.I4BV
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.slice_u_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A one-sided Poincaré inequality on the angular slice `[0, π/2]`

For a function `u` which is `C²` on the *open* interval `(0, π/2)`, continuous on the closed
interval, and vanishes at the left endpoint `0`, we prove

  `∫_{Iθ} u² ≤ (π/2)² · ∫_{Iθ} (u')²`      (`Iθ = [0, π/2]`),

**without** assuming anything at the right endpoint `π/2` (no Dirichlet condition there, and no
smoothness beyond continuity on `[0, π/2]`).  This is the crude Poincaré estimate used to dominate
the `L²` zero-order angular term by the angular energy.

Route:

* for `θ ∈ (0, π/2)` the fundamental theorem of calculus
  (`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`, applicable because `u` is `C²` on the
  open interval and `u'` is integrable there) gives `u θ = ∫_0^θ u'`;
* hence `|u θ| ≤ ∫_0^θ |u'|`, and Cauchy–Schwarz for the interval integral
  (`Work.FTS.H2.DivQ.sqIntervalIntegralLe`) gives
  `(∫_0^θ |u'|)² ≤ θ · ∫_0^θ (u')² ≤ (π/2) · ∫_{Iθ} (u')²`;
* the resulting bound `(u θ)² ≤ (π/2) · ∫_{Iθ} (u')²` holds for every `θ ∈ (0, π/2)` and also at
  `θ = 0` (where `u = 0`), so it holds almost everywhere on `Iθ`; integrating it
  (`MeasureTheory.setIntegral_mono_on_ae`) gives the claim.

The only point of `Iθ` where the pointwise bound is not available directly is the right endpoint
`π/2`, which is a null set: the bound at that point is never needed.
-/

namespace Work.FTS.EllipticEst.Mine

open MeasureTheory Set Filter
open scoped Real Topology

set_option linter.style.haveILetI false

theorem slice_u_sq_le {u : ℝ → ℝ}
    (hC : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (h0 : u 0 = 0)
    (hint : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 2 * (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) := by
  have hpi : 0 < Real.pi / 2 := by positivity
  -- energy abbreviation
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hA
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    exact MeasureTheory.integral_nonneg (fun θ => sq_nonneg (deriv u θ))
  have hM_nonneg : 0 ≤ (Real.pi / 2) * A := mul_nonneg hpi.le hA_nonneg
  -- integrability of `u²` on the slice
  have hu2 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ :=
    (hcont.pow 2).integrableOn_compact isCompact_Icc
  refine ⟨hu2, ?_⟩
  -- smoothness facts
  have hderivCont : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hC.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hDO : DifferentiableOn ℝ u (Set.Ioo 0 (Real.pi / 2)) :=
    hC.differentiableOn (by norm_num)
  -- ## Step 1: the pointwise bound on the open interval
  have hbound : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (u θ) ^ 2 ≤ (Real.pi / 2) * A := by
    intro θ hθ
    have hθle : (0 : ℝ) ≤ θ := le_of_lt hθ.1
    have hθlt : θ < Real.pi / 2 := hθ.2
    have hIcc_sub : Set.Icc 0 θ ⊆ Work.Spaces.Iθ := fun x hx => ⟨hx.1, hx.2.trans hθlt.le⟩
    have hIoo_sub : Set.Ioo 0 θ ⊆ Set.Ioo 0 (Real.pi / 2) := fun x hx => ⟨hx.1, hx.2.trans hθlt⟩
    have hIoc_sub : Set.Ioc 0 θ ⊆ Work.Spaces.Iθ := fun x hx =>
      ⟨le_of_lt hx.1, hx.2.trans hθlt.le⟩
    have hcont_sub : ContinuousOn u (Set.Icc 0 θ) := hcont.mono hIcc_sub
    have hderiv : ∀ x ∈ Set.Ioo 0 θ, HasDerivAt u (deriv u x) x := fun x hx =>
      hDO.hasDerivAt (isOpen_Ioo.mem_nhds (hIoo_sub hx))
    -- integrability of `(u')²` and of `u'` on `(0, θ]`
    have hg2Ioc : MeasureTheory.IntegrableOn (fun x => (deriv u x) ^ 2) (Set.Ioc 0 θ) :=
      hint.mono_set hIoc_sub
    have hII : IntervalIntegrable (deriv u) volume 0 θ := by
      have hAESM : AEStronglyMeasurable (deriv u) (volume.restrict (Set.Ioc 0 θ)) := by
        have h1 : AEStronglyMeasurable (deriv u) (volume.restrict (Set.Ioo 0 θ)) :=
          (hderivCont.mono hIoo_sub).aestronglyMeasurable measurableSet_Ioo
        rwa [MeasureTheory.restrict_Ioo_eq_restrict_Ioc] at h1
      haveI : IsFiniteMeasure (volume.restrict (Set.Ioc 0 θ)) :=
        ⟨by
          rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]
          exact ENNReal.ofReal_lt_top⟩
      have hmem : MemLp (deriv u) 2 (volume.restrict (Set.Ioc 0 θ)) :=
        (MeasureTheory.memLp_two_iff_integrable_sq hAESM).mpr hg2Ioc
      have hmem1 : MemLp (deriv u) 1 (volume.restrict (Set.Ioc 0 θ)) :=
        hmem.mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hθle).mpr
        (MeasureTheory.memLp_one_iff_integrable.mp hmem1)
    -- the fundamental theorem of calculus
    have hftc : u θ = ∫ x in (0 : ℝ)..θ, deriv u x := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        (f := u) (f' := deriv u) (a := 0) (b := θ) hθle hcont_sub hderiv hII
      rw [h0, sub_zero] at h
      exact h.symm
    have habs : |u θ| ≤ ∫ x in (0 : ℝ)..θ, |deriv u x| := by
      calc |u θ| = |∫ x in (0 : ℝ)..θ, deriv u x| := by rw [hftc]
        _ ≤ ∫ x in (0 : ℝ)..θ, |deriv u x| :=
            intervalIntegral.abs_integral_le_integral_abs (f := deriv u) (a := 0) (b := θ) hθle
    -- Cauchy–Schwarz for the interval integral
    have hCS : (∫ x in (0 : ℝ)..θ, |deriv u x|) ^ 2
        ≤ θ * (∫ x in (0 : ℝ)..θ, (deriv u x) ^ 2) := by
      have hf : IntervalIntegrable (fun x => |deriv u x|) volume 0 θ := hII.abs
      have hf2 : IntervalIntegrable (fun x => |deriv u x| ^ 2) volume 0 θ := by
        refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hθle).mpr ?_
        exact hg2Ioc.congr_fun (fun x _ => (sq_abs (deriv u x)).symm) measurableSet_Ioc
      have h := Work.FTS.H2.DivQ.sqIntervalIntegralLe (fun x => |deriv u x|) hθle hf hf2
      rw [sub_zero] at h
      have hconv : (∫ x in (0 : ℝ)..θ, |deriv u x| ^ 2)
          = ∫ x in (0 : ℝ)..θ, (deriv u x) ^ 2 :=
        intervalIntegral.integral_congr (fun x _ => sq_abs (deriv u x))
      rwa [hconv] at h
    -- comparison with the full slice energy
    have hBA : (∫ x in (0 : ℝ)..θ, (deriv u x) ^ 2) ≤ A := by
      rw [hA, intervalIntegral.integral_of_le (f := fun x => (deriv u x) ^ 2) hθle]
      refine MeasureTheory.setIntegral_mono_set (f := fun x => (deriv u x) ^ 2) hint ?_ ?_
      · filter_upwards with x
        exact sq_nonneg _
      · filter_upwards with x hx
        exact hIoc_sub hx
    have hBnn : 0 ≤ ∫ x in (0 : ℝ)..θ, (deriv u x) ^ 2 :=
      intervalIntegral.integral_nonneg (f := fun x => (deriv u x) ^ 2) hθle
        (fun _ _ => sq_nonneg _)
    calc (u θ) ^ 2 = (|u θ|) ^ 2 := (sq_abs (u θ)).symm
      _ ≤ (∫ x in (0 : ℝ)..θ, |deriv u x|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg (u θ)) habs 2
      _ ≤ θ * (∫ x in (0 : ℝ)..θ, (deriv u x) ^ 2) := hCS
      _ ≤ (Real.pi / 2) * A := mul_le_mul hθlt.le hBA hBnn hpi.le
  -- ## Step 2: the bound holds almost everywhere on `Iθ` (the bad point `π/2` is null)
  have hpoint : ∀ θ ∈ Work.Spaces.Iθ, θ ≠ Real.pi / 2 → (u θ) ^ 2 ≤ (Real.pi / 2) * A := by
    intro θ hθ hne
    rcases eq_or_lt_of_le hθ.1 with h | h
    · rw [← h, h0]
      simpa using hM_nonneg
    · exact hbound θ ⟨h, lt_of_le_of_ne hθ.2 hne⟩
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ),
      θ ∈ Work.Spaces.Iθ → (u θ) ^ 2 ≤ (Real.pi / 2) * A := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (Real.pi / 2))
    intro θ hθ
    simp only [Set.mem_ofPred_eq, not_imp] at hθ
    by_contra hne
    exact hθ.2 (hpoint θ hθ.1 hne)
  -- ## Step 3: integrate the a.e. bound
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (Real.pi / 2) * A) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (C := (Real.pi / 2) * A) (by
      rw [Work.Spaces.Iθ, Real.volume_Icc, sub_zero]
      exact ENNReal.ofReal_lt_top.ne)
  have hmono := MeasureTheory.setIntegral_mono_on_ae hu2 hconst measurableSet_Icc hae
  refine hmono.trans_eq ?_
  rw [MeasureTheory.setIntegral_const]
  have hvol : (volume : Measure ℝ).real Work.Spaces.Iθ = Real.pi / 2 := by
    rw [Work.Spaces.Iθ, MeasureTheory.measureReal_def, Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hvol, smul_eq_mul]
  ring

end Work.FTS.EllipticEst.Mine
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.zIbpTwoD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false

/-- **Fubini for the domain `Iz ×ˢ Iθ`, `θ`-outer**: the two-dimensional integral over
`Iz ×ˢ Iθ` equals the iterated integral with the `z`-integration innermost. -/
theorem setIntegral_prod_swap_IzIθ (F : ℝ × ℝ → ℝ)
    (hF : MeasureTheory.IntegrableOn F (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, F p)
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, F (z, θ) := by
  have h1 : (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, F p)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F (z, θ) :=
    MeasureTheory.setIntegral_prod F hF
  rw [h1]
  have hInt : MeasureTheory.Integrable (Function.uncurry (fun z θ : ℝ => F (z, θ)))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hF
  exact MeasureTheory.integral_integral_swap hInt

/-- Integrability on `Iz ×ˢ Iθ` gives integrability of almost every `θ`-slice on `Ioi 0`
(note that a.e. `θ` lies in `Iθ`, and that `Ioi 0 ⊆ Iz`; the point `z = 0` is irrelevant). -/
theorem ae_integrableOn_slice_Ioi_of_integrableOn_prod {F : ℝ × ℝ → ℝ}
    (hF : MeasureTheory.IntegrableOn F (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => F (z, θ)) (Set.Ioi 0) := by
  have hF' : MeasureTheory.Integrable F
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hF
  filter_upwards [MeasureTheory.Integrable.prod_left_ae hF'] with θ hθ
  exact MeasureTheory.IntegrableOn.mono_set hθ (fun x hx => by
    simp only [Work.Spaces.Iz, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    exact le_of_lt hx)

theorem zIbpTwoD {φ ψ : ℝ → ℝ → ℝ}
    (hint1 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * φ p.1 p.2
      * (p.1 * deriv (fun z' => ψ z' p.2) p.1)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (-(p.1 * deriv (fun z' => φ z' p.2) p.1) - ((p.1 - 3) / (1 + p.1)) * φ p.1 p.2)
      * ψ p.1 p.2) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hφ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ContDiffOn ℝ 1 (fun z => φ z θ) (Set.Ioi 0))
    (hψ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ContDiffOn ℝ 1 (fun z => ψ z θ) (Set.Ioi 0))
    (hf0 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), Filter.Tendsto
      (fun z => z * (Work.Spaces.w z) ^ 2 * φ z θ * ψ z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hf1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), Filter.Tendsto
      (fun z => z * (Work.Spaces.w z) ^ 2 * φ z θ * ψ z θ) Filter.atTop (nhds 0)) :
    (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2 * φ p.1 p.2
        * (p.1 * deriv (fun z' => ψ z' p.2) p.1))
      = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
          * (-(p.1 * deriv (fun z' => φ z' p.2) p.1) - ((p.1 - 3) / (1 + p.1)) * φ p.1 p.2)
          * ψ p.1 p.2 := by
  -- both sides become `θ`-outer iterated integrals
  have hL := setIntegral_prod_swap_IzIθ _ hint1
  have hR := setIntegral_prod_swap_IzIθ _ hint2
  rw [hL, hR]
  refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
  -- move all the almost-everywhere-in-`θ` hypotheses to the ambient measure
  have hφ' := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Icc).mp hφ
  have hψ' := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Icc).mp hψ
  have hf0' := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Icc).mp hf0
  have hf1' := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Icc).mp hf1
  have hs1' := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Icc).mp
    (ae_integrableOn_slice_Ioi_of_integrableOn_prod hint1)
  have hs2' := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Icc).mp
    (ae_integrableOn_slice_Ioi_of_integrableOn_prod hint2)
  filter_upwards [hφ', hψ', hf0', hf1', hs1', hs2'] with θ a b c d e f hmem
  -- the one-dimensional radial integration by parts on the slice at `θ`
  have h := radialIbpWild (a hmem) (b hmem) (e hmem) (f hmem) (c hmem) (d hmem)
  calc
    (∫ z in Work.Spaces.Iz, (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * φ p.1 p.2
        * (p.1 * deriv (fun z' => ψ z' p.2) p.1)) (z, θ))
        = ∫ z in Set.Ioi 0, (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * φ p.1 p.2
            * (p.1 * deriv (fun z' => ψ z' p.2) p.1)) (z, θ) :=
          (MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0:ℝ)))).symm
    _ = ∫ z in Set.Ioi 0, (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
          * (-(p.1 * deriv (fun z' => φ z' p.2) p.1) - ((p.1 - 3) / (1 + p.1)) * φ p.1 p.2)
          * ψ p.1 p.2) (z, θ) := h
    _ = ∫ z in Work.Spaces.Iz, (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
          * (-(p.1 * deriv (fun z' => φ z' p.2) p.1) - ((p.1 - 3) / (1 + p.1)) * φ p.1 p.2)
          * ψ p.1 p.2) (z, θ) :=
          MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0:ℝ)))

end Work.FTS.EllipticEst.Prop
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TanTheta.psi_bounds_sc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TanTheta

private lemma pi_half_pos : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]




end Work.FTS.EllipticEst.TanTheta
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.hasDerivAt_self_antideriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- `π` is the notation for `Real.pi`; it is a *scoped* notation (`open scoped Real`).
open scoped Real

namespace Work.FTS.EllipticEst

/-- **Pointwise antiderivative identity for the self-pairing of `L₀`.**  For `f : ℝ → ℝ` which is
`C²` at `θ ∈ (0, π/2)`, the function `F(θ) = -f'(θ)·f(θ) + (1/2)·tan θ·f(θ)²` has derivative
`L₀(f)(θ)·f(θ) - f'(θ)² - (1/2)(f(θ)/cos θ)² + 6f(θ)²`, where `L₀` is `Work.Elliptic.Lzero`
applied to the `θ`-slice `fun _ θ' => f θ'` (so `L₀(f)(θ) = -f''(θ) + (tan θ · f(θ))' - 6f(θ)`).
The hypothesis `θ ∈ (0, π/2)` is what makes `tan` differentiable at `θ`. -/
theorem hasDerivAt_self_antideriv (f : ℝ → ℝ) (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (h2 : ContDiffAt ℝ 2 f θ) :
    HasDerivAt (fun s => -(deriv f s) * f s + (1 / 2) * Real.tan s * (f s) ^ 2)
      (Work.Elliptic.Lzero (fun _ s => f s) 0 θ * f θ
        - (deriv f θ) ^ 2 - (1 / 2) * (f θ / Real.cos θ) ^ 2 + 6 * (f θ) ^ 2) θ := by
  -- `cos θ ≠ 0` on `(0, π/2)`, so that `tan` is differentiable at `θ`.
  have hcos : Real.cos θ ≠ 0 := by
    refine ne_of_gt (Real.cos_pos_of_mem_Ioo (x := θ) ⟨?_, hθ.2⟩)
    linarith [hθ.1, Real.pi_pos]
  -- first and second derivative of `f` at `θ`, from `C²`-regularity.
  have h1 : HasDerivAt f (deriv f θ) θ := (h2.hasStrictDerivAt (by norm_num)).hasDerivAt
  have h2' : HasDerivAt (deriv f) (deriv (deriv f) θ) θ :=
    ((h2.derivWithin (m := 1) (by norm_num)).hasStrictDerivAt (by norm_num)).hasDerivAt
  have htan : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := Real.hasDerivAt_tan hcos
  -- unfold `L₀` on the `θ`-slice `fun _ s => f s`.
  have hL : Work.Elliptic.Lzero (fun _ s => f s) 0 θ
      = -(deriv (deriv f) θ) + deriv (fun s => Real.tan s * f s) θ - 6 * f θ := by
    simp only [Work.Elliptic.Lzero, Work.Spaces.pth, Work.Spaces.pthIter]
  rw [hL]
  have htanf : deriv (fun s => Real.tan s * f s) θ
      = (1 / Real.cos θ ^ 2) * f θ + Real.tan θ * deriv f θ := (htan.mul h1).deriv
  rw [htanf]
  -- the derivative of `F`, computed with the product rule.
  have hderiv : HasDerivAt (fun s => -(deriv f s) * f s + (1 / 2) * Real.tan s * (f s) ^ 2)
      (-(deriv (deriv f) θ * f θ + deriv f θ * deriv f θ)
        + (1 / 2) * ((1 / Real.cos θ ^ 2) * (f θ) ^ 2
            + Real.tan θ * (2 * (f θ) * deriv f θ))) θ := by
    have hsq : HasDerivAt (fun s => (f s) ^ 2) (2 * (f θ) * deriv f θ) θ := by
      convert h1.pow 2 using 1; ring_nf
    have hA : HasDerivAt (fun s => -(deriv f s) * f s)
        (-(deriv (deriv f) θ * f θ + deriv f θ * deriv f θ)) θ := by
      convert (h2'.mul h1).neg using 1;
        (funext s; simp only [Pi.neg_apply, Pi.mul_apply]; ring_nf)
    have hB : HasDerivAt (fun s => (1 / 2) * Real.tan s * (f s) ^ 2)
        ((1 / 2) * ((1 / Real.cos θ ^ 2) * (f θ) ^ 2
            + Real.tan θ * (2 * (f θ) * deriv f θ))) θ := by
      convert (htan.mul hsq).const_mul (1 / 2) using 1;
        (funext s; simp only [Pi.mul_apply]; ring_nf)
    exact hA.add hB
  exact hderiv.congr_deriv (by ring_nf)

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.HardyFin.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Finite-order calculus on `(0,x₁]`

This file redevelops the elementary calculus API of `Submission/Work/FTS/H2/DivQ/vanishAux.lean`
and the first two results of the `DivQ` Hardy-development (`primIntegrable`, `primitiveDerivData`)
with a **finite** smoothness hypothesis `ContDiffOn ℝ (N : ℕ∞ω) f (Ioc 0 x₁)` instead of the
`C^∞` hypothesis `ContDiffOn ℝ ⊤ f (Ioc 0 x₁)` used there.

All statements are of the form "for `j ≤ N`", so that they can be instantiated at `N = k + 2`
in the finite-order Hardy division `Work.FTS.EllipticEst.remov.hardyDiv_fin`.
-/

namespace Work.FTS.EllipticEst.remov.HardyFin

open MeasureTheory Filter Set
open scoped Topology

/-- For `f` of class `C^N` on the open interval `(0,x₁)` and `j ≤ N`, the `j`-th iterated
derivative `iteratedDeriv j f` is continuous on `(0,x₁)`.  (This is the version that applies to
`f/y`, which is only smooth on the open interval.) -/
lemma continuousOn_iteratedDeriv_Ioo_fin' {f : ℝ → ℝ} {x₁ : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioo 0 x₁)) {j : ℕ} (hj : j ≤ N) :
    ContinuousOn (iteratedDeriv j f) (Set.Ioo 0 x₁) := by
  have hs : UniqueDiffOn ℝ (Set.Ioo (0 : ℝ) x₁) := isOpen_Ioo.uniqueDiffOn
  have h1 : ContinuousOn (iteratedDerivWithin j f (Set.Ioo 0 x₁)) (Set.Ioo 0 x₁) :=
    hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) hs
  refine h1.congr fun x hx => ?_
  exact (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm

/-- For `f` of class `C^N` on the half-open interval `(0,x₁]` and `j ≤ N`, the `j`-th iterated
derivative `iteratedDeriv j f` is continuous on the open interval `(0,x₁)`. -/
lemma continuousOn_iteratedDeriv_Ioo_fin {f : ℝ → ℝ} {x₁ : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁)) {j : ℕ} (hj : j ≤ N) :
    ContinuousOn (iteratedDeriv j f) (Set.Ioo 0 x₁) :=
  continuousOn_iteratedDeriv_Ioo_fin' (hf.mono Set.Ioo_subset_Ioc_self) hj

/-- For `f` of class `C^N` on the open interval `(0,x₁)` and `j < N`, the `j`-th iterated
derivative is differentiable there. -/
lemma differentiableOn_iteratedDeriv_Ioo_fin' {f : ℝ → ℝ} {x₁ : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioo 0 x₁)) {j : ℕ} (hj : j < N) :
    DifferentiableOn ℝ (iteratedDeriv j f) (Set.Ioo 0 x₁) := by
  have hs : UniqueDiffOn ℝ (Set.Ioo (0 : ℝ) x₁) := isOpen_Ioo.uniqueDiffOn
  have h1 : DifferentiableOn ℝ (iteratedDerivWithin j f (Set.Ioo 0 x₁)) (Set.Ioo 0 x₁) :=
    hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hj) hs
  refine h1.congr fun x hx => ?_
  exact (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm

/-- For `f` of class `C^N` on `(0,x₁]` and `j < N`, the `j`-th iterated derivative is
differentiable on the open interval `(0,x₁)`. -/
lemma differentiableOn_iteratedDeriv_Ioo_fin {f : ℝ → ℝ} {x₁ : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁)) {j : ℕ} (hj : j < N) :
    DifferentiableOn ℝ (iteratedDeriv j f) (Set.Ioo 0 x₁) :=
  differentiableOn_iteratedDeriv_Ioo_fin' (hf.mono Set.Ioo_subset_Ioc_self) hj

/-- At an interior point of `(0,x₁)`, the `j`-th iterated derivative of a `C^N` function
(with `j + 1 ≤ N`) has derivative the `(j+1)`-st iterated derivative. -/
lemma hasDerivAt_iteratedDeriv_Ioo_fin {f : ℝ → ℝ} {x₁ : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁)) {j : ℕ} (hj : j + 1 ≤ N)
    {x : ℝ} (hx : x ∈ Set.Ioo 0 x₁) :
    HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv j f) x :=
    (differentiableOn_iteratedDeriv_Ioo_fin hf (by omega)).differentiableAt
      (Ioo_mem_nhds hx.1 hx.2)
  rw [iteratedDeriv_succ]
  exact hd.hasDerivAt

/-- Continuity of the iterated derivatives on a compact subinterval `[a,b] ⊆ (0,x₁)`. -/
lemma continuousOn_iteratedDeriv_Icc_fin {f : ℝ → ℝ} {x₁ : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁)) {j : ℕ} (hj : j ≤ N)
    {a b : ℝ} (ha : 0 < a) (hb : b < x₁) :
    ContinuousOn (iteratedDeriv j f) (Set.Icc a b) :=
  (continuousOn_iteratedDeriv_Ioo_fin hf hj).mono
    fun _ hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩

/-- **The fundamental theorem of calculus for the iterated derivatives**, on a compact
subinterval `[a,b]` with `0 < a` and `b < x₁`, for `f` of class `C^{j+1}` on `(0,x₁]`:

`∫_a^b f^{(j+1)} = f^{(j)}(b) − f^{(j)}(a)`. -/
theorem intervalIntegral_iteratedDeriv_succ_fin {f : ℝ → ℝ} {x₁ : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁)) {j : ℕ} (hj : j + 1 ≤ N)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < x₁) :
    ∫ s in a..b, iteratedDeriv (j + 1) f s = iteratedDeriv j f b - iteratedDeriv j f a := by
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x :=
    fun x hx =>
      hasDerivAt_iteratedDeriv_Ioo_fin hf hj
        ⟨lt_trans ha hx.1, lt_of_lt_of_le hx.2 (le_of_lt hb)⟩
  have hint : IntervalIntegrable (iteratedDeriv (j + 1) f) volume a b :=
    (continuousOn_iteratedDeriv_Icc_fin hf (by omega) ha hb).intervalIntegrable_of_Icc hab
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (continuousOn_iteratedDeriv_Icc_fin hf (by omega) ha hb) hderiv hint

/-! ## Integrability and the primitive -/

/-- Finite-order version of `Work.FTS.H2.DivQ.primIntegrable`: `s ↦ s^k f^{(k+1)}(s)` is
integrable on `(0,x₁]` as soon as `f` is of class `C^{k+1}` there and the weighted square of
`f^{(k+1)}` is integrable. -/
theorem primIntegrable_fin (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ)
    {N : ℕ} (f : ℝ → ℝ) (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁))
    (hN : k + 1 ≤ N)
    (hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
      (Set.Ioc 0 x₁) := by
  have hcψ : ContinuousOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioo 0 x₁) :=
    (continuousOn_id.pow k).mul (continuousOn_iteratedDeriv_Ioo_fin hf hN)
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (volume.restrict (Set.Ioc 0 x₁)) := by
    have h := hcψ.aestronglyMeasurable (μ := volume) measurableSet_Ioo
    rwa [MeasureTheory.restrict_Ioo_eq_restrict_Ioc] at h
  have h1 : MeasureTheory.Integrable (fun s : ℝ => s ^ γ) (volume.restrict (Set.Ioc 0 x₁)) := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := x₁) (r := γ) hγ
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx₁.le] at h
    exact h
  have h2 : MeasureTheory.Integrable
      (fun s : ℝ => s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2)
      (volume.restrict (Set.Ioc 0 x₁)) := hint
  have hInt : MeasureTheory.Integrable
      (fun s : ℝ => s ^ γ + s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2)
      (volume.restrict (Set.Ioc 0 x₁)) := h1.add h2
  have hbound : ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 x₁)),
      ‖s ^ k * iteratedDeriv (k + 1) f s‖ ≤
        s ^ γ + s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hs0.le k)]
    have hpos : 0 ≤ s ^ k * |iteratedDeriv (k + 1) f s| :=
      mul_nonneg (pow_nonneg hs0.le k) (abs_nonneg _)
    linarith [Work.FTS.H2.DivQ.two_mul_pow_mul_abs_le_amgm k γ s (iteratedDeriv (k + 1) f s) hs0]
  exact MeasureTheory.Integrable.mono' hInt hmeas hbound

/-- Finite-order version of `Work.FTS.H2.DivQ.primitiveDerivData`. -/
theorem primitiveDerivData_fin (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ)
    {N : ℕ} (f : ℝ → ℝ) (hf : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁))
    (hN : k + 1 ≤ N)
    (hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
        (Set.Ioc 0 x₁) ∧
      ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, s ^ k * iteratedDeriv (k + 1) f s)
        (Set.Icc 0 x₁) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) x₁,
        HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, s ^ k * iteratedDeriv (k + 1) f s)
          (t ^ k * iteratedDeriv (k + 1) f t) t) := by
  have hc : ContinuousOn (iteratedDeriv (k + 1) f) (Set.Ioo 0 x₁) :=
    continuousOn_iteratedDeriv_Ioo_fin hf hN
  have hcont : ContinuousOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioo 0 x₁) :=
    (continuousOn_id.pow k).mul hc
  have hIoc : MeasureTheory.IntegrableOn
      (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioc 0 x₁) :=
    primIntegrable_fin k γ x₁ hx₁ hγ f hf hN hint
  have hIcc : MeasureTheory.IntegrableOn
      (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Icc 0 x₁) :=
    hIoc.congr_set_ae (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := 0) (b := x₁)).symm
  refine ⟨hIoc, ?_, ?_⟩
  · have h := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := x₁)
      (μ := volume) (f := fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
      (by rwa [Set.uIcc_of_le hx₁.le])
    simpa [Set.uIcc_of_le hx₁.le] using h
  · intro t ht
    have ht0 : 0 < t := ht.1
    have htx : t < x₁ := ht.2
    have hII : IntervalIntegrable (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
        volume 0 t := by
      refine ⟨hIoc.mono_set (Set.Ioc_subset_Ioc_right htx.le), ?_⟩
      refine MeasureTheory.IntegrableOn.of_measure_zero ?_
      rw [Set.Ioc_eq_empty (not_lt.mpr ht0.le)]
      exact measure_empty
    have hcat : ContinuousAt (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) t :=
      ((continuous_pow k).continuousAt).mul
        (hc.continuousAt (isOpen_Ioo.mem_nhds ⟨ht0, htx⟩))
    have hsl : StronglyMeasurableAtFilter (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
        (nhds t) volume := by
      refine ⟨Set.Ioo (t / 2) ((t + x₁) / 2), ?_, ?_⟩
      · exact IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩
      · refine (hcont.mono ?_).aestronglyMeasurable measurableSet_Ioo
        intro y hy
        exact ⟨by linarith [hy.1, ht0], by linarith [hy.2, htx]⟩
    exact intervalIntegral.integral_hasDerivAt_right hII hsl hcat

end Work.FTS.EllipticEst.remov.HardyFin
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterBddOfPeriodicSmooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SliceTopAux

open scoped Real Topology

/-- The derivative of a function periodic with period `c` is again periodic with period `c`.
(No differentiability hypothesis is needed: at a point where `f` is not differentiable both
`fderiv`s involved vanish by definition.) -/
private lemma periodic_deriv {f : ℝ → ℝ} {c : ℝ} (hp : Function.Periodic f c) :
    Function.Periodic (deriv f) c := by
  intro x
  have h1 : deriv (fun y => f (c + y)) x = deriv f (c + x) := deriv_comp_const_add f c x
  have h2 : (fun y => f (c + y)) = f := by
    funext y
    rw [add_comm, hp y]
  rw [h2] at h1
  rw [show (x + c : ℝ) = c + x from add_comm _ _]
  exact h1.symm

/-- `θ ↦ sin (2θ)` is periodic with period `π`. -/
private lemma periodic_sin_two : Function.Periodic (fun θ : ℝ => Real.sin (2 * θ)) Real.pi := by
  intro x
  have h := Real.sin_periodic (2 * x)
  show Real.sin (2 * (x + Real.pi)) = Real.sin (2 * x)
  rw [show (2 * (x + Real.pi)) = 2 * x + 2 * Real.pi by ring]
  exact h

/-- `Dth1Iter j h` is `C^∞` and `π`-periodic whenever `h` is (the `ContDiff`-`ω`, i.e. analytic,
hypothesis of the theorem implies `C^∞`) and `π`-periodic. -/
private lemma contDiff_periodic_Dth1Iter {h : ℝ → ℝ} (hsm : ContDiff ℝ (⊤ : WithTop ℕ∞) h)
    (hp : Function.Periodic h Real.pi) (j : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Elliptic.Dth1Iter j h)
      ∧ Function.Periodic (Work.Elliptic.Dth1Iter j h) Real.pi := by
  -- `ω` (the analytic notion) implies `∞` (all finite orders).
  have hsm' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h :=
    hsm.of_le (le_top : ((⊤ : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
  induction j with
  | zero => simpa using ⟨hsm', hp⟩
  | succ j ih =>
    obtain ⟨hF, hper⟩ := ih
    -- `deriv` of a `C^∞` function is `C^∞`: `deriv f = fun x => (fderiv ℝ f x) 1`.
    have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ (Work.Elliptic.Dth1Iter j h)) :=
      (contDiff_infty_iff_fderiv.mp hF).2
    have hder : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (Work.Elliptic.Dth1Iter j h)) :=
      hfd.clm_apply (contDiff_const (c := (1 : ℝ)))
    have hsin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ)) :=
      Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
    have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Work.Elliptic.Dth1 (Work.Elliptic.Dth1Iter j h)) :=
      hsin.mul hder
    have hper' : Function.Periodic (Work.Elliptic.Dth1 (Work.Elliptic.Dth1Iter j h)) Real.pi :=
      periodic_sin_two.mul (periodic_deriv hper)
    rw [Work.Elliptic.Dth1Iter_succ]
    exact ⟨hcd, hper'⟩

theorem Dth1IterBddOfPeriodicSmooth {h : ℝ → ℝ} (hsm : ContDiff ℝ (⊤ : WithTop ℕ∞) h)
    (hp : Function.Periodic h Real.pi) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ, |Work.Elliptic.Dth1Iter j h θ| ≤ C := by
  obtain ⟨hcd, hper⟩ := contDiff_periodic_Dth1Iter hsm hp j
  -- a continuous periodic function is bounded
  have hb : Bornology.IsBounded (Set.range (Work.Elliptic.Dth1Iter j h)) :=
    hper.isBounded_of_continuous Real.pi_ne_zero hcd.continuous
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  refine ⟨C, ?_, ?_⟩
  · have h0 := hC _ ⟨0, rfl⟩
    rw [Real.norm_eq_abs] at h0
    exact le_trans (abs_nonneg _) h0
  · intro θ
    have h1 := hC _ ⟨θ, rfl⟩
    rwa [Real.norm_eq_abs] at h1

end Work.FTS.EllipticEst.remov.SliceTopAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterSubEqOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SliceTopAux

noncomputable section

/-- **Smoothness of the iterates at finite order.**  If `f` is `C^k` on the open interval
`(0, π/2)` then its `n`-th `D_θ`-iterate is `C^{k-n}` there, for every `n ≤ k`.

The subtraction of orders is genuine: each application of `D_θ` uses one derivative of the
current iterate (`ContDiffOn.deriv_of_isOpen`) and multiplication by the smooth factor
`sin(2θ)`. -/
private lemma Dth1Iter_contDiffOn (k : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (k : WithTop ℕ∞) f (Set.Ioo 0 (Real.pi / 2))) :
    ∀ n : ℕ, n ≤ k →
      ContDiffOn ℝ ((k - n : ℕ) : WithTop ℕ∞) (Work.Elliptic.Dth1Iter n f)
        (Set.Ioo 0 (Real.pi / 2)) := by
  intro n
  induction n with
  | zero => intro _; simpa using hf
  | succ n ih =>
    intro hn
    have hn' : n ≤ k := le_trans (Nat.le_succ n) hn
    have ih' := ih hn'
    have hle : 1 ≤ k - n := by omega
    -- one derivative is spent: `(k - n - 1) + 1 ≤ k - n`
    have hm : ((k - n - 1 : ℕ) : WithTop ℕ∞) + 1 ≤ ((k - n : ℕ) : WithTop ℕ∞) := by
      have h1 : ((k - n - 1 : ℕ) : WithTop ℕ∞) + 1
          = (((k - n - 1) + 1 : ℕ) : WithTop ℕ∞) := by
        norm_cast
      rw [h1, Nat.sub_add_cancel hle]
    have hd : ContDiffOn ℝ ((k - n - 1 : ℕ) : WithTop ℕ∞)
        (deriv (Work.Elliptic.Dth1Iter n f)) (Set.Ioo 0 (Real.pi / 2)) :=
      ih'.deriv_of_isOpen isOpen_Ioo hm
    have hsin : ContDiffOn ℝ ((k - n - 1 : ℕ) : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ))
        (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
    have hmul := hsin.mul hd
    rw [show k - (n + 1) = k - n - 1 from (Nat.sub_sub k n 1).symm]
    change ContDiffOn ℝ ((k - n - 1 : ℕ) : WithTop ℕ∞)
      (fun x : ℝ => Real.sin (2 * x) * deriv (Work.Elliptic.Dth1Iter n f) x)
      (Set.Ioo 0 (Real.pi / 2))
    exact hmul

theorem Dth1IterSubEqOn (N : ℕ) {u v : ℝ → ℝ}
    (hu : ContDiffOn ℝ (N : WithTop ℕ∞) u (Set.Ioo 0 (Real.pi / 2)))
    (hv : ContDiffOn ℝ (N : WithTop ℕ∞) v (Set.Ioo 0 (Real.pi / 2))) :
    Set.EqOn (Work.Elliptic.Dth1Iter N (fun θ => u θ - v θ))
      (fun θ => Work.Elliptic.Dth1Iter N u θ - Work.Elliptic.Dth1Iter N v θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have key : ∀ n : ℕ, n ≤ N → Set.EqOn (Work.Elliptic.Dth1Iter n (fun θ => u θ - v θ))
      (fun θ => Work.Elliptic.Dth1Iter n u θ - Work.Elliptic.Dth1Iter n v θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    induction n with
    | zero => intro _ θ hθ; simp [Work.Elliptic.Dth1Iter]
    | succ n ih =>
      intro hn θ hθ
      have hnN : n ≤ N := le_trans (Nat.le_succ n) hn
      have hIH := ih hnN
      -- `n < N`, so the `n`-th iterates are differentiable at `θ`
      have hne : ((N - n : ℕ) : WithTop ℕ∞) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]; omega
      have hd_u : DifferentiableAt ℝ (Work.Elliptic.Dth1Iter n u) θ :=
        ((Dth1Iter_contDiffOn N hu n hnN).differentiableOn hne).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hd_v : DifferentiableAt ℝ (Work.Elliptic.Dth1Iter n v) θ :=
        ((Dth1Iter_contDiffOn N hv n hnN).differentiableOn hne).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      -- the induction hypothesis holds on the whole open interval, hence near `θ`
      have heq : Work.Elliptic.Dth1Iter n (fun θ => u θ - v θ) =ᶠ[𝓝 θ]
          (fun θ => Work.Elliptic.Dth1Iter n u θ - Work.Elliptic.Dth1Iter n v θ) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
        exact hIH hy
      calc Work.Elliptic.Dth1Iter (n + 1) (fun θ => u θ - v θ) θ
          = Real.sin (2 * θ)
              * deriv (Work.Elliptic.Dth1Iter n (fun θ => u θ - v θ)) θ := rfl
        _ = Real.sin (2 * θ)
              * deriv (fun θ => Work.Elliptic.Dth1Iter n u θ
                  - Work.Elliptic.Dth1Iter n v θ) θ := by
              rw [heq.deriv_eq]
        _ = Real.sin (2 * θ)
              * (deriv (Work.Elliptic.Dth1Iter n u) θ
                  - deriv (Work.Elliptic.Dth1Iter n v) θ) := by
              rw [show deriv (fun θ : ℝ => Work.Elliptic.Dth1Iter n u θ
                    - Work.Elliptic.Dth1Iter n v θ) θ
                    = deriv (Work.Elliptic.Dth1Iter n u) θ
                      - deriv (Work.Elliptic.Dth1Iter n v) θ
                  from deriv_sub hd_u hd_v]
        _ = Real.sin (2 * θ) * deriv (Work.Elliptic.Dth1Iter n u) θ
              - Real.sin (2 * θ) * deriv (Work.Elliptic.Dth1Iter n v) θ := by rw [mul_sub]
        _ = Work.Elliptic.Dth1Iter (n + 1) u θ
              - Work.Elliptic.Dth1Iter (n + 1) v θ := rfl
  exact key N le_rfl

end

end Work.FTS.EllipticEst.remov.SliceTopAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.hasDerivAt_divSinCos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound


end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.coerc.mul_sq_vanishing_right =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology
set_option maxHeartbeats 800000

namespace Work.FTS.EllipticEst.remov.coerc

theorem mul_sq_vanishing_right {f φ : ℝ → ℝ} {b C d : ℝ} (hC : 0 < C)
    (hφ : ∀ᶠ θ in nhdsWithin b (Set.Iio b), |φ θ| ≤ C * (b - θ))
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2) (Set.Ioo (b - 1) b))
    (hw : Filter.Tendsto (fun θ => φ θ * f θ) (nhdsWithin b (Set.Iio b)) (nhds d)) :
    d = 0 := by
  by_contra hd
  have hdabs : 0 < |d| := abs_pos.mpr hd
  have hε2 : 0 < |d| / 2 := by linarith
  have h2 : ∀ᶠ θ in nhdsWithin b (Set.Iio b), |φ θ * f θ - d| < |d| / 2 := by
    have hh := (Metric.tendsto_nhds.mp hw) (|d| / 2) hε2
    filter_upwards [hh] with θ hθ
    rwa [Real.dist_eq] at hθ
  have h3 : ∀ᶠ θ in nhdsWithin b (Set.Iio b),
      |φ θ| ≤ C * (b - θ) ∧ |φ θ * f θ - d| < |d| / 2 := hφ.and h2
  rw [eventually_nhdsWithin_iff] at h3
  rw [Metric.eventually_nhds_iff] at h3
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := h3
  set δ : ℝ := min δ₀ 1 with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos one_pos
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hδle1 : δ ≤ 1 := min_le_right _ _
  have hmem : Set.Ioo (b - δ) b ⊆ Set.Ioo (b - 1) b :=
    fun x hx => ⟨by linarith [hx.1, hδle1], hx.2⟩
  have hpt : ∀ θ ∈ Set.Ioo (b - δ) b,
      (|d| / (2 * C)) ^ 2 / (b - θ) ^ 2 ≤ (f θ) ^ 2 := by
    intro θ hθ
    have hbθ : 0 < b - θ := by linarith [hθ.2]
    have hdb : dist θ b < δ₀ := by
      rw [Real.dist_eq, abs_of_neg (by linarith [hθ.2] : θ - b < 0)]
      linarith [hθ.1, hδle]
    obtain ⟨hφθ, hwθ⟩ := hδ₀ hdb hθ.2
    have habs : |d| / 2 < |φ θ| * |f θ| := by
      have h1 : |d| ≤ |φ θ * f θ| + |φ θ * f θ - d| := by
        calc |d| = |φ θ * f θ + (d - φ θ * f θ)| := by
              rw [show φ θ * f θ + (d - φ θ * f θ) = d from by ring]
          _ ≤ |φ θ * f θ| + |d - φ θ * f θ| := abs_add_le _ _
          _ = |φ θ * f θ| + |φ θ * f θ - d| := by rw [abs_sub_comm]
      rw [abs_mul] at h1
      linarith
    have hfb : (|d| / 2) / (C * (b - θ)) < |f θ| := by
      rw [div_lt_iff₀ (mul_pos hC hbθ)]
      have h3' : |φ θ| * |f θ| ≤ |f θ| * (C * (b - θ)) := by
        calc |φ θ| * |f θ| ≤ (C * (b - θ)) * |f θ| :=
              mul_le_mul_of_nonneg_right hφθ (abs_nonneg _)
          _ = |f θ| * (C * (b - θ)) := by ring
      linarith
    have hsq : ((|d| / 2) / (C * (b - θ))) ^ 2 ≤ (f θ) ^ 2 := by
      have hnn : 0 ≤ (|d| / 2) / (C * (b - θ)) := by positivity
      have h := pow_le_pow_left₀ hnn (le_of_lt hfb) 2
      rwa [sq_abs] at h
    have halg : ((|d| / 2) / (C * (b - θ))) ^ 2 = (|d| / (2 * C)) ^ 2 / (b - θ) ^ 2 := by
      rw [div_pow, div_pow, mul_pow]
      field_simp
    rw [halg] at hsq
    exact hsq
  have hfδ : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2) (Set.Ioo (b - δ) b) :=
    hf.mono_set hmem
  have hcpos : 0 < (|d| / (2 * C)) ^ 2 :=
    pow_pos (div_pos hdabs (by linarith)) 2
  exact (not_integrableOn_of_le_div_sub_pow (f := fun θ => (f θ) ^ 2) (c := (|d| / (2 * C)) ^ 2)
      (b := b) (ε := δ) hcpos hδpos (k := 2) (by norm_num) hpt) hfδ

end Work.FTS.EllipticEst.remov.coerc
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.sliceAbsSinCos2CS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Set

/-! ## Elementary angular facts on `Iθ = [0,π/2]` -/

/-- `θ ↦ sin(2θ)^a` is a.e. strongly measurable on `Iθ`, for *every* real exponent `a`
(the instance `MeasurablePow ℝ ℝ` supplies measurability of `rpow` in the base). -/
private lemma aesm_sin_two_rpow (a : ℝ) :
    AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ a)
      (volume.restrict Work.Spaces.Iθ) :=
  ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const a).aestronglyMeasurable

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
private lemma sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- A vanishing `sin(2θ)` kills any non-zero power of it. -/
private lemma sin_two_rpow_eq_zero {θ a : ℝ} (h : Real.sin (2 * θ) = 0) (ha : a ≠ 0) :
    (Real.sin (2 * θ)) ^ a = 0 := by
  rw [h, Real.zero_rpow ha]

/-- At `sin(2θ) = 0` the angular weight `sinθcos²θ` vanishes as well. -/
private lemma sinCos2_eq_zero_of_sin_two_eq_zero {θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    Work.Elliptic.sinCos2 θ = 0 := by
  have h2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  rw [h] at h2
  rcases mul_eq_zero.mp h2.symm with h3 | h3
  · have hs : Real.sin θ = 0 := by linarith
    simp only [Work.Elliptic.sinCos2, hs, zero_mul]
  · simp only [Work.Elliptic.sinCos2, h3]
    ring

/-- `sinθcos²θ ≥ 0` on `Iθ`. -/
private lemma sinCos2_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ.2⟩
  simp only [Work.Elliptic.sinCos2]
  exact mul_nonneg h1 (pow_nonneg h2 2)

/-- `sinθcos²θ ≤ 1` on `Iθ`. -/
private lemma sinCos2_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Elliptic.sinCos2 θ ≤ 1 := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  have h2 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ.2⟩
  have hsq : Real.cos θ ^ 2 ≤ 1 := by nlinarith [Real.cos_le_one θ, h2]
  simp only [Work.Elliptic.sinCos2]
  have h := mul_le_mul (Real.sin_le_one θ) hsq (pow_nonneg h2 2) (by norm_num : (0 : ℝ) ≤ 1)
  simpa using h

/-! ## The slice Cauchy–Schwarz bound -/

/-- **Slice Cauchy–Schwarz for the angular moment `∫_Iθ |f|·sinθcos²θ`.**

With `u = |f|·sin(2θ)^{-η/2}` and `v = sinθcos²θ·sin(2θ)^{η/2}` (both non-negative on `Iθ`),
the product `u·v` equals `|f|·sinθcos²θ` while `u² = f²·sin(2θ)^{-η}` and
`v² = sin²θcos⁴θ·sin(2θ)^η ≤ 1`, whose integral over `Iθ` is at most `π/2 = |Iθ|`.
Cauchy–Schwarz `(∫u v)² ≤ (∫u²)(∫v²)` (Mathlib's `L²` version `Work.Spaces.cs_integral`) then
gives the claim. -/
theorem sliceAbsSinCos2CS {f : ℝ → ℝ}
    (haesm : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (h2 : MeasureTheory.Integrable
      (fun θ : ℝ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    (∫ θ in Work.Spaces.Iθ, |f θ| * Work.Elliptic.sinCos2 θ)
      ≤ Real.sqrt (Real.pi / 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hη : 0 < Work.Spaces.eta := Work.Spaces.eta_pos
  -- the two Cauchy–Schwarz factors
  set u : ℝ → ℝ := fun θ => |f θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) with hu
  set v : ℝ → ℝ :=
    fun θ => Work.Elliptic.sinCos2 θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hv
  -- ## measurability
  have hfabs : AEStronglyMeasurable (fun θ : ℝ => |f θ|) (volume.restrict Work.Spaces.Iθ) := by
    simpa only [Real.norm_eq_abs] using haesm.norm
  have hu_aesm : AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ) := by
    rw [hu]
    exact hfabs.mul (aesm_sin_two_rpow _)
  have hsc_cont : Continuous fun θ : ℝ => Work.Elliptic.sinCos2 θ := by
    simp only [Work.Elliptic.sinCos2]
    fun_prop
  have hv_aesm : AEStronglyMeasurable v (volume.restrict Work.Spaces.Iθ) := by
    rw [hv]
    exact hsc_cont.aestronglyMeasurable.mul (aesm_sin_two_rpow _)
  -- ## the pointwise identities
  have hu2_eq : ∀ θ ∈ Work.Spaces.Iθ,
      (u θ) ^ 2 = f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    intro θ hθ
    rw [hu]
    simp only
    rcases eq_or_lt_of_le (sin_two_nonneg hθ) with hzero' | hpos
    · have hzero : Real.sin (2 * θ) = 0 := hzero'.symm
      have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) = 0 :=
        sin_two_rpow_eq_zero hzero (by linarith)
      have h2' : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) = 0 :=
        sin_two_rpow_eq_zero hzero (by linarith)
      rw [h1, h2']
      ring
    · have hpow : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
          = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring
      calc (|f θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
          = |f θ| ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) := by
            rw [mul_pow]; ring
        _ = f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by rw [sq_abs, hpow]
  have hv2_eq : ∀ θ ∈ Work.Spaces.Iθ,
      (v θ) ^ 2
        = (Work.Elliptic.sinCos2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    intro θ hθ
    rw [hv]
    simp only
    rcases eq_or_lt_of_le (sin_two_nonneg hθ) with hzero' | hpos
    · have hzero : Real.sin (2 * θ) = 0 := hzero'.symm
      have h1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 :=
        sin_two_rpow_eq_zero hzero (by linarith)
      have h2' : (Real.sin (2 * θ)) ^ (Work.Spaces.eta) = 0 :=
        sin_two_rpow_eq_zero hzero (by linarith)
      rw [h1, h2']
      ring
    · have hpow : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
            * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
          = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring
      calc (Work.Elliptic.sinCos2 θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
          = (Work.Elliptic.sinCos2 θ) ^ 2 * ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
              * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by rw [mul_pow]; ring
        _ = (Work.Elliptic.sinCos2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
            rw [hpow]
  have huv_eq : (∫ θ in Work.Spaces.Iθ, u θ * v θ)
      = ∫ θ in Work.Spaces.Iθ, |f θ| * Work.Elliptic.sinCos2 θ := by
    refine MeasureTheory.setIntegral_congr_fun hIθ (fun θ hθ => ?_)
    rw [hu, hv]
    simp only
    rcases eq_or_lt_of_le (sin_two_nonneg hθ) with hzero' | hpos
    · have hzero : Real.sin (2 * θ) = 0 := hzero'.symm
      have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) = 0 :=
        sin_two_rpow_eq_zero hzero (by linarith)
      have h2' : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 :=
        sin_two_rpow_eq_zero hzero (by linarith)
      rw [h1, h2', sinCos2_eq_zero_of_sin_two_eq_zero hzero]
      ring
    · have hkey : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
            * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 1 := by
        rw [← Real.rpow_add hpos]
        rw [show (-(Work.Spaces.eta / 2) + Work.Spaces.eta / 2) = 0 by ring, Real.rpow_zero]
      calc (|f θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
              * (Work.Elliptic.sinCos2 θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
          = (|f θ| * Work.Elliptic.sinCos2 θ)
              * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
                * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by ring
        _ = |f θ| * Work.Elliptic.sinCos2 θ := by rw [hkey, mul_one]
  -- ## integrability of the two factors
  have hu2_int : Integrable (fun θ : ℝ => (u θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.IntegrableOn.congr_fun h2 (fun θ hθ => (hu2_eq θ hθ).symm) hIθ
  have hsin_cont : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
  have hv2_cont : Continuous fun θ : ℝ =>
      (Work.Elliptic.sinCos2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta) :=
    (hsc_cont.pow 2).mul ((Real.continuous_rpow_const hη.le).comp hsin_cont)
  have hv2_int : Integrable (fun θ : ℝ => (v θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.IntegrableOn.congr_fun
      (ContinuousOn.integrableOn_compact (K := Work.Spaces.Iθ) isCompact_Icc
        hv2_cont.continuousOn)
      (fun θ hθ => (hv2_eq θ hθ).symm) hIθ
  have hu_memLp : MemLp u 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hu_aesm).mpr hu2_int
  have hv_memLp : MemLp v 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hv_aesm).mpr hv2_int
  -- ## Cauchy–Schwarz
  have hcs := Work.Spaces.cs_integral (u := u) (v := v) (s := Work.Spaces.Iθ) hu_memLp hv_memLp
  -- ## the bound on `∫ v²`
  have hv2_le_one : ∀ θ ∈ Work.Spaces.Iθ, (v θ) ^ 2 ≤ 1 := by
    intro θ hθ
    rw [hv2_eq θ hθ]
    have hsin0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
    have hpow1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta) ≤ 1 :=
      Real.rpow_le_one hsin0 (Real.sin_le_one _) hη.le
    have hsc2 : (Work.Elliptic.sinCos2 θ) ^ 2 ≤ 1 := by
      nlinarith [sinCos2_nonneg hθ, sinCos2_le_one hθ]
    have h := mul_le_mul hsc2 hpow1 (Real.rpow_nonneg hsin0 _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  have hone : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, mul_one, Work.Spaces.Iθ]
    rw [Real.volume_real_Icc_of_le (by positivity)]
    ring
  have hv2_le : (∫ θ in Work.Spaces.Iθ, (v θ) ^ 2) ≤ Real.pi / 2 := by
    have hone_int : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict Work.Spaces.Iθ) :=
      ContinuousOn.integrableOn_compact (K := Work.Spaces.Iθ) isCompact_Icc
        continuous_const.continuousOn
    have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), (v θ) ^ 2 ≤ 1 :=
      (MeasureTheory.ae_restrict_iff' hIθ).mpr
        (Filter.Eventually.of_forall fun θ hθ => hv2_le_one θ hθ)
    have h := MeasureTheory.integral_mono_ae hv2_int hone_int hae
    rwa [hone] at h
  -- ## non-negativity of the three integrals
  have hC_nonneg : 0 ≤ ∫ θ in Work.Spaces.Iθ, u θ * v θ :=
    MeasureTheory.setIntegral_nonneg_ae hIθ (Filter.Eventually.of_forall fun θ hθ =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hθ) _))
        (mul_nonneg (sinCos2_nonneg hθ) (Real.rpow_nonneg (sin_two_nonneg hθ) _)))
  have hA : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hB : 0 ≤ ∫ θ in Work.Spaces.Iθ, (v θ) ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hu2_int_eq : (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    MeasureTheory.setIntegral_congr_fun hIθ (fun θ hθ => hu2_eq θ hθ)
  have hAB : 0 ≤ (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) * (∫ θ in Work.Spaces.Iθ, (v θ) ^ 2) :=
    mul_nonneg hA hB
  -- ## assembly
  calc (∫ θ in Work.Spaces.Iθ, |f θ| * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, u θ * v θ := huv_eq.symm
    _ ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) * (∫ θ in Work.Spaces.Iθ, (v θ) ^ 2)) :=
        (Real.le_sqrt hC_nonneg hAB).mpr hcs
    _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (v θ) ^ 2) := Real.sqrt_mul hA _
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) * Real.sqrt (Real.pi / 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv2_le) (Real.sqrt_nonneg _)
    _ = Real.sqrt (Real.pi / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ,
              f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        rw [hu2_int_eq]; ring

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.slice_bd_tail_g =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.EllipticEst.remov

/-- The weight `cos⁴/σ`, `σ t = sin (2t)^{2-γ}`, is bounded by `(π/4)^4` on the right half
`(ν, π/2)` of the slice, for `ν ≥ π/4` and `1 ≤ γ ≤ 3/2`.

Writing `ε = π/2 - t`, `cos t = sin ε ≤ ε` and Jordan's inequality
`sin (2t) = sin (2ε) ≥ (2/π)(2ε) = (4/π)ε` give `σ ≥ ((4/π)ε)^{2-γ} ≥ (4/π)ε`; hence
`cos⁴t/σ ≤ ε⁴/((4/π)ε) = (π/4)ε³ ≤ (π/4)⁴`. -/
lemma cos4_div_sigma_le_const (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {ν : ℝ}
    (hν : ν ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) {t : ℝ}
    (ht : t ∈ Set.Ioo ν (Real.pi / 2)) :
    (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ) ≤ (Real.pi / 4) ^ 4 := by
  have hν4 : Real.pi / 4 ≤ ν := hν.1
  have ht1 : ν < t := ht.1
  have ht2 : t < Real.pi / 2 := ht.2
  have hπne : Real.pi ≠ 0 := Real.pi_ne_zero
  set ε : ℝ := Real.pi / 2 - t with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hεle : ε ≤ Real.pi / 4 := by rw [hε]; linarith
  have hεne : ε ≠ 0 := ne_of_gt hεpos
  have hsin_eq : Real.sin (2 * t) = Real.sin (2 * ε) := by
    have h2 : 2 * ε = Real.pi - 2 * t := by rw [hε]; ring
    rw [h2, Real.sin_pi_sub]
  have h2ε_nn : 0 ≤ 2 * ε := by linarith
  have h2ε_le : 2 * ε ≤ Real.pi / 2 := by linarith
  have hjordan : 2 / Real.pi * (2 * ε) ≤ Real.sin (2 * ε) := Real.mul_le_sin h2ε_nn h2ε_le
  have hσge : 4 / Real.pi * ε ≤ Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    have hσge' : Real.rpow (4 / Real.pi * ε) (2 - γ) ≤
        Real.rpow (Real.sin (2 * t)) (2 - γ) := by
      have hbase : 2 / Real.pi * (2 * ε) = 4 / Real.pi * ε := by ring
      rw [hsin_eq, ← hbase]
      exact Real.rpow_le_rpow (by positivity) hjordan (by linarith)
    have hbase1 : 4 / Real.pi * ε ≤ 1 := by
      have h1 : 4 / Real.pi * (Real.pi / 4) = 1 := by field_simp
      calc 4 / Real.pi * ε ≤ 4 / Real.pi * (Real.pi / 4) :=
            mul_le_mul_of_nonneg_left hεle (by positivity)
        _ = 1 := h1
    have hrp : 4 / Real.pi * ε ≤ Real.rpow (4 / Real.pi * ε) (2 - γ) := by
      have h := Real.rpow_le_rpow_of_exponent_ge (x := 4 / Real.pi * ε) (y := 1) (z := 2 - γ)
        (by positivity) hbase1 (by linarith)
      rwa [Real.rpow_one] at h
    exact le_trans hrp hσge'
  have hcos_eq : Real.cos t = Real.sin ε := by
    rw [hε]; exact (Real.sin_pi_div_two_sub t).symm
  have hcos_le : Real.cos t ≤ ε := by
    rw [hcos_eq]; exact Real.sin_le (le_of_lt hεpos)
  have hcos_nn : 0 ≤ Real.cos t := by
    rw [hcos_eq]
    refine Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hεpos, ?_⟩
    linarith [hεle, Real.pi_pos]
  have hcos4_le : (Real.cos t) ^ 4 ≤ ε ^ 4 := pow_le_pow_left₀ hcos_nn hcos_le 4
  have hbasepos : 0 < 4 / Real.pi * ε := by positivity
  calc (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ)
      ≤ (Real.cos t) ^ 4 / (4 / Real.pi * ε) :=
        div_le_div_of_nonneg_left (pow_nonneg hcos_nn 4) hbasepos hσge
    _ ≤ ε ^ 4 / (4 / Real.pi * ε) :=
        div_le_div_of_nonneg_right hcos4_le (le_of_lt hbasepos)
    _ = (Real.pi / 4) * ε ^ 3 := by field_simp
    _ ≤ (Real.pi / 4) * (Real.pi / 4) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hεpos) hεle 3) (by positivity)
    _ = (Real.pi / 4) ^ 4 := by ring

/-- `cos⁴/σ` is integrable on `(ν, π/2)`, `σ t = sin (2t)^{2-γ}`, `1 ≤ γ ≤ 3/2`,
`ν ∈ [π/4, π/2)`: it is a bounded function on a set of finite measure. -/
lemma integrableOn_cos4_div_sigma (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {ν : ℝ}
    (hν : ν ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    MeasureTheory.IntegrableOn
      (fun t => (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ))
      (Set.Ioo ν (Real.pi / 2)) := by
  have hγ0 : 0 ≤ 2 - γ := by linarith
  have hcontσ : Continuous (fun t : ℝ => Real.rpow (Real.sin (2 * t)) (2 - γ)) :=
    (Real.continuous_rpow_const hγ0).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ ((Real.pi / 4) ^ 4) ?_
  · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  · exact (((Real.continuous_cos.pow 4).measurable).div hcontσ.measurable).aestronglyMeasurable
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall (fun t ht => ?_))
    have hnn : 0 ≤ (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ) :=
      div_nonneg (pow_nonneg (Real.cos_nonneg_of_mem_Icc (by
        constructor <;> linarith [ht.1, ht.2, hν.1, Real.pi_pos])) 4)
        (le_of_lt (Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi
          (by linarith [ht.1, hν.1, Real.pi_pos]) (by linarith [ht.2, Real.pi_pos])) _))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact cos4_div_sigma_le_const γ hγ1 hγ2 hν ht

/-- Weighted Cauchy–Schwarz on the right half of the slice: the `g`-part of the tail.

For `ν ∈ [π/4, π/2)`, `g` a.e.-strongly-measurable and `g²σ` integrable on `(ν, π/2)`
(`σ = sin(2t)^{2-γ}`, `1 ≤ γ ≤ 3/2`), the function `|g|cos²` is integrable there and

  `∫_{Ioo ν (π/2)} |g t| cos²t ≤ √(Cw · ∫_{Ioo ν (π/2)} g²σ) · (π/2-ν)^{(3+γ)/2}`

whenever `∫_{Ioo ν (π/2)} cos⁴/σ ≤ Cw (π/2-ν)^{3+γ}`.

Proof: write `|g|cos² = (√σ·|g|)·(cos²/√σ)` (σ > 0 on the open interval) and apply
Cauchy–Schwarz; `∫(√σ g)² = ∫σg²` and `∫(cos²/√σ)² = ∫cos⁴/σ`.  Integrability of `|g|cos²`
follows from the pointwise AM–GM bound `|g|cos² ≤ g²σ/2 + (cos⁴/σ)/2` together with the
boundedness of `cos⁴/σ` near the endpoints (it is bounded by `1/(2 sin ν)^{2-γ}` on `[ν, π/2]`).
Note that `cos⁴/σ` and `cos⁶/σ` are *unconditionally* integrable on `(ν, π/2)` for `ν > 0`. -/
theorem slice_bd_tail_g (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {g : ℝ → ℝ} {Cw ν : ℝ}
    (hCw : 0 ≤ Cw) (hν : ν ∈ Set.Ico (Real.pi / 4) (Real.pi / 2))
    (hGm : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))))
    (hG : MeasureTheory.IntegrableOn
      (fun t => (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
      (Set.Ioo ν (Real.pi / 2)))
    (hI4 : (∫ t in ν..(Real.pi / 2),
        (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ))
        ≤ Cw * (Real.pi / 2 - ν) ^ (3 + γ)) :
    (MeasureTheory.IntegrableOn (fun t => |g t| * (Real.cos t) ^ 2)
        (Set.Ioo ν (Real.pi / 2)))
      ∧ (∫ t in Set.Ioo ν (Real.pi / 2), |g t| * (Real.cos t) ^ 2
          ≤ Real.sqrt (Cw * (∫ t in Set.Ioo ν (Real.pi / 2),
                (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)))
            * (Real.pi / 2 - ν) ^ ((3 + γ) / 2)) := by
  have hν4 : Real.pi / 4 ≤ ν := hν.1
  have hνlt : ν < Real.pi / 2 := hν.2
  have hbpos : 0 < Real.pi / 2 - ν := by linarith
  have hbnonneg : 0 ≤ Real.pi / 2 - ν := le_of_lt hbpos
  have hγ0 : 0 ≤ 2 - γ := by linarith
  have hσpos : ∀ t ∈ Set.Ioo ν (Real.pi / 2), 0 < Real.rpow (Real.sin (2 * t)) (2 - γ) := by
    intro t ht
    refine Real.rpow_pos_of_pos ?_ _
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1, hν4, Real.pi_pos])
      (by linarith [ht.2, Real.pi_pos])
  -- pointwise identities on the interval, and their a.e. versions
  have hpt_u : ∀ t ∈ Set.Ioo ν (Real.pi / 2),
      (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)
        = (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|) ^ 2 := by
    intro t ht
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hσpos t ht)), sq_abs]
    ring
  have hae_u : (fun t => (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))]
      (fun t => (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|) ^ 2) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall (fun t ht => hpt_u t ht))
  have hpt_v : ∀ t ∈ Set.Ioo ν (Real.pi / 2),
      (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ)
        = ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) ^ 2 := by
    intro t ht
    rw [div_pow, Real.sq_sqrt (le_of_lt (hσpos t ht)), ← pow_mul]
  have hae_v : (fun t => (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))]
      (fun t => ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) ^ 2) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall (fun t ht => hpt_v t ht))
  have hpt_uv : ∀ t ∈ Set.Ioo ν (Real.pi / 2),
      (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|)
          * ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)))
        = |g t| * (Real.cos t) ^ 2 := by
    intro t ht
    have hne : Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (hσpos t ht))
    calc (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|)
          * ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)))
        = ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)))
          * (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|) := by
          rw [mul_comm]
      _ = (((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)))
          * Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) * |g t| := by
          rw [mul_assoc]
      _ = (Real.cos t) ^ 2 * |g t| := by rw [div_mul_cancel₀ _ hne]
      _ = |g t| * (Real.cos t) ^ 2 := by rw [mul_comm]
  have hae_uv : (fun t => (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|)
      * ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))]
      (fun t => |g t| * (Real.cos t) ^ 2) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall (fun t ht => hpt_uv t ht))
  have hcontσ : Continuous (fun t : ℝ => Real.rpow (Real.sin (2 * t)) (2 - γ)) :=
    (Real.continuous_rpow_const hγ0).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  -- the two factors are `L²`
  have hu : MeasureTheory.MemLp
      (fun t => Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|) 2
      (MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))) := by
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun t => Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|)
        (MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))) :=
      ((Real.continuous_sqrt.comp hcontσ).aestronglyMeasurable).mul
        (by simpa [Real.norm_eq_abs] using hGm.norm)
    exact (MeasureTheory.memLp_two_iff_integrable_sq haesm).mpr (hG.congr hae_u)
  have hv : MeasureTheory.MemLp
      (fun t => (Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) 2
      (MeasureTheory.volume.restrict (Set.Ioo ν (Real.pi / 2))) := by
    have hmeas : Measurable
        (fun t : ℝ => (Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) :=
      ((Real.continuous_cos.pow 2).measurable).div
        (Real.continuous_sqrt.comp hcontσ).measurable
    exact (MeasureTheory.memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr
      ((integrableOn_cos4_div_sigma γ hγ1 hγ2 hν).congr hae_v)
  -- the set-integral form of the hypothesis
  have hI4set : (∫ t in Set.Ioo ν (Real.pi / 2),
      (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ))
      ≤ Cw * (Real.pi / 2 - ν) ^ (3 + γ) := by
    have h := hI4
    rwa [intervalIntegral.integral_of_le (le_of_lt hνlt),
      MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
  -- Cauchy–Schwarz
  have hcs := Ebs.abs_integral_mul_le_sqrt hu hv
  have hmain : (∫ t in Set.Ioo ν (Real.pi / 2),
        (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|)
          * ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))))
      = (∫ t in Set.Ioo ν (Real.pi / 2), |g t| * (Real.cos t) ^ 2) :=
    integral_congr_ae hae_uv
  have hIu : (∫ t in Set.Ioo ν (Real.pi / 2),
        (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|) ^ 2)
      = (∫ t in Set.Ioo ν (Real.pi / 2),
          (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)) :=
    integral_congr_ae hae_u.symm
  have hIv : (∫ t in Set.Ioo ν (Real.pi / 2),
        ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) ^ 2)
      = (∫ t in Set.Ioo ν (Real.pi / 2),
          (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ)) :=
    integral_congr_ae hae_v.symm
  have hsqrt_rpow : Real.sqrt ((Real.pi / 2 - ν) ^ (3 + γ))
      = (Real.pi / 2 - ν) ^ ((3 + γ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbnonneg]
    congr 1
    ring
  have hcoef : Real.sqrt (∫ t in Set.Ioo ν (Real.pi / 2),
        (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)) * Real.sqrt Cw
      = Real.sqrt (Cw * (∫ t in Set.Ioo ν (Real.pi / 2),
          (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))) := by
    rw [mul_comm (Real.sqrt _), Real.sqrt_mul hCw]
  refine ⟨?_, ?_⟩
  · exact (hu.integrable_mul hv).congr hae_uv
  · calc (∫ t in Set.Ioo ν (Real.pi / 2), |g t| * (Real.cos t) ^ 2)
        = (∫ t in Set.Ioo ν (Real.pi / 2),
            (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|)
              * ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)))) :=
          hmain.symm
      _ ≤ |∫ t in Set.Ioo ν (Real.pi / 2),
            (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|)
              * ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)))| :=
          le_abs_self _
      _ ≤ Real.sqrt (∫ t in Set.Ioo ν (Real.pi / 2),
              (Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ)) * |g t|) ^ 2)
            * Real.sqrt (∫ t in Set.Ioo ν (Real.pi / 2),
              ((Real.cos t) ^ 2 / Real.sqrt (Real.rpow (Real.sin (2 * t)) (2 - γ))) ^ 2) :=
          hcs
      _ = Real.sqrt (∫ t in Set.Ioo ν (Real.pi / 2),
              (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
            * Real.sqrt (∫ t in Set.Ioo ν (Real.pi / 2),
              (Real.cos t) ^ 4 / Real.rpow (Real.sin (2 * t)) (2 - γ)) := by
          rw [hIu, hIv]
      _ ≤ Real.sqrt (∫ t in Set.Ioo ν (Real.pi / 2),
              (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
            * Real.sqrt (Cw * (Real.pi / 2 - ν) ^ (3 + γ)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hI4set) (Real.sqrt_nonneg _)
      _ = Real.sqrt (∫ t in Set.Ioo ν (Real.pi / 2),
              (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ))
            * (Real.sqrt Cw * (Real.pi / 2 - ν) ^ ((3 + γ) / 2)) := by
          rw [Real.sqrt_mul hCw, hsqrt_rpow]
      _ = Real.sqrt (Cw * (∫ t in Set.Ioo ν (Real.pi / 2),
              (g t) ^ 2 * Real.rpow (Real.sin (2 * t)) (2 - γ)))
            * (Real.pi / 2 - ν) ^ ((3 + γ) / 2) := by
          rw [← mul_assoc, hcoef]

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.sin_complete_Ioc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

theorem sin_complete_Ioc {L : ℝ} (hL : 0 < L) {F : ℝ → ℝ}
    (hmem : MeasureTheory.MemLp F 2 (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) L)))
    (h : ∀ n : ℕ, 0 < n → ∫ θ in (0:ℝ)..L, F θ * Real.sin (n * Real.pi * θ / L) = 0) :
    F =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) L)] 0 := by
  have hmem2 : MeasureTheory.MemLp (sinOdd F) 2
      (MeasureTheory.volume.restrict (Set.Ioc (-L) L)) := sinOdd_memLp hL hmem
  have hint := sinInt_eq_zero hL h
  have hcoeff : ∀ n : ℤ, fourierCoeffOn (show (-L) < L by linarith) (sinOdd F) n = 0 := by
    intro n
    rw [sinOdd_fourierCoeffOn hL hmem2 n, hint n, mul_zero]
  have hcoeff0 : ∀ i : ℤ,
      ‖fourierCoeffOn (show (-L) < L by linarith) (sinOdd F) i‖ ^ 2 = 0 :=
    fun i => by rw [hcoeff i, norm_zero]; norm_num
  have hP := hasSum_sq_fourierCoeffOn (show (-L) < L by linarith) hmem2
  have hP0 : HasSum (fun _ : ℤ => (0:ℝ))
      ((L - -L)⁻¹ • ∫ x in (-L)..L, ‖sinOdd F x‖ ^ 2) := by
    simpa only [hcoeff0] using hP
  have hval : ((L - -L)⁻¹ • ∫ x in (-L)..L, ‖sinOdd F x‖ ^ 2) = 0 := by
    simpa using hP0.tsum_eq.symm
  have hInt : ∫ x in (-L)..L, ‖sinOdd F x‖ ^ 2 = 0 := by
    rw [smul_eq_mul] at hval
    exact (mul_eq_zero.mp hval).resolve_left (inv_ne_zero (by linarith : L - -L ≠ 0))
  exact sinOdd_ae_eq_zero hL hmem2 hInt

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.wirtinger_interval =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set Filter intervalIntegral

namespace Work.FTS.EllipticEst

/-- **Wirtinger's inequality on an interval, in the `r`-parametrised form.**  If `r > 0` with
`r * (b - a) = π` and `u` is `C²` on `[a,b]` with `u a = u b = 0`, then
`r² ∫ u² ≤ ∫ u'²`.  The proof uses the auxiliary function
`Φ x = r * u x ^ 2 * cot (r * (x - a))`, which vanishes at both endpoints and satisfies
`Φ' = u'² - r² u² - ((u' sin - u r cos) / sin)²` on `(a,b)`; integrating the identity and
dropping the nonnegative square gives the claim. -/
theorem wirtinger_interval_aux {a b r : ℝ} (hab : a < b) (hr : 0 < r) (hrb : r * (b - a) = π)
    {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Icc a b)) (ha : u a = 0) (hb : u b = 0) :
    r ^ 2 * (∫ θ in a..b, (u θ) ^ 2) ≤ ∫ θ in a..b, (deriv u θ) ^ 2 := by
  set Phi : ℝ → ℝ :=
    fun x => r * (u x) ^ 2 * (Real.cos (r * (x - a)) / Real.sin (r * (x - a))) with hPhi
  set G : ℝ → ℝ := fun x => ((deriv u x * Real.sin (r * (x - a))
      - u x * (r * Real.cos (r * (x - a)))) / Real.sin (r * (x - a))) ^ 2 with hG
  set f : ℝ → ℝ := fun x => (deriv u x) ^ 2 - r ^ 2 * (u x) ^ 2 - G x with hf
  have hA : IntervalIntegrable (fun x => (deriv u x) ^ 2) volume a b :=
    wirt_deriv_sq_integrable hab hu
  have hB : IntervalIntegrable (fun x => r ^ 2 * (u x) ^ 2) volume a b :=
    ((hu.continuousOn.pow 2).const_mul (r ^ 2)).intervalIntegrable_of_Icc hab.le
  have hGi : IntervalIntegrable G volume a b := by
    rw [hG]; exact wirt_G_integrable hab hr hrb hu ha hb
  have hf_int : IntervalIntegrable f volume a b := by
    rw [hf]
    exact (hA.sub hB).sub hGi
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt Phi (f x) x := by
    intro x hx
    rw [hPhi, hf, hG]
    exact wirt_phi_deriv hab hr hrb hu x hx
  obtain ⟨hta, htb⟩ := wirt_phi_tendsto hab hr hrb hu ha hb
  have hta' : Tendsto Phi (nhdsWithin a (Set.Ioi a)) (nhds 0) := by rw [hPhi]; exact hta
  have htb' : Tendsto Phi (nhdsWithin b (Set.Iio b)) (nhds 0) := by rw [hPhi]; exact htb
  have hFTC : ∫ x in a..b, f x = 0 := by
    rw [integral_eq_sub_of_hasDerivAt_of_tendsto hab hderiv hf_int hta' htb']
    ring
  have hnonneg : 0 ≤ ∫ x in a..b, G x := by
    refine integral_nonneg hab.le (fun x hx => ?_)
    rw [hG]; positivity
  have hpt : ∀ x, f x + G x = (deriv u x) ^ 2 - r ^ 2 * (u x) ^ 2 := by
    intro x; rw [hf]; ring
  have h1 : (∫ x in a..b, ((deriv u x) ^ 2 - r ^ 2 * (u x) ^ 2))
      = (∫ x in a..b, f x) + (∫ x in a..b, G x) := by
    rw [← intervalIntegral.integral_add hf_int hGi]
    exact (intervalIntegral.integral_congr (fun x _ => hpt x)).symm
  have h2 : (∫ x in a..b, ((deriv u x) ^ 2 - r ^ 2 * (u x) ^ 2))
      = (∫ x in a..b, (deriv u x) ^ 2) - ∫ x in a..b, r ^ 2 * (u x) ^ 2 := by
    rw [intervalIntegral.integral_sub hA hB]
  have h3 : (∫ x in a..b, r ^ 2 * (u x) ^ 2) = r ^ 2 * ∫ x in a..b, (u x) ^ 2 :=
    intervalIntegral.integral_const_mul (r ^ 2) (fun x => (u x) ^ 2)
  have key : r ^ 2 * (∫ x in a..b, (u x) ^ 2) ≤ ∫ x in a..b, (deriv u x) ^ 2 := by
    have h := h1
    rw [h2, h3, hFTC, zero_add] at h
    linarith [hnonneg]
  exact key

/-- **Wirtinger's inequality on an interval.** For a `C²` function `u` on `[a,b]` with
`u a = u b = 0`, `(π/(b-a))² ∫ u² ≤ ∫ u'²`. -/
theorem wirtinger_interval {a b : ℝ} (hab : a < b) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Icc a b)) (ha : u a = 0) (hb : u b = 0) :
    (π / (b - a)) ^ 2 * (∫ θ in a..b, (u θ) ^ 2) ≤ ∫ θ in a..b, (deriv u θ) ^ 2 := by
  have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hr : 0 < π / (b - a) := div_pos Real.pi_pos (sub_pos.mpr hab)
  have hrb : π / (b - a) * (b - a) = π := div_mul_cancel₀ π hne
  simpa using wirtinger_interval_aux hab hr hrb hu ha hb

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.PsiWt.Dth_sq_sin_rpow_le_HkIntegrand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses.PsiWt

theorem Dth_sq_sin_rpow_le_HkIntegrand {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.Dth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam a))
      ≤ Work.Spaces.HkIntegrand a 4 f z θ := by
  -- `D_θ f = D_z^0 D_θ^1 f` is the mixed slot `(i,j) = (1,0)` of the `H^4` integrand, so it
  -- suffices to compare the two expressions.  Both the extra factor `w z ≥ 1` (for `z > 0`)
  -- and the identity `sin(2θ)^{-γ} = (sin(2θ)^{-γ/2})²` (for `sin(2θ) > 0`, i.e. on the open
  -- angular interval) only make that slot larger than the left-hand side.
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by have := Real.pi_pos; linarith [hθ.2])
  have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam a)) :=
    Real.rpow_nonneg (le_of_lt hs) _
  have hw1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith [hz]
  have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ hw1
  have hsq : (Real.sin (2 * θ) ^ (-(Work.Spaces.gam a / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam a)) := by
    rw [sq, ← Real.rpow_add hs,
      show -(Work.Spaces.gam a / 2) + -(Work.Spaces.gam a / 2) = -(Work.Spaces.gam a) by ring]
  have hterm : (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt a z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand a 4 f z θ :=
    Work.Spaces.sq_le_HkIntegrand_mixed a 4 f z θ 1 0 le_rfl (by norm_num)
  refine le_trans ?_ hterm
  have hmix : Work.Spaces.mixed 0 1 f = Work.Spaces.Dth f := rfl
  rw [hmix]
  calc (Work.Spaces.Dth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam a))
      = (Work.Spaces.Dth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam a)) * 1 := by
        ring
    _ ≤ (Work.Spaces.Dth f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam a))
          * (Work.Spaces.w z) ^ 2 :=
        mul_le_mul_of_nonneg_left hw2 (mul_nonneg (sq_nonneg _) hsnn)
    _ = (Work.Spaces.Dth f z θ
          * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam a / 2)))) ^ 2 := by
        rw [mul_pow, mul_pow, hsq]; ring
    _ = (Work.Spaces.Dth f z θ * Work.Spaces.Wt a z θ) ^ 2 := by
        rw [Work.Spaces.Wt, Work.Spaces.wTheta]

end Work.FTS.FireFix.Clauses.PsiWt
end
-- ===== merged: Submission.Work.FTS.FireFix.Clauses.XferChain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Work.FTS.FireFix.Clauses

/-- The angular interval `(-π/2, π/2)`. -/
abbrev ThetaI : Set ℝ := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)

/-- The domain `(0,∞) × (-π/2, π/2)` of the transferred profile. -/
abbrev Adom : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ ThetaI

/-- The profile pulled back to a point `(r,z)` of the half plane:
`(r,z) ↦ g (√(r²+z²)^{3α}/B) (arctan (z/r))`. -/
def prof (α B : ℝ) (g : ℝ → ℝ → ENNReal) (r z : ℝ) : ENNReal :=
  g (Real.sqrt (r ^ 2 + z ^ 2) ^ (3 * α) / B) (Real.arctan (z / r))

@[simp] lemma rho_pt3 (a b t : ℝ) :
    Work.Cyl.rho (pt3 a b t) = Real.sqrt (a ^ 2 + b ^ 2 + t ^ 2) := by
  simp only [Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.axial, pt3_zero, pt3_one, pt3_two]

@[simp] lemma theta_pt3 (a b t : ℝ) :
    Work.Cyl.theta (pt3 a b t) = Real.arctan (t / Real.sqrt (a ^ 2 + b ^ 2)) := by
  simp only [Work.Cyl.theta, Work.Cyl.axial, Work.Cyl.radial, Work.Cyl.radSq,
    pt3_zero, pt3_one, pt3_two]

lemma prof_measurable {α B : ℝ} (hα : 0 ≤ α) {g : ℝ → ℝ → ENNReal}
    (hg : Measurable (fun q : ℝ × ℝ => g q.1 q.2)) :
    Measurable (fun p : ℝ × ℝ => prof α B g p.1 p.2) := by
  refine hg.comp (Measurable.prodMk ?_ ?_)
  · have hsq : Continuous fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2 := by fun_prop
    have hpow : Measurable (fun p : ℝ × ℝ => Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ^ (3 * α)) :=
      ((Real.continuous_sqrt.comp hsq).rpow_const
        (fun p => Or.inr (by linarith))).measurable
    exact hpow.div measurable_const
  · exact Real.continuous_arctan.measurable.comp (measurable_snd.div measurable_fst)

/-- The angular profile is radial in the plane: `prof α B g (√(a²+b²)) t` is the profile of the
point `pt3 a b t`. -/
lemma prof_sqrt (α B : ℝ) (g : ℝ → ℝ → ENNReal) (a b t : ℝ) :
    prof α B g (Real.sqrt (a ^ 2 + b ^ 2)) t
      = g (Real.sqrt (a ^ 2 + b ^ 2 + t ^ 2) ^ (3 * α) / B)
          (Real.arctan (t / Real.sqrt (a ^ 2 + b ^ 2))) := by
  simp only [prof, Real.sq_sqrt (by positivity : (0:ℝ) ≤ a ^ 2 + b ^ 2)]

/-- On the half plane `r > 0` the polar coordinates `z ↦ (r cos z, r sin z)` give back the
profile `g (r^{3α}/B) z`. -/
lemma prof_polar (α B : ℝ) (g : ℝ → ℝ → ENNReal) {r z : ℝ} (hr : 0 < r) (hz : z ∈ ThetaI) :
    prof α B g (r * Real.cos z) (r * Real.sin z) = g (r ^ (3 * α) / B) z := by
  have hsq : (r * Real.cos z) ^ 2 + (r * Real.sin z) ^ 2 = r ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  rw [prof, hsq, Real.sqrt_sq hr.le]
  congr 1
  rw [mul_div_mul_left _ _ (ne_of_gt hr), ← Real.tan_eq_sin_div_cos]
  exact Real.arctan_tan hz.1 hz.2


/-- The coordinate map `x ↦ (ρ x ^ (3α)/B, θ x)` is measurable. -/
lemma measurable_rhoTheta {α B : ℝ} (hα : 0 ≤ α) :
    Measurable (fun x : EuclideanSpace ℝ (Fin 3) =>
      (Work.Cyl.rho x ^ (3 * α) / B, Work.Cyl.theta x)) := by
  refine Measurable.prodMk ?_ ?_
  · have hcont : Continuous fun x : EuclideanSpace ℝ (Fin 3) => Work.Cyl.rho x := by
      simp only [Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.axial]
      fun_prop
    exact ((hcont.rpow_const (fun x => Or.inr (by linarith))).measurable).div_const B
  · show Measurable (fun x : EuclideanSpace ℝ (Fin 3) =>
        Real.arctan (x 2 / Real.sqrt (x 0 ^ 2 + x 1 ^ 2)))
    exact Real.continuous_arctan.measurable.comp
      ((by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin 3) => x 2).div
        (by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin 3) =>
          Real.sqrt (x 0 ^ 2 + x 1 ^ 2)))

/-- **The half plane step**: the polar change of variables on `r > 0`, with the constant `2π` of
the plane already present. -/
lemma halfline_step {α B : ℝ} (hα : 0 < α) (hB : 0 < B) {g : ℝ → ℝ → ENNReal}
    (hg : Measurable (fun q : ℝ × ℝ => g q.1 q.2)) :
    (∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ),
        ENNReal.ofReal p.1 * (ENNReal.ofReal (2 * Real.pi) * prof α B g p.1 p.2))
      = ∫⁻ q in Adom,
          ENNReal.ofReal (q.1 ^ 2 * Real.cos q.2) * (ENNReal.ofReal (2 * Real.pi) *
            g (q.1 ^ (3 * α) / B) q.2) := by
  have hK : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (2 * Real.pi) * prof α B g p.1 p.2) MeasureTheory.volume :=
    (measurable_const.mul (prof_measurable hα.le hg)).aemeasurable
  have h := xfer_halfline_polar (K := fun r z => ENNReal.ofReal (2 * Real.pi) * prof α B g r z) hK
  rw [h]
  refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) ?_
  rintro ⟨r, z⟩ hq
  obtain ⟨hr, hz⟩ := hq
  show ENNReal.ofReal (r ^ 2 * Real.cos z) *
      (ENNReal.ofReal (2 * Real.pi) * prof α B g (r * Real.cos z) (r * Real.sin z))
    = ENNReal.ofReal (r ^ 2 * Real.cos z) *
        (ENNReal.ofReal (2 * Real.pi) * g (r ^ (3 * α) / B) z)
  rw [prof_polar α B g hr hz]

/-- **The scaling step**: the substitution `ρ = (B s)^{1/(3α)}` in the radial variable. -/
lemma scaling_step {α B : ℝ} (hα : 0 < α) (hB : 0 < B) {g : ℝ → ℝ → ENNReal}
    (hg : Measurable (fun q : ℝ × ℝ => g q.1 q.2)) :
    (∫⁻ q in Adom, ENNReal.ofReal (q.1 ^ 2 * Real.cos q.2) * g (q.1 ^ (3 * α) / B) q.2)
      = ENNReal.ofReal (B ^ (1 / α) / (3 * α)) *
        ∫⁻ q in Adom, ENNReal.ofReal (q.1 ^ (1 / α - 1) * Real.cos q.2) * g q.1 q.2 := by
  have h3α : (0 : ℝ) < 3 * α := by positivity
  have hmul : (1 : ℝ) / (3 * α) * (3 * α) = 1 := by field_simp
  -- measurability of the two integrands
  have hmeas1 : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (p.1 ^ 2 * Real.cos p.2) * g (p.1 ^ (3 * α) / B) p.2)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict Adom) :=
    Measurable.aemeasurable (Measurable.mul
      (ENNReal.measurable_ofReal.comp
        ((measurable_fst.pow_const 2).mul (Real.continuous_cos.measurable.comp measurable_snd)))
      (hg.comp (Measurable.prodMk
        ((measurable_fst.pow_const _).div measurable_const) measurable_snd)))
  have hmeas2 : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (p.1 ^ (1 / α - 1) * Real.cos p.2) * g p.1 p.2)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict Adom) :=
    Measurable.aemeasurable (Measurable.mul
      (ENNReal.measurable_ofReal.comp
        ((measurable_fst.pow_const _).mul (Real.continuous_cos.measurable.comp measurable_snd)))
      hg)
  -- pass to the iterated integral, angular variable outermost
  have hunwrap : (∫⁻ q in Adom,
        ENNReal.ofReal (q.1 ^ 2 * Real.cos q.2) * g (q.1 ^ (3 * α) / B) q.2)
      = ∫⁻ z in ThetaI, ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (r ^ 2 * Real.cos z) * g (r ^ (3 * α) / B) z := by
    rw [show Adom = Set.Ioi (0 : ℝ) ×ˢ ThetaI from rfl]
    exact setLIntegral_prod_symm _ hmeas1
  rw [hunwrap]
  have hstep : ∀ z ∈ ThetaI, (∫⁻ r in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (r ^ 2 * Real.cos z) * g (r ^ (3 * α) / B) z)
      = ENNReal.ofReal (Real.cos z) *
        (ENNReal.ofReal (B ^ (1 / α) / (3 * α)) *
          ∫⁻ s in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (s ^ (1 / α - 1)) * g s z) := by
    intro z hz
    have hcos : 0 ≤ Real.cos z := (Real.cos_pos_of_mem_Ioo hz).le
    have hG : AEMeasurable (fun r : ℝ => g (r ^ (3 * α) / B) z) MeasureTheory.volume :=
      (hg.comp (Measurable.prodMk ((measurable_id.pow_const _).div measurable_const)
        measurable_const)).aemeasurable
    have hcongr : (∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (r ^ 2 * Real.cos z) * g (r ^ (3 * α) / B) z)
        = ∫⁻ r in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (Real.cos z) * (ENNReal.ofReal (r ^ 2) * g (r ^ (3 * α) / B) z) := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
      rw [mul_comm (r ^ 2) (Real.cos z), ENNReal.ofReal_mul hcos, mul_assoc]
    rw [hcongr, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    rw [xfer_scaling_rpow (α := α) (B := B) hα hB (G := fun r => g (r ^ (3 * α) / B) z) hG]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : 0 < s := hs
    have hBs : (0:ℝ) < B * s := mul_pos hB hs0
    have harg : ((B * s) ^ (1 / (3 * α))) ^ (3 * α) / B = s := by
      rw [← Real.rpow_mul hBs.le, hmul, Real.rpow_one, mul_div_cancel_left₀ s (ne_of_gt hB)]
    rw [harg]
  rw [setLIntegral_congr_fun measurableSet_Ioo (fun z hz => hstep z hz)]
  -- reassociate so that the constant `B^{1/α}/(3α)` is the outermost factor
  rw [show (∫⁻ z in ThetaI, ENNReal.ofReal (Real.cos z) *
        (ENNReal.ofReal (B ^ (1 / α) / (3 * α)) *
          ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (s ^ (1 / α - 1)) * g s z))
      = ∫⁻ z in ThetaI, ENNReal.ofReal (B ^ (1 / α) / (3 * α)) *
        (ENNReal.ofReal (Real.cos z) *
          ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (s ^ (1 / α - 1)) * g s z) from
    setLIntegral_congr_fun measurableSet_Ioo (fun z _ => by
      rw [← mul_assoc,
        mul_comm (ENNReal.ofReal (Real.cos z)) (ENNReal.ofReal (B ^ (1 / α) / (3 * α))),
        mul_assoc])]
  -- pull the constant out of the angular integral
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  -- move `ofReal (cos z)` inside the radial integral
  have hinner : (∫⁻ z in ThetaI, ENNReal.ofReal (Real.cos z) *
        ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (s ^ (1 / α - 1)) * g s z)
      = ∫⁻ z in ThetaI, ∫⁻ s in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.cos z) * (ENNReal.ofReal (s ^ (1 / α - 1)) * g s z) := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun z _ => ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hinner]
  -- back to the product domain, and identify the two weights
  have hmeas3 : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Real.cos p.2) * (ENNReal.ofReal (p.1 ^ (1 / α - 1)) * g p.1 p.2))
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict Adom) :=
    Measurable.aemeasurable (Measurable.mul
      (ENNReal.measurable_ofReal.comp (Real.continuous_cos.measurable.comp measurable_snd))
      (Measurable.mul (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)) hg))
  have hrewrap : (∫⁻ z in ThetaI, ∫⁻ r in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (Real.cos z) * (ENNReal.ofReal (r ^ (1 / α - 1)) * g r z))
      = ∫⁻ q in Adom,
          ENNReal.ofReal (Real.cos q.2) *
            (ENNReal.ofReal (q.1 ^ (1 / α - 1)) * g q.1 q.2) := by
    rw [show Adom = Set.Ioi (0 : ℝ) ×ˢ ThetaI from rfl]
    exact (setLIntegral_prod_symm _ hmeas3).symm
  rw [hrewrap]
  refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := hp
  have hcos : 0 ≤ Real.cos p.2 := (Real.cos_pos_of_mem_Ioo hp2).le
  show ENNReal.ofReal (Real.cos p.2) * (ENNReal.ofReal (p.1 ^ (1 / α - 1)) * g p.1 p.2)
    = ENNReal.ofReal (p.1 ^ (1 / α - 1) * Real.cos p.2) * g p.1 p.2
  rw [mul_comm (p.1 ^ (1 / α - 1)) (Real.cos p.2), ENNReal.ofReal_mul hcos, mul_assoc]

/-- **The `(ρ, θ)`-transfer** (the `ℝ≥0∞`-valued change of variables): the pushforward of the
Lebesgue measure on `ℝ³` under `x ↦ (ρ x ^ (3α)/B, θ x)` has density
`ofReal (2π B^{1/α} / (3α)) * ofReal (q.1^{1/α-1} cos q.2)` on `(0,∞) × (-π/2, π/2)`. -/
theorem lintegral_transfer {α B : ℝ} (hα : 0 < α) (hB : 0 < B)
    {g : ℝ → ℝ → ENNReal} (hg : Measurable (fun q : ℝ × ℝ => g q.1 q.2)) :
    ∫⁻ x : EuclideanSpace ℝ (Fin 3), g (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)
      = ENNReal.ofReal (2 * Real.pi * B ^ (1 / α) / (3 * α)) *
        ∫⁻ q in Adom, ENNReal.ofReal (q.1 ^ (1 / α - 1) * Real.cos q.2) * g q.1 q.2 := by
  have h3α : (0 : ℝ) < 3 * α := by positivity
  -- measurability of the coordinate map and of the integrand
  have hT : Measurable (fun x : EuclideanSpace ℝ (Fin 3) =>
      (Work.Cyl.rho x ^ (3 * α) / B, Work.Cyl.theta x)) := measurable_rhoTheta hα.le
  have hGb : Measurable (fun x : EuclideanSpace ℝ (Fin 3) =>
      g (Work.Cyl.rho x ^ (3 * α) / B) (Work.Cyl.theta x)) := hg.comp hT
  -- transport to the iterated integral over the axis coordinate and the plane coordinates
  rw [lintegral_eucl3_eq_prod hGb]
  -- rewrite `ρ` and `θ` on the coordinate points
  rw [show (∫⁻ t : ℝ, ∫⁻ v : ℝ × ℝ, g (Work.Cyl.rho (pt3 v.1 v.2 t) ^ (3 * α) / B)
        (Work.Cyl.theta (pt3 v.1 v.2 t)))
      = ∫⁻ t : ℝ, ∫⁻ v : ℝ × ℝ,
          g (Real.sqrt (v.1 ^ 2 + v.2 ^ 2 + t ^ 2) ^ (3 * α) / B)
            (Real.arctan (t / Real.sqrt (v.1 ^ 2 + v.2 ^ 2))) from
    lintegral_congr fun t => lintegral_congr fun v => by rw [rho_pt3, theta_pt3]]
  -- identify the integrand as the profile, radial in the plane
  rw [show (∫⁻ t : ℝ, ∫⁻ v : ℝ × ℝ,
          g (Real.sqrt (v.1 ^ 2 + v.2 ^ 2 + t ^ 2) ^ (3 * α) / B)
            (Real.arctan (t / Real.sqrt (v.1 ^ 2 + v.2 ^ 2))))
      = ∫⁻ t : ℝ, ∫⁻ v : ℝ × ℝ, prof α B g (Real.sqrt (v.1 ^ 2 + v.2 ^ 2)) t from
    lintegral_congr fun t => lintegral_congr fun v => (prof_sqrt α B g v.1 v.2 t).symm]
  -- the two-dimensional polar change of variables in the plane, slice by slice
  rw [show (∫⁻ t : ℝ, ∫⁻ v : ℝ × ℝ, prof α B g (Real.sqrt (v.1 ^ 2 + v.2 ^ 2)) t)
      = ∫⁻ t : ℝ, ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r * prof α B g r t from
    lintegral_congr fun t =>
      xfer_plane_radial ((prof_measurable hα.le hg).comp
        (by fun_prop : Measurable fun r : ℝ => (r, t))).aemeasurable]
  -- move the constant `2π` inside the radial integral
  rw [show (∫⁻ t : ℝ, ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r * prof α B g r t)
      = ∫⁻ t : ℝ, ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal r * (ENNReal.ofReal (2 * Real.pi) * prof α B g r t) from
    lintegral_congr fun t => by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact setLIntegral_congr_fun measurableSet_Ioi fun r _ => by
        rw [← mul_assoc,
          mul_comm (ENNReal.ofReal (2 * Real.pi)) (ENNReal.ofReal r), mul_assoc]]
  -- Fubini: the iterated integral over `(0,∞) × ℝ` is the integral over the half plane
  have hmeasH : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * (ENNReal.ofReal (2 * Real.pi) * prof α B g p.1 p.2))
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) :=
    (Measurable.aemeasurable (Measurable.mul (ENNReal.measurable_ofReal.comp measurable_fst)
      (Measurable.mul measurable_const (prof_measurable hα.le hg)))).mono_measure
        Measure.restrict_le_self
  rw [show (∫⁻ t : ℝ, ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal r * (ENNReal.ofReal (2 * Real.pi) * prof α B g r t))
      = ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ),
          ENNReal.ofReal p.1 * (ENNReal.ofReal (2 * Real.pi) * prof α B g p.1 p.2) from by
    have h := (setLIntegral_prod_symm (f := fun p : ℝ × ℝ =>
        ENNReal.ofReal p.1 * (ENNReal.ofReal (2 * Real.pi) * prof α B g p.1 p.2)) hmeasH).symm
    simpa only [MeasureTheory.Measure.restrict_univ,
      show (MeasureTheory.volume : Measure (ℝ × ℝ))
        = (MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume : Measure ℝ) from rfl]
      using h]
  -- the polar change of variables in the half plane `r > 0`
  rw [halfline_step hα hB hg]
  -- reassociate and pull the constant `2π` out of the integral over the domain
  rw [show (∫⁻ q in Adom, ENNReal.ofReal (q.1 ^ 2 * Real.cos q.2) *
        (ENNReal.ofReal (2 * Real.pi) * g (q.1 ^ (3 * α) / B) q.2))
      = ∫⁻ q in Adom, ENNReal.ofReal (2 * Real.pi) *
          (ENNReal.ofReal (q.1 ^ 2 * Real.cos q.2) * g (q.1 ^ (3 * α) / B) q.2) from
    setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun q _ => by
      rw [← mul_assoc, mul_comm (ENNReal.ofReal (q.1 ^ 2 * Real.cos q.2))
        (ENNReal.ofReal (2 * Real.pi)), mul_assoc])]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- the radial substitution `ρ = (B s)^{1/(3α)}`
  rw [scaling_step hα hB hg]
  -- combine the two constants
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  congr 1
  ring_nf

end Work.FTS.FireFix.Clauses
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.GalApprox.pzIter_pthIter_comm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter

namespace Work.FTS.GalBasis.GalApprox

namespace PzIterAux

/-! ## Smoothness of the iterated slice derivatives -/

/-- `∂_z` lowers the smoothness class by one.  (On a neighbourhood of the point, the
slice derivative `pz G` is the `(1,0)`-component of `fderiv ℝ (uncurry G)`.) -/
lemma pz_contDiffAt {G : ℝ → ℝ → ℝ} {y : ℝ × ℝ} {m : ℕ}
    (h : ContDiffAt ℝ (m + 1) (Function.uncurry G) y) :
    ContDiffAt ℝ m (Function.uncurry (Work.Spaces.pz G)) y := by
  have hfd : ContDiffAt ℝ m (fderiv ℝ (Function.uncurry G)) y := by
    have := ContDiffAt.fderiv_right (𝕜 := ℝ) h
      (by norm_num : ((m : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((m + 1 : ℕ) : ℕ∞))
    simpa using this
  have hfun : ContDiffAt ℝ m
      (fun y' : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) y') (1, 0)) y :=
    hfd.clm_apply contDiffAt_const
  refine ContDiffAt.congr_of_eventuallyEq hfun ?_
  filter_upwards [h.eventually (by simp)] with y' hy'
  have hd : DifferentiableAt ℝ (Function.uncurry G) y' := hy'.differentiableAt (by norm_num)
  have := Work.Spaces.deriv_slice_fst (Function.uncurry G) y'.1 y'.2 hd
  show Work.Spaces.pz G y'.1 y'.2 = _
  rw [show Work.Spaces.pz G y'.1 y'.2
      = deriv (fun z' => Function.uncurry G (z', y'.2)) y'.1 from rfl]
  exact this

/-- `∂_θ` lowers the smoothness class by one. -/
lemma pth_contDiffAt {G : ℝ → ℝ → ℝ} {y : ℝ × ℝ} {m : ℕ}
    (h : ContDiffAt ℝ (m + 1) (Function.uncurry G) y) :
    ContDiffAt ℝ m (Function.uncurry (Work.Spaces.pth G)) y := by
  have hfd : ContDiffAt ℝ m (fderiv ℝ (Function.uncurry G)) y := by
    have := ContDiffAt.fderiv_right (𝕜 := ℝ) h
      (by norm_num : ((m : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((m + 1 : ℕ) : ℕ∞))
    simpa using this
  have hfun : ContDiffAt ℝ m
      (fun y' : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) y') (0, 1)) y :=
    hfd.clm_apply contDiffAt_const
  refine ContDiffAt.congr_of_eventuallyEq hfun ?_
  filter_upwards [h.eventually (by simp)] with y' hy'
  have hd : DifferentiableAt ℝ (Function.uncurry G) y' := hy'.differentiableAt (by norm_num)
  have := Work.Spaces.deriv_slice_snd (Function.uncurry G) y'.1 y'.2 hd
  show Work.Spaces.pth G y'.1 y'.2 = _
  rw [show Work.Spaces.pth G y'.1 y'.2
      = deriv (fun θ' => Function.uncurry G (y'.1, θ')) y'.2 from rfl]
  exact this

/-- `∂_z^i` lowers the smoothness class by `i`. -/
lemma pzIter_contDiffAt {F : ℝ → ℝ → ℝ} {y : ℝ × ℝ} :
    ∀ (i m : ℕ), ContDiffAt ℝ (m + i) (Function.uncurry F) y →
      ContDiffAt ℝ m (Function.uncurry (Work.Spaces.pzIter i F)) y := by
  intro i
  induction i with
  | zero => intro m h; simpa using h
  | succ i ih =>
      intro m h
      have h' : ContDiffAt ℝ ((m + 1) + i) (Function.uncurry F) y := by
        convert h using 1
        push_cast
        ring
      have hG : ContDiffAt ℝ (m + 1) (Function.uncurry (Work.Spaces.pzIter i F)) y :=
        ih (m + 1) h'
      exact pz_contDiffAt hG

/-- `∂_θ^j` lowers the smoothness class by `j`. -/
lemma pthIter_contDiffAt {F : ℝ → ℝ → ℝ} {y : ℝ × ℝ} :
    ∀ (j m : ℕ), ContDiffAt ℝ (m + j) (Function.uncurry F) y →
      ContDiffAt ℝ m (Function.uncurry (Work.Spaces.pthIter j F)) y := by
  intro j
  induction j with
  | zero => intro m h; simpa using h
  | succ j ih =>
      intro m h
      have h' : ContDiffAt ℝ ((m + 1) + j) (Function.uncurry F) y := by
        convert h using 1
        push_cast
        ring
      have hG : ContDiffAt ℝ (m + 1) (Function.uncurry (Work.Spaces.pthIter j F)) y :=
        ih (m + 1) h'
      exact pth_contDiffAt hG

/-! ## Congruence of the slice derivatives -/

/-- The slice derivative `∂_z` only depends on the germ of the function. -/
lemma pz_congr_ev {g g' : ℝ → ℝ → ℝ} {y : ℝ × ℝ}
    (h : Function.uncurry g =ᶠ[𝓝 y] Function.uncurry g') :
    Work.Spaces.pz g y.1 y.2 = Work.Spaces.pz g' y.1 y.2 := by
  have hd := (h.comp_tendsto (Continuous.prodMk_left y.2).continuousAt).deriv_eq
  show deriv (fun z' => g z' y.2) y.1 = deriv (fun z' => g' z' y.2) y.1
  exact hd

/-- The slice derivative `∂_θ` only depends on the germ of the function. -/
lemma pth_congr_ev {g g' : ℝ → ℝ → ℝ} {y : ℝ × ℝ}
    (h : Function.uncurry g =ᶠ[𝓝 y] Function.uncurry g') :
    Work.Spaces.pth g y.1 y.2 = Work.Spaces.pth g' y.1 y.2 := by
  have hd := (h.comp_tendsto (Continuous.prodMk_right y.1).continuousAt).deriv_eq
  show deriv (fun θ' => g y.1 θ') y.2 = deriv (fun θ' => g' y.1 θ') y.2
  exact hd

/-! ## Moving a single `∂_z` through `j` iterated `∂_θ`'s -/

/-- One `∂_z` can be moved through `j` iterated `∂_θ`'s, at the cost of one order of
smoothness (Clairaut at every stage). -/
lemma pz_pthIter_eq : ∀ (j : ℕ) (F : ℝ → ℝ → ℝ) (y : ℝ × ℝ),
    ContDiffAt ℝ (j + 1) (Function.uncurry F) y →
    Work.Spaces.pz (Work.Spaces.pthIter j F) y.1 y.2
      = Work.Spaces.pthIter j (Work.Spaces.pz F) y.1 y.2 := by
  intro j
  induction j with
  | zero => intro F y h; rfl
  | succ j ih =>
      intro F y h
      have hG : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pthIter j F)) y := by
        have := pthIter_contDiffAt (F := F) (y := y) j 2 (by
          convert h using 1
          push_cast
          ring)
        simpa using this
      have hcl := Work.Spaces.pz_pth_comm (f := Work.Spaces.pthIter j F) hG
      have hev : Function.uncurry (Work.Spaces.pz (Work.Spaces.pthIter j F)) =ᶠ[𝓝 y]
          Function.uncurry (Work.Spaces.pthIter j (Work.Spaces.pz F)) := by
        filter_upwards [h.eventually (by simp)] with y' hy'
        exact ih F y' (hy'.of_le (by norm_num))
      have hstep := pth_congr_ev hev
      show Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pthIter j F)) y.1 y.2
          = Work.Spaces.pth (Work.Spaces.pthIter j (Work.Spaces.pz F)) y.1 y.2
      rw [hcl, hstep]

/-! ## The main commutation -/

/-- The general statement: if `F` is `C^n` at `y` and `i + j ≤ n` then
`∂_z^i ∂_θ^j F = ∂_θ^j ∂_z^i F` at `y`.  (Stated with a fixed `n` so that the
smoothness class is a single natural number, which keeps the "eventually" arguments
clean.) -/
lemma pzIter_pthIter_comm_aux (n : ℕ) :
    ∀ (i j : ℕ) (F : ℝ → ℝ → ℝ) (y : ℝ × ℝ), i + j ≤ n →
      ContDiffAt ℝ n (Function.uncurry F) y →
      Work.Spaces.pzIter i (Work.Spaces.pthIter j F) y.1 y.2
        = Work.Spaces.pthIter j (Work.Spaces.pzIter i F) y.1 y.2 := by
  intro i
  induction i with
  | zero => intro j F y hij h; rfl
  | succ i ih =>
      intro j F y hij h
      have hij' : i + j ≤ n := by omega
      -- the induction hypothesis at nearby points, as an eventual equality
      have hev : Function.uncurry (Work.Spaces.pzIter i (Work.Spaces.pthIter j F))
          =ᶠ[𝓝 y]
          Function.uncurry (Work.Spaces.pthIter j (Work.Spaces.pzIter i F)) := by
        filter_upwards [h.eventually (by simp)] with y' hy'
        exact ih j F y' hij' hy'
      have hpz := pz_congr_ev hev
      -- move the outer `∂_z` through the remaining `j` iterated `∂_θ`'s
      have hG : ContDiffAt ℝ (j + 1) (Function.uncurry (Work.Spaces.pzIter i F)) y := by
        have h1 : ContDiffAt ℝ ((j + 1) + i) (Function.uncurry F) y :=
          h.of_le (by exact_mod_cast (by omega : (j + 1) + i ≤ n))
        exact pzIter_contDiffAt (F := F) (y := y) i (j + 1) h1
      have hA := pz_pthIter_eq j (Work.Spaces.pzIter i F) y hG
      rw [Work.Spaces.pzIter_succ, hpz]
      exact hA

end PzIterAux

theorem pzIter_pthIter_comm {F : ℝ → ℝ → ℝ} {z θ : ℝ} {n : ℕ}
    (h : ContDiffAt ℝ n (Function.uncurry F) (z, θ)) (i j : ℕ) (hij : i + j ≤ n) :
    Work.Spaces.pzIter i (Work.Spaces.pthIter j F) z θ =
      Work.Spaces.pthIter j (Work.Spaces.pzIter i F) z θ :=
  PzIterAux.pzIter_pthIter_comm_aux n i j F (z, θ) hij h

end Work.FTS.GalBasis.GalApprox
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cut.sliceGamma =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cut

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The measure-theoretic helpers -/




private theorem ofReal_intervalIntegral_eq_lintegral {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfint : IntegrableOn f (Set.Icc a b)) (hfnn : ∀ x ∈ Set.Icc a b, 0 ≤ f x) :
    ENNReal.ofReal (∫ x in a..b, f x) = ∫⁻ x in Set.Icc a b, ENNReal.ofReal (f x) := by
  rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfint
    ((ae_restrict_iff' measurableSet_Icc).mpr
      (Filter.Eventually.of_forall (fun x hx => hfnn x hx)))


/-! ## The main theorem -/


end Work.FTS.GalBasis.cut
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.exists_poly2_uniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Uniform approximation of a continuous function on a rectangle by two-variable polynomials

We prove that every function `h : ℝ → ℝ → ℝ` which is continuous on a rectangle
`[A,B] × [C,D]` can be uniformly approximated there by a finite sum of two-variable monomials
`c * z ^ p * θ ^ q`, with `p q : ℕ` and `c : ℝ`.

The argument is the Stone–Weierstrass theorem.  Writing `s` for the rectangle, the monomial
sums (`Work.FTS.GalBasis.IsPolySum`) form a subalgebra `polySumSubalgebra s` of `C(s, ℝ)`
which contains the two coordinate projections and hence separates points; therefore it is
dense, and `exists_mem_subalgebra_near_continuousMap_of_separatesPoints` provides, for every
`ε > 0`, a monomial sum within `ε` of `h`.  Finally the `Fintype`-indexed sum is reshaped into
a `Fin m`-indexed one (`exists_fin_monomial_sum`), which is the form required.
-/

namespace Work.FTS.GalBasis

open scoped BigOperators

variable (s : Set (ℝ × ℝ))











end Work.FTS.GalBasis
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.DthIter_sliceX =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Set Filter

namespace Work.FTS.H2.DivQ

/-! ## Auxiliary one-variable facts for the substitution `x = sin(2θ)`

Everything is proved for points of the open interval `(-1,1)`, i.e. under the map `thetaOf` for
`θ ∈ (-π/4, π/4)`; the target statement only needs the sub-interval `(0, xNear)`. -/

/-- `thetaOf` is differentiable on `(-1,1)` with derivative `1/(2√(1-x²))`. -/
private lemma hasDerivAt_thetaOf {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt thetaOf (1 / (2 * Real.sqrt (1 - x ^ 2))) x := by
  have h1 : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
    Real.hasDerivAt_arcsin (ne_of_gt hx.1) (ne_of_lt hx.2)
  have h2 : HasDerivAt (fun y => Real.arcsin y / 2) ((1 / Real.sqrt (1 - x ^ 2)) / 2) x :=
    h1.div_const 2
  have heq : (1 / Real.sqrt (1 - x ^ 2)) / 2 = 1 / (2 * Real.sqrt (1 - x ^ 2)) := by
    have hs : Real.sqrt (1 - x ^ 2) ≠ 0 := by
      apply ne_of_gt; apply Real.sqrt_pos.mpr; nlinarith [hx.1, hx.2]
    field_simp
  rw [heq] at h2
  exact h2

/-- On the near interval, `thetaOf` lands in the angular interval `(0,π/2)` on which `h` is
smooth. -/
private lemma thetaOf_mem {x : ℝ} (hx : x ∈ Set.Ioo 0 xNear) :
    thetaOf x ∈ Set.Ioo 0 (Real.pi / 2) := by
  have ha0 : 0 < Real.arcsin x := Real.arcsin_pos.mpr hx.1
  have ha2 : Real.arcsin x ≤ Real.pi / 2 := (Real.arcsin_mem_Icc x).2
  constructor <;> simp only [thetaOf] <;> linarith

/-- **The single transport step.**  For any function `U` differentiable at `thetaOf x`
(`x ∈ (-1,1)`), applying `D_θ = sin(2θ)∂_θ` to `U` at `thetaOf x` is the same as applying `Gop`
to the reparametrised function `sliceX U = U ∘ thetaOf` at `x`.  This is the chain rule
`deriv (U ∘ thetaOf) x = deriv U (thetaOf x) · deriv thetaOf x` combined with
`sin (2 thetaOf x) = x`, `cos (2 thetaOf x) = √(1-x²) = kappa x`. -/
private lemma Dth1_thetaOf_eq_Gop (U : ℝ → ℝ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hU : DifferentiableAt ℝ U (thetaOf x)) :
    Work.Elliptic.Dth1 U (thetaOf x) = Gop (sliceX U) x := by
  have hs' : Real.sqrt (1 - x ^ 2) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr; nlinarith [hx.1, hx.2]
  have hsin : Real.sin (2 * thetaOf x) = x := by
    have h2 : 2 * thetaOf x = Real.arcsin x := by simp only [thetaOf]; ring
    rw [h2, Real.sin_arcsin (by linarith [hx.1]) (by linarith [hx.2])]
  have hcos : Real.cos (2 * thetaOf x) = Real.sqrt (1 - x ^ 2) := by
    have h2 : 2 * thetaOf x = Real.arcsin x := by simp only [thetaOf]; ring
    rw [h2, Real.cos_arcsin]
  have htheta := hasDerivAt_thetaOf hx
  have hchain : deriv (sliceX U) x = deriv U (thetaOf x) * (1 / (2 * Real.sqrt (1 - x ^ 2))) :=
    (HasDerivAt.comp x (hU.hasDerivAt) htheta).deriv
  have key : Work.Elliptic.Dth1 U (thetaOf x) = x * deriv U (thetaOf x) := by
    simp only [Work.Elliptic.Dth1, hsin]
  have key2 : Gop (sliceX U) x = 2 * Real.sqrt (1 - x ^ 2) * (x * deriv (sliceX U) x) := by
    simp only [Gop, kappa, hcos]
  rw [key, key2, hchain]
  field_simp

/-- `Gop` only sees `u` through `deriv u x`, so it is insensitive to replacing `u` by a function
that agrees with it near `x`. -/
private lemma Gop_congr_deriv {u v : ℝ → ℝ} {x : ℝ} (h : u =ᶠ[𝓝 x] v) :
    Gop u x = Gop v x := by
  have hd : deriv u x = deriv v x := Filter.EventuallyEq.deriv_eq h
  simp only [Gop, hd]

/-- `Dth1Iter m` of a function of class `C^∞` on an open set is again of class `C^∞` there. -/
private lemma contDiffOn_Dth1Iter_prv {s : Set ℝ} (hs : IsOpen s) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) :
    ∀ m : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (Work.Elliptic.Dth1Iter m f) s := by
  intro m
  induction m with
  | zero => simpa using hf
  | succ m ih =>
    rw [Work.Elliptic.Dth1Iter_succ]
    have hsin : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Real.sin (2 * θ)) s :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
    have hder : ContDiffOn ℝ (⊤ : ℕ∞) (deriv (Work.Elliptic.Dth1Iter m f)) s :=
      ih.deriv_of_isOpen hs (by simp)
    exact hsin.mul hder

/-- **Transport of the slice-level `D_θ`-iterates to the coordinate `x = sin(2θ)`.**  For `h` of
class `C^∞` on the open angular interval `(0,π/2)`,

  `Dth1Iter i h (thetaOf x) = (Gop^[i]) (sliceX h) x`  for all `x ∈ (0, xNear)`,

in the vocabulary of `Work.FTS.H2.DivQ.Defs` (`thetaOf x = arcsin(x)/2`, `sliceX h x = h (thetaOf x)`,
`Gop u x = 2 κ(x) · (x · deriv u x)`, `κ x = cos(2 thetaOf x) = √(1-x²)`, `xNear = sin(π/4) = 1/√2`)
and `Work.Elliptic.Dth1Iter`, the one-dimensional iterate of `D_θ = sin(2θ) ∂_θ` on slices.

ROUTE.  Prove `Set.EqOn … (Set.Ioo 0 xNear)` by induction on `i`.

* One-variable facts for `x ∈ (-1,1)`: `Real.sin (2 * thetaOf x) = x` (`Real.sin_arcsin`),
  `Real.cos (2 * thetaOf x) = Real.sqrt (1 - x^2) = kappa x` (`Real.cos_arcsin`), and
  `deriv thetaOf x = 1/(2 * Real.sqrt (1-x^2))` (`Real.deriv_arcsin`).
* Base `i = 0`: `rfl`.
* Step: `Dth1Iter (i+1) h = Dth1 (Dth1Iter i h)` with `Dth1 u = sin(2·) * deriv u`; for
  `U := Dth1Iter i h` (again `C^∞` on the open interval) the chain rule
  `deriv (U ∘ thetaOf) x = deriv U (thetaOf x) * deriv thetaOf x` and `sin (2 * thetaOf x) = x`
  give `Dth1 U (thetaOf x) = 2 * kappa x * (x * deriv (U ∘ thetaOf) x) = Gop (U ∘ thetaOf) x`.
  The induction hypothesis identifies `U ∘ thetaOf` with `Gop^[i] (sliceX h)` on `(0,xNear)`;
  since both are the restrictions of differentiable functions, replace them and use
  `Function.iterate_succ_apply'` (`Gop^[i+1] = Gop ∘ Gop^[i]`). -/
theorem DthIter_sliceX (i : ℕ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    Set.EqOn (fun x => Work.Elliptic.Dth1Iter i h (thetaOf x)) ((Gop^[i]) (sliceX h))
      (Set.Ioo 0 xNear) := by
  induction i with
  | zero => intro x hx; rfl
  | succ i ih =>
    intro x hx
    show Work.Elliptic.Dth1Iter (i + 1) h (thetaOf x) = (Gop^[i + 1]) (sliceX h) x
    have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := by
      refine ⟨by linarith [hx.1], ?_⟩
      have hxN : xNear ≤ 1 := Real.sin_le_one _
      linarith [hx.2]
    have hmem : thetaOf x ∈ Set.Ioo 0 (Real.pi / 2) := thetaOf_mem hx
    have hU : DifferentiableAt ℝ (Work.Elliptic.Dth1Iter i h) (thetaOf x) :=
      ((contDiffOn_Dth1Iter_prv isOpen_Ioo hsm i).contDiffAt
        (isOpen_Ioo.mem_nhds hmem)).differentiableAt (by simp)
    have hstep : Work.Elliptic.Dth1Iter (i + 1) h (thetaOf x)
        = Gop (sliceX (Work.Elliptic.Dth1Iter i h)) x := by
      rw [Work.Elliptic.Dth1Iter_succ]
      exact Dth1_thetaOf_eq_Gop _ hxI hU
    rw [hstep, Function.iterate_succ_apply']
    exact Gop_congr_deriv (by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      simpa only [sliceX] using ih hy)

end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.aCoeff_expansion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

/-!
# The expansion of `G^i (2κ ∂_x f)` in powers of `x`

This file proves `aCoeff_expansion`, the `x`-coordinate counterpart of `bCoeff_expansion`:

  `(G^i (2κ ∂_x f)) x = Σ_{l ∈ range (i+1)} aCoeff i l x · (x^l · ∂_x^{l+1} f x)`

for `f` of class `C^∞` on `(0, xNear)`.  The proof is an induction on `i`; the pieces are

* `CoeffAux.deriv_sum_expansion` — the term-by-term derivative of `Σ_l c l y · (y^l · u l y)`;
* `CoeffAux.aCoeff_term_ident` — the elementary regrouping of one summand, which is the
  recursion `a (i+1) l = 2κ (x (a i l)' + l a i l) + 2κ a i (l-1)`;
* `CoeffAux.sum_step_reindex` — the index bookkeeping turning `Σ_{l ≤ i}` into `Σ_{j ≤ i+1}`;
* `aCoeff_contDiffOn`, `aCoeff_eq_zero_of_lt` — smoothness of the coefficients and the
  vanishing `a i j = 0` for `j > i`, needed to differentiate the induction hypothesis and to
  close the top index;
* `CoeffAux.contDiffOn_iteratedDeriv` — `iteratedDeriv n f` is again `C^∞` on an open set.

The mathematical heart is `aCoeff_step`, which performs one induction step for an arbitrary
point, and then `aCoeff_expansion` assembles the induction.
-/



namespace CoeffAux

/-- Differentiate a finite sum of the form `y ↦ c l y * (y^l * u l y)` term by term at a point
where every component is differentiable. -/
theorem deriv_sum_expansion (N : ℕ) (c u : ℕ → ℝ → ℝ) {x : ℝ}
    (hc : ∀ l, DifferentiableAt ℝ (c l) x) (hu : ∀ l, DifferentiableAt ℝ (u l) x) :
    deriv (fun y => ∑ l ∈ Finset.range (N + 1), c l y * (y ^ l * u l y)) x
      = ∑ l ∈ Finset.range (N + 1),
          (deriv (c l) x * (x ^ l * u l x)
            + c l x * ((l : ℝ) * x ^ (l - 1) * u l x + x ^ l * deriv (u l) x)) := by
  have hd : ∀ l, DifferentiableAt ℝ (fun y => c l y * (y ^ l * u l y)) x := fun l =>
    DifferentiableAt.mul (hc l) (DifferentiableAt.mul (differentiableAt_pow l) (hu l))
  have hfun : (fun y => ∑ l ∈ Finset.range (N + 1), c l y * (y ^ l * u l y))
      = ∑ l ∈ Finset.range (N + 1), fun y => c l y * (y ^ l * u l y) := by
    ext y; simp
  rw [hfun, deriv_sum (fun l _ => hd l)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have h1 : deriv (fun y => c l y * (y ^ l * u l y)) x
      = deriv (c l) x * (x ^ l * u l x) + c l x * deriv (fun y => y ^ l * u l y) x :=
    deriv_mul (hc l) (DifferentiableAt.mul (differentiableAt_pow l) (hu l))
  have h2 : deriv (fun y => y ^ l * u l y) x
      = (l : ℝ) * x ^ (l - 1) * u l x + x ^ l * deriv (u l) x := by
    show deriv ((fun y : ℝ => y ^ l) * u l) x
      = (l : ℝ) * x ^ (l - 1) * u l x + x ^ l * deriv (u l) x
    rw [deriv_mul (differentiableAt_pow l) (hu l)]
    rw [show deriv (fun y : ℝ => y ^ l) x = (l : ℝ) * x ^ (l - 1) from (hasDerivAt_pow l x).deriv]
  rw [h1, h2]

/-- The elementary identity behind the recursion for `aCoeff`: differentiating the summand
`c · (y^l · d) + a · (l y^(l-1) d + y^l e)` and multiplying by `k · y` regroups the result into
the `l`-th and `(l+1)`-st coefficient slots. -/
theorem aCoeff_term_ident (k y a c d e : ℝ) (l : ℕ) :
    k * (y * (c * (y ^ l * d) + a * ((l : ℝ) * y ^ (l - 1) * d + y ^ l * e)))
      = (k * (y * c + (l : ℝ) * a)) * (y ^ l * d) + (k * a) * (y ^ (l + 1) * e) := by
  rcases l with _ | m
  · ring
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

/-- Reindexing identity: a sum of `P l * T l + Q l * T (l+1)` equals the sum over one more index
of `(P j + (if j = 0 then 0 else Q (j-1))) * T j`, given `P (N+1) = 0` (the hypothesis that makes
the top coefficient vanish, as it does for `aCoeff`). -/
theorem sum_step_reindex (N : ℕ) (P Q T : ℕ → ℝ) (hP : P (N + 1) = 0) :
    (∑ l ∈ Finset.range (N + 1), (P l * T l + Q l * T (l + 1)))
      = ∑ j ∈ Finset.range (N + 2), (P j + (if j = 0 then 0 else Q (j - 1))) * T j := by
  have hL : (∑ l ∈ Finset.range (N + 1), (P l * T l + Q l * T (l + 1)))
      = (∑ l ∈ Finset.range N, (P l * T l + Q l * T (l + 1))) + P N * T N + Q N * T (N + 1) := by
    rw [Finset.sum_range_succ]
    ring
  have hR : (∑ j ∈ Finset.range (N + 2), (P j + (if j = 0 then 0 else Q (j - 1))) * T j)
      = (∑ j ∈ Finset.range N, P (j + 1) * T (j + 1)) + (∑ j ∈ Finset.range N, Q j * T (j + 1))
          + P 0 * T 0 + Q N * T (N + 1) := by
    rw [Finset.sum_range_succ]
    rw [show (P (N + 1) + (if N + 1 = 0 then 0 else Q (N + 1 - 1))) * T (N + 1)
        = Q N * T (N + 1) by
      rw [hP]; simp]
    rw [Finset.sum_range_succ']
    rw [show (P 0 + (if (0 : ℕ) = 0 then 0 else Q (0 - 1))) * T 0 = P 0 * T 0 by simp]
    have hcongr : (∑ k ∈ Finset.range N,
          (P (k + 1) + (if k + 1 = 0 then 0 else Q (k + 1 - 1))) * T (k + 1))
        = (∑ k ∈ Finset.range N, (P (k + 1) * T (k + 1) + Q k * T (k + 1))) :=
      Finset.sum_congr rfl (fun k _ => by
        simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]; ring)
    rw [hcongr]
    rw [Finset.sum_add_distrib]
  rw [hL, hR]
  have hkey : (∑ j ∈ Finset.range N, P (j + 1) * T (j + 1)) + P 0 * T 0
      = (∑ j ∈ Finset.range N, P j * T j) + P N * T N := by
    rw [← Finset.sum_range_succ' (fun j => P j * T j) N]
    rw [Finset.sum_range_succ (fun j => P j * T j) N]
  have hkey' : (∑ j ∈ Finset.range N, P (j + 1) * T (j + 1))
      = (∑ j ∈ Finset.range N, P j * T j) + P N * T N - P 0 * T 0 := by linarith [hkey]
  rw [hkey', Finset.sum_add_distrib]
  ring

/-- Every iterated derivative of a function of class `C^∞` on an open set is again of class `C^∞`
there. -/
theorem contDiffOn_iteratedDeriv {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv n f) s := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen hs (by simp)

end CoeffAux

/-- The coefficient `aCoeff i j` vanishes identically once `j > i`: the `i`-th iterate
`G^i (2κ ∂_x f)` only involves `∂_x^{1}, …, ∂_x^{i+1} f`.  (This is the input that closes the
top index of the expansion at each induction step.) -/
theorem aCoeff_eq_zero_of_lt {i j : ℕ} (h : i < j) :
    aCoeff i j = fun _ => (0 : ℝ) := by
  induction i generalizing j with
  | zero =>
    funext x
    show (fun x => if j = 0 then 2 * kappa x else 0) x = 0
    simp [show j ≠ 0 by omega]
  | succ i ih =>
    have h1 : i < j := by omega
    have h2 : i < j - 1 := by omega
    funext x
    show (fun x => 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
      + (if j = 0 then 0 else 2 * kappa x * aCoeff i (j - 1) x)) x = 0
    rw [ih h1, ih h2]
    simp [show j ≠ 0 by omega]

/-- Every coefficient `aCoeff i j` is of class `C^∞` on the near interval `(0, xNear)`: it is
built from `κ = cos ∘ arcsin` and its derivatives by the recursion. -/
theorem aCoeff_contDiffOn (i j : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (aCoeff i j) (Set.Ioo 0 xNear) := by
  have hxNear1 : xNear < 1 := by
    unfold xNear
    rw [Real.sin_pi_div_four]
    have h : Real.sqrt 2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    linarith
  have hk : ContDiffOn ℝ (⊤ : ℕ∞) kappa (Set.Ioo 0 xNear) := by
    have hfun : kappa = fun x => Real.cos (Real.arcsin x) := by
      funext x
      show Real.cos (2 * thetaOf x) = Real.cos (Real.arcsin x)
      rw [show 2 * thetaOf x = Real.arcsin x by unfold thetaOf; ring]
    rw [hfun]
    intro x hx
    exact (Real.contDiff_cos.contDiffAt.comp x
      (Real.contDiffAt_arcsin (by linarith [hx.1])
        (by linarith [hx.2, hxNear1]))).contDiffWithinAt
  have key : ∀ i j : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (aCoeff i j) (Set.Ioo 0 xNear) := by
    intro i
    induction i with
    | zero =>
      intro j
      by_cases hj : j = 0
      · have hf0 : aCoeff 0 j = fun x => 2 * kappa x := by
          funext x
          show (fun x => if j = 0 then 2 * kappa x else 0) x = 2 * kappa x
          simp [hj]
        rw [hf0]
        exact contDiffOn_const.mul hk
      · have hf0 : aCoeff 0 j = fun _ => (0 : ℝ) := by
          funext x
          show (fun x => if j = 0 then 2 * kappa x else 0) x = 0
          simp [hj]
        rw [hf0]
        exact contDiffOn_const
    | succ i ih =>
      intro j
      have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (deriv (aCoeff i j)) (Set.Ioo 0 xNear) :=
        (ih j).deriv_of_isOpen isOpen_Ioo (by simp)
      by_cases hj : j = 0
      · have hfs : aCoeff (i + 1) j
            = fun x => 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x) := by
          funext x
          show (fun x => 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
            + (if j = 0 then 0 else 2 * kappa x * aCoeff i (j - 1) x)) x
            = 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
          simp [hj]
        rw [hfs]
        exact ((contDiffOn_const.mul hk).mul
          ((contDiffOn_id.mul h1).add (contDiffOn_const.mul (ih j))))
      · have hfs : aCoeff (i + 1) j
            = fun x => 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
                + 2 * kappa x * aCoeff i (j - 1) x := by
          funext x
          show (fun x => 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
            + (if j = 0 then 0 else 2 * kappa x * aCoeff i (j - 1) x)) x
            = 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
              + 2 * kappa x * aCoeff i (j - 1) x
          simp [hj]
        rw [hfs]
        exact ((contDiffOn_const.mul hk).mul
          ((contDiffOn_id.mul h1).add (contDiffOn_const.mul (ih j)))).add
          ((contDiffOn_const.mul hk).mul (ih (j - 1)))
  exact key i j

/-- **One induction step of `aCoeff_expansion`.**  If the expansion is known at level `i`,
differentiating it (`G = 2κ x ∂_x`) and regrouping produces the expansion at level `i+1`. -/
theorem aCoeff_step {f : ℝ → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo 0 xNear))
    (i : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo 0 xNear) :
    2 * kappa x * (x * deriv (fun y => ∑ l ∈ Finset.range (i + 1),
        aCoeff i l y * (y ^ l * iteratedDeriv (l + 1) f y)) x)
      = ∑ l ∈ Finset.range (i + 2), aCoeff (i + 1) l x * (x ^ l * iteratedDeriv (l + 1) f x) := by
  have hc : ∀ l, DifferentiableAt ℝ (aCoeff i l) x := fun l =>
    ((aCoeff_contDiffOn i l).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hx)
  have hu : ∀ l, DifferentiableAt ℝ (iteratedDeriv (l + 1) f) x := fun l =>
    ((CoeffAux.contDiffOn_iteratedDeriv isOpen_Ioo hf (l + 1)).differentiableOn
      (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hx)
  have hd := CoeffAux.deriv_sum_expansion i (fun l => aCoeff i l)
    (fun l => iteratedDeriv (l + 1) f) hc hu
  have hD : ∀ l, deriv (iteratedDeriv (l + 1) f) x = iteratedDeriv (l + 2) f x := fun l =>
    congrFun (iteratedDeriv_succ (n := l + 1) (f := f)).symm x
  have hd' : deriv (fun y => ∑ l ∈ Finset.range (i + 1),
        aCoeff i l y * (y ^ l * iteratedDeriv (l + 1) f y)) x
      = ∑ l ∈ Finset.range (i + 1), (deriv (aCoeff i l) x * (x ^ l * iteratedDeriv (l + 1) f x)
          + aCoeff i l x * ((l : ℝ) * x ^ (l - 1) * iteratedDeriv (l + 1) f x
              + x ^ l * iteratedDeriv (l + 2) f x)) := by
    rw [hd]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hD l]
  rw [hd']
  have hL : 2 * kappa x * (x * (∑ l ∈ Finset.range (i + 1),
        (deriv (aCoeff i l) x * (x ^ l * iteratedDeriv (l + 1) f x)
          + aCoeff i l x * ((l : ℝ) * x ^ (l - 1) * iteratedDeriv (l + 1) f x
              + x ^ l * iteratedDeriv (l + 2) f x))))
      = ∑ l ∈ Finset.range (i + 1),
          ((2 * kappa x * (x * deriv (aCoeff i l) x + (l : ℝ) * aCoeff i l x))
              * (x ^ l * iteratedDeriv (l + 1) f x)
            + (2 * kappa x * aCoeff i l x) * (x ^ (l + 1) * iteratedDeriv (l + 2) f x)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    exact CoeffAux.aCoeff_term_ident (2 * kappa x) x (aCoeff i l x) (deriv (aCoeff i l) x)
      (iteratedDeriv (l + 1) f x) (iteratedDeriv (l + 2) f x) l
  have hP : 2 * kappa x * (x * deriv (aCoeff i (i + 1)) x
      + ((i + 1 : ℕ) : ℝ) * aCoeff i (i + 1) x) = 0 := by
    rw [aCoeff_eq_zero_of_lt (Nat.lt_succ_self i)]
    simp
  have hsum := CoeffAux.sum_step_reindex i
    (fun j => 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x))
    (fun j => 2 * kappa x * aCoeff i j x) (fun j => x ^ j * iteratedDeriv (j + 1) f x)
    (show (fun j => 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)) (i + 1)
      = 0 from hP)
  have hR : (∑ j ∈ Finset.range (i + 2),
        aCoeff (i + 1) j x * (x ^ j * iteratedDeriv (j + 1) f x))
      = ∑ j ∈ Finset.range (i + 2),
          ((2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x))
            + (if j = 0 then 0 else 2 * kappa x * aCoeff i (j - 1) x))
              * (x ^ j * iteratedDeriv (j + 1) f x) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    show ((fun x => 2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
        + (if j = 0 then 0 else 2 * kappa x * aCoeff i (j - 1) x)) x)
          * (x ^ j * iteratedDeriv (j + 1) f x)
      = ((2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x))
          + (if j = 0 then 0 else 2 * kappa x * aCoeff i (j - 1) x))
            * (x ^ j * iteratedDeriv (j + 1) f x)
    rfl
  rw [hL, hR]
  exact hsum

/-- **The expansion of `G^i (2κ ∂_x f)` in powers of `x`.**  With `aCoeff` as defined in
`Work.FTS.H2.DivQ.Defs` (`a 0 0 = 2κ`, `a 0 j = 0` for `j ≠ 0`, and the same recursion as `bCoeff`),

for every `f` of class `C^∞` on `(0, x₁)` (`x₁ = xNear = sin(π/4)`) and every `x ∈ (0,x₁)`:

  `(G^i (fun y => 2 κ y * ∂_x f y)) x = Σ_{l ∈ range (i+1)} a i l x · (x^l · ∂_x^{l+1} f (x))`.

This is the `x`-form of `D_θ^i(∂_θ h)(arcsin x / 2)`: indeed `∂_θ h(θ(x)) = 2κ(x) ∂_x(sliceX h) x`.

ROUTE.  Same as `bCoeff_expansion`, by induction on `i`, with the initial datum `u_0 = 2κ ∂_x f`
and the product rule `∂_x(2κ y ∂_x f y) = 2κ' y ∂_x f y + 2κ y ∂_x² f y`; the induction hypothesis
expresses `G^i(2κ∂_x f)` as `Σ_l a i l x · x^l ∂_x^{l+1} f x`, and `G` adds one more `∂_x` (the
`l ↦ l+1` re-indexing) and differentiates the coefficient (the `a (i+1) l` recursion). -/
theorem aCoeff_expansion (i : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo 0 xNear)) {x : ℝ} (hx : x ∈ Set.Ioo 0 xNear) :
    (Gop^[i] (fun y => 2 * kappa y * deriv f y)) x
      = ∑ l ∈ Finset.range (i + 1), aCoeff i l x * (x ^ l * iteratedDeriv (l + 1) f x) := by
  have key : ∀ i : ℕ, ∀ x ∈ Set.Ioo 0 xNear,
      (Gop^[i] (fun y => 2 * kappa y * deriv f y)) x
        = ∑ l ∈ Finset.range (i + 1), aCoeff i l x * (x ^ l * iteratedDeriv (l + 1) f x) := by
    intro i
    induction i with
    | zero =>
      intro x hx
      show (fun y => 2 * kappa y * deriv f y) x = _
      simp [iteratedDeriv_one]
    | succ i ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      show 2 * kappa x * (x * deriv (Gop^[i] (fun y => 2 * kappa y * deriv f y)) x) = _
      have hev : (fun y => ∑ l ∈ Finset.range (i + 1),
            aCoeff i l y * (y ^ l * iteratedDeriv (l + 1) f y))
          =ᶠ[𝓝 x] (Gop^[i] (fun y => 2 * kappa y * deriv f y)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        exact (ih y hy).symm
      rw [← hev.deriv_eq]
      show 2 * kappa x * (x * deriv (fun y => ∑ l ∈ Finset.range (i + 1),
            aCoeff i l y * (y ^ l * iteratedDeriv (l + 1) f y)) x)
          = ∑ l ∈ Finset.range (i + 2), aCoeff (i + 1) l x
              * (x ^ l * iteratedDeriv (l + 1) f x)
      exact aCoeff_step hf i hx
  exact key i x hx

end Work.FTS.H2.DivQ
end
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.bCoeff_expansion =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

set_option autoImplicit false

/-! ## Elementary facts about the right end `xNear = sin(π/4)` of the near region -/


lemma xNear_lt_one_b : xNear < 1 := by
  rw [xNear, Real.sin_pi_div_four]
  have h : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

/-! ## Smoothness of the coefficients

`kappa x = cos (arcsin x)` is smooth on `(-1,1)`, hence on `(0, xNear)`; the coefficients
`bCoeff i j` are built from it by the recursion, so they are smooth too. -/

lemma contDiffOn_kappa_b : ContDiffOn ℝ (⊤ : ℕ∞) kappa (Set.Ioo 0 xNear) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) Real.arcsin (Set.Ioo 0 xNear) :=
    (Real.contDiffOn_arcsin (n := (⊤ : ℕ∞))).mono (by
      intro x hx
      simp only [Set.mem_Ioo] at hx
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨by linarith [hx.1], by linarith [hx.2, xNear_lt_one_b]⟩)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => Real.cos (Real.arcsin x)) (Set.Ioo 0 xNear) :=
    Real.contDiff_cos.comp_contDiffOn h1
  refine h2.congr (fun x hx => ?_)
  simp only [kappa, thetaOf]
  congr 1
  ring

/-- On an open set, `ContDiffOn` is preserved by `deriv`. -/
lemma contDiffOn_deriv_of_isOpen (s : Set ℝ) (hs : IsOpen s) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) : ContDiffOn ℝ (⊤ : ℕ∞) (deriv f) s := by
  have h := hf.derivWithin hs.uniqueDiffOn (m := (⊤ : ℕ∞)) (by simp)
  exact h.congr (fun x hx => (derivWithin_of_isOpen hs hx).symm)

/-- Every iterated derivative of a function smooth on `(0,xNear)` is smooth there. -/
lemma contDiffOn_iteratedDeriv_b {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (Set.Ioo 0 xNear)) (j : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv j u) (Set.Ioo 0 xNear) := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
      have h := contDiffOn_deriv_of_isOpen _ isOpen_Ioo ih
      rw [iteratedDeriv_succ]
      exact h

/-- The coefficients `bCoeff i j` are smooth on `(0, xNear)`. -/
lemma contDiffOn_bCoeff (i : ℕ) : ∀ j : ℕ,
    ContDiffOn ℝ (⊤ : ℕ∞) (bCoeff i j) (Set.Ioo 0 xNear) := by
  induction i with
  | zero =>
      intro j
      by_cases hj : j = 0
      · subst hj
        rw [bCoeff_zero_zero]
        exact contDiffOn_const
      · have : bCoeff 0 j = fun _ => (0:ℝ) := by
          funext x
          simp only [bCoeff, hj, ↓reduceIte]
        rw [this]
        exact contDiffOn_const
  | succ i ih =>
      intro j
      rw [show bCoeff (i + 1) j = (fun x => 2 * kappa x * (x * deriv (bCoeff i j) x
              + (j : ℝ) * bCoeff i j x)
            + (if j = 0 then 0 else 2 * kappa x * bCoeff i (j - 1) x)) from rfl]
      have hk : ContDiffOn ℝ (⊤ : ℕ∞) kappa (Set.Ioo 0 xNear) := contDiffOn_kappa_b
      have hderiv : ContDiffOn ℝ (⊤ : ℕ∞) (deriv (bCoeff i j)) (Set.Ioo 0 xNear) :=
        contDiffOn_deriv_of_isOpen _ isOpen_Ioo (ih j)
      have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun x => x * deriv (bCoeff i j) x + (j : ℝ) * bCoeff i j x) (Set.Ioo 0 xNear) :=
        (contDiffOn_id.mul hderiv).add (contDiffOn_const.mul (ih j))
      have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun x => 2 * kappa x * (x * deriv (bCoeff i j) x + (j : ℝ) * bCoeff i j x))
          (Set.Ioo 0 xNear) :=
        (contDiffOn_const.mul hk).mul h1
      have h3 : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun x => (if j = 0 then (0:ℝ) else 2 * kappa x * bCoeff i (j - 1) x))
          (Set.Ioo 0 xNear) := by
        by_cases hj : j = 0
        · simp only [hj, ↓reduceIte]
          exact contDiffOn_const
        · simp only [hj, ↓reduceIte]
          exact (contDiffOn_const.mul hk).mul (ih (j - 1))
      exact h2.add h3

/-! ## The vanishing of the coefficients above the diagonal -/

/-- `bCoeff i j` vanishes identically once `j > i`. -/
lemma bCoeff_eq_zero_of_lt (i : ℕ) : ∀ j : ℕ, i < j → bCoeff i j = fun _ => (0:ℝ) := by
  induction i with
  | zero =>
      intro j hj
      funext x
      simp only [bCoeff, Nat.pos_iff_ne_zero.mp hj, ↓reduceIte]
  | succ i ih =>
      intro j hj
      funext x
      have h1 : bCoeff i j = fun _ => (0:ℝ) := ih j (by omega)
      have h2 : bCoeff i (j - 1) = fun _ => (0:ℝ) := ih (j - 1) (by omega)
      have h3 : j ≠ 0 := by omega
      rw [show bCoeff (i + 1) j = (fun x => 2 * kappa x * (x * deriv (bCoeff i j) x
            + (j : ℝ) * bCoeff i j x)
            + (if j = 0 then 0 else 2 * kappa x * bCoeff i (j - 1) x)) from rfl, h1, h2]
      simp [h3]

/-! ## The expansion sum `S` -/

/-- The right-hand side of the expansion: `∑_{j ≤ i} b i j x · (x^j · ∂_x^j u x)`. -/
def S (u : ℝ → ℝ) (i : ℕ) : ℝ → ℝ :=
  fun x => ∑ j ∈ Finset.range (i + 1), bCoeff i j x * (x ^ j * iteratedDeriv j u x)

/-! ## The two algebraic lemmas behind the induction step -/

/-- Pointwise form of the induction step: pulling `x ∂_x` through the `j`-th term of the
expansion shifts the summation index in the last summand. -/
lemma step_point (x K : ℝ) (P : ℕ → ℝ) (A A' : ℕ → ℝ) (j : ℕ) :
    K * (x * (A' j * (x ^ j * P j) + A j * ((j : ℝ) * x ^ (j - 1) * P j + x ^ j * P (j + 1))))
      = (K * (x * A' j + (j : ℝ) * A j)) * (x ^ j * P j)
        + K * A j * (x ^ (j + 1) * P (j + 1)) := by
  have key : x * ((j : ℝ) * x ^ (j - 1) * P j) = (j : ℝ) * x ^ j * P j := by
    match j with
    | 0 => simp
    | k + 1 => rw [show (k + 1) - 1 = k by omega, pow_succ']; ring
  have key2 : x * (x ^ j * P (j + 1)) = x ^ (j + 1) * P (j + 1) := by
    rw [← mul_assoc, ← pow_succ']
  calc K * (x * (A' j * (x ^ j * P j) + A j * ((j : ℝ) * x ^ (j - 1) * P j + x ^ j * P (j + 1))))
      = K * (x * (A' j * (x ^ j * P j))
          + (x * (A j * ((j : ℝ) * x ^ (j - 1) * P j)) + x * (A j * (x ^ j * P (j + 1))))) := by ring
    _ = K * ((A' j * (x * (x ^ j * P j)))
          + (A j * (x * ((j : ℝ) * x ^ (j - 1) * P j)) + A j * (x * (x ^ j * P (j + 1))))) := by ring
    _ = K * ((A' j * (x * (x ^ j * P j)))
          + (A j * ((j : ℝ) * x ^ j * P j) + A j * (x ^ (j + 1) * P (j + 1)))) := by rw [key, key2]
    _ = (K * (x * A' j + (j : ℝ) * A j)) * (x ^ j * P j)
        + K * A j * (x ^ (j + 1) * P (j + 1)) := by ring

/-- Sum form of the induction step, matching the recursion defining `bCoeff`. -/
lemma step_alg (i : ℕ) (x K : ℝ) (P : ℕ → ℝ) (A A' : ℕ → ℝ)
    (hA : A (i + 1) = 0) (hA' : A' (i + 1) = 0) :
    K * (x * ∑ j ∈ Finset.range (i + 1),
        (A' j * (x ^ j * P j) + A j * ((j : ℝ) * x ^ (j - 1) * P j + x ^ j * P (j + 1))))
      = ∑ j ∈ Finset.range (i + 2),
          (K * (x * A' j + (j : ℝ) * A j) + (if j = 0 then 0 else K * A (j - 1)))
            * (x ^ j * P j) := by
  have hL : K * (x * ∑ j ∈ Finset.range (i + 1),
        (A' j * (x ^ j * P j) + A j * ((j : ℝ) * x ^ (j - 1) * P j + x ^ j * P (j + 1))))
      = ∑ j ∈ Finset.range (i + 1),
          ((K * (x * A' j + (j : ℝ) * A j)) * (x ^ j * P j)
            + K * A j * (x ^ (j + 1) * P (j + 1))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => step_point x K P A A' j)
  have hFtop : (K * (x * A' (i + 1) + ((i + 1 : ℕ)) * A (i + 1))) * (x ^ (i + 1) * P (i + 1)) = 0 := by
    simp [hA, hA']
  have hF : ∑ j ∈ Finset.range (i + 2), (K * (x * A' j + (j : ℝ) * A j)) * (x ^ j * P j)
      = ∑ j ∈ Finset.range (i + 1), (K * (x * A' j + (j : ℝ) * A j)) * (x ^ j * P j) := by
    rw [Finset.sum_range_succ, hFtop, add_zero]
  have hG : ∑ k ∈ Finset.range (i + 2), (if k = 0 then 0 else K * A (k - 1)) * (x ^ k * P k)
      = ∑ j ∈ Finset.range (i + 1), K * A j * (x ^ (j + 1) * P (j + 1)) := by
    rw [Finset.sum_range_succ']
    have h0 : (if (0 : ℕ) = 0 then (0 : ℝ) else K * A (0 - 1)) * (x ^ 0 * P 0) = 0 := by simp
    rw [h0, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
  rw [hL, Finset.sum_add_distrib, ← hF, ← hG, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-! ## The derivative of the expansion sum -/

/-- The derivative of `S u i` is obtained by the product rule, term by term. -/
lemma deriv_S (i : ℕ) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (Set.Ioo 0 xNear)) {x : ℝ} (hx : x ∈ Set.Ioo 0 xNear) :
    deriv (S u i) x
      = ∑ j ∈ Finset.range (i + 1),
          (deriv (bCoeff i j) x * (x ^ j * iteratedDeriv j u x)
            + bCoeff i j x * ((j : ℝ) * x ^ (j - 1) * iteratedDeriv j u x
                + x ^ j * iteratedDeriv (j + 1) u x)) := by
  have hs : Set.Ioo (0 : ℝ) xNear ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx
  have hterm : ∀ j : ℕ, HasDerivAt (fun y => bCoeff i j y * (y ^ j * iteratedDeriv j u y))
      (deriv (bCoeff i j) x * (x ^ j * iteratedDeriv j u x)
        + bCoeff i j x * ((j : ℝ) * x ^ (j - 1) * iteratedDeriv j u x
            + x ^ j * iteratedDeriv (j + 1) u x)) x := by
    intro j
    have hb : HasDerivAt (bCoeff i j) (deriv (bCoeff i j) x) x :=
      (((contDiffOn_bCoeff i j).differentiableOn (by simp)).differentiableAt hs).hasDerivAt
    have hiu : HasDerivAt (iteratedDeriv j u) (iteratedDeriv (j + 1) u x) x := by
      have h := (((contDiffOn_iteratedDeriv_b hu j).differentiableOn (by simp)).differentiableAt hs).hasDerivAt
      rwa [← iteratedDeriv_succ] at h
    exact hb.mul ((hasDerivAt_pow j x).mul hiu)
  rw [show S u i = (fun y => ∑ j ∈ Finset.range (i + 1),
        bCoeff i j y * (y ^ j * iteratedDeriv j u y)) from rfl,
      deriv_fun_sum (fun j _ => (hterm j).differentiableAt)]
  exact Finset.sum_congr rfl (fun j _ => (hterm j).deriv)

/-! ## The expansion, as an equality of functions on the near region -/

lemma bCoeff_expansion_eqon (i : ℕ) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (Set.Ioo 0 xNear)) :
    Set.EqOn ((Gop^[i]) u) (S u i) (Set.Ioo 0 xNear) := by
  induction i with
  | zero =>
      intro x hx
      simp [S, bCoeff]
  | succ i ih =>
      intro x hx
      have hEv : (Gop^[i]) u =ᶠ[𝓝 x] S u i :=
        ih.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx)
      have hderiv : deriv ((Gop^[i]) u) x = deriv (S u i) x := hEv.deriv_eq
      rw [Function.iterate_succ_apply',
        show Gop ((Gop^[i]) u) x = 2 * kappa x * (x * deriv ((Gop^[i]) u) x) from rfl, hderiv,
        deriv_S i hu hx]
      have hA : (fun j => bCoeff i j x) (i + 1) = 0 := by
        show bCoeff i (i + 1) x = 0
        rw [bCoeff_eq_zero_of_lt i (i + 1) (by omega)]
      have hA' : (fun j => deriv (bCoeff i j) x) (i + 1) = 0 := by
        show deriv (bCoeff i (i + 1)) x = 0
        rw [bCoeff_eq_zero_of_lt i (i + 1) (by omega)]
        simp
      rw [step_alg i x (2 * kappa x) (fun j => iteratedDeriv j u x) (fun j => bCoeff i j x)
        (fun j => deriv (bCoeff i j) x) hA hA']
      rw [show S u (i + 1) x = ∑ j ∈ Finset.range (i + 2),
            bCoeff (i + 1) j x * (x ^ j * iteratedDeriv j u x) from rfl]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [show bCoeff (i + 1) j x = 2 * kappa x * (x * deriv (bCoeff i j) x
            + (j : ℝ) * bCoeff i j x) + (if j = 0 then 0 else 2 * kappa x * bCoeff i (j - 1) x)
          from rfl]

/-- **The expansion of `G^i u` in powers of `x`.**  With `bCoeff` as defined in
`Work.FTS.H2.DivQ.Defs` (`b 0 0 = 1`, `b 0 j = 0` for `j ≠ 0`, and

  `b (i+1) j = 2κ · (x · (b i j)' + j · b i j) + (if j = 0 then 0 else 2κ · b i (j-1))`),

for every `u` of class `C^∞` on `(0, x₁)` (`x₁ = xNear = sin(π/4)`) and every `x ∈ (0,x₁)`:

  `(G^i u) x = Σ_{j ∈ range (i+1)} b i j x · (x^j · ∂_x^j u (x))`.

ROUTE.  Induction on `i`.  `i = 0`: both sides are `u x`.  Step: write `u_i := G^i u`, assume the
expansion for `u_i` and compute
`G u_i = 2κ x ∂_x (Σ_j b i j · x^j ∂_x^j u)`.  Termwise (product rule, three terms)
`∂_x(b i j · x^j ∂_x^j u) = (b i j)' x^j ∂_x^j u + b i j · j x^{j-1} ∂_x^j u + b i j x^j ∂_x^{j+1} u`,
so `2κ x ∂_x(…) = Σ_j b (i+1) j x^j ∂_x^j u` after re-indexing `j ↦ j-1` in the last sum (the new
coefficient of `x^j ∂_x^j u` is `2κ(x (b i j)' + j b i j) + 2κ b i (j-1)`, which is the recursion).
All identities hold on the open interval `(0,x₁)`, where `u` is smooth, so `∂_x^j u = iteratedDeriv j u`
and the finite sum can be differentiated termwise; note the induction also needs
`ContDiffOn ⊤ (Gop u_i) (Ioo 0 x₁)`, which follows from the expansion and the smoothness of the
coefficients `b i j` on the open set. -/
theorem bCoeff_expansion (i : ℕ) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (Set.Ioo 0 xNear)) {x : ℝ} (hx : x ∈ Set.Ioo 0 xNear) :
    (Gop^[i] u) x
      = ∑ j ∈ Finset.range (i + 1), bCoeff i j x * (x ^ j * iteratedDeriv j u x) := by
  have h := bCoeff_expansion_eqon i hu hx
  simpa [S] using h

end Work.FTS.H2.DivQ
end
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.divSinPrimitive =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set Filter
open scoped Topology

/-! ### The family `V_j = x^{j+1}·∂_x^j (f/x)`, whose derivative is `x^j·f^{(j+1)}` on `(0,x₁)`. -/

private noncomputable def dspV (f : ℝ → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  x ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) x

/-! ### The primitive `G u = ∫_0^u s^k f^{(k+1)}(s) ds`: integrability, derivative, limit at `0⁺`. -/

private theorem dsp_iteratedDeriv_continuousOn_Ioo {f : ℝ → ℝ} {x₁ : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁)) (m : ℕ) :
    ContinuousOn (fun x : ℝ => iteratedDeriv m f x) (Set.Ioo 0 x₁) := by
  have hs : UniqueDiffOn ℝ (Set.Ioo (0 : ℝ) x₁) := isOpen_Ioo.uniqueDiffOn
  have hcont : ContinuousOn (iteratedDerivWithin m f (Set.Ioo (0 : ℝ) x₁)) (Set.Ioo (0 : ℝ) x₁) :=
    (hf.mono Set.Ioo_subset_Ioc_self).continuousOn_iteratedDerivWithin (by simp) hs
  exact hcont.congr fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm

private theorem dspPrimProps (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁))
    (hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioc 0 x₁) ∧
    (∀ x ∈ Set.Ioo 0 x₁,
        HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, s ^ k * iteratedDeriv (k + 1) f s)
          (x ^ k * iteratedDeriv (k + 1) f x) x) ∧
    Filter.Tendsto (fun u : ℝ => ∫ s in (0 : ℝ)..u, s ^ k * iteratedDeriv (k + 1) f s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hψ := primIntegrable k γ x₁ hx₁ hγ f hf hint
  refine ⟨hψ, ?_, ?_⟩
  · intro x hx
    have hInt : IntervalIntegrable (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
        volume (0 : ℝ) x := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hx.1.le]
      exact hψ.mono_set (Set.Ioc_subset_Ioc le_rfl hx.2.le)
    have hcontψ : ContinuousOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioo 0 x₁) :=
      (continuous_id.pow k).continuousOn.mul (dsp_iteratedDeriv_continuousOn_Ioo hf (k + 1))
    have hcontAt : ContinuousAt (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) x :=
      hcontψ.continuousAt (isOpen_Ioo.mem_nhds hx)
    have hsm := hcontψ.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo x hx
    exact intervalIntegral.integral_hasDerivAt_right hInt hsm hcontAt
  · refine Filter.Tendsto.congr' ?_ ((hardyIter_tendsto_zero hx₁ hψ).mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (intervalIntegral.integral_of_le hδ.le).symm

/-- **The primitive form of `∂_x^k (f/x)`, and the boundary control.**

Let `0 < x₁`, `γ > -1`, and let `f` be of class `C^∞` on the half-open interval `(0,x₁]`, with
`f(x) → 0` as `x → 0⁺` (the *limit*, not merely the value at `0`), and with
`B := ∫_0^{x₁} x^{2k-γ}(∂_x^{k+1} f)² < ∞` (honest — the hypothesis under which `paperHardyIter`
applies).  Then for every `x ∈ (0,x₁)` (note: the *open* interval, because `iteratedDeriv` is the
two-sided derivative)

  `x^{k+1} · ∂_x^k (fun y => f y / y) x = ∫_0^x s^k · ∂_x^{k+1} f (s) ds`

and the *boundary control*

  `x^{2k+1-γ} · (∂_x^k (fun y => f y / y) x)² ≤ 1/(1+γ) · ∫_0^x s^{2k-γ}(∂_x^{k+1} f (s))² ds`,

in particular `x^{2k+1-γ}(∂_x^k(f/x) x)² → 0` as `x → 0⁺`.

This is the missing ingredient for the *honesty* of the left-hand integral in
`Submission/Work/FTS/H2/DivQ/NOTES.md` §9.1: with it, the truncated integration-by-parts of
`paperHardyIter` gives `A_ε = ∫_ε^{x₁}x^{2k-γ}(∂_x^k(f/x))² ≤ C' B` uniformly in `ε`, hence
`A < ∞` by monotone convergence — the left-hand side of the paper's Lemma 2 *is* integrable, which
the junk-safe formulation of `paperHardyIter` alone cannot certify.

ROUTE.  Let `H = f/x`.  Write `P_k(x) := x^{k+1}H^{(k)}(x) - ∫_0^x s^k f^{(k+1)}(s)ds`.  By the
Leibniz identity `f^{(k+1)} = xH^{(k+1)} + (k+1)H^{(k)}` we get the *formal* derivative identity
`(x^{k+1}H^{(k)})' = x^k f^{(k+1)}` on `(0,x₁)`, hence `P_k` is constant there.  Then prove

  `(⋆_k)   |x^{k+1}H^{(k)}(x)| ≤ (1/(1+γ))^{1/2} x^{(1+γ)/2} B^{1/2}   for x ∈ (0,x₁)`

by induction on `k`: `⋆_0` is `|f(x)|`; `⋆_k` gives `lim_{ε→0}P_k(ε) = 0` because
`ε^{k+1}H^{(k)}(ε) → 0` by `⋆_k` and `|∫_0^ε s^k f^{(k+1)}| ≤ (∫_0^ε s^{2k-γ}(f^{(k+1)})²)^{1/2}
(∫_0^ε s^γ)^{1/2} → 0` by Cauchy–Schwarz and integrability; so `P_k ≡ 0` on `(0,x₁)`, which is the
claimed identity, and then Cauchy–Schwarz applied to `∫_0^x s^k f^{(k+1)}` gives `⋆_{k+1}`.
(`f(x) → 0` is needed exactly for `⋆_0`; with only `f 0 = 0` the statement is false, e.g.
`f = 1` on `(0,x₁)`.) -/
theorem divSinPrimitive (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁) →
      Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
        (Set.Ioc 0 x₁) →
      (∀ x ∈ Set.Ioo (0 : ℝ) x₁,
          x ^ (k + 1) * iteratedDeriv k (fun y : ℝ => f y / y) x
            = ∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s) ∧
        (∀ x ∈ Set.Ioo (0 : ℝ) x₁,
          x ^ (2 * (k : ℝ) + 1 - γ) * (iteratedDeriv k (fun y : ℝ => f y / y) x) ^ 2
            ≤ 1 / (1 + γ) * (∫ s in (0 : ℝ)..x,
                s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2)) := by
  intro f hf hf0 hint
  obtain ⟨hVd, hVr⟩ := divSinPrimitiveDeriv x₁ hx₁ f hf
  obtain ⟨hψint, hGd, hGt⟩ := dspPrimProps k γ x₁ hx₁ hγ f hf hint
  have hvan : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      Filter.Tendsto (fun x : ℝ => x ^ j * iteratedDeriv j f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    divSinPrimitiveVanish k γ x₁ hx₁ hγ f hf hint
  have hVd' : ∀ (j : ℕ) (x : ℝ), x ∈ Set.Ioo 0 x₁ →
      HasDerivAt (dspV f j) (x ^ j * iteratedDeriv (j + 1) f x) x := by
    intro j x hx
    change HasDerivAt (fun t : ℝ => t ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) t)
      (x ^ j * iteratedDeriv (j + 1) f x) x
    exact hVd j x hx
  have hVr' : ∀ (j : ℕ) (y : ℝ), y ∈ Set.Ioo 0 x₁ →
      dspV f (j + 1) y = y ^ (j + 1) * iteratedDeriv (j + 1) f y
        - (j + 1) * dspV f j y := by
    intro j y hy
    have h := hVr j y hy
    have hgoal : dspV f (j + 1) y
        = y ^ (j + 2) * iteratedDeriv (j + 1) (fun y : ℝ => f y / y) y := by
      simp only [dspV]
    rw [hgoal, h]
    simp only [dspV]
  -- the vanishings kill the boundary term
  have hVtend : ∀ j ≤ k,
      Filter.Tendsto (dspV f j) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hEq : dspV f 0 =ᶠ[nhdsWithin 0 (Set.Ioi 0)] f := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [dspV, iteratedDeriv_zero, Nat.zero_add, pow_one]
        rw [mul_comm x (f x / x), div_mul_cancel₀ (f x) (ne_of_gt hx)]
      exact hf0.congr' hEq.symm
    | succ n ih =>
      intro hn
      have hn' : n ≤ k := by omega
      have h1 : Filter.Tendsto (fun y : ℝ => y ^ (n + 1) * iteratedDeriv (n + 1) f y)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := hvan (n + 1) (by omega) hn
      have h2 : Filter.Tendsto (fun y : ℝ => (n + 1) * dspV f n y)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have h := (ih hn').const_mul ((n + 1 : ℕ) : ℝ)
        simpa using h
      have h3 := h1.sub h2
      have hstep : dspV f (n + 1) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          fun y : ℝ => y ^ (n + 1) * iteratedDeriv (n + 1) f y - (n + 1) * dspV f n y := by
        filter_upwards [Ioo_mem_nhdsGT hx₁] with y hy
        exact hVr' n y hy
      simpa using h3.congr' hstep.symm
  have hVk : Filter.Tendsto (dspV f k) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := hVtend k le_rfl
  -- the identity
  have hVg : ∀ x ∈ Set.Ioo (0 : ℝ) x₁, dspV f k x
      = ∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s := by
    have ha : x₁ / 2 ∈ Set.Ioo (0 : ℝ) x₁ := ⟨by linarith, by linarith⟩
    have hconst : ∀ x ∈ Set.Ioo (0 : ℝ) x₁,
        dspV f k x - (∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s)
          = dspV f k (x₁ / 2)
            - (∫ s in (0 : ℝ)..(x₁ / 2), s ^ k * iteratedDeriv (k + 1) f s) := by
      intro x hx
      have hder : ∀ y ∈ Set.uIcc (x₁ / 2) x,
          HasDerivAt (fun z : ℝ => dspV f k z
            - (∫ s in (0 : ℝ)..z, s ^ k * iteratedDeriv (k + 1) f s)) 0 y := by
        intro y hy
        have hyI : y ∈ Set.Ioo (0 : ℝ) x₁ := by
          rw [Set.mem_uIcc] at hy
          rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨lt_of_lt_of_le (by linarith) h1, lt_of_le_of_lt h2 hx.2⟩
          · exact ⟨lt_of_lt_of_le hx.1 h1, lt_of_le_of_lt h2 (by linarith)⟩
        have h := (hVd' k y hyI).sub (hGd y hyI)
        rw [sub_self] at h
        change HasDerivAt (fun z : ℝ => dspV f k z
          - (∫ s in (0 : ℝ)..z, s ^ k * iteratedDeriv (k + 1) f s)) 0 y
        exact h
      have hint0 : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (x₁ / 2) x :=
        intervalIntegrable_const
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint0
      simp only [intervalIntegral.integral_const, smul_eq_mul] at hftc
      linarith
    have hlim : Filter.Tendsto (fun x : ℝ => dspV f k x
        - (∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 - 0)) := hVk.sub hGt
    have hlimc : Filter.Tendsto (fun x : ℝ => dspV f k x
        - (∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (dspV f k (x₁ / 2)
          - (∫ s in (0 : ℝ)..(x₁ / 2), s ^ k * iteratedDeriv (k + 1) f s))) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hx₁] with x hx
      exact (hconst x hx).symm
    have hzero : dspV f k (x₁ / 2)
        - (∫ s in (0 : ℝ)..(x₁ / 2), s ^ k * iteratedDeriv (k + 1) f s) = 0 := by
      have h := tendsto_nhds_unique hlim hlimc
      linarith
    intro x hx
    have h := hconst x hx
    linarith
  refine ⟨?_, ?_⟩
  · intro x hx
    simpa [dspV] using hVg x hx
  · intro x hx
    set A : ℝ := iteratedDeriv k (fun y : ℝ => f y / y) x with hA
    set J : ℝ := ∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s with hJ
    set I0 : ℝ := ∫ s in (0 : ℝ)..x,
      s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2 with hI0
    have hx0 : 0 < x := hx.1
    have hxle : x ≤ x₁ := le_of_lt hx.2
    have hId : x ^ (k + 1) * A = J := by
      rw [hA, hJ]
      simpa [dspV] using hVg x hx
    have hi1 : MeasureTheory.IntegrableOn (fun s : ℝ =>
        s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2) (Set.Ioc 0 x) :=
      hint.mono_set (fun s hs => ⟨hs.1, le_trans hs.2 hxle⟩)
    have hi2 : MeasureTheory.IntegrableOn
        (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioc 0 x) :=
      hψint.mono_set (fun s hs => ⟨hs.1, le_trans hs.2 hxle⟩)
    have hCS := csWeightedInterval k γ x hx0 hγ (fun s : ℝ => iteratedDeriv (k + 1) f s) hi1 hi2
    rw [← hJ] at hCS
    have hIntγ : (∫ s in (0 : ℝ)..x, s ^ γ) = x ^ (1 + γ) / (1 + γ) := by
      rw [integral_rpow (Or.inl hγ), Real.zero_rpow (by linarith : γ + 1 ≠ 0), sub_zero,
        show γ + 1 = 1 + γ by ring]
    rw [hIntγ] at hCS
    rw [← hId] at hCS
    have h2 := mul_le_mul_of_nonneg_right hCS (Real.rpow_nonneg hx0.le (-1 - γ))
    have hcomb : x ^ (2 * (k : ℝ) + 2) * x ^ (-1 - γ) = x ^ (2 * (k : ℝ) + 1 - γ) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    have hsq : (x ^ (k + 1) * A) ^ 2 = x ^ (2 * (k : ℝ) + 2) * A ^ 2 := by
      rw [mul_pow]
      congr 1
      rw [← pow_mul, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have hxpow : x ^ (1 + γ) * x ^ (-1 - γ) = 1 := by
      rw [← Real.rpow_add hx0, show (1 : ℝ) + γ + (-1 - γ) = 0 by ring, Real.rpow_zero]
    have id1 : x ^ (2 * (k : ℝ) + 1 - γ) * A ^ 2
        = (x ^ (k + 1) * A) ^ 2 * x ^ (-1 - γ) := by
      rw [hsq, mul_assoc, mul_comm (A ^ 2) (x ^ (-1 - γ)), ← mul_assoc, hcomb]
    have id2 : ((x ^ (1 + γ) / (1 + γ)) * I0) * x ^ (-1 - γ) = (1 / (1 + γ)) * I0 := by
      have h1 : ((x ^ (1 + γ) / (1 + γ)) * I0) * x ^ (-1 - γ)
          = (x ^ (1 + γ) * x ^ (-1 - γ) * I0) / (1 + γ) := by ring
      rw [h1, hxpow, one_mul]
      ring
    calc x ^ (2 * (k : ℝ) + 1 - γ) * A ^ 2
        = (x ^ (k + 1) * A) ^ 2 * x ^ (-1 - γ) := id1
      _ ≤ ((x ^ (1 + γ) / (1 + γ)) * I0) * x ^ (-1 - γ) := h2
      _ = (1 / (1 + γ)) * I0 := id2


end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.honestPoincarePoint =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set Filter

/-- **Pointwise Poincaré for an honest slice.**  If `h` is smooth on the open angular interval
`(0, π/2)`, tends to `0` at the left endpoint `0`, and the weighted square `(h')² · sin(2θ)^{-η}`
is integrable on `Iθ = [0, π/2]` (`η = Work.Spaces.eta = 99/100`), then for every `θ ∈ (0, π/2)`

  `(h θ)² ≤ C · ∫_{Iθ} (h')² · sin(2θ)^{-η}`

with a universal constant `C`.  (The value `π/2` works: `h θ = ∫_0^θ h'`, so
`(h θ)² ≤ θ · ∫_0^θ (h')² ≤ (π/2) · ∫_{Iθ} (h')² ≤ (π/2) · ∫_{Iθ} (h')² sin(2θ)^{-η}`, the last
step because `sin(2θ)^{-η} ≥ 1` on the open interval.)  Only the left endpoint limit is needed. -/
theorem honestPoincarePoint :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (h θ) ^ 2 ≤ C *
          (∫ x in Work.Spaces.Iθ,
            (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))) := by
  refine ⟨Real.pi / 2, by positivity, ?_⟩
  intro h hsm hten hint θ hθ
  -- integrability of `(h')²` and `h'` on `(0, θ]`, interval integrability, and the primitive form
  obtain ⟨hint2Ioc, _hderivIoc, hI1, hI2, hFTC⟩ := derivIntegrablePrimitive hθ hsm hten hint
  -- Cauchy–Schwarz against the constant function `1`
  have hCS := sqIntervalIntegralLe (deriv h) hθ.1.le hI1 hI2
  -- `∫_0^θ (h')² ≤ ∫_{Iθ} (h')² sin(2θ)^{-η}`
  have hmono := sqIntegral_le_weightedIntegral hθ hint hint2Ioc
  have hnn : 0 ≤ ∫ x in (0 : ℝ)..θ, (deriv h x) ^ 2 :=
    intervalIntegral.integral_nonneg_of_ae hθ.1.le (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have hBnn : 0 ≤ ∫ x in Work.Spaces.Iθ,
      (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) := le_trans hnn hmono
  rw [hFTC]
  calc (∫ x in (0 : ℝ)..θ, deriv h x) ^ 2
      ≤ θ * ∫ x in (0 : ℝ)..θ, (deriv h x) ^ 2 := by simpa using hCS
    _ ≤ θ * (∫ x in Work.Spaces.Iθ,
          (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_left hmono (le_of_lt hθ.1)
    _ ≤ (Real.pi / 2) * (∫ x in Work.Spaces.Iθ,
          (deriv h x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_right hθ.2.le hBnn

end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.reflSlice_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

set_option autoImplicit false


lemma sin_two_reflSlice (θ : ℝ) : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
  have h : 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ := by ring
  rw [h, Real.sin_pi_sub]

/-- `Dth1Iter` preserves `C^∞` on an open interval (slices are smooth on `(0,π/2)`). -/
lemma contDiffOn_dth1Iter {h : ℝ → ℝ} (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (j : ℕ) : ContDiffOn ℝ (⊤ : ℕ∞) (Work.Elliptic.Dth1Iter j h) (Set.Ioo 0 (Real.pi / 2)) := by
  induction j with
  | zero => simpa using hsm
  | succ j ih =>
      rw [Work.Elliptic.Dth1Iter_succ]
      have hder : ContDiffOn ℝ (⊤ : ℕ∞) (deriv (Work.Elliptic.Dth1Iter j h))
          (Set.Ioo 0 (Real.pi / 2)) :=
        ih.deriv_of_isOpen isOpen_Ioo (by simp)
      have hsin : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Real.sin (2 * θ))
          (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
      have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Elliptic.Dth1Iter j h) θ)
          (Set.Ioo 0 (Real.pi / 2)) := hsin.mul hder
      exact h1

theorem reflSlice_facts (i : ℕ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Work.Elliptic.Dth1Iter i (fun θ' => h (Real.pi / 2 - θ')) θ
          = (-1 : ℝ) ^ i * Work.Elliptic.Dth1Iter i h (Real.pi / 2 - θ)) ∧
      (∀ F : ℝ → ℝ,
        (∫ θ in (0 : ℝ)..(Real.pi / 2), F (Real.pi / 2 - θ))
          = ∫ θ in (0 : ℝ)..(Real.pi / 2), F θ) ∧
      (∀ θ : ℝ, Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ)) := by
  refine ⟨?_, ?_, sin_two_reflSlice⟩
  · -- anti-invariance of `D_θ` under the reflection
    have hmem : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.pi / 2 - θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      fun θ hθ => ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    intro θ
    induction i generalizing θ with
    | zero => intro _; simp
    | succ i ih =>
        intro hθ
        have hderiv : ∀ j : ℕ, DifferentiableAt ℝ (Work.Elliptic.Dth1Iter j h)
            (Real.pi / 2 - θ) := fun j =>
          ((contDiffOn_dth1Iter hsm j).contDiffAt (isOpen_Ioo.mem_nhds (hmem θ hθ))).differentiableAt
            (by simp)
        have hev : Work.Elliptic.Dth1Iter i (fun θ' => h (Real.pi / 2 - θ'))
            =ᶠ[𝓝 θ] fun θ' => (-1 : ℝ) ^ i * Work.Elliptic.Dth1Iter i h (Real.pi / 2 - θ') := by
          filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
          exact ih θ' hθ'
        have hcomp : HasDerivAt (fun θ' : ℝ => Work.Elliptic.Dth1Iter i h (Real.pi / 2 - θ'))
            (deriv (Work.Elliptic.Dth1Iter i h) (Real.pi / 2 - θ) * (-1)) θ := by
          have h1 : HasDerivAt (fun θ' : ℝ => Real.pi / 2 - θ') (-1) θ := by
            have h0 := (hasDerivAt_const (x := θ) (c := Real.pi / 2)).sub (hasDerivAt_id θ)
            have hf : ((fun _ : ℝ => Real.pi / 2) - (id : ℝ → ℝ))
                = fun θ' : ℝ => Real.pi / 2 - θ' := by
              funext θ'; simp
            rw [hf] at h0
            convert h0 using 1 <;> ring
          exact (hderiv i).hasDerivAt.comp θ h1
        have hchain : deriv (fun θ' : ℝ => (-1 : ℝ) ^ i * Work.Elliptic.Dth1Iter i h (Real.pi / 2 - θ')) θ
            = (-1 : ℝ) ^ i * (-(deriv (Work.Elliptic.Dth1Iter i h) (Real.pi / 2 - θ))) := by
          rw [(hcomp.const_mul ((-1 : ℝ) ^ i)).deriv]
          ring
        have hd : deriv (Work.Elliptic.Dth1Iter i (fun θ' => h (Real.pi / 2 - θ'))) θ
            = deriv (fun θ' : ℝ => (-1 : ℝ) ^ i * Work.Elliptic.Dth1Iter i h (Real.pi / 2 - θ')) θ :=
          hev.deriv_eq
        rw [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_succ]
        simp only [Work.Elliptic.Dth1]
        rw [hd, hchain, sin_two_reflSlice, pow_succ]
        ring
  · intro F
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi / 2)
      (d := Real.pi / 2) (f := F)
    simpa using h

end Work.FTS.H2.DivQ
end
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.thetaOfSubst =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

/-- `x₁ = sin(π/4) = √2/2` is strictly smaller than `1`, hence lies in the domain `(-1,1)` of the
arcsine. -/
private theorem xNear_lt_one : xNear < 1 := by
  rw [xNear, Real.sin_pi_div_four]
  have h : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- `x₁ > 0`. -/
private theorem xNear_pos_prv : 0 < xNear := by
  rw [xNear, Real.sin_pi_div_four]
  have h : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- On all of `ℝ` the factor `κ x = cos (2 θ(x))` coincides with `√(1-x²)`. -/
private theorem kappa_eq_sqrt_prv (x : ℝ) : kappa x = Real.sqrt (1 - x ^ 2) := by
  simp only [kappa, thetaOf]
  rw [show 2 * (Real.arcsin x / 2) = Real.arcsin x by ring, Real.cos_arcsin]

private theorem thetaOf_zero_prv : thetaOf 0 = 0 := by simp [thetaOf]

/-- `θ(x₁) = π/8`. -/
private theorem thetaOf_xNear_prv : thetaOf xNear = Real.pi / 8 := by
  rw [thetaOf, xNear, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  ring

/-- The change of variables `x = sin(2θ)` out of the `x`-variable into the `θ`-variable, on the
half `(0, x₁)` of the interval (where `κ ≥ 1/√2`): the substitution is carried by the
`ds/dθ = 2κ(s)` Jacobian `1/(2κ x)`, and since `Ψ ≥ 0` the integral over the corresponding
sub-interval `(0, π/8) ⊆ Iθ` is at most the full weighted integral. -/
theorem thetaOfSubst {Ψ : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn Ψ Work.Spaces.Iθ)
    (hnonneg : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Ψ θ) :
    MeasureTheory.IntegrableOn (fun x : ℝ => Ψ (thetaOf x) * (1 / (2 * kappa x)))
        (Set.Ioc 0 xNear) ∧
      (∫ x in (0 : ℝ)..xNear, Ψ (thetaOf x) * (1 / (2 * kappa x)))
        ≤ ∫ θ in Work.Spaces.Iθ, Ψ θ := by
  have hcont : ContinuousOn thetaOf (Set.uIcc (0 : ℝ) xNear) :=
    (Real.continuous_arcsin.div_const 2).continuousOn
  -- the derivative of `θ` at `x` is the Jacobian `1/(2κ x)`
  have hderiv : ∀ x ∈ Set.Ioo (min (0 : ℝ) xNear) (max (0 : ℝ) xNear),
      HasDerivAt thetaOf (1 / (2 * kappa x)) x := by
    intro x hx
    rw [min_eq_left (le_of_lt xNear_pos_prv), max_eq_right (le_of_lt xNear_pos_prv)] at hx
    have h1 : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
      Real.hasDerivAt_arcsin (by linarith [hx.1]) (by linarith [hx.2, xNear_lt_one])
    have h2 : HasDerivAt (fun y => Real.arcsin y / 2) ((1 / Real.sqrt (1 - x ^ 2)) / 2) x :=
      h1.div_const 2
    have hval : (1 / Real.sqrt (1 - x ^ 2)) / 2 = 1 / (2 * kappa x) := by
      rw [kappa_eq_sqrt_prv x]; ring
    exact h2.congr_deriv hval
  -- the Jacobian is nonnegative
  have hnn : ∀ x ∈ Set.Ioo (min (0 : ℝ) xNear) (max (0 : ℝ) xNear), 0 ≤ 1 / (2 * kappa x) := by
    intro x hx
    rw [min_eq_left (le_of_lt xNear_pos_prv), max_eq_right (le_of_lt xNear_pos_prv)] at hx
    have hpos : 0 < Real.sqrt (1 - x ^ 2) :=
      Real.sqrt_pos.mpr (by nlinarith [hx.1, hx.2, xNear_lt_one])
    rw [kappa_eq_sqrt_prv x]
    positivity
  -- `Ψ` is integrable on the image interval `(0, π/8)`
  have hPsi_int : IntervalIntegrable Ψ volume (0 : ℝ) (Real.pi / 8) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 8)]
    exact hint.mono_set (by intro x hx; exact ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩)
  -- integrability on `(0, x₁)`, by the change-of-variables criterion
  have hI : IntervalIntegrable (fun x : ℝ => Ψ (thetaOf x) * (1 / (2 * kappa x))) volume
      (0 : ℝ) xNear := by
    have hPsi' : IntervalIntegrable Ψ volume (thetaOf 0) (thetaOf xNear) := by
      rwa [thetaOf_zero_prv, thetaOf_xNear_prv]
    exact (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (a := (0 : ℝ)) (b := xNear) (f := thetaOf) (f' := fun x => 1 / (2 * kappa x)) (g := Ψ)
      hcont hderiv hnn).mpr hPsi'
  have hIntOn : IntegrableOn (fun x : ℝ => Ψ (thetaOf x) * (1 / (2 * kappa x)))
      (Set.Ioc 0 xNear) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt xNear_pos_prv)).mp hI
  -- the change-of-variables identity
  have hmain : ∫ x in (0 : ℝ)..xNear, Ψ (thetaOf x) * (1 / (2 * kappa x))
      = ∫ u in (0 : ℝ)..(Real.pi / 8), Ψ u := by
    have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0 : ℝ)) (b := xNear) (f := thetaOf) (f' := fun x => 1 / (2 * kappa x)) (g := Ψ)
      hcont hderiv hnn
    rw [thetaOf_zero_prv, thetaOf_xNear_prv] at h
    simpa [Function.comp_def] using h
  -- enlarge the interval to the whole `Iθ`
  have hae : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (Real.pi / 2))] Ψ :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall
        (fun x hx => hnonneg x ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩))
  have hPsi2 : IntervalIntegrable Ψ volume (0 : ℝ) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)).mpr
      (hint.mono_set (by intro x hx; exact ⟨le_of_lt hx.1, hx.2⟩))
  have h1 : ∫ u in (0 : ℝ)..(Real.pi / 8), Ψ u ≤ ∫ u in (0 : ℝ)..(Real.pi / 2), Ψ u :=
    intervalIntegral.integral_mono_interval (f := Ψ) (a := (0 : ℝ)) (b := Real.pi / 8)
      (μ := volume) (c := (0 : ℝ)) (d := Real.pi / 2)
      le_rfl (by positivity) (by linarith [Real.pi_pos]) hae hPsi2
  have hconv : ∫ u in (0 : ℝ)..(Real.pi / 2), Ψ u = ∫ θ in Work.Spaces.Iθ, Ψ θ := by
    rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact (MeasureTheory.integral_Icc_eq_integral_Ioc (f := Ψ) (x := (0 : ℝ))
      (y := Real.pi / 2)).symm
  exact ⟨hIntOn, by rw [hmain]; exact h1.trans (le_of_eq hconv)⟩

end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.H2.DivSinQR.zSlotHardy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivSinQR

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The honest power-weight Hardy inequality (delegated) -/

/-! ## The honest power-weight Hardy inequality on the open interval `(0,a)` -/






/-! ## Reflection and splitting bookkeeping -/



/-- Splitting an integral over `Iθ` into the two halves. -/
private lemma integral_Iθ_split {G : ℝ → ℝ} (h1 : IntervalIntegrable G volume 0 (Real.pi / 4))
    (h2 : IntervalIntegrable G volume (Real.pi / 4) (Real.pi / 2)) :
    (∫ θ in Work.Spaces.Iθ, G θ)
      = (∫ θ in Set.Ioo 0 (Real.pi / 4), G θ)
        + ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), G θ := by
  have h4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have h4le : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h2le : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le h2le]
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le h4, ← intervalIntegral.integral_of_le h4le]
  exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm



private lemma integrableOn_of_le {s : Set ℝ} {f g : ℝ → ℝ} (hms : MeasurableSet s)
    (hg : MeasureTheory.IntegrableOn g s) (hf : AEStronglyMeasurable f (volume.restrict s))
    (hnn : ∀ x ∈ s, 0 ≤ f x) (hle : ∀ x ∈ s, f x ≤ g x) : MeasureTheory.IntegrableOn f s := by
  have hg' : Integrable g (volume.restrict s) := hg
  refine hg'.mono' hf ?_
  rw [MeasureTheory.ae_restrict_iff' hms]
  filter_upwards with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn x hx)]
  exact hle x hx

/-! ## The target theorem -/


end Work.FTS.H2.DivSinQR
end
end
-- ===== merged: Submission.Work.FTS.H2.HQ.HardyZQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.HQ

theorem HardyZQ (v : ℝ → ℝ) (hcd : ContDiffOn ℝ 1 v (Set.Ioi (0 : ℝ)))
    (hdec : Filter.Tendsto v Filter.atTop (nhds 0))
    (hint : MeasureTheory.IntegrableOn
      (fun s => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz) :
    ∀ z ∈ Set.Ioi (0 : ℝ), (v z) ^ 2 ≤ MeasureTheory.integral
      (MeasureTheory.volume.restrict Work.Spaces.Iz)
      (fun s => (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2) := by
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  have hz0 : 0 ≤ z := le_of_lt hzpos
  -- `v` is continuous on `(0,∞)` and `deriv v` is continuous there
  have hvcont : ContinuousOn v (Set.Ioi (0 : ℝ)) := hcd.continuousOn
  have hdvcontU : ContinuousOn (derivWithin v (Set.Ioi (0 : ℝ))) (Set.Ioi (0 : ℝ)) :=
    hcd.continuousOn_derivWithin isOpen_Ioi.uniqueDiffOn le_rfl
  have hdvcont : ContinuousOn (deriv v) (Set.Ioi (0 : ℝ)) :=
    hdvcontU.congr (fun x hx => (derivWithin_of_isOpen isOpen_Ioi hx).symm)
  have hdiff : DifferentiableOn ℝ v (Set.Ioi (0 : ℝ)) := hcd.differentiableOn one_ne_zero
  set P : ℝ := ∫ s in Work.Spaces.Iz, (s * deriv v s) ^ 2 * (Work.Spaces.w s) ^ 2 with hPdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]; exact integral_nonneg fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- the fundamental theorem of calculus for `v` on `[z,B]`
  have hFTC : ∀ B, z ≤ B → ∫ s in z..B, deriv v s = v B - v z := by
    intro B hzB
    have hderiv : ∀ x ∈ Set.Ioo z B, HasDerivAt v (deriv v x) x := by
      intro x hx
      have hxmem : x ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith [hx.1])
      exact (hdiff.differentiableAt (isOpen_Ioi.mem_nhds hxmem)).hasDerivAt
    have hcont : ContinuousOn v (Set.Icc z B) :=
      hvcont.mono (fun x hx => Set.mem_Ioi.mpr (by linarith [hx.1]))
    have hintv : IntervalIntegrable (deriv v) volume z B := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hzB]
      exact hdvcont.mono (fun x hx => Set.mem_Ioi.mpr (by linarith [hx.1]))
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hzB hcont hderiv hintv
  -- continuity of the two Cauchy–Schwarz factors on `uIcc z B`
  have hAc : ∀ {B}, z ≤ B → ContinuousOn (fun s => s * deriv v s * Work.Spaces.w s)
      (Set.uIcc z B) := by
    intro B hzB
    rw [Set.uIcc_of_le hzB]
    refine (continuousOn_id.mul ?_).mul ?_
    · exact hdvcont.mono (fun x hx => Set.mem_Ioi.mpr (by linarith [hx.1]))
    · unfold Work.Spaces.w
      apply ContinuousOn.div
      · exact (continuousOn_const.add continuousOn_id).pow 2
      · exact continuousOn_id.pow 2
      · intro x hx
        have : 0 < x := by linarith [hx.1]
        positivity
  have hψc : ∀ {B}, z ≤ B → ContinuousOn (fun s => s / (1 + s) ^ 2) (Set.uIcc z B) := by
    intro B hzB
    rw [Set.uIcc_of_le hzB]
    apply ContinuousOn.div
    · exact continuousOn_id
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · intro x hx
      have : 0 < x := by linarith [hx.1]
      positivity
  -- the key bound, for every `B ≥ z`
  have hkey : ∀ B, z ≤ B → |v z| ≤ |v B| + Real.sqrt P := by
    intro B hzB
    have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt z B hzB (hAc hzB) (hψc hzB)
    have hcongr : ∫ x in z..B, (x * deriv v x * Work.Spaces.w x) * (x / (1 + x) ^ 2)
        = ∫ x in z..B, deriv v x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hzB] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      simp only [Work.Spaces.w]
      field_simp
    have hA2le : ∫ x in z..B, (x * deriv v x * Work.Spaces.w x) ^ 2 ≤ P := by
      have h1 : ∫ x in z..B, (x * deriv v x * Work.Spaces.w x) ^ 2
          = ∫ x in z..B, (x * deriv v x) ^ 2 * (Work.Spaces.w x) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x _; ring
      rw [h1, hPdef]
      exact Work.Spaces.hardyZ_integral_Ioc_le_integral_Iz hz0 hzB hint
        (fun s _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hψle : ∫ x in z..B, (x / (1 + x) ^ 2) ^ 2 ≤ 1 :=
      Work.Spaces.hardyZ_integral_psi_sq_le_one hz0 hzB
    have hchain : |∫ x in z..B, deriv v x| ≤ Real.sqrt P := by
      rw [← hcongr]
      calc |∫ x in z..B, (x * deriv v x * Work.Spaces.w x) * (x / (1 + x) ^ 2)|
          ≤ Real.sqrt (∫ x in z..B, (x * deriv v x * Work.Spaces.w x) ^ 2) *
              Real.sqrt (∫ x in z..B, (x / (1 + x) ^ 2) ^ 2) := hcs
        _ ≤ Real.sqrt P * Real.sqrt 1 := by
            exact mul_le_mul (Real.sqrt_le_sqrt hA2le) (Real.sqrt_le_sqrt hψle)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = Real.sqrt P := by rw [Real.sqrt_one, mul_one]
    have hchain' : |v B - v z| ≤ Real.sqrt P := by
      rw [← hFTC B hzB]; exact hchain
    have hsplit : v z = v B - (v B - v z) := by ring
    calc |v z| = |v B - (v B - v z)| := congrArg abs hsplit
      _ ≤ |v B| + |v B - v z| := abs_sub _ _
      _ ≤ |v B| + Real.sqrt P := by linarith [hchain']
  have hlim : Tendsto (fun B => |v B| + Real.sqrt P) atTop (nhds (Real.sqrt P)) := by
    have habs : Tendsto (fun B => |v B|) atTop (nhds 0) := by simpa using hdec.abs
    simpa using habs.add_const (Real.sqrt P)
  have hev : ∀ᶠ B in atTop, |v z| ≤ |v B| + Real.sqrt P :=
    (eventually_ge_atTop z).mono fun B hB => hkey B hB
  have hle : |v z| ≤ Real.sqrt P := ge_of_tendsto hlim hev
  calc (v z) ^ 2 = |v z| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt P) ^ 2 := by nlinarith [hle, abs_nonneg (v z), Real.sqrt_nonneg P]
    _ = P := Real.sq_sqrt hPnn

end Work.FTS.H2.HQ
end
end
-- ===== merged: Submission.Work.FTS.H2.HkIntegrandSlotSum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2


end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.H2.ModalSol.ModeIdent.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSol.ModeIdent

set_option autoImplicit false

/-- The angular weight `e_m(θ)·cos θ` of the mode-`m` pairing. -/
def pw (m : ℕ) (θ : ℝ) : ℝ := Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ


/-- The angular eigenfunction is `C³` (indeed `C^∞`). -/
theorem contDiff_eFam (m : ℕ) : ContDiff ℝ 3 (Work.FTS.PhiStar.Gegenbauer.eFam m) :=
  Real.contDiff_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).comp Real.contDiff_sin)

/-- The angular eigenfunction is continuous. -/
theorem continuous_eFam (m : ℕ) : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) :=
  (contDiff_eFam m).continuous


/-! ## Vanishing of the iterated derivatives off the support -/



/-- If the `θ`-slice `F z ·` vanishes on an *open* set `V`, then the iterated `θ`-derivatives
vanish there. -/
theorem pthIter_eq_zero_of_isOpen_zero {F : ℝ → ℝ → ℝ} {z : ℝ} {V : Set ℝ} (hV : IsOpen V)
    (h0 : ∀ θ ∈ V, F z θ = 0) :
    ∀ k, ∀ θ ∈ V, Work.Spaces.pthIter k F z θ = 0 := by
  intro k
  induction k with
  | zero => intro θ hθ; exact h0 θ hθ
  | succ k ih =>
    intro θ hθ
    rw [Work.Spaces.pthIter_succ]
    show deriv (fun θ' => Work.Spaces.pthIter k F z θ') θ = 0
    have hconst : (fun θ' => Work.Spaces.pthIter k F z θ') =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
      filter_upwards [hV.mem_nhds hθ] with θ' hθ'
      exact ih θ' hθ'
    rw [hconst.deriv_eq, deriv_const]

/-- If the `θ`-slice `F z ·` is eventually zero at `θ`, then its iterated `θ`-derivatives
vanish at `θ`. -/
theorem pthIter_eq_zero_of_eventually {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ θ' in 𝓝 θ, F z θ' = 0) (k : ℕ) :
    Work.Spaces.pthIter k F z θ = 0 := by
  obtain ⟨V, hVN, hVopen, hθV⟩ := mem_nhds_iff.mp h
  exact pthIter_eq_zero_of_isOpen_zero hVopen (fun θ' hθ' => hVN hθ') k θ hθV

end Work.FTS.H2.ModalSol.ModeIdent
end
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.contOn_primitive_Ioc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

/-- Continuity on `(0,∞)` of the primitive `z ↦ ∫ t in (0)..z, c t · w t`, for `c ∈ L²(0,∞)`
(only `∫ c² < ∞` is assumed, plus a.e. strong measurability of `c`, since the Bochner integral
returns `0` for non-integrable integrands) and `w` continuous on `(0,∞)`, assuming `c · w` is
integrable on `(0,z)` for every `z > 0`.  Route: `∫ t in (0)..z` is `∫_{Ioc 0 z}`
(`intervalIntegral.integral_of_le`); for `z₀ > 0` and `z` with `|z - z₀| ≤ z₀/2`, split the
difference with `setIntegral_union` and bound `|∫_{(z₀,z)} c w| ≤ M·∫_{(z₀,z)} |c| ≤
M·√(∫_{(z₀,z)} c²)·√|z - z₀|`, where `M` bounds `|w|` on the compact `[z₀/2, 3z₀/2]`
(`IsCompact.exists_bound_of_continuousOn`), Cauchy–Schwarz being applied to `√(c t ²)` and the
constant `1`. -/
theorem contOn_primitive_Ioc {c w : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hw : ContinuousOn w (Set.Ioi 0))
    (hint : ∀ z ∈ Set.Ioi 0,
      MeasureTheory.IntegrableOn (fun t => c t * w t) (Set.Ioc 0 z)) :
    ContinuousOn (fun z => ∫ t in (0 : ℝ)..z, c t * w t) (Set.Ioi 0) := by
  intro z₀ hz₀
  -- Pick `z₁ > z₀`.  The primitive is continuous on the compact segment `[0, z₁]`, which
  -- contains `z₀` in its interior, while `Ioi 0` is a neighbourhood of `z₀`.
  obtain ⟨z₁, hz₀z₁⟩ := exists_gt z₀
  have hz₁ : 0 < z₁ := lt_trans hz₀ hz₀z₁
  -- `IntegrableOn` transfers across the null set `{0}`.
  have hInt : MeasureTheory.IntegrableOn (fun t => c t * w t) (Set.Icc 0 z₁) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hint z₁ hz₁
  -- The set-integral primitive is continuous (dominated convergence).
  have hprim : ContinuousOn (fun x : ℝ => (∫ t in Set.Ioc 0 x, c t * w t : ℝ))
      (Set.Icc 0 z₁) :=
    intervalIntegral.continuousOn_primitive (E := ℝ) (f := fun t => c t * w t)
      (a := 0) (b := z₁) (μ := MeasureTheory.volume) hInt
  -- On `[0, z₁]` the interval integral is the set integral over `Ioc 0 x`.
  have hcongr : Set.EqOn (fun x : ℝ => (∫ t in (0 : ℝ)..x, c t * w t : ℝ))
      (fun x : ℝ => (∫ t in Set.Ioc 0 x, c t * w t : ℝ)) (Set.Icc 0 z₁) := by
    intro x hx
    exact intervalIntegral.integral_of_le (E := ℝ) (f := fun t => c t * w t)
      (μ := MeasureTheory.volume) (a := 0) (b := x) hx.1
  have hcont : ContinuousOn (fun x : ℝ => (∫ t in (0 : ℝ)..x, c t * w t : ℝ))
      (Set.Icc 0 z₁) :=
    hprim.congr hcongr
  exact (hcont.continuousAt (Icc_mem_nhds hz₀ hz₀z₁)).continuousWithinAt

end Work.FTS.H2.ModalSolR
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.contOn_tailIoi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.H2.ModalSolR

/-- **Continuity of the tail integral at a fixed lower limit.**  If `f` is integrable on the
tail `Set.Ioi a`, then the map `z ↦ ∫ t in Set.Ioi z, f t` is continuous at every point of
`Set.Ioi a`.

Proof: fix `z₀ ∈ Ioi a` and let `μ = volume.restrict (Ioi a)`.  For `z ∈ Ioi a` one has
`∫ t in Ioi z, f t = ∫ t, (Set.Ioi z).indicator f t ∂μ` (`MeasureTheory.integral_indicator`
together with `Measure.restrict_restrict_of_subset`), so the claim follows from Lebesgue's
dominated convergence theorem for filters (`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`),
with dominating function `t ↦ ‖f t‖` (integrable on `Ioi a`) and pointwise limit
`(Set.Ioi z).indicator f t → (Set.Ioi z₀).indicator f t` for every `t ≠ z₀`; the exceptional
point `z₀` is null.  The limit function integrates to `∫ t in Set.Ioi z₀, f t`, again by
`MeasureTheory.integral_indicator` and `Measure.restrict_restrict_of_subset`. -/
theorem continuousOn_integral_Ioi {f : ℝ → ℝ} {a : ℝ}
    (hf : MeasureTheory.IntegrableOn f (Set.Ioi a)) :
    ContinuousOn (fun z => ∫ t in Set.Ioi z, f t) (Set.Ioi a) := by
  intro z₀ hz₀
  -- the a.e. pointwise convergence of the indicator functions
  have hlim : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi a)),
      Tendsto (fun z => (Set.Ioi z).indicator f t) (𝓝[Set.Ioi a] z₀)
        (𝓝 ((Set.Ioi z₀).indicator f t)) := by
    have h1 : (MeasureTheory.volume.restrict (Set.Ioi a)) {z₀} = 0 := by
      rw [Measure.restrict_apply (measurableSet_singleton z₀)]
      exact measure_mono_null Set.inter_subset_left Real.volume_singleton
    have h2 : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi a)), t ∈ ({z₀} : Set ℝ)ᶜ :=
      MeasureTheory.compl_mem_ae_iff.2 h1
    filter_upwards [h2] with t ht
    rcases lt_trichotomy t z₀ with h | h | h
    · -- `t < z₀`: eventually `z > t`, so both indicator functions vanish at `t`
      have hev : ∀ᶠ z in 𝓝[Set.Ioi a] z₀, t < z := by
        rw [eventually_nhdsWithin_iff]
        filter_upwards [Ioi_mem_nhds h] with z hz _
        exact hz
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hev] with z hz
      rw [Set.indicator_of_notMem (s := Set.Ioi z₀) (by rw [Set.mem_Ioi]; exact not_lt.mpr h.le),
        Set.indicator_of_notMem (s := Set.Ioi z) (by rw [Set.mem_Ioi]; exact not_lt.mpr hz.le)]
    · -- `t = z₀`, excluded by the a.e. statement
      exact absurd h ht
    · -- `z₀ < t`: eventually `z < t`, so both indicator functions are `f t`
      have hev : ∀ᶠ z in 𝓝[Set.Ioi a] z₀, z < t := by
        rw [eventually_nhdsWithin_iff]
        filter_upwards [Iio_mem_nhds h] with z hz _
        exact hz
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hev] with z hz
      rw [Set.indicator_of_mem (s := Set.Ioi z₀) (by rw [Set.mem_Ioi]; exact h),
        Set.indicator_of_mem (s := Set.Ioi z) (by rw [Set.mem_Ioi]; exact hz)]
  -- dominated convergence
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict (Set.Ioi a))
    (l := 𝓝[Set.Ioi a] z₀)
    (F := fun z t => (Set.Ioi z).indicator f t)
    (f := fun t => (Set.Ioi z₀).indicator f t)
    (bound := fun t => ‖f t‖)
    (Filter.Eventually.of_forall fun z => hf.aestronglyMeasurable.indicator measurableSet_Ioi)
    (Filter.Eventually.of_forall fun z =>
      Filter.Eventually.of_forall fun t => norm_indicator_le_norm_self (s := Set.Ioi z) f t)
    hf.norm
    hlim
  -- the limit value
  have hcod : (∫ t, (Set.Ioi z₀).indicator f t ∂(MeasureTheory.volume.restrict (Set.Ioi a)))
      = ∫ t in Set.Ioi z₀, f t := by
    rw [MeasureTheory.integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict_of_subset (Set.Ioi_subset_Ioi hz₀.le)]
  -- the function whose integral the DCT controls is `z ↦ ∫ t in Ioi z, f t` on `Ioi a`
  have hdom : (fun z => ∫ t, (Set.Ioi z).indicator f t ∂(MeasureTheory.volume.restrict (Set.Ioi a)))
      =ᶠ[𝓝[Set.Ioi a] z₀] (fun z => ∫ t in Set.Ioi z, f t) :=
    eventually_nhdsWithin_of_forall fun z hz => by
      show (∫ t, (Set.Ioi z).indicator f t ∂(MeasureTheory.volume.restrict (Set.Ioi a)))
        = ∫ t in Set.Ioi z, f t
      rw [MeasureTheory.integral_indicator measurableSet_Ioi,
        Measure.restrict_restrict_of_subset (Set.Ioi_subset_Ioi hz.le)]
  have hres := Filter.Tendsto.congr' hdom hDCT
  rw [hcod] at hres
  exact hres

set_option linter.unusedVariables false

/-- Continuity on `(0,∞)` of the tail integral `z ↦ ∫ t in Set.Ioi z, c t · w t`, under the same
hypotheses as `contOn_primitive_Ioc` except that the integrability of `c · w` is assumed on the
tail `Set.Ioi z` for every `z > 0`.  Route: for `z₀ > 0` and `z` near `z₀`, write the difference
with `intervalIntegral.integral_Ioi_sub_Ioi'` (which gives `∫_{Ioi z₀} - ∫_{Ioi z} = ∫_{z₀}^{z}`,
and `∫_{Ioi z} - ∫_{Ioi z₀} = ∫_z^{z₀}` in the other direction) and bound
`|∫_{(z₀,z)} c w| ≤ M·√(∫_{(z₀,z)} c²)·√|z - z₀|` with `M` a bound for `w` on the compact
`[z₀/2, 3z₀/2]`. -/
theorem contOn_tailIoi {c w : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hw : ContinuousOn w (Set.Ioi 0))
    (hint : ∀ z ∈ Set.Ioi 0,
      MeasureTheory.IntegrableOn (fun t => c t * w t) (Set.Ioi z)) :
    ContinuousOn (fun z => ∫ t in Set.Ioi z, c t * w t) (Set.Ioi 0) := by
  -- `Continuity on (0,∞)` is a local statement: at `z₀ > 0` it is continuity of the tail
  -- integral with lower limit `z₀/2`, which is a genuine tail (so `c * w` is integrable on it)
  -- and, being an open neighbourhood of `z₀`, has the same neighbourhood filter.
  intro z₀ hz₀
  have hhalf : (0 : ℝ) < z₀ / 2 := by linarith [show (0 : ℝ) < z₀ from hz₀]
  have hlt : z₀ / 2 < z₀ := by linarith
  have hcont : ContinuousWithinAt (fun z => ∫ t in Set.Ioi z, c t * w t) (Set.Ioi (z₀ / 2)) z₀ :=
    continuousOn_integral_Ioi (f := fun t => c t * w t) (a := z₀ / 2)
      (hint (z₀ / 2) hhalf) z₀ hlt
  have hca : ContinuousAt (fun z => ∫ t in Set.Ioi z, c t * w t) z₀ :=
    (continuousWithinAt_iff_continuousAt (Ioi_mem_nhds hlt)).mp hcont
  exact hca.continuousWithinAt

end Work.FTS.H2.ModalSolR
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.integrableOn_Ioc_mul_rpow_sub_one =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

open MeasureTheory

/-- For `c` with `∫_0^∞ c² < ∞` and `β ≥ 1`, the function `t ↦ c t · t ^ (β - 1)` is integrable
on `(0,z]` for every `z > 0`.  Route: `t ^ (β-1) ≤ z ^ (β-1)` on `(0,z]`, so it suffices that
`√(c t ²) ∈ L¹((0,z])`, which is Cauchy–Schwarz for `√(c t ²)` and the constant `1` on the
finite-measure set `(0,z]` (using `√(c t ²) = |c t|` and `∫_0^z c² ≤ ∫_0^∞ c²`). -/
theorem integrableOn_Ioc_mul_rpow_sub_one {c : ℝ → ℝ} {β z : ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hβ : 1 ≤ β) (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun t => c t * t ^ (β - 1)) (Set.Ioc 0 z) := by
  have hβ' : 0 ≤ β - 1 := by linarith
  have hzβ : 0 ≤ z ^ (β - 1) := Real.rpow_nonneg hz.le _
  -- `c²` is integrable on `(0,z]`, since `(0,z] ⊆ (0,∞)`.
  have hc' : Integrable (fun t => c t ^ 2) (MeasureTheory.volume.restrict (Set.Ioc 0 z)) :=
    hc.mono_set (fun _ ht => ht.1)
  -- the constant `1` is integrable on `(0,z]`, a set of finite measure.
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) (MeasureTheory.volume.restrict (Set.Ioc 0 z)) :=
    integrableOn_const (C := (1 : ℝ)) (hs := by simp)
  -- the dominating function `(z^(β-1)/2) * (c² + 1)`: AM–GM for `2|c t| ≤ (c t)² + 1`,
  -- together with the bound `t^(β-1) ≤ z^(β-1)` on `(0,z]`.
  have hdom : Integrable (fun t => (z ^ (β - 1) / 2) * (c t ^ 2 + 1))
      (MeasureTheory.volume.restrict (Set.Ioc 0 z)) := by
    have h1 : Integrable (fun t => c t ^ 2 + 1) _ := hc'.add hconst
    exact h1.const_mul (z ^ (β - 1) / 2)
  refine Integrable.mono' hdom ?_ ?_
  · have h1 : AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioc 0 z)) :=
      hcm.mono_measure (Measure.restrict_mono (fun _ ht => ht.1) le_rfl)
    have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ (β - 1))
        (MeasureTheory.volume.restrict (Set.Ioc 0 z)) :=
      ((Real.continuous_rpow_const hβ').measurable.aestronglyMeasurable).restrict
    exact h1.mul h2
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 ≤ t := ht.1.le
    have htnn : 0 ≤ t ^ (β - 1) := Real.rpow_nonneg ht0 _
    have hle : t ^ (β - 1) ≤ z ^ (β - 1) := Real.rpow_le_rpow ht0 ht.2 hβ'
    have h2 : 2 * |c t| ≤ c t ^ 2 + 1 := by
      nlinarith [sq_nonneg (|c t| - 1), abs_nonneg (c t), sq_abs (c t)]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg htnn]
    have key : |c t| * t ^ (β - 1) ≤ |c t| * z ^ (β - 1) :=
      mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    have key2 : 2 * (|c t| * z ^ (β - 1)) ≤ z ^ (β - 1) * (c t ^ 2 + 1) := by
      have h3 := mul_le_mul_of_nonneg_left h2 hzβ
      linarith
    linarith

end Work.FTS.H2.ModalSolR
end
-- ===== merged: Submission.Work.FTS.H2.PhiWeight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.H2

/-! ## The two auxiliary facts behind `PhiWeight`

The pointwise Hardy-weight comparison (on the open quadrant `z > 0`, `0 < θ < π/2`) and the
a.e. strong measurability of the weighted angular energy on `(0,∞)`. -/




end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.H2.StarPkg.SubstBsl =====
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


end Work.FTS.H2.StarPkg
end
end
-- ===== merged: Submission.Work.FTS.H2.T2EasyDefs =====
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

/-! ## The block decomposition of the "easy part" `Heasy`

`Heasy α f g = H4PairInt α (f·D_z g) g - Hhard α f g` is a sum of the sixteen
`H⁴`-pairing blocks of `u = f·D_z g` against those of `g`, minus the five "hard"
terms of `Hhard`, each of which equals exactly the block product whose `g`-factor
carries all five derivatives.  Removing those five cancellations block by block
leaves `Heasy` as a sum of products

  `EasyZ f g i · GblkZ g i`     (`i ≤ 4`, weight `Whz² = w²sin(2θ)^{-η}`),
  `EasyM α f g j i · GblkM α g j i`  (`1 ≤ i`, `i+j ≤ 4`, weight `Wm² = w²sin(2θ)^{-γ}`),

where the `g`-blocks are the summands of `HkIntegrand α 4 g` and each "easy block"
has the *same* weight as its `g`-partner.  Hence the pointwise Cauchy–Schwarz
inequality bounds `|Heasy|` by `√(EasyU)·√(HkIntegrand α 4 g)`, with
`EasyU` the sum of the squares of the easy blocks.  -/







end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.Transport3Aux.Defs =====
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








end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.Whz_Wm_sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Squaring the two weights of the flat `ℋ⁴` pairing

The weights of `HkIntegrand` (`Submission/Work/Spaces/Defs.lean`, `Submission/Work/FTS/H2/Defs.lean`)
are square roots of the weights that actually appear in the energy:

* `Whz z θ = w z / sin(2θ)^{η/2}`, so `Whz z θ ^ 2 = w z ^ 2 · sin(2θ)^{-η}`;
* `Wm α z θ = W α z θ = w z · sin(2θ)^{-γ/2}`, so `Wm α z θ ^ 2 = w z ^ 2 · sin(2θ)^{-γ}`.

Both identities are pure `rpow` algebra on the base `a = sin(2θ) ≥ 0` (the sign is
the only place the hypothesis `θ ∈ Iθ` is used); at `θ = 0` and `θ = π/2` the
identity survives Lean's totalised `rpow` at `a = 0` because `0 ^ x = 0` for
`x ≠ 0`.  Note that squaring is *not* removed at `θ ∈ {0, π/2}`: the two sides are
both `0` there.
-/

namespace Work.FTS.H2

set_option autoImplicit false

/-- `sin (2θ) ≥ 0` on the angular interval `Iθ = [0, π/2]`: this is the only use of
the hypothesis `θ ∈ Iθ` in `Whz_Wm_sq`. -/
theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  have h1 : (0 : ℝ) ≤ θ := hθ.1
  have h2 : θ ≤ Real.pi / 2 := hθ.2
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩

/-- `(a ^ p) ^ 2 = a ^ (p * 2)` for `a ≥ 0`.  The natural-number power on the left is
converted to a real one by `Real.rpow_natCast` before `Real.rpow_mul` is applied. -/
theorem sq_rpow_mul_two {a : ℝ} (ha : 0 ≤ a) (p : ℝ) : (a ^ p) ^ 2 = a ^ (p * 2) := by
  rw [← Real.rpow_natCast (a ^ p) 2]
  exact (Real.rpow_mul ha p 2).symm

theorem Whz_Wm_sq (α : ℝ) (hα : 0 < α) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.H2.Whz z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) ∧
      (Work.FTS.H2.Wm α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have ha : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  refine ⟨?_, ?_⟩
  · -- `Whz`: pull the division out of the square as an inverse `rpow`, then square.
    have h1 : Whz z θ
        = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
      rw [Whz_eq, div_eq_mul_inv, ← Real.rpow_neg ha (Work.Spaces.eta / 2)]
    rw [h1, mul_pow, sq_rpow_mul_two ha (-(Work.Spaces.eta / 2))]
    rw [show (-(Work.Spaces.eta / 2)) * 2 = -Work.Spaces.eta by ring]
  · -- `Wm`: the angular weight already carries the negative half exponent.
    have h1 : Wm α z θ
        = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
      rw [Wm_eq, Work.Spaces.Wt, Work.Spaces.wTheta]
    rw [h1, mul_pow, sq_rpow_mul_two ha (-(Work.Spaces.gam α / 2))]
    rw [show (-(Work.Spaces.gam α / 2)) * 2 = -(Work.Spaces.gam α) by ring]

end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.LocData.abs_zpow_mul_Gker_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real

namespace Work.FTS.LocData

set_option autoImplicit false


end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.LocData.hasDerivAt_Gker =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.LocData

set_option autoImplicit false


end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.N4Fields.wlInf_of_pointwise_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.N4Fields

theorem wlInf_of_pointwise_bounds {α B : ℝ} {h : ℝ → ℝ → ℝ} (hB : 0 ≤ B)
    (hr : ∀ k : ℕ, k ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k h z θ| ≤ B)
    (ht : ∀ j k : ℕ, 1 ≤ j → k + j ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j h) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ B) :
    Work.Spaces.WlInfMem α 4 h ∧ Work.Spaces.WlInf α 4 h ≤ 30 * B := by
  constructor
  · -- membership: every supremum occurring in `WlInf` is bounded by `B`
    refine ⟨fun k _ => ⟨B, fun y hy => ?_⟩, fun j _ k _ hj hjk => ⟨B, fun y hy => ?_⟩⟩
    · rcases hy with ⟨z, hz, θ, hθ, rfl⟩
      exact hr k (by omega) z hz θ hθ
    · rcases hy with ⟨z, hz, θ, hθ, rfl⟩
      exact ht j k hj hjk z hz θ hθ
  · -- every one of the `15 ≤ 25` summands is bounded by `B`
    have hzsum : (∑ k ∈ Finset.range 5, Work.Spaces.supAbs (fun z θ =>
        (z + 1) ^ k * Work.Spaces.pzIter k h z θ))
        ≤ ∑ k ∈ Finset.range 5, B := by
      apply Finset.sum_le_sum
      intro k hk
      exact Work.Spaces.supAbs_le fun z hz θ hθ =>
        hr k (by have := Finset.mem_range.mp hk; omega) z hz θ hθ
    have hmsum : (∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
        (if 1 ≤ j ∧ k + j ≤ 4 then Work.Spaces.supAbs (fun z θ =>
          (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j h) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0))
        ≤ ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5, B := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      split_ifs with hc
      · exact Work.Spaces.supAbs_le fun z hz θ hθ => ht j k hc.1 hc.2 z hz θ hθ
      · exact hB
    have hB5 : (∑ _k ∈ Finset.range 5, B) = 5 * B := by
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hB25 : (∑ _j ∈ Finset.range 5, ∑ _k ∈ Finset.range 5, B) = 25 * B := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    calc Work.Spaces.WlInf α 4 h
        = (∑ k ∈ Finset.range 5, Work.Spaces.supAbs (fun z θ =>
              (z + 1) ^ k * Work.Spaces.pzIter k h z θ))
          + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
              (if 1 ≤ j ∧ k + j ≤ 4 then Work.Spaces.supAbs (fun z θ =>
                (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j h) z θ
                  * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0) := rfl
      _ ≤ (∑ _k ∈ Finset.range 5, B) + ∑ _j ∈ Finset.range 5, ∑ _k ∈ Finset.range 5, B :=
          add_le_add hzsum hmsum
      _ = 5 * B + 25 * B := by rw [hB25, hB5]
      _ = 30 * B := by ring

end Work.FTS.Nonlinear.N4Fields
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row19Prep.Defs =====
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

/-! ## The vocabulary -/

/-- The radial factor `H₂(z) = 2z²(1-z)/(1+z)⁴ = (z/(1+z))·H(z)` of the row-19 piece. -/
def H2b (z : ℝ) : ℝ := 2 * z ^ 2 * (1 - z) / (1 + z) ^ 4

/-- `H₂ = z²·Ψ` with `Ψ(z) = 2(1-z)/(1+z)⁴ = 4/(1+z)⁴ - 2/(1+z)³`; the `z²` is what makes
`H₂·(1+z)·w(z)·z^{m-2}` bounded at the origin. -/
def Psi (z : ℝ) : ℝ := 2 * (1 - z) / (1 + z) ^ 4



/-- The angular factor `Γ` lifted to a function on the quadrant. -/
def GamF (α : ℝ) : ℝ → ℝ → ℝ := fun _ θ => Work.Spaces.Gam α θ

/-- The (un-normalised) row-19 product `α·Γ·(A·H₂)`: `V(Φ̃_*)·D_zF_* = (1/c(α))·Zf α A`. -/
def Zf (α : ℝ) (A : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => α * Work.Spaces.Gam α θ * (A z θ * H2b z)

@[simp] theorem GamF_apply (α z θ : ℝ) : GamF α z θ = Work.Spaces.Gam α θ := rfl

@[simp] theorem Zf_apply (α : ℝ) (A : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Zf α A z θ = α * Work.Spaces.Gam α θ * (A z θ * H2b z) := rfl

/-! ## Elementary facts about the radial factor -/



/-- `|1 - z| ≤ 1 + z` for `z ≥ 0`. -/
theorem abs_one_sub_le {z : ℝ} : |1 - z| ≤ 1 + z ↔ 0 ≤ z := by
  rw [abs_sub_le_iff]
  constructor
  · intro h; linarith [h.1]
  · intro h; exact ⟨by linarith, by linarith⟩


/-- The weighted bound used at order `0`: `(1+z)·w(z)·|H₂(z)| ≤ 2`. -/
theorem one_add_mul_w_mul_abs_H2b_le {z : ℝ} (hz : 0 < z) :
    (1 + z) * Work.Spaces.w z * |H2b z| ≤ 2 := by
  have h1 : (0 : ℝ) < (1 + z) ^ 4 := by positivity
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have h2 : |1 - z| ≤ 1 + z := abs_one_sub_le.mpr hz.le
  have h3 : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
  have hH : |H2b z| = 2 * z ^ 2 * |1 - z| / (1 + z) ^ 4 := by
    rw [H2b, abs_div, abs_of_pos h1, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg (sq_nonneg z)]
  have h4 : (1 + z) * ((1 + z) ^ 2 / z ^ 2) * (2 * z ^ 2 * |1 - z| / (1 + z) ^ 4)
      = 2 * |1 - z| / (1 + z) := by
    field_simp
  rw [h3, hH, h4]
  rw [div_le_iff₀ hz1]
  linarith

theorem Gam_nonneg {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1


theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])







/-! ## The two degenerate factors: `z`-derivatives kill a `θ`-only factor, and conversely -/

/-- `∂_z^c` of a function of `θ` alone is `0` for `c ≥ 1`. -/
theorem pzIter_theta_only (a : ℝ → ℝ) (c : ℕ) :
    Work.Spaces.pzIter c (fun z θ => a θ) = fun z θ => if c = 0 then a θ else 0 := by
  induction c with
  | zero => rfl
  | succ c ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      show deriv (fun z' : ℝ => (if c = 0 then a θ else (0 : ℝ))) z
        = (if c + 1 = 0 then a θ else 0)
      rw [deriv_const]
      simp

/-- `D_θ^{n+1}` of a function of `z` alone is `0`. -/
theorem DthIter_succ_z_only (φ : ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DthIter (n + 1) (fun z θ => φ z) = fun (_ : ℝ) (_ : ℝ) => (0 : ℝ) := by
  induction n with
  | zero =>
      funext z θ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.Dth,
        Work.Spaces.pth]
      simp [deriv_const]
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by ring, Work.Spaces.DthIter_succ, ih]
      funext z θ
      rw [Work.Spaces.Dth, Work.Spaces.pth]
      simp [deriv_const]

/-- `D_θ^n` of a function of `z` alone is `0` for `n ≥ 1`. -/
theorem DthIter_z_only (φ : ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DthIter n (fun z θ => φ z)
      = if n = 0 then (fun z θ => φ z) else fun (_ : ℝ) (_ : ℝ) => (0 : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
    rw [if_neg (Nat.succ_ne_zero m)]
    exact DthIter_succ_z_only φ m

end Work.FTS.Nonlinear.Open.Row19Prep
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Bookkeeping vocabulary for row 15 (`N₂^{ss}`)

If at some `z > 0` the mixed derivatives of `f` satisfy the pointwise bound

`|D_z^j D_θ^i f(z,θ)·w(z)| ≤ K·α³·(Cs+1)·Γ(θ)·(1+log(1+z))/(1+z)`   (`i + j ≤ 4`),

then each of the fifteen terms of `HkIntegrand α 4 f z θ` is bounded by the square of
that quantity times an angular weight.  Collecting the terms gives

`HkIntegrand α 4 f z θ ≤ (K·α³·(Cs+1))² · rlog(z)² · Gwt α θ`,

with `rlog` and `Gwt` as defined below, and the whole point of the row-15 bookkeeping is
that both factors are integrable with explicit constants (`∫_z rlog² ≤ 100`,
`∫_θ Gwt ≤ 2000/α`), so that `HkSq α 4 f ≤ 10¹²·K²·(Cs+1)²·α⁴`.

The two remaining ingredients (`HkIntegrand_le_of_mixed_bound`, the θ-integral and the
z-integral of the two weights) are proved in the sibling modules; this file only fixes the
vocabulary they share.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

/-- The radial bookkeeping weight `z ↦ (1 + log(1+z))/(1+z)` of the row-15 pointwise bound.
It is nonnegative for `z ≥ 0` and its square integrates to at most `100` over `[0,∞)`. -/
def rlog (z : ℝ) : ℝ := (1 + Real.log (1 + z)) / (1 + z)

@[simp] theorem rlog_def (z : ℝ) : rlog z = (1 + Real.log (1 + z)) / (1 + z) := rfl




/-- `Γ(θ) ≤ sin(2θ)^{α/5}` on `Iθ` for `α > 0`.  This is the angular weight estimate
that turns `Γ(θ)²·sin(2θ)^{-q}` into the single `rpow` weight `sin(2θ)^{2α/5-q}`.

It is proved inside `Work.Spaces.Gam_mul_weight_le` (as the step `hGam` of the proof of
`Gam_mul_weight_le`); we record it separately because several row-15 estimates need it. -/
theorem Gam_le_sin_two_rpow (α θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  set A : ℝ := Real.sin θ * Real.cos θ ^ 2 with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hGamA : Work.Spaces.Gam α θ = A ^ (α / 3) := by
    simp only [Work.Spaces.Gam]
    rw [hA]
  have he0 : 0 ≤ Real.sin (2 * θ) := by rw [Real.sin_two_mul]; positivity
  have hA5r : A ^ (5:ℝ) ≤ (Real.sin (2 * θ)) ^ (3:ℝ) := by
    have hm : A ^ 5 ≤ (Real.sin (2 * θ)) ^ 3 := by
      rw [hA, Real.sin_two_mul]
      have h1 : (Real.sin θ) ^ 2 * (Real.cos θ) ^ 7 ≤ 1 := by
        have a : (Real.sin θ) ^ 2 ≤ 1 := pow_le_one₀ (n := 2) hs0 hs1
        have b : (Real.cos θ) ^ 7 ≤ 1 := pow_le_one₀ (n := 7) hc0 hc1
        nlinarith [mul_le_mul a b (pow_nonneg hc0 7) (by norm_num : (0:ℝ) ≤ 1)]
      have hQ : 0 ≤ (Real.sin θ) ^ 3 * (Real.cos θ) ^ 3 := by positivity
      have step : ((Real.sin θ) ^ 2 * (Real.cos θ) ^ 7) * ((Real.sin θ) ^ 3 * (Real.cos θ) ^ 3)
          ≤ 1 * ((Real.sin θ) ^ 3 * (Real.cos θ) ^ 3) :=
        mul_le_mul_of_nonneg_right h1 hQ
      nlinarith [step, hQ, sq_nonneg (Real.sin θ * Real.cos θ)]
    simpa using hm
  have h1 : A ^ (α / 3) = (A ^ (5:ℝ)) ^ (α / 15) := by
    rw [← Real.rpow_mul hA0 5 (α / 15), show (5:ℝ) * (α / 15) = α / 3 by ring]
  have h2 : ((Real.sin (2 * θ)) ^ (3:ℝ)) ^ (α / 15) = (Real.sin (2 * θ)) ^ (α / 5) := by
    rw [← Real.rpow_mul he0 3 (α / 15), show (3:ℝ) * (α / 15) = α / 5 by ring]
  have h3 : (A ^ (5:ℝ)) ^ (α / 15) ≤ ((Real.sin (2 * θ)) ^ (3:ℝ)) ^ (α / 15) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hA0 5) hA5r (by linarith)
  rw [← h1, h2] at h3
  rwa [hGamA]


end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.LzeroBootstrap =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Bootstrap of the angular regularity for the ODE `Lzero u = h`

The `α = 0` part of the elliptic operator of Elgindi's elliptic section,
`Work.Elliptic.Lzero Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ`, is an *ordinary* differential
operator of order two in `θ` for functions that do not depend on the radial variable `z`:
for `Ψ = fun _ θ' => f θ'` one has

  `Lzero Ψ z θ = -f''(θ) + (tan θ · f)'(θ) - 6 f(θ)`.

Hence the equation `Lzero Ψ 0 · = h` can be solved for `f''`,

  `f'' = (tan · f)' - 6 f - h`   on `(0, π/2)`,

and since the right hand side is `C^{m-1}` as soon as `f` is `C^m` and `h` is `C^{m-1}`
(`tan` being smooth on `(0, π/2)`), one gets one more derivative for free: `f` is `C^{m+1}`.
This is the `LzeroBootstrap` below.  It is the standard gain of regularities used to read off
regularity of an angular profile from the regularity of its `Lzero`-image, and it is what lets
downstream arguments replace `h` by `Lzero` of a smooth function without losing control.

The statement does not need the assumption `2 ≤ m` in full strength: `m ≥ 1` suffices
(`m ≥ 2` is what the hypotheses of the original statement give).  We keep the hypothesis as
requested.
-/

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux.MomentChiaAux

/-- The `θ`-slice of `Lzero` on functions that do not depend on `z`: for `Ψ = fun _ θ' => f θ'`
and any `z` (in particular `z = 0`),

  `Lzero Ψ z θ = -f''(θ) + (tan θ · f)'(θ) - 6 f(θ)`. -/
theorem Lzero_of_thetaOnly (f : ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero (fun _ θ' => f θ') z θ
      = -deriv (deriv f) θ + deriv (fun t => Real.tan t * f t) θ - 6 * f θ := by
  simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
    Work.Spaces.pth]

/-- `tan` is smooth on the angular interval `(0, π/2)`. -/
theorem contDiffOn_tan_Ioo : ContDiffOn ℝ ⊤ Real.tan (Set.Ioo 0 (Real.pi / 2)) := by
  intro x hx
  rw [contDiffWithinAt_iff_contDiffAt (isOpen_Ioo.mem_nhds hx)]
  exact Real.contDiffAt_tan.2
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩).ne'

/-- **Bootstrap of angular regularity.**  If `f` is `C^m` on `(0, π/2)` and
`θ ↦ Lzero (fun _ θ' => f θ') 0 θ` is `C^{m-1}` there, then `f` is `C^{m+1}`.

The point is that the equation can be solved for the second derivative,

`f'' = (tan · f)' - 6 f - h`  on `(0, π/2)`,

and the right hand side is one order more regular than `f`, so the second derivative of `f` is
`C^{m-1}` while `f` itself is already `C^m`. -/
theorem LzeroBootstrap {f h : ℝ → ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hf : ContDiffOn ℝ m f (Set.Ioo 0 (Real.pi / 2)))
    (hh : ContDiffOn ℝ (m - 1) h (Set.Ioo 0 (Real.pi / 2)))
    (heq : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Elliptic.Lzero (fun _ θ' => f θ') 0 θ = h θ) :
    ContDiffOn ℝ (m + 1) f (Set.Ioo 0 (Real.pi / 2)) := by
  set s : Set ℝ := Set.Ioo 0 (Real.pi / 2) with hs
  have hs_open : IsOpen s := isOpen_Ioo
  have hm1 : 1 ≤ m := by omega
  -- the coercion `ℕ → ℕ∞ω` is additive, and `(m - 1) + 1 = m` since `m ≥ 1`
  have hcast : (((m - 1 : ℕ)) : ℕ∞ω) + 1 = (m : ℕ∞ω) := by
    have h : m - 1 + 1 = m := Nat.sub_add_cancel hm1
    exact_mod_cast h
  -- **Step 1.**  The equation, solved for the second derivative of `f`.
  have hpt : ∀ θ ∈ s, deriv (deriv f) θ
      = deriv (fun t => Real.tan t * f t) θ - 6 * f θ - h θ := by
    intro θ hθ
    have h1 := heq θ hθ
    rw [Lzero_of_thetaOnly f 0 θ] at h1
    linarith
  -- **Step 2.**  The right hand side is `C^{m-1}` on `s`.
  have htan : ContDiffOn ℝ m Real.tan s := contDiffOn_tan_Ioo.of_le le_top
  have htf : ContDiffOn ℝ m (fun θ => Real.tan θ * f θ) s := htan.mul hf
  have hdtf : ContDiffOn ℝ (m - 1) (deriv (fun θ => Real.tan θ * f θ)) s :=
    ContDiffOn.deriv_of_isOpen htf hs_open (le_of_eq hcast)
  have hf_le : ContDiffOn ℝ (m - 1) f s := hf.of_le (by
    calc (((m - 1 : ℕ)) : ℕ∞ω) ≤ (((m - 1 : ℕ)) : ℕ∞ω) + 1 := le_self_add
      _ = (m : ℕ∞ω) := hcast)
  have h6f : ContDiffOn ℝ (m - 1) (fun θ => (6 : ℝ) * f θ) s :=
    contDiffOn_const.mul hf_le
  have hg : ContDiffOn ℝ (m - 1)
      (fun θ => deriv (fun t => Real.tan t * f t) θ - 6 * f θ - h θ) s :=
    ((hdtf.sub h6f).sub hh).congr (fun _ _ => rfl)
  -- **Step 3.**  Transfer to the actual second derivative of `f`.
  have hdd : ContDiffOn ℝ (m - 1) (deriv (deriv f)) s :=
    hg.congr (fun θ hθ => hpt θ hθ)
  -- **Step 4.**  `deriv f` is `C^m`.
  have hdf' : ContDiffOn ℝ (m - 1) (deriv f) s :=
    ContDiffOn.deriv_of_isOpen hf hs_open (le_of_eq hcast)
  have hdiff : DifferentiableOn ℝ (deriv f) s := by
    refine hdf'.differentiableOn ?_
    have h : (((m - 1 : ℕ)) : ℕ∞ω) ≠ 0 := by
      exact_mod_cast (by omega : (m - 1) ≠ 0)
    exact h
  have hderivf : ContDiffOn ℝ m (deriv f) s := by
    have hmain : ContDiffOn ℝ ((((m - 1 : ℕ)) : ℕ∞ω) + 1) (deriv f) s :=
      (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (f := deriv f) (s := s)
        (n := (((m - 1 : ℕ)) : ℕ∞ω)) hs_open).mpr
        ⟨hdiff, (fun hc => absurd hc WithTop.coe_ne_top), hdd⟩
    rw [hcast] at hmain
    exact hmain
  -- **Step 5.**  `f` itself is `C^{m+1}`.
  have hfin : ContDiffOn ℝ ((m : ℕ∞ω) + 1) f s :=
    (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (f := f) (s := s)
      (n := (m : ℕ∞ω)) hs_open).mpr
      ⟨hf.differentiableOn (by exact_mod_cast (by omega : m ≠ 0)),
        (fun hc => absurd hc WithTop.coe_ne_top), hderivf⟩
  exact hfin

end Work.FTS.PhiStar.FlatWAux.MomentChiaAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.PzDthComm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.FTS.PhiStar.FlatWAux

namespace PzDthAux

set_option autoImplicit false

/-! ## Smoothness of the slice derivatives -/

/-- `∂_z` lowers the order of differentiability by one. -/
lemma pz_contDiffAt {G : ℝ → ℝ → ℝ} {y : ℝ × ℝ} {m : ℕ}
    (h : ContDiffAt ℝ (m + 1) (Function.uncurry G) y) :
    ContDiffAt ℝ m (Function.uncurry (Work.Spaces.pz G)) y := by
  have hfd : ContDiffAt ℝ m (fderiv ℝ (Function.uncurry G)) y := by
    have := ContDiffAt.fderiv_right (𝕜 := ℝ) h
      (by norm_num : ((m : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((m + 1 : ℕ) : ℕ∞))
    simpa using this
  have hfun : ContDiffAt ℝ m
      (fun y' : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) y') (1, 0)) y :=
    hfd.clm_apply contDiffAt_const
  refine ContDiffAt.congr_of_eventuallyEq hfun ?_
  filter_upwards [h.eventually (by simp)] with y' hy'
  have hd : DifferentiableAt ℝ (Function.uncurry G) y' := hy'.differentiableAt (by norm_num)
  have := Work.Spaces.deriv_slice_fst (Function.uncurry G) y'.1 y'.2 hd
  show Work.Spaces.pz G y'.1 y'.2 = _
  rw [show Work.Spaces.pz G y'.1 y'.2
      = deriv (fun z' => Function.uncurry G (z', y'.2)) y'.1 from rfl]
  exact this

/-- `∂_θ` lowers the order of differentiability by one. -/
lemma pth_contDiffAt {G : ℝ → ℝ → ℝ} {y : ℝ × ℝ} {m : ℕ}
    (h : ContDiffAt ℝ (m + 1) (Function.uncurry G) y) :
    ContDiffAt ℝ m (Function.uncurry (Work.Spaces.pth G)) y := by
  have hfd : ContDiffAt ℝ m (fderiv ℝ (Function.uncurry G)) y := by
    have := ContDiffAt.fderiv_right (𝕜 := ℝ) h
      (by norm_num : ((m : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((m + 1 : ℕ) : ℕ∞))
    simpa using this
  have hfun : ContDiffAt ℝ m
      (fun y' : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) y') (0, 1)) y :=
    hfd.clm_apply contDiffAt_const
  refine ContDiffAt.congr_of_eventuallyEq hfun ?_
  filter_upwards [h.eventually (by simp)] with y' hy'
  have hd : DifferentiableAt ℝ (Function.uncurry G) y' := hy'.differentiableAt (by norm_num)
  have := Work.Spaces.deriv_slice_snd (Function.uncurry G) y'.1 y'.2 hd
  show Work.Spaces.pth G y'.1 y'.2 = _
  rw [show Work.Spaces.pth G y'.1 y'.2
      = deriv (fun θ' => Function.uncurry G (y'.1, θ')) y'.2 from rfl]
  exact this


/-- `∂_z^i` lowers the order of differentiability by `i`. -/
lemma pzIter_contDiffAt {F : ℝ → ℝ → ℝ} {y : ℝ × ℝ} :
    ∀ (i m : ℕ), ContDiffAt ℝ (m + i) (Function.uncurry F) y →
      ContDiffAt ℝ m (Function.uncurry (Work.Spaces.pzIter i F)) y := by
  intro i
  induction i with
  | zero => intro m h; simpa using h
  | succ i ih =>
      intro m h
      have h' : ContDiffAt ℝ ((m + 1) + i) (Function.uncurry F) y := by
        convert h using 1
        push_cast
        ring
      have hG : ContDiffAt ℝ (m + 1) (Function.uncurry (Work.Spaces.pzIter i F)) y :=
        ih (m + 1) h'
      exact pz_contDiffAt hG

/-- `D_θ = sin(2θ) ∂_θ` lowers the order of differentiability by one (the coefficient
`sin(2θ)` is smooth, so it costs nothing). -/
lemma Dth_contDiffAt {G : ℝ → ℝ → ℝ} {y : ℝ × ℝ} {m : ℕ}
    (h : ContDiffAt ℝ (m + 1) (Function.uncurry G) y) :
    ContDiffAt ℝ m (Function.uncurry (Work.Spaces.Dth G)) y := by
  have hp : ContDiffAt ℝ m (Function.uncurry (Work.Spaces.pth G)) y := pth_contDiffAt h
  have hs : ContDiffAt ℝ m (fun p : ℝ × ℝ => Real.sin (2 * p.2)) y := by fun_prop
  have hmul : ContDiffAt ℝ m ((fun p : ℝ × ℝ => Real.sin (2 * p.2))
      * (Function.uncurry (Work.Spaces.pth G))) y := hs.mul hp
  have hfun : ((fun p : ℝ × ℝ => Real.sin (2 * p.2))
      * (Function.uncurry (Work.Spaces.pth G)))
      = Function.uncurry (Work.Spaces.Dth G) := by
    funext p
    rfl
  rw [hfun] at hmul
  exact hmul

/-- `D_θ^j` lowers the order of differentiability by `j`. -/
lemma DthIter_contDiffAt {F : ℝ → ℝ → ℝ} {y : ℝ × ℝ} :
    ∀ (j m : ℕ), ContDiffAt ℝ (m + j) (Function.uncurry F) y →
      ContDiffAt ℝ m (Function.uncurry (Work.Spaces.DthIter j F)) y := by
  intro j
  induction j with
  | zero => intro m h; simpa using h
  | succ j ih =>
      intro m h
      have h' : ContDiffAt ℝ ((m + 1) + j) (Function.uncurry F) y := by
        convert h using 1
        push_cast
        ring
      have hG : ContDiffAt ℝ (m + 1) (Function.uncurry (Work.Spaces.DthIter j F)) y :=
        ih (m + 1) h'
      exact Dth_contDiffAt hG

/-! ## Congruence of the slice derivatives -/

/-- The slice derivative `∂_z` only depends on the germ of the function. -/
lemma pz_congr_ev {g g' : ℝ → ℝ → ℝ} {y : ℝ × ℝ}
    (h : Function.uncurry g =ᶠ[𝓝 y] Function.uncurry g') :
    Work.Spaces.pz g y.1 y.2 = Work.Spaces.pz g' y.1 y.2 := by
  have hd := (h.comp_tendsto (Continuous.prodMk_left y.2).continuousAt).deriv_eq
  show deriv (fun z' => g z' y.2) y.1 = deriv (fun z' => g' z' y.2) y.1
  exact hd

/-- The slice derivative `∂_θ` only depends on the germ of the function. -/
lemma pth_congr_ev {g g' : ℝ → ℝ → ℝ} {y : ℝ × ℝ}
    (h : Function.uncurry g =ᶠ[𝓝 y] Function.uncurry g') :
    Work.Spaces.pth g y.1 y.2 = Work.Spaces.pth g' y.1 y.2 := by
  have hd := (h.comp_tendsto (Continuous.prodMk_right y.1).continuousAt).deriv_eq
  show deriv (fun θ' => g y.1 θ') y.2 = deriv (fun θ' => g' y.1 θ') y.2
  exact hd

/-- The slice derivative `∂_θ` only depends on the values on an open set. -/
lemma pth_congr_isOpen {X Y : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry X) (Function.uncurry Y) V) {p : ℝ × ℝ} (hp : p ∈ V) :
    Work.Spaces.pth X p.1 p.2 = Work.Spaces.pth Y p.1 p.2 := by
  have hnb : ∀ᶠ θ' in 𝓝 p.2, (p.1, θ') ∈ V :=
    (Continuous.prodMk_right p.1).continuousAt.eventually (hV.mem_nhds hp)
  have hslice : (fun θ' => X p.1 θ') =ᶠ[𝓝 p.2] (fun θ' => Y p.1 θ') := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  have hd := hslice.deriv_eq
  show deriv (fun θ' => X p.1 θ') p.2 = deriv (fun θ' => Y p.1 θ') p.2
  exact hd

/-- Functions that agree on an open set have agreeing `D_θ`-iterates there. -/
lemma DthIter_congr_eqOn {X Y : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry X) (Function.uncurry Y) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i X))
      (Function.uncurry (Work.Spaces.DthIter i Y)) V := by
  induction i with
  | zero => exact h
  | succ i ih =>
      intro p hp
      have h1 : Work.Spaces.pth (Work.Spaces.DthIter i X) p.1 p.2
          = Work.Spaces.pth (Work.Spaces.DthIter i Y) p.1 p.2 :=
        pth_congr_isOpen hV ih hp
      show Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter i X) p.1 p.2
        = Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter i Y) p.1 p.2
      rw [h1]

/-! ## A single `∂_z` through the iterates of `D_θ` -/


/-! ## The main commutation -/



end PzDthAux


end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.PhiStar.Gegenbauer

set_option autoImplicit false

/-! ## The one-variable calculus of `θ ↦ cos θ · q (sin θ)` -/

/-- The `θ`-derivative of `θ ↦ cos θ · q (sin θ)`:
`∂_θ(cos θ · q(sin θ)) = -sin θ · q(sin θ) + cos²θ · q'(sin θ)`. -/
lemma deriv_cos_comp_sin (q : ℝ → ℝ) (hq : ContDiff ℝ 3 q) :
    deriv (fun θ' => Real.cos θ' * q (Real.sin θ'))
      = fun θ' => -Real.sin θ' * q (Real.sin θ') + Real.cos θ' ^ 2 * deriv q (Real.sin θ') := by
  funext θ
  have hdq : DifferentiableAt ℝ q (Real.sin θ) := (hq.differentiable (by norm_num)).differentiableAt
  have hcomp : HasDerivAt (fun θ' : ℝ => q (Real.sin θ')) (deriv q (Real.sin θ) * Real.cos θ) θ :=
    (hdq.hasDerivAt).comp θ (Real.hasDerivAt_sin θ)
  have hm := (Real.hasDerivAt_cos θ).mul hcomp
  have h1 : deriv (fun θ' : ℝ => Real.cos θ' * q (Real.sin θ')) θ
      = -Real.sin θ * q (Real.sin θ) + Real.cos θ * (deriv q (Real.sin θ) * Real.cos θ) := hm.deriv
  rw [h1]
  ring

/-- The second `θ`-derivative of `θ ↦ cos θ · q (sin θ)`:
`∂_θθ(cos θ · q(sin θ)) = -cos θ · q(sin θ) - 3 sin θ cos θ · q'(sin θ) + cos³θ · q''(sin θ)`. -/
lemma deriv2_cos_comp_sin (q : ℝ → ℝ) (hq : ContDiff ℝ 3 q) (θ : ℝ) :
    deriv (deriv (fun θ' => Real.cos θ' * q (Real.sin θ'))) θ
      = -Real.cos θ * q (Real.sin θ) - 3 * Real.sin θ * Real.cos θ * deriv q (Real.sin θ)
        + Real.cos θ ^ 3 * deriv (deriv q) (Real.sin θ) := by
  rw [deriv_cos_comp_sin q hq]
  have hdq : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hddq : Differentiable ℝ (deriv q) :=
    ((ContDiff.deriv' (n := 2) hq).differentiable (by norm_num))
  have h1 : HasDerivAt (fun θ' : ℝ => -Real.sin θ' * q (Real.sin θ'))
      ((-Real.cos θ) * q (Real.sin θ)
        + (-Real.sin θ) * (deriv q (Real.sin θ) * Real.cos θ)) θ := by
    have hcomp : HasDerivAt (fun θ' : ℝ => q (Real.sin θ'))
        (deriv q (Real.sin θ) * Real.cos θ) θ :=
      ((hdq.differentiableAt).hasDerivAt).comp θ (Real.hasDerivAt_sin θ)
    exact (Real.hasDerivAt_sin θ).neg.mul hcomp
  have h2 : HasDerivAt (fun θ' : ℝ => Real.cos θ' ^ 2 * deriv q (Real.sin θ'))
      ((2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ)) * deriv q (Real.sin θ)
        + Real.cos θ ^ 2 * (deriv (deriv q) (Real.sin θ) * Real.cos θ)) θ := by
    have hc2 : HasDerivAt (fun θ' : ℝ => Real.cos θ' ^ 2)
        (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ)) θ := (Real.hasDerivAt_cos θ).pow 2
    have hcomp : HasDerivAt (fun θ' : ℝ => deriv q (Real.sin θ'))
        (deriv (deriv q) (Real.sin θ) * Real.cos θ) θ :=
      ((hddq.differentiableAt).hasDerivAt).comp θ (Real.hasDerivAt_sin θ)
    exact hc2.mul hcomp
  have hsum : HasDerivAt (fun θ' : ℝ => -Real.sin θ' * q (Real.sin θ')
        + Real.cos θ' ^ 2 * deriv q (Real.sin θ'))
      (((-Real.cos θ) * q (Real.sin θ)
          + (-Real.sin θ) * (deriv q (Real.sin θ) * Real.cos θ))
        + ((2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ)) * deriv q (Real.sin θ)
          + Real.cos θ ^ 2 * (deriv (deriv q) (Real.sin θ) * Real.cos θ))) θ := h1.add h2
  rw [hsum.deriv]
  norm_num
  ring

/-- Where `cos θ ≠ 0` (hence on a neighbourhood of `θ`),
`∂_θ(tan θ · cos θ · q(sin θ)) = ∂_θ(sin θ · q(sin θ)) = cos θ · q(sin θ) + sin θ cos θ · q'(sin θ)`. -/
lemma deriv_tan_cos_comp_sin (q : ℝ → ℝ) (hq : ContDiff ℝ 3 q) (θ : ℝ)
    (hθ : Real.cos θ ≠ 0) :
    deriv (fun θ' => Real.tan θ' * (Real.cos θ' * q (Real.sin θ'))) θ
      = Real.cos θ * q (Real.sin θ) + Real.sin θ * Real.cos θ * deriv q (Real.sin θ) := by
  have hne : ∀ᶠ θ' in nhds θ, Real.cos θ' ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hθ
  have heq : (fun θ' => Real.tan θ' * (Real.cos θ' * q (Real.sin θ')))
      =ᶠ[nhds θ] fun θ' => Real.sin θ' * q (Real.sin θ') := by
    filter_upwards [hne] with θ' h'
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  rw [heq.deriv_eq]
  have hdq : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hcomp : HasDerivAt (fun θ' : ℝ => q (Real.sin θ'))
      (deriv q (Real.sin θ) * Real.cos θ) θ :=
    ((hdq.differentiableAt).hasDerivAt).comp θ (Real.hasDerivAt_sin θ)
  have hm := (Real.hasDerivAt_sin θ).mul hcomp
  have h1 : deriv (fun θ' : ℝ => Real.sin θ' * q (Real.sin θ')) θ
      = Real.cos θ * q (Real.sin θ) + Real.sin θ * (deriv q (Real.sin θ) * Real.cos θ) := hm.deriv
  rw [h1]
  ring

/-! ## The action of `Lzero` on `cos θ · q(sin θ)` -/

/-- **The reduction of `Lzero` on the Gegenbauer form.**  For a three-times differentiable `q`
and `cos θ ≠ 0`:

  `Lzero (fun _ θ' => cos θ' · q(sin θ')) z θ
     = cos θ · (-(1 - sin²θ) · q''(sin θ) + 4 sin θ · q'(sin θ) - 4 q(sin θ))`

— the operator acquires the factor `cos θ` and the *regular* Gegenbauer operator in the
variable `u = sin θ` (no `tan` remains). -/
lemma Lzero_cos_comp_sin (q : ℝ → ℝ) (hq : ContDiff ℝ 3 q) (z : ℝ) {θ : ℝ}
    (hθ : Real.cos θ ≠ 0) :
    Work.Elliptic.Lzero (fun _ θ' => Real.cos θ' * q (Real.sin θ')) z θ
      = Real.cos θ * (-(1 - Real.sin θ ^ 2) * deriv (deriv q) (Real.sin θ)
          + 4 * Real.sin θ * deriv q (Real.sin θ) - 4 * q (Real.sin θ)) := by
  -- on a `z`-independent function, `Lzero` is the one-variable operator of `Lzero_eq_deriv`
  have hL : Work.Elliptic.Lzero (fun _ θ' => Real.cos θ' * q (Real.sin θ')) z θ
      = -(deriv (deriv (fun θ' => Real.cos θ' * q (Real.sin θ'))) θ)
        + deriv (fun θ' => Real.tan θ' * (Real.cos θ' * q (Real.sin θ'))) θ
        - 6 * (Real.cos θ * q (Real.sin θ)) := by
    simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
      Work.Spaces.pth]
  rw [hL, deriv2_cos_comp_sin q hq θ, deriv_tan_cos_comp_sin q hq θ hθ]
  have hsq := Real.sin_sq_add_cos_sq θ
  linear_combination (-Real.cos θ * deriv (deriv q) (Real.sin θ)) * hsq

/-! ## The eigenfunction identity -/

theorem eFam_Lzero (m : ℕ) {θ : ℝ} (hθ : Real.cos θ ≠ 0) (z : ℝ) :
    Work.Elliptic.Lzero (fun _ θ' => Work.FTS.PhiStar.Gegenbauer.eFam m θ') z θ
      = Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  change Work.Elliptic.Lzero
      (fun _ θ' => Real.cos θ' * gC (2 * m + 1) (Real.sin θ')) z θ
    = lam m * (Real.cos θ * gC (2 * m + 1) (Real.sin θ))
  rw [Lzero_cos_comp_sin (gC (2 * m + 1)) (contDiff_gC (2 * m + 1)) z hθ]
  have hode := (gC_ode (2 * m + 1)).2 (Real.sin θ)
  have hn : ((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3) - 4 = lam m := by
    simp only [lam]; push_cast; ring
  have hkey : -(1 - Real.sin θ ^ 2) * deriv (deriv (gC (2 * m + 1))) (Real.sin θ)
      + 4 * Real.sin θ * deriv (gC (2 * m + 1)) (Real.sin θ)
      = ((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)
        * gC (2 * m + 1) (Real.sin θ) := by
    linarith [hode]
  rw [hkey, ← hn]
  ring

end Work.FTS.PhiStar.Gegenbauer
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_subst =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory

namespace Work.FTS.PhiStar.Gegenbauer

set_option autoImplicit false

theorem eFam_norm_subst (m : ℕ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
      = ∫ u in (0 : ℝ)..1,
          (1 - u ^ 2) * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) u ^ 2 := by
  set G : ℝ → ℝ := fun u => (1 - u ^ 2) * gC (2 * m + 1) u ^ 2 with hG
  have hGcont : Continuous G := by
    rw [hG]
    exact (continuous_const.sub (continuous_id.pow 2)).mul
      ((contDiff_gC (2 * m + 1)).continuous.pow 2)
  -- the set integral over `Iθ = Icc 0 (π/2)` is the interval integral over `0..π/2`
  have hIθ : (∫ θ in Work.Spaces.Iθ, eFam m θ ^ 2 * Real.cos θ)
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), eFam m θ ^ 2 * Real.cos θ := by
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
  -- substitute `u = sin θ`
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := Real.pi / 2) (f := Real.sin) (f' := Real.cos) (g := G)
    (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn hGcont
  rw [Real.sin_zero, Real.sin_pi_div_two] at hsub
  -- the integrand `eFam m θ ^ 2 * cos θ` is `G (sin θ) * cos θ`
  have hcongr : (∫ θ in (0 : ℝ)..(Real.pi / 2), eFam m θ ^ 2 * Real.cos θ)
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), (G ∘ Real.sin) θ * Real.cos θ := by
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [Function.comp_apply, hG, eFam]
    rw [← Real.cos_sq']
    ring
  rw [hIθ, hcongr, hsub, hG]

end Work.FTS.PhiStar.Gegenbauer
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CSTools.sq_tail_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sq_tail_le`: the weighted Cauchy–Schwarz bound on the far tail

For `s < -1`, `z ≥ 1` and `c` with `(c t)²` integrable on `(1,∞)`,

  `(∫_z^∞ c t · t^s)² ≤ (∫_z^∞ (c t)²) · z^{2s+1}/(-(2s+1))`.

This is the Cauchy–Schwarz (Bunyakovsky) inequality applied to the two `L²(Ioi z)`
functions `t ↦ c t` and `t ↦ t^s`, together with the elementary evaluation
`∫_z^∞ t^{2s} dt = z^{2s+1}/(-(2s+1))` of the weight (legitimate because `2s < -2`), i.e. the
`L²`-norm of the weight `t^s` on the tail.  It is the estimate that bounds the decaying radial
Green integral `∫_z^∞ c t · t^{-(2m/α) - 1}` of `Work.FTS.PhiStar.Radial.radGreen` by the
`L²`-mass `∫_z^∞ c²`.

The formalisation goes through the "square roots" form of Cauchy–Schwarz
(`Work.PhiStar.Honesty.sq_integral_sqrt_mul_le`, which is stated for two nonnegative integrable
functions `A`, `B`), with `A t = (c t)²` and `B t = t^{2s}`: on `(z,∞)` one has `t > 0`, so
`√((c t)²) · √(t^{2s}) = |c t| · t^s`.  This avoids ever having to *prove* that `c · t^s` is
integrable: all that is used is `|∫ f| ≤ ∫ |f|`, which is unconditional.
-/

noncomputable section

open MeasureTheory Set

namespace Work.FTS.PhiStar.Honesty.CSTools


end Work.FTS.PhiStar.Honesty.CSTools
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CmodeMass.cmode_sq_mass_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PhiStar.Honesty.CmodeMass

theorem cmode_sq_mass_le {c : ℝ → ℝ} {b M : ℝ} (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hmeas : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hsupp : ∀ t : ℝ, b < t → c t = 0) (hbd : ∀ t : ℝ, |c t| ≤ M) :
    MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2) (Set.Ioi 0) ∧
      (∫ t in Set.Ioi 0, c t ^ 2) ≤ M ^ 2 * b := by
  have hsub : Set.Ioc (0 : ℝ) b ⊆ Set.Ioi 0 := Set.Ioc_subset_Ioi_self
  -- `c ^ 2` vanishes on the part of `Ioi 0` which is not in `Ioc 0 b`
  have hvanish : ∀ x ∈ Set.Ioi (0 : ℝ) \ Set.Ioc 0 b, c x ^ 2 = 0 := by
    rintro x ⟨hx, hx'⟩
    have hxb : b < x := lt_of_not_ge fun h => hx' ⟨hx, h⟩
    simp [hsupp x hxb]
  -- the set carrying the whole mass has finite measure
  have hfin : MeasureTheory.volume (Set.Ioc (0 : ℝ) b) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  -- bounded measurable on a finite-measure set
  have hIntSmall : MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2) (Set.Ioc 0 b)
      MeasureTheory.volume := by
    have hgm : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioc 0 b)) :=
      (hmeas.mono_measure (Measure.restrict_mono hsub le_rfl)).pow 2
    have hg : MeasureTheory.Integrable (fun _ : ℝ => M ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioc 0 b)) :=
      MeasureTheory.integrableOn_const (C := M ^ 2) hfin
    refine hg.mono' hgm ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    change |c x ^ 2| ≤ M ^ 2
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbd x) 2
  -- transport the integrability back to `Ioi 0` through the indicator
  have hIntBig : MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2) (Set.Ioi 0)
      MeasureTheory.volume := by
    have h1 : MeasureTheory.Integrable ((Set.Ioc 0 b).indicator (fun t : ℝ => c t ^ 2))
        MeasureTheory.volume :=
      hIntSmall.integrable_indicator measurableSet_Ioc
    have hid : (Set.Ioi (0 : ℝ)).indicator (fun t : ℝ => c t ^ 2)
        = (Set.Ioc 0 b).indicator (fun t : ℝ => c t ^ 2) := by
      funext x
      rcases em (x ∈ Set.Ioi (0 : ℝ)) with hx | hx
      · rcases em (x ∈ Set.Ioc 0 b) with hx' | hx'
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
        · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hx']
          exact hvanish x ⟨hx, hx'⟩
      · have hx'' : x ∉ Set.Ioc 0 b := fun h => hx (hsub h)
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx'']
    rw [← hid] at h1
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioi).1 h1
  refine ⟨hIntBig, ?_⟩
  -- the integral over `Ioi 0` is the integral over `Ioc 0 b`
  have hIeq : (∫ x in Set.Ioi (0 : ℝ), c x ^ 2) = ∫ x in Set.Ioc 0 b, c x ^ 2 :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub hvanish
  rw [hIeq]
  calc ∫ x in Set.Ioc 0 b, c x ^ 2
      ≤ ∫ x in Set.Ioc 0 b, M ^ 2 :=
        MeasureTheory.setIntegral_mono_on hIntSmall
          (MeasureTheory.integrableOn_const (C := M ^ 2) hfin) measurableSet_Ioc
          (fun x _ => by
            rw [show c x ^ 2 = |c x| ^ 2 from by rw [sq_abs]]
            exact pow_le_pow_left₀ (abs_nonneg _) (hbd x) 2)
    _ = M ^ 2 * b := by
        rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hb, sub_zero,
          smul_eq_mul, mul_comm]

end Work.FTS.PhiStar.Honesty.CmodeMass
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.LamEst.cs_cutoff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Cauchy–Schwarz cut-off estimate `cs_cutoff`

This file proves the angular Cauchy–Schwarz inequality used in the `λ`-cut-off estimates of
`Submission/Work/FTS/PhiStar/Honesty/CptApp`.  With

* `f θ = X θ · (w z / sin(2θ)^{η/2})` (the "square-integrable" factor, hypothesis `hA2`), and
* `h θ = γ θ · sin(2θ)^{η/2} · sinCos2 θ` (the second factor, controlled by `|γ| ≤ 1`),

one has, **on `Iθ = [0, π/2]`**,

* `f θ * h θ = w z * (γ θ * X θ * sinCos2 θ)`
  (the `sin(2θ)^{η/2}` factors cancel where `sin 2θ ≠ 0`; where `sin 2θ = 0` both sides
  vanish because then `sinCos2 θ = sin θ cos²θ = 0`), and
* `(h θ)² = (γ θ)² · sin(2θ)^{η} · sinCos2 θ²`
  (using `(sin 2θ)^{η/2} · (sin 2θ)^{η/2} = (sin 2θ)^{η}`, valid since `sin 2θ ≥ 0` on `Iθ`).

Applying the Cauchy–Schwarz inequality `Work.RPFresh.integral_mul_sq_le_sq_mul_sq` to `f`
and `h` over `volume.restrict Iθ` and rewriting the two sides gives the claim.
-/

namespace Work.FTS.PhiStar.Honesty.CptApp.LamEst

open MeasureTheory

private lemma eta_half_ne : Work.Spaces.eta / 2 ≠ 0 := by unfold Work.Spaces.eta; norm_num

private lemma eta_half_pos : (0 : ℝ) < Work.Spaces.eta / 2 := by
  unfold Work.Spaces.eta; norm_num

/-- `sin θ cos²θ = sin(2θ) · cos θ / 2`. -/
private lemma sc_eq (θ : ℝ) : Work.Elliptic.sinCos2 θ = Real.sin (2 * θ) * Real.cos θ / 2 := by
  rw [Real.sin_two_mul, Work.Elliptic.sinCos2]; ring

/-- On `Iθ = [0, π/2]` one has `sin(2θ) ≥ 0`. -/
private lemma sin0 {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩

/-- `|sin θ cos²θ| ≤ 1` everywhere. -/
private lemma sc_abs_le (θ : ℝ) : |Work.Elliptic.sinCos2 θ| ≤ 1 := by
  unfold Work.Elliptic.sinCos2
  rw [abs_mul, abs_pow]
  nlinarith [Real.abs_sin_le_one θ, Real.abs_cos_le_one θ, abs_nonneg (Real.sin θ),
    abs_nonneg (Real.cos θ)]

/-- The pointwise cancellation of the `sin(2θ)^{η/2}` weights **on `Iθ`**. -/
private lemma mul_eq_cutoff (X γ : ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (X θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) *
        (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) * Work.Elliptic.sinCos2 θ))
      = Work.Spaces.w z * (γ θ * X θ * Work.Elliptic.sinCos2 θ) := by
  have hs0 := sin0 hθ
  rcases eq_or_ne (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) 0 with ha0 | ha0
  · -- `sin(2θ)^{η/2} = 0`, hence `sin 2θ = 0` and `sinCos2 θ = 0`: both sides vanish.
    have hs : Real.sin (2 * θ) = 0 := (Real.rpow_eq_zero hs0 eta_half_ne).mp ha0
    rw [ha0, sc_eq, hs]
    ring
  · -- `sin(2θ)^{η/2} ≠ 0`: cancel the weight.
    rw [sc_eq]
    have hcancel : Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) = Work.Spaces.w z :=
      div_mul_cancel₀ _ ha0
    rw [show X θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) *
          (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
            * (Real.sin (2 * θ) * Real.cos θ / 2)))
        = (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
            * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))
          * (X θ * γ θ * (Real.sin (2 * θ) * Real.cos θ / 2)) by ring, hcancel]
    ring

/-- The pointwise identification of the square of the second factor, **on `Iθ`**. -/
private lemma sq_eq_cutoff (γ : ℝ → ℝ) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) * Work.Elliptic.sinCos2 θ)) ^ 2
      = (γ θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
        * (Work.Elliptic.sinCos2 θ) ^ 2 := by
  have hs0 := sin0 hθ
  have ha2 : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
    rw [show (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
          = (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ (2 : ℝ) from
            (Real.rpow_natCast _ 2).symm,
        (Real.rpow_mul hs0 (Work.Spaces.eta / 2) 2).symm]
    congr 1
    ring
  rw [mul_pow, mul_pow, ha2]
  ring

theorem cs_cutoff {X γ : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hγm : MeasureTheory.AEStronglyMeasurable γ (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hγb : ∀ θ : ℝ, |γ θ| ≤ 1)
    (hAm : MeasureTheory.AEStronglyMeasurable
      (fun θ => X θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hA2 : MeasureTheory.Integrable
      (fun θ => (X θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    (∫ θ in Work.Spaces.Iθ, γ θ * X θ * Work.Elliptic.sinCos2 θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ,
            (X θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        * (∫ θ in Work.Spaces.Iθ,
            (γ θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
              * (Work.Elliptic.sinCos2 θ) ^ 2) := by
  -- the second factor `h θ = γ θ · sin(2θ)^{η/2} · sinCos2 θ` is measurable and its square is
  -- bounded by `1` on the finite-measure set `Iθ`
  have hGcont : Continuous (fun θ : ℝ =>
      Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) * Work.Elliptic.sinCos2 θ) := by
    apply Continuous.mul
    · exact (Real.continuous_rpow_const (le_of_lt eta_half_pos)).comp (by continuity)
    · unfold Work.Elliptic.sinCos2; fun_prop
  have hHm : AEStronglyMeasurable
      (fun θ => γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) * Work.Elliptic.sinCos2 θ))
      (volume.restrict Work.Spaces.Iθ) :=
    hγm.mul hGcont.aestronglyMeasurable
  have hH2 : Integrable
      (fun θ => (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        * Work.Elliptic.sinCos2 θ)) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
    haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
      Real.isFiniteMeasure_restrict_Icc 0 (Real.pi / 2)
    refine Integrable.of_bound (hHm.pow 2) 1
      (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_))
    have hs0 := sin0 hθ
    have ha1 : |Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)| ≤ 1 := by
      rw [abs_of_nonneg (Real.rpow_nonneg hs0 _)]
      exact Real.rpow_le_one hs0 (Real.sin_le_one _) (le_of_lt eta_half_pos)
    have hH1 : |γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        * Work.Elliptic.sinCos2 θ)| ≤ 1 := by
      rw [abs_mul, abs_mul]
      have h1 : |γ θ| * |Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)| ≤ 1 := by
        nlinarith [hγb θ, ha1, abs_nonneg (γ θ),
          abs_nonneg (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))]
      nlinarith [h1, sc_abs_le θ, abs_nonneg (Work.Elliptic.sinCos2 θ),
        abs_nonneg (|γ θ| * |Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)|)]
    rw [Real.norm_eq_abs, abs_sq]
    nlinarith [hH1,
      abs_nonneg (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        * Work.Elliptic.sinCos2 θ)),
      sq_abs (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        * Work.Elliptic.sinCos2 θ))]
  -- Cauchy–Schwarz for `f` and `h`
  have hkey := Work.RPFresh.integral_mul_sq_le_sq_mul_sq (volume.restrict Work.Spaces.Iθ)
      (f := fun θ => X θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      (h := fun θ => γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        * Work.Elliptic.sinCos2 θ))
      hAm hHm hA2 hH2
  -- identify the three integrals
  have hprod : (∫ θ in Work.Spaces.Iθ,
        (X θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) *
          (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) * Work.Elliptic.sinCos2 θ)))
      = Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, γ θ * X θ * Work.Elliptic.sinCos2 θ) :=
    calc (∫ θ in Work.Spaces.Iθ,
            (X θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) *
              (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
                * Work.Elliptic.sinCos2 θ)))
        = ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.w z * (γ θ * X θ * Work.Elliptic.sinCos2 θ)) :=
          integral_congr_ae (by
            filter_upwards [ae_restrict_of_forall_mem (s := Set.Icc 0 (Real.pi / 2))
              (p := fun θ => (X θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) *
                  (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
                    * Work.Elliptic.sinCos2 θ))
                  = Work.Spaces.w z * (γ θ * X θ * Work.Elliptic.sinCos2 θ))
              measurableSet_Icc (fun θ hθ => mul_eq_cutoff X γ z θ hθ)] with θ hθ
            exact hθ)
      _ = Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, γ θ * X θ * Work.Elliptic.sinCos2 θ) :=
          integral_const_mul _ _
  have hsq : (∫ θ in Work.Spaces.Iθ,
        (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) * Work.Elliptic.sinCos2 θ)) ^ 2)
      = ∫ θ in Work.Spaces.Iθ,
          (γ θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
            * (Work.Elliptic.sinCos2 θ) ^ 2 :=
    integral_congr_ae (by
      filter_upwards [ae_restrict_of_forall_mem (s := Set.Icc 0 (Real.pi / 2))
        (p := fun θ => (γ θ * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
              * Work.Elliptic.sinCos2 θ)) ^ 2
            = (γ θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
              * (Work.Elliptic.sinCos2 θ) ^ 2)
        measurableSet_Icc (fun θ hθ => sq_eq_cutoff γ θ hθ)] with θ hθ
      exact hθ)
  rw [hprod, hsq] at hkey
  calc (∫ θ in Work.Spaces.Iθ, γ θ * X θ * Work.Elliptic.sinCos2 θ) ^ 2
        * (Work.Spaces.w z) ^ 2
      = (Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, γ θ * X θ * Work.Elliptic.sinCos2 θ)) ^ 2 :=
        by ring
    _ ≤ (∫ θ in Work.Spaces.Iθ,
            (X θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        * (∫ θ in Work.Spaces.Iθ,
            (γ θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
              * (Work.Elliptic.sinCos2 θ) ^ 2) := hkey

end Work.FTS.PhiStar.Honesty.CptApp.LamEst
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.LamEst.integrable_mul_sinCos2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `X · sin θ cos²θ` is integrable from `L²` weighted control of `X`

Let `Iθ = [0, π/2]`, `η = 99/100`, `w z = (1+z)²/z² > 0` (for `z > 0`) and
`φ θ = w z / sin(2θ)^{η/2}`.  If `X` is a.e. strongly measurable on `Iθ` and the weighted
square `(X · φ)²` is integrable there, then `θ ↦ X θ · sin θ cos²θ` is integrable on `Iθ`.

The argument is a pointwise AM–GM domination.  On `Iθ` one has `0 ≤ sin(2θ) ≤ 1`, so
`0 ≤ sin(2θ)^{η/2} ≤ 1`, and `sin θ cos²θ = (sin 2θ / 2) · cos θ` is bounded by `1` in
absolute value.  For `sin (2θ) ≠ 0` (i.e. off the two endpoints, a null set)

`X θ · sinθcos²θ = (X θ · φ θ) · (sinθcos²θ / φ θ)`,

and `|sinθcos²θ / φ θ| = |sinθcos²θ| · sin(2θ)^{η/2} / w z ≤ 1 / w z`.  Hence, by AM–GM,

`‖X θ · sinθcos²θ‖ ≤ (X θ · φ θ)²/2 + 1/(2 (w z)²)`,

and the right-hand side is an integrable majorant because `(X · φ)²` is integrable (hypothesis)
and the second term is a constant (`Iθ` has finite measure).  Measurability of
`X · sinθcos²θ` follows from `hXm` and continuity of `sinCos2`.
-/

namespace Work.FTS.PhiStar.Honesty.CptApp.LamEst

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

theorem integrable_mul_sinCos2 {X : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hXm : MeasureTheory.AEStronglyMeasurable X (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hX2 : MeasureTheory.Integrable
      (fun θ => (X θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.Integrable (fun θ => X θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  -- `Iθ` has finite measure, so constants are integrable.
  have hfin : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.isFiniteMeasure_restrict, Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  -- `w z > 0` for `z > 0`.
  have hW : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]; positivity
  -- the majorant `(X · φ)²/2 + 1/(2 (w z)²)` is integrable.
  have hmaj : MeasureTheory.Integrable
      (fun θ => (X θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 / 2
        + 1 / (2 * (Work.Spaces.w z) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (hX2.div_const 2).add (MeasureTheory.integrable_const_iff.mpr (Or.inr hfin))
  -- a.e. strong measurability of the target.
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => X θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine hXm.mul ?_
    exact (by unfold Work.Elliptic.sinCos2; fun_prop :
      Measurable Work.Elliptic.sinCos2).aestronglyMeasurable
  refine MeasureTheory.Integrable.mono' hmaj hmeas ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  have hsnn : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  -- `sin θ cos²θ = (sin 2θ / 2) cos θ`
  have hsc_eq : Work.Elliptic.sinCos2 θ = Real.sin (2 * θ) / 2 * Real.cos θ := by
    unfold Work.Elliptic.sinCos2; rw [Real.sin_two_mul]; ring
  by_cases hs : Real.sin (2 * θ) = 0
  · -- at the endpoints both sides vanish
    have hsc : Work.Elliptic.sinCos2 θ = 0 := by rw [hsc_eq, hs]; ring
    rw [hsc, mul_zero, Real.norm_eq_abs, abs_zero]
    positivity
  · have hs_pos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne hsnn (Ne.symm hs)
    have hsp : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs_pos _
    have hspne : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≠ 0 := ne_of_gt hsp
    set φ : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hφdef
    have hφpos : 0 < φ := by rw [hφdef]; exact div_pos hW hsp
    have hφne : φ ≠ 0 := ne_of_gt hφpos
    -- `X θ · sinθcos²θ = (X θ · φ) · (sinθcos²θ / φ)`
    have hid : X θ * Work.Elliptic.sinCos2 θ
        = (X θ * φ) * (Work.Elliptic.sinCos2 θ / φ) := by
      rw [mul_assoc, mul_div_cancel₀ _ hφne]
    rw [hid, Real.norm_eq_abs, abs_mul]
    -- `|sinθcos²θ| ≤ 1`
    have hsc_abs : |Work.Elliptic.sinCos2 θ| ≤ 1 := by
      rw [hsc_eq, abs_mul]
      have h3 : |Real.sin (2 * θ) / 2| ≤ 1 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith [Real.abs_sin_le_one (2 * θ)]
      nlinarith [h3, Real.abs_cos_le_one θ, abs_nonneg (Real.sin (2 * θ) / 2),
        abs_nonneg (Real.cos θ)]
    have hsp_le : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one hsnn (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
    -- `|sinθcos²θ / φ| ≤ 1 / w z`
    have hB : |Work.Elliptic.sinCos2 θ / φ| ≤ 1 / Work.Spaces.w z := by
      have hrew : Work.Elliptic.sinCos2 θ / φ
          = Work.Elliptic.sinCos2 θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
            / Work.Spaces.w z := by
        rw [hφdef]; field_simp
      rw [hrew, abs_div, abs_of_pos hW]
      refine div_le_div_of_nonneg_right ?_ (le_of_lt hW)
      rw [abs_mul]
      have h1 : |(Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)| ≤ 1 := by
        rw [abs_of_nonneg (Real.rpow_nonneg hsnn _)]; exact hsp_le
      nlinarith [hsc_abs, h1, abs_nonneg (Work.Elliptic.sinCos2 θ),
        abs_nonneg ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))]
    have hB2 : (Work.Elliptic.sinCos2 θ / φ) ^ 2 ≤ 1 / (Work.Spaces.w z) ^ 2 := by
      rw [← sq_abs (Work.Elliptic.sinCos2 θ / φ), ← one_div_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hB 2
    -- AM–GM and the final assembly
    have hamgm : |X θ * φ| * |Work.Elliptic.sinCos2 θ / φ|
        ≤ ((X θ * φ) ^ 2 + (Work.Elliptic.sinCos2 θ / φ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|X θ * φ| - |Work.Elliptic.sinCos2 θ / φ|),
        sq_abs (X θ * φ), sq_abs (Work.Elliptic.sinCos2 θ / φ)]
    calc |X θ * φ| * |Work.Elliptic.sinCos2 θ / φ|
        ≤ ((X θ * φ) ^ 2 + (Work.Elliptic.sinCos2 θ / φ) ^ 2) / 2 := hamgm
      _ ≤ ((X θ * φ) ^ 2 + 1 / (Work.Spaces.w z) ^ 2) / 2 := by nlinarith [hB2]
      _ = (X θ * φ) ^ 2 / 2 + 1 / (2 * (Work.Spaces.w z) ^ 2) := by ring

end Work.FTS.PhiStar.Honesty.CptApp.LamEst
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.DiffGreen.radGreen_sub =====
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

namespace Work.FTS.PhiStar.Honesty.DiffGreen

/-- AM–GM: `|a·b| ≤ (a² + b²)/2`. -/
private lemma abs_mul_le_half_sq_add_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : 2 * (|a| * |b|) ≤ |a| ^ 2 + |b| ^ 2 := by nlinarith [sq_nonneg (|a| - |b|)]
  rw [abs_mul]
  linarith [h, sq_abs a, sq_abs b]

/-- The pure power `t ↦ t^e` is a.e. strongly measurable against the restriction of Lebesgue
measure to any subset of `(0,∞)`. -/
private lemma aesm_rpow {s : Set ℝ} (hs : s ⊆ Set.Ioi 0) (e : ℝ) :
    MeasureTheory.AEStronglyMeasurable (fun t : ℝ => t ^ e) (MeasureTheory.volume.restrict s) :=
  ((ContinuousOn.rpow_const continuousOn_id
      (fun _ hx => Or.inl (ne_of_gt hx))).aestronglyMeasurable measurableSet_Ioi).mono_measure
    (Measure.restrict_mono hs le_rfl)

/-- A product of an a.e. strongly measurable function (on `(0,∞)`) with a pure power is a.e.
strongly measurable against the restriction to a subset of `(0,∞)`. -/
private lemma aesm_mul_rpow {f : ℝ → ℝ} {s : Set ℝ} (hs : s ⊆ Set.Ioi 0) {e : ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    MeasureTheory.AEStronglyMeasurable (fun t : ℝ => f t * t ^ e)
      (MeasureTheory.volume.restrict s) :=
  (hf.mono_measure (Measure.restrict_mono hs le_rfl)).mul (aesm_rpow hs e)

/-- The integrand `c t · t^{q-1}` of the forward primitive is integrable on `(0,z]` as soon as
`c²` is integrable on `(0,∞)` and `1 ≤ q` (so that `t^{q-1}` is bounded by `z^{q-1}` there). -/
private lemma rgF1_integrableOn_Ioc {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {z : ℝ}
    (hq : 1 ≤ rgQ α m) (hz : 0 < z)
    (hc : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hc2 : MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2) (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn (rgF1 α m c) (Set.Ioc 0 z) := by
  have he0 : 0 ≤ rgQ α m - 1 := by linarith
  have hC0 : 0 ≤ z ^ (rgQ α m - 1) := Real.rpow_nonneg hz.le _
  have hdom : Integrable (fun t : ℝ => ((c t) ^ 2 + (z ^ (rgQ α m - 1)) ^ 2) / 2)
      (MeasureTheory.volume.restrict (Set.Ioc 0 z)) := by
    have h1 : Integrable (fun t : ℝ => c t ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioc 0 z)) :=
      hc2.mono_set Set.Ioc_subset_Ioi_self
    have h2 : Integrable (fun _ : ℝ => (z ^ (rgQ α m - 1)) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioc 0 z)) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    exact (h1.add h2).div_const 2
  refine MeasureTheory.Integrable.mono' hdom
    (aesm_mul_rpow Set.Ioc_subset_Ioi_self hc) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  have hnorm : ‖rgF1 α m c t‖ = |c t| * t ^ (rgQ α m - 1) := by
    simp only [rgF1, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
  rw [hnorm]
  have hle : t ^ (rgQ α m - 1) ≤ z ^ (rgQ α m - 1) :=
    Real.rpow_le_rpow ht0.le ht.2 he0
  calc |c t| * t ^ (rgQ α m - 1) ≤ |c t| * z ^ (rgQ α m - 1) :=
        mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    _ ≤ ((c t) ^ 2 + (z ^ (rgQ α m - 1)) ^ 2) / 2 := by
        have h := abs_mul_le_half_sq_add_sq (c t) (z ^ (rgQ α m - 1))
        rwa [abs_mul, abs_of_nonneg hC0] at h

/-- The integrand `c t · t^{-p-1}` of the tail primitive is integrable on `(z,∞)` for `z > 0`
as soon as `c²` is integrable on `(0,∞)` and `0 ≤ p`: AM–GM against `(c² + t^{-2p-2})/2`, whose
two pieces are integrable there (the pure power because `-2p-2 < -1`). -/
private lemma rgF2_integrableOn_Ioi {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {z : ℝ}
    (hp : 0 ≤ rgP α m) (hz : 0 < z)
    (hc : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hc2 : MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2) (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioi z) := by
  have hdom : Integrable (fun t : ℝ => ((c t) ^ 2 + t ^ (-(2 * rgP α m) - 2)) / 2)
      (MeasureTheory.volume.restrict (Set.Ioi z)) := by
    have h1 : Integrable (fun t : ℝ => c t ^ 2) (MeasureTheory.volume.restrict (Set.Ioi z)) :=
      hc2.mono_set (Set.Ioi_subset_Ioi hz.le)
    have h2 : Integrable (fun t : ℝ => t ^ (-(2 * rgP α m) - 2))
        (MeasureTheory.volume.restrict (Set.Ioi z)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hz
    exact (h1.add h2).div_const 2
  refine MeasureTheory.Integrable.mono' hdom
    (aesm_mul_rpow (Set.Ioi_subset_Ioi hz.le) hc) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := lt_trans hz ht
  have hnorm : ‖rgF2 α m c t‖ = |c t| * t ^ (-(rgP α m) - 1) := by
    simp only [rgF2, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
  rw [hnorm]
  have hsq : (t ^ (-(rgP α m) - 1)) ^ 2 = t ^ (-(2 * rgP α m) - 2) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul ht0.le]
    congr 1
    ring
  calc |c t| * t ^ (-(rgP α m) - 1)
      = |c t * t ^ (-(rgP α m) - 1)| := by
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    _ ≤ ((c t) ^ 2 + (t ^ (-(rgP α m) - 1)) ^ 2) / 2 := abs_mul_le_half_sq_add_sq _ _
    _ = ((c t) ^ 2 + t ^ (-(2 * rgP α m) - 2)) / 2 := by rw [hsq]

/-- **Additivity of `radGreen` in the source.**  For `0 < α ≤ 1/4`, `m : ℕ`, `z > 0` and two
a.e.-strongly-measurable `L²((0,∞))` sources `c`, `c'`,

  `radGreen α m (c' - c) z = radGreen α m c' z - radGreen α m c z`.

Both Green integrals are honest under these hypotheses: on `(0,z)` the integrand
`t ↦ c t · t^{q-1}` (`q = (2m+5)/α ≥ 20`) is dominated by `(c t² + t^{2q-2})/2` with
`2q-2 > -1`, and on `(z,∞)` the integrand `t ↦ c t · t^{-p-1}` (`p = 2m/α ≥ 0`) is dominated by
`(c t² + t^{-2p-2})/2` with `2p+2 > 1`; `L²` controls `∫ c²` on both pieces by AM–GM, so the
interval/set integrals are additive in the source.  The named pieces `rgK`, `rgQ`, `rgP`, `rgA`,
`rgB`, `rgF1`, `rgF2` of `Work.FTS.EllExist.RadGreenDefs` and the identity
`Work.FTS.EllExist.radGreen_eq` are available. -/
theorem radGreen_sub {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) {c c' : ℝ → ℝ}
    (hc : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hc' : MeasureTheory.AEStronglyMeasurable c' (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hc2 : MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2) (Set.Ioi 0))
    (hc'2 : MeasureTheory.IntegrableOn (fun t : ℝ => c' t ^ 2) (Set.Ioi 0))
    {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Radial.radGreen α m (fun t => c' t - c t) z
      = Work.FTS.PhiStar.Radial.radGreen α m c' z
        - Work.FTS.PhiStar.Radial.radGreen α m c z := by
  have hq1 : 1 ≤ Work.FTS.EllExist.rgQ α m := by
    rw [Work.FTS.EllExist.rgQ, le_div_iff₀ hα]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hp0 : 0 ≤ Work.FTS.EllExist.rgP α m := Work.FTS.EllExist.rgP_nonneg hα m
  -- the difference of the sources is again a.e. strongly measurable with integrable square
  have hsub_aesm : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c' t - c t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hc'.sub hc
  have hsub2 : MeasureTheory.IntegrableOn (fun t : ℝ => (c' t - c t) ^ 2) (Set.Ioi 0) := by
    have hdom : Integrable (fun t : ℝ => 2 * ((c' t) ^ 2 + (c t) ^ 2))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := (hc'2.add hc2).const_mul 2
    refine MeasureTheory.Integrable.mono' hdom (hsub_aesm.pow 2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (c' t + c t)]
  -- the two integrands are additive in the source
  have hF1 : ∀ t : ℝ,
      Work.FTS.EllExist.rgF1 α m (fun s => c' s - c s) t
        = Work.FTS.EllExist.rgF1 α m c' t - Work.FTS.EllExist.rgF1 α m c t := by
    intro t
    simp only [Work.FTS.EllExist.rgF1]
    ring
  have hF2 : ∀ t : ℝ,
      Work.FTS.EllExist.rgF2 α m (fun s => c' s - c s) t
        = Work.FTS.EllExist.rgF2 α m c' t - Work.FTS.EllExist.rgF2 α m c t := by
    intro t
    simp only [Work.FTS.EllExist.rgF2]
    ring
  -- additivity of the forward interval integral
  have hA : Work.FTS.EllExist.rgA α m (fun t => c' t - c t) z
      = Work.FTS.EllExist.rgA α m c' z - Work.FTS.EllExist.rgA α m c z := by
    have hInt1 : IntervalIntegrable (Work.FTS.EllExist.rgF1 α m c') volume 0 z := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hz.le]
      exact rgF1_integrableOn_Ioc hq1 hz hc' hc'2
    have hInt2 : IntervalIntegrable (Work.FTS.EllExist.rgF1 α m c) volume 0 z := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hz.le]
      exact rgF1_integrableOn_Ioc hq1 hz hc hc2
    simp only [Work.FTS.EllExist.rgA, hF1]
    exact intervalIntegral.integral_sub hInt1 hInt2
  -- additivity of the tail set integral
  have hB : Work.FTS.EllExist.rgB α m (fun t => c' t - c t) z
      = Work.FTS.EllExist.rgB α m c' z - Work.FTS.EllExist.rgB α m c z := by
    simp only [Work.FTS.EllExist.rgB, hF2]
    rw [MeasureTheory.integral_sub (rgF2_integrableOn_Ioi hp0 hz hc' hc'2)
      (rgF2_integrableOn_Ioi hp0 hz hc hc2)]
  rw [Work.FTS.EllExist.radGreen_eq, Work.FTS.EllExist.radGreen_eq,
    Work.FTS.EllExist.radGreen_eq, hA, hB]
  ring

end Work.FTS.PhiStar.Honesty.DiffGreen
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.RadGreenSupp.Consts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real
open MeasureTheory Set

namespace Work.FTS.PhiStar.Honesty.RadGreenSupp

set_option autoImplicit false

/-- The constant of the weighted support bound for the radial Green function. -/
def C (α a b : ℝ) : ℝ :=
  (1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α)
    + (1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α)
    + (1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α))

theorem C_pos {α a b : ℝ} (_hα : 0 < α) (ha : 0 < a) (hab : a ≤ b) : 0 < C α a b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : 0 < a ^ (-(2 / α)) := Real.rpow_pos_of_pos ha _
  have h2 : 0 < (1 + a) ^ (7 / α) := Real.rpow_pos_of_pos (by linarith) _
  have h3 : 0 < (1 + b) ^ (7 / α) := Real.rpow_pos_of_pos (by linarith) _
  have h4 : 0 < b ^ (-(2 / α)) := Real.rpow_pos_of_pos hb _
  simp only [C]
  positivity

theorem C_term1_le {α a b : ℝ} (_hα : 0 < α) (ha : 0 < a) (hab : a ≤ b) :
    (1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α) ≤ C α a b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : 0 ≤ a ^ (-(2 / α)) := (Real.rpow_pos_of_pos ha _).le
  have h2 : 0 ≤ (1 + a) ^ (7 / α) := (Real.rpow_pos_of_pos (by linarith) _).le
  have h3 : 0 ≤ (1 + b) ^ (7 / α) := (Real.rpow_pos_of_pos (by linarith) _).le
  have h4 : 0 ≤ b ^ (-(2 / α)) := (Real.rpow_pos_of_pos hb _).le
  have h5 : 0 ≤ (1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α) := by positivity
  have h6 : 0 ≤ (1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α)) := by positivity
  simp only [C]
  linarith

theorem C_term2_le {α a b : ℝ} (_hα : 0 < α) (ha : 0 < a) (hab : a ≤ b) :
    (1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α) ≤ C α a b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : 0 ≤ a ^ (-(2 / α)) := (Real.rpow_pos_of_pos ha _).le
  have h2 : 0 ≤ (1 + a) ^ (7 / α) := (Real.rpow_pos_of_pos (by linarith) _).le
  have h3 : 0 ≤ (1 + b) ^ (7 / α) := (Real.rpow_pos_of_pos (by linarith) _).le
  have h4 : 0 ≤ b ^ (-(2 / α)) := (Real.rpow_pos_of_pos hb _).le
  have h5 : 0 ≤ (1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α) := by positivity
  have h6 : 0 ≤ (1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α)) := by positivity
  simp only [C]
  linarith

theorem C_term3_le {α a b : ℝ} (_hα : 0 < α) (ha : 0 < a) (hab : a ≤ b) :
    (1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α)) ≤ C α a b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : 0 ≤ a ^ (-(2 / α)) := (Real.rpow_pos_of_pos ha _).le
  have h2 : 0 ≤ (1 + a) ^ (7 / α) := (Real.rpow_pos_of_pos (by linarith) _).le
  have h3 : 0 ≤ (1 + b) ^ (7 / α) := (Real.rpow_pos_of_pos (by linarith) _).le
  have h4 : 0 ≤ b ^ (-(2 / α)) := (Real.rpow_pos_of_pos hb _).le
  have h5 : 0 ≤ (1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α) := by positivity
  have h6 : 0 ≤ (1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α) := by positivity
  simp only [C]
  linarith

theorem rgK_div_rgP_le {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) :
    Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgP α m ≤ 1 / 18 := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have heq : Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgP α m
      = 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ))) := by
    rw [Work.FTS.EllExist.rgK, Work.FTS.EllExist.rgP]
    field_simp
  rw [heq]
  refine one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 18) ?_
  nlinarith

theorem rgK_div_rgQ_le {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) :
    Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgQ α m ≤ 1 / 63 := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have heq : Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgQ α m
      = 1 / ((4 * (m : ℝ) + 5) * (2 * (m : ℝ) + 5)) := by
    rw [Work.FTS.EllExist.rgK, Work.FTS.EllExist.rgQ]
    field_simp
  rw [heq]
  refine one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 63) ?_
  nlinarith

theorem rgK_mul_inv_add_le {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) :
    Work.FTS.EllExist.rgK α m
        * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m) ≤ 1 / 14 := by
  have hP : 0 < Work.FTS.EllExist.rgP α m := Work.FTS.EllExist.rgP_pos hα hm
  have hQ : 0 < Work.FTS.EllExist.rgQ α m := Work.FTS.EllExist.rgQ_pos hα m
  have h1 := rgK_div_rgP_le hα hm
  have h2 := rgK_div_rgQ_le hα hm
  have heq : Work.FTS.EllExist.rgK α m
        * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)
      = Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgQ α m
        + Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgP α m := by
    rw [mul_add, mul_one_div, mul_one_div]
  rw [heq]
  linarith

theorem two_div_alpha_le_rgP {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) :
    2 / α ≤ Work.FTS.EllExist.rgP α m := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [Work.FTS.EllExist.rgP, div_le_div_iff_of_pos_right hα]
  linarith

theorem seven_div_alpha_le_rgQ {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) :
    7 / α ≤ Work.FTS.EllExist.rgQ α m := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [Work.FTS.EllExist.rgQ, div_le_div_iff_of_pos_right hα]
  linarith

end Work.FTS.PhiStar.Honesty.RadGreenSupp
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.WeightedL2Aux.cs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty.WeightedL2Aux

set_option autoImplicit false

/-- **Cauchy–Schwarz for the set integral.**  If `f²` and `g²` are integrable on the measurable
set `s`, then `(∫_s f g)² ≤ (∫_s f²)(∫_s g²)`.  No measurability of `f` or `g` is required. -/
theorem sq_setIntegral_mul_le {s : Set ℝ} (hs : MeasurableSet s) {f g : ℝ → ℝ}
    (hf : IntegrableOn (fun t => (f t) ^ 2) s)
    (hg : IntegrableOn (fun t => (g t) ^ 2) s) :
    (∫ t in s, f t * g t) ^ 2 ≤ (∫ t in s, (f t) ^ 2) * (∫ t in s, (g t) ^ 2) := by
  have hcs := Work.PhiStar.Honesty.sq_integral_sqrt_mul_le hs hf hg
    (fun t _ => sq_nonneg (f t)) (fun t _ => sq_nonneg (g t))
  have h1 : (∫ t in s, Real.sqrt ((f t) ^ 2) * Real.sqrt ((g t) ^ 2))
      = ∫ t in s, |f t| * |g t| :=
    MeasureTheory.setIntegral_congr_fun hs (fun t _ => by
      rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs])
  have h2 : (∫ t in s, |f t| * |g t|) = ∫ t in s, |f t * g t| :=
    MeasureTheory.setIntegral_congr_fun hs (fun t _ => by rw [abs_mul])
  have h3 : |∫ t in s, f t * g t| ≤ ∫ t in s, |f t * g t| :=
    MeasureTheory.abs_integral_le_integral_abs (f := fun t => f t * g t)
  have h4 : (∫ t in s, |f t * g t|) = ∫ t in s, Real.sqrt ((f t) ^ 2) * Real.sqrt ((g t) ^ 2) :=
    (h1.trans h2).symm
  calc (∫ t in s, f t * g t) ^ 2
      = |∫ t in s, f t * g t| ^ 2 := by rw [sq_abs]
    _ ≤ (∫ t in s, |f t * g t|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h3 2
    _ = (∫ t in s, Real.sqrt ((f t) ^ 2) * Real.sqrt ((g t) ^ 2)) ^ 2 := by rw [h4]
    _ ≤ (∫ t in s, (f t) ^ 2) * (∫ t in s, (g t) ^ 2) := hcs

/-- **Junk-robust difference of set integrals.**  If `f - g` is integrable on `s`, then
`|∫_s f - ∫_s g| ≤ |∫_s (f - g)|`. -/
theorem integral_sub_abs_le {s : Set ℝ} {f g : ℝ → ℝ}
    (h : IntegrableOn (fun t => f t - g t) s) :
    |(∫ t in s, f t) - (∫ t in s, g t)| ≤ |∫ t in s, (f t - g t)| := by
  by_cases hf : IntegrableOn f s
  · have hg : IntegrableOn g s :=
      MeasureTheory.Integrable.congr (hf.sub h)
        (Filter.Eventually.of_forall (fun t => by change f t - (f t - g t) = g t; ring))
    rw [MeasureTheory.integral_sub hf hg]
  · have hg : ¬ IntegrableOn g s := by
      intro hg
      refine hf ?_
      have h1 : IntegrableOn (fun t => g t + (f t - g t)) s := hg.add h
      exact MeasureTheory.Integrable.congr h1
        (Filter.Eventually.of_forall (fun t => by ring))
    rw [MeasureTheory.integral_undef hf, MeasureTheory.integral_undef hg]
    simp

/-- `√(a+b) ≤ √a + √b` for `a, b ≥ 0`. -/
theorem sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have h2 := Real.sq_sqrt ha
    have h3 := Real.sq_sqrt hb
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, h2, h3]
  have h4 : Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) :=
    Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))] at h4

end Work.FTS.PhiStar.Honesty.WeightedL2Aux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.exists_bound_eFam_mul_cos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

/-- A continuous function on the compact interval `[-1,1]` is bounded there in absolute value. -/
private lemma exists_abs_le_on_Icc {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) :
    ∃ C : ℝ, ∀ x ∈ Set.Icc (-1 : ℝ) 1, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := f) hf
  exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩

/-- The Gegenbauer polynomial `gC (2m+1)` is bounded in absolute value on `[-1,1]`. -/
private lemma exists_abs_gC_le (m : ℕ) : ∃ C : ℝ,
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) x| ≤ C :=
  exists_abs_le_on_Icc
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).continuousOn)

theorem exists_bound_eFam_mul_cos (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| ≤ C := by
  obtain ⟨M, hM⟩ := exists_abs_gC_le m
  refine ⟨max M 0, le_max_right _ _, fun θ hθ => ?_⟩
  have hsin : Real.sin θ ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hb : |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| ≤ M := hM _ hsin
  have hcos_sq : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.cos θ), Real.cos_le_one θ, Real.neg_one_le_cos θ]
  calc |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ|
      = Real.cos θ ^ 2 * |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| := by
        rw [Work.FTS.PhiStar.Gegenbauer.eFam]
        rw [show Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
              * Real.cos θ
            = Real.cos θ ^ 2 * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
            from by ring]
        rw [abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ))]
    _ ≤ 1 * M := mul_le_mul hcos_sq hb (abs_nonneg _) (by norm_num)
    _ ≤ max M 0 := by
        rw [one_mul]
        exact le_max_left _ _

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.ofReal_integral_rpow_mul_sq_eq_lintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

/-- The general form of the target: for an integrable-on-`(1,∞)` square `c²` and any real
exponent `q > 0`, the Lebesgue integral of `t ↦ (c t)² t^q` over `(1,z)` (i.e. the `ofReal` of
the interval integral over `1..z`) agrees with the `lintegral` of its `ofReal` over `Ioo 1 z`.

This is the standard `ofReal_integral_eq_lintegral_ofReal` (applied to the restricted measure
`volume.restrict (Ioo 1 z)`) together with the identification of `∫ t in 1..z` with the set
integral over `Ioo 1 z` for `1 ≤ z` (the endpoints differ by a null set).  Integrability comes
from `hfar` by domination with `z^q`, the exponent being bounded on `(1,z)`. -/
private theorem ofReal_integral_mul_rpow_eq_lintegral {c : ℝ → ℝ} {q : ℝ} (hq : 0 < q)
    (hc : AEMeasurable c)
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ z : ℝ, 1 ≤ z →
      ENNReal.ofReal (∫ t in (1 : ℝ)..z, (c t) ^ 2 * t ^ q)
        = ∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ q) := by
  intro z hz
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [MeasureTheory.restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hz]
  · -- integrability on `Ioo 1 z`
    have hmem : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioo (1 : ℝ) z) :=
      hfar.mono_set Set.Ioo_subset_Ioi_self
    refine MeasureTheory.Integrable.mono' (hmem.mul_const (z ^ q)) ?_ ?_
    · refine AEStronglyMeasurable.mul ((hc.aestronglyMeasurable.restrict).pow 2) ?_
      exact (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x)))).aestronglyMeasurable
        measurableSet_Ioo
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      filter_upwards with t ht
      have ht0 : (0 : ℝ) ≤ t := by linarith [ht.1]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht0 q))]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht0 ht.2.le hq.le) (sq_nonneg _)
  · change ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) z), 0 ≤ (c t) ^ 2 * t ^ q
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with t ht
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t) q)

theorem ofReal_integral_rpow_mul_sq_eq_lintegral {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ z : ℝ, 1 ≤ z →
      ENNReal.ofReal (∫ t in (1 : ℝ)..z, (c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))
        = ∫⁻ t in Set.Ioo (1 : ℝ) z,
            ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)) := by
  have hq : 0 < Work.FTS.EllExist.rgQ α m - 1 := by
    have := Work.FTS.EllExist.rgQ_ge hα hα4 hm
    linarith
  exact ofReal_integral_mul_rpow_eq_lintegral (q := Work.FTS.EllExist.rgQ α m - 1) hq hc hfar

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.radGreenCPCore =====
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


/-! ### Auxiliary real-power facts -/



/-! ### the shrinking-interval integral vanishes at the base point -/


/-! ### interval-integral helpers -/



/-! ### the combined difference quotient is `O(√|y-z|)` -/


/-! ### the combined difference quotient tends to `0` -/



end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgA_step_claim =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false
set_option linter.unusedVariables false




end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgA_value_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

local notation "rgQ" => Work.FTS.EllExist.rgQ
local notation "rgF1" => Work.FTS.EllExist.rgF1

/-- **Interval-integral comparison with a pointwise majorant.**  If `|f| ≤ g` on `Ioc a b` and
`g` is interval integrable there, then `|∫_a^b f| ≤ ∫_a^b g`. -/
private theorem abs_intervalIntegral_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Set.Ioc a b, |f t| ≤ g t) (hg : IntervalIntegrable g volume a b) :
    |∫ t in a..b, f t| ≤ ∫ t in a..b, g t := by
  have h' : ∀ᵐ t ∂volume, t ∈ Set.Ioc a b → ‖f t‖ ≤ g t :=
    Eventually.of_forall fun t ht => by simpa [Real.norm_eq_abs] using h t ht
  have h2 := intervalIntegral.norm_integral_le_of_norm_le hab h' hg
  simpa [Real.norm_eq_abs] using h2


end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgB_value_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The value bound for the tail (growing) Green primitive `rgB`

`rgB α m c z = ∫_{t > z} c t · t^{-p-1} dt` with `p = rgP α m = 2m/α ≥ 8`.  We prove, for
`0 < z ≤ 1` and a source `c` which is controlled by `|c t| ≤ ε t^{3/2}` on `(0,δ]`
(`δ ≤ 1`), `L²`-integrable on `(1,∞)` and with `c t/t²` `L²`-integrable on `(0,1)`:

  `|rgB α m c z| ≤ ε·z^{3/2-p}/(p-3/2) + ½∫_{(0,1)} c²/t⁴ + ½∫_{(1,∞)} c² + δ^{-(2p+1)} + 1`,

which is the tail estimate needed in the honesty/regularity estimates for the radial Green
function.

The proof splits the tail `(z,∞)` at `δ` (near part: the smallness hypothesis; far part:
`(δ,1)` by AM–GM against `c²/t⁴`, `(1,∞)` by AM–GM against `c²` and the integrable weight
`t^{-2p-2}`).  The two value estimates and the two integrability facts are provided by the
sibling modules `rgB_tail_le`, `rgB_near_le`, `rgB_int_Ioi`, `rgB_int_Ioc`; the measurability
interface `aesm_abs_c_of` is proved here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty


/-! ## The value bound -/


end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgHonest_aemeas =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

/-- AM–GM: `a·b ≤ (a² + b²)/2` for nonnegative `a`, `b`. -/
private lemma mul_le_half_sq_add_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    have h2 : 2 * (|a| * |b|) ≤ |a| ^ 2 + |b| ^ 2 := by
      nlinarith [sq_nonneg (|a| - |b|)]
    rw [abs_mul]
    linarith [h2, sq_abs a, sq_abs b]
  rwa [abs_of_nonneg (mul_nonneg ha hb)] at h

/-- AM–GM in the form `|y| ≤ (y² + 1)/2`. -/
private lemma abs_le_sq_add_one_div_two (y : ℝ) : |y| ≤ (y ^ 2 + 1) / 2 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1)]

/-- A.e. strong measurability of `t ↦ c t · t^r` on a set contained in `(0,∞)`, from
`AEMeasurable c`: the constant power is continuous there. -/
private lemma aestronglyMeasurable_mul_rpow {c : ℝ → ℝ} (hc : AEMeasurable c) {r : ℝ}
    {s : Set ℝ} (hs : s ⊆ Set.Ioi 0) :
    AEStronglyMeasurable (fun t : ℝ => c t * t ^ r) (volume.restrict s) := by
  have h1 : AEStronglyMeasurable c (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hc.aestronglyMeasurable.restrict
  have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ r) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (ne_of_gt hx))).aestronglyMeasurable measurableSet_Ioi
  exact (h1.mul h2).mono_set hs

/-- `t ↦ t^r` is continuous on `[0,1]` for `0 ≤ r` (at `0` one uses the exponent). -/
private lemma continuousOn_rpow_Icc_zero {r : ℝ} (hr : 0 ≤ r) :
    ContinuousOn (fun t : ℝ => t ^ r) (Set.Icc 0 1) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h
    exact (Real.continuousAt_rpow_const 0 r (Or.inr hr)).continuousWithinAt
  · exact (Real.continuousAt_rpow_const t r (Or.inl (ne_of_gt h))).continuousWithinAt

/-- Honestness of the two Green integrands of the radial Euler Green function
`Work.FTS.PhiStar.Radial.radGreen`, under the weak hypotheses of the corrected
`radGreen_mul_deriv_atTop_zero_meas`.  Here `q = rgQ α m = (2m+5)/α ≥ 28`, `p = rgP α m = 2m/α ≥ 8`,
`rgF1 α m c t = c t · t^{q-1}`, `rgF2 α m c t = c t · t^{-p-1}`.

Both are derived from `(c t)²/t⁴ ∈ L¹(0,1)` and `(c t)² ∈ L¹(1,∞)` together with `AEMeasurable c`
(this last is what supplies a.e. strong measurability; the AM–GM inequality
`|c t| · t^{r} ≤ ((c t)²/t⁴ + t^{2r+4})/2` does the domination, and all the surviving powers are
locally integrable). -/
theorem rgHonest_aemeas {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hc : AEMeasurable c)
    (hnear : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Set.Ioc 0 1)
      ∧ (∀ z : ℝ, 1 ≤ z → IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Set.Ioc 1 z))
      ∧ (∀ z : ℝ, 1 ≤ z → IntegrableOn (Work.FTS.EllExist.rgF2 α m c) (Set.Ioi z)) := by
  have hq : 28 ≤ Work.FTS.EllExist.rgQ α m := Work.FTS.EllExist.rgQ_ge hα hα4 hm
  have hp : 8 ≤ Work.FTS.EllExist.rgP α m := Work.FTS.EllExist.rgP_ge hα hα4 hm
  have hq1 : 0 ≤ Work.FTS.EllExist.rgQ α m - 1 := by linarith
  have hp0 : 0 ≤ Work.FTS.EllExist.rgP α m := by linarith
  -- ### the pointwise AM–GM domination for `rgF1` on `(0,1)`
  have key1 : ∀ t : ℝ, 0 < t →
      ‖Work.FTS.EllExist.rgF1 α m c t‖
        ≤ ((c t) ^ 2 / t ^ 4 + t ^ (2 * (Work.FTS.EllExist.rgQ α m - 1) + 4)) / 2 := by
    intro t ht
    have hpow : t ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)
        = t ^ (Work.FTS.EllExist.rgQ α m + 1) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht]
      congr 1
      ring
    have hmain : ‖Work.FTS.EllExist.rgF1 α m c t‖
        = (|c t| / t ^ 2) * t ^ (Work.FTS.EllExist.rgQ α m + 1) := by
      rw [Real.norm_eq_abs, Work.FTS.EllExist.rgF1, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg ht.le _), ← hpow]
      field_simp
    rw [hmain]
    have hA := mul_le_half_sq_add_sq (by positivity : (0 : ℝ) ≤ |c t| / t ^ 2)
      (Real.rpow_nonneg ht.le (Work.FTS.EllExist.rgQ α m + 1))
    have hsq1 : (|c t| / t ^ 2) ^ 2 = (c t) ^ 2 / t ^ 4 := by
      rw [div_pow, sq_abs]
      ring
    have hsq2 : (t ^ (Work.FTS.EllExist.rgQ α m + 1)) ^ 2
        = t ^ (2 * (Work.FTS.EllExist.rgQ α m - 1) + 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      congr 1
      ring
    rw [hsq1, hsq2] at hA
    exact hA
  refine ⟨?_, ?_, ?_⟩
  · -- ### `rgF1` on `(0,1]`
    have hnearI : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioc 0 1) :=
      hnear.congr_set_ae (Ioo_ae_eq_Ioc).symm
    have hrpowI : IntegrableOn (fun t : ℝ => t ^ (2 * (Work.FTS.EllExist.rgQ α m - 1) + 4))
        (Set.Ioc 0 1) :=
      ((continuousOn_rpow_Icc_zero (by linarith)).integrableOn_Icc).mono_set
        Set.Ioc_subset_Icc_self
    have hmaj : Integrable
        (fun t : ℝ => ((c t) ^ 2 / t ^ 4 + t ^ (2 * (Work.FTS.EllExist.rgQ α m - 1) + 4)) / 2)
        (volume.restrict (Set.Ioc 0 1)) := (hnearI.add hrpowI).div_const 2
    refine Integrable.mono' hmaj ?_ ?_
    · exact aestronglyMeasurable_mul_rpow hc (s := Set.Ioc 0 1) Set.Ioc_subset_Ioi_self
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact key1 t ht.1
  · -- ### `rgF1` on `(1,z]`
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz1
    have hfarI : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioc 1 z) :=
      hfar.mono_set (fun t ht => ht.1)
    have hconstI : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 1 z) :=
      continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    have hmaj : Integrable
        (fun t : ℝ => z ^ (Work.FTS.EllExist.rgQ α m - 1) * (((c t) ^ 2 + 1) / 2))
        (volume.restrict (Set.Ioc 1 z)) :=
      ((hfarI.add hconstI).div_const 2).const_mul (z ^ (Work.FTS.EllExist.rgQ α m - 1))
    refine Integrable.mono' hmaj ?_ ?_
    · exact aestronglyMeasurable_mul_rpow hc (s := Set.Ioc 1 z)
        (fun t ht => lt_trans zero_lt_one ht.1)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht.1
      have hbound : |c t| * t ^ (Work.FTS.EllExist.rgQ α m - 1)
          ≤ ((c t) ^ 2 + 1) / 2 * z ^ (Work.FTS.EllExist.rgQ α m - 1) :=
        mul_le_mul (abs_le_sq_add_one_div_two (c t))
          (Real.rpow_le_rpow ht0.le ht.2 hq1)
          (Real.rpow_nonneg ht0.le _) (by positivity)
      rw [Real.norm_eq_abs, Work.FTS.EllExist.rgF1, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      calc |c t| * t ^ (Work.FTS.EllExist.rgQ α m - 1)
          ≤ ((c t) ^ 2 + 1) / 2 * z ^ (Work.FTS.EllExist.rgQ α m - 1) := hbound
        _ = z ^ (Work.FTS.EllExist.rgQ α m - 1) * (((c t) ^ 2 + 1) / 2) := by ring
  · -- ### `rgF2` on `(z,∞)`
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz1
    have hmaj : Integrable
        (fun t : ℝ => ((c t) ^ 2 + t ^ (-(2 * Work.FTS.EllExist.rgP α m) - 2)) / 2)
        (volume.restrict (Set.Ioi z)) := by
      have h1 : Integrable (fun t : ℝ => (c t) ^ 2) (volume.restrict (Set.Ioi z)) :=
        hfar.mono_set (fun t ht => lt_of_le_of_lt hz1 ht)
      have h2 : Integrable (fun t : ℝ => t ^ (-(2 * Work.FTS.EllExist.rgP α m) - 2))
          (volume.restrict (Set.Ioi z)) :=
        integrableOn_Ioi_rpow_of_lt (by linarith) hz0
      exact (h1.add h2).div_const 2
    refine Integrable.mono' hmaj ?_ ?_
    · exact aestronglyMeasurable_mul_rpow hc (s := Set.Ioi z)
        (fun t ht => lt_trans hz0 ht)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans hz0 ht
      rw [Real.norm_eq_abs, Work.FTS.EllExist.rgF2, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      have hA := mul_le_half_sq_add_sq (abs_nonneg (c t))
        (Real.rpow_nonneg ht0.le _ :
          (0 : ℝ) ≤ t ^ (-(Work.FTS.EllExist.rgP α m) - 1))
      have hsq : (t ^ (-(Work.FTS.EllExist.rgP α m) - 1)) ^ 2
          = t ^ (-(2 * Work.FTS.EllExist.rgP α m) - 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
        congr 1
        ring
      rw [hsq, sq_abs] at hA
      exact hA

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.sq_integral_mul_cos_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty


end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.tendsto_sq_weighted_of_tendsto_difference =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem tendsto_sq_weighted_of_tendsto_difference {c : ℝ → ℝ} {c_ : ℕ → ℝ → ℝ}
    (hcw : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hint : ∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hcross : ∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hconv : Filter.Tendsto (fun n => ∫ t in Set.Ioi 0, (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ t in Set.Ioi 0, (c_ n t) ^ 2 * (Work.Spaces.w t) ^ 2) Filter.atTop
      (nhds (∫ t in Set.Ioi 0, (c t) ^ 2 * (Work.Spaces.w t) ^ 2)) := by
  have ha : ∀ n, MeasureTheory.Integrable
      (fun t : ℝ => ((c_ n t - c t) * Work.Spaces.w t) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    intro n
    exact (hint n).congr
      (Filter.Eventually.of_forall fun t => (mul_pow (c_ n t - c t) (Work.Spaces.w t) 2).symm)
  have hb : MeasureTheory.Integrable (fun t : ℝ => (c t * Work.Spaces.w t) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    exact hcw.congr
      (Filter.Eventually.of_forall fun t => (mul_pow (c t) (Work.Spaces.w t) 2).symm)
  have hconv' : Filter.Tendsto
      (fun n : ℕ => ∫ x, ((c_ n x - c x) * Work.Spaces.w x) ^ 2
        ∂(MeasureTheory.volume.restrict (Set.Ioi 0))) Filter.atTop (nhds 0) := by
    simpa only [mul_pow] using hconv
  have hcross0 : Filter.Tendsto
      (fun n : ℕ => ∫ x, ((c_ n x - c x) * Work.Spaces.w x) * (c x * Work.Spaces.w x)
        ∂(MeasureTheory.volume.restrict (Set.Ioi 0))) Filter.atTop (nhds 0) :=
    tendsto_integral_mul_of_tendsto_integral_sq_zero (α := ℝ)
      (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
      (a := fun n x => (c_ n x - c x) * Work.Spaces.w x)
      (b := fun x => c x * Work.Spaces.w x) ha hb hconv'
  have hcross0' : Filter.Tendsto
      (fun n : ℕ => ∫ t in Set.Ioi 0, (c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2)
      Filter.atTop (nhds 0) := by
    refine hcross0.congr (fun n => ?_)
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    ring
  have hsum : Filter.Tendsto
      (fun n : ℕ => (∫ t in Set.Ioi 0, (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        + 2 * (∫ t in Set.Ioi 0, (c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2)
        + ∫ t in Set.Ioi 0, (c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      Filter.atTop (nhds (∫ t in Set.Ioi 0, (c t) ^ 2 * (Work.Spaces.w t) ^ 2)) := by
    have h1 : Filter.Tendsto
        (fun n : ℕ => (∫ t in Set.Ioi 0, (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
          + 2 * (∫ t in Set.Ioi 0, (c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2))
        Filter.atTop (nhds (0 + 2 * 0)) := hconv.add (hcross0'.const_mul 2)
    have h2 := h1.add (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ => ∫ t in Set.Ioi 0, (c t) ^ 2 * (Work.Spaces.w t) ^ 2) Filter.atTop
      (nhds (∫ t in Set.Ioi 0, (c t) ^ 2 * (Work.Spaces.w t) ^ 2)))
    simpa using h2
  refine hsum.congr (fun n => ?_)
  exact (integral_sq_eq_of_difference (c := c) (c_ := c_) n hcw (hint n) (hcross n)).symm

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.zDerivAux =====
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

/-! ### exponent facts -/



/-! ### measurability -/



/-! ### pointwise bounds -/







/-! ### `rgF1` integrability -/




/-! ### `rgF2` integrability on intervals inside `(0,1]` and `(1,∞)` -/


/-! ### `rgF2` integrable on `(1,∞)` and the tail-splitting identity for `rgB` -/



/-! ### a.e. differentiability of the two branches -/





end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Radial.radGreen_solves =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Radial

set_option autoImplicit false

/-- **The radial Green's function solves the mode-`m` Euler equation.**  For `α > 0`, `m : ℕ` and a
continuous source `c` on `(0,∞)` with the four integrability conditions, the explicit decaying
solution `radGreen α m c` satisfies `-α²z²a'' - α(5+α)z a' + λ_m a = c` at every `z > 0`. -/
theorem radGreen_solves {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z, 0 < z →
      -α ^ 2 * z ^ 2 * deriv (deriv (radGreen α m c)) z
        - α * (5 + α) * z * deriv (radGreen α m c) z
        + lamR m * radGreen α m c z = c z := by
  have hfun : radGreen α m c = radGreenI α m c := rfl
  have h := radGreenI_solves (α := α) hα m hc h0 h0' hinf
  simpa only [hfun] using h

end Work.FTS.PhiStar.Radial
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.continuousOnTsumEFam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Continuity of a series in the Dirichlet eigenbasis `eFam`

`eFam m θ = cos θ · C_{2m+1}^{(3/2)}(sin θ)` is a (trigonometric) polynomial in `θ`, hence
continuous.  If the coefficients `b m` satisfy the pointwise domination
`|b m · eFam m θ| ≤ u m` on the *whole* open interval `(0, π/2)` for a summable majorant `u`,
then the Weierstrass M-test gives uniform convergence of the series on `(0, π/2)`, and a uniform
limit of continuous functions is continuous there.  This is the content of `continuousOnTsumEFam`.
-/

namespace Work.FTS.PhiStar.Series.Deleg

open scoped Real

/-- `eFam m` is continuous: it is `cos θ` times the polynomial `gC (2m+1)` evaluated at `sin θ`. -/
lemma continuous_eFam_deleg (m : ℕ) :
    Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) :=
  Real.continuous_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp Real.continuous_sin)

theorem continuousOnTsumEFam (b : ℕ → ℝ) (u : ℕ → ℝ) (hu : Summable u)
    (h : ∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ u m) :
    ContinuousOn (fun θ : ℝ => ∑' m : ℕ, b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  refine continuousOn_tsum (s := Set.Ioo 0 (Real.pi / 2))
    (f := fun m θ => b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) (u := u)
    (fun m => ?_) hu (fun m θ hθ => ?_)
  · exact (continuous_const.mul (continuous_eFam_deleg m)).continuousOn
  · rw [Real.norm_eq_abs]
    exact h m θ hθ

end Work.FTS.PhiStar.Series.Deleg
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.gCAtOne =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Series.Deleg

open Work.FTS.PhiStar.Gegenbauer (gC gC_rec)

/-- The value of `C^{(3/2)}_k` at `1`: `C^{(3/2)}_k(1) = (k+1)(k+2)/2`. -/
theorem gCAtOne (k : ℕ) :
    Work.FTS.PhiStar.Gegenbauer.gC k 1 = (((k : ℝ) + 1) * ((k : ℝ) + 2)) / 2 := by
  induction k using Nat.twoStepInduction with
  | zero =>
    rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    norm_num
  | one =>
    rw [show gC 1 = (fun x : ℝ => 3 * x) from rfl]
    norm_num
  | more n ih1 ih2 =>
    have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    have h : ((n : ℝ) + 2) * gC (n + 2) 1
        = ((n : ℝ) + 2) * (((n : ℝ) + 2 + 1) * ((n : ℝ) + 2 + 2) / 2) := by
      rw [gC_rec n 1, ih1, ih2]
      push_cast
      ring
    have hh := mul_left_cancel₀ h2 h
    push_cast
    exact hh

end Work.FTS.PhiStar.Series.Deleg
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.bmcut_chi_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series

open MeasureTheory Filter

/-- The angular Dirichlet eigenfunctions `eFam m` of `Lzero` are continuous. -/
private lemma continuous_eFam_prv (m : ℕ) :
    Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  have h : (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      = fun θ : ℝ =>
          Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) := rfl
  rw [h]
  exact Real.continuous_cos.mul
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
      Real.continuous_sin)

/-- The cut-off family `χ δ` tends to `1` pointwise on the *open* angular interval, so
it is an approximation of the identity on `Iθ = [0, π/2]` up to a null set.  Consequently
the truncated integrals `∫_{Iθ} f · χ δ · (eFam m · cos)` converge to the untruncated one. -/
theorem bmcut_chi_tendsto (χ : ℝ → ℝ → ℝ) (A : ℝ) (hA : 0 < A) (m : ℕ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 (Real.pi / 2)))
    (hχc : ∀ δ : ℝ, 0 < δ → Continuous (χ δ))
    (hχ0 : ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, θ ∉ Set.Ioo (δ / 2) (Real.pi / 2 - δ / 2) → χ δ θ = 0)
    (hχ1 : ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, θ ∈ Set.Icc δ (Real.pi / 2 - δ) → χ δ θ = 1)
    (hχnn : ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, 0 ≤ χ δ θ)
    (hχle : ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, χ δ θ ≤ 1)
    (hAe : ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| ≤ A) :
    Filter.Tendsto
      (fun n : ℕ => ∫ θ in Work.Spaces.Iθ,
        f θ * χ (1 / ((n : ℝ) + 1)) θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      Filter.atTop
      (nhds (∫ θ in Work.Spaces.Iθ,
        f θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)) := by
  -- `f` is bounded on the compact interval `Iθ`
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hC0 : 0 ≤ C := by
    have h0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_refl 0, by linarith [Real.pi_pos]⟩
    have := hC 0 h0
    rw [Real.norm_eq_abs] at this
    exact le_trans (abs_nonneg (f 0)) this
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIθ_top : (volume : Measure ℝ) Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  -- the dominating function `C * A` is integrable on `Iθ`
  have hbound_int : Integrable (fun _ : ℝ => C * A) (volume.restrict Work.Spaces.Iθ) := by
    refine integrableOn_const (s := Work.Spaces.Iθ) hIθ_top ?_
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_ne_top
  -- measurability of every member of the sequence
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun θ : ℝ => f θ * χ (1 / ((n : ℝ) + 1)) θ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      (volume.restrict Work.Spaces.Iθ) := by
    intro n
    have hδ : 0 < 1 / ((n : ℝ) + 1) := by positivity
    exact (((hf.aestronglyMeasurable (show MeasurableSet Work.Spaces.Iθ from
              measurableSet_Icc)).mul
            ((hχc _ hδ).aestronglyMeasurable)).mul
          ((continuous_eFam_prv m).aestronglyMeasurable)).mul
      Real.continuous_cos.aestronglyMeasurable
  -- the dominating bound, using `0 ≤ χ ≤ 1` and the two given bounds
  have hbound : ∀ n : ℕ, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖f θ * χ (1 / ((n : ℝ) + 1)) θ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ‖ ≤ C * A := by
    intro n
    rw [ae_restrict_iff' (s := Work.Spaces.Iθ) (show MeasurableSet Work.Spaces.Iθ from
        measurableSet_Icc)]
    refine Eventually.of_forall fun θ hθ => ?_
    have hδ : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hχabs : |χ (1 / ((n : ℝ) + 1)) θ| ≤ 1 := by
      rw [abs_of_nonneg (hχnn _ hδ θ)]
      exact hχle _ hδ θ
    have hfC : |f θ| ≤ C := by
      have h := hC θ (by simpa [Work.Spaces.Iθ] using hθ)
      rwa [Real.norm_eq_abs] at h
    have heA : |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| ≤ A := hAe θ hθ
    have h2 : |Work.FTS.PhiStar.Gegenbauer.eFam m θ| * |Real.cos θ| ≤ A := by
      rw [← abs_mul]
      exact heA
    have h1 : |f θ| * |χ (1 / ((n : ℝ) + 1)) θ| ≤ C := by
      calc |f θ| * |χ (1 / ((n : ℝ) + 1)) θ| ≤ C * 1 :=
            mul_le_mul hfC hχabs (abs_nonneg _) hC0
        _ = C := mul_one C
    calc ‖f θ * χ (1 / ((n : ℝ) + 1)) θ *
            Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ‖
        = |f θ| * |χ (1 / ((n : ℝ) + 1)) θ| *
            |Work.FTS.PhiStar.Gegenbauer.eFam m θ| * |Real.cos θ| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      _ = (|f θ| * |χ (1 / ((n : ℝ) + 1)) θ|) *
            (|Work.FTS.PhiStar.Gegenbauer.eFam m θ| * |Real.cos θ|) := by ring
      _ ≤ C * A := mul_le_mul h1 h2 (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hC0
  -- pointwise convergence on a conull subset of `Iθ`: on `(0, π/2)` the cut-off is
  -- eventually identically `1`
  have hlim : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Tendsto (fun n : ℕ => f θ * χ (1 / ((n : ℝ) + 1)) θ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) atTop
        (nhds (f θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)) := by
    have hcount : ({0, Real.pi / 2} : Set ℝ).Countable :=
      ((Set.finite_singleton (Real.pi / 2)).insert 0).countable
    have hae1 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({0, Real.pi / 2} : Set ℝ) :=
      hcount.ae_notMem volume
    refine ((ae_restrict_mem hIθ_meas).and (ae_restrict_of_ae hae1)).mono ?_
    rintro θ ⟨hθI, hne⟩
    have hθI' : θ ∈ Set.Icc 0 (Real.pi / 2) := hθI
    have hθ0 : 0 < θ :=
      lt_of_le_of_ne hθI'.1 (fun h => hne (by simp [h]))
    have hθlt : θ < Real.pi / 2 :=
      lt_of_le_of_ne hθI'.2 (fun h => hne (by simp [h]))
    have hmin : 0 < min θ (Real.pi / 2 - θ) := lt_min hθ0 (by linarith)
    have hsmall : ∀ᶠ n : ℕ in atTop,
        1 / ((n : ℝ) + 1) < min θ (Real.pi / 2 - θ) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (eventually_lt_nhds hmin)
    refine (tendsto_const_nhds (x := f θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * Real.cos θ)).congr' ?_
    filter_upwards [hsmall] with n hn
    have hδ : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hle1 : 1 / ((n : ℝ) + 1) ≤ θ :=
      le_of_lt (lt_of_lt_of_le hn (min_le_left _ _))
    have hle2 : θ ≤ Real.pi / 2 - 1 / ((n : ℝ) + 1) :=
      le_of_lt (by linarith [lt_of_lt_of_le hn (min_le_right θ (Real.pi / 2 - θ))])
    have hχ1' : χ (1 / ((n : ℝ) + 1)) θ = 1 :=
      hχ1 _ hδ θ (Set.mem_Icc.mpr ⟨hle1, hle2⟩)
    simp only [hχ1', mul_one]
  exact tendsto_integral_of_dominated_convergence (fun _ : ℝ => C * A)
    hmeas hbound_int hbound hlim

end Work.FTS.PhiStar.Series
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.eFam_zero_moment =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-- The `m = 0` Dirichlet eigenfunction of `Lzero`: `e_0(θ) = 3 sin θ cos θ = (3/2) sin (2θ)`. -/
lemma eFam_zero_apply (θ : ℝ) :
    Work.FTS.PhiStar.Gegenbauer.eFam 0 θ = 3 * (Real.sin θ * Real.cos θ) := by
  rw [Work.FTS.PhiStar.Gegenbauer.eFam]
  simp only [Work.FTS.PhiStar.Gegenbauer.gC]
  ring

/-- The `m = 0` coefficient of the slice is `3·Fstar` divided by the (nonzero) normalisation:
in particular it vanishes as soon as the source moment does. -/
theorem eFam_zero_moment (F : ℝ → ℝ → ℝ) {z : ℝ} (h : Work.Elliptic.Fstar F z = 0) :
    Work.FTS.PhiStar.Series.cmode 0 F z = 0 := by
  have hpoint : ∀ θ : ℝ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ
      = 3 * (F z θ * Work.Elliptic.sinCos2 θ) := by
    intro θ
    rw [eFam_zero_apply]
    simp only [Work.Elliptic.sinCos2]
    ring
  have hnum : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        F z θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ)
      = 3 * Work.Elliptic.Fstar F z := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    rw [show (∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 2),
          F z θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ)
        = ∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 2), 3 * (F z θ * Work.Elliptic.sinCos2 θ) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun θ _ => hpoint θ)]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    simp only [Work.Elliptic.Fstar, Work.Spaces.Iθ]
    exact (MeasureTheory.integral_Icc_eq_integral_Ioc).symm
  rw [Work.FTS.PhiStar.Series.cmode, hnum, h, mul_zero, zero_div]


end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

open Work.FTS.PhiStar.Radial (hasDerivAt_integral_Ioi intervalIntegrable_of_Ioi_Ioo
  integrableOn_Ioi_of_Ioi_Ioo)

/-! ### Scaffolding: the two integrals whose combination is `radGreenI` -/

/-- The decaying indicial exponent `s⁻ = -(2m+5)/α`. -/
def rgiSn (α : ℝ) (m : ℕ) : ℝ := -(2 * (m : ℝ) + 5) / α

/-- The growing indicial exponent `s⁺ = 2m/α`. -/
def rgiSp (α : ℝ) (m : ℕ) : ℝ := 2 * (m : ℝ) / α

/-- The normalising constant `1/(α(4m+5))`. -/
def rgiK (α : ℝ) (m : ℕ) : ℝ := 1 / (α * (4 * (m : ℝ) + 5))

/-- The integrand of the `0..z` integral. -/
def rgiF1 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (t : ℝ) : ℝ :=
  c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)

/-- The integrand of the `Ioi z` integral. -/
def rgiF2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (t : ℝ) : ℝ :=
  c t * t ^ (-(2 * (m : ℝ) / α) - 1)

/-- The interval integral `∫₀^z c t t^{(2m+5)/α-1} dt`. -/
def rgiA (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in (0 : ℝ)..z, rgiF1 α m c t

/-- The tail integral `∫_{Ioi z} c t t^{-2m/α-1} dt`. -/
def rgiB (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in Set.Ioi z, rgiF2 α m c t

/-- The formula for the derivative of `radGreenI`. -/
def rgiD1 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (y : ℝ) : ℝ :=
  rgiK α m * ((rgiSn α m * y ^ (rgiSn α m - 1)) * rgiA α m c y
    + (rgiSp α m * y ^ (rgiSp α m - 1)) * rgiB α m c y)

/-- `radGreenI` written with the scaffolding names of this file (definitional). -/
lemma radGreenI_eq_rgi (α : ℝ) (m : ℕ) (c : ℝ → ℝ) :
    Work.FTS.PhiStar.Radial.radGreenI α m c
      = fun z => rgiK α m * (z ^ (rgiSn α m) * rgiA α m c z
        + z ^ (rgiSp α m) * rgiB α m c z) := by
  funext z
  rfl

/-! ### Continuity and differentiability of the two integrals -/

lemma rgiF1_continuousOn {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0)) :
    ContinuousOn (rgiF1 α m c) (Set.Ioi 0) :=
  hc.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht)))

lemma rgiF2_continuousOn {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0)) :
    ContinuousOn (rgiF2 α m c) (Set.Ioi 0) :=
  hc.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht)))

/-- Fundamental theorem of calculus: `rgiA` is differentiable on `(0,∞)` with derivative `rgiF1`. -/
lemma rgiA_hasDerivAt {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (rgiA α m c) (rgiF1 α m c z) z := by
  intro z hz
  have hF : ContinuousOn (rgiF1 α m c) (Set.Ioi 0) := rgiF1_continuousOn hc
  have hsm : StronglyMeasurableAtFilter (rgiF1 α m c) (𝓝 z) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hF z hz
  exact intervalIntegral.integral_hasDerivAt_right (a := 0) (b := z)
    (intervalIntegrable_of_Ioi_Ioo hz hF h0) hsm (hF.continuousAt (Ioi_mem_nhds hz))

/-- Fundamental theorem of calculus for the tail integral: `rgiB` is differentiable on `(0,∞)`
with derivative `-(rgiF2 ·)`. -/
lemma rgiB_hasDerivAt {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (rgiB α m c) (-(rgiF2 α m c z)) z := by
  intro z hz
  have hz0 : (0 : ℝ) < z := hz
  have hF : ContinuousOn (rgiF2 α m c) (Set.Ioi 0) := rgiF2_continuousOn hc
  have hz2 : 0 < z / 2 := by linarith
  exact hasDerivAt_integral_Ioi (f := rgiF2 α m c) (a := z / 2) (z := z) (by linarith)
    (hF.mono (fun t ht => by simp only [Set.mem_Ioi] at ht ⊢; linarith))
    (integrableOn_Ioi_of_Ioi_Ioo hz2 hF hinf)

/-! ### The derivative of `radGreenI` -/

/-- **`radGreenI` is differentiable on `(0,∞)`**, with the explicit derivative `rgiD1`. -/
lemma hasDerivAt_radGreenI {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.FTS.PhiStar.Radial.radGreenI α m c) (rgiD1 α m c z) z := by
  intro z hz
  have hy0 : (0 : ℝ) < z := hz
  have hyne : z ≠ 0 := ne_of_gt hy0
  have hA := rgiA_hasDerivAt (α := α) (m := m) (c := c) hc h0 z hz
  have hB := rgiB_hasDerivAt (α := α) (m := m) (c := c) hc hinf z hz
  have hp1 : HasDerivAt (fun t : ℝ => t ^ (rgiSn α m))
      (rgiSn α m * z ^ (rgiSn α m - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hyne)
  have hp2 : HasDerivAt (fun t : ℝ => t ^ (rgiSp α m))
      (rgiSp α m * z ^ (rgiSp α m - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hyne)
  have hm1 : HasDerivAt (fun t : ℝ => t ^ (rgiSn α m) * rgiA α m c t)
      ((rgiSn α m * z ^ (rgiSn α m - 1)) * rgiA α m c z
        + z ^ (rgiSn α m) * rgiF1 α m c z) z := hp1.mul hA
  have hm2 : HasDerivAt (fun t : ℝ => t ^ (rgiSp α m) * rgiB α m c t)
      ((rgiSp α m * z ^ (rgiSp α m - 1)) * rgiB α m c z
        + z ^ (rgiSp α m) * (-(rgiF2 α m c z))) z := hp2.mul hB
  have h3 : HasDerivAt (fun t : ℝ => rgiK α m *
        (t ^ (rgiSn α m) * rgiA α m c t + t ^ (rgiSp α m) * rgiB α m c t))
      (rgiK α m * (((rgiSn α m * z ^ (rgiSn α m - 1)) * rgiA α m c z
            + z ^ (rgiSn α m) * rgiF1 α m c z)
          + ((rgiSp α m * z ^ (rgiSp α m - 1)) * rgiB α m c z
            + z ^ (rgiSp α m) * (-(rgiF2 α m c z))))) z :=
    (hm1.add hm2).const_mul (rgiK α m)
  -- the two `c`-terms of the product rule cancel
  have hcs1 : z ^ (rgiSn α m) * rgiF1 α m c z = c z / z := by
    have he : (2 * (m : ℝ) + 5) / α - 1 = -1 - (-(2 * (m : ℝ) + 5) / α) := by ring
    have hf : rgiF1 α m c z = c z * z ^ (-1 - rgiSn α m) := by
      simp only [rgiF1, rgiSn]; rw [he]
    calc z ^ (rgiSn α m) * rgiF1 α m c z
        = z ^ (rgiSn α m) * (c z * z ^ (-1 - rgiSn α m)) := by rw [hf]
      _ = c z * (z ^ (rgiSn α m) * z ^ (-1 - rgiSn α m)) := by ring
      _ = c z * z ^ (-(1 : ℝ)) := by
            have hExp : rgiSn α m + (-1 - rgiSn α m) = -(1 : ℝ) := by ring
            rw [← Real.rpow_add hy0, hExp]
      _ = c z / z := by rw [Real.rpow_neg_one, div_eq_mul_inv]
  have hcs2 : z ^ (rgiSp α m) * rgiF2 α m c z = c z / z := by
    have he : -(2 * (m : ℝ) / α) - 1 = -1 - (2 * (m : ℝ) / α) := by ring
    have hf : rgiF2 α m c z = c z * z ^ (-1 - rgiSp α m) := by
      simp only [rgiF2, rgiSp]; rw [he]
    calc z ^ (rgiSp α m) * rgiF2 α m c z
        = z ^ (rgiSp α m) * (c z * z ^ (-1 - rgiSp α m)) := by rw [hf]
      _ = c z * (z ^ (rgiSp α m) * z ^ (-1 - rgiSp α m)) := by ring
      _ = c z * z ^ (-(1 : ℝ)) := by
            have hExp : rgiSp α m + (-1 - rgiSp α m) = -(1 : ℝ) := by ring
            rw [← Real.rpow_add hy0, hExp]
      _ = c z / z := by rw [Real.rpow_neg_one, div_eq_mul_inv]
  have hval : rgiK α m * (((rgiSn α m * z ^ (rgiSn α m - 1)) * rgiA α m c z
            + z ^ (rgiSn α m) * rgiF1 α m c z)
          + ((rgiSp α m * z ^ (rgiSp α m - 1)) * rgiB α m c z
            + z ^ (rgiSp α m) * (-(rgiF2 α m c z)))) = rgiD1 α m c z := by
    simp only [rgiD1]
    rw [mul_neg, hcs1, hcs2]
    ring
  rw [radGreenI_eq_rgi]
  exact h3.congr_deriv hval

/-- **The derivative `rgiD1` of `radGreenI` is itself differentiable on `(0,∞)`.** -/
lemma rgiD1_differentiableAt {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (rgiD1 α m c) z := by
  intro z hz
  have hzne : z ≠ 0 := ne_of_gt hz
  have hA : DifferentiableAt ℝ (rgiA α m c) z :=
    (rgiA_hasDerivAt (α := α) (m := m) (c := c) hc h0 z hz).differentiableAt
  have hB : DifferentiableAt ℝ (rgiB α m c) z :=
    (rgiB_hasDerivAt (α := α) (m := m) (c := c) hc hinf z hz).differentiableAt
  have h1 : DifferentiableAt ℝ (fun y : ℝ => rgiSn α m * y ^ (rgiSn α m - 1)) z :=
    ((Real.hasDerivAt_rpow_const (x := z) (p := rgiSn α m - 1) (Or.inl hzne)).const_mul
      (rgiSn α m)).differentiableAt
  have h2 : DifferentiableAt ℝ (fun y : ℝ => rgiSp α m * y ^ (rgiSp α m - 1)) z :=
    ((Real.hasDerivAt_rpow_const (x := z) (p := rgiSp α m - 1) (Or.inl hzne)).const_mul
      (rgiSp α m)).differentiableAt
  exact ((h1.mul hA).add (h2.mul hB)).const_mul (rgiK α m)

/-! ### The target -/

theorem radGreenI_differentiableAt {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (Work.FTS.PhiStar.Radial.radGreenI α m c) z ∧
        DifferentiableAt ℝ (deriv (Work.FTS.PhiStar.Radial.radGreenI α m c)) z := by
  have _hαne : α ≠ 0 := ne_of_gt hα
  intro z hz
  refine ⟨(hasDerivAt_radGreenI (α := α) (m := m) (c := c) hc h0 hinf z hz).differentiableAt,
    ?_⟩
  have heq : deriv (Work.FTS.PhiStar.Radial.radGreenI α m c) =ᶠ[𝓝 z] rgiD1 α m c :=
    eventually_of_mem (Ioi_mem_nhds hz)
      (fun y hy => (hasDerivAt_radGreenI (α := α) (m := m) (c := c) hc h0 hinf y hy).deriv)
  exact (heq.differentiableAt_iff).mpr
    (rgiD1_differentiableAt (α := α) (m := m) (c := c) hc h0 hinf z hz)

end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R2.Clauses =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The three clauses of the repaired Taylor datum

`zClause_aux` (radial Lipschitz clause), `angClause_aux` (angular `α`-Hölder clause under the
*minimal* repair: continuity of the angular slices on `Iθ`), and `angClause_nbhd` (the same
clause under the *widened* smoothness hypothesis, i.e. `C¹` on a neighbourhood of the closed
angular range, which is the shape adopted by the repaired interface `R2b`).

The two analytic inputs of the angular clause are hypotheses here:
`hM`/`hIntγ` come from `Work.FTS.RegPkgGal.R2.angIntegral_le`, and `hE` from
`Work.FTS.RegPkgGal.R2.integrableOn_pth_slice`.  `angClause_nbhd` does not need `hE` (the
closed-interval FTC supplies the integrability of the derivative).
-/

open MeasureTheory Set Filter Topology
open scoped Topology Real

namespace Work.FTS.RegPkgGal.R2

/-- Auxiliary: the angular clause of the corrected Taylor datum. -/
theorem angClause_aux {α Cθ M : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCθ : 0 ≤ Cθ) (hM0 : 0 ≤ M)
    {g : ℝ → ℝ → ℝ}
    (hM : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
      (∫ θ in a..b, (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ)) ≤ M * (b - a) ^ α)
    (hIntγ : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
      IntervalIntegrable (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
        volume a b)
    (hE : ∀ z : ℝ, 0 < z → IntegrableOn (fun s : ℝ => Work.Spaces.pth g z s)
      (Set.Icc 0 (Real.pi / 2)) volume)
    (hsm : ContDiffOn ℝ 1 (Function.uncurry g)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth g z θ| ≤ Cθ * z ^ 2 * (Real.sin θ * Real.cos θ ^ 2) ^ α)
    (hcontθ : ∀ z : ℝ, 0 < z → z ≤ 2 → ContinuousOn (fun θ => g z θ) Work.Spaces.Iθ)
    (hB1 : ∀ {z θ : ℝ}, 0 < z → θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
      HasDerivAt (fun s : ℝ => g z s) (Work.Spaces.pth g z θ) θ) :
    ∀ z θ θ' : ℝ, 0 < z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ Cθ * M * z ^ 2 * |θ - θ'| ^ α := by
  intro z θ θ' hz hz2 hθ hθ'
  have key : ∀ a b : ℝ, a ∈ Work.Spaces.Iθ → b ∈ Work.Spaces.Iθ → a ≤ b →
      |g z a - g z b| ≤ Cθ * M * z ^ 2 * |a - b| ^ α := by
    intro a b ha hb hab
    rcases eq_or_lt_of_le hab with heq | hlt
    · subst heq
      simp [Real.zero_rpow (ne_of_gt hα)]
    have habI : Set.Icc a b ⊆ Work.Spaces.Iθ := fun s hs =>
      ⟨le_trans ha.1 hs.1, le_trans hs.2 hb.2⟩
    have hcont : ContinuousOn (fun s : ℝ => g z s) (Set.Icc a b) :=
      (hcontθ z hz hz2).mono habI
    have hderiv : ∀ s ∈ Set.Ioo a b,
        HasDerivAt (fun s : ℝ => g z s) (Work.Spaces.pth g z s) s := by
      intro s hs
      exact hB1 hz ⟨lt_of_le_of_lt ha.1 hs.1, lt_of_lt_of_le hs.2 hb.2⟩
    have hint : IntervalIntegrable (fun s : ℝ => Work.Spaces.pth g z s) volume a b := by
      have hsub : Set.uIoc a b ⊆ Set.Icc 0 (Real.pi / 2) := by
        intro s hs
        rw [Set.uIoc_of_le hab] at hs
        exact ⟨le_trans ha.1 (le_of_lt hs.1), le_trans hs.2 hb.2⟩
      exact intervalIntegrable_iff.mpr ((hE z hz).mono_set hsub)
    have hftc : ∫ s in a..b, Work.Spaces.pth g z s = g z b - g z a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint
    have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ Real.pi / 2 := by
      rw [ae_iff]
      simpa using measure_singleton (Real.pi / 2)
    have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Ioc a b →
        ‖Work.Spaces.pth g z s‖
          ≤ Cθ * z ^ 2 * ((Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s)) := by
      filter_upwards [hne] with s hs_ne hs_mem
      have hs0 : 0 < s := lt_of_le_of_lt ha.1 hs_mem.1
      have hs1 : s < Real.pi / 2 :=
        lt_of_le_of_ne (le_trans hs_mem.2 hb.2) hs_ne
      have hsin : 0 < Real.sin (2 * s) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      rw [Real.norm_eq_abs]
      have hD := hd z s (le_of_lt hz) ⟨hs0.le, le_of_lt hs1⟩
      have hpth : |Work.Spaces.pth g z s| = |Work.Spaces.Dth g z s| / Real.sin (2 * s) := by
        rw [Work.Spaces.Dth, abs_mul, abs_of_pos hsin,
          mul_div_cancel_left₀ _ (ne_of_gt hsin)]
      rw [hpth]
      refine (div_le_div_of_nonneg_right hD hsin.le).trans_eq ?_
      ring
    have hIntMaj : IntervalIntegrable
        (fun s : ℝ => Cθ * z ^ 2 * ((Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s)))
        volume a b :=
      (hIntγ a b ha.1 hab hb.2).const_mul (Cθ * z ^ 2)
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le hab hae hIntMaj
    rw [Real.norm_eq_abs] at hnorm
    have h2 : (∫ s in a..b, Cθ * z ^ 2 *
          ((Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s)))
        = Cθ * z ^ 2 *
          (∫ s in a..b, (Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s)) := by
      rw [intervalIntegral.integral_const_mul]
    rw [h2] at hnorm
    have h3 : Cθ * z ^ 2 *
          (∫ s in a..b, (Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s))
        ≤ Cθ * M * z ^ 2 * (b - a) ^ α := by
      have h := hM a b ha.1 hab hb.2
      have hcz : 0 ≤ Cθ * z ^ 2 := mul_nonneg hCθ (sq_nonneg z)
      have h4 := mul_le_mul_of_nonneg_left h hcz
      calc Cθ * z ^ 2 *
            (∫ s in a..b, (Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s))
          ≤ Cθ * z ^ 2 * (M * (b - a) ^ α) := h4
        _ = Cθ * M * z ^ 2 * (b - a) ^ α := by ring
    have hfin : |∫ s in a..b, Work.Spaces.pth g z s| ≤ Cθ * M * z ^ 2 * (b - a) ^ α :=
      hnorm.trans h3
    calc |g z a - g z b| = |g z b - g z a| := abs_sub_comm _ _
      _ = |∫ s in a..b, Work.Spaces.pth g z s| := by rw [hftc]
      _ ≤ Cθ * M * z ^ 2 * (b - a) ^ α := hfin
      _ = Cθ * M * z ^ 2 * |a - b| ^ α := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
  rcases le_total θ θ' with hle | hle
  · exact key θ θ' hθ hθ' hle
  · rw [abs_sub_comm, abs_sub_comm θ θ']
    exact key θ' θ hθ' hθ hle

/-- Auxiliary: the radial Lipschitz clause of the corrected Taylor datum. -/
theorem zClause_aux {K Q K' : ℝ} (hQ0 : 0 ≤ Q) (hQK : max Q K ≤ K')
    {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 (Function.uncurry g)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hvt : Work.Spaces.VanishTheta g)
    (hquad : ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ| ≤ K * z ^ 2)
    (hlinz : ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |Work.Spaces.pz g z θ| ≤ Q * z)
    (hB2 : ∀ {z θ : ℝ}, 0 < z → θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
      HasDerivAt (fun s : ℝ => g s θ) (Work.Spaces.pz g z θ) z) :
    ∀ θ ∈ Work.Spaces.Iθ, ∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
      |g z θ - g z' θ| ≤ K' * max z z' * |z - z'| := by
  intro θ hθ z z' hz hz2 hz' hz'2
  have hK'0 : 0 ≤ K' := le_trans (le_max_of_le_left hQ0) hQK
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    rw [hvt.1 z, hvt.1 z', sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hK'0 (le_max_of_le_right hz')) (abs_nonneg _)
  rcases eq_or_lt_of_le hθ.2 with hpi | hpi
  · subst hpi
    rw [hvt.2 z, hvt.2 z', sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hK'0 (le_max_of_le_right hz')) (abs_nonneg _)
  have hθI : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨h0, hpi⟩
  have hzero : g 0 θ = 0 := by
    have h := hquad θ hθ 0 le_rfl (by norm_num : (0:ℝ) ≤ 2)
    have h' : |g 0 θ| ≤ 0 := by simpa using h
    exact abs_eq_zero.mp (le_antisymm h' (abs_nonneg _))
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ 2 → 0 ≤ b → b ≤ 2 → a ≤ b →
      |g a θ - g b θ| ≤ K' * max a b * |a - b| := by
    intro a b ha ha2 hb hb2 hab
    rcases eq_or_lt_of_le hab with heq | hlt
    · subst heq
      simp
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · subst ha0
      rw [hzero, zero_sub, abs_neg, max_eq_right hb, zero_sub, abs_neg, abs_of_nonneg hb]
      have h1 : |g b θ| ≤ K * b ^ 2 := hquad θ hθ b hb hb2
      have hK' : K ≤ K' := le_trans (le_max_right Q K) hQK
      have h1' : K * b ^ 2 ≤ K' * b ^ 2 := mul_le_mul_of_nonneg_right hK' (sq_nonneg b)
      nlinarith [h1, h1']
    · have hcont : ContinuousOn (fun s : ℝ => g s θ) (Set.Icc a b) := by
        have h1 : ContinuousOn (fun s : ℝ => (s, θ)) (Set.Icc a b) :=
          continuousOn_id.prodMk continuousOn_const
        have h2 := hsm.continuousOn.comp h1 (fun s hs => ⟨lt_of_lt_of_le hapos hs.1, hθI⟩)
        simpa [Function.comp_def, Function.uncurry] using h2
      have hderiv : ∀ s ∈ Set.Ico a b,
          HasDerivWithinAt (fun s : ℝ => g s θ) (Work.Spaces.pz g s θ) (Set.Ici s) s :=
        fun s hs => (hB2 (lt_of_lt_of_le hapos hs.1) hθI).hasDerivWithinAt
      have hbound : ∀ s ∈ Set.Ico a b, ‖Work.Spaces.pz g s θ‖ ≤ Q * b := by
        intro s hs
        rw [Real.norm_eq_abs]
        have hs2 : s ≤ 2 := by linarith [hs.2, hb2]
        have h1 : |Work.Spaces.pz g s θ| ≤ Q * s := hlinz θ hθ s (le_trans ha hs.1) hs2
        have h2 : Q * s ≤ Q * b := mul_le_mul_of_nonneg_left hs.2.le hQ0
        linarith
      have hkey := norm_image_sub_le_of_norm_deriv_right_le_segment
        (f := fun s : ℝ => g s θ) (f' := fun s : ℝ => Work.Spaces.pz g s θ)
        (a := a) (b := b) (C := Q * b) hcont hderiv hbound
      have hmem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
      have hmain : ‖g b θ - g a θ‖ ≤ Q * b * (b - a) := hkey b hmem
      rw [Real.norm_eq_abs, abs_sub_comm] at hmain
      have hQK' : Q ≤ K' := le_trans (le_max_left Q K) hQK
      have h4 : Q * b * (b - a) ≤ K' * b * (b - a) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQK' hb) (by linarith)
      calc |g a θ - g b θ| ≤ Q * b * (b - a) := hmain
        _ ≤ K' * b * (b - a) := h4
        _ = K' * max a b * |a - b| := by
            rw [max_eq_right hab, abs_of_nonpos (by linarith), neg_sub]
  rcases le_total z z' with hle | hle
  · exact key z z' hz hz2 hz' hz'2 hle
  · rw [abs_sub_comm, max_comm, abs_sub_comm z z']
    exact key z' z hz' hz'2 hz hz2 hle

/-! ## The angular clause in the *widened* smoothness setting

When the joint `C¹` hypothesis is taken on a neighbourhood of the closed angular range
(`θ ∈ (-1, π/2+1)`), every angular slice is `C¹` *across* the two endpoints, so the `θ`-FTC
(`intervalIntegral.integral_deriv_of_contDiffOn_Icc`) applies with no integrability side
condition; only the angular integral bound `∫_a^b Γ/sin(2θ) ≤ M (b-a)^α` is needed.  This is
the shape of the statement used by the repaired interface. -/


end Work.FTS.RegPkgGal.R2
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R7e.Vth_barrier_L =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter
open scoped Topology

namespace Work.FTS.RegPkgGal.R7e

/-- Lipschitz control of a `θ`-slice of `Vθ` in the shifted domain `Ioi L`.

This is the `Set.Ioi L`-variant of `Work.FTS.RegPkgGal.R7d.Vth_lip_slice`: the Lipschitz
hypothesis is only available on `Ioi L ×ˢ Ioo 0 (π/2)` and the first coordinate of the two
compared points is the *same* number `z`, so the conclusion only needs `L < z` (and not
`0 < z`). -/
theorem Vth_lip_slice_L {Vz Vθ : ℝ → ℝ → ℝ → ℝ} {K S L : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ τ ∈ Set.Icc 0 S, LipschitzOnWith ⟨K, hK⟩
      (fun p : ℝ × ℝ => (Vz p.1 p.2 τ, Vθ p.1 p.2 τ))
      (Set.Ioi L ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)))
    {z τ θ₁ θ₂ : ℝ} (hz : L < z) (hτ : τ ∈ Set.Icc 0 S)
    (h₁ : θ₁ ∈ Set.Ioo (0:ℝ) (Real.pi / 2)) (h₂ : θ₂ ∈ Set.Ioo (0:ℝ) (Real.pi / 2)) :
    |Vθ z θ₁ τ - Vθ z θ₂ τ| ≤ K * |θ₁ - θ₂| := by
  -- Both points `(z, θ₁)` and `(z, θ₂)` lie in the domain `Ioi L ×ˢ Ioo 0 (π/2)`
  -- of the Lipschitz map, so the Lipschitz bound applies to them.
  have hp₁ : ((z, θ₁) : ℝ × ℝ) ∈ Set.Ioi L ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨hz, h₁⟩
  have hp₂ : ((z, θ₂) : ℝ × ℝ) ∈ Set.Ioi L ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨hz, h₂⟩
  have hd := (hlip τ hτ).dist_le_mul (z, θ₁) hp₁ (z, θ₂) hp₂
  -- The second coordinate of the product metric is dominated by the product metric.
  have hle : dist (Vθ z θ₁ τ) (Vθ z θ₂ τ)
      ≤ dist ((Vz z θ₁ τ, Vθ z θ₁ τ) : ℝ × ℝ) (Vz z θ₂ τ, Vθ z θ₂ τ) := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  -- The two base points share their first coordinate, so their distance is `|θ₁ - θ₂|`.
  have hdist : dist ((z, θ₁) : ℝ × ℝ) (z, θ₂) = |θ₁ - θ₂| := by
    simp [Prod.dist_eq, Real.dist_eq]
  calc |Vθ z θ₁ τ - Vθ z θ₂ τ| = dist (Vθ z θ₁ τ) (Vθ z θ₂ τ) := (Real.dist_eq _ _).symm
    _ ≤ dist ((Vz z θ₁ τ, Vθ z θ₁ τ) : ℝ × ℝ) (Vz z θ₂ τ, Vθ z θ₂ τ) := hle
    _ ≤ K * dist ((z, θ₁) : ℝ × ℝ) (z, θ₂) := hd
    _ = K * |θ₁ - θ₂| := by rw [hdist]

/-- Barrier estimate for the angular component of a Lipschitz velocity field which vanishes on
the two angular endpoints, in the shifted domain `z > L`.

If `(Vz, Vθ)` is `K`-Lipschitz on the quadrant `(L,∞) × (0,π/2)`, uniformly for the parameter
`τ ∈ [0,S]`, jointly continuous on the closed strip `(0,∞) × [0,π/2] × [0,S]`, and `Vθ` vanishes
at `θ = 0` and at `θ = π/2` (for `τ > 0`), then for `z > L ≥ 0`, `θ ∈ (0,π/2)` and `τ ∈ [0,S]`
one has `|Vθ z θ τ| ≤ K θ` and `|Vθ z θ τ| ≤ K (π/2 - θ)`.

The three ingredients are separated out: `Vth_lip_slice_L` turns the Lipschitz hypothesis into
the slicewise bound `|Vθ z θ₁ τ - Vθ z θ₂ τ| ≤ K |θ₁ - θ₂|` (only `z > L` is used, since the two
compared points share the first coordinate), `Vth_edge_cont` gives the one-sided continuity at
the two endpoints, and both limits `θ₂ → 0⁺` and `θ₂ → (π/2)⁻` are then taken by
`le_of_tendsto_of_tendsto`.

At `τ = 0` the two endpoint values are *recovered* from the joint continuity in `τ` together
with the `τ > 0` vanishing, so no case distinction is needed in the conclusion. -/
theorem Vth_barrier_L {Vz Vθ : ℝ → ℝ → ℝ → ℝ} {K S L : ℝ} (hS : 0 < S) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hlip : ∀ τ ∈ Set.Icc 0 S, LipschitzOnWith ⟨K, hK⟩
      (fun p : ℝ × ℝ => (Vz p.1 p.2 τ, Vθ p.1 p.2 τ))
      (Set.Ioi L ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)))
    (hcont : ContinuousOn (fun p : ℝ × ℝ × ℝ => (Vz p.1 p.2.1 p.2.2, Vθ p.1 p.2.1 p.2.2))
      (Set.Ioi (0:ℝ) ×ˢ (Set.Icc (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)))
    (h0 : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z 0 τ = 0)
    (hπ : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z (Real.pi / 2) τ = 0) :
    ∀ z θ τ : ℝ, L < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ → τ ≤ S →
      |Vθ z θ τ| ≤ K * θ ∧ |Vθ z θ τ| ≤ K * (Real.pi / 2 - θ) := by
  intro z θ τ hzL hθ0 hθπ hτ0 hτS
  -- `z > L ≥ 0`, so the joint continuity (which lives on `Ioi 0`) applies at `z`.
  have hz : 0 < z := lt_of_le_of_lt hL hzL
  have hπ2pos : (0:ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  set reg : Set (ℝ × ℝ × ℝ) :=
    Set.Ioi (0:ℝ) ×ˢ (Set.Icc (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S) with hreg
  -- the two angular boundary points lie in the continuity region
  have hmem0 : (z, (0:ℝ), τ) ∈ reg := ⟨hz, ⟨⟨le_rfl, hπ2pos.le⟩, ⟨hτ0, hτS⟩⟩⟩
  have hmemπ : (z, Real.pi / 2, τ) ∈ reg := ⟨hz, ⟨⟨hπ2pos.le, le_rfl⟩, ⟨hτ0, hτS⟩⟩⟩
  -- the Lipschitz control of a slice (shifted-domain variant proved above)
  have hlip_slice : ∀ θ₁ θ₂ : ℝ, θ₁ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
      θ₂ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) → |Vθ z θ₁ τ - Vθ z θ₂ τ| ≤ K * |θ₁ - θ₂| :=
    fun θ₁ θ₂ h₁ h₂ =>
      Vth_lip_slice_L (K := K) (S := S) (L := L) hK hlip hzL ⟨hτ0, hτS⟩ h₁ h₂
  -- one-sided continuity in `θ` at the two endpoints (Lipschitz-independent)
  have hedge := Work.FTS.RegPkgGal.R7d.Vth_edge_cont (S := S) hcont hz hτ0 hτS
  have htend0 : Tendsto (fun θ' : ℝ => Vθ z θ' τ) (𝓝[>] (0:ℝ)) (𝓝 (Vθ z 0 τ)) := hedge.1
  have htendπ : Tendsto (fun θ' : ℝ => Vθ z θ' τ) (𝓝[<] (Real.pi / 2))
      (𝓝 (Vθ z (Real.pi / 2) τ)) := hedge.2
  -- the two endpoint values vanish (at `τ = 0` recovered by continuity in `τ`)
  have hb0 : Vθ z 0 τ = 0 := by
    rcases eq_or_lt_of_le hτ0 with hτ | hτ
    · subst hτ
      have hc : Tendsto (fun t : ℝ => Vθ z 0 t) (𝓝[>] (0:ℝ)) (𝓝 (Vθ z 0 0)) := by
        have hmap : Set.MapsTo (fun t : ℝ => (z, (0:ℝ), t)) (Set.Ioo (0:ℝ) S) reg := by
          intro t ht
          exact ⟨hz, ⟨⟨le_rfl, hπ2pos.le⟩, ⟨ht.1.le, ht.2.le⟩⟩⟩
        have hcw := ContinuousWithinAt.comp (f := fun t : ℝ => (z, (0:ℝ), t))
          (s := Set.Ioo (0:ℝ) S) (x := (0:ℝ))
          (hcont.continuousWithinAt hmem0) (by fun_prop) hmap
        change Tendsto (fun t : ℝ => (Vz z 0 t, Vθ z 0 t))
          (𝓝[Set.Ioo (0:ℝ) S] (0:ℝ)) (𝓝 (Vz z 0 0, Vθ z 0 0)) at hcw
        rw [nhdsWithin_Ioo_eq_nhdsGT hS, nhds_prod_eq] at hcw
        exact hcw.snd
      have hev : (fun _ : ℝ => (0:ℝ)) =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ => Vθ z 0 t) := by
        filter_upwards [Ioo_mem_nhdsGT hS] with t ht
        exact (h0 z t hz ht.1 ht.2.le).symm
      exact tendsto_nhds_unique hc (Tendsto.congr' hev tendsto_const_nhds)
    · exact h0 z τ hz hτ hτS
  have hbπ : Vθ z (Real.pi / 2) τ = 0 := by
    rcases eq_or_lt_of_le hτ0 with hτ | hτ
    · subst hτ
      have hc : Tendsto (fun t : ℝ => Vθ z (Real.pi / 2) t) (𝓝[>] (0:ℝ))
          (𝓝 (Vθ z (Real.pi / 2) 0)) := by
        have hmap : Set.MapsTo (fun t : ℝ => (z, Real.pi / 2, t)) (Set.Ioo (0:ℝ) S) reg := by
          intro t ht
          exact ⟨hz, ⟨⟨hπ2pos.le, le_rfl⟩, ⟨ht.1.le, ht.2.le⟩⟩⟩
        have hcw := ContinuousWithinAt.comp (f := fun t : ℝ => (z, Real.pi / 2, t))
          (s := Set.Ioo (0:ℝ) S) (x := (0:ℝ))
          (hcont.continuousWithinAt hmemπ) (by fun_prop) hmap
        change Tendsto (fun t : ℝ => (Vz z (Real.pi / 2) t, Vθ z (Real.pi / 2) t))
          (𝓝[Set.Ioo (0:ℝ) S] (0:ℝ))
          (𝓝 (Vz z (Real.pi / 2) 0, Vθ z (Real.pi / 2) 0)) at hcw
        rw [nhdsWithin_Ioo_eq_nhdsGT hS, nhds_prod_eq] at hcw
        exact hcw.snd
      have hev : (fun _ : ℝ => (0:ℝ)) =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ => Vθ z (Real.pi / 2) t) := by
        filter_upwards [Ioo_mem_nhdsGT hS] with t ht
        exact (hπ z t hz ht.1 ht.2.le).symm
      exact tendsto_nhds_unique hc (Tendsto.congr' hev tendsto_const_nhds)
    · exact hπ z τ hz hτ hτS
  have hθmem : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨hθ0, hθπ⟩
  -- the two limit passages `θ₂ → 0⁺` and `θ₂ → (π/2)⁻`
  have key0 : |Vθ z θ τ - Vθ z 0 τ| ≤ K * θ := by
    have hev : (fun θ₂ : ℝ => |Vθ z θ τ - Vθ z θ₂ τ|) ≤ᶠ[𝓝[>] (0:ℝ)]
        (fun θ₂ : ℝ => K * |θ - θ₂|) := by
      filter_upwards [Ioo_mem_nhdsGT hπ2pos] with θ₂ hθ₂
      exact hlip_slice θ θ₂ hθmem ⟨hθ₂.1, hθ₂.2⟩
    have hlim1 : Tendsto (fun θ₂ : ℝ => |Vθ z θ τ - Vθ z θ₂ τ|) (𝓝[>] (0:ℝ))
        (𝓝 |Vθ z θ τ - Vθ z 0 τ|) :=
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => Vθ z θ τ) (𝓝[>] (0:ℝ))
        (𝓝 (Vθ z θ τ))).sub htend0).abs
    have hlim2 : Tendsto (fun θ₂ : ℝ => K * |θ - θ₂|) (𝓝[>] (0:ℝ)) (𝓝 (K * θ)) := by
      have hA : Tendsto (fun x : ℝ => |θ - x|) (𝓝[>] (0:ℝ)) (𝓝 |θ - 0|) :=
        (((continuous_const.sub continuous_id).tendsto 0).mono_left
          nhdsWithin_le_nhds).abs
      have hB := hA.const_mul K
      simpa [abs_of_pos hθ0] using hB
    exact le_of_tendsto_of_tendsto hlim1 hlim2 hev
  have keyπ : |Vθ z θ τ - Vθ z (Real.pi / 2) τ| ≤ K * (Real.pi / 2 - θ) := by
    have hev : (fun θ₂ : ℝ => |Vθ z θ τ - Vθ z θ₂ τ|) ≤ᶠ[𝓝[<] (Real.pi / 2)]
        (fun θ₂ : ℝ => K * |θ - θ₂|) := by
      filter_upwards [Ioo_mem_nhdsLT hπ2pos] with θ₂ hθ₂
      exact hlip_slice θ θ₂ hθmem ⟨hθ₂.1, hθ₂.2⟩
    have hlim1 : Tendsto (fun θ₂ : ℝ => |Vθ z θ τ - Vθ z θ₂ τ|) (𝓝[<] (Real.pi / 2))
        (𝓝 |Vθ z θ τ - Vθ z (Real.pi / 2) τ|) :=
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => Vθ z θ τ) (𝓝[<] (Real.pi / 2))
        (𝓝 (Vθ z θ τ))).sub htendπ).abs
    have hlim2 : Tendsto (fun θ₂ : ℝ => K * |θ - θ₂|) (𝓝[<] (Real.pi / 2))
        (𝓝 (K * (Real.pi / 2 - θ))) := by
      have hA : Tendsto (fun x : ℝ => |θ - x|) (𝓝[<] (Real.pi / 2)) (𝓝 |θ - Real.pi / 2|) :=
        (((continuous_const.sub continuous_id).tendsto (Real.pi / 2)).mono_left
          nhdsWithin_le_nhds).abs
      have hB := hA.const_mul K
      have habs : |θ - Real.pi / 2| = Real.pi / 2 - θ := by
        rw [abs_of_neg (show θ - Real.pi / 2 < 0 by linarith)]
        ring
      simpa [habs] using hB
    exact le_of_tendsto_of_tendsto hlim1 hlim2 hev
  have hfinal0 : |Vθ z θ τ| ≤ K * θ := by
    have h := key0
    rw [hb0, sub_zero] at h
    exact h
  have hfinalπ : |Vθ z θ τ| ≤ K * (Real.pi / 2 - θ) := by
    have h := keyπ
    rw [hbπ, sub_zero] at h
    exact h
  exact ⟨hfinal0, hfinalπ⟩

end Work.FTS.RegPkgGal.R7e
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R7e.trajectory_bounds_L =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R7e

open Set Filter
open scoped Topology

/-- **Right-continuation of strict good behaviour.**  If the trajectory is strictly above the
level `L` and strictly inside the open quadrant at a time `σ < T`, then it stays so on a
further right neighbourhood of `σ` (inside `[0,T]`).  This is the `L`-analogue of
`Work.FTS.RegPkgGal.R7d.quadrant_extend`; note that `L < z` does *not* follow from `0 < z`. -/
theorem quadrant_extend_L {α : ℝ → ℝ × ℝ} {L σ T : ℝ} (hσ0 : 0 ≤ σ) (hσT : σ < T)
    (hαc : ContinuousOn α (Set.Icc 0 T)) (h1 : L < (α σ).1) (h2 : 0 < (α σ).2)
    (h3 : (α σ).2 < Real.pi / 2) :
    ∃ δ : ℝ, 0 < δ ∧ σ + δ ≤ T ∧
      ∀ x ∈ Set.Ioo σ (σ + δ), L < (α x).1 ∧ 0 < (α x).2 ∧ (α x).2 < Real.pi / 2 := by
  have hopen : IsOpen {y : ℝ × ℝ | L < y.1 ∧ 0 < y.2 ∧ y.2 < Real.pi / 2} := by
    have h1o : IsOpen {y : ℝ × ℝ | L < y.1} := isOpen_lt continuous_const continuous_fst
    have h2o : IsOpen {y : ℝ × ℝ | 0 < y.2} := isOpen_lt continuous_const continuous_snd
    have h3o : IsOpen {y : ℝ × ℝ | y.2 < Real.pi / 2} :=
      isOpen_lt continuous_snd continuous_const
    exact h1o.inter (h2o.inter h3o)
  have hσmem : σ ∈ Set.Icc 0 T := ⟨hσ0, le_of_lt hσT⟩
  have hVw : α ⁻¹' {y : ℝ × ℝ | L < y.1 ∧ 0 < y.2 ∧ y.2 < Real.pi / 2} ∈
      𝓝[Set.Icc 0 T] σ :=
    (hαc.continuousWithinAt hσmem) (hopen.mem_nhds ⟨h1, h2, h3⟩)
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhdsWithin_iff.mp hVw
  refine ⟨min (ε / 2) ((T - σ) / 2), ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · have hle : min (ε / 2) ((T - σ) / 2) ≤ (T - σ) / 2 := min_le_right _ _
    linarith
  · intro x hx
    have hxIcc : x ∈ Set.Icc 0 T := by
      have hmm : min (ε / 2) ((T - σ) / 2) ≤ (T - σ) / 2 := min_le_right _ _
      constructor <;> linarith [hx.1, hx.2]
    have hxball : x ∈ Metric.ball σ ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith [hx.1])]
      have hmm : min (ε / 2) ((T - σ) / 2) ≤ ε / 2 := min_le_left _ _
      linarith [hx.2]
    exact hε ⟨hxball, hxIcc⟩

theorem trajectory_bounds_L {Vz Vθ : ℝ → ℝ → ℝ → ℝ} {a K S τ₀ T z₀ θ₀ L : ℝ} {α : ℝ → ℝ × ℝ}
    (hL : 0 ≤ L)
    (hT : 0 ≤ T) (hTS : T ≤ τ₀) (hτ₀S : τ₀ ≤ S)
    (hz₀ : L < z₀ * Real.exp (-(a * T)))
    (hθ₀ : 0 < θ₀) (hθ₀' : θ₀ < Real.pi / 2) (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hα0 : α 0 = (z₀, θ₀))
    (hode : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivWithinAt α
      (-((α t).1 * Vz (α t).1 (α t).2 (τ₀ - t)), -(Vθ (α t).1 (α t).2 (τ₀ - t)))
      (Set.Icc (0:ℝ) T) t)
    (hVz0 : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → 0 ≤ Vz z θ τ)
    (hVza : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → Vz z θ τ ≤ a)
    (hVθl : ∀ z θ τ : ℝ, L < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → |Vθ z θ τ| ≤ K * θ)
    (hVθu : ∀ z θ τ : ℝ, L < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      |Vθ z θ τ| ≤ K * (Real.pi / 2 - θ)) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      z₀ * Real.exp (-(a * t)) ≤ (α t).1 ∧ (α t).1 ≤ z₀ ∧
      θ₀ * Real.exp (-(K * t)) ≤ (α t).2 ∧
      (α t).2 ≤ Real.pi / 2 - (Real.pi / 2 - θ₀) * Real.exp (-(K * t)) := by
  -- The trajectory is strictly above the level `L` and strictly inside the open quadrant on
  -- the (a priori unknown) maximal interval `(0, σ)`.  On that interval the pointwise
  -- hypotheses on the velocity field are available, since `L < z` together with `0 ≤ L`
  -- gives `0 < z`.
  have hαc : ContinuousOn α (Set.Icc (0:ℝ) T) :=
    fun t ht => (hode t ht).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) T, HasDerivAt α
      (-((α x).1 * Vz (α x).1 (α x).2 (τ₀ - x)), -(Vθ (α x).1 (α x).2 (τ₀ - x))) x :=
    fun x hx => (hode x ⟨hx.1.le, hx.2.le⟩).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  -- ## Step 1: the four bounds on `[0,b]`, given that `L < (α x).1` and the trajectory is
  -- strictly inside the open quadrant for `x ∈ (0,b)`
  have hbounds : ∀ b ∈ Set.Icc (0:ℝ) T,
      (∀ x ∈ Set.Ioo (0:ℝ) b, L < (α x).1 ∧ 0 < (α x).2 ∧ (α x).2 < Real.pi / 2) →
      ∀ x ∈ Set.Icc (0:ℝ) b,
        z₀ * Real.exp (-(a * x)) ≤ (α x).1 ∧ (α x).1 ≤ z₀ ∧
        θ₀ * Real.exp (-(K * x)) ≤ (α x).2 ∧
        (α x).2 ≤ Real.pi / 2 - (Real.pi / 2 - θ₀) * Real.exp (-(K * x)) := by
    intro b hb hQ
    -- `L < z` upgrades to `0 < z`, which is what the field hypotheses and `zBounds` need
    have hQz : ∀ x ∈ Set.Ioo (0:ℝ) b, 0 < (α x).1 :=
      fun x hx => lt_of_le_of_lt hL (hQ x hx).1
    -- the fake time `τ₀ - x` is strictly positive and at most `S` on `(0,b)`
    have hτpos : ∀ x ∈ Set.Ioo (0:ℝ) b, 0 < τ₀ - x := by
      intro x hx
      have hxτ : x < τ₀ := lt_of_lt_of_le (lt_of_lt_of_le hx.2 hb.2) hTS
      linarith
    have hτle : ∀ x ∈ Set.Ioo (0:ℝ) b, τ₀ - x ≤ S := by
      intro x hx
      linarith [hx.1, hτ₀S]
    have hbc : ContinuousOn α (Set.Icc (0:ℝ) b) := hαc.mono (Icc_subset_Icc le_rfl hb.2)
    -- the `z`-bounds
    have hzB : ∀ x ∈ Set.Icc (0:ℝ) b,
        z₀ * Real.exp (-(a * x)) ≤ (α x).1 ∧ (α x).1 ≤ z₀ :=
      Work.FTS.RegPkgGal.R7d.zBounds (z := fun x => (α x).1)
        (V := fun x => Vz (α x).1 (α x).2 (τ₀ - x))
        (a := a) (z₀ := z₀) (T := b) hbc.fst (by rw [hα0])
        (fun x hx => Work.FTS.RegPkgGal.R7d.hasDerivAt_fst
          (hderiv x ⟨hx.1, lt_of_lt_of_le hx.2 hb.2⟩))
        (fun x hx => hVz0 _ _ _ (hQz x hx) (hQ x hx).2.1 (hQ x hx).2.2 (hτpos x hx) (hτle x hx))
        (fun x hx => hVza _ _ _ (hQz x hx) (hQ x hx).2.1 (hQ x hx).2.2 (hτpos x hx) (hτle x hx))
        (fun x hx => (hQz x hx).le)
    -- the `θ`-bounds
    have hθB : ∀ x ∈ Set.Icc (0:ℝ) b,
        θ₀ * Real.exp (-(K * x)) ≤ (α x).2 ∧
        (α x).2 ≤ Real.pi / 2 - (Real.pi / 2 - θ₀) * Real.exp (-(K * x)) :=
      Work.FTS.RegPkgGal.R7d.thBounds (θ := fun x => (α x).2)
        (V := fun x => Vθ (α x).1 (α x).2 (τ₀ - x))
        (K := K) (θ₀ := θ₀) (T := b) hbc.snd (by rw [hα0])
        (fun x hx => Work.FTS.RegPkgGal.R7d.hasDerivAt_snd
          (hderiv x ⟨hx.1, lt_of_lt_of_le hx.2 hb.2⟩))
        (fun x hx => hVθl _ _ _ (hQ x hx).1 (hQ x hx).2.1 (hQ x hx).2.2 (hτpos x hx) (hτle x hx))
        (fun x hx => hVθu _ _ _ (hQ x hx).1 (hQ x hx).2.1 (hQ x hx).2.2 (hτpos x hx) (hτle x hx))
    intro x hx
    exact ⟨(hzB x hx).1, (hzB x hx).2, (hθB x hx).1, (hθB x hx).2⟩
  -- ## Step 2: the bootstrap on the maximal time of strict good behaviour
  set G : Set ℝ := {b | b ∈ Set.Icc (0:ℝ) T ∧
    ∀ x ∈ Set.Ioo (0:ℝ) b, L < (α x).1 ∧ 0 < (α x).2 ∧ (α x).2 < Real.pi / 2}
  have hG0 : (0 : ℝ) ∈ G := by
    refine ⟨⟨le_rfl, hT⟩, ?_⟩
    intro x hx
    exact absurd hx.1 (not_lt.mpr hx.2.le)
  have hGne : G.Nonempty := ⟨0, hG0⟩
  have hGbdd : BddAbove G := ⟨T, fun b hb => hb.1.2⟩
  have hσ0 : 0 ≤ sSup G := le_csSup hGbdd hG0
  have hσT : sSup G ≤ T := (csSup_le_iff hGbdd hGne).mpr (fun b hb => hb.1.2)
  -- the trajectory is good on `(0, sSup G)`
  have hQsSup : ∀ x ∈ Set.Ioo (0:ℝ) (sSup G),
      L < (α x).1 ∧ 0 < (α x).2 ∧ (α x).2 < Real.pi / 2 := by
    intro x hx
    obtain ⟨b, hbG, hxb⟩ := (lt_csSup_iff hGbdd hGne).mp hx.2
    exact hbG.2 x ⟨hx.1, hxb⟩
  -- hence the bounds hold on `[0, sSup G]`
  have hPsSup : ∀ x ∈ Set.Icc (0:ℝ) (sSup G),
      z₀ * Real.exp (-(a * x)) ≤ (α x).1 ∧ (α x).1 ≤ z₀ ∧
      θ₀ * Real.exp (-(K * x)) ≤ (α x).2 ∧
      (α x).2 ≤ Real.pi / 2 - (Real.pi / 2 - θ₀) * Real.exp (-(K * x)) :=
    hbounds (sSup G) ⟨hσ0, hσT⟩ hQsSup
  have hPsSup' := hPsSup (sSup G) ⟨hσ0, le_rfl⟩
  -- `z₀` is positive, and the lower `z`-bound is above `L` at `sSup G`
  have hz₀pos : 0 < z₀ :=
    pos_of_mul_pos_left (lt_of_le_of_lt hL hz₀) (Real.exp_pos _).le
  -- strict good behaviour at `sSup G`
  have hQσ : L < (α (sSup G)).1 ∧ 0 < (α (sSup G)).2 ∧ (α (sSup G)).2 < Real.pi / 2 := by
    refine ⟨?_, ?_, ?_⟩
    · have hexp_le : Real.exp (-(a * T)) ≤ Real.exp (-(a * sSup G)) := by
        rw [Real.exp_le_exp]
        linarith [mul_le_mul_of_nonneg_left hσT ha]
      have h1 : z₀ * Real.exp (-(a * T)) ≤ z₀ * Real.exp (-(a * sSup G)) :=
        mul_le_mul_of_nonneg_left hexp_le hz₀pos.le
      linarith [hPsSup'.1]
    · have hpos : 0 < θ₀ * Real.exp (-(K * sSup G)) := mul_pos hθ₀ (Real.exp_pos _)
      linarith [hPsSup'.2.2.1]
    · have hpos : 0 < (Real.pi / 2 - θ₀) * Real.exp (-(K * sSup G)) :=
        mul_pos (by linarith) (Real.exp_pos _)
      linarith [hPsSup'.2.2.2]
  -- `sSup G` is maximal: it cannot be strictly below `T`
  have hσeq : sSup G = T := by
    rcases lt_or_eq_of_le hσT with hlt | heq
    · exfalso
      obtain ⟨δ, hδ0, hσδT, hQδ⟩ :=
        quadrant_extend_L hσ0 hlt hαc hQσ.1 hQσ.2.1 hQσ.2.2
      have hmem : sSup G + δ ∈ G := by
        refine ⟨⟨by linarith, hσδT⟩, fun x hx => ?_⟩
        rcases lt_trichotomy x (sSup G) with hlt' | heq' | hgt'
        · exact hQsSup x ⟨hx.1, hlt'⟩
        · rw [heq']; exact hQσ
        · exact hQδ x ⟨hgt', hx.2⟩
      have hle : sSup G + δ ≤ sSup G := le_csSup hGbdd hmem
      linarith
    · exact heq
  -- ## Step 3: conclusion
  have hQT : ∀ x ∈ Set.Ioo (0:ℝ) T,
      L < (α x).1 ∧ 0 < (α x).2 ∧ (α x).2 < Real.pi / 2 := by
    intro x hx
    rw [← hσeq] at hx
    exact hQsSup x hx
  exact hbounds T ⟨hT, le_rfl⟩ hQT

end Work.FTS.RegPkgGal.R7e
end
-- ===== merged: Submission.Work.FTS.Regularity.Moduli.fstarDerivLip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Regularity.Moduli

open Set

/-- The second derivative of the profile `F_*`: the function `2(1-z)/(1+z)³` is
differentiable on `[0,∞)` with derivative `4(z-2)/(1+z)⁴`. -/
private lemma hasDerivAt_derivFstar (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => 2 * (1 - y) / (1 + y) ^ 3) (4 * (x - 2) / (1 + x) ^ 4) x := by
  have hnum : HasDerivAt (fun y : ℝ => 2 * (1 - y)) (-2) x := by
    have h : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id' (𝕜 := ℝ) x).const_sub 1
    convert h.const_mul 2 using 1
    ring
  have hden : HasDerivAt (fun y : ℝ => (1 + y) ^ 3) (3 * (1 + x) ^ 2) x := by
    have h := (Work.FM.hasDerivAt_add_const 1 x).pow 3
    convert h using 1
    ring
  have hne : (1 + x) ^ 3 ≠ 0 := by
    have h1 : (0 : ℝ) < 1 + x := by linarith
    positivity
  have hdiv := hnum.div hden hne
  convert hdiv using 1
  have h1 : (1 + x) ≠ 0 := by linarith
  field_simp
  ring

/-- The bound `|4(z-2)/(1+z)⁴| ≤ 8` for `z ≥ 0`, i.e. `|z-2| ≤ 2(1+z)⁴`. -/
private lemma norm_secondDerivFstar_le (x : ℝ) (hx : 0 ≤ x) :
    ‖4 * (x - 2) / (1 + x) ^ 4‖ ≤ 8 := by
  have hpow : (1 + x) ≤ (1 + x) ^ 4 := by
    have h := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + x) (by norm_num : 1 ≤ 4)
    simpa using h
  have h4 : |x - 2| ≤ 2 * (1 + x) ^ 4 := by
    rw [abs_le]
    constructor <;> nlinarith [hpow, hx]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + x) ^ 4),
    div_le_iff₀ (by positivity : (0 : ℝ) < (1 + x) ^ 4), abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  linarith

/-- `deriv F_*` is Lipschitz with constant `8` on `[0,∞)`: the fundamental model's
profile derivative cannot oscillate faster than this on the physical range of the
self-similar variable. -/
lemma fstarDerivLip {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') : |deriv Work.FM.Fstar z - deriv Work.FM.Fstar z'| ≤ 8 * |z - z'| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => 2 * (1 - y) / (1 + y) ^ 3)
    (f' := fun y : ℝ => 4 * (y - 2) / (1 + y) ^ 4)
    (s := Set.Ici 0) (C := 8) (x := z') (y := z)
    (fun y hy => (hasDerivAt_derivFstar y hy).hasDerivWithinAt)
    (fun y hy => norm_secondDerivFstar_le y hy)
    (convex_Ici 0) hz' hz
  rw [Work.FM.deriv_Fstar z (by linarith), Work.FM.deriv_Fstar z' (by linarith)]
  simpa [Real.norm_eq_abs] using h

end Work.FTS.Regularity.Moduli
end
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.StarAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.ClassCRHS

set_option autoImplicit false

/-- The radial profile `z ↦ 2z²/(1+z)³` of the first two scaled `F_*`-atoms. -/
def SR0 (z : ℝ) : ℝ := 2 * z ^ 2 / (1 + z) ^ 3

/-- The radial profile `z ↦ 2z²(1-z)/(1+z)⁴` of the third scaled `F_*`-atom. -/
def SR2 (z : ℝ) : ℝ := 2 * z ^ 2 * (1 - z) / (1 + z) ^ 4

/-- The angular profile `αΓ/c` of `F_*`. -/
def SA0 (α θ : ℝ) : ℝ := α * Work.Spaces.Gam α θ / Work.Spaces.c α

/-- The angular profile `α D_θΓ/c` of `D_θF_*`. -/
def SA1 (α θ : ℝ) : ℝ :=
  α * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α

/-- The angular majorant `Γ·(α + sin 2θ)`: `G²·sin(2θ)^{-γ}` has an `α`-uniform mass bound
(`Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt`). -/
def SGmj (α θ : ℝ) : ℝ := Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))

end Work.FTS.StrongEps.ClassCRHS
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.vfs4_maj_integral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

open scoped Real
open MeasureTheory

theorem vfs4_maj_integral {A Bm α : ℝ} (hA : 0 ≤ A) (hBm : 0 ≤ Bm)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + Bm * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ,
          (A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + Bm * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30))))
        ≤ A * 400 + Bm * (120 / (17 * α)) := by
  have hEta := Work.Coercivity.integral_sin_two_neg_rpow_le Work.Spaces.eta
      Work.Spaces.eta_pos Work.Spaces.eta_lt_one
  have hq0 : 0 < 1 - 17 * α / 30 := by linarith
  have hq1 : 1 - 17 * α / 30 < 1 := by linarith
  have hQ := Work.Coercivity.integral_sin_two_neg_rpow_le (1 - 17 * α / 30) hq0 hq1
  have hIntA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => A * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    hEta.1.const_mul A
  have hIntB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Bm * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30))) Work.Spaces.Iθ :=
    hQ.1.const_mul Bm
  have e1 : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ 400 := by
    refine le_trans hEta.2 ?_
    norm_num [Work.Spaces.eta]
  have e2 : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)))
      ≤ 120 / (17 * α) := by
    have hpos : (0 : ℝ) < 17 * α / 30 := by positivity
    have hpos' : (0 : ℝ) < 17 * α := by positivity
    have key : 4 / (1 - (1 - 17 * α / 30)) ≤ 120 / (17 * α) := by
      rw [show 1 - (1 - 17 * α / 30) = 17 * α / 30 by ring]
      rw [div_le_div_iff₀ hpos hpos']
      ring_nf
      linarith
    exact le_trans hQ.2 key
  refine ⟨hIntA.add hIntB, ?_⟩
  rw [integral_add hIntA hIntB, integral_const_mul, integral_const_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left e1 hA) (mul_le_mul_of_nonneg_left e2 hBm)

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary.sin_two_rpow_block_integrals =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary

/-- Both exponents occurring in the block integrals are of the form `-q` with `0 < q < 1`, so
`Work.Coercivity.integral_sin_two_neg_rpow_le` applies directly:

* `eta - 2α/3 = 97/300 + (1-α)2/3 ≥ 97/300 > 0` for `α ≤ 1`, giving the bound
  `4/(1 - (eta - 2α/3)) = 4/(1/100 + 2α/3) ≤ 400`;
* `gam α - 2α/3 = 1 - 17α/30 ∈ [13/30, 1)` for `0 < α ≤ 1`, and
  `4/(1 - (gam α - 2α/3)) = 4/(17α/30) = 120/(17α)` **exactly**. -/
theorem sin_two_rpow_block_integrals : ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta))
        Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)) ≤ 400 ∧
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
        Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α))
      ≤ 120 / (17 * α) := by
  intro α hα
  obtain ⟨hα0, hα1⟩ := hα
  have heta : Work.Spaces.eta = 99 / 100 := rfl
  have hgam : Work.Spaces.gam α = 1 + α / 10 := rfl
  -- ### The first block: exponent `2α/3 - η = -(η - 2α/3)`
  have hq0 : 0 < Work.Spaces.eta - 2 * α / 3 := by
    rw [heta]; linarith
  have hq1 : Work.Spaces.eta - 2 * α / 3 < 1 := by
    rw [heta]; linarith
  obtain ⟨hInt1, hBd1⟩ :=
    Work.Coercivity.integral_sin_two_neg_rpow_le (Work.Spaces.eta - 2 * α / 3) hq0 hq1
  have hexp1 : (2 * α / 3 : ℝ) - Work.Spaces.eta = -(Work.Spaces.eta - 2 * α / 3) := by ring
  -- ### The second block: exponent `2α/3 - γ = -(γ - 2α/3)`
  have hq0' : 0 < Work.Spaces.gam α - 2 * α / 3 := by
    rw [hgam]; linarith
  have hq1' : Work.Spaces.gam α - 2 * α / 3 < 1 := by
    rw [hgam]; linarith
  obtain ⟨hInt2, hBd2⟩ :=
    Work.Coercivity.integral_sin_two_neg_rpow_le (Work.Spaces.gam α - 2 * α / 3) hq0' hq1'
  have hexp2 : (2 * α / 3 : ℝ) - Work.Spaces.gam α = -(Work.Spaces.gam α - 2 * α / 3) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hexp1] using hInt1
  · have h400 : 4 / (1 - (99 / 100 - 2 * α / 3)) ≤ 400 := by
      rw [show (1 : ℝ) - (99 / 100 - 2 * α / 3) = 1 / 100 + 2 * α / 3 by ring]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 / 100 + 2 * α / 3)]
      linarith
    calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.eta)
        = ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta - 2 * α / 3)) := by
          simp only [hexp1]
      _ ≤ 4 / (1 - (Work.Spaces.eta - 2 * α / 3)) := hBd1
      _ = 4 / (1 - (99 / 100 - 2 * α / 3)) := by rw [heta]
      _ ≤ 400 := h400
  · simpa only [hexp2] using hInt2
  · have hb2 : 4 / (1 - (Work.Spaces.gam α - 2 * α / 3)) = 120 / (17 * α) := by
      rw [show (1 : ℝ) - (Work.Spaces.gam α - 2 * α / 3) = 17 * α / 30 by rw [hgam]; ring]
      rw [div_eq_div_iff (by positivity : (17 * α / 30 : ℝ) ≠ 0)
        (by positivity : (17 * α : ℝ) ≠ 0)]
      ring
    calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)
        = ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 2 * α / 3)) := by
          simp only [hexp2]
      _ ≤ 4 / (1 - (Work.Spaces.gam α - 2 * α / 3)) := hBd2
      _ = 120 / (17 * α) := hb2

end Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.AgmonWindow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false


/-! ## Elementary facts about the weight `w` -/

/-- The weight `w(z) = (1+z)²/z² = (1 + 1/z)²` is antitone on `(0,∞)`. -/
theorem w_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Work.Spaces.w b ≤ Work.Spaces.w a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : (1 + b) / b = 1 + 1 / b := by field_simp; ring
  have h2 : (1 + a) / a = 1 + 1 / a := by field_simp; ring
  have h3 : (1 : ℝ) + 1 / b ≤ 1 + 1 / a := by
    have h : 1 / b ≤ 1 / a := one_div_le_one_div_of_le ha hab
    linarith
  have h4 : 0 ≤ 1 + 1 / b := by positivity
  calc Work.Spaces.w b = ((1 + b) / b) ^ 2 := by rw [Work.Spaces.w]; ring_nf
    _ = (1 + 1 / b) ^ 2 := by rw [h1]
    _ ≤ (1 + 1 / a) ^ 2 := pow_le_pow_left₀ h4 h3 2
    _ = ((1 + a) / a) ^ 2 := by rw [h2]
    _ = Work.Spaces.w a := by rw [Work.Spaces.w]; ring_nf


/-! ## The weighted form on the window `[z/2, 3z/2]` -/


end Work.FTS.StrongEps.E5Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.slotIdents.pz_pth_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux.slotIdents

/-- `∂_z ∂_θ` versus the mixed operator: `mixed 1 1 u = D_z(D_θ u) = z · ∂_z(sin(2θ)·∂_θu)`,
and the factor `sin(2θ)` is constant in `z`, so the mixed derivative is `z · sin(2θ) · ∂_z∂_θ u`. -/
theorem pz_pth_eq {u : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ)) (hz : z ≠ 0)
    (hs : Real.sin (2 * θ) ≠ 0) :
    Work.Spaces.pz (Work.Spaces.pth u) z θ
      = Work.Spaces.mixed 1 1 u z θ / (z * Real.sin (2 * θ)) := by
  -- `mixed 1 1 u = Dz (Dth u) = z · ∂_z(D_θ u)` definitionally.
  have hmix : Work.Spaces.mixed 1 1 u z θ
      = z * Work.Spaces.pz (Work.Spaces.Dth u) z θ := rfl
  -- The `θ`-slice factor `sin(2θ)` is constant in `z`, so it comes out of the derivative.
  have h1 : Work.Spaces.pz (Work.Spaces.Dth u) z θ
      = Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth u) z θ := by
    show deriv (fun z' => Real.sin (2 * θ) * Work.Spaces.pth u z' θ) z
      = Real.sin (2 * θ) * deriv (fun z' => Work.Spaces.pth u z' θ) z
    rw [deriv_const_mul_field]
  rw [hmix, h1, eq_div_iff (mul_ne_zero hz hs)]
  ring

end Work.FTS.StrongEps.E5Aux.slotIdents
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.AngFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false

open scoped Real Topology
open MeasureTheory

/-!
Elementary angular facts on `Iθ = [0,π/2]`, `K θ = 3 sin θ cos²θ`, `qfun θ = cos 2θ - 1/3`.

The proofs are direct computations:
* `K ≥ 0` and `cos ≥ 0` on `Iθ` are pointwise positivity;
* `K θ ≤ 2 cos θ` follows from `3 sin θ cos θ ≤ 3/2 ≤ 2` and `cos θ ≥ 0`;
* `∫_{Iθ} cos = 1` is the FTC with primitive `sin`, `∫_{Iθ} K = 1` the FTC with
  primitive `-cos³`;
* `|qfun| ≤ 4/3` is `|cos 2θ - 1/3| ≤ 4/3` from `-1 ≤ cos ≤ 1`;
* `K θ = (3/2) cos θ sin (2θ)` is `Real.sin_two_mul` and `ring`;
* `|sin (2θ)| ≤ 2` is `|sin| ≤ 1`.
-/

/-- The set integral over `Iθ = [0, π/2]` is the interval integral from `0` to `π/2`. -/
private lemma Iθ_setIntegral_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le
      (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]

/-- `cos` is nonnegative on `Iθ`. -/
private lemma cos_nonneg_of_mem_Iθ_prv {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩

/-- `sin` is nonnegative on `Iθ`. -/
private lemma sin_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin θ :=
  Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [Real.pi_pos, hθ.2]⟩

/-- `3 sin θ cos θ ≤ 2` for all `θ` (the maximum of `3 sin θ cos θ` is `3/2`). -/
private lemma three_sin_cos_le_two (θ : ℝ) : 3 * Real.sin θ * Real.cos θ ≤ 2 := by
  have hsq : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have h4 : 4 * Real.sin θ ^ 2 * Real.cos θ ^ 2 ≤ 1 :=
    calc 4 * Real.sin θ ^ 2 * Real.cos θ ^ 2
        = 1 - (Real.sin θ ^ 2 - Real.cos θ ^ 2) ^ 2 := by
          nlinarith [hsq]
      _ ≤ 1 := by linarith [sq_nonneg (Real.sin θ ^ 2 - Real.cos θ ^ 2)]
  have h9 : (3 * Real.sin θ * Real.cos θ) ^ 2 ≤ 4 := by nlinarith [h4]
  nlinarith [h9, sq_nonneg (3 * Real.sin θ * Real.cos θ - 2)]

/-- The angular weight `K` is continuous. -/
private lemma continuous_K_prv : Continuous fun θ : ℝ => Work.Spaces.K θ := by
  rw [show (fun θ : ℝ => Work.Spaces.K θ)
        = fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2 from by
      funext θ; rw [Work.Spaces.K]]
  exact (continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)

/-- `∫_{Iθ} cos θ = 1` (FTC with primitive `sin`). -/
private lemma integral_cos_Iθ_prv : (∫ θ in Work.Spaces.Iθ, Real.cos θ) = 1 := by
  rw [Iθ_setIntegral_eq_intervalIntegral]
  have h : (∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos θ)
      = Real.sin (Real.pi / 2) - Real.sin 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => Real.hasDerivAt_sin x)
      (Real.continuous_cos.intervalIntegrable _ _)
  rw [h, Real.sin_pi_div_two, Real.sin_zero, sub_zero]

/-- `d/dθ (-cos³θ) = K θ`, so `-cos³` is a primitive of `K`. -/
private lemma hasDerivAt_neg_cos_cube_prv (x : ℝ) :
    HasDerivAt (fun t : ℝ => -(Real.cos t) ^ 3) (Work.Spaces.K x) x := by
  have h1 : HasDerivAt (fun t : ℝ => Real.cos t ^ 3)
      (3 * Real.cos x ^ 2 * -Real.sin x) x :=
    (Real.hasDerivAt_cos x).pow 3
  convert h1.neg using 1
  rw [Work.Spaces.K]; ring

/-- `∫_{Iθ} K θ = 1` (FTC with primitive `-cos³`). -/
private lemma integral_K_Iθ : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ) = 1 := by
  rw [Iθ_setIntegral_eq_intervalIntegral]
  have hInt : (∫ θ in (0 : ℝ)..(Real.pi / 2), Work.Spaces.K θ)
      = (fun t : ℝ => -(Real.cos t) ^ 3) (Real.pi / 2)
        - (fun t : ℝ => -(Real.cos t) ^ 3) 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => -(Real.cos t) ^ 3)
      (f' := fun t : ℝ => Work.Spaces.K t) (fun x _ => hasDerivAt_neg_cos_cube_prv x)
      (continuous_K_prv.intervalIntegrable _ _)
  rw [hInt]
  norm_num [Real.cos_pi_div_two, Real.cos_zero]

theorem AngFacts :
    (∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.Spaces.K θ) ∧
    (∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.K θ ≤ 2 * Real.cos θ) ∧
    (∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.cos θ) ∧
    (∫ θ in Work.Spaces.Iθ, Real.cos θ) = 1 ∧
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ) = 1 ∧
    (∀ θ : ℝ, |Work.Spaces.qfun θ| ≤ 4 / 3) ∧
    (∀ θ : ℝ, Work.Spaces.K θ = 3 / 2 * Real.cos θ * Real.sin (2 * θ)) ∧
    (∀ θ ∈ Work.Spaces.Iθ, |Real.sin (2 * θ)| ≤ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `K ≥ 0` on `Iθ`
    intro θ hθ
    have hs := sin_nonneg_of_mem_Iθ hθ
    have hc : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
    rw [Work.Spaces.K]
    exact mul_nonneg (mul_nonneg (by norm_num) hs) hc
  · -- `K θ ≤ 2 cos θ` on `Iθ`
    intro θ hθ
    have hc0 := cos_nonneg_of_mem_Iθ_prv hθ
    have hsc := three_sin_cos_le_two θ
    rw [Work.Spaces.K]
    nlinarith [mul_le_mul_of_nonneg_right hsc hc0]
  · exact fun θ hθ => cos_nonneg_of_mem_Iθ_prv hθ
  · exact integral_cos_Iθ_prv
  · exact integral_K_Iθ
  · -- `|qfun θ| ≤ 4/3`
    intro θ
    rw [Work.Spaces.qfun_apply, abs_le]
    constructor <;> linarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
  · -- `K θ = (3/2) cos θ sin (2θ)`
    intro θ
    rw [Work.Spaces.K, Real.sin_two_mul]
    ring
  · -- `|sin (2θ)| ≤ 2` on `Iθ`
    intro θ _
    linarith [Real.abs_sin_le_one (2 * θ)]

end Work.FTS.StrongEps.E5Aux2
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.abs_Transport_slotMaj_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

theorem abs_Transport_slotMaj_le {f : ℝ → ℝ → ℝ} {Maj : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hslot : ∀ θ : ℝ, |Work.Spaces.mixed 0 1 f z θ| ≤ Maj z) :
    ∀ θ : ℝ, |Work.Coercivity.Transport f z θ| ≤ 3 * Maj z / (1 + z) := by
  intro θ
  -- `Transport f z θ = 3 · D_θ f z θ / (1+z)` and `D_θ f = mixed 0 1 f`, definitionally.
  rw [show Work.Coercivity.Transport f z θ
      = 3 * Work.Spaces.mixed 0 1 f z θ / (1 + z) from rfl]
  have hz1 : (0:ℝ) < 1 + z := by linarith
  rw [abs_div, abs_of_pos hz1, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hslot θ) (by norm_num)) hz1.le

end Work.FTS.StrongEps.E5Aux2
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.LevelK =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

set_option autoImplicit false

/-! ## The weights are `≥ 1` on the region `z > 0`, `sin(2θ) > 0` -/

private lemma one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have hz2 : 0 < z ^ 2 := by positivity
  rw [Work.Spaces.w, one_le_div hz2]
  calc z ^ 2 ≤ (1 + z) ^ 2 := pow_le_pow_left₀ (le_of_lt hz) (by linarith) 2
    _ = (1 + z) ^ 2 := rfl

private lemma one_le_wTheta {α θ : ℝ} (hα : 0 < α) (hsin : 0 < Real.sin (2 * θ)) :
    1 ≤ Work.Spaces.wTheta α θ := by
  have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hexp : -(Work.Spaces.gam α / 2) ≤ 0 := by
    have h := Work.Spaces.gam_pos hα
    linarith
  have h := Real.rpow_le_rpow_of_exponent_ge hsin hsin1 hexp
  rwa [Real.rpow_zero] at h

private lemma one_le_Wt {α z θ : ℝ} (hα : 0 < α) (hz : 0 < z)
    (hsin : 0 < Real.sin (2 * θ)) : 1 ≤ Work.Spaces.Wt α z θ := by
  have h1 : 1 ≤ Work.Spaces.w z := one_le_w_of_pos hz
  have h2 : 1 ≤ Work.Spaces.wTheta α θ := one_le_wTheta hα hsin
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ Work.Spaces.w z * Work.Spaces.wTheta α θ :=
        mul_le_mul h1 h2 zero_le_one (le_trans zero_le_one h1)
    _ = Work.Spaces.Wt α z θ := rfl

private lemma one_le_w_div_sin_eta {z θ : ℝ} (hz : 0 < z) (hsin : 0 < Real.sin (2 * θ)) :
    1 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsin _
  have hsle : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hsin.le hs1 (by norm_num [Work.Spaces.eta])
  rw [one_le_div hspos]
  have h1 : 1 ≤ Work.Spaces.w z := one_le_w_of_pos hz
  linarith

private lemma sq_le_sq_mul_of_one_le {A M : ℝ} (hM : 1 ≤ M) : A ^ 2 ≤ (A * M) ^ 2 := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have h : |A| ≤ |A * M| := by
    rw [abs_mul, abs_of_pos hMpos]
    nlinarith [abs_nonneg A]
  exact sq_le_sq.mpr h

/-! ## A single mixed derivative at level `k` -/

/-- The square of a single mixed derivative `D_z^jD_θ^i F` of order `i + j ≤ k` is dominated
pointwise by the `ℋ^k`-integrand of `F`, on the region `z > 0`, `0 < sin(2θ) ≤ 1`. -/
theorem mixed_sq_le_HkIntegrand_level (α : ℝ) (k : ℕ) (hα : 0 < α) (j i : ℕ) (hji : j + i ≤ k)
    {F : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z) (hsin : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.mixed j i F z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k F z θ := by
  by_cases hi1 : 1 ≤ i
  · have h1 : 1 ≤ Work.Spaces.Wt α z θ := one_le_Wt hα hz hsin
    have h2 : (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k F z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α k F z θ i j hi1 (by omega)
    exact le_trans (sq_le_sq_mul_of_one_le h1) h2
  · have hi0 : i = 0 := by omega
    have h3 : (Work.Spaces.DzIter j F z θ) ^ 2
        ≤ (Work.Spaces.DzIter j F z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 :=
      sq_le_sq_mul_of_one_le (one_le_w_div_sin_eta hz hsin)
    have h4 : (Work.Spaces.DzIter j F z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α k F z θ :=
      Work.Spaces.sq_le_HkIntegrand_z α k F z θ j (by omega)
    have h5 : Work.Spaces.mixed j i F = Work.Spaces.DzIter j F := by
      rw [hi0]
      simp
    rw [h5]
    exact le_trans h3 h4

/-! ## The rectangle integral comparison at level `k` -/

/-- If `g²` is dominated pointwise on the rectangle `[a,b] × [c,d]` (`⊆ (0,∞) × (0,π/2)`) by
`K` times the `ℋ^k`-integrand of `F`, then the iterated integral of `g²` over the rectangle is
dominated by `K` times the squared `ℋ^k`-norm of `F`. -/
theorem rect_integral_le_of_pointwise_level {a b c d K α : ℝ} (k : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hd : d < Real.pi / 2) {F g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k F) (hK : 0 ≤ K)
    (hpt : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (g z θ) ^ 2 ≤ K * Work.Spaces.HkIntegrand α k F z θ) :
    (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (g z θ) ^ 2) ≤ K * Work.Spaces.HkSq α k F := by
  have hsubz : Set.Icc a b ⊆ Work.Spaces.Iz := fun z hz => le_trans ha.le hz.1
  have hsubθ : Set.Icc c d ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_trans hc.le hθ.1, le_trans hθ.2 hd.le⟩
  -- (1) the angular integral at a fixed `z ∈ [a,b]`
  have hinner : ∀ z ∈ Set.Icc a b,
      (∫ θ in Set.Icc c d, (g z θ) ^ 2)
        ≤ K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := hsubz hz
    have hInt : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k F z θ) (Set.Icc c d) :=
      (hmem.1 z hzIz).mono_set hsubθ
    have hInt2 : IntegrableOn
        (fun θ => K * Work.Spaces.HkIntegrand α k F z θ) (Set.Icc c d) := hInt.const_mul _
    have hstep1 : (∫ θ in Set.Icc c d, (g z θ) ^ 2)
        ≤ ∫ θ in Set.Icc c d, K * Work.Spaces.HkIntegrand α k F z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall fun θ => sq_nonneg _) hInt2
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          fun θ hθ => hpt z hz θ hθ)
    have hstep2 : (∫ θ in Set.Icc c d, Work.Spaces.HkIntegrand α k F z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ :=
      setIntegral_mono_set (hmem.1 z hzIz)
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)
        (Eventually.of_forall fun θ hθ => hsubθ hθ)
    calc (∫ θ in Set.Icc c d, (g z θ) ^ 2)
        ≤ ∫ θ in Set.Icc c d, K * Work.Spaces.HkIntegrand α k F z θ := hstep1
      _ = K * ∫ θ in Set.Icc c d, Work.Spaces.HkIntegrand α k F z θ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ :=
          mul_le_mul_of_nonneg_left hstep2 hK
  -- (2) the radial integral
  have houter : (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (g z θ) ^ 2)
      ≤ K * ∫ z in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k F z θ := by
    have hInt : IntegrableOn
        (fun z => K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
        (Set.Icc a b) := (hmem.2.mono_set hsubz).const_mul _
    calc (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (g z θ) ^ 2)
        ≤ ∫ z in Set.Icc a b, K * ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k F z θ :=
          MeasureTheory.integral_mono_of_nonneg
            (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hInt
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
              fun z hz => hinner z hz)
      _ = K * ∫ z in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k F z θ := MeasureTheory.integral_const_mul _ _
  -- (3) enlarging `[a,b]` to `Iz`
  have hlast : (∫ z in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k F z θ) ≤ Work.Spaces.HkSq α k F := by
    rw [Work.Spaces.HkSq]
    exact setIntegral_mono_set hmem.2
      (Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)
      (Eventually.of_forall fun z hz => hsubz hz)
  exact le_trans houter (mul_le_mul_of_nonneg_left hlast hK)

end Work.FTS.StrongEps.E5G
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.SqrtDLocInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsLocalPStar

set_option autoImplicit false

/-- `sin(2σ) ≥ 0` on the angular interval `Iθ = [0,π/2]`. -/
theorem SqrtD_sin_two_nonneg {σ : ℝ} (hσ : σ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * σ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hσ.1], by linarith [hσ.2, Real.pi_pos]⟩

/-- The radial weight is bounded below by `1` on the half-line: `1 ≤ w(u)²` for `u > 0`. -/
theorem SqrtD_one_le_w_sq {u : ℝ} (hu : 0 < u) : 1 ≤ (Work.Spaces.w u) ^ 2 := by
  have h1 : 1 ≤ Work.Spaces.w u := by
    rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg u]
  exact one_le_pow₀ h1

/-- **The pointwise reduction to the `D_θ`-slot of the `ℋ¹`-integrand.**  For `u > 0` and
`σ ∈ Iθ`, the integrand of `D α f u` is dominated by the `(i,j) = (1,0)` summand of
`HkIntegrand α 1 f u ·`. -/
theorem SqrtD_integrand_le_HkIntegrand {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ}
    {u σ : ℝ} (hu : 0 < u) (hσ : σ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 1 f u σ := by
  have hγ0 : Work.Spaces.gam α ≠ 0 := by
    have := Work.Spaces.one_lt_gam hα.1; linarith
  have hγ2 : Work.Spaces.gam α ≠ 2 := by
    intro h; linarith [Work.Spaces.gam_sub_one α, hα.2, h]
  have hs : 0 ≤ Real.sin (2 * σ) := SqrtD_sin_two_nonneg hσ
  have hw : 1 ≤ (Work.Spaces.w u) ^ 2 := SqrtD_one_le_w_sq hu
  -- `sin(2σ)^{2-γ} = sin(2σ)² · sin(2σ)^{-γ}`
  have h1 : (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
    have h : (2 : ℝ) + (-(Work.Spaces.gam α)) ≠ 0 := by
      intro hh; exact hγ2 (by linarith)
    calc (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        = (Real.sin (2 * σ)) ^ ((2 : ℝ) + (-(Work.Spaces.gam α))) := rfl
      _ = (Real.sin (2 * σ)) ^ (2 : ℝ) * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
            Real.rpow_add' hs h
      _ = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
            rw [Real.rpow_two]
  -- `sin(2σ)^{-γ} = (sin(2σ)^{-γ/2})²`
  have h2 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      = ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
    have h : (-(Work.Spaces.gam α / 2)) + (-(Work.Spaces.gam α / 2)) ≠ 0 := by
      intro hh; exact hγ0 (by linarith)
    calc (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        = (Real.sin (2 * σ)) ^ ((-(Work.Spaces.gam α / 2)) + (-(Work.Spaces.gam α / 2))) := by
            ring_nf
      _ = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2))
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2)) := Real.rpow_add' hs h
      _ = ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by ring
  -- expansion of the `HkIntegrand`-summand as `sin(2σ)^{2-γ}(∂_θf)² · w(u)²`
  have hsq : (Work.Spaces.mixed 0 1 f u σ * Work.Spaces.Wt α u σ) ^ 2
      = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.pth f u σ) ^ 2 * (Work.Spaces.w u) ^ 2 := by
    rw [h2]
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, Work.Spaces.Dth, Work.Spaces.Wt, Work.Spaces.wTheta]
    ring
  refine le_trans ?_ (Work.Spaces.sq_le_HkIntegrand_mixed α 1 f u σ 1 0 le_rfl (by norm_num))
  calc (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2
      = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.pth f u σ) ^ 2 := by rw [h1]
    _ ≤ (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.pth f u σ) ^ 2 * (Work.Spaces.w u) ^ 2 :=
        le_mul_of_one_le_right
          (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)) (sq_nonneg _)) hw
    _ = (Work.Spaces.mixed 0 1 f u σ * Work.Spaces.Wt α u σ) ^ 2 := hsq.symm

theorem SqrtDLocInt {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α 1 f) {a b : ℝ} (ha : 0 < a) :
    ∫⁻ u in Set.Icc a b, ENNReal.ofReal (Real.sqrt (∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2)) < ⊤ := by
  -- Step 1: the `σ`-integral of the integrand is dominated by `F(u) = ∫ HkIntegrand α 1 f u`.
  have hDle : ∀ u ∈ Set.Ioi (0 : ℝ),
      (∫ σ in Work.Spaces.Iθ,
          (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2)
        ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f u σ := by
    intro u hu
    have hu0 : 0 < u := Set.mem_Ioi.mp hu
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hm.1 u (le_of_lt hu0)) ?_
    · exact MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun σ hσ => mul_nonneg (Real.rpow_nonneg (SqrtD_sin_two_nonneg hσ) _) (sq_nonneg _))
    · exact MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun σ hσ => SqrtD_integrand_le_HkIntegrand hα hu0 hσ)
  -- Step 2: `u ↦ F(u) + 1` is integrable on the compact interval `[a,b] ⊆ (0,∞)`.
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := fun u hu => le_of_lt (lt_of_lt_of_le ha hu.1)
  have hFint : MeasureTheory.IntegrableOn
      (fun u => ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f u σ) (Set.Icc a b) :=
    hm.2.mono_set hsub
  have hvol : MeasureTheory.volume (Set.Icc a b) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have h1int : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
    MeasureTheory.integrableOn_const (ne_of_lt hvol)
  have hH : MeasureTheory.IntegrableOn
      (fun u => (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f u σ) + 1)
      (Set.Icc a b) :=
    hFint.add h1int
  -- Step 3: pointwise `√(D α f u) ≤ F(u) + 1` on `[a,b]`, hence the lintegral bound.
  refine lt_of_le_of_lt ?_ hH.setLIntegral_lt_top
  refine MeasureTheory.lintegral_mono_ae ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet (Set.Icc a b) from measurableSet_Icc) (fun u hu => ?_)
  have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
  have hFnn : 0 ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f u σ :=
    integral_nonneg (fun σ => Work.Spaces.HkIntegrand_nonneg α 1 f u σ)
  have hle : Real.sqrt (∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2)
      ≤ (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f u σ) + 1 := by
    rw [Real.sqrt_le_left (by linarith)]
    have h1 := hDle u (Set.mem_Ioi.mpr hu0)
    nlinarith [sq_nonneg ((∫ σ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 1 f u σ) + 1 / 2)]
  exact ENNReal.ofReal_le_ofReal hle

end Work.FTS.StrongEps.EpsLocalPStar
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceThetaStep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsLocalPStar

/-! ## Step: from the pointwise trace rate at `θ = 0⁺` to the `L²` bound

The pointwise hypothesis of `TraceThetaStep` says that on `(0, π/4)` the slice `u` is close to
`m` at the rate `sin(2θ)^{(γ-1)/2}`.  On that interval `sin(2θ)^{-η} ≥ 1`, so the weighted
integral of `u` over `(0, π/4)` controls `m²`: from `m² ≤ 2u² + 2(u-m)²` we get

`(m²/2) ∫_{(0,π/4)} sin^{-η} ≤ ∫_{Iθ} u² sin^{-η} + (100/(γ-1)) A ∫_{(0,π/4)} sin^{γ-1-η}`,

and since `sin ≤ 1` on `(0,π/4)` (so `∫ sin^{γ-1-η} ≤ ∫ sin^{-η}`) and
`∫_{(0,π/4)} sin^{-η} ≥ π/4`, division by the weight integral gives the stated constants. -/

/-- Integrability of `θ ↦ sin(2θ)^p` on `(0, π/4)` for every `p > -1`. -/
private theorem tsIntegrableSinPow {p : ℝ} (hp : -1 < p) :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (Set.Ioo (0 : ℝ) (Real.pi / 4)) := by
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 4) ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
  by_cases hp0 : p ≤ 0
  · exact ((Work.Spaces.sin_two_rpow p hp hp0).1).mono_set hsub
  · have hp0' : 0 < p := not_le.mp hp0
    refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => (1 : ℝ)) ?_ ?_ ?_
    · simp
    · exact ((Measurable.pow_const (Real.measurable_sin.comp
        (measurable_const.mul measurable_id)) p)).aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hsin0 : 0 ≤ Real.sin (2 * θ) :=
        le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))
      have hnorm : ‖(Real.sin (2 * θ)) ^ p‖ ≤ (1 : ℝ) := by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg hsin0 p)]
        exact Real.rpow_le_one hsin0 (Real.sin_le_one _) (le_of_lt hp0')
      simpa using hnorm

/-- On `(0, π/2)` the weight `sin(2θ)^{-η}` is at least `1`. -/
private theorem tsOneLe {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_nonpos hsin hle
    (show -(Work.Spaces.eta) ≤ 0 by linarith [Work.Spaces.eta_pos])
  rwa [Real.one_rpow] at h

/-- The weighted length of `(0, π/4)` is at least `π/4`. -/
private theorem tsPiDivFourLe :
    Real.pi / 4 ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hInt : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
    tsIntegrableSinPow (p := -(Work.Spaces.eta)) (by linarith [Work.Spaces.eta_lt_one])
  have hInt1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo (0 : ℝ) (Real.pi / 4)) := by
    simp
  have hmono : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), (1 : ℝ))
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    integral_mono_ae hInt1 hInt
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun θ hθ => tsOneLe hθ.1 (by linarith [hθ.2, Real.pi_pos])))
  have hconst : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4), (1 : ℝ)) = Real.pi / 4 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), smul_eq_mul, mul_one]
    ring
  linarith [hmono, hconst]

theorem TraceThetaStep {γ m A : ℝ} {u : ℝ → ℝ}
    (hγ : 1 < γ) (hA : 0 ≤ A)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) Work.Spaces.Iθ)
    (hpt : ∀ θ ∈ Set.Ioo 0 (π/4), (u θ - m)^2 ≤ 100/(γ-1) * (Real.sin (2*θ))^(γ-1) * A) :
    m^2 ≤ 200/(γ-1) * A + 8/Real.pi * (∫ θ in Work.Spaces.Iθ,
        (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) := by
  have hγ1 : 0 < γ - 1 := by linarith
  have hγ10 : (0 : ℝ) ≤ 100 / (γ - 1) := by positivity
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 4) ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
  set K : ℝ := ∫ θ in Work.Spaces.Iθ,
    (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta) with hK
  set J0 : ℝ := ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
    (Real.sin (2*θ))^(-Work.Spaces.eta) with hJ
  have hIntU : IntegrableOn (fun θ : ℝ => (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta))
      (Set.Ioo (0 : ℝ) (Real.pi / 4)) := hint.mono_set hsub
  have hIntS : IntegrableOn (fun θ : ℝ => (Real.sin (2*θ))^(-Work.Spaces.eta))
      (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
    tsIntegrableSinPow (p := -(Work.Spaces.eta)) (by linarith [Work.Spaces.eta_lt_one])
  have hIntExp : IntegrableOn (fun θ : ℝ => (Real.sin (2*θ))^(γ-1-Work.Spaces.eta))
      (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
    tsIntegrableSinPow (p := γ - 1 - Work.Spaces.eta) (by linarith [Work.Spaces.eta_lt_one])
  -- the pointwise inequality `m²/2 · s ≤ u² · s + (100/(γ-1)) A sin^{γ-1-η}`
  have hpoint : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 4))),
      (m^2/2) * (Real.sin (2*θ))^(-Work.Spaces.eta)
        ≤ (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)
          + (100/(γ-1))*A*((Real.sin (2*θ))^(γ-1-(Work.Spaces.eta))) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hsin : 0 < Real.sin (2*θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hsnn : 0 ≤ (Real.sin (2*θ))^(-Work.Spaces.eta) := Real.rpow_nonneg hsin.le _
    have hkey : m^2/2 ≤ (u θ)^2 + (100/(γ-1)) * (Real.sin (2*θ))^(γ-1) * A := by
      have hms : m^2 ≤ 2*(u θ)^2 + 2*(u θ - m)^2 := by nlinarith [sq_nonneg (2*u θ - m)]
      have hp := hpt θ hθ
      linarith
    have hrw : (Real.sin (2*θ))^(γ-1) * (Real.sin (2*θ))^(-Work.Spaces.eta)
        = (Real.sin (2*θ))^(γ-1-Work.Spaces.eta) := by
      rw [← Real.rpow_add hsin]
      ring_nf
    have h2 := mul_le_mul_of_nonneg_right hkey hsnn
    have heq : ((u θ)^2 + (100/(γ-1)) * (Real.sin (2*θ))^(γ-1) * A)
          * (Real.sin (2*θ))^(-Work.Spaces.eta)
        = (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)
          + (100/(γ-1))*A*((Real.sin (2*θ))^(γ-1-Work.Spaces.eta)) := by
      rw [add_mul, ← hrw]; ring
    rwa [heq] at h2
  have hF : IntegrableOn (fun θ : ℝ => (m^2/2) * (Real.sin (2*θ))^(-Work.Spaces.eta))
      (Set.Ioo (0 : ℝ) (Real.pi / 4)) := MeasureTheory.Integrable.const_mul hIntS (m^2/2)
  have hG : IntegrableOn (fun θ : ℝ => (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)
      + (100/(γ-1))*A*((Real.sin (2*θ))^(γ-1-Work.Spaces.eta)))
      (Set.Ioo (0 : ℝ) (Real.pi / 4)) :=
    hIntU.add (MeasureTheory.Integrable.const_mul hIntExp ((100/(γ-1))*A))
  have hmono := integral_mono_ae hF hG hpoint
  rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add hIntU (MeasureTheory.Integrable.const_mul hIntExp _),
      MeasureTheory.integral_const_mul, ← hJ] at hmono
  -- comparison of the two integrals with their `Iθ`-counterparts
  have hA1 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
      (u θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) ≤ K := by
    rw [hK]
    refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])) _)
    · exact Filter.Eventually.of_forall hsub
  have hA2 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 4),
      (Real.sin (2*θ))^(γ-1-Work.Spaces.eta)) ≤ J0 := by
    rw [hJ]
    refine integral_mono_ae hIntExp hIntS ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hsin : 0 < Real.sin (2*θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hle : (Real.sin (2*θ))^(γ-1-Work.Spaces.eta)
        ≤ (Real.sin (2*θ))^(-Work.Spaces.eta) := by
      rw [show γ - 1 - Work.Spaces.eta = (-Work.Spaces.eta) + (γ - 1) by ring,
        Real.rpow_add hsin]
      exact mul_le_of_le_one_right (Real.rpow_nonneg hsin.le _)
        (Real.rpow_le_one hsin.le (Real.sin_le_one _) (by linarith))
    exact hle
  have hmain : (m^2/2) * J0 ≤ K + (100/(γ-1))*A*J0 := by
    have hcoef : 0 ≤ (100/(γ-1))*A := mul_nonneg hγ10 hA
    have h3 := mul_le_mul_of_nonneg_left hA2 hcoef
    linarith [hmono, hA1, h3]
  have hJge : Real.pi / 4 ≤ J0 := by rw [hJ]; exact tsPiDivFourLe
  have hJpos : 0 < J0 := by linarith [hJge, Real.pi_pos]
  have hKnn : 0 ≤ K := by
    rw [hK]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])) _)
  have hJne : J0 ≠ 0 := ne_of_gt hJpos
  have h1 : m^2/2 ≤ K/J0 + 100/(γ-1)*A := by
    have hdiv : (m^2/2)*J0/J0 ≤ (K + (100/(γ-1))*A*J0)/J0 :=
      div_le_div_of_nonneg_right hmain hJpos.le
    rw [mul_div_assoc, div_self hJne, mul_one] at hdiv
    have hrhs : (K + (100/(γ-1))*A*J0)/J0 = K/J0 + 100/(γ-1)*A := by
      field_simp
    linarith [hdiv, hrhs.le, hrhs.ge]
  have hbnd : K/J0 ≤ (4/Real.pi) * K := by
    have hpi4 : 0 < Real.pi/4 := by linarith [Real.pi_pos]
    have hinv : J0⁻¹ ≤ (Real.pi/4)⁻¹ := inv_anti₀ hpi4 hJge
    have h4 : K/J0 = K * J0⁻¹ := by rw [div_eq_mul_inv]
    rw [h4]
    calc K * J0⁻¹ ≤ K * (Real.pi/4)⁻¹ := mul_le_mul_of_nonneg_left hinv hKnn
      _ = (4/Real.pi) * K := by rw [inv_div]; ring
  have h5 : m^2/2 ≤ (4/Real.pi)*K + 100/(γ-1)*A := by linarith [h1, hbnd]
  have h6 : m^2 ≤ (8/Real.pi)*K + 200/(γ-1)*A := by
    calc m^2 = 2*(m^2/2) := by ring
      _ ≤ 2*((4/Real.pi)*K + 100/(γ-1)*A) := mul_le_mul_of_nonneg_left h5 (by norm_num)
      _ = (8/Real.pi)*K + 200/(γ-1)*A := by ring
  have h7 : (8/Real.pi)*K + 200/(γ-1)*A = 200/(γ-1)*A + 8/Real.pi*K := by ring
  exact h6.trans h7.le

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.WlInfMem_Dth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary facts about `D_θ` and the angular weight

The level shift `WlInfMem α (l+1) f → WlInfMem α l (D_θ f)` hinges on two elementary
observations, recorded here before the main theorem:

* `DthIter j (D_θ f) = DthIter (j+1) f`, so every angular slot of the level-`l` norm of
  `D_θ f` is *literally* a slot of the level-`(l+1)` norm of `f`;
* the angular weight of the level-`(l+1)` norm, `sin(2θ)^{-α/5}/(α + sin 2θ)`, dominates
  `1/(α+1)` on `Iθ`, because `sin(2θ)^{α/5}(α + sin 2θ) ≤ α + 1` there.  Since the plain
  `z`-slots of the level-`l` norm of `D_θ f` are the *unweighted* versions of the `j = 1`
  slots of `f`, this is exactly the constant `(α+1)` of the statement.
-/

/-- `D_θ^j (D_θ f) = D_θ^{j+1} f`. -/
theorem DthIter_Dth (f : ℝ → ℝ → ℝ) :
    ∀ j : ℕ, Work.Spaces.DthIter j (Work.Spaces.Dth f) = Work.Spaces.DthIter (j + 1) f
  | 0 => rfl
  | j + 1 => by
      show Work.Spaces.Dth (Work.Spaces.DthIter j (Work.Spaces.Dth f))
        = Work.Spaces.DthIter (j + 1 + 1) f
      rw [DthIter_Dth f j]
      rfl

/-- `sin(2θ) ≥ 0` on the angular interval `[0, π/2]`. -/
theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

/-- On `Iθ` the inverse angular weight is at most `α+1`:
`sin(2θ)^{α/5} (α + sin 2θ) ≤ α + 1`. -/
theorem weight_mul_le {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) ^ (α / 5) * (α + Real.sin (2 * θ)) ≤ α + 1 := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h1 : Real.sin (2 * θ) ^ (α / 5) ≤ 1 := Real.rpow_le_one hs0 hs1 (by linarith)
  calc Real.sin (2 * θ) ^ (α / 5) * (α + Real.sin (2 * θ))
      ≤ 1 * (α + 1) := mul_le_mul h1 (by linarith) (by linarith) (by norm_num)
    _ = α + 1 := one_mul _

/-- The inverse of the angular weight at `θ`, when `sin(2θ) > 0`. -/
theorem weight_key {α θ : ℝ} (hα : 0 < α) (_hθ : θ ∈ Work.Spaces.Iθ)
    (hs : 0 < Real.sin (2 * θ)) :
    ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      * ((Real.sin (2 * θ)) ^ (α / 5) * (α + Real.sin (2 * θ))) = 1 := by
  have hαs : α + Real.sin (2 * θ) ≠ 0 := by linarith
  rw [div_eq_mul_inv]
  rw [show (Real.sin (2 * θ)) ^ (-(α / 5)) * (α + Real.sin (2 * θ))⁻¹
        * ((Real.sin (2 * θ)) ^ (α / 5) * (α + Real.sin (2 * θ)))
      = ((Real.sin (2 * θ)) ^ (-(α / 5)) * (Real.sin (2 * θ)) ^ (α / 5))
        * ((α + Real.sin (2 * θ))⁻¹ * (α + Real.sin (2 * θ))) from by ring]
  rw [← Real.rpow_add hs, inv_mul_cancel₀ hαs, mul_one]
  have hexp : -(α / 5) + α / 5 = 0 := by ring
  rw [hexp, Real.rpow_zero]

/-- **Pointwise form of the weight bound.**  If `g` vanishes wherever `sin(2θ) = 0`, then on
`Iθ` the plain value `g z θ` is at most `(α+1)` times its weighted version
`g z θ · sin(2θ)^{-α/5}/(α + sin 2θ)`.  Indeed on `Iθ` the weight is `≥ 1/(α+1)`. -/
theorem abs_le_mul_abs_weight {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hzero : ∀ z θ, Real.sin (2 * θ) = 0 → g z θ = 0)
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |g z θ| ≤ (α + 1) * |g z θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  rcases eq_or_lt_of_le hs0 with hs | hs
  · rw [← hs, hzero z θ hs.symm]; simp
  · have hαs : 0 < α + Real.sin (2 * θ) := by linarith
    have hkey := weight_key hα hθ hs
    have hc : g z θ = (g z θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        * ((Real.sin (2 * θ)) ^ (α / 5) * (α + Real.sin (2 * θ))) := by
      rw [show g z θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
          = g z θ * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) from by ring]
      rw [mul_assoc, hkey, mul_one]
    have hc2 : |g z θ| = |g z θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
        * ((Real.sin (2 * θ)) ^ (α / 5) * (α + Real.sin (2 * θ))) := by
      conv_lhs => rw [hc]
      rw [abs_mul, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hs0 _) (le_of_lt hαs))]
    rw [hc2]
    calc |g z θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
          * ((Real.sin (2 * θ)) ^ (α / 5) * (α + Real.sin (2 * θ)))
        ≤ |g z θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| * (α + 1) :=
          mul_le_mul_of_nonneg_left (weight_mul_le hα hθ) (abs_nonneg _)
      _ = (α + 1) * |g z θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| := by ring

/-- One `D_θ`-derivative costs one level of the `𝒲`-norm, with the explicit constant `(α+1)`.

For `0 < α ≤ 1` and `WlInfMem α (l+1) f`, both `WlInfMem α l (Dth f)` and
`WlInf α l (Dth f) ≤ (α + 1) · WlInf α (l+1) f` hold.  Indeed `DthIter j (Dth f) = DthIter (j+1) f`
definitionally, so every angular slot of `WlInf α l (Dth f)` is literally a slot of
`WlInf α (l+1) f`; the only difference is that the level-`l` norm lists the *unweighted*
suprema `(z+1)^k ∂_z^k (Dth f)`, while the level-`(l+1)` norm prices `Dth f` only through the
weighted slot with weight `sin(2θ)^{-α/5}/(α+sin 2θ)`.  The inverse weight
`sin(2θ)^{α/5}(α+sin 2θ)` is bounded by `α+1` on `Iθ` (`sin 2θ ≤ 1`, and `sin(2θ) = 0` implies
`DthIter j f z θ = 0`, so the endpoints are harmless). -/
theorem WlInfMem_Dth {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {l : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.WlInfMem α (l + 1) f) :
    Work.Spaces.WlInfMem α l (Work.Spaces.Dth f) ∧
      Work.Spaces.WlInf α l (Work.Spaces.Dth f)
        ≤ (α + 1) * Work.Spaces.WlInf α (l + 1) f := by
  have hzeroD : ∀ (k : ℕ) (z θ : ℝ), Real.sin (2 * θ) = 0 →
      (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ = 0 := by
    intro k z θ hθ
    have h1 : Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ = 0 :=
      Work.Spaces.pzIter_DthIter_eq_zero_of_sin_eq_zero f 0 hθ k z
    rw [h1, mul_zero]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- the plain `z`-slots of the level-`l` norm of `D_θ f`
    intro k hk
    refine ⟨(α + 1) * Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
        * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))), ?_⟩
    rintro y ⟨z, hz, θ, hθ, rfl⟩
    have hfin : Work.Spaces.SupFinite (fun z θ => (z + 1) ^ k
        * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
      h.2 1 (by omega) k (by omega) (le_refl 1) (by omega)
    have h2 : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
        ≤ Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
          * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
      Work.Spaces.abs_le_supAbs hz hθ hfin
    refine le_trans (abs_le_mul_abs_weight hα
      (g := fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ)
      (fun z θ hs => hzeroD k z θ hs) hθ) ?_
    exact mul_le_mul_of_nonneg_left h2 (by linarith)
  · -- the weighted angular slots of `D_θ f` are the `j = 1` slots of `f`
    intro j hj k hk hj1 hjk
    simp only [DthIter_Dth f]
    exact h.2 (j + 1) (by omega) k (by omega) (by omega) (by omega)
  · -- the norm inequality
    change ((∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs (fun z θ =>
            (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ))
          + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
              (if 1 ≤ j ∧ k + j ≤ l then Work.Spaces.supAbs (fun z θ =>
                (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (Work.Spaces.Dth f)) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0))
        ≤ (α + 1) * ((∑ k ∈ Finset.range (l + 2), Work.Spaces.supAbs (fun z θ =>
            (z + 1) ^ k * Work.Spaces.pzIter k f z θ))
          + ∑ j ∈ Finset.range (l + 2), ∑ k ∈ Finset.range (l + 2),
              (if 1 ≤ j ∧ k + j ≤ l + 1 then Work.Spaces.supAbs (fun z θ =>
                (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0))
    -- replace `D_θ^j (D_θ f)` by `D_θ^{j+1} f` in the angular sum
    simp only [DthIter_Dth f]
    set SD := (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs (fun z θ =>
      (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ)) with hSDdef
    set TD := (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
      (if 1 ≤ j ∧ k + j ≤ l then Work.Spaces.supAbs (fun z θ =>
        (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter (j + 1) f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0)) with hTDdef
    set SF := (∑ k ∈ Finset.range (l + 2), Work.Spaces.supAbs (fun z θ =>
      (z + 1) ^ k * Work.Spaces.pzIter k f z θ)) with hSFdef
    set TF := (∑ j ∈ Finset.range (l + 2), ∑ k ∈ Finset.range (l + 2),
      (if 1 ≤ j ∧ k + j ≤ l + 1 then Work.Spaces.supAbs (fun z θ =>
        (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0)) with hTFdef
    -- each plain `z`-slot of `D_θ f` is dominated by the `j = 1` weighted slot of `f`
    have hslot : ∀ k ≤ l, Work.Spaces.supAbs (fun z θ =>
        (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ)
        ≤ (α + 1) * Work.Spaces.supAbs (fun z θ =>
          (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter 1 f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
      intro k hk
      refine Work.Spaces.supAbs_le (fun z hz θ hθ => ?_)
      have hfin : Work.Spaces.SupFinite (fun z θ => (z + 1) ^ k
          * Work.Spaces.pzIter k (Work.Spaces.DthIter 1 f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
        h.2 1 (by omega) k (by omega) (le_refl 1) (by omega)
      have h2 : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
          ≤ Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (Work.Spaces.DthIter 1 f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
        Work.Spaces.abs_le_supAbs hz hθ hfin
      refine le_trans (abs_le_mul_abs_weight hα
        (g := fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.Dth f) z θ)
        (fun z θ hs => hzeroD k z θ hs) hθ) ?_
      exact mul_le_mul_of_nonneg_left h2 (by linarith)
    have hSD : SD ≤ (α + 1) * (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs
        (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter 1 f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by
      rw [hSDdef, Finset.mul_sum]
      exact Finset.sum_le_sum fun k hk => hslot k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    have hSFnn : 0 ≤ SF := by
      rw [hSFdef]
      exact Finset.sum_nonneg fun k hk =>
        Work.Spaces.supAbs_nonneg (h.1 k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    have hTDnn : 0 ≤ TD := by
      rw [hTDdef]
      refine Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun k hk => ?_
      have hj' : j < l + 1 := Finset.mem_range.mp hj
      have hk' : k < l + 1 := Finset.mem_range.mp hk
      by_cases hc : 1 ≤ j ∧ k + j ≤ l
      · rw [ite_eq_left hc]
        exact Work.Spaces.supAbs_nonneg
          (h.2 (j + 1) (by omega) k (by omega) (by omega) (by omega))
      · rw [ite_eq_right hc]
    -- the `j = 1` slots of `f` together with the shifted slots form the angular part of `f`
    have hid' : (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs
        (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter 1 f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) + TD = TF := by
      rw [hTDdef, hTFdef]
      exact WlInfDthAux.sum_shift_identity (fun j k => Work.Spaces.supAbs (fun z θ =>
        (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) l
    rw [← hid']
    set E := (∑ k ∈ Finset.range (l + 1), Work.Spaces.supAbs
        (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter 1 f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) with hEdef
    have hSD' : SD ≤ (α + 1) * E := by rw [hEdef]; exact hSD
    have hgrow : TD ≤ (α + 1) * TD := le_mul_of_one_le_left hTDnn (by linarith)
    calc SD + TD
        ≤ (α + 1) * E + TD := by linarith [hSD']
      _ ≤ (α + 1) * E + (α + 1) * TD := by linarith [hgrow]
      _ = (α + 1) * (E + TD) := by rw [mul_add]
      _ ≤ (α + 1) * (SF + (E + TD)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hSFnn) (by linarith)

end Work.FTS.StrongEps.H5
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.WlInfMem_mono =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5

set_option autoImplicit false

/-! ## Two `Finset` lemmas comparing sums over `range m` with sums over `range n`, `m ≤ n`

Both sums in `Work.Spaces.WlInf` are sums over `Finset.range (l + 1)` of terms that are
manifestly nonnegative once the corresponding `SupFinite` slots are available.  Enlarging the
range therefore only adds nonnegative terms. -/

/-- A sum over `range m` of a nonnegative summand is at most the sum over the larger
`range n` (`m ≤ n`). -/
private theorem range_sum_le_range_sum {A : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n)
    (hA : ∀ k ∈ Finset.range n, 0 ≤ A k) :
    ∑ k ∈ Finset.range m, A k ≤ ∑ k ∈ Finset.range n, A k :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hmn)
    (fun k hk _ => hA k hk)

/-- The two-dimensional version of `range_sum_le_range_sum`: a double sum over the smaller
rectangle `range m × range m` is at most the double sum over `range n × range n`. -/
private theorem range_sum₂_le {B : ℕ → ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n)
    (hB : ∀ j ∈ Finset.range n, ∀ k ∈ Finset.range n, 0 ≤ B j k) :
    ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, B j k
      ≤ ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, B j k := by
  have h1 : ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, B j k
      ≤ ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range n, B j k :=
    Finset.sum_le_sum fun j hj =>
      range_sum_le_range_sum hmn (fun k hk =>
        hB j (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hmn)) k hk)
  refine h1.trans ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hmn) ?_
  intro j hj _
  exact Finset.sum_nonneg fun k hk => hB j hj k hk

/-- The angular double sum of `WlInf`: replacing the truncation level `l'` by a larger `l`
only weakens the truncation condition `1 ≤ j ∧ k + j ≤ m`, and enlarging the two ranges adds
nonnegative terms. -/
private theorem angular_sum_le {C : ℕ → ℕ → ℝ} {l l' : ℕ} (hll : l' ≤ l)
    (hC : ∀ j ≤ l, ∀ k ≤ l, 1 ≤ j → k + j ≤ l → 0 ≤ C j k) :
    (∑ j ∈ Finset.range (l' + 1), ∑ k ∈ Finset.range (l' + 1),
        if 1 ≤ j ∧ k + j ≤ l' then C j k else 0)
      ≤ ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        if 1 ≤ j ∧ k + j ≤ l then C j k else 0 := by
  -- termwise comparison of the two `if`s
  have hpt : ∀ j ≤ l', ∀ k ≤ l',
      (if 1 ≤ j ∧ k + j ≤ l' then C j k else 0)
        ≤ (if 1 ≤ j ∧ k + j ≤ l then C j k else 0) := by
    intro j hj k hk
    by_cases hc : 1 ≤ j ∧ k + j ≤ l'
    · have hc' : 1 ≤ j ∧ k + j ≤ l := ⟨hc.1, le_trans hc.2 hll⟩
      rw [if_pos hc, if_pos hc']
    · rw [if_neg hc]
      by_cases hc' : 1 ≤ j ∧ k + j ≤ l
      · rw [if_pos hc']
        exact hC j (le_trans hj hll) k (le_trans hk hll) hc'.1 hc'.2
      · rw [if_neg hc']
  have h1 : (∑ j ∈ Finset.range (l' + 1), ∑ k ∈ Finset.range (l' + 1),
        if 1 ≤ j ∧ k + j ≤ l' then C j k else 0)
      ≤ ∑ j ∈ Finset.range (l' + 1), ∑ k ∈ Finset.range (l' + 1),
        if 1 ≤ j ∧ k + j ≤ l then C j k else 0 :=
    Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk =>
      hpt j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
        k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  refine h1.trans ?_
  refine range_sum₂_le (Nat.succ_le_succ hll) ?_
  intro j hj k hk
  by_cases hc : 1 ≤ j ∧ k + j ≤ l
  · rw [if_pos hc]
    exact hC j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hc.1 hc.2
  · rw [if_neg hc]

/-- `WlInfMem` and the `𝒲^{l,∞}`-norm are monotone in the order: from `WlInfMem α l f` and
`l' ≤ l`, both the memory statement `WlInfMem α l' f` and the inequality `WlInf α l' f ≤ WlInf α l f`
follow.  (The slots of `WlInf α l' f` are a subset of those of `WlInf α l f`, and `WlInfMem α l f`
makes all the `sSup`s honest.) -/
theorem WlInfMem_mono {α : ℝ} {l l' : ℕ} (hll : l' ≤ l) {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.WlInfMem α l f) :
    Work.Spaces.WlInfMem α l' f ∧ Work.Spaces.WlInf α l' f ≤ Work.Spaces.WlInf α l f := by
  constructor
  · exact ⟨fun k hk => h.1 k (le_trans hk hll),
      fun j hj k hk hj1 hjk => h.2 j (le_trans hj hll) k (le_trans hk hll) hj1 (le_trans hjk hll)⟩
  · simp only [Work.Spaces.WlInf]
    refine add_le_add ?_ ?_
    · exact range_sum_le_range_sum (Nat.succ_le_succ hll) (fun k hk =>
        Work.Spaces.supAbs_nonneg (h.1 k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))))
    · exact angular_sum_le hll (fun j hj k hk hj1 hjk =>
        Work.Spaces.supAbs_nonneg (h.2 j hj k hk hj1 hjk))

end Work.FTS.StrongEps.H5
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.mixed_sq_le_HkIntegrand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-! ## The weight bounds on the region `z > 0`, `sin(2θ) > 0` -/

/-- `w(z) = (1+z)²/z² ≥ 1` for `z > 0`. -/
private lemma one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have hz2 : 0 < z ^ 2 := by positivity
  rw [Work.Spaces.w, one_le_div hz2]
  calc z ^ 2 ≤ (1 + z) ^ 2 := pow_le_pow_left₀ (le_of_lt hz) (by linarith) 2
    _ = (1 + z) ^ 2 := rfl

/-- `w_θ(θ) = sin(2θ)^{-γ/2} ≥ 1` for `0 < sin(2θ) ≤ 1` and `γ = gam α ≥ 0`. -/
private lemma one_le_wTheta {α θ : ℝ} (hα : 0 < α) (hsin : 0 < Real.sin (2 * θ)) :
    1 ≤ Work.Spaces.wTheta α θ := by
  have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hexp : -(Work.Spaces.gam α / 2) ≤ 0 := by
    have h := Work.Spaces.gam_pos hα
    linarith
  have h := Real.rpow_le_rpow_of_exponent_ge hsin hsin1 hexp
  rwa [Real.rpow_zero] at h

/-- The product weight `W = w·w_θ` is `≥ 1`: both factors are. -/
private lemma one_le_Wt {α z θ : ℝ} (hα : 0 < α) (hz : 0 < z)
    (hsin : 0 < Real.sin (2 * θ)) : 1 ≤ Work.Spaces.Wt α z θ := by
  have h1 : 1 ≤ Work.Spaces.w z := one_le_w_of_pos hz
  have h2 : 1 ≤ Work.Spaces.wTheta α θ := one_le_wTheta hα hsin
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ Work.Spaces.w z * Work.Spaces.wTheta α θ :=
        mul_le_mul h1 h2 zero_le_one (le_trans zero_le_one h1)
    _ = Work.Spaces.Wt α z θ := rfl

/-- The `η`-weight `w(z)/sin(2θ)^{η/2}` is `≥ 1`. -/
private lemma one_le_w_div_sin_eta {z θ : ℝ} (hz : 0 < z) (hsin : 0 < Real.sin (2 * θ)) :
    1 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsin _
  have hsle : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hsin.le hs1 (by norm_num [Work.Spaces.eta])
  rw [one_le_div hspos]
  have h1 : 1 ≤ Work.Spaces.w z := one_le_w_of_pos hz
  linarith

/-- If `1 ≤ M` then `A² ≤ (A·M)²`. -/
private lemma sq_le_sq_mul_of_one_le {A M : ℝ} (hM : 1 ≤ M) : A ^ 2 ≤ (A * M) ^ 2 := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have h : |A| ≤ |A * M| := by
    rw [abs_mul, abs_of_pos hMpos]
    nlinarith [abs_nonneg A]
  exact sq_le_sq.mpr h

/-! ## The lemma -/

theorem mixed_sq_le_HkIntegrand (α : ℝ) (hα : 0 < α) (j i : ℕ) (hji : j + i ≤ 6)
    {F : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z) (hsin : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.mixed j i F z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 F z θ := by
  by_cases hi1 : 1 ≤ i
  · have h1 : 1 ≤ Work.Spaces.Wt α z θ := one_le_Wt hα hz hsin
    have h2 : (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 F z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 6 F z θ i j hi1 (by omega)
    exact le_trans (sq_le_sq_mul_of_one_le h1) h2
  · have hi0 : i = 0 := by omega
    have h3 : (Work.Spaces.DzIter j F z θ) ^ 2
        ≤ (Work.Spaces.DzIter j F z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 :=
      sq_le_sq_mul_of_one_le (one_le_w_div_sin_eta hz hsin)
    have h4 : (Work.Spaces.DzIter j F z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 F z θ :=
      Work.Spaces.sq_le_HkIntegrand_z α 6 F z θ j (by omega)
    have h5 : Work.Spaces.mixed j i F = Work.Spaces.DzIter j F := by
      rw [hi0]
      simp
    rw [h5]
    exact le_trans h3 h4

end Work.FTS.StrongEps.LocUnif
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.rect_integral_le_of_pointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

/-- If `g²` is dominated pointwise on the rectangle `[a,b] × [c,d]` (`⊆ (0,∞) × (0,π/2)`) by
`K` times the `ℋ⁶`-integrand of `F`, then the iterated integral of `g²` over the rectangle is
dominated by `K` times the squared `ℋ⁶`-norm of `F`.

The proof is pure monotonicity of the integral: the rectangle is contained in `Iz × Iθ`, the
`ℋ⁶`-integrand is a sum of squares and hence nonnegative, and the only integrability needed is
the one supplied by `HkMem α 6 F`. -/
theorem rect_integral_le_of_pointwise {a b c d K α : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hd : d < Real.pi / 2) {F g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 6 F) (hK : 0 ≤ K)
    (hpt : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (g z θ) ^ 2 ≤ K * Work.Spaces.HkIntegrand α 6 F z θ) :
    (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (g z θ) ^ 2) ≤ K * Work.Spaces.HkSq α 6 F := by
  have hsubz : Set.Icc a b ⊆ Work.Spaces.Iz := fun z hz => le_trans ha.le hz.1
  have hsubθ : Set.Icc c d ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_trans hc.le hθ.1, le_trans hθ.2 hd.le⟩
  -- (1) the angular integral at a fixed `z ∈ [a,b]`
  have hinner : ∀ z ∈ Set.Icc a b,
      (∫ θ in Set.Icc c d, (g z θ) ^ 2)
        ≤ K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 F z θ := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := hsubz hz
    have hInt : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 6 F z θ) (Set.Icc c d) :=
      (hmem.1 z hzIz).mono_set hsubθ
    have hInt2 : IntegrableOn
        (fun θ => K * Work.Spaces.HkIntegrand α 6 F z θ) (Set.Icc c d) := hInt.const_mul _
    have hstep1 : (∫ θ in Set.Icc c d, (g z θ) ^ 2)
        ≤ ∫ θ in Set.Icc c d, K * Work.Spaces.HkIntegrand α 6 F z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall fun θ => sq_nonneg _) hInt2
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          fun θ hθ => hpt z hz θ hθ)
    have hstep2 : (∫ θ in Set.Icc c d, Work.Spaces.HkIntegrand α 6 F z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 F z θ :=
      setIntegral_mono_set (hmem.1 z hzIz)
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 F z θ)
        (Eventually.of_forall fun θ hθ => hsubθ hθ)
    calc (∫ θ in Set.Icc c d, (g z θ) ^ 2)
        ≤ ∫ θ in Set.Icc c d, K * Work.Spaces.HkIntegrand α 6 F z θ := hstep1
      _ = K * ∫ θ in Set.Icc c d, Work.Spaces.HkIntegrand α 6 F z θ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 F z θ :=
          mul_le_mul_of_nonneg_left hstep2 hK
  -- (2) the radial integral
  have houter : (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (g z θ) ^ 2)
      ≤ K * ∫ z in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 F z θ := by
    have hInt : IntegrableOn
        (fun z => K * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 F z θ)
        (Set.Icc a b) := (hmem.2.mono_set hsubz).const_mul _
    calc (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (g z θ) ^ 2)
        ≤ ∫ z in Set.Icc a b, K * ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 6 F z θ :=
          MeasureTheory.integral_mono_of_nonneg
            (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hInt
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
              fun z hz => hinner z hz)
      _ = K * ∫ z in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 6 F z θ := MeasureTheory.integral_const_mul _ _
  -- (3) enlarging `[a,b]` to `Iz`
  have hlast : (∫ z in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 F z θ) ≤ Work.Spaces.HkSq α 6 F := by
    rw [Work.Spaces.HkSq]
    exact setIntegral_mono_set hmem.2
      (Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 F z θ)
      (Eventually.of_forall fun z hz => hsubz hz)
  exact le_trans houter (mul_le_mul_of_nonneg_left hlast hK)

end Work.FTS.StrongEps.LocUnif
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.SupPort.AuxMixSq.mixed_sq_w_le_HkIntegrand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.SupPort.AuxMixSq

set_option autoImplicit false

/-- The angular weight factor `w_θ = sin(2θ)^{-γ/2}` is `≥ 1` on the open quadrant:
there `0 < sin(2θ) ≤ 1` and the exponent `-γ/2` is nonpositive (indeed `γ > 1 > 0`). -/
theorem one_le_wTheta_sq {α : ℝ} (hα : 0 < α) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    1 ≤ (Work.Spaces.wTheta α θ) ^ 2 := by
  -- `2θ ∈ (0,π)`, so `0 < sin(2θ) ≤ 1`.
  have ht0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have ht1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hc : 0 ≤ Work.Spaces.gam α / 2 := by
    have h := Work.Spaces.gam_pos hα
    linarith
  -- `sin(2θ)^{γ/2} ≤ 1^{γ/2} = 1`.
  have hpow1 : (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2) ≤ 1 := by
    have h := Real.rpow_le_rpow (le_of_lt ht0) ht1 hc
    simpa using h
  have hpow0 : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2) :=
    Real.rpow_pos_of_pos ht0 _
  -- Hence the reciprocal power `sin(2θ)^{-γ/2}` is `≥ 1`, and so is its square.
  have hkey : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    have h : (1 : ℝ)⁻¹ ≤ ((Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2))⁻¹ := by
      rw [inv_le_inv₀ one_pos hpow0]
      exact hpow1
    rw [Real.rpow_neg (le_of_lt ht0)]
    simpa using h
  rw [Work.Spaces.wTheta]
  exact one_le_pow₀ hkey

/-- The unweighted square of a mixed slot is dominated by the `ℋ⁴`-integrand: on the open
quadrant the angular factor of `Wt` is `≥ 1`, so `(D_z^jD_θ^if)²w² ≤ (D_z^jD_θ^if·Wt)²`,
which is one of the summands of `HkIntegrand α 4 f`. -/
theorem mixed_sq_w_le_HkIntegrand {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (j i : ℕ)
    (hi : 1 ≤ i) (hij : i + j ≤ 4) {s σ : ℝ} (hσ : σ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f s σ := by
  have hWt : 1 ≤ (Work.Spaces.wTheta α σ) ^ 2 := one_le_wTheta_sq hα hσ
  -- `(mixed · Wt)² = (mixed)² w² (w_θ)² ≥ (mixed)² w²`, and it is a summand of the integrand.
  refine le_trans ?_ (Work.Spaces.sq_le_HkIntegrand_mixed α 4 f s σ i j hi hij)
  rw [Work.Spaces.Wt, mul_pow, mul_pow]
  exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (sq_nonneg _) hWt) (sq_nonneg _)

end Work.FTS.StrongEps.SupPort.AuxMixSq
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.AK6.akRho_jet_bound6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The order-`6` radial jet bound for the profile `z ↦ 2z²/(1+z)³`

We prove

`∃ R, 0 ≤ R ∧ ∀ j ≤ 6, ∀ z ∈ [0,∞), ∀ θ, (D_z^j f(z,θ) · w z)^2 ≤ R/(1+z)^2`,
`f z θ = 2z²/(1+z)³`, `w z = (1+z)²/z²`, `D_z = z ∂_z`

— the order-`6` strengthening of `Work.FTS.NonlinRows.AkRhoJetBasic.akRho_jet_bound`
(which covers `j ≤ 4` and `0 < z`).

The proof identifies the jets exactly: with `P_j` an explicit polynomial of degree `j`
(coefficients `akC j`),

`D_z^j f(z,θ) = z² · P_j(z) / (1+z)^{j+3}`  (for `z ≠ -1`),

equivalently `D_z^j f(z,θ) · w z = P_j(z)/(1+z)^{j+1}` on `z > 0`.  This is proved by
induction on `j` from the closed forms: the recursion `D_z^{j+1} f = z ∂_z(D_z^j f)` turns
into `P_{j+1} = z(1+z) P_j' + (2 - (j+1)z) P_j` for the numerators, which is exactly what
the `HasDerivAt` computation of the derivative of `w ↦ w² P_j(w)/(1+w)^{j+3}` produces.
The bound then follows from `|P_j(z)| ≤ (Σ_i |akC j i|)(1+z)^j ≤ 40320·(1+z)^j` for `z ≥ 0`
(the coefficient sums are `(j+1)!`, so `40320` works uniformly for `j ≤ 6`).

The `j ≤ 4` part can also be read off from `akRho_jet_bound`, but the argument here is
uniform in `j ≤ 6`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.AK6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The profile `z ↦ 2z²/(1+z)³`, as a function of `(z,θ)` independent of `θ`. -/
def akf : ℝ → ℝ → ℝ := fun z _ => 2 * z ^ 2 / (1 + z) ^ 3

/-- Coefficients of `P_j`, the numerator of the `j`-th weighted radial jet:
`akC j i` is the coefficient of `z^i` in `P_j` (and `0` for `i > j`). -/
def akC : ℕ → ℕ → ℝ
  | 0, i => if i = 0 then 2 else 0
  | 1, i => if i = 0 then 4 else if i = 1 then -2 else 0
  | 2, i => if i = 0 then 8 else if i = 1 then -14 else if i = 2 then 2 else 0
  | 3, i => if i = 0 then 16 else if i = 1 then -66 else if i = 2 then 36
              else if i = 3 then -2 else 0
  | 4, i => if i = 0 then 32 else if i = 1 then -262 else if i = 2 then 342
              else if i = 3 then -82 else if i = 4 then 2 else 0
  | 5, i => if i = 0 then 64 else if i = 1 then -946 else if i = 2 then 2416
              else if i = 3 then -1436 else if i = 4 then 176
              else if i = 5 then -2 else 0
  | _, i => if i = 0 then 128 else if i = 1 then -3222 else if i = 2 then 14394
              else if i = 3 then -16844 else if i = 4 then 5364
              else if i = 5 then -366 else if i = 6 then 2 else 0

/-- The polynomial `P_j` whose coefficients are `akC j`. -/
def akP (j : ℕ) (z : ℝ) : ℝ := ∑ i ∈ Finset.range (j + 1), akC j i * z ^ i

/-- The formal derivative of `akP j`. -/
def akPd (j : ℕ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), akC j i * ((i : ℝ) * z ^ (i - 1))

lemma hasDerivAt_akP (j : ℕ) (z : ℝ) :
    HasDerivAt (fun w : ℝ => akP j w) (akPd j z) z := by
  simp only [akP, akPd]
  exact HasDerivAt.fun_sum fun i _ => (hasDerivAt_pow i z).const_mul (akC j i)

lemma akC_sum_le (j : ℕ) (hj : j ≤ 6) :
    (∑ i ∈ Finset.range (j + 1), |akC j i|) ≤ 40320 := by
  interval_cases j <;> simp [akC, Finset.sum_range_succ] <;> norm_num

/-- The coefficient bound `|P_j(z)| ≤ 40320 (1+z)^j` for `z ≥ 0`, `j ≤ 6`. -/
lemma akP_abs_le (j : ℕ) (hj : j ≤ 6) {z : ℝ} (hz : 0 ≤ z) :
    |akP j z| ≤ 40320 * (1 + z) ^ j := by
  have h1' : (1 : ℝ) ≤ 1 + z := by linarith
  have hsum :
      |∑ i ∈ Finset.range (j + 1), akC j i * z ^ i| ≤ 40320 * (1 + z) ^ j := by
    calc |∑ i ∈ Finset.range (j + 1), akC j i * z ^ i|
        ≤ ∑ i ∈ Finset.range (j + 1), |akC j i * z ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1), |akC j i| * (1 + z) ^ j := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          rw [Finset.mem_range] at hi
          have h2 : |z| ^ i ≤ (1 + z) ^ i := by
            refine pow_le_pow_left₀ (abs_nonneg z) ?_ i
            rw [abs_of_nonneg hz]; linarith
          have h3 : (1 + z) ^ i ≤ (1 + z) ^ j := pow_le_pow_right₀ h1' (by omega)
          rw [abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left (le_trans h2 h3) (abs_nonneg _)
      _ = (∑ i ∈ Finset.range (j + 1), |akC j i|) * (1 + z) ^ j := by rw [Finset.sum_mul]
      _ ≤ 40320 * (1 + z) ^ j :=
          mul_le_mul_of_nonneg_right (akC_sum_le j hj) (by positivity)
  rwa [akP]

/-- The derivative of the `j`-th closed form; the recursion
`P_{j+1} = z(1+z) P_j' + (2 - (j+1)z) P_j` for the numerators. -/
lemma deriv_akRatio (j : ℕ) (hj : j ≤ 5) {z : ℝ} (hz : z ≠ -1) :
    deriv (fun w : ℝ => w ^ 2 * akP j w / (1 + w) ^ (j + 3)) z
      = z * akP (j + 1) z / (1 + z) ^ (j + 4) := by
  have h1 : (1 : ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  have hp : (1 + z) ^ (j + 3) ≠ 0 := pow_ne_zero _ h1
  have hp2 : ((1 + z) ^ (j + 3)) ^ 2 ≠ 0 := pow_ne_zero 2 hp
  have hnum : HasDerivAt (fun w : ℝ => w ^ 2 * akP j w)
      (2 * z * akP j z + z ^ 2 * akPd j z) z := by
    have h := (hasDerivAt_pow 2 z).mul (hasDerivAt_akP j z)
    refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w; simp
    · ring
  have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ (j + 3))
      (((j + 3 : ℕ) : ℝ) * (1 + z) ^ (j + 3 - 1)) z :=
    Work.FTS.NonlinRows.AkRhoJetBasic.hasDerivAt_one_add_pow (j + 3) z
  have hq : HasDerivAt (fun w : ℝ => w ^ 2 * akP j w / (1 + w) ^ (j + 3))
      (z * akP (j + 1) z / (1 + z) ^ (j + 4)) z := by
    refine (hnum.fun_div hden hp).congr_deriv ?_
    interval_cases j <;>
      · simp only [akP, akPd, akC, Finset.sum_range_succ]
        norm_num
        field_simp [h1, hp, hp2]
        ring
  exact hq.deriv

/-- The exact closed form of the `j`-th radial jet, `j ≤ 6`:
`D_z^j f(z,θ) = z² · P_j(z) / (1+z)^{j+3}` for `z ≠ -1`. -/
lemma akJetP (j : ℕ) : j ≤ 6 → ∀ {z : ℝ}, z ≠ -1 → ∀ (θ : ℝ),
    Work.Spaces.DzIter j akf z θ = z ^ 2 * akP j z / (1 + z) ^ (j + 3) := by
  induction j with
  | zero =>
      intro _ z _ θ
      have h0 : akP 0 z = 2 := by norm_num [akP, akC, Finset.sum_range_succ]
      rw [h0]
      simp only [Work.Spaces.DzIter_zero, akf]
      norm_num
      ring
  | succ j ih =>
      intro hj z hz θ
      have hj' : j ≤ 5 := by omega
      have hfun : (fun w : ℝ => Work.Spaces.DzIter j akf w θ) =ᶠ[𝓝 z]
          (fun w : ℝ => w ^ 2 * akP j w / (1 + w) ^ (j + 3)) := by
        filter_upwards [(isOpen_ne (x := (-1 : ℝ))).mem_nhds hz] with w hw
        exact ih (by omega) hw θ
      have hstep : Work.Spaces.DzIter (j + 1) akf z θ
          = z * deriv (fun w : ℝ => w ^ 2 * akP j w / (1 + w) ^ (j + 3)) z := by
        simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
        rw [Filter.EventuallyEq.deriv_eq hfun]
      rw [hstep, deriv_akRatio j hj' hz, show (j + 1) + 3 = j + 4 from by omega]
      ring

/-- The weighted form of the exact jet: `D_z^j f(z,θ) · w z = P_j(z)/(1+z)^{j+1}` for
`z > 0` (via `z ≠ 0`), `j ≤ 6`. -/
lemma akJetP_mul_w (j : ℕ) (hj : j ≤ 6) {z : ℝ} (hz : z ≠ 0) (hz1 : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter j akf z θ * Work.Spaces.w z = akP j z / (1 + z) ^ (j + 1) := by
  have h1 : (1 + z) ≠ 0 := by intro h; exact hz1 (by linarith)
  have hpow : (1 + z) ^ (j + 3) = (1 + z) ^ (j + 1) * (1 + z) ^ 2 := by
    rw [show j + 3 = (j + 1) + 2 from by omega, pow_add]
  rw [akJetP j hj hz1 θ, Work.Spaces.w, hpow]
  field_simp

theorem akRho_jet_bound6 : ∃ R : ℝ, 0 ≤ R ∧ ∀ (j : ℕ), j ≤ 6 → ∀ (z : ℝ), z ∈ Work.Spaces.Iz → ∀ (θ : ℝ), (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2 := by
  refine ⟨40320 ^ 2, by norm_num, fun j hj z hz θ => ?_⟩
  have hz0 : 0 ≤ z := hz
  rcases eq_or_lt_of_le hz0 with h | h
  · -- `z = 0`: the weight `w` vanishes, so the left-hand side is `0 ≤ R`.
    subst h
    have hw : Work.Spaces.w 0 = 0 := by norm_num [Work.Spaces.w]
    rw [hw, mul_zero]
    simp
  · have hz1 : z ≠ -1 := by linarith
    have hzne : z ≠ 0 := ne_of_gt h
    have hpos : (0 : ℝ) < 1 + z := by linarith
    have hw : Work.Spaces.DzIter j akf z θ * Work.Spaces.w z
        = akP j z / (1 + z) ^ (j + 1) := akJetP_mul_w j hj hzne hz1 θ
    rw [show Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ
          = Work.Spaces.DzIter j akf z θ from rfl, hw]
    have hb : |akP j z| ≤ 40320 * (1 + z) ^ j := akP_abs_le j hj hz0
    have hden : (0 : ℝ) < (1 + z) ^ (j + 1) := by positivity
    have hkey : |akP j z / (1 + z) ^ (j + 1)| ≤ 40320 / (1 + z) := by
      rw [abs_div, abs_of_pos hden]
      rw [div_le_div_iff₀ hden hpos]
      calc |akP j z| * (1 + z) ≤ (40320 * (1 + z) ^ j) * (1 + z) :=
            mul_le_mul_of_nonneg_right hb hpos.le
        _ = 40320 * (1 + z) ^ (j + 1) := by rw [mul_assoc, ← pow_succ]
    calc (akP j z / (1 + z) ^ (j + 1)) ^ 2
        = |akP j z / (1 + z) ^ (j + 1)| ^ 2 := (sq_abs _).symm
      _ ≤ (40320 / (1 + z)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hkey 2
      _ = 40320 ^ 2 / (1 + z) ^ 2 := by rw [div_pow]

end Work.FTS.StrongPersist.AK6
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkSlotDom =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false


/-- `sin (2θ) ≥ 0` for `0 ≤ θ ≤ π/2`, in the strict form used here. -/
private lemma sin_two_nonneg {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩


end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-- The open interval `Ioo 0 (π/2)` is conull in `Iθ = [0,π/2]`: it differs from `Iθ`
only by the two endpoints, which form a null set.  This is what makes the hypotheses
"on `Ioo 0 (π/2)`" sufficient for statements about `∫ θ in Iθ, ·`. -/
private lemma ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  show ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (π / 2))), θ ∈ Set.Ioo 0 (π / 2)
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2))]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hθ)

/-- The square of the mixed weight `Wt α z θ = w z · sin(2θ)^{-γ/2}` is
`w z² · sin(2θ)^{-γ}`; this is the identity which converts a slot of `HkIntegrand`
into the corresponding explicit weighted square. -/
private lemma Wt_sq_eq (α z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ ((2 : ℝ)) from
      (Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2).symm]
  rw [← Real.rpow_mul hs]
  rw [show (-(Work.Spaces.gam α / 2)) * (2 : ℝ) = -(Work.Spaces.gam α) by ring]

/-- The pointwise comparison for a pure `D_z`-slot: if `θw θ ≤ sin(2θ)^{-η}` then the
weighted square `w² θw (D_z^i f)²` is dominated by the `i`-th slot of `HkIntegrand`.
Only interior angles are needed (there the exponent identity `(w/s^{η/2})² = w² s^{-η}`
is available). -/
private lemma zSlot_pointwise (α : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) (hi : i ≤ 6)
    (θw : ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hle : θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :
    (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hmain : (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2
      ≤ (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [Work.Spaces.sq_mul_div_rpow _ _ _ _ (le_of_lt hs) (by norm_num [Work.Spaces.eta])]
    calc (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2
        = (Work.Spaces.w z) ^ 2
            * (θw θ * (Work.Spaces.DzIter i f z θ) ^ 2) := by ring
      _ ≤ (Work.Spaces.w z) ^ 2
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              * (Work.Spaces.DzIter i f z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) (sq_nonneg _)
      _ = (Work.Spaces.DzIter i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring
  exact hmain.trans (Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ i hi)

/-- The pointwise comparison for a mixed slot: if `θw θ ≤ sin(2θ)^{-γ}` then the
weighted square `w² θw (D_z^j D_θ^i f)²` is dominated by the `(i,j)`-slot of
`HkIntegrand`. -/
private lemma mSlot_pointwise (α : ℝ) (f : ℝ → ℝ → ℝ) (i j : ℕ) (hi : 1 ≤ i)
    (hij : i + j ≤ 6) (θw : ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hle : θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :
    (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hmain : (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    calc (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2
        = (Work.Spaces.w z) ^ 2
            * (θw θ * (Work.Spaces.mixed j i f z θ) ^ 2) := by ring
      _ ≤ (Work.Spaces.w z) ^ 2
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j i f z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) (sq_nonneg _)
      _ = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          rw [mul_pow, Wt_sq_eq α z θ hs]
          ring
  exact hmain.trans (Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ i j hi hij)

theorem intSlotLeHkSq (α : ℝ) {f : ℝ → ℝ → ℝ} (h : Work.Spaces.HkMem α 6 f) :
    (∀ i : ℕ, i ≤ 6 → ∀ θw : ℝ → ℝ,
      (∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ θw θ) →
      (∀ θ ∈ Set.Ioo 0 (π / 2), θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2)
        ≤ Work.Spaces.HkSq α 6 f) ∧
    (∀ j i : ℕ, 1 ≤ i → i + j ≤ 6 → ∀ θw : ℝ → ℝ,
      (∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ θw θ) →
      (∀ θ ∈ Set.Ioo 0 (π / 2), θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2)
        ≤ Work.Spaces.HkSq α 6 f) := by
  have hIoo := ae_mem_Ioo_Iθ
  constructor
  · intro i hi θw hnn hle
    have hnn' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ θw θ :=
      hIoo.mono fun θ hθ => hnn θ hθ
    have hle' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      hIoo.mono fun θ hθ => hle θ hθ
    have hinner_nn : ∀ z, 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ => (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2) :=
      fun z => hnn'.mono fun θ h1 =>
        mul_nonneg (mul_nonneg (sq_nonneg _) h1) (sq_nonneg _)
    have hinner_le : ∀ z, (fun θ =>
          (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => Work.Spaces.HkIntegrand α 6 f z θ) :=
      fun z => (hIoo.and hle').mono fun θ hθ => zSlot_pointwise α f i hi θw z θ hθ.1 hθ.2
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => MeasureTheory.integral_nonneg_of_ae (hinner_nn z)) h.2 ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz =>
      MeasureTheory.integral_mono_of_nonneg (hinner_nn z) (h.1 z hz) (hinner_le z)
  · intro j i hi hij θw hnn hle
    have hnn' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ θw θ :=
      hIoo.mono fun θ hθ => hnn θ hθ
    have hle' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      hIoo.mono fun θ hθ => hle θ hθ
    have hinner_nn : ∀ z, 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ => (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2) :=
      fun z => hnn'.mono fun θ h1 =>
        mul_nonneg (mul_nonneg (sq_nonneg _) h1) (sq_nonneg _)
    have hinner_le : ∀ z, (fun θ =>
          (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => Work.Spaces.HkIntegrand α 6 f z θ) :=
      fun z => (hIoo.and hle').mono fun θ hθ =>
        mSlot_pointwise α f i j hi hij θw z θ hθ.1 hθ.2
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => MeasureTheory.integral_nonneg_of_ae (hinner_nn z)) h.2 ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz =>
      MeasureTheory.integral_mono_of_nonneg (hinner_nn z) (h.1 z hz) (hinner_le z)

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.TraceOsc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false

/-- **The oscillation argument at `0⁺`.**  If `u ≥ 0` is differentiable on `(0,1)` with
`∫₀¹ |u'| < ∞` and `∫₀¹ u/z < ∞`, then `u → 0` at `0⁺`. -/
theorem tendsto_zero_of_integrableOn_deriv_left {u : ℝ → ℝ}
    (hu : ∀ z ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ u z)
    (hnn : ∀ z ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ u z)
    (hdiv : IntegrableOn (fun z => u z / z) (Set.Ioo (0 : ℝ) 1))
    (hder : IntegrableOn (deriv u) (Set.Ioo (0 : ℝ) 1)) :
    Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hosc : ∀ {a b δ : ℝ}, 0 < a → a ≤ b → b < δ → δ < 1 →
      |u b - u a| ≤ ∫ x in Set.Ioo (0 : ℝ) δ, |deriv u x| := by
    intro a b δ ha hab hb hδ
    have hsu : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) 1 := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 (lt_trans hb hδ)⟩
    have hInt : IntervalIntegrable (deriv u) volume a b :=
      IntegrableOn.intervalIntegrable (IntegrableOn.mono_set hder hsu)
    have hFTC : ∫ x in a..b, deriv u x = u b - u a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => (hu x (hsu hx)).hasDerivAt) hInt
    have h1 : |u b - u a| ≤ ∫ x in a..b, |deriv u x| := by
      rw [← hFTC]
      exact intervalIntegral.abs_integral_le_integral_abs hab
    have h2 : (∫ x in a..b, |deriv u x|) ≤ ∫ x in Set.Ioo (0 : ℝ) δ, |deriv u x| := by
      rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      refine MeasureTheory.setIntegral_mono_set
        (IntegrableOn.mono_set (Integrable.abs hder) (fun x hx => ⟨hx.1, lt_trans hx.2 hδ⟩))
        ?_ ?_
      · exact Filter.Eventually.of_forall (fun x => abs_nonneg (deriv u x))
      · exact Filter.Eventually.of_forall (fun x hx => ⟨lt_trans ha hx.1, lt_trans hx.2 hb⟩)
    linarith
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := exists_setIntegral_Ioo_abs_le hder (show (0 : ℝ) < ε / 2 by linarith)
  set C : ℝ := ∫ x in Set.Ioo (0 : ℝ) 1, u x / x with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact div_nonneg (hnn x hx) (le_of_lt hx.1)
  have hkey : ∀ z ∈ Set.Ioo (0 : ℝ) δ, u z < ε := by
    intro z hz
    by_contra hcon
    push_neg at hcon
    have hA : ∀ z' ∈ Set.Ioo (0 : ℝ) δ, ε / 2 ≤ u z' := by
      intro z' hz'
      have h1 : |u z' - u z| ≤ ∫ x in Set.Ioo (0 : ℝ) δ, |deriv u x| := by
        rcases le_total z' z with h | h
        · rw [abs_sub_comm]
          exact hosc (a := z') (b := z) (δ := δ) hz'.1 h hz.2 hδ1
        · exact hosc (a := z) (b := z') (δ := δ) hz.1 h hz'.2 hδ1
      have h2 := (abs_le.mp h1).1
      have h3 : u z' ≥ u z - ε / 2 := by linarith [h2, hδ]
      linarith [hcon, h3]
    have hlog : ∀ M : ℝ, ∀ᶠ a in 𝓝[>] (0 : ℝ), M < Real.log (δ / a) := by
      intro M
      have h1 : ∀ᶠ a in 𝓝[>] (0 : ℝ), Real.log a < Real.log δ - M :=
        Real.tendsto_log_nhdsGT_zero.eventually (eventually_lt_atBot _)
      filter_upwards [h1, self_mem_nhdsWithin] with a ha ha0
      rw [Real.log_div (ne_of_gt hδ0) (ne_of_gt ha0)]
      linarith
    have hlt : ∀ᶠ a in 𝓝[>] (0 : ℝ), a < δ := nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hδ0)
    have hpos' : ∀ᶠ a in 𝓝[>] (0 : ℝ), (0 : ℝ) < a := self_mem_nhdsWithin
    have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ), (2 * C / ε < Real.log (δ / a)) ∧ a < δ ∧ 0 < a :=
      (hlog (2 * C / ε)).and (hlt.and hpos')
    obtain ⟨a, hlog_a, haδ, ha0⟩ := hev.exists
    have hId' : (∫ x in a..δ, (ε / 2) / x) = (ε / 2) * Real.log (δ / a) := by
      have h1 : (fun x : ℝ => (ε / 2) / x) = fun x : ℝ => (ε / 2) * x⁻¹ := by
        funext x; rw [div_eq_mul_inv]
      rw [h1, intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 hδ0]
    have hpt : ∀ x ∈ Set.Ioo a δ, (ε / 2) / x ≤ u x / x := by
      intro x hx
      have hx0 : 0 < x := lt_trans ha0 hx.1
      rw [div_le_div_iff_of_pos_right hx0]
      exact hA x ⟨hx0, hx.2⟩
    have hIntc : IntervalIntegrable (fun x : ℝ => (ε / 2) / x) volume a δ := by
      refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.div continuousOn_id (fun x hx => ?_)
      rw [Set.uIcc_of_le (le_of_lt haδ)] at hx
      exact ne_of_gt (lt_of_lt_of_le ha0 hx.1)
    have hIntu : IntervalIntegrable (fun x : ℝ => u x / x) volume a δ := by
      refine IntegrableOn.intervalIntegrable (IntegrableOn.mono_set hdiv ?_)
      intro x hx
      rw [Set.uIcc_of_le (le_of_lt haδ)] at hx
      exact ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt hx.2 hδ1⟩
    have hcmp : (∫ x in a..δ, (ε / 2) / x) ≤ ∫ x in a..δ, u x / x :=
      intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt haδ) hIntc hIntu hpt
    have hup : (∫ x in a..δ, u x / x) ≤ C := by
      rw [intervalIntegral.integral_of_le (le_of_lt haδ),
        MeasureTheory.integral_Ioc_eq_integral_Ioo, hCdef]
      refine MeasureTheory.setIntegral_mono_set hdiv ?_ ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        exact div_nonneg (hnn x hx) (le_of_lt hx.1)
      · exact Filter.Eventually.of_forall (fun x hx => ⟨lt_trans ha0 hx.1, lt_trans hx.2 hδ1⟩)
    have hε2 : 0 < ε / 2 := by linarith
    have hkey2 : C < (ε / 2) * Real.log (δ / a) := by
      have := mul_lt_mul_of_pos_left hlog_a hε2
      have heq : (ε / 2) * (2 * C / ε) = C := by
        field_simp
      rwa [heq] at this
    have h3 : (ε / 2) * Real.log (δ / a) ≤ C := by
      rw [← hId']
      exact le_trans hcmp hup
    linarith
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hδ0)] with z hz1 hz2
  have hz : z ∈ Set.Ioo (0 : ℝ) 1 := ⟨hz1, lt_trans hz2 hδ1⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnn z hz)]
  exact hkey z ⟨hz1, hz2⟩

/-- **The oscillation argument at `+∞`.**  If `u ≥ 0` is differentiable on `(1,∞)` with
`∫₁^∞ |u'| < ∞` and `∫₁^∞ u/z < ∞`, then `u → 0` at `+∞`. -/
theorem tendsto_zero_of_integrableOn_deriv_atTop {u : ℝ → ℝ}
    (hu : ∀ z ∈ Set.Ioi (1 : ℝ), DifferentiableAt ℝ u z)
    (hnn : ∀ z ∈ Set.Ioi (1 : ℝ), 0 ≤ u z)
    (hdiv : IntegrableOn (fun z => u z / z) (Set.Ioi (1 : ℝ)))
    (hder : IntegrableOn (deriv u) (Set.Ioi (1 : ℝ))) :
    Tendsto u atTop (𝓝 0) := by
  have hosc : ∀ {R a b : ℝ}, 1 < R → R < a → a ≤ b →
      |u b - u a| ≤ ∫ x in Set.Ioi R, |deriv u x| := by
    intro R a b hR1 hRa hab
    have hsub : Set.uIcc a b ⊆ Set.Ioi (1 : ℝ) := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      simp only [Set.mem_Ioi]
      exact lt_of_lt_of_le (lt_trans hR1 hRa) hx.1
    have hInt : IntervalIntegrable (deriv u) volume a b :=
      IntegrableOn.intervalIntegrable (IntegrableOn.mono_set hder hsub)
    have hFTC : ∫ x in a..b, deriv u x = u b - u a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => (hu x (hsub hx)).hasDerivAt) hInt
    have h1 : |u b - u a| ≤ ∫ x in a..b, |deriv u x| := by
      rw [← hFTC]
      exact intervalIntegral.abs_integral_le_integral_abs hab
    have h2 : (∫ x in a..b, |deriv u x|) ≤ ∫ x in Set.Ioi R, |deriv u x| := by
      rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      refine MeasureTheory.setIntegral_mono_set
        (IntegrableOn.mono_set (Integrable.abs hder) (fun x hx => lt_trans hR1 hx)) ?_ ?_
      · exact Filter.Eventually.of_forall (fun x => abs_nonneg (deriv u x))
      · exact Filter.Eventually.of_forall (fun x hx => lt_trans hRa hx.1)
    linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR1, hR⟩ := exists_setIntegral_Ioi_abs_le hder (show (0 : ℝ) < ε / 2 by linarith)
  set C : ℝ := ∫ x in Set.Ioi (1 : ℝ), u x / x with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact div_nonneg (hnn x hx) (le_of_lt (lt_trans zero_lt_one hx))
  have hRpos : 0 < R := lt_trans zero_lt_one hR1
  have hkey : ∀ z ∈ Set.Ioi R, u z < ε := by
    intro z hz
    by_contra hcon
    push_neg at hcon
    have hA : ∀ z' ∈ Set.Ioi R, ε / 2 ≤ u z' := by
      intro z' hz'
      have h1 : |u z' - u z| ≤ ∫ x in Set.Ioi R, |deriv u x| := by
        rcases le_total z' z with h | h
        · rw [abs_sub_comm]
          exact hosc (R := R) (a := z') (b := z) hR1 hz' h
        · exact hosc (R := R) (a := z) (b := z') hR1 hz h
      have h2 := (abs_le.mp h1).1
      have h3 : u z' ≥ u z - ε / 2 := by linarith [h2, hR]
      linarith [hcon, h3]
    have hlog : ∀ M : ℝ, ∀ᶠ S in atTop, M < Real.log (S / R) ∧ R < S := by
      intro M
      have h1 : ∀ᶠ S in atTop, Real.log R + M < Real.log S :=
        Real.tendsto_log_atTop.eventually (eventually_gt_atTop _)
      filter_upwards [h1, Filter.Ioi_mem_atTop R] with S hS hRS
      have hSpos : 0 < S := lt_of_lt_of_le hRpos (le_of_lt hRS)
      refine ⟨?_, hRS⟩
      rw [Real.log_div (x := S) (y := R) (ne_of_gt hSpos) (ne_of_gt hRpos)]
      linarith
    obtain ⟨S, hlogS, hRS⟩ := (hlog (2 * C / ε)).exists
    have hSpos : 0 < S := lt_of_lt_of_le hRpos (le_of_lt hRS)
    have hId' : (∫ x in R..S, (ε / 2) / x) = (ε / 2) * Real.log (S / R) := by
      have h1 : (fun x : ℝ => (ε / 2) / x) = fun x : ℝ => (ε / 2) * x⁻¹ := by
        funext x; rw [div_eq_mul_inv]
      rw [h1, intervalIntegral.integral_const_mul, integral_inv_of_pos hRpos hSpos]
    have hpt : ∀ x ∈ Set.Ioo R S, (ε / 2) / x ≤ u x / x := by
      intro x hx
      have hx0 : 0 < x := lt_trans hRpos hx.1
      rw [div_le_div_iff_of_pos_right hx0]
      exact hA x hx.1
    have hIntc : IntervalIntegrable (fun x : ℝ => (ε / 2) / x) volume R S := by
      refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.div continuousOn_id (fun x hx => ?_)
      rw [Set.uIcc_of_le (le_of_lt hRS)] at hx
      exact ne_of_gt (lt_of_lt_of_le hRpos hx.1)
    have hIntu : IntervalIntegrable (fun x : ℝ => u x / x) volume R S := by
      refine IntegrableOn.intervalIntegrable (IntegrableOn.mono_set hdiv ?_)
      intro x hx
      rw [Set.uIcc_of_le (le_of_lt hRS)] at hx
      exact lt_of_lt_of_le hR1 hx.1
    have hcmp : (∫ x in R..S, (ε / 2) / x) ≤ ∫ x in R..S, u x / x :=
      intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt hRS) hIntc hIntu hpt
    have hup : (∫ x in R..S, u x / x) ≤ C := by
      rw [intervalIntegral.integral_of_le (le_of_lt hRS),
        MeasureTheory.integral_Ioc_eq_integral_Ioo, hCdef]
      refine MeasureTheory.setIntegral_mono_set hdiv ?_ ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact div_nonneg (hnn x hx) (le_of_lt (lt_trans zero_lt_one hx))
      · exact Filter.Eventually.of_forall (fun x hx => lt_trans hR1 hx.1)
    have hε2 : 0 < ε / 2 := by linarith
    have hkey2 : C < (ε / 2) * Real.log (S / R) := by
      have := mul_lt_mul_of_pos_left hlogS hε2
      have heq : (ε / 2) * (2 * C / ε) = C := by
        field_simp
      rwa [heq] at this
    have h3 : (ε / 2) * Real.log (S / R) ≤ C := by
      rw [← hId']
      exact le_trans hcmp hup
    linarith
  refine ⟨R + 1, fun n hn => ?_⟩
  have hnR : n ∈ Set.Ioi R := by simp only [Set.mem_Ioi]; linarith
  have hn1 : n ∈ Set.Ioi (1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnn n hn1)]
  exact hkey n hnR

end Work.FTS.StrongPersist.N6Trans.Hon
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.power_hardy_interval =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The weighted Hardy inequality on an interval bounded away from `0`.**

For `c > -1`, `0 < ε < b` and `f` of class `C¹` on `[ε,b]`,

  `∫_ε^b f² x^c ≤ 4/(c+1)² ∫_ε^b (f')² x^{c+2} + 2/(c+1) f(b)² b^{c+1}`.

This is the same inequality as `Work.FTS.H2.Transport3Aux.power_hardy_boundary`, but with the
lower endpoint `0` replaced by `ε > 0`; the only difference is that the lower boundary term
`-f(ε)² ε^{c+1}` (which is non-positive, hence harmless) is kept rather than discarded, and
that no limiting argument at `0` is needed: the fundamental theorem of calculus is applied
directly on `[ε,b]`.

Writing `φ(t) = f(t)² t^{c+1}`, one has `φ'(t) = 2 f f' t^{c+1} + (c+1) f² t^c` on `(ε,b)`, so
`(c+1)∫_ε^b f² t^c = f(b)²b^{c+1} - f(ε)²ε^{c+1} - 2∫_ε^b f f' t^{c+1}`.  The pointwise
weighted arithmetic--geometric mean inequality
`2|f f'| t^{c+1} ≤ (c+1)/2 f² t^c + 2/(c+1) (f')² t^{c+2}` then bounds the cross term. -/
theorem power_hardy_interval {c ε b : ℝ} (hc : -1 < c) (hε : 0 < ε) (hεb : ε < b) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc ε b)) :
    (∫ x in Set.Ioc ε b, (f x) ^ 2 * x ^ c)
      ≤ 4 / (c + 1) ^ 2 * (∫ x in Set.Ioc ε b, (deriv f x) ^ 2 * x ^ (c + 2))
        + 2 / (c + 1) * (f b) ^ 2 * b ^ (c + 1) := by
  have hc1 : 0 < c + 1 := by linarith
  rw [← intervalIntegral.integral_of_le hεb.le, ← intervalIntegral.integral_of_le hεb.le]
  -- ## Step 1: continuity and integrability of the three integrands
  have hcontf : ContinuousOn f (Set.Icc ε b) := hf.continuousOn
  have hdcont : ContinuousOn (derivWithin f (Set.Icc ε b)) (Set.Icc ε b) :=
    hf.continuousOn_derivWithin (uniqueDiffOn_Icc hεb) le_rfl
  have hrpow : ∀ r : ℝ, ContinuousOn (fun t : ℝ => t ^ r) (Set.Icc ε b) := fun r =>
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hε ht.1)))
  have mkII : ∀ {G : ℝ → ℝ}, ContinuousOn G (Set.Icc ε b) → IntervalIntegrable G volume ε b :=
    fun {G} hG => ContinuousOn.intervalIntegrable (show ContinuousOn G (Set.uIcc ε b) from by
      rw [Set.uIcc_of_le hεb.le]; exact hG)
  -- on `(ε,b]` the derivatives `deriv f` and `derivWithin f (Icc ε b)` may differ only at `b`
  have hb_ae : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ≠ b := by
    rw [MeasureTheory.ae_iff]
    simp
  have hae_deriv' : ∀ᵐ t ∂(volume.restrict (Set.Ioc ε b)),
      deriv f t = derivWithin f (Set.Icc ε b) t := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hb_ae] with t htb ht
    have ht' : t ∈ Set.Ioo ε b := ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩
    exact (derivWithin_of_mem_nhds
      (mem_of_superset (Ioo_mem_nhds ht'.1 ht'.2) Set.Ioo_subset_Icc_self)).symm
  have hae_deriv : (fun t : ℝ => deriv f t)
      =ᵐ[volume.restrict (Set.Ioc ε b)] (fun t : ℝ => derivWithin f (Set.Icc ε b) t) :=
    hae_deriv'
  have hI1 : IntervalIntegrable (fun t : ℝ => f t ^ 2 * t ^ c) volume ε b :=
    mkII ((hcontf.pow 2).mul (hrpow c))
  have hI2' : IntervalIntegrable (fun t : ℝ => (derivWithin f (Set.Icc ε b) t) ^ 2 * t ^ (c + 2))
      volume ε b := mkII ((hdcont.pow 2).mul (hrpow (c + 2)))
  have hI2 : IntervalIntegrable (fun t : ℝ => (deriv f t) ^ 2 * t ^ (c + 2)) volume ε b := by
    refine hI2'.congr_ae ?_
    rw [Set.uIoc_of_le hεb.le]
    change ∀ᵐ t ∂(volume.restrict (Set.Ioc ε b)),
      (derivWithin f (Set.Icc ε b) t) ^ 2 * t ^ (c + 2) = (deriv f t) ^ 2 * t ^ (c + 2)
    filter_upwards [hae_deriv'] with t ht
    rw [ht]
  have hI3' : IntervalIntegrable
      (fun t : ℝ => f t * derivWithin f (Set.Icc ε b) t * t ^ (c + 1)) volume ε b :=
    mkII ((hcontf.mul hdcont).mul (hrpow (c + 1)))
  have hI3 : IntervalIntegrable (fun t : ℝ => f t * deriv f t * t ^ (c + 1)) volume ε b := by
    refine hI3'.congr_ae ?_
    rw [Set.uIoc_of_le hεb.le]
    change ∀ᵐ t ∂(volume.restrict (Set.Ioc ε b)),
      f t * derivWithin f (Set.Icc ε b) t * t ^ (c + 1) = f t * deriv f t * t ^ (c + 1)
    filter_upwards [hae_deriv'] with t ht
    rw [ht]
  -- ## Step 2: the fundamental theorem of calculus for `φ t = f t ^ 2 * t ^ (c+1)`
  have hφcont : ContinuousOn (fun s : ℝ => f s ^ 2 * s ^ (c + 1)) (Set.Icc ε b) :=
    (hcontf.pow 2).mul (hrpow (c + 1))
  have hφderiv : ∀ x ∈ Set.Ioo ε b, HasDerivAt (fun s : ℝ => f s ^ 2 * s ^ (c + 1))
      (2 * (f x * deriv f x * x ^ (c + 1)) + (c + 1) * (f x ^ 2 * x ^ c)) x := by
    intro x hx
    have hnhds : Set.Icc ε b ∈ 𝓝 x :=
      mem_of_superset (Ioo_mem_nhds hx.1 hx.2) Set.Ioo_subset_Icc_self
    have hd : HasDerivAt f (deriv f x) x :=
      (hf.contDiffAt hnhds).differentiableAt_one.hasDerivAt
    have h1 : HasDerivAt (fun s : ℝ => f s ^ 2) (2 * f x ^ 1 * deriv f x) x := hd.pow 2
    have h2 : HasDerivAt (fun s : ℝ => s ^ (c + 1)) ((c + 1) * x ^ ((c + 1) - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl (lt_trans hε hx.1).ne')
    have h3 := h1.mul h2
    rw [show (c + 1) - 1 = c by ring] at h3
    refine h3.congr_deriv ?_
    ring
  have hφint : IntervalIntegrable
      (fun t : ℝ => 2 * (f t * deriv f t * t ^ (c + 1)) + (c + 1) * (f t ^ 2 * t ^ c))
      volume ε b := (hI3.const_mul 2).add (hI1.const_mul (c + 1))
  have hFTC : ∫ t in ε..b,
      (2 * (f t * deriv f t * t ^ (c + 1)) + (c + 1) * (f t ^ 2 * t ^ c))
      = f b ^ 2 * b ^ (c + 1) - f ε ^ 2 * ε ^ (c + 1) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεb.le hφcont hφderiv hφint
  -- ## Step 3: notation
  set A : ℝ := ∫ t in ε..b, f t ^ 2 * t ^ c with hAdef
  set B : ℝ := ∫ t in ε..b, (deriv f t) ^ 2 * t ^ (c + 2) with hBdef
  set S : ℝ := ∫ t in ε..b, f t * deriv f t * t ^ (c + 1) with hSdef
  set L : ℝ := ∫ t in ε..b, |f t * deriv f t * t ^ (c + 1)| with hLdef
  have hsplit : (∫ t in ε..b,
      (2 * (f t * deriv f t * t ^ (c + 1)) + (c + 1) * (f t ^ 2 * t ^ c)))
      = 2 * S + (c + 1) * A := by
    rw [intervalIntegral.integral_add (hI3.const_mul 2) (hI1.const_mul (c + 1)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hSdef, hAdef]
  -- ## Step 4: the identity `(c+1) A = f b ^ 2 * b ^ (c+1) - f ε ^ 2 * ε ^ (c+1) - 2 S`
  have hAB : (c + 1) * A = f b ^ 2 * b ^ (c + 1) - f ε ^ 2 * ε ^ (c + 1) - 2 * S := by
    rw [hsplit] at hFTC
    linarith
  have hSL : |S| ≤ L := by
    rw [hSdef, hLdef]
    exact intervalIntegral.abs_integral_le_integral_abs hεb.le
  -- ## Step 5: the weighted arithmetic--geometric mean inequality
  have hpt : ∀ t ∈ Set.Ioo ε b,
      2 * |f t * deriv f t * t ^ (c + 1)|
        ≤ (c + 1) / 2 * (f t ^ 2 * t ^ c)
          + 2 / (c + 1) * ((deriv f t) ^ 2 * t ^ (c + 2)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans hε ht.1
    have hta : 0 ≤ t ^ c := Real.rpow_nonneg ht0.le c
    have hpow1 : t ^ (c + 1) = t ^ c * t := by
      rw [Real.rpow_add ht0 c 1, Real.rpow_one]
    have hpow2 : t ^ (c + 2) = t ^ c * t ^ 2 := by
      rw [Real.rpow_add ht0 c 2, Real.rpow_two]
    have hL : |f t * deriv f t * (t ^ c * t)| = (|f t| * |deriv f t| * t) * t ^ c := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hta, abs_of_pos ht0]
      ring
    have hkey : 4 * (c + 1) * (|f t| * |deriv f t| * t)
        ≤ (c + 1) ^ 2 * f t ^ 2 + 4 * (deriv f t) ^ 2 * t ^ 2 := by
      have htwo := two_mul_le_add_sq ((c + 1) * |f t|) (2 * |deriv f t| * t)
      have hfa : |f t| ^ 2 = f t ^ 2 := sq_abs (f t)
      have hga : |deriv f t| ^ 2 = (deriv f t) ^ 2 := sq_abs (deriv f t)
      nlinarith [htwo, hfa, hga]
    have hred : 2 * (|f t| * |deriv f t| * t)
        ≤ (c + 1) / 2 * f t ^ 2 + 2 / (c + 1) * ((deriv f t) ^ 2 * t ^ 2) := by
      have hc2 : (0 : ℝ) < 2 * (c + 1) := by linarith
      refine le_of_mul_le_mul_right ?_ hc2
      have h1 : ((c + 1) / 2 * f t ^ 2 + 2 / (c + 1) * ((deriv f t) ^ 2 * t ^ 2))
          * (2 * (c + 1)) = (c + 1) ^ 2 * f t ^ 2 + 4 * (deriv f t) ^ 2 * t ^ 2 := by
        field_simp
        ring
      have h2 : 2 * (|f t| * |deriv f t| * t) * (2 * (c + 1))
          = 4 * (c + 1) * (|f t| * |deriv f t| * t) := by ring
      rw [h1, h2]
      exact hkey
    rw [hpow1, hpow2, hL]
    have hmul := mul_le_mul_of_nonneg_right hred hta
    nlinarith [hmul]
  -- ## Step 6: integrate the pointwise bound
  have hIL : IntervalIntegrable (fun t : ℝ => 2 * |f t * deriv f t * t ^ (c + 1)|)
      volume ε b := (hI3.abs).const_mul 2
  have hIR : IntervalIntegrable (fun t : ℝ =>
      (c + 1) / 2 * (f t ^ 2 * t ^ c) + 2 / (c + 1) * ((deriv f t) ^ 2 * t ^ (c + 2)))
      volume ε b :=
    (hI1.const_mul ((c + 1) / 2)).add (hI2.const_mul (2 / (c + 1)))
  have hAMGM : 2 * L ≤ (c + 1) / 2 * A + 2 / (c + 1) * B := by
    have h := intervalIntegral.integral_mono_on_of_le_Ioo hεb.le hIL hIR hpt
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hI1.const_mul ((c + 1) / 2)) (hI2.const_mul (2 / (c + 1))),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
    exact h
  -- ## Step 7: finish
  have hstep : (c + 1) / 2 * A ≤ f b ^ 2 * b ^ (c + 1) + 2 / (c + 1) * B := by
    have h1 : -2 * S ≤ 2 * L := by
      have h2 := neg_abs_le S
      linarith
    have hεpow : 0 ≤ f ε ^ 2 * ε ^ (c + 1) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hε.le _)
    nlinarith [hAB, h1, hAMGM, hεpow]
  have hfin : A ≤ 2 / (c + 1) * (f b ^ 2 * b ^ (c + 1)) + 4 / (c + 1) ^ 2 * B := by
    have hc2 : (0 : ℝ) < (c + 1) / 2 := by linarith
    have h1 : A * ((c + 1) / 2) ≤ f b ^ 2 * b ^ (c + 1) + 2 / (c + 1) * B := by linarith
    have h2 := (le_div_iff₀ hc2).2 h1
    have h3 : (f b ^ 2 * b ^ (c + 1) + 2 / (c + 1) * B) / ((c + 1) / 2)
        = 2 / (c + 1) * (f b ^ 2 * b ^ (c + 1)) + 4 / (c + 1) ^ 2 * B := by
      field_simp
      ring
    rw [h3] at h2
    exact h2
  have hgoal : 2 / (c + 1) * (f b ^ 2 * b ^ (c + 1)) + 4 / (c + 1) ^ 2 * B
      = 4 / (c + 1) ^ 2 * B + 2 / (c + 1) * (f b) ^ 2 * b ^ (c + 1) := by ring
  linarith [hfin, hgoal]

end Work.FTS.StrongPersist.N6Trans.SixRoute
end
-- ===== merged: Submission.Work.FTS.Top.Integrable.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter Topology
open scoped Topology NNReal Matrix ENNReal

namespace Work.FTS.Top.Integrable

/-- The curl (vorticity) of a continuous linear map `ℝ³ →L[ℝ] ℝ³`, in exactly the form in which
the curl of a differentiable field appears in `FiniteTimeSingularity.vorticity`:
`∇×L = ∑ᵢ eᵢ ×₃ (L eᵢ)`. -/
noncomputable def curlOf (L : R3 →L[ℝ] R3) : R3 :=
  WithLp.toLp 2 (∑ i, FiniteTimeSingularity.e i ⨯₃ (L (FiniteTimeSingularity.e i)))

/-- `curlOf` is continuous (it is a finite sum of compositions of the continuous linear maps
`L ↦ L (e i)` and the bilinear cross product with the fixed vector `e i`). -/
theorem continuous_curlOf : Continuous curlOf := by
  unfold curlOf
  fun_prop

/-- The spatial derivative of the time slice `y ↦ u y t` at `x` is the restriction of the joint
derivative `fderiv ℝ u.uncurry (x,t)` to the first factor `ℝ³ → ℝ³ × ℝ`. -/
theorem fderiv_slice_eq {u : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (h : DifferentiableAt ℝ u.uncurry (x, t)) :
    fderiv ℝ (fun y => u y t) x
      = (fderiv ℝ u.uncurry (x, t)) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ) := by
  rw [show (fun y : R3 => u y t) = u.uncurry ∘ (fun y => (y, t)) from rfl]
  rw [fderiv_comp x h (hasFDerivAt_prodMk_left x t).differentiableAt]
  rw [(hasFDerivAt_prodMk_left x t).fderiv]

/-- The vorticity of a slice, through the derivative of the joint field. -/
theorem vorticity_eq_curlOf {u : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (h : DifferentiableAt ℝ u.uncurry (x, t)) :
    vorticity (fun y => u y t) x
      = curlOf ((fderiv ℝ u.uncurry (x, t)) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ)) := by
  simp only [FiniteTimeSingularity.vorticity, curlOf, fderiv_slice_eq h]

/-- **Joint continuity of the vorticity.**  If `u.uncurry` is `C¹` on the closed strip
`ℝ³ × [0,S]` then `(x,s) ↦ ‖vorticity (u · s) x‖` is continuous on the open strip `ℝ³ × (0,S)`:
each point of the latter is an interior point of the closed strip, so `ContDiffOn` upgrades to
`ContDiffAt` and `fderiv ℝ u.uncurry` is continuous there. -/
theorem continuousOn_vorticity_joint {u : R3 → ℝ → R3} {S : ℝ}
    (hcd : ContDiffOn ℝ 1 u.uncurry (Set.univ ×ˢ Set.Icc 0 S)) :
    ContinuousOn (fun p : R3 × ℝ => ‖vorticity (u · p.2) p.1‖) (Set.univ ×ˢ Set.Ioo 0 S) := by
  have hopen : IsOpen (Set.univ ×ˢ Set.Ioo 0 S : Set (R3 × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hcd' : ContDiffOn ℝ 1 u.uncurry (Set.univ ×ˢ Set.Ioo 0 S) :=
    hcd.mono (Set.prod_mono_right Set.Ioo_subset_Icc_self)
  have hderiv : ContinuousOn (fderiv ℝ u.uncurry) (Set.univ ×ˢ Set.Ioo 0 S) :=
    hcd'.continuousOn_fderiv_of_isOpen hopen le_rfl
  have hcomp : ContinuousOn
      (fun p : R3 × ℝ => (fderiv ℝ u.uncurry p) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ))
      (Set.univ ×ˢ Set.Ioo 0 S) :=
    hderiv.clm_comp continuousOn_const
  have hcurl : ContinuousOn
      (fun p : R3 × ℝ => curlOf ((fderiv ℝ u.uncurry p) ∘SL (ContinuousLinearMap.inl ℝ R3 ℝ)))
      (Set.univ ×ˢ Set.Ioo 0 S) :=
    continuous_curlOf.comp_continuousOn hcomp
  refine (hcurl.norm).congr (fun p hp => ?_)
  have hdiff : DifferentiableAt ℝ u.uncurry p :=
    (hcd'.differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds hp)
  rw [vorticity_eq_curlOf hdiff]

end Work.FTS.Top.Integrable
end
-- ===== merged: Submission.Work.FTS.Top.Rescale.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Top

/-! ## The two linear maps -/

/-- The time rescaling `(x,t) ↦ (x, c·t)` of spacetime, as a continuous linear map. -/
def timeCLM (c : ℝ) : (R3 × ℝ) →L[ℝ] (R3 × ℝ) :=
  (ContinuousLinearMap.fst ℝ R3 ℝ).prod (c • ContinuousLinearMap.snd ℝ R3 ℝ)

@[simp] theorem timeCLM_apply (c : ℝ) (z : R3 × ℝ) : timeCLM c z = (z.1, c * z.2) := rfl

/-- The scalar multiplication `y ↦ c • y` on the values, as a continuous linear map. -/
def smulCLM (c : ℝ) : R3 →L[ℝ] R3 := c • ContinuousLinearMap.id ℝ R3

@[simp] theorem smulCLM_apply (c : ℝ) (y : R3) : smulCLM c y = c • y := rfl

/-! ## The rescaled fields -/

/-- **The time-rescaled velocity**: `u₁(x,t) = c·u(x, c·t)`. -/
def timeScale (c : ℝ) (u : R3 → ℝ → R3) : R3 → ℝ → R3 := fun x t => c • u x (c * t)

@[simp] theorem timeScale_apply (c : ℝ) (u : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    timeScale c u x t = c • u x (c * t) := rfl

/-- **The pressure of the time-rescaled solution**: `p₁(x,t) = c²·p(x, c·t)` (the factor `c²` is
what makes `∂ₜu₁ + (u₁·∇)u₁ + ∇p₁ = 0`). -/
def timeScaleP (c : ℝ) (p : R3 → ℝ → ℝ) : R3 → ℝ → ℝ := fun x t => c ^ 2 * p x (c * t)

@[simp] theorem timeScaleP_apply (c : ℝ) (p : R3 → ℝ → ℝ) (x : R3) (t : ℝ) :
    timeScaleP c p x t = c ^ 2 * p x (c * t) := rfl

/-! ## The structural identities

`timeScale c u = smulCLM c ∘ u.uncurry ∘ timeCLM c` and
`timeScaleP c p = (c² ·) ∘ p.uncurry ∘ timeCLM c`: this is exactly the shape of the generic
reparametrisation lemma `Work.SolutionDelivery.Scaling.isContDiffHolderOn_comp_clm`, so the strip
`C^{1,α}` regularity transfers without any new chain rule. -/

theorem timeScale_uncurry (c : ℝ) (u : R3 → ℝ → R3) :
    (timeScale c u).uncurry = fun z : R3 × ℝ => smulCLM c (u.uncurry (timeCLM c z)) := rfl


/-- The strip `ℝ³ × [0,S]` is carried into `ℝ³ × [0, c·S]` by `timeCLM c` when `c ≥ 0`. -/
theorem mapsTo_timeCLM_Icc {c : ℝ} (hc : 0 ≤ c) (S : ℝ) :
    Set.MapsTo (timeCLM c) (Set.univ ×ˢ Set.Icc (0 : ℝ) S)
      (Set.univ ×ˢ Set.Icc (0 : ℝ) (c * S)) := by
  rintro ⟨x, t⟩ ⟨-, ht⟩
  simp only [Set.mem_prod, Set.mem_univ, true_and, timeCLM_apply, Set.mem_Icc] at ht ⊢
  exact ⟨mul_nonneg hc ht.1, mul_le_mul_of_nonneg_left ht.2 hc⟩


/-- Every point of the strip `ℝ³ × [0,S]` with `S > 0` is a point of unique differentiability of
the strip (the spatial factor is all of `ℝ³`, and `Icc 0 S` has nonempty interior). -/
theorem uniqueDiffWithinAt_prod_Icc {S : ℝ} (hS : 0 < S) :
    ∀ z ∈ (Set.univ ×ˢ Set.Icc (0 : ℝ) S : Set (R3 × ℝ)),
      UniqueDiffWithinAt ℝ (Set.univ ×ˢ Set.Icc (0 : ℝ) S) z := by
  rintro ⟨x, t⟩ ⟨-, ht⟩
  exact UniqueDiffWithinAt.prod uniqueDiffWithinAt_univ ((uniqueDiffOn_Icc hS) t ht)

/-! ## Scaling of the fixed differential operators on the values

The time rescaling `timeScale c u = fun x t => c • u x (c·t)` scales the *values* of the field by
`c` and does not touch the space variable.  The three operators of `ChallengeDeps` that are linear
in the field therefore obey unconditional scaling laws (`fderiv_const_smul_field` is
hypothesis-free in Mathlib), which is what makes the Euler equation, the divergence-freeness and
the vorticity decay of the rescaled solution immediate.
-/

/-- The pointwise form of Mathlib's `fderiv_const_smul_field`. -/
theorem fderiv_const_smul_apply (c : ℝ) (v : R3 → R3) (x : R3) :
    fderiv ℝ (fun y => c • v y) x = c • fderiv ℝ v x :=
  congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := v) c) x

/-- **The divergence of a scalar multiple of a field**: `div (c • v) = c · div v`. -/
theorem div_const_smul (c : ℝ) (v : R3 → R3) (x : R3) :
    div (fun y => c • v y) x = c * div v x := by
  simp only [div, fderiv_const_smul_apply, ContinuousLinearMap.toLinearMap_smul, map_smul,
    smul_eq_mul]

/-- **The vorticity of a scalar multiple of a field**: `∇×(c v) = c ∇×v`. -/
theorem vorticity_const_smul (c : ℝ) (v : R3 → R3) :
    vorticity (fun y => c • v y) = fun x => c • vorticity v x := by
  funext x
  have hderiv : fderiv ℝ (fun y => c • v y) x = c • fderiv ℝ v x := fderiv_const_smul_apply c v x
  simp only [FiniteTimeSingularity.vorticity]
  rw [hderiv]
  have hterm : ∀ i : Fin 3,
      crossProduct (FiniteTimeSingularity.e i) ((c • fderiv ℝ v x) (FiniteTimeSingularity.e i))
        = c • crossProduct (FiniteTimeSingularity.e i) (fderiv ℝ v x (FiniteTimeSingularity.e i)) :=
    fun i => by rw [ContinuousLinearMap.smul_apply, WithLp.ofLp_smul, map_smul]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [WithLp.toLp_sum]
  simp only [WithLp.toLp_smul]
  rw [← Finset.smul_sum, ← WithLp.toLp_sum]

/-! ## The scaling laws of the four operators of `ChallengeDeps`

`timeScale c u · t` is literally `fun y => c • (u · (c·t)) y`, so all the *space*-only operators
which are linear in the field are immediate from the value-scaling lemmas above. -/

/-- **`fderiv` of the rescaled slice**: `D_x u₁(·,t) = c · D_xu(·,c t)`. -/
theorem fderiv_timeScale (c : ℝ) (u : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    fderiv ℝ (timeScale c u · t) x = c • fderiv ℝ (u · (c * t)) x :=
  fderiv_const_smul_apply c (u · (c * t)) x

/-- **`div` of the rescaled slice**: `div u₁(·,t) = c · div u(·,c t)`. -/
theorem div_timeScale (c : ℝ) (u : R3 → ℝ → R3) (t : ℝ) :
    div (timeScale c u · t) = fun x => c * div (u · (c * t)) x := by
  funext x
  exact div_const_smul c (u · (c * t)) x

/-- **`vorticity` of the rescaled slice**: `∇×u₁(·,t) = c · (∇×u)(·,c t)`.  (No factor `c²`: the
space variable is *not* rescaled.) -/
theorem vorticity_timeScale (c : ℝ) (u : R3 → ℝ → R3) (t : ℝ) :
    vorticity (timeScale c u · t) = fun x => c • vorticity (u · (c * t)) x :=
  vorticity_const_smul c (u · (c * t))

/-- The convection term of the time-rescaled field: both the field and its derivative are scaled
by `c`, so the product scales by `c²`. -/
theorem directionalDeriv_timeScale (c : ℝ) (u : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    directionalDeriv (timeScale c u) (timeScale c u) x t
      = (c * c) • directionalDeriv u u x (c * t) := by
  have h1 : directionalDeriv (timeScale c u) (timeScale c u) x t
      = (c • fderiv ℝ (u · (c * t)) x) (timeScale c u x t) := by
    rw [directionalDeriv, fderiv_timeScale]
  rw [h1]
  show (c • fderiv ℝ (u · (c * t)) x) (c • u x (c * t))
      = (c * c) • fderiv ℝ (u · (c * t)) x (u x (c * t))
  rw [ContinuousLinearMap.smul_apply, map_smul, smul_smul]

/-- **`timeDeriv` of the rescaled field**: `∂ₜu₁ = c² · (∂ₜu)(·,c t)` (one factor `c` from the
value scaling and one from the chain rule for `t ↦ c·t`). -/
theorem timeDeriv_timeScale (c : ℝ) (u : R3 → ℝ → R3) (x : R3) (t : ℝ)
    (hd : DifferentiableAt ℝ (u x) (c * t)) :
    timeDeriv (timeScale c u) x t = (c * c) • timeDeriv u x (c * t) := by
  have hd1 : DifferentiableAt ℝ (fun s : ℝ => u x (c * s)) t :=
    hd.comp t (hasDerivAt_const_mul c).differentiableAt
  have h2 : timeDeriv (timeScale c u) x t = c • deriv (fun s : ℝ => u x (c * s)) t :=
    deriv_const_smul c hd1
  rw [h2, deriv_comp_mul_left c (u x) t, smul_smul]
  rfl

end Work.FTS.Top
end
-- ===== merged: Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary facts -/

/-- The weight `w` is positive on `(0,∞)`. -/
theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  positivity

/-- `1 ≤ w z` for `z > 0`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith [sq_nonneg z]

/-- The algebraic identity behind the weighted Cauchy–Schwarz step:
`(z h'(z) w(z)) · (z/(1+z)²) = h'(z)` for `z > 0`. -/
theorem w_mul_psi_eq {h' : ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    (z * h' z * Work.Spaces.w z) * (z / (1 + z) ^ 2) = h' z := by
  have h1 : (1 + z) ≠ 0 := ne_of_gt (by linarith)
  have hz' : z ≠ 0 := ne_of_gt hz
  simp only [Work.Spaces.w]
  field_simp

/-! ## The window form of the radial Hardy inequality -/

/-- **The radial Hardy inequality in window form.**  For `0 < z₀ ≤ R₀`, a function `h` of
class `C¹` on `[z₀, 2R₀]` whose square is integrable on `[R₀, 2R₀]`,

  `h(z₀)² ≤ 2 ∫_{z₀}^{2R₀} (z h'(z) w(z))² dz + (2/R₀) ∫_{R₀}^{2R₀} h(z)² dz`.

The second term is the price of the missing decay hypothesis; it is an average over the
window `[R₀, 2R₀]`, hence tends to `0` for fixed `L²`-data as `R₀ → ∞`. -/
theorem half_line_window_bound {h h' : ℝ → ℝ} {z₀ R₀ : ℝ} (hz₀ : 0 < z₀) (hR : z₀ ≤ R₀)
    (hderiv : ∀ x ∈ Set.Icc z₀ (2 * R₀), HasDerivAt h (h' x) x)
    (hcont : ContinuousOn h (Set.Icc R₀ (2 * R₀)))
    (hcont' : ContinuousOn h' (Set.Icc z₀ (2 * R₀)))
    (hint : IntegrableOn (fun x => (h x) ^ 2) (Set.Icc R₀ (2 * R₀))) :
    (h z₀) ^ 2 ≤ 2 * (∫ x in z₀..(2 * R₀), (x * h' x * Work.Spaces.w x) ^ 2)
      + (2 / R₀) * ∫ x in R₀..(2 * R₀), (h x) ^ 2 := by
  have hR₀ : 0 < R₀ := lt_of_lt_of_le hz₀ hR
  have hz2R : z₀ ≤ 2 * R₀ := by linarith
  have hR2R : R₀ ≤ 2 * R₀ := by linarith
  -- the weighted square of the derivative, as an interval integral over the big window
  set P : ℝ := ∫ x in z₀..(2 * R₀), (x * h' x * Work.Spaces.w x) ^ 2 with hPdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact intervalIntegral.integral_nonneg hz2R fun x _ => sq_nonneg _
  -- the "key" bound `(h z₀ - h R)² ≤ P` for every `R ∈ [R₀, 2R₀]`
  have hkey : ∀ R ∈ Set.Icc R₀ (2 * R₀), (h z₀ - h R) ^ 2 ≤ P := by
    intro R hRmem
    have hzR : z₀ ≤ R := le_trans hR hRmem.1
    have hRle : R ≤ 2 * R₀ := hRmem.2
    have hsub' : Set.Icc z₀ R ⊆ Set.Icc z₀ (2 * R₀) := Set.Icc_subset_Icc le_rfl hRle
    -- the weighted derivative is continuous on the big window `[z₀, 2R₀]`
    have hWc : ContinuousOn (fun x => x * h' x * Work.Spaces.w x) (Set.Icc z₀ (2 * R₀)) := by
      refine ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz₀ hx.1))
    have hAc : ContinuousOn (fun x => (x * h' x * Work.Spaces.w x) ^ 2)
        (Set.Icc z₀ (2 * R₀)) := hWc.pow 2
    -- the two factors of the Cauchy–Schwarz step are continuous on `[z₀,R]`
    have hcontA : ContinuousOn (fun x => x * h' x * Work.Spaces.w x) (Set.uIcc z₀ R) := by
      rw [Set.uIcc_of_le hzR]
      exact hWc.mono hsub'
    have hcontψ : ContinuousOn (fun x => x / (1 + x) ^ 2) (Set.uIcc z₀ R) := by
      rw [Set.uIcc_of_le hzR]
      refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.1]))
    -- the fundamental theorem of calculus
    have hFTC : ∫ x in z₀..R, h' x = h R - h z₀ := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
      · intro x hx
        rw [Set.uIcc_of_le hzR] at hx
        exact hderiv x ⟨hx.1, le_trans hx.2 hRle⟩
      · refine (show ContinuousOn h' (Set.uIcc z₀ R) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hzR]
        exact hcont'.mono hsub'
    -- the Cauchy–Schwarz inequality for the interval integral
    have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt z₀ R hzR hcontA hcontψ
    -- the product is the derivative
    have hcongr : ∫ x in z₀..R, (x * h' x * Work.Spaces.w x) * (x / (1 + x) ^ 2)
        = ∫ x in z₀..R, h' x := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le hzR] at hx
      exact w_mul_psi_eq (lt_of_lt_of_le hz₀ hx.1)
    -- the `ψ`-factor has mass at most one
    have hpsi : ∫ x in z₀..R, (x / (1 + x) ^ 2) ^ 2 ≤ 1 :=
      Work.Spaces.hardyZ_integral_psi_sq_le_one hz₀.le hzR
    -- the first factor is dominated by `P`
    have hAint : IntervalIntegrable (fun x => (x * h' x * Work.Spaces.w x) ^ 2)
        volume z₀ (2 * R₀) := by
      refine (show ContinuousOn (fun x => (x * h' x * Work.Spaces.w x) ^ 2)
        (Set.uIcc z₀ (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hz2R]
      exact hAc
    have hA : ∫ x in z₀..R, (x * h' x * Work.Spaces.w x) ^ 2 ≤ P := by
      rw [hPdef]
      exact intervalIntegral.integral_mono_interval le_rfl hzR hRle
        (Filter.Eventually.of_forall fun x => sq_nonneg _) hAint
    have hsq : (h z₀ - h R) ^ 2 ≤ P := by
      have h1 : (h z₀ - h R) ^ 2
          = (∫ x in z₀..R, (x * h' x * Work.Spaces.w x) * (x / (1 + x) ^ 2)) ^ 2 := by
        rw [hcongr, hFTC]
        ring
      have hAfnn : 0 ≤ ∫ x in z₀..R, (x * h' x * Work.Spaces.w x) ^ 2 :=
        intervalIntegral.integral_nonneg hzR fun x _ => sq_nonneg _
      have hBnn : 0 ≤ ∫ x in z₀..R, (x / (1 + x) ^ 2) ^ 2 :=
        intervalIntegral.integral_nonneg hzR fun x _ => sq_nonneg _
      have h2 : (∫ x in z₀..R, (x * h' x * Work.Spaces.w x) * (x / (1 + x) ^ 2)) ^ 2
          = |∫ x in z₀..R, (x * h' x * Work.Spaces.w x) * (x / (1 + x) ^ 2)| ^ 2 := by
        rw [sq_abs]
      rw [h1, h2]
      have h3 : |∫ x in z₀..R, (x * h' x * Work.Spaces.w x) * (x / (1 + x) ^ 2)| ^ 2
          ≤ (Real.sqrt (∫ x in z₀..R, (x * h' x * Work.Spaces.w x) ^ 2)) ^ 2
            * (Real.sqrt (∫ x in z₀..R, (x / (1 + x) ^ 2) ^ 2)) ^ 2 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) hcs 2
      rw [Real.sq_sqrt hAfnn, Real.sq_sqrt hBnn] at h3
      nlinarith [h3, hA, hpsi, hAfnn, hPnn]
    exact hsq
  -- average the pointwise bound over the window
  have hpt : ∀ R ∈ Set.Icc R₀ (2 * R₀), (h z₀) ^ 2 ≤ 2 * P + 2 * (h R) ^ 2 := by
    intro R hRmem
    have h1 : (h z₀) ^ 2 ≤ 2 * (h z₀ - h R) ^ 2 + 2 * (h R) ^ 2 :=
      by nlinarith [sq_nonneg (h z₀ - 2 * h R)]
    nlinarith [h1, hkey R hRmem]
  -- interval integrability of the two sides
  have hIntL : IntervalIntegrable (fun _ : ℝ => (h z₀) ^ 2) volume R₀ (2 * R₀) :=
    intervalIntegrable_const
  have hcontR : ContinuousOn (fun x : ℝ => 2 * P + 2 * (h x) ^ 2) (Set.Icc R₀ (2 * R₀)) :=
    continuousOn_const.add ((continuousOn_const.mul (hcont.pow 2)))
  have hIntR : IntervalIntegrable (fun x : ℝ => 2 * P + 2 * (h x) ^ 2) volume R₀ (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => 2 * P + 2 * (h x) ^ 2)
      (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact hcontR
  have hmono := intervalIntegral.integral_mono_on hR2R hIntL hIntR (fun x hx => hpt x hx)
  -- compute the two interval integrals
  have hL : ∫ x in R₀..(2 * R₀), (h z₀) ^ 2 = (h z₀) ^ 2 * R₀ := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hIntC : IntervalIntegrable (fun _ : ℝ => 2 * P) volume R₀ (2 * R₀) :=
    intervalIntegrable_const
  have hIntH : IntervalIntegrable (fun x : ℝ => 2 * (h x) ^ 2) volume R₀ (2 * R₀) := by
    refine (show ContinuousOn (fun x : ℝ => 2 * (h x) ^ 2) (Set.uIcc R₀ (2 * R₀)) from ?_)
      |>.intervalIntegrable
    rw [Set.uIcc_of_le hR2R]
    exact (hcont.pow 2).const_mul 2
  have hRint : ∫ x in R₀..(2 * R₀), (2 * P + 2 * (h x) ^ 2)
      = 2 * P * R₀ + 2 * ∫ x in R₀..(2 * R₀), (h x) ^ 2 := by
    rw [intervalIntegral.integral_add hIntC hIntH, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, smul_eq_mul]
    ring
  rw [hL, hRint] at hmono
  -- divide by `R₀`
  have hQnn : 0 ≤ ∫ x in R₀..(2 * R₀), (h x) ^ 2 :=
    intervalIntegral.integral_nonneg hR2R fun x _ => sq_nonneg _
  have hid : 2 * P + (2 / R₀) * (∫ x in R₀..(2 * R₀), (h x) ^ 2)
      = (2 * P * R₀ + 2 * (∫ x in R₀..(2 * R₀), (h x) ^ 2)) / R₀ := by
    field_simp
  rw [hid, le_div_iff₀ hR₀]
  linarith [hmono]

end Work.FTS.TransportS
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ThetaJets.thetaTraces_one_of =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ThetaJets.thetaTraces_one_of` (lead install R6, 2026-10-11)

`ThetaTraces α k g → ThetaTraces 1 k g` for `α ≥ 1`: `γ(1) ≤ γ(α)`, so on `sin 2θ ∈ (0,1]`,
`sin^{1-γ(1)} ≤ sin^{1-γ(α)}` (the θ-part of `bdryTraces_one_of`).  Feeds the `thTr` field in
`classC_one_of` (`ThetaJets/ClassC_le.lean`).
-/

noncomputable section
open scoped Real Topology
open Filter

namespace Work.FTS_EllLimOK.ThetaJets

theorem thetaTraces_one_of {α : ℝ} (hα : 1 ≤ α) {k : ℕ} {g : ℝ → ℝ → ℝ}
    (htr : Work.FTS.PhiStar.ThetaTraces α k g) : Work.FTS.PhiStar.ThetaTraces 1 k g := by
  intro s hs z hz
  obtain ⟨h3, h4⟩ := htr s hs z hz
  have hgam : Work.Spaces.gam 1 ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam, Work.Spaces.gam]; linarith
  constructor
  · refine squeeze_zero' ?_ ?_ h3
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))) _) (sq_nonneg _)
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact Real.rpow_le_rpow_of_exponent_ge
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
        (Real.sin_le_one _) (by linarith)
  · refine squeeze_zero' ?_ ?_ h4
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))) _) (sq_nonneg _)
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact Real.rpow_le_rpow_of_exponent_ge
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
        (Real.sin_le_one _) (by linarith)

end Work.FTS_EllLimOK.ThetaJets
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.AgmonND.hasDerivAt_agmonF =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise derivative of `agmonF v`

`agmonF v x = x * (v x * w x) ^ 2` with `w x = (1 + x) ^ 2 / x ^ 2`.  On `(0, ∞)` this is
`(v x) ^ 2 * (1 + x) ^ 4 / x ^ 3`, and differentiating that rational expression gives the
function `agmonFderiv v v'` whenever `v` has derivative `v'` on `(0, ∞)`.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.AgmonND

theorem hasDerivAt_agmonF {v v' : ℝ → ℝ}
    (hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt v (v' x) x) :
    ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.FTS_RegExport.RXT.agmonF v)
        (Work.FTS_RegExport.RXT.agmonFderiv v v' x) x := by
  intro x hx
  have hx0 : 0 < x := hx
  have hxne : x ≠ 0 := ne_of_gt hx0
  have h1x : (1 : ℝ) + x ≠ 0 := by positivity
  -- On a neighbourhood of `x > 0`, `agmonF v` is the rational function `v²(1+y)⁴/y³`.
  have hev : Work.FTS_RegExport.RXT.agmonF v =ᶠ[𝓝 x]
      fun y : ℝ => (v y) ^ 2 * (1 + y) ^ 4 / y ^ 3 := by
    filter_upwards [isOpen_Ioi.mem_nhds hx0] with y hy
    have hyne : y ≠ 0 := ne_of_gt hy
    simp only [Work.FTS_RegExport.RXT.agmonF, Work.Spaces.w]
    field_simp
  have hv2 : HasDerivAt (fun y : ℝ => (v y) ^ 2) (2 * v x * v' x) x := by
    have h := (hderiv x hx).pow 2
    convert h using 1 <;> ring
  have h1xy : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    have h := (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
    convert h using 1
    · funext y; simp
    · simp
  have hp : HasDerivAt (fun y : ℝ => (1 + y) ^ 4) (4 * (1 + x) ^ 3) x := by
    have h := h1xy.pow 4
    convert h using 1 <;> ring
  have hden : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    have h := (hasDerivAt_id x).pow 3
    convert h using 1
    · funext y; rfl
    · simp
  have hnum : HasDerivAt (fun y : ℝ => (v y) ^ 2 * (1 + y) ^ 4)
      (2 * v x * v' x * (1 + x) ^ 4 + (v x) ^ 2 * (4 * (1 + x) ^ 3)) x := by
    have h := hv2.mul hp
    convert h using 1 <;> ring
  have hq := hnum.div hden (pow_ne_zero 3 hxne)
  refine (hev.hasDerivAt_iff).mpr ?_
  convert hq using 1
  rw [Work.FTS_RegExport.RXT.agmonFderiv]
  simp only [Work.Spaces.w]
  field_simp <;> ring

end Work.FTS_RegExport.RXT.AgmonND
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Angular.cs_weighted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Angular

theorem cs_weighted {γ : ℝ} (hγ : 1 < γ) {g' : ℝ → ℝ}
    (hmes : MeasureTheory.AEStronglyMeasurable g'
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hint2 : MeasureTheory.IntegrableOn
      (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    (hWv : IntervalIntegrable (fun θ => (Real.sin (2 * θ)) ^ (γ - 2))
      MeasureTheory.volume 0 (Real.pi / 2))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    (∫ x in a..b, |g' x|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (γ - 2)) :=
  Work.FTS_RXTPieces.Angular.cs_weighted hγ hmes hint2 hWv ha hab hb

end Work.FTS_RegExport.RXT.Angular
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Angular.integral_deriv_eq_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Angular

theorem integral_deriv_eq_sub {γ : ℝ} (hγ : 1 < γ) {g g' : ℝ → ℝ}
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (g' θ) θ)
    (hint2 : MeasureTheory.IntegrableOn
      (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    ∫ x in a..b, g' x = g b - g a :=
  Work.FTS_RXTPieces.Angular.integral_deriv_eq_sub hγ hg hint2 ha hab hb

end Work.FTS_RegExport.RXT.Angular
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Angular.meanValue =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Angular

theorem meanValue {g : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ => g θ ^ 2) Work.Spaces.Iθ) :
    ∃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      2 * g t ^ 2 ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, g θ ^ 2) :=
  Work.FTS_RXTPieces.Angular.meanValue hint

end Work.FTS_RegExport.RXT.Angular
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.noDecayPieces.agmonF_deriv_bnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.noDecayPieces

theorem agmonF_deriv_bnd {v v' : ℝ → ℝ}
    (hv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt v (v' x) x) :
    ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => y * (v y * Work.Spaces.w y) ^ 2)
        (2 * v x * (x * v' x) * (Work.Spaces.w x) ^ 2
          + (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))) x
      ∧ |2 * v x * (x * v' x) * (Work.Spaces.w x) ^ 2
            + (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))|
          ≤ 4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2 :=
  Work.FTS_RXTPieces.noDecayPieces.agmonF_deriv_bnd hv

end Work.FTS_RegExport.RXT.noDecayPieces
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.noDecayPieces.sq_le_of_profile_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.noDecayPieces

theorem sq_le_of_profile_le {v : ℝ → ℝ} {z K : ℝ} (hz : 0 < z) (hK : 0 ≤ K)
    (h : z * (v z * Work.Spaces.w z) ^ 2 ≤ K) :
    v z ^ 2 ≤ K * (min z 1) ^ 2 :=
  Work.FTS_RXTPieces.noDecayPieces.sq_le_of_profile_le hz hK h

end Work.FTS_RegExport.RXT.noDecayPieces
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.st1_fb_dz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open Set Filter
open scoped Real Topology

namespace Work.FTS_RegExport.RXT

theorem dziter_two_fb {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    Work.Spaces.DzIter 2 f z θ = z * Work.Spaces.pz f z θ
      + z ^ 2 * Work.Spaces.pz (Work.Spaces.pz f) z θ := by
  -- `∂_zf(·,θ)` is (eventually near `z`) the `(1,0)`-evaluation of `fderiv (uncurry f)`
  set Φ : ℝ × ℝ → ℝ := fun p => (fderiv ℝ (Function.uncurry f) p) (1, 0) with hΦ
  have hΦeq : Φ = (ContinuousLinearMap.apply ℝ ℝ (1, 0))
      ∘ (fderiv ℝ (Function.uncurry f)) := by
    funext p
    simp only [hΦ, Function.comp_apply, ContinuousLinearMap.apply_apply]
  have hfd_diff : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry f)) (z, θ) :=
    (h.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hΦdiff : DifferentiableAt ℝ Φ (z, θ) := by
    rw [hΦeq]
    exact (ContinuousLinearMap.apply ℝ ℝ (1, 0)).differentiableAt.comp (z, θ) hfd_diff
  have hnd : ∀ᶠ y in 𝓝 (z, θ), DifferentiableAt ℝ (Function.uncurry f) y :=
    (h.eventually (by decide : (2 : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞))).mono
      (fun y hy => hy.differentiableAt (by norm_num))
  have hθ : ∀ᶠ t in 𝓝 z, DifferentiableAt ℝ (Function.uncurry f) (t, θ) :=
    (Continuous.prodMk_left θ).continuousAt.eventually hnd
  have hslice : (fun t : ℝ => Work.Spaces.pz f t θ) =ᶠ[𝓝 z] (fun t => Φ (t, θ)) := by
    filter_upwards [hθ] with t ht
    exact Work.Spaces.deriv_slice_fst (Function.uncurry f) t θ ht
  have hd1 : DifferentiableAt ℝ (fun t : ℝ => Φ (t, θ)) z := by
    show DifferentiableAt ℝ (Φ ∘ fun t : ℝ => (t, θ)) z
    exact hΦdiff.comp z (hasFDerivAt_prodMk_left z θ).differentiableAt
  have hdiff : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pz f t θ) z :=
    hd1.congr_of_eventuallyEq hslice
  have hderiv : deriv (fun t : ℝ => t * Work.Spaces.pz f t θ) z
      = Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ := by
    have h3 := (hasDerivAt_id z).mul hdiff.hasDerivAt
    have h4 : HasDerivAt ((fun t : ℝ => t) * (fun t : ℝ => Work.Spaces.pz f t θ))
        (Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ) z :=
      h3.congr_deriv (by rw [one_mul, id_eq]; rfl)
    exact h4.deriv
  show z * deriv (fun t : ℝ => t * Work.Spaces.pz f t θ) z = _
  rw [hderiv]; ring

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.H2.T1Q.IbpCutoff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.H2.T1Q.IbpCutoff`

The angular integration by parts that localises the "hard" (order-five) angular terms of
Elgindi's `Transport1`/`SpecialTransport` pairing to a compact subinterval of `(0, π/2)`.

For `χ` smooth and vanishing off `[δ, π/2-δ]` (`0 < δ ≤ π/4`) and `hf`, `hv` of class `C¹` on
the open interval `(0, π/2)`, the identity

  `∫_θ sin(2θ)^{-q}·(χ hf)·(sin(2θ)·hv')·hv
      = -∫_θ sin(2θ)^{-q}·(χ·((1/2) sin(2θ) hf' + (1-q) cos(2θ) hf)
                              + (1/2) sin(2θ) χ' hf)·hv²`

holds with *both* sides integrable.  Because the cutoff `χ` vanishes identically off
`[δ, π/2-δ] ⊂ (0, π/2)`, the boundary terms of the integration by parts vanish exactly (not
merely in the limit) and no boundary regularity of `hf`, `hv` is needed at `0` or `π/2`.

The proof has three parts, all in the file:

* `ibpCutoff_integrable` — both integrands are supported in `[δ, π/2-δ]` (`χ` vanishes off it,
  and `deriv χ` vanishes wherever `χ` is locally `0`) and continuous there, hence integrable on
  `Iθ = [0, π/2]`;
* `ibpCutoff_deriv` — on `(0, π/2)` the primitive `IbpPrim q χ hf hv` has derivative
  `IbpG q χ hf hv + IbpK q χ hf hv`;
* the fundamental theorem of calculus on `[0, π/2]` in its one-sided/tendsto form, the boundary
  terms of the primitive vanishing (`ibpCutoff_prim_tendsto_zero_right/left`).

The objects `IbpG`, `IbpK`, `IbpPrim` live in `Submission.Work.H2.T1Q.IbpCutoffDefs`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

/-- `sin (2θ) > 0` on the open interval `(0, π/2)`. -/
lemma ibpCutoff_sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- A function vanishing off the compact interval `[a,b] ⊂ (0, π/2)` and continuous there is
integrable on `Iθ = [0, π/2]`. -/
lemma ibpCutoff_integrableOn_Iθ_of_continuousOn_Icc {a b : ℝ} (ha : 0 < a) (hb : b < π / 2)
    {f : ℝ → ℝ} (hvan : ∀ θ : ℝ, θ ∉ Set.Icc a b → f θ = 0)
    (hcont : ContinuousOn f (Set.Icc a b)) : IntegrableOn f Work.Spaces.Iθ := by
  have hsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) (π / 2) :=
    fun θ hθ => ⟨by linarith [hθ.1, ha], by linarith [hθ.2, hb, Real.pi_pos]⟩
  have h1 : IntegrableOn f (Set.Icc a b) := hcont.integrableOn_compact isCompact_Icc
  have h2 : IntegrableOn f (Set.Icc (0 : ℝ) (π / 2) \ Set.Icc a b) := by
    refine IntegrableOn.congr_fun (f := fun _ : ℝ => (0 : ℝ)) integrableOn_zero ?_ ?_
    · intro x hx
      exact (hvan x hx.2).symm
    · exact measurableSet_Icc.diff measurableSet_Icc
  have h3 : IntegrableOn f (Set.Icc a b ∪ (Set.Icc (0 : ℝ) (π / 2) \ Set.Icc a b)) :=
    h1.union h2
  rwa [Set.union_sdiff_cancel hsub] at h3

/-- `deriv χ` vanishes at every point where `χ` is locally `0`. -/
lemma ibpCutoff_deriv_eq_zero_of_eventually_eq_zero {χ : ℝ → ℝ} {θ : ℝ}
    (h : χ =ᶠ[𝓝 θ] (fun _ : ℝ => (0 : ℝ))) : deriv χ θ = 0 := by
  rw [h.deriv_eq, deriv_const]

/-- **The primitive.**  On the open interval `(0, π/2)` the derivative of the primitive
`IbpPrim q χ hf hv` is `IbpG q χ hf hv + IbpK q χ hf hv`. -/
lemma ibpCutoff_deriv {q : ℝ} {χ hf hv : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (hχ : DifferentiableAt ℝ χ θ) (hhf : DifferentiableAt ℝ hf θ) (hhv : DifferentiableAt ℝ hv θ) :
    HasDerivAt (IbpPrim q χ hf hv) (IbpG q χ hf hv θ + IbpK q χ hf hv θ) θ := by
  have hsin : 0 < Real.sin (2 * θ) := ibpCutoff_sin_two_pos hθ
  have hsinne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsin
  have hs2 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    simpa only [Function.comp_def, mul_comm] using h
  have hpow : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (1 - q))
      ((1 - q) * (Real.sin (2 * θ)) ^ (1 - q - 1) * (2 * Real.cos (2 * θ))) θ := by
    have h := (Real.hasDerivAt_rpow_const (x := Real.sin (2 * θ)) (p := 1 - q)
      (Or.inl hsinne)).comp θ hs2
    simpa only [Function.comp_def] using h
  have hdχ : HasDerivAt χ (deriv χ θ) θ := hχ.hasDerivAt
  have hdhf : HasDerivAt hf (deriv hf θ) θ := hhf.hasDerivAt
  have hdhv : HasDerivAt hv (deriv hv θ) θ := hhv.hasDerivAt
  have hχhf : HasDerivAt (fun t => χ t * hf t) (deriv χ θ * hf θ + χ θ * deriv hf θ) θ :=
    hdχ.mul hdhf
  have hv2 : HasDerivAt (fun t : ℝ => (hv t) ^ 2) (2 * hv θ * deriv hv θ) θ := by
    have h : HasDerivAt (fun t : ℝ => hv t * hv t)
        (deriv hv θ * hv θ + hv θ * deriv hv θ) θ := hdhv.mul hdhv
    convert h using 1
    · funext t; ring
    · ring
  have h1 : HasDerivAt (fun t => (1 / 2) * (Real.sin (2 * t)) ^ (1 - q))
      ((1 / 2) * ((1 - q) * (Real.sin (2 * θ)) ^ (1 - q - 1) * (2 * Real.cos (2 * θ)))) θ :=
    hpow.const_mul (1 / 2)
  have h2 : HasDerivAt (fun t => (1 / 2) * (Real.sin (2 * t)) ^ (1 - q) * (χ t * hf t))
      ((1 / 2) * ((1 - q) * (Real.sin (2 * θ)) ^ (1 - q - 1) * (2 * Real.cos (2 * θ)))
          * (χ θ * hf θ)
        + (1 / 2) * (Real.sin (2 * θ)) ^ (1 - q) * (deriv χ θ * hf θ + χ θ * deriv hf θ)) θ :=
    h1.mul hχhf
  have h3 : HasDerivAt
      (fun t => (1 / 2) * (Real.sin (2 * t)) ^ (1 - q) * (χ t * hf t) * (hv t) ^ 2)
      (((1 / 2) * ((1 - q) * (Real.sin (2 * θ)) ^ (1 - q - 1) * (2 * Real.cos (2 * θ)))
            * (χ θ * hf θ)
          + (1 / 2) * (Real.sin (2 * θ)) ^ (1 - q) * (deriv χ θ * hf θ + χ θ * deriv hf θ))
          * (hv θ) ^ 2
        + ((1 / 2) * (Real.sin (2 * θ)) ^ (1 - q) * (χ θ * hf θ))
            * (2 * hv θ * deriv hv θ)) θ :=
    h2.mul hv2
  have hA : (Real.sin (2 * θ)) ^ (-q) = (Real.sin (2 * θ)) ^ (1 - q - 1) := by
    rw [show (1 : ℝ) - q - 1 = -q by ring]
  have hB : (Real.sin (2 * θ)) ^ (1 - q)
      = (Real.sin (2 * θ)) ^ (1 - q - 1) * Real.sin (2 * θ) := by
    have h1 : (Real.sin (2 * θ)) ^ (1 - q - 1) * Real.sin (2 * θ)
        = (Real.sin (2 * θ)) ^ (1 - q - 1) * (Real.sin (2 * θ)) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    rw [h1, ← Real.rpow_add hsin, show (1 : ℝ) - q - 1 + 1 = 1 - q by ring]
  have hval : ((1 / 2) * ((1 - q) * (Real.sin (2 * θ)) ^ (1 - q - 1) * (2 * Real.cos (2 * θ)))
          * (χ θ * hf θ)
        + (1 / 2) * (Real.sin (2 * θ)) ^ (1 - q) * (deriv χ θ * hf θ + χ θ * deriv hf θ))
        * (hv θ) ^ 2
        + ((1 / 2) * (Real.sin (2 * θ)) ^ (1 - q) * (χ θ * hf θ))
            * (2 * hv θ * deriv hv θ)
      = IbpG q χ hf hv θ + IbpK q χ hf hv θ := by
    simp only [IbpG, IbpK]
    rw [hA, hB]
    ring
  rw [hval] at h3
  exact h3

/-- **Integrability.**  Both integrands of `IbpCutoff` are integrable on `Iθ`: the cutoff `χ`
localises them to the compact subinterval `[δ, π/2-δ] ⊂ (0, π/2)`, on which every factor is
continuous. -/
lemma ibpCutoff_integrable {q : ℝ} {χ hf hv : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ π / 4)
    (hχ0 : ∀ θ : ℝ, θ ≤ δ → χ θ = 0)
    (hχ2 : ∀ θ : ℝ, π / 2 - δ ≤ θ → χ θ = 0)
    (hf' : ContDiffOn ℝ 1 hf (Set.Ioo 0 (π / 2)))
    (hv' : ContDiffOn ℝ 1 hv (Set.Ioo 0 (π / 2))) :
    IntegrableOn (IbpG q χ hf hv) Work.Spaces.Iθ
      ∧ IntegrableOn (IbpK q χ hf hv) Work.Spaces.Iθ := by
  set K : Set ℝ := Set.Icc δ (π / 2 - δ) with hK
  have : δ ≤ π / 2 - δ := by linarith [hδ4, Real.pi_pos]
  have hbpi : π / 2 - δ < π / 2 := by linarith [hδ]
  have hIcc_sub : K ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
    intro θ hθ
    exact ⟨by linarith [hθ.1, hδ], by linarith [hθ.2, hδ]⟩
  have hχvan : ∀ θ : ℝ, θ ∉ K → χ θ = 0 := by
    intro θ hθ
    rw [hK, Set.mem_Icc, not_and_or] at hθ
    rcases hθ with h | h
    · exact hχ0 θ (le_of_lt (not_le.mp h))
    · exact hχ2 θ (le_of_lt (not_le.mp h))
  have hdχvan : ∀ θ : ℝ, θ ∉ K → deriv χ θ = 0 := by
    intro θ hθ
    rw [hK, Set.mem_Icc, not_and_or] at hθ
    refine ibpCutoff_deriv_eq_zero_of_eventually_eq_zero ?_
    rcases hθ with h | h
    · filter_upwards [isOpen_Iio.mem_nhds (not_le.mp h)] with t ht
      exact hχ0 t (le_of_lt ht)
    · filter_upwards [isOpen_Ioi.mem_nhds (not_le.mp h)] with t ht
      exact hχ2 t (le_of_lt ht)
  have hsin2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) K :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcos2 : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) K :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hA : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)) K :=
    hsin2.rpow_const (fun x hx => Or.inl (ne_of_gt (ibpCutoff_sin_two_pos (hIcc_sub hx))))
  have hχcont : ContinuousOn χ K := hχ.continuous.continuousOn
  have hχdcont : ContinuousOn (deriv χ) K := (hχ.continuous_deriv (by simp)).continuousOn
  have hfcont : ContinuousOn hf K := hf'.continuousOn.mono hIcc_sub
  have hvcont : ContinuousOn hv K := hv'.continuousOn.mono hIcc_sub
  have hdhfcont : ContinuousOn (fun θ : ℝ => deriv hf θ) K :=
    (hf'.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hIcc_sub
  have hdhvcont : ContinuousOn (fun θ : ℝ => deriv hv θ) K :=
    (hv'.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hIcc_sub
  have hv2cont : ContinuousOn (fun θ : ℝ => (hv θ) ^ 2) K := hvcont.pow 2
  have hvanG : ∀ θ : ℝ, θ ∉ K → IbpG q χ hf hv θ = 0 := by
    intro θ hθ
    show (Real.sin (2 * θ)) ^ (-q) * (χ θ * hf θ) * (Real.sin (2 * θ) * deriv hv θ) * hv θ = 0
    rw [hχvan θ hθ]
    ring
  have hvanK : ∀ θ : ℝ, θ ∉ K → IbpK q χ hf hv θ = 0 := by
    intro θ hθ
    show (Real.sin (2 * θ)) ^ (-q)
        * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv hf θ)
              + (1 - q) * Real.cos (2 * θ) * hf θ)
            + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * hf θ)
        * (hv θ) ^ 2 = 0
    rw [hχvan θ hθ, hdχvan θ hθ]
    ring
  have ht1 : ContinuousOn (fun θ : ℝ => (1 / 2) * (Real.sin (2 * θ) * deriv hf θ)
      + (1 - q) * Real.cos (2 * θ) * hf θ) K :=
    ((hsin2.mul hdhfcont).const_mul (1 / 2)).add ((hcos2.const_mul (1 - q)).mul hfcont)
  have ht2 : ContinuousOn (fun θ : ℝ => (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * hf θ) K :=
    ((hsin2.mul hχdcont).const_mul (1 / 2)).mul hfcont
  have hcontG : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q) * (χ θ * hf θ)
      * (Real.sin (2 * θ) * deriv hv θ) * hv θ) K :=
    ((hA.mul (hχcont.mul hfcont)).mul (hsin2.mul hdhvcont)).mul hvcont
  have hcontK : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)
      * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv hf θ)
            + (1 - q) * Real.cos (2 * θ) * hf θ)
          + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * hf θ)
      * (hv θ) ^ 2) K :=
    (hA.mul ((hχcont.mul ht1).add ht2)).mul hv2cont
  exact ⟨ibpCutoff_integrableOn_Iθ_of_continuousOn_Icc hδ hbpi hvanG hcontG,
    ibpCutoff_integrableOn_Iθ_of_continuousOn_Icc hδ hbpi hvanK hcontK⟩

/-- The primitive vanishes at `0⁺`, because `χ = 0` on `[0, δ]`. -/
lemma ibpCutoff_prim_tendsto_zero_right {q : ℝ} {χ hf hv : ℝ → ℝ}
    {δ : ℝ} (hδ : 0 < δ) (hχ0 : ∀ θ : ℝ, θ ≤ δ → χ θ = 0) :
    Tendsto (IbpPrim q χ hf hv) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)] (IbpPrim q χ hf hv) := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with θ hθ
    simp only [IbpPrim]
    rw [hχ0 θ (le_of_lt hθ.2)]
    ring
  exact Tendsto.congr' hev tendsto_const_nhds

/-- The primitive vanishes at `(π/2)⁻`, because `χ = 0` on `[π/2-δ, π/2]`. -/
lemma ibpCutoff_prim_tendsto_zero_left {q : ℝ} {χ hf hv : ℝ → ℝ}
    {δ : ℝ} (hδ : 0 < δ) (hχ2 : ∀ θ : ℝ, π / 2 - δ ≤ θ → χ θ = 0) :
    Tendsto (IbpPrim q χ hf hv) (𝓝[<] (π / 2)) (𝓝 0) := by
  have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[<] (π / 2)] (IbpPrim q χ hf hv) := by
    filter_upwards [Ioo_mem_nhdsLT (show π / 2 - δ < π / 2 by linarith [hδ])] with θ hθ
    simp only [IbpPrim]
    rw [hχ2 θ (le_of_lt hθ.1)]
    ring
  exact Tendsto.congr' hev tendsto_const_nhds


end Work.H2.T1Q
end
end

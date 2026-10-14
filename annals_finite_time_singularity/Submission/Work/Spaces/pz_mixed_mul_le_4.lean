import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Constructible
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.FTS.PhiStar.Series.psiTrunc_solves
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.scoef_sum_shift
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.thD_reindex
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.sphere_integral_kDerivCLM_angular =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory

theorem sphere_integral_kDerivCLM_angular :
    (∫ ω : Metric.sphere (0 : Work.LWP.R3) 1,
        (ContinuousLinearMap.id ℝ Work.LWP.R3
          - (3 : ℝ) • (innerSL ℝ (ω : Work.LWP.R3)).smulRight (ω : Work.LWP.R3))
      ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere) = 0 := by
  -- Integrability of the continuous, compactly supported integrand.
  have hcont : Continuous (fun ω : Metric.sphere (0 : Work.LWP.R3) 1 =>
        (ContinuousLinearMap.id ℝ Work.LWP.R3
          - (3 : ℝ) • (innerSL ℝ (ω : Work.LWP.R3)).smulRight (ω : Work.LWP.R3))) := by
    fun_prop
  have hint : Integrable (fun ω : Metric.sphere (0 : Work.LWP.R3) 1 =>
        (ContinuousLinearMap.id ℝ Work.LWP.R3
          - (3 : ℝ) • (innerSL ℝ (ω : Work.LWP.R3)).smulRight (ω : Work.LWP.R3)))
      ((MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere) := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
    exact Integrable.of_bound hcont.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => hC ω (Set.mem_univ ω))
  -- The total mass of the sphere: `σ(univ) = 3 · |B₁| = 3 · (4π/3) = 4π`.
  have hmass : ((MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere).real Set.univ
      = 4 * Real.pi := by
    rw [Measure.toSphere_real_apply_univ]
    have hfr : (Module.finrank ℝ Work.LWP.R3 : ℝ) = 3 := by
      simp [Work.LWP.R3, finrank_euclideanSpace]
    have hball : (MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).real
        (Metric.ball (0 : Work.LWP.R3) 1) = Real.pi * 4 / 3 := by
      rw [Measure.real_def, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
        ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1),
        ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ Real.pi * 4 / 3)]
      norm_num
    rw [hfr, hball]; ring
  -- Test the integral against an arbitrary vector `y`.
  apply ContinuousLinearMap.ext
  intro y
  rw [ContinuousLinearMap.integral_apply hint y]
  simp only [zero_apply]
  simp only [sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply]
  have hf1 : Integrable (fun _ : Metric.sphere (0 : Work.LWP.R3) 1 => y)
      ((MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere) := integrable_const y
  have hf3 : Integrable (fun ω : Metric.sphere (0 : Work.LWP.R3) 1 =>
      (3 : ℝ) • (inner ℝ (ω : Work.LWP.R3) y • (ω : Work.LWP.R3)))
      ((MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere) := by
    have hc : Continuous (fun ω : Metric.sphere (0 : Work.LWP.R3) 1 =>
        (3 : ℝ) • (inner ℝ (ω : Work.LWP.R3) y • (ω : Work.LWP.R3))) := by fun_prop
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
    exact Integrable.of_bound hc.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => hC ω (Set.mem_univ ω))
  -- The vector second moment of the sphere.
  have hcomp : (∫ ω : Metric.sphere (0 : Work.LWP.R3) 1,
        inner ℝ (ω : Work.LWP.R3) y • (ω : Work.LWP.R3)
        ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere)
      = (4 * Real.pi / 3) • y := by
    rw [show (∫ ω : Metric.sphere (0 : Work.LWP.R3) 1,
          inner ℝ (ω : Work.LWP.R3) y • (ω : Work.LWP.R3)
          ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere)
        = (∫ ω : Metric.sphere (0 : Work.LWP.R3) 1,
          inner ℝ y (ω : Work.LWP.R3) • (ω : Work.LWP.R3)
          ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere) from
        integral_congr_ae (Filter.Eventually.of_forall fun ω => by
          simp only [real_inner_comm y (ω : Work.LWP.R3)])]
    exact KfBall.sphere_integral_inner_smul y
  -- Linearity of the Bochner integral splits the integrand into the two pieces.
  rw [show (∫ ω : Metric.sphere (0 : Work.LWP.R3) 1,
        (y - (3 : ℝ) • (inner ℝ (ω : Work.LWP.R3) y • (ω : Work.LWP.R3)))
        ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere)
      = (∫ ω : Metric.sphere (0 : Work.LWP.R3) 1, y
          ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere)
        - (∫ ω : Metric.sphere (0 : Work.LWP.R3) 1,
            (3 : ℝ) • (inner ℝ (ω : Work.LWP.R3) y • (ω : Work.LWP.R3))
          ∂(MeasureTheory.volume : MeasureTheory.Measure Work.LWP.R3).toSphere) from
      integral_sub hf1 hf3]
  rw [integral_const, integral_smul, hcomp, hmass, ← mul_smul,
    show (3 : ℝ) * (4 * Real.pi / 3) = 4 * Real.pi by ring, sub_self]

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.EllipticEst.Core.derivIntegrableOfEnergy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

open MeasureTheory Set Filter
open scoped Real

/-- The angular weight `thEta θ = sin(2θ)^{-η}` is `≥ 1` on `Ioo 0 (π/2)`, because there
`0 < sin(2θ) ≤ 1` and the exponent `-η` is negative. -/
theorem one_le_thEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (1 : ℝ) ≤ Work.FTS.EllipticEst.thEta θ := by
  have hsin_pos : 0 < Real.sin (2 * θ) := Work.FTS.EllipticEst.sin_two_pos hθ
  have hsin_le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h : Real.sin (2 * θ) ^ (0 : ℝ) ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_le_rpow_of_exponent_ge hsin_pos hsin_le (by rw [Work.Spaces.eta]; norm_num)
  rwa [Real.rpow_zero] at h

/-- `|x| ≤ x² + 1` for every real `x`. -/
theorem abs_le_sq_add_one (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  have hh : |x| ^ 2 = x ^ 2 := sq_abs x
  nlinarith [sq_nonneg (|x| - 1 / 2), abs_nonneg x]

/-- **The energy form dominates the plain `L²`/`L¹` norms.**

Since `thEta θ = sin(2θ)^{-η} ≥ 1` on `Ioo 0 (π/2)`, integrability of the weighted energy
`(f')²·thEta` on the open angular interval gives integrability of `(f')²` there (domination),
then of `|f'|` (via `|x| ≤ x² + 1` and finiteness of the interval), and finally of `f'` on
every subinterval `(a,b)` with `0 < a < b < π/2` (restriction of the measure).

The only regularity input is `f ∈ C¹` on the open interval, which supplies continuity — hence
a.e. strong measurability — of `deriv f` there; no differentiability at the endpoints is
needed. -/
theorem derivIntegrableOfEnergy (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => (deriv f θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) ∧
    MeasureTheory.IntegrableOn (fun θ => |deriv f θ|) (Set.Ioo 0 (Real.pi / 2)) ∧
    (∀ a b : ℝ, a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      MeasureTheory.IntegrableOn (fun θ => deriv f θ) (Set.Ioo a b)) := by
  have hSopen : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hcont : ContinuousOn (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ContDiffOn.continuousOn_deriv_of_isOpen hf hSopen le_rfl
  have hmeas : AEStronglyMeasurable (deriv f)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  -- `(f')² ≤ (f')²·thEta` pointwise, and the right-hand side is integrable
  have hsq : IntegrableOn (fun θ => (deriv f θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine Integrable.mono' hint (hmeas.pow 2) ?_
    refine Filter.Eventually.mono (ae_restrict_mem measurableSet_Ioo) ?_
    intro θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (one_le_thEta hθ)
  -- the constant `1` is integrable on the bounded interval
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  -- `|f'| ≤ (f')² + 1`
  have hsum : IntegrableOn (fun θ => (deriv f θ) ^ 2 + 1) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1 : Integrable (fun θ => (deriv f θ) ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := hsq
    have h2 : Integrable (fun _ : ℝ => (1 : ℝ))
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := hconst
    exact h1.add h2
  have habs : IntegrableOn (fun θ => |deriv f θ|) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine Integrable.mono' hsum hmeas.norm ?_
    refine Filter.Eventually.mono (ae_restrict_mem measurableSet_Ioo) ?_
    intro θ _
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_le_sq_add_one (deriv f θ)
  refine ⟨hsq, habs, ?_⟩
  intro a b ha hb
  have hsub : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro θ hθ
    exact ⟨lt_trans ha.1 hθ.1, lt_trans hθ.2 hb.2⟩
  have habs' : IntegrableOn (fun θ => |deriv f θ|) (Set.Ioo a b) := habs.mono_set hsub
  have hmeas' : AEStronglyMeasurable (deriv f) (volume.restrict (Set.Ioo a b)) :=
    (hcont.mono hsub).aestronglyMeasurable measurableSet_Ioo
  refine (integrable_norm_iff hmeas').mp ?_
  show Integrable (fun θ => |deriv f θ|) (volume.restrict (Set.Ioo a b))
  exact habs'

end Work.EllipticEst.Core
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.TVRed.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- The angular factor `q(θ) = 2 η cot(2θ)` of the logarithmic derivative of the weight
`thEta θ = sin(2θ)^{-η}`, so that `thEta' = -qTh * thEta` on `(0, π/2)`. -/
noncomputable def qTh (θ : ℝ) : ℝ := 2 * Work.Spaces.eta * Real.cot (2 * θ)

/-- The two-sided trace-matching surrogate attached to a bump `ψ`:
`surrFun ψ F₀ F₁ L θ = F₀ * ψ (θ / L) + F₁ * ψ ((π/2 - θ) / L)`.
For a bump with `ψ = 1` on `(-∞, 1/4]` and `ψ = 0` on `[1/2, ∞)` its one-sided limits at `0⁺`
and `(π/2)⁻` are `F₀` and `F₁`, and its first two derivatives are supported in the two shells
`(L/4, L/2)` and `(π/2 - L/2, π/2 - L/4)`. -/
noncomputable def surrFun (ψ : ℝ → ℝ) (F₀ F₁ L θ : ℝ) : ℝ :=
  F₀ * ψ (θ / L) + F₁ * ψ ((Real.pi / 2 - θ) / L)

/-- The structure of the bump `ψ` used to build the surrogate: it is `C²` (with the two
chain-rule data `HasDerivAt` fields), equals `1` on `(-∞, 1/4]`, equals `0` on `[1/2, ∞)`,
takes values in `[0,1]`, and its first two derivatives are bounded by `C` and vanish off the
shell `(1/4, 1/2)`. -/
structure IsBump (ψ : ℝ → ℝ) (C : ℝ) : Prop where
  /-- the bound is positive. -/
  C_pos : 0 < C
  /-- `ψ` is of class `C²`. -/
  contDiff : ContDiff ℝ 2 ψ
  /-- the first derivative exists at every point. -/
  hasDerivAt : ∀ x : ℝ, HasDerivAt ψ (deriv ψ x) x
  /-- the derivative of `ψ` is differentiable at every point. -/
  hasDerivAt_deriv : ∀ x : ℝ, HasDerivAt (deriv ψ) (deriv (deriv ψ) x) x
  /-- `ψ = 1` on `(-∞, 1/4]`. -/
  eq_one : ∀ x : ℝ, x ≤ 1 / 4 → ψ x = 1
  /-- `ψ = 0` on `[1/2, ∞)`. -/
  eq_zero : ∀ x : ℝ, 1 / 2 ≤ x → ψ x = 0
  /-- `ψ ≥ 0`. -/
  nonneg : ∀ x : ℝ, 0 ≤ ψ x
  /-- `ψ ≤ 1`. -/
  le_one : ∀ x : ℝ, ψ x ≤ 1
  /-- the first derivative is bounded by `C`. -/
  deriv_bound : ∀ x : ℝ, |deriv ψ x| ≤ C
  /-- the second derivative is bounded by `C`. -/
  deriv2_bound : ∀ x : ℝ, |deriv (deriv ψ) x| ≤ C
  /-- the first derivative vanishes on `(-∞, 1/4)`. -/
  deriv_eq_zero_left : ∀ x : ℝ, x < 1 / 4 → deriv ψ x = 0
  /-- the first derivative vanishes on `(1/2, ∞)`. -/
  deriv_eq_zero_right : ∀ x : ℝ, 1 / 2 < x → deriv ψ x = 0
  /-- the second derivative vanishes on `(-∞, 1/4)`. -/
  deriv2_eq_zero_left : ∀ x : ℝ, x < 1 / 4 → deriv (deriv ψ) x = 0
  /-- the second derivative vanishes on `(1/2, ∞)`. -/
  deriv2_eq_zero_right : ∀ x : ℝ, 1 / 2 < x → deriv (deriv ψ) x = 0

end Work.EllipticEst.Core.i0Aux
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.TVRed.csThEta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

/-!
# Cauchy–Schwarz for the angular weight `thEta`

The angular weight `thEta θ = sin(2θ)^{-η}` is nonnegative on `Iθ = [0, π/2]`, so the
elementary Cauchy–Schwarz inequality holds for it:

  `(∫_{Iθ} g h thEta)² ≤ (∫_{Iθ} g² thEta) · (∫_{Iθ} h² thEta)`.

The point of the present formulation (and the reason it is not just an instance of
`Work.Spaces.cs_integral`) is that **no measurability of `g` or `h` is assumed**: only that
the two weighted squares `g² thEta`, `h² thEta` are integrable.  The proof therefore uses
the discriminant argument rather than `L²`-Cauchy–Schwarz: for every real `t` the function
`(g + t h)² thEta` is nonnegative, hence (when it is integrable, which it is exactly when
`g h thEta` is) has nonnegative integral `A + 2 t B + t² C`, which forces `B² ≤ A C`.  If
`g h thEta` is *not* integrable then the Bochner integral on the left vanishes by definition
and the right-hand side is a product of two nonnegative integrals.
-/

/-- Weighted Cauchy–Schwarz for an a.e. nonnegative weight `w` and **arbitrary** (not
necessarily measurable) functions `g`, `h` whose weighted squares are integrable:
`(∫_s g h w)² ≤ (∫_s g² w) · (∫_s h² w)`. -/
private lemma weighted_cs {w g h : ℝ → ℝ} {s : Set ℝ}
    (hw : ∀ᵐ θ ∂(MeasureTheory.volume.restrict s), 0 ≤ w θ)
    (hg : MeasureTheory.Integrable (fun θ : ℝ => (g θ) ^ 2 * w θ)
      (MeasureTheory.volume.restrict s))
    (hh : MeasureTheory.Integrable (fun θ : ℝ => (h θ) ^ 2 * w θ)
      (MeasureTheory.volume.restrict s)) :
    (∫ θ in s, g θ * h θ * w θ) ^ 2
      ≤ (∫ θ in s, (g θ) ^ 2 * w θ) * (∫ θ in s, (h θ) ^ 2 * w θ) := by
  by_cases hI : MeasureTheory.Integrable (fun θ : ℝ => g θ * h θ * w θ)
      (MeasureTheory.volume.restrict s)
  · -- Main case: `g h w` is integrable, so every quadratic `(g + t h)² w` is integrable
    -- and the discriminant of `t ↦ ∫ (g + t h)² w` is nonpositive.
    have key : ∀ t : ℝ, 0 ≤ (∫ θ in s, (g θ) ^ 2 * w θ)
        + 2 * t * (∫ θ in s, g θ * h θ * w θ) + t ^ 2 * (∫ θ in s, (h θ) ^ 2 * w θ) := by
      intro t
      have hpt : ∀ θ : ℝ, (g θ + t * h θ) ^ 2 * w θ
          = (g θ) ^ 2 * w θ + 2 * t * (g θ * h θ * w θ)
            + (t ^ 2) * ((h θ) ^ 2 * w θ) := fun θ => by ring
      have hnn : 0 ≤ ∫ θ in s, (g θ + t * h θ) ^ 2 * w θ :=
        MeasureTheory.integral_nonneg_of_ae
          (hw.mono (fun θ hθ => mul_nonneg (sq_nonneg _) hθ))
      have heq : (∫ θ in s, (g θ + t * h θ) ^ 2 * w θ)
          = (∫ θ in s, (g θ) ^ 2 * w θ) + 2 * t * (∫ θ in s, g θ * h θ * w θ)
            + t ^ 2 * (∫ θ in s, (h θ) ^ 2 * w θ) := by
        have h1 : MeasureTheory.Integrable
            (fun θ : ℝ => (g θ) ^ 2 * w θ + 2 * t * (g θ * h θ * w θ))
            (MeasureTheory.volume.restrict s) :=
          hg.add (hI.const_mul (2 * t))
        have h2 : MeasureTheory.Integrable (fun θ : ℝ => t ^ 2 * ((h θ) ^ 2 * w θ))
            (MeasureTheory.volume.restrict s) := hh.const_mul (t ^ 2)
        calc (∫ θ in s, (g θ + t * h θ) ^ 2 * w θ)
            = ∫ θ in s,
                ((g θ) ^ 2 * w θ + 2 * t * (g θ * h θ * w θ)) + t ^ 2 * ((h θ) ^ 2 * w θ) := by
              rw [funext hpt]
          _ = (∫ θ in s, ((g θ) ^ 2 * w θ + 2 * t * (g θ * h θ * w θ)))
                + ∫ θ in s, t ^ 2 * ((h θ) ^ 2 * w θ) :=
              MeasureTheory.integral_add h1 h2
          _ = ((∫ θ in s, (g θ) ^ 2 * w θ) + ∫ θ in s, 2 * t * (g θ * h θ * w θ))
                + ∫ θ in s, t ^ 2 * ((h θ) ^ 2 * w θ) := by
              rw [MeasureTheory.integral_add hg (hI.const_mul (2 * t))]
          _ = ((∫ θ in s, (g θ) ^ 2 * w θ) + 2 * t * (∫ θ in s, g θ * h θ * w θ))
                + t ^ 2 * (∫ θ in s, (h θ) ^ 2 * w θ) := by
              rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      linarith [hnn, heq.le, heq.ge]
    have hA : 0 ≤ ∫ θ in s, (g θ) ^ 2 * w θ :=
      MeasureTheory.integral_nonneg_of_ae
        (hw.mono (fun θ hθ => mul_nonneg (sq_nonneg _) hθ))
    have hC : 0 ≤ ∫ θ in s, (h θ) ^ 2 * w θ :=
      MeasureTheory.integral_nonneg_of_ae
        (hw.mono (fun θ hθ => mul_nonneg (sq_nonneg _) hθ))
    rcases eq_or_lt_of_le hC with hC0 | hCpos
    · -- `∫ h² w = 0`: then `∫ g h w = 0` as well.
      have hB0 : (∫ θ in s, g θ * h θ * w θ) = 0 := by
        by_contra hBne
        have hk := key (-((∫ θ in s, (g θ) ^ 2 * w θ) + 1)
          / (2 * (∫ θ in s, g θ * h θ * w θ)))
        have hval : (∫ θ in s, (g θ) ^ 2 * w θ)
              + 2 * (-((∫ θ in s, (g θ) ^ 2 * w θ) + 1)
                  / (2 * (∫ θ in s, g θ * h θ * w θ))) * (∫ θ in s, g θ * h θ * w θ)
              + (-((∫ θ in s, (g θ) ^ 2 * w θ) + 1)
                  / (2 * (∫ θ in s, g θ * h θ * w θ))) ^ 2 * (∫ θ in s, (h θ) ^ 2 * w θ)
            = -1 := by
          rw [← hC0]; field_simp; ring
        rw [hval] at hk
        linarith [hk]
      rw [hB0, ← hC0]
      norm_num
    · -- `∫ h² w > 0`: instantiate the quadratic at `t = -(∫ g h w)/(∫ h² w)`.
      have hk := key (-(∫ θ in s, g θ * h θ * w θ) / (∫ θ in s, (h θ) ^ 2 * w θ))
      have hval : (∫ θ in s, (g θ) ^ 2 * w θ)
            + 2 * (-(∫ θ in s, g θ * h θ * w θ) / (∫ θ in s, (h θ) ^ 2 * w θ))
              * (∫ θ in s, g θ * h θ * w θ)
            + (-(∫ θ in s, g θ * h θ * w θ) / (∫ θ in s, (h θ) ^ 2 * w θ)) ^ 2
              * (∫ θ in s, (h θ) ^ 2 * w θ)
          = (∫ θ in s, (g θ) ^ 2 * w θ)
            - (∫ θ in s, g θ * h θ * w θ) ^ 2 / (∫ θ in s, (h θ) ^ 2 * w θ) := by
        field_simp; ring
      rw [hval] at hk
      have h2 : (∫ θ in s, g θ * h θ * w θ) ^ 2 / (∫ θ in s, (h θ) ^ 2 * w θ)
          ≤ (∫ θ in s, (g θ) ^ 2 * w θ) := by linarith
      rwa [div_le_iff₀ hCpos] at h2
  · -- Otherwise the left-hand integral is `0` by definition and the right-hand side is a
    -- product of two nonnegative integrals.
    rw [MeasureTheory.integral_undef hI]
    have hA : 0 ≤ ∫ θ in s, (g θ) ^ 2 * w θ :=
      MeasureTheory.integral_nonneg_of_ae
        (hw.mono (fun θ hθ => mul_nonneg (sq_nonneg _) hθ))
    have hC : 0 ≤ ∫ θ in s, (h θ) ^ 2 * w θ :=
      MeasureTheory.integral_nonneg_of_ae
        (hw.mono (fun θ hθ => mul_nonneg (sq_nonneg _) hθ))
    norm_num
    exact mul_nonneg hA hC

theorem csThEta {g h : ℝ → ℝ}
    (hg : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hh : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (h θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (fun θ : ℝ => g θ * h θ * Work.FTS.EllipticEst.thEta θ)) ^ 2
      ≤ (MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
            (fun θ : ℝ => (g θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
        * (MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
            (fun θ : ℝ => (h θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) := by
  have hw : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ Work.FTS.EllipticEst.thEta θ :=
    (MeasureTheory.ae_restrict_iff' (measurableSet_Icc :
      MeasurableSet Work.Spaces.Iθ)).mpr
      (Filter.Eventually.of_forall
        (fun θ (hθ : θ ∈ Work.Spaces.Iθ) => Work.FTS.EllipticEst.thEta_nonneg hθ))
  exact weighted_cs hw hg hh

end Work.EllipticEst.Core.i0Aux.TVRed
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.TVRed.integralSqSub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

theorem integralSqSub {u v : ℝ → ℝ}
    (hu : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hv : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (v θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (huv : MeasureTheory.IntegrableOn
      (fun θ : ℝ => u θ * v θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (fun θ : ℝ => (u θ - v θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      = (MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
            (fun θ : ℝ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
        - 2 * (MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
            (fun θ : ℝ => u θ * v θ * Work.FTS.EllipticEst.thEta θ))
        + (MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
            (fun θ : ℝ => (v θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) := by
  -- Expand `(u - v)² = u² - 2uv + v²` pointwise and use the linearity of the Bochner
  -- integral against the restricted measure `volume.restrict Iθ`; the three
  -- integrability hypotheses are exactly the ones the linearity rules need.
  set μ := MeasureTheory.volume.restrict Work.Spaces.Iθ
  have hgrp : (fun θ : ℝ => (u θ - v θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = fun θ : ℝ => ((u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
          - 2 * (u θ * v θ * Work.FTS.EllipticEst.thEta θ))
          + (v θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    funext θ; ring
  have h2w : MeasureTheory.Integrable
      (fun θ : ℝ => 2 * (u θ * v θ * Work.FTS.EllipticEst.thEta θ)) μ := huv.const_mul 2
  have hsub : MeasureTheory.Integrable
      (fun θ : ℝ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
        - 2 * (u θ * v θ * Work.FTS.EllipticEst.thEta θ)) μ := hu.sub h2w
  rw [hgrp, MeasureTheory.integral_add hsub hv,
      MeasureTheory.integral_sub hu h2w, MeasureTheory.integral_const_mul]

end Work.EllipticEst.Core.i0Aux.TVRed
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.i0_fubini_package =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

open MeasureTheory Set Filter


end Work.EllipticEst.Core.i0Aux
end
-- ===== merged: Submission.Work.EllipticEst.Core.tendstoSqBoundLeft =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

/-- If `(f θ - c)² ≤ M θ^{1+η}` on `(0, π/2)` with `M ≥ 0` and `η > 0`, then `f → c`
as `θ → 0⁺`: the right-hand side tends to `0` (indeed `θ^{1+η} ≤ θ` for `θ ≤ 1`), so the
square of `f θ - c` tends to `0`, hence so does `|f θ - c|`, hence `f θ - c` itself. -/
theorem tendstoSqBoundLeft {f : ℝ → ℝ} {c M : ℝ} (hM : 0 ≤ M)
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (f θ - c) ^ 2 ≤ M * θ ^ (1 + Work.Spaces.eta)) :
    Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) := by
  have heta : 0 < Work.Spaces.eta := Work.Spaces.eta_pos
  have hIoi : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < θ := self_mem_nhdsWithin
  have hIio : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), θ < Real.pi / 2 :=
    Filter.le_def.mp nhdsWithin_le_nhds _ (Iio_mem_nhds (by linarith [Real.pi_pos]))
  have hI1 : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), θ < 1 :=
    Filter.le_def.mp nhdsWithin_le_nhds _ (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  -- Pointwise domination of the square by the linear function `M * θ`.
  have hU : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), (f θ - c) ^ 2 ≤ M * θ := by
    filter_upwards [hIoi, hIio, hI1] with θ h1 h2 h3
    have hmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
    have hh := h θ hmem
    have hrpow : θ ^ (1 + Work.Spaces.eta) ≤ θ := by
      rw [Real.rpow_add h1 1 Work.Spaces.eta, Real.rpow_one]
      exact mul_le_of_le_one_right (le_of_lt h1)
        (Real.rpow_le_one (le_of_lt h1) (le_of_lt h3) (le_of_lt heta))
    calc (f θ - c) ^ 2 ≤ M * θ ^ (1 + Work.Spaces.eta) := hh
      _ ≤ M * θ := mul_le_mul_of_nonneg_left hrpow hM
  -- `M * θ → 0` along `θ → 0⁺`.
  have hMθ : Filter.Tendsto (fun θ : ℝ => M * θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h0 : Filter.Tendsto (fun θ : ℝ => M * θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (M * 0)) :=
      Filter.Tendsto.const_mul M ((continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
    simpa using h0
  -- Squeeze: the square of `f θ - c` tends to `0`.
  have hsq : Filter.Tendsto (fun θ : ℝ => (f θ - c) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun θ => sq_nonneg _)) hU hMθ
  -- Hence the square root, i.e. `|f θ - c|`, tends to `0`.
  have hsqrt : Filter.Tendsto (fun θ : ℝ => Real.sqrt ((f θ - c) ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h0 : Filter.Tendsto (fun θ : ℝ => Real.sqrt ((f θ - c) ^ 2))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
    simpa using h0
  have habs : Filter.Tendsto (fun θ : ℝ => |f θ - c|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa [Real.sqrt_sq_eq_abs] using hsqrt
  have hsub : Filter.Tendsto (fun θ : ℝ => f θ - c)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 (by simpa [Real.norm_eq_abs] using habs)
  simpa [sub_add_cancel] using hsub.add_const c

end Work.EllipticEst.Core
end
-- ===== merged: Submission.Work.EllipticEst.Core.tendstoSqBoundRight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

/-- If `(f θ - c)^2` is controlled by `M * (π/2 - θ)^(1+η)` on the open interval
`(0, π/2)`, then `f θ → c` as `θ → (π/2)⁻` (with `η = 99/100 > 0`). -/
theorem tendstoSqBoundRight {f : ℝ → ℝ} {c M : ℝ} (hM : 0 ≤ M)
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (f θ - c) ^ 2 ≤ M * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)) :
    Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) := by
  set l : Filter ℝ := nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) with hl
  have hpi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  -- near `π/2` from below we land in the open interval `(0, π/2)`
  have hgt : ∀ᶠ θ in l, (0 : ℝ) < θ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hpi)
  have hlt : ∀ᶠ θ in l, θ < Real.pi / 2 := self_mem_nhdsWithin
  have hmem : ∀ᶠ θ in l, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    Filter.Eventually.mono (Filter.Eventually.and hgt hlt) fun θ hθ => ⟨hθ.1, hθ.2⟩
  -- `θ ↦ π/2 - θ` tends to `0`
  have ht : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) l (nhds 0) := by
    have h' : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhds (Real.pi / 2))
        (nhds (Real.pi / 2 - Real.pi / 2)) :=
      tendsto_const_nhds.sub Filter.tendsto_id
    simpa using h'.mono_left nhdsWithin_le_nhds
  -- hence the upper bound `M * (π/2 - θ)^(1+η)` tends to `0`
  have hg : Filter.Tendsto (fun θ : ℝ => M * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta))
      l (nhds 0) := by
    have hpos : (0 : ℝ) < 1 + Work.Spaces.eta := by
      rw [Work.Spaces.eta]; norm_num
    simpa using (ht.rpow_const_nhds_zero hpos).const_mul M
  -- squeeze `(f θ - c)^2` between `0` and it
  have hsq : Filter.Tendsto (fun θ : ℝ => (f θ - c) ^ 2) l (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (Filter.Eventually.mono hmem fun θ hθ => h θ hθ)
  -- `√((f θ - c)^2) = |f θ - c| → 0`, so `f θ - c → 0`
  have hsub : Filter.Tendsto (fun θ : ℝ => f θ - c) l (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsqrt : Filter.Tendsto (fun θ : ℝ => Real.sqrt ((f θ - c) ^ 2)) l
        (nhds (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa [Real.sqrt_sq_eq_abs] using hsqrt
  simpa using hsub.const_add c

end Work.EllipticEst.Core
end
-- ===== merged: Submission.Work.EllipticEst.Core.thEtaFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

/-- Basic facts about the angular weight `thEta θ = sin(2θ)^{-η}` (`η = 99/100`) on the
open angular interval `(0, π/2)`: it is strictly positive, it is `≥ 1`, its inverse is
`sin(2θ)^{η}`, and it is continuous there.

All four are immediate from `0 < sin(2θ) ≤ 1` on that interval: the totalised real power
`x ↦ x^p` is positive for `x > 0`, is `≤ 1` for `x ≤ 1` and `p ≤ 0`, satisfies
`x^{-p} = (x^p)⁻¹` for `x ≥ 0`, and is continuous where the base does not vanish. -/
theorem thEtaFacts :
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Work.FTS.EllipticEst.thEta θ) ∧
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 1 ≤ Work.FTS.EllipticEst.thEta θ) ∧
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (Work.FTS.EllipticEst.thEta θ)⁻¹
        = (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) ∧
    ContinuousOn Work.FTS.EllipticEst.thEta (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ hθ
    rw [Work.FTS.EllipticEst.thEta]
    exact Real.rpow_pos_of_pos (hsin θ hθ) _
  · intro θ hθ
    rw [Work.FTS.EllipticEst.thEta]
    have hs := hsin θ hθ
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hη0 : (0 : ℝ) ≤ Work.Spaces.eta := Work.Spaces.eta_pos.le
    have hspow : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 := Real.rpow_le_one hs.le hs1 hη0
    have hpos : 0 < (Real.sin (2 * θ)) ^ Work.Spaces.eta := Real.rpow_pos_of_pos hs _
    rw [Real.rpow_neg hs.le, inv_eq_one_div]
    rw [le_div_iff₀ hpos, one_mul]
    exact hspow
  · intro θ hθ
    rw [Work.FTS.EllipticEst.thEta, Real.rpow_neg (hsin θ hθ).le, inv_inv]
  · refine ContinuousOn.rpow_const ?_ ?_
    · exact Real.continuous_sin.comp_continuousOn
        ((continuous_const.mul continuous_id).continuousOn)
    · intro θ hθ
      exact Or.inl (ne_of_gt (hsin θ hθ))

end Work.EllipticEst.Core
end
-- ===== merged: Submission.Work.EllipticEst.Core.thEtaInvIntegralBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

open scoped Real
open MeasureTheory Set

/-- On the open strip `(0, π/2)` the reciprocal of the angular weight `thEta` is the
*positive* power `sin(2θ)^η` of `sin(2θ)`. -/
lemma thEta_inv_eq_sin_two_rpow {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.FTS.EllipticEst.thEta t)⁻¹ = (Real.sin (2 * t)) ^ (Work.Spaces.eta) := by
  have hs : 0 ≤ Real.sin (2 * t) :=
    Work.FTS.EllipticEst.sin_two_nonneg (Set.Ioo_subset_Icc_self ht)
  rw [Work.FTS.EllipticEst.thEta, Real.rpow_neg hs, inv_inv]

/-- `θ ↦ sin(2θ)^η` is continuous on every closed interval. -/
lemma continuousOn_sin_two_rpow_eta (a b : ℝ) :
    ContinuousOn (fun t : ℝ => (Real.sin (2 * t)) ^ (Work.Spaces.eta)) (Set.Icc a b) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
    (fun _ _ => Or.inr Work.Spaces.eta_nonneg)

/-- `θ ↦ sin(2θ)^η` is integrable on every open interval with finite endpoints. -/
lemma integrableOn_sin_two_rpow_eta_Ioo (a b : ℝ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (Real.sin (2 * t)) ^ (Work.Spaces.eta)) (Set.Ioo a b) :=
  ((continuousOn_sin_two_rpow_eta a b).integrableOn_compact isCompact_Icc).mono_set
    Set.Ioo_subset_Icc_self

/-- The pointwise bound at the left endpoint: for `0 < t < θ < π/2`,
`sin(2t)^η ≤ 2^η θ^η`. -/
lemma sin_two_rpow_le_of_lt {θ t : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (ht : t ∈ Set.Ioo (0 : ℝ) θ) :
    (Real.sin (2 * t)) ^ (Work.Spaces.eta) ≤
      (2 : ℝ) ^ (Work.Spaces.eta) * θ ^ (Work.Spaces.eta) := by
  obtain ⟨hθ0, hθ2⟩ := hθ
  obtain ⟨ht0, htθ⟩ := ht
  have hpi := Real.pi_pos
  have hsin0 : 0 ≤ Real.sin (2 * t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hle : Real.sin (2 * t) ≤ 2 * θ := by
    have h1 : Real.sin (2 * t) ≤ 2 * t := Real.sin_le (by linarith)
    linarith
  have hstep := Real.rpow_le_rpow hsin0 hle Work.Spaces.eta_nonneg
  rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hθ0)] at hstep

/-- The pointwise bound at the right endpoint: for `0 < θ < t < π/2`,
`sin(2t)^η ≤ 2^η (π/2 - θ)^η`. -/
lemma sin_two_rpow_le_of_gt {θ t : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (ht : t ∈ Set.Ioo θ (Real.pi / 2)) :
    (Real.sin (2 * t)) ^ (Work.Spaces.eta) ≤
      (2 : ℝ) ^ (Work.Spaces.eta) * (Real.pi / 2 - θ) ^ (Work.Spaces.eta) := by
  obtain ⟨hθ0, hθ2⟩ := hθ
  obtain ⟨htθ, ht2⟩ := ht
  have hpi := Real.pi_pos
  have hsin0 : 0 ≤ Real.sin (2 * t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hsub0 : 0 ≤ Real.pi / 2 - θ := by linarith
  have hle : Real.sin (2 * t) ≤ 2 * (Real.pi / 2 - θ) := by
    have h1 : Real.sin (2 * (Real.pi / 2 - t)) ≤ 2 * (Real.pi / 2 - t) :=
      Real.sin_le (by linarith)
    have h2 : Real.sin (2 * t) = Real.sin (2 * (Real.pi / 2 - t)) := by
      rw [show 2 * (Real.pi / 2 - t) = Real.pi - 2 * t by ring, Real.sin_pi_sub]
    rw [h2]
    linarith
  have hstep := Real.rpow_le_rpow hsin0 hle Work.Spaces.eta_nonneg
  rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hsub0] at hstep

/-- The elementary arithmetic at the heart of both endpoint estimates:
`2^η L^η · L ≤ 2 L^{1+η}` for `L > 0`. -/
lemma two_pow_eta_mul_rpow_mul_le {L : ℝ} (hL : 0 < L) :
    (2 : ℝ) ^ (Work.Spaces.eta) * L ^ (Work.Spaces.eta) * L ≤
      2 * L ^ (1 + Work.Spaces.eta) := by
  have h2 : (2 : ℝ) ^ (Work.Spaces.eta) ≤ 2 := by
    calc (2 : ℝ) ^ (Work.Spaces.eta) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt Work.Spaces.eta_lt_one)
      _ = 2 := Real.rpow_one 2
  have hpow : L ^ (1 + Work.Spaces.eta) = L ^ Work.Spaces.eta * L := by
    rw [Real.rpow_add hL, Real.rpow_one, mul_comm]
  calc (2 : ℝ) ^ (Work.Spaces.eta) * L ^ (Work.Spaces.eta) * L
      = (2 : ℝ) ^ (Work.Spaces.eta) * (L ^ Work.Spaces.eta * L) := by ring
    _ = (2 : ℝ) ^ (Work.Spaces.eta) * L ^ (1 + Work.Spaces.eta) := by rw [hpow]
    _ ≤ 2 * L ^ (1 + Work.Spaces.eta) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (le_of_lt hL) _)

/-- Integrating a nonnegative function on `(a, b)` which is everywhere bounded by the
constant `2^η (b - a)^η` gives at most `2 (b - a)^{1+η}`. -/
lemma integral_le_two_mul_rpow {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (h0 : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo a b)] f)
    (hle : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioo a b)),
      f t ≤ (2 : ℝ) ^ (Work.Spaces.eta) * (b - a) ^ (Work.Spaces.eta)) :
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo a b)) f
      ≤ 2 * (b - a) ^ (1 + Work.Spaces.eta) := by
  have hvol : MeasureTheory.volume (Set.Ioo a b) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hgi : MeasureTheory.Integrable
      (fun _ : ℝ => (2 : ℝ) ^ (Work.Spaces.eta) * (b - a) ^ (Work.Spaces.eta))
      (MeasureTheory.volume.restrict (Set.Ioo a b)) := by
    rw [MeasureTheory.integrable_const_iff]
    exact Or.inr (MeasureTheory.isFiniteMeasure_restrict.mpr hvol)
  have hmono : MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo a b)) f
      ≤ MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo a b))
          (fun _ : ℝ => (2 : ℝ) ^ (Work.Spaces.eta) * (b - a) ^ (Work.Spaces.eta)) :=
    MeasureTheory.integral_mono_of_nonneg h0 hgi hle
  have hconst : MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo a b))
      (fun _ : ℝ => (2 : ℝ) ^ (Work.Spaces.eta) * (b - a) ^ (Work.Spaces.eta))
      = (2 : ℝ) ^ (Work.Spaces.eta) * (b - a) ^ (Work.Spaces.eta) * (b - a) := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Ioo,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (le_of_lt hab)), smul_eq_mul]
    ring
  exact hmono.trans
    (le_trans (le_of_eq hconst) (two_pow_eta_mul_rpow_mul_le (sub_pos.mpr hab)))

theorem thEtaInvIntegralBounds :
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      MeasureTheory.IntegrableOn (fun t => (Work.FTS.EllipticEst.thEta t)⁻¹) (Set.Ioo 0 θ)) ∧
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo 0 θ))
        (fun t => (Work.FTS.EllipticEst.thEta t)⁻¹) ≤ 2 * θ ^ (1 + Work.Spaces.eta)) ∧
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      MeasureTheory.IntegrableOn (fun t => (Work.FTS.EllipticEst.thEta t)⁻¹) (Set.Ioo θ (Real.pi / 2))) ∧
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo θ (Real.pi / 2)))
        (fun t => (Work.FTS.EllipticEst.thEta t)⁻¹) ≤ 2 * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Integrability on `(0, θ)`
    intro θ hθ
    exact (integrableOn_sin_two_rpow_eta_Ioo 0 θ).congr_fun
      (fun t ht => (thEta_inv_eq_sin_two_rpow ⟨ht.1, lt_trans ht.2 hθ.2⟩).symm)
      measurableSet_Ioo
  · -- The bound on `(0, θ)`
    intro θ hθ
    have hmain := integral_le_two_mul_rpow (a := 0) (b := θ) hθ.1
      (f := fun t => (Work.FTS.EllipticEst.thEta t)⁻¹) ?_ ?_
    · simpa using hmain
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      rw [thEta_inv_eq_sin_two_rpow ⟨ht.1, lt_trans ht.2 hθ.2⟩]
      exact Real.rpow_nonneg
        (Work.FTS.EllipticEst.sin_two_nonneg
          ⟨le_of_lt ht.1, le_of_lt (lt_trans ht.2 hθ.2)⟩) _
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      rw [thEta_inv_eq_sin_two_rpow ⟨ht.1, lt_trans ht.2 hθ.2⟩]
      simpa using sin_two_rpow_le_of_lt (θ := θ) (t := t) hθ ht
  · -- Integrability on `(θ, π/2)`
    intro θ hθ
    exact (integrableOn_sin_two_rpow_eta_Ioo θ (Real.pi / 2)).congr_fun
      (fun t ht => (thEta_inv_eq_sin_two_rpow ⟨lt_trans hθ.1 ht.1, ht.2⟩).symm)
      measurableSet_Ioo
  · -- The bound on `(θ, π/2)`
    intro θ hθ
    have hmain := integral_le_two_mul_rpow (a := θ) (b := Real.pi / 2) hθ.2
      (f := fun t => (Work.FTS.EllipticEst.thEta t)⁻¹) ?_ ?_
    · simpa using hmain
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      rw [thEta_inv_eq_sin_two_rpow ⟨lt_trans hθ.1 ht.1, ht.2⟩]
      exact Real.rpow_nonneg
        (Work.FTS.EllipticEst.sin_two_nonneg
          ⟨le_of_lt (lt_trans hθ.1 ht.1), le_of_lt ht.2⟩) _
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      rw [thEta_inv_eq_sin_two_rpow ⟨lt_trans hθ.1 ht.1, ht.2⟩]
      simpa using sin_two_rpow_le_of_gt (θ := θ) (t := t) hθ ht

end Work.EllipticEst.Core
end
-- ===== merged: Submission.Work.EllipticEst.Core.thetaDerivDescent =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core


end Work.EllipticEst.Core
end
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.PTB.finSum_lzero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution.PTB

/--
`Lzero` on a finite linear combination of the Gegenbauer modes: the operator is a *linear*
differential operator, so it distributes over the finite sum, and each mode is an eigenfunction
(`eFam_Lzero`): `Lzero e_m = lam m • e_m`.

The `z`-argument is irrelevant (the summands do not depend on it); the proof reuses the
finite-sum differentiation lemmas of `Work.FTS.PhiStar.Series.psiTrunc_solves`
(`pthIter_two_sum_sep`, `pth_tan_sum_sep`), which are the `b m : ℝ → ℝ` version of the needed
identities with constant coefficients `b m = fun _ => a m`. -/
theorem finSum_lzero (a : ℕ → ℝ) (s : Finset ℕ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    Work.Elliptic.Lzero
        (fun _ θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') z θ
      = ∑ m ∈ s,
          Work.FTS.PhiStar.Gegenbauer.lam m * a m
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  -- the angular modes are `C³`
  have he : ∀ m ∈ s, ∀ θ' : ℝ,
      DifferentiableAt ℝ (Work.FTS.PhiStar.Gegenbauer.eFam m) θ' := fun m _ θ' =>
    ((Work.FTS.PhiStar.Series.contDiff_eFam m).differentiable (by norm_num)).differentiableAt
  have he1 : ∀ m ∈ s,
      DifferentiableAt ℝ (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ := fun m _ =>
    ((ContDiff.deriv' (n := 2) (Work.FTS.PhiStar.Series.contDiff_eFam m)).differentiable
      (by norm_num)).differentiableAt
  -- the two derivative identities for the finite sum
  have hpthId : Work.Spaces.pthIter 2
        (fun z' θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') z θ
      = ∑ m ∈ s, a m * deriv (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ := by
    show Work.Spaces.pthIter 2 (fun z' θ' => ∑ m ∈ s,
        (fun _ : ℝ => a m) z' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') z θ = _
    exact Work.FTS.PhiStar.Series.pthIter_two_sum_sep s (fun m _ => a m)
      Work.FTS.PhiStar.Gegenbauer.eFam z θ he he1
  have htanId : Work.Spaces.pth
        (fun z' θ' => Real.tan θ' * (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ')) z θ
      = ∑ m ∈ s, a m * deriv (fun θ' : ℝ =>
          Real.tan θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ := by
    show Work.Spaces.pth (fun z' θ' => Real.tan θ' * (∑ m ∈ s,
        (fun _ : ℝ => a m) z' * Work.FTS.PhiStar.Gegenbauer.eFam m θ')) z θ = _
    exact Work.FTS.PhiStar.Series.pth_tan_sum_sep s (fun m _ => a m)
      Work.FTS.PhiStar.Gegenbauer.eFam z θ hθ (fun m hm => he m hm θ)
  -- unfold `Lzero` on the (z-independent) sum
  have hLzeroId : Work.Elliptic.Lzero
        (fun _ θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') z θ
      = -(∑ m ∈ s, a m * deriv (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ)
        + (∑ m ∈ s, a m * deriv (fun θ' : ℝ =>
            Real.tan θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ)
        - 6 * (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
    show -(Work.Spaces.pthIter 2
          (fun _ θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') z θ)
        + Work.Spaces.pth (fun z θ' => Real.tan θ'
            * (fun _ θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') z θ') z θ
        - 6 * (fun _ θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') z θ = _
    rw [hpthId, htanId]
  rw [hLzeroId]
  -- distribute the linear combination into the sum
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  -- the single-mode eigenrelation `Lzero e_m = lam m • e_m`
  have hLam : deriv (fun θ' : ℝ => Real.tan θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
      - deriv (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ
      - 6 * Work.FTS.PhiStar.Gegenbauer.eFam m θ
      = Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
    have h2 : -(deriv (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ)
        + deriv (fun t : ℝ => Real.tan t * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
        - 6 * Work.FTS.PhiStar.Gegenbauer.eFam m θ
        = Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
      have h4 := congrFun
        (Work.FTS.EllipticEst.Lzero1_eq_Lzero (Work.FTS.PhiStar.Gegenbauer.eFam m) z) θ
      rw [Work.FTS.PhiStar.Gegenbauer.eFam_Lzero m hθ z] at h4
      simpa only [Work.FTS.EllipticEst.Lzero1] using h4
    linarith [h2]
  have hdist : -(a m * deriv (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ)
        + a m * deriv (fun θ' : ℝ => Real.tan θ' *
            Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
        - 6 * (a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      = a m * (deriv (fun θ' : ℝ => Real.tan θ' *
            Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
          - deriv (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ
          - 6 * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by ring
  rw [hdist, hLam]
  ring

end Work.EllipticEst.ModalSolution.PTB
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.PTBSupp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution.PTBSupp

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "eF" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "lamF" => Work.FTS.PhiStar.Gegenbauer.lam

/-! ## Elementary facts about the modes -/

private lemma continuous_eFam' (m : ℕ) : Continuous (eF m) := by
  have h : eF m = fun θ : ℝ =>
      Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) := rfl
  rw [h]
  exact Real.continuous_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp Real.continuous_sin)

private lemma integrableOn_eFam_mul' (m n : ℕ) :
    IntegrableOn (fun θ => eF m θ * eF n θ * Real.cos θ) Iθ :=
  ContinuousOn.integrableOn_compact isCompact_Icc
    (((continuous_eFam' m).mul (continuous_eFam' n)).mul Real.continuous_cos).continuousOn

private lemma setIntegral_Iθ_eq_interval' (f : ℝ → ℝ) :
    (∫ θ in Iθ, f θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
  show (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2), f θ) = _
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le
    (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)).symm

private lemma eFam_orth_Iθ' {m n : ℕ} (hmn : m ≠ n) :
    (∫ θ in Iθ, eF m θ * eF n θ * Real.cos θ) = 0 := by
  rw [setIntegral_Iθ_eq_interval']
  exact Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal m n hmn

private lemma eFam_diag' (m : ℕ) :
    (∫ θ in Iθ, eF m θ * eF m θ * Real.cos θ)
      = ∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ := by
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  ring

/-! ## Bilinear Parseval for a finite set of modes -/

/-- **Bilinear Parseval for a finite set of modes**: the `L²(Iθ, cos θ dθ)` pairing of two finite
mode sums collapses to the diagonal sum. -/
theorem finSum_bilin_gen (a b : ℕ → ℝ) (s : Finset ℕ) :
    (∫ θ in Iθ,
        (∑ m ∈ s, a m * eF m θ) * (∑ m ∈ s, b m * eF m θ) * Real.cos θ)
      = ∑ m ∈ s,
          (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) * a m * b m := by
  have hpt : ∀ θ : ℝ, (∑ m ∈ s, a m * eF m θ) * (∑ m ∈ s, b m * eF m θ) * Real.cos θ
      = ∑ m ∈ s, ∑ n ∈ s, (a m * b n) * (eF m θ * eF n θ * Real.cos θ) := by
    intro θ
    calc (∑ m ∈ s, a m * eF m θ) * (∑ m ∈ s, b m * eF m θ) * Real.cos θ
        = (∑ m ∈ s, (a m * eF m θ) * (∑ n ∈ s, b n * eF n θ)) * Real.cos θ := by
          rw [Finset.sum_mul]
      _ = ∑ m ∈ s, ((a m * eF m θ) * (∑ n ∈ s, b n * eF n θ)) * Real.cos θ := by
          rw [Finset.sum_mul]
      _ = ∑ m ∈ s, ∑ n ∈ s, (a m * b n) * (eF m θ * eF n θ * Real.cos θ) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
  have hint : ∀ m ∈ s, ∀ n ∈ s,
      IntegrableOn (fun θ => (a m * b n) * (eF m θ * eF n θ * Real.cos θ)) Iθ :=
    fun m _ n _ => (integrableOn_eFam_mul' m n).const_mul (a m * b n)
  have h1 : (∫ θ in Iθ, (∑ m ∈ s, a m * eF m θ) * (∑ m ∈ s, b m * eF m θ) * Real.cos θ)
      = ∫ θ in Iθ, ∑ m ∈ s, ∑ n ∈ s,
          (a m * b n) * (eF m θ * eF n θ * Real.cos θ) :=
    integral_congr_ae (Eventually.of_forall hpt)
  rw [h1]
  rw [MeasureTheory.integral_finset_sum s
    (fun m hm => MeasureTheory.integrable_finset_sum s (fun n hn => hint m hm n hn))]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MeasureTheory.integral_finset_sum s (fun n hn => hint m hm n hn)]
  have hkey : (∑ n ∈ s, (a m * b n) * (∫ θ in Iθ, eF m θ * eF n θ * Real.cos θ))
      = (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ) * a m * b m := by
    have hsingle := Finset.sum_eq_single (s := s)
      (f := fun n => (a m * b n) * (∫ θ in Iθ, eF m θ * eF n θ * Real.cos θ)) m
      (fun n _ hnm => by rw [eFam_orth_Iθ' (Ne.symm hnm), mul_zero])
      (fun hms => absurd hm hms)
    rw [hsingle, eFam_diag' m]
    ring
  rw [Finset.sum_congr rfl (fun n _ => by rw [MeasureTheory.integral_const_mul])]
  exact hkey

/-! ## The action of `Lzero` on a finite sum of modes -/

private lemma lzero_indep' (f : ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero (fun _ θ' => f θ') z θ
      = -(deriv (deriv f) θ) + deriv (fun θ' => Real.tan θ' * f θ') θ - 6 * f θ := by
  simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
    Work.Spaces.pth]

private lemma deriv_sum_const_mul' (s : Finset ℕ) (a : ℕ → ℝ) (e : ℕ → ℝ → ℝ) (θ : ℝ)
    (he : ∀ m ∈ s, DifferentiableAt ℝ (e m) θ) :
    deriv (fun θ' => ∑ m ∈ s, a m * e m θ') θ = ∑ m ∈ s, a m * deriv (e m) θ := by
  have hfun : (fun θ' : ℝ => ∑ m ∈ s, a m * e m θ')
      = ∑ m ∈ s, (fun θ' : ℝ => a m * e m θ') := by
    funext θ'; rw [Finset.sum_apply]
  rw [hfun, deriv_sum (fun m hm => (he m hm).const_mul (a m))]
  exact Finset.sum_congr rfl fun m hm => deriv_const_mul (a m) (he m hm)

private lemma deriv_sum_tan_const_mul' (s : Finset ℕ) (a : ℕ → ℝ) (e : ℕ → ℝ → ℝ) (θ : ℝ)
    (hcos : Real.cos θ ≠ 0) (he : ∀ m ∈ s, DifferentiableAt ℝ (e m) θ) :
    deriv (fun θ' => Real.tan θ' * (∑ m ∈ s, a m * e m θ')) θ
      = ∑ m ∈ s, a m * deriv (fun θ' => Real.tan θ' * e m θ') θ := by
  have htan : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
  have hfun : (fun θ' : ℝ => Real.tan θ' * (∑ m ∈ s, a m * e m θ'))
      = ∑ m ∈ s, (fun θ' : ℝ => Real.tan θ' * (a m * e m θ')) := by
    funext θ'; rw [Finset.sum_apply, Finset.mul_sum]
  have hstep : deriv (∑ m ∈ s, (fun θ' : ℝ => Real.tan θ' * (a m * e m θ'))) θ
      = ∑ m ∈ s, deriv (fun θ' : ℝ => Real.tan θ' * (a m * e m θ')) θ :=
    deriv_sum (fun m hm => htan.mul ((he m hm).const_mul (a m)))
  rw [hfun, hstep]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [show (fun θ' : ℝ => Real.tan θ' * (a m * e m θ'))
      = fun θ' : ℝ => a m * (Real.tan θ' * e m θ') from by funext θ'; ring]
  exact deriv_const_mul (a m) (htan.mul (he m hm))

/-- **`Lzero` acts diagonally on a finite sum of modes**: for `cos θ ≠ 0` the modes are
eigenfunctions with eigenvalue `lam m = 2m(2m+5)`. -/
theorem lzero_finSum_gen (a : ℕ → ℝ) (s : Finset ℕ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    Work.Elliptic.Lzero (fun _ θ' => ∑ m ∈ s, a m * eF m θ') z θ
      = ∑ m ∈ s, lamF m * a m * eF m θ := by
  have he : ∀ m ∈ s, ∀ θ' : ℝ, DifferentiableAt ℝ (eF m) θ' :=
    fun m _ θ' => (Work.FTS.PhiStar.Series.contDiff_eFam m).differentiable (by norm_num)
      |>.differentiableAt
  have he1 : ∀ m ∈ s, DifferentiableAt ℝ (deriv (eF m)) θ :=
    fun m _ => (ContDiff.deriv' (n := 2) (Work.FTS.PhiStar.Series.contDiff_eFam m)).differentiable
      (by norm_num) |>.differentiableAt
  have h2 : deriv (deriv (fun θ' => ∑ m ∈ s, a m * eF m θ')) θ
      = ∑ m ∈ s, a m * deriv (deriv (eF m)) θ := by
    have hf : deriv (fun θ' => ∑ m ∈ s, a m * eF m θ')
        = fun θ' => ∑ m ∈ s, a m * deriv (eF m) θ' := by
      funext θ'
      exact deriv_sum_const_mul' s a (fun m => eF m) θ' (fun m hm => he m hm θ')
    rw [hf]
    exact deriv_sum_const_mul' s a (fun m => deriv (eF m)) θ (fun m hm => he1 m hm)
  have h1 : deriv (fun θ' => Real.tan θ' * (∑ m ∈ s, a m * eF m θ')) θ
      = ∑ m ∈ s, a m * deriv (fun θ' => Real.tan θ' * eF m θ') θ :=
    deriv_sum_tan_const_mul' s a (fun m => eF m) θ hθ (fun m hm => he m hm θ)
  have hL : Work.Elliptic.Lzero (fun _ θ' => ∑ m ∈ s, a m * eF m θ') z θ
      = -(∑ m ∈ s, a m * deriv (deriv (eF m)) θ)
        + (∑ m ∈ s, a m * deriv (fun θ' => Real.tan θ' * eF m θ') θ)
        - 6 * (∑ m ∈ s, a m * eF m θ) := by
    rw [lzero_indep']
    rw [h2, h1]
  have hLam : ∀ m ∈ s, deriv (fun θ' => Real.tan θ' * eF m θ') θ
      - deriv (deriv (eF m)) θ - 6 * eF m θ = lamF m * eF m θ := by
    intro m _
    have h6 := lzero_indep' (eF m) z θ
    rw [Work.FTS.PhiStar.Gegenbauer.eFam_Lzero m hθ z] at h6
    linarith [h6]
  rw [hL]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  calc -(a m * deriv (deriv (eF m)) θ) + a m * deriv (fun θ' => Real.tan θ' * eF m θ') θ
        - 6 * (a m * eF m θ)
      = a m * (deriv (fun θ' => Real.tan θ' * eF m θ') θ - deriv (deriv (eF m)) θ
          - 6 * eF m θ) := by ring
    _ = a m * (lamF m * eF m θ) := by rw [hLam m hm]
    _ = lamF m * a m * eF m θ := by ring

end Work.EllipticEst.ModalSolution.PTBSupp
end
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.PairIdent.eFam_finSum_bilin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution.PairIdent

local notation "e" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "Iθ" => Work.Spaces.Iθ

/-! ## Elementary facts about the modes `eFam m` needed for the bilinear expansion -/

/-- `eFam m` is continuous (it is `cos θ · gC (2m+1) (sin θ)`). -/
private lemma continuous_eFam (m : ℕ) : Continuous (e m) := by
  have h : e m = fun θ : ℝ =>
      Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) := rfl
  rw [h]
  exact Real.continuous_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp Real.continuous_sin)

/-- `e m θ · e n θ · cos θ` is integrable on `Iθ` (continuous on a compact interval). -/
private lemma integrableOn_eFam_mul (m n : ℕ) :
    IntegrableOn (fun θ => e m θ * e n θ * Real.cos θ) Iθ :=
  ContinuousOn.integrableOn_compact isCompact_Icc
    (((continuous_eFam m).mul (continuous_eFam n)).mul Real.continuous_cos).continuousOn

/-- The set integral over `Iθ = [0, π/2]` is the interval integral over `(0, π/2)`; the two
differ only at the (`volume`-null) endpoint `θ = 0`. -/
private lemma setIntegral_Iθ_eq_interval (f : ℝ → ℝ) :
    (∫ θ in Iθ, f θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
  show (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2), f θ) = _
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le
    (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)).symm



/-! ## The bilinear identity -/


end Work.EllipticEst.ModalSolution.PairIdent
end
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.PairIdent.lzero_finSum_eFam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped BigOperators

namespace Work.EllipticEst.ModalSolution.PairIdent

set_option autoImplicit false

open Work.FTS.PhiStar.Gegenbauer

/-! ## `Lzero` on a `z`-independent function, and its linearity over finite mode sums

`Lzero Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ` involves only `θ`-derivatives, so on a function of
`θ` alone it is the one-variable operator `Lzero1 f = -f'' + (tan · f)' - 6f` (`lzero_indep`).
It is linear, hence commutes with a finite sum of modes whose summands are differentiable
(`deriv_sum_const_mul`, `deriv_sum_tan_const_mul`), and each mode is an eigenfunction with
eigenvalue `lam m = 2m(2m+5)` (`eFam_Lzero`), which gives `lzero_sum_indep` and then the
requested identity for the truncated mode series. -/

/-- `Lzero` applied to a function of `θ` alone: the `z`-variable is irrelevant. -/
private lemma lzero_indep (f : ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero (fun _ θ' => f θ') z θ
      = -(deriv (deriv f) θ) + deriv (fun θ' => Real.tan θ' * f θ') θ - 6 * f θ := by
  simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
    Work.Spaces.pth]

/-- `∂_θ` of a finite sum of modes `θ ↦ ∑ m, a m · e m θ`. -/
private lemma deriv_sum_const_mul (s : Finset ℕ) (a : ℕ → ℝ) (e : ℕ → ℝ → ℝ) (θ : ℝ)
    (he : ∀ m ∈ s, DifferentiableAt ℝ (e m) θ) :
    deriv (fun θ' => ∑ m ∈ s, a m * e m θ') θ = ∑ m ∈ s, a m * deriv (e m) θ := by
  have hfun : (fun θ' : ℝ => ∑ m ∈ s, a m * e m θ')
      = ∑ m ∈ s, (fun θ' : ℝ => a m * e m θ') := by
    funext θ'; rw [Finset.sum_apply]
  rw [hfun, deriv_sum (fun m hm => (he m hm).const_mul (a m))]
  exact Finset.sum_congr rfl fun m hm => deriv_const_mul (a m) (he m hm)

/-- `∂_θ(tan θ · ·)` of a finite sum of modes `θ ↦ ∑ m, a m · e m θ`. -/
private lemma deriv_sum_tan_const_mul (s : Finset ℕ) (a : ℕ → ℝ) (e : ℕ → ℝ → ℝ) (θ : ℝ)
    (hcos : Real.cos θ ≠ 0) (he : ∀ m ∈ s, DifferentiableAt ℝ (e m) θ) :
    deriv (fun θ' => Real.tan θ' * (∑ m ∈ s, a m * e m θ')) θ
      = ∑ m ∈ s, a m * deriv (fun θ' => Real.tan θ' * e m θ') θ := by
  have htan : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
  have hfun : (fun θ' : ℝ => Real.tan θ' * (∑ m ∈ s, a m * e m θ'))
      = ∑ m ∈ s, (fun θ' : ℝ => Real.tan θ' * (a m * e m θ')) := by
    funext θ'; rw [Finset.sum_apply, Finset.mul_sum]
  have hstep : deriv (∑ m ∈ s, (fun θ' : ℝ => Real.tan θ' * (a m * e m θ'))) θ
      = ∑ m ∈ s, deriv (fun θ' : ℝ => Real.tan θ' * (a m * e m θ')) θ :=
    deriv_sum (fun m hm => htan.mul ((he m hm).const_mul (a m)))
  rw [hfun, hstep]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [show (fun θ' : ℝ => Real.tan θ' * (a m * e m θ'))
      = fun θ' : ℝ => a m * (Real.tan θ' * e m θ') from by funext θ'; ring]
  exact deriv_const_mul (a m) (htan.mul (he m hm))



end Work.EllipticEst.ModalSolution.PairIdent
end
end
-- ===== merged: Submission.Work.EllipticEst.ModalSolution.eFamBasisFts_FALSE =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real
open MeasureTheory

namespace Work.EllipticEst.ModalSolution


/-- **The first conjunct is true, in the set-integral form used in `eFamBasisFts`.**  This is the
three-line conversion of `Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal` (interval-integral form):
the set integral over `Iθ = Icc 0 (π/2)` equals the interval integral `∫ θ in (0)..(π/2)` because
`Icc` and `Ioc` differ by the single point `0`. -/
theorem eFam_orthogonal_Iθ (m n : ℕ) (hmn : m ≠ n) :
    (∫ θ in Work.Spaces.Iθ,
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ
        * Real.cos θ) = 0 := by
  have h := Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal m n hmn
  simp only [Work.Spaces.Iθ]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
  exact h

/-- The `m`-th mode weight `θ ↦ eFam m θ · cos θ` is continuous. -/
lemma continuous_eFam_mul_cos (m : ℕ) :
    Continuous (fun θ : ℝ =>
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) := by
  have hFam : Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
    simp only [Work.FTS.PhiStar.Gegenbauer.eFam]
    exact Real.continuous_cos.mul
      (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
        Real.continuous_sin)
  exact hFam.mul Real.continuous_cos

/-- **Non-measurability is inherited by the products with the modes.**  If `g` is not a.e. strongly
measurable for `volume.restrict Iθ` and the mode weights vanish only on a null set, then for every
`m` the integrand `θ ↦ g θ · eFam m θ · cos θ` is not a.e. strongly measurable either. -/
lemma not_aestronglyMeasurable_mul_eFam
    {g : ℝ → ℝ} (hg : ¬ MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hφ : ∀ m : ℕ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ ≠ 0)
    (m : ℕ) :
    ¬ MeasureTheory.AEStronglyMeasurable
      (fun θ => g θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  set φ : ℝ → ℝ := fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ with hφdef
  intro hprod
  obtain ⟨v, hv_sm, hv_eq⟩ := hprod
  have hφ_sm : StronglyMeasurable φ := (continuous_eFam_mul_cos m).stronglyMeasurable
  have hdiv : StronglyMeasurable (fun θ : ℝ => v θ / φ θ) := hv_sm.div hφ_sm
  have hae : g =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ : ℝ => v θ / φ θ := by
    filter_upwards [hv_eq, hφ m] with θ hv hne
    rw [mul_assoc] at hv
    exact (eq_div_iff hne).mpr hv
  exact hg (hdiv.aestronglyMeasurable.congr hae.symm)



end Work.EllipticEst.ModalSolution
end
end
-- ===== merged: Submission.Work.FTS.BSSwirl.Book =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory Bornology
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-- **`HolderWith` in pointwise norm form.** -/
theorem holderWith_dist_le {C α : ℝ≥0} {ω : R3 → R3} (h : HolderWith C α ω) (a b : R3) :
    ‖ω a - ω b‖ ≤ (C : ℝ) * ‖a - b‖ ^ ((α : ℝ≥0) : ℝ) := by
  simpa [dist_eq_norm] using h.dist_le a b


/-- A `HolderWith` field of positive exponent is a.e. strongly measurable. -/
theorem aestronglyMeasurable_of_holderWith {C α : ℝ≥0} {ω : R3 → R3} (h : HolderWith C α ω)
    (hα : 0 < (α : ℝ)) : AEStronglyMeasurable ω volume :=
  (h.continuous hα).aestronglyMeasurable

/-- **A pointwise Hölder bound gives continuity**, for a positive exponent. -/
theorem continuous_of_holder_pointwise {ω : R3 → R3} {C α : ℝ} (hα : 0 < α)
    (h : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ α) : Continuous ω := by
  have h' : ∀ a b : R3, ‖ω a - ω b‖ ≤ (max C 0 + 1) * ‖a - b‖ ^ α := fun a b =>
    le_trans (h a b) (mul_le_mul_of_nonneg_right (by linarith [le_max_left C 0])
      (Real.rpow_nonneg (norm_nonneg _) _))
  rw [Metric.continuous_iff]
  rintro x ε hε
  have hM : 0 < max C 0 + 1 := by linarith [le_max_right C 0]
  refine ⟨(ε / (max C 0 + 1)) ^ (1 / α), Real.rpow_pos_of_pos (div_pos hε hM) _, ?_⟩
  intro y hy
  have hy' : ‖y - x‖ < (ε / (max C 0 + 1)) ^ (1 / α) := by simpa [dist_eq_norm] using hy
  have h2 : ‖y - x‖ ^ α < ε / (max C 0 + 1) := by
    calc ‖y - x‖ ^ α < ((ε / (max C 0 + 1)) ^ (1 / α)) ^ α :=
          Real.rpow_lt_rpow (norm_nonneg _) hy' hα
      _ = ε / (max C 0 + 1) := by
          rw [← Real.rpow_mul (le_of_lt (div_pos hε hM)) (1 / α) α, one_div,
            inv_mul_cancel₀ (ne_of_gt hα), Real.rpow_one]
  calc dist (ω y) (ω x) = ‖ω y - ω x‖ := dist_eq_norm _ _
    _ ≤ (max C 0 + 1) * ‖y - x‖ ^ α := h' y x
    _ < (max C 0 + 1) * (ε / (max C 0 + 1)) := mul_lt_mul_of_pos_left h2 hM
    _ = ε := by field_simp

/-- **Boundedness of a `HolderWith` field with compactly supported values.**  A continuous field
vanishing off `closedBall 0 R` is bounded by the maximum of its norm over the (compact) ball of
radius `max R 0`. -/
theorem exists_bound_of_holderWith_support {C α : ℝ≥0} {ω : R3 → R3} {R : ℝ}
    (hα : 0 < (α : ℝ)) (h : HolderWith C α ω) (hsupp : ∀ x, ω x ≠ 0 → ‖x‖ ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖ω x‖ ≤ M := by
  have hcont : Continuous ω := h.continuous hα
  have hsub : ∀ x, ω x ≠ 0 → x ∈ Metric.closedBall (0 : R3) (max R 0) := fun x hx =>
    Metric.mem_closedBall.mpr (by
      rw [dist_zero_right]
      exact le_trans (hsupp x hx) (le_max_left R 0))
  obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_closedBall (0 : R3) (max R 0)).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self (le_max_right R 0)⟩ (hcont.continuousOn.norm)
  exact ⟨‖ω x₀‖, norm_nonneg _, fun x => by
    by_cases hx : ω x = 0
    · simp [hx]
    · exact hmax (hsub x hx)⟩

/-- **A `HolderWith` field whose support radius is `≤ 0` vanishes identically.**  It vanishes off
the origin by the support condition and at the origin by continuity. -/
theorem eq_zero_of_holderWith_support_le {C α : ℝ≥0} {ω : R3 → R3} {R : ℝ}
    (hα : 0 < (α : ℝ)) (h : HolderWith C α ω) (hsupp : ∀ x, ω x ≠ 0 → ‖x‖ ≤ R) (hR : R ≤ 0) :
    ∀ x, ω x = 0 := by
  have hcont : Continuous ω := h.continuous hα
  have hoff : ∀ x, x ≠ 0 → ω x = 0 := by
    intro x hx
    by_contra h0
    have h1 : ‖x‖ ≤ R := hsupp x h0
    have h2 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    linarith
  intro x
  by_cases hx : x = 0
  · subst hx
    have h1 : Tendsto ω (𝓝[≠] (0 : R3)) (𝓝 (ω 0)) :=
      hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto ω (𝓝[≠] (0 : R3)) (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hoff y hy).symm
    exact tendsto_nhds_unique h1 h2
  · exact hoff x hx

end

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.CdAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Set Filter
open scoped Topology ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-- **The scalar kernel of the derivative of the Newtonian potential**,
`k z = ‖z‖⁻³ • ⟪z, ·⟫ : ℝ³ →L[ℝ] ℝ`.  It is odd in `z` and of homogeneity `-2` in `z`. -/
def potKer (z : R3) : R3 →L[ℝ] ℝ :=
  (‖z‖ ^ (3 : ℕ))⁻¹ • innerSL ℝ z

/-- The kernel `potKer` cut off to the ball `B(0,ρ)`.  Unlike `potKer` itself, this is integrable
on all of `ℝ³` (the singularity `‖z‖⁻²` is integrable in dimension `3`). -/
def potKerBall (ρ : ℝ) : R3 → (R3 →L[ℝ] ℝ) :=
  (Metric.ball 0 ρ).indicator potKer

theorem potKerBall_apply_of_mem {ρ : ℝ} {z : R3} (hz : z ∈ Metric.ball 0 ρ) :
    potKerBall ρ z = potKer z :=
  Set.indicator_of_mem hz _



/-- Pulling a scalar out of the first argument of `smulRight`. -/
theorem smul_smulRight (c : ℝ) (f : R3 →L[ℝ] ℝ) (v : R3) :
    (c • f).smulRight v = c • f.smulRight v := by
  refine ContinuousLinearMap.ext fun h => ?_
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_smul,
    smul_eq_mul]

theorem potKer_smulRight (z v : R3) :
    (potKer z).smulRight v = (‖z‖ ^ (3 : ℕ))⁻¹ • (innerSL ℝ z).smulRight v :=
  smul_smulRight _ _ _


/-- **The kernel is of homogeneity `-2`**: `‖k z‖ ≤ ‖z‖⁻²` (in particular it is dominated by the
integrable function `‖z‖ ^ (-2 : ℝ)`). -/
theorem potKer_norm_le (z : R3) : ‖potKer z‖ ≤ ‖z‖ ^ (-2 : ℝ) := by
  have hx : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  rw [potKer, norm_smul, innerSL_apply_norm, Real.norm_eq_abs]
  have h3 : (0 : ℝ) ≤ ‖z‖ ^ (3 : ℕ) := by positivity
  rw [abs_of_nonneg (inv_nonneg.mpr h3)]
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]
    simp [Real.zero_rpow (by norm_num : (-2 : ℝ) ≠ 0)]
  · have hxne : ‖z‖ ≠ 0 := ne_of_gt h
    have key : (‖z‖ ^ (3 : ℕ))⁻¹ * ‖z‖ = ‖z‖ ^ (-2 : ℝ) := by
      have h2 : (‖z‖ : ℝ) ^ (3 : ℕ) = ‖z‖ ^ 2 * ‖z‖ := by ring
      rw [Real.rpow_neg hx, Real.rpow_two, h2, mul_inv_rev,
        mul_comm ‖z‖⁻¹ ((‖z‖ ^ 2)⁻¹), mul_assoc, inv_mul_cancel₀ hxne, mul_one]
    rw [key]

theorem measurable_potKer : Measurable potKer := by
  rw [show potKer = fun z : R3 => (‖z‖ ^ (3 : ℕ))⁻¹ • innerSL ℝ z from rfl]
  measurability

theorem aestronglyMeasurable_potKer : AEStronglyMeasurable potKer volume :=
  measurable_potKer.aestronglyMeasurable

/-- **Integrability of the cut-off kernel.**  `potKerBall ρ` is integrable on `ℝ³` for every `ρ`:
the singularity `‖z‖⁻²` is integrable in dimension `3`, and the cut-off makes the kernel
compactly supported. -/
theorem integrable_potKerBall (ρ : ℝ) : Integrable (potKerBall ρ) volume := by
  have h1 : IntegrableOn (fun z : R3 => 1 + ‖z‖ ^ (-2 : ℝ)) (Metric.ball (0 : R3) ρ) volume :=
    Work.CoreResiduals.BiotSavart.integrableOn_one_add_norm_rpow_ball (-2) ρ (by norm_num)
  have h2 : Integrable ((Metric.ball (0 : R3) ρ).indicator fun z : R3 => 1 + ‖z‖ ^ (-2 : ℝ))
      volume :=
    (integrable_indicator_iff measurableSet_ball).mpr h1
  refine Integrable.mono' h2 (aestronglyMeasurable_potKer.indicator measurableSet_ball) ?_
  filter_upwards with z
  by_cases hz : z ∈ Metric.ball (0 : R3) ρ
  · simp only [potKerBall, Set.indicator_of_mem hz]
    exact le_trans (potKer_norm_le z) (le_add_of_nonneg_left zero_le_one)
  · simp only [potKerBall, Set.indicator_of_notMem hz]
    simp


end

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.CrossAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

open FiniteTimeSingularity MeasureTheory
open scoped Matrix

namespace Work.FTS.BSSwirl

noncomputable section

/-! ## The cross product of two vectors of `ℝ³` -/

/-- The cross product of `a b : ℝ³`, transported from the coordinate cross product on
`Fin 3 → ℝ`. -/
def crossR3 (a b : R3) : R3 := WithLp.toLp 2 (a.ofLp ⨯₃ b.ofLp)

@[simp] lemma crossR3_ofLp (a b : R3) : (crossR3 a b).ofLp = a.ofLp ⨯₃ b.ofLp := rfl

/-- Anticommutativity of the cross product, in the orientation suited to `simp`. -/
@[simp] lemma neg_crossR3 (a b : R3) : - crossR3 a b = crossR3 b a := by
  simp only [crossR3, ← WithLp.toLp_neg, cross_anticomm]


lemma crossR3_add_left (a₁ a₂ b : R3) : crossR3 (a₁ + a₂) b = crossR3 a₁ b + crossR3 a₂ b := by
  apply PiLp.ext; intro j
  simp only [crossR3_ofLp, WithLp.ofLp_add, map_add, LinearMap.add_apply, Pi.add_apply]

lemma crossR3_smul_left (c : ℝ) (a b : R3) : crossR3 (c • a) b = c • crossR3 a b := by
  apply PiLp.ext; intro j
  simp only [crossR3_ofLp, WithLp.ofLp_smul, map_smul, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul]

lemma crossR3_add_right (a b₁ b₂ : R3) : crossR3 a (b₁ + b₂) = crossR3 a b₁ + crossR3 a b₂ := by
  apply PiLp.ext; intro j
  simp only [crossR3_ofLp, WithLp.ofLp_add, map_add, Pi.add_apply]

lemma crossR3_smul_right (c : ℝ) (a b : R3) : crossR3 a (c • b) = c • crossR3 a b := by
  apply PiLp.ext; intro j
  simp only [crossR3_ofLp, WithLp.ofLp_smul, map_smul, Pi.smul_apply, smul_eq_mul]

/-- The norm of the cross product is at most the product of the norms. -/
lemma norm_crossR3_le (a b : R3) : ‖crossR3 a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h := InnerProductGeometry.norm_ofLp_crossProduct a b
  rw [crossR3, h]
  have h1 : Real.sin (InnerProductGeometry.angle a b) ≤ 1 := Real.sin_le_one _
  have h2 : 0 ≤ ‖a‖ * ‖b‖ := mul_nonneg (norm_nonneg a) (norm_nonneg b)
  nlinarith [h1, h2]

/-- The cross product of `ℝ³` as a continuous bilinear map. -/
def crossBilin : R3 →L[ℝ] R3 →L[ℝ] R3 :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ crossR3 crossR3_add_left crossR3_smul_left crossR3_add_right
      crossR3_smul_right)
    1 (fun a b => by simpa using norm_crossR3_le a b)

@[simp] lemma crossBilin_apply (a b : R3) : crossBilin a b = crossR3 a b := rfl

@[simp] lemma crossR3_zero_right (a : R3) : crossR3 a 0 = 0 := by simp [crossR3]

@[simp] lemma crossR3_zero_left (b : R3) : crossR3 0 b = 0 := by simp [crossR3]

/-! ## The scalar triple product -/

/-- The inner product of two vectors of `ℝ³` is the coordinatewise dot product. -/
lemma inner_eq_dot (u v : R3) : inner ℝ u v = u.ofLp ⬝ᵥ v.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.star_apply]
  rw [star_trivial]
  ring

/-- The cyclic identity for the scalar triple product: `⟪a × b, c⟫ = ⟪a, b × c⟫`. -/
lemma inner_crossR3_cyclic₁ (a b c : R3) :
    inner ℝ (crossR3 a b) c = inner ℝ a (crossR3 b c) := by
  rw [inner_eq_dot, inner_eq_dot, crossR3_ofLp, crossR3_ofLp,
    dotProduct_comm (a.ofLp ⨯₃ b.ofLp) c.ofLp]
  exact triple_product_permutation c.ofLp a.ofLp b.ofLp

/-- The cyclic identity for the scalar triple product: `⟪a, b × c⟫ = ⟪b, c × a⟫`. -/
lemma inner_crossR3_cyclic₂ (a b c : R3) :
    inner ℝ a (crossR3 b c) = inner ℝ b (crossR3 c a) := by
  rw [inner_eq_dot, inner_eq_dot, crossR3_ofLp, crossR3_ofLp]
  exact triple_product_permutation a.ofLp b.ofLp c.ofLp

/-! ## The curl and the divergence in the standard basis -/

/-- The curl of a field is `∑ i, eᵢ × ∂ᵢu`. -/
lemma vorticity_eq_sum_crossR3 (u : R3 → R3) (x : R3) :
    vorticity u x = ∑ i, crossR3 (e i) (fderiv ℝ u x (e i)) := by
  simp [vorticity, crossR3]

/-- The divergence of a field is `∑ i, ⟪eᵢ, ∂ᵢu⟫`. -/
lemma div_eq_sum_inner (u : R3 → R3) (x : R3) :
    div u x = ∑ i, inner ℝ (e i) (fderiv ℝ u x (e i)) := by
  rw [div,
    show (fderiv ℝ u x).trace ℝ R3 = ((fderiv ℝ u x) : R3 →ₗ[ℝ] R3).trace ℝ R3 from rfl,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_apply]
  rfl

/-! ## The derivative of a cross product of two fields -/

/-- **Product rule for the cross product.**  If `V` and `Ψ` are differentiable at `x`, then so is
`y ↦ V y × Ψ y`, with derivative `∂V(x)[·] × Ψ(x) + V(x) × ∂Ψ(x)[·]`. -/
theorem hasFDerivAt_crossR3 {V Ψ : R3 → R3} {x : R3}
    (hV : HasFDerivAt V (fderiv ℝ V x) x) (hΨ : HasFDerivAt Ψ (fderiv ℝ Ψ x) x) :
    HasFDerivAt (fun y => crossR3 (V y) (Ψ y))
      ((crossBilin.flip (Ψ x)).comp (fderiv ℝ V x) + (crossBilin (V x)).comp (fderiv ℝ Ψ x))
      x := by
  have hc : HasFDerivAt (fun y => crossBilin (V y)) (crossBilin.comp (fderiv ℝ V x)) x :=
    crossBilin.hasFDerivAt.comp x hV
  have hmain := hc.clm_apply hΨ
  have hEq : (crossBilin (V x)).comp (fderiv ℝ Ψ x)
      + (crossBilin.comp (fderiv ℝ V x)).flip (Ψ x)
      = (crossBilin.flip (Ψ x)).comp (fderiv ℝ V x)
        + (crossBilin (V x)).comp (fderiv ℝ Ψ x) := by
    ext u
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
    exact add_comm _ _
  simpa only [crossBilin_apply, hEq] using hmain

/-- The cross product of two `C^n` fields is `C^n`. -/
theorem contDiff_crossR3 {V Ψ : R3 → R3} {n : ℕ∞} (hV : ContDiff ℝ n V) (hΨ : ContDiff ℝ n Ψ) :
    ContDiff ℝ n (fun y => crossR3 (V y) (Ψ y)) :=
  (crossBilin.contDiff.comp hV).clm_apply hΨ

/-- The curl of a `C¹` field is continuous. -/
theorem continuous_vorticity {u : R3 → R3} (hu : ContDiff ℝ 1 u) : Continuous (vorticity u) := by
  have h1 : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hfun : vorticity u = fun x => ∑ i, crossBilin (e i) (fderiv ℝ u x (e i)) := by
    funext x
    simp only [vorticity_eq_sum_crossR3, crossBilin_apply]
  rw [hfun]
  refine continuous_finset_sum _ fun i _ => ?_
  refine (crossBilin (e i)).continuous.comp ?_
  have h2 : Continuous fun x => (ContinuousLinearMap.apply ℝ R3 (e i)) (fderiv ℝ u x) :=
    (ContinuousLinearMap.apply ℝ R3 (e i)).continuous.comp h1
  simpa [ContinuousLinearMap.apply_apply] using h2

end

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.VortVV.laplacian_apply_e =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl.VortVV

open scoped Topology

/-- The standard orthonormal basis `EuclideanSpace.basisFun (Fin 3) ℝ` of `ℝ³` agrees with the
workspace basis `FiniteTimeSingularity.e`.  (A local copy of `Work.FTS.BSSwirl.basisFun_eq_e`, so
that this module needs nothing from the pressure area; the two live in different namespaces, so
importing both is harmless.) -/
theorem basisFun_eq_e_ (i : Fin 3) :
    (EuclideanSpace.basisFun (Fin 3) ℝ) i = FiniteTimeSingularity.e i := by
  rw [EuclideanSpace.basisFun_apply, FiniteTimeSingularity.e]
  rfl

/-- **The Laplacian in the orthonormal basis `e`.**  For an arbitrary (not assumed differentiable)
`Ψ : ℝ³ → ℝ³`, Mathlib's `Laplacian.laplacian` — the second derivative paired with the canonical
covariant tensor, i.e. the sum of the diagonal entries of the Hessian in an orthonormal basis — is
the sum `∑ᵢ ∂ᵢ∂ᵢΨ(x)` in the workspace basis `e` of `ChallengeDeps.lean`.

No regularity hypothesis is needed: `Laplacian.laplacian Ψ` is by definition
`tensorIteratedFDerivTwo ℝ Ψ · (canonicalCovariantTensor ℝ³)`, and
`InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis` rewrites it as the plain sum of
`iteratedFDeriv ℝ 2 Ψ x ![v i, v i]` over any orthonormal basis `v`, for *every* `Ψ`; the
instances of `fderiv` occurring there are total functions, so the identity is an algebraic
identity about `fderiv`, not a regularity statement.  Finally
`iteratedFDeriv_two_apply` identifies `iteratedFDeriv ℝ 2 Ψ x ![u, u]` with
`fderiv ℝ (fderiv ℝ Ψ) x u u`. -/
theorem laplacian_apply_e (Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3)
    (x : Work.FTS.BSSwirl.R3) :
    Laplacian.laplacian Ψ x
      = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ Ψ) x (FiniteTimeSingularity.e i)
          (FiniteTimeSingularity.e i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis Ψ
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [basisFun_eq_e_ i, iteratedFDeriv_two_apply]
  simp

end Work.FTS.BSSwirl.VortVV
end
-- ===== merged: Submission.Work.FTS.BSSwirl.ball_lintegral_rpow_sub_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl

open MeasureTheory Set

/-- **Translation invariance of the set `lintegral` over an open ball**, in the centred
form: for any `ℝ≥0∞`-valued `F`, `∫⁻_{B(c,r)} F (y - c) = ∫⁻_{B(0,r)} F`.  The map
`y ↦ y - c` is measure preserving and carries `B(c,r)` onto `B(0,r)`. -/
private lemma lintegral_ball_sub_center_eq (c : R3) (r : ℝ) (F : R3 → ENNReal) :
    ∫⁻ y in Metric.ball c r, F (y - c) = ∫⁻ z in Metric.ball (0 : R3) r, F z := by
  classical
  have hs : MeasurableSet (Metric.ball c r) := Metric.isOpen_ball.measurableSet
  have hs0 : MeasurableSet (Metric.ball (0 : R3) r) := Metric.isOpen_ball.measurableSet
  have hmem : ∀ y : R3, y ∈ Metric.ball c r ↔ y - c ∈ Metric.ball (0 : R3) r := by
    intro y
    rw [Metric.mem_ball, Metric.mem_ball, dist_eq_norm, dist_eq_norm, sub_zero]
  rw [← lintegral_indicator hs (fun y => F (y - c))]
  have h1 : (fun y => (Metric.ball c r).indicator (fun y => F (y - c)) y)
      = fun y => (Metric.ball (0 : R3) r).indicator F (y - c) := by
    funext y
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ Metric.ball c r
    · simp [hy, (hmem y).mp hy]
    · have hy' : y - c ∉ Metric.ball (0 : R3) r := fun h => hy ((hmem y).mpr h)
      simp [hy, hy']
  rw [h1, lintegral_sub_right_eq_self
    (fun z => (Metric.ball (0 : R3) r).indicator F z) c]
  rw [lintegral_indicator hs0 F]

theorem ball_lintegral_rpow_sub_le {s : ℝ} (hs : -3 < s) (c : Work.FTS.BSSwirl.R3) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ y in Metric.ball c ρ, ENNReal.ofReal (‖c - y‖ ^ s)
      ≤ ENNReal.ofReal (4 * Real.pi * ρ ^ (s + 3) / (s + 3)) := by
  -- `‖c - y‖ = ‖y - c‖`, so the integrand is a function of `y - c`.
  have hswap : (fun y : R3 => ENNReal.ofReal (‖c - y‖ ^ s))
      = fun y : R3 => ENNReal.ofReal (‖y - c‖ ^ s) := by
    funext y
    rw [norm_sub_rev]
  rw [hswap]
  -- translate the ball to the origin
  rw [lintegral_ball_sub_center_eq c ρ (fun z : R3 => ENNReal.ofReal (‖z‖ ^ s))]
  -- and evaluate the radial power integral
  exact le_of_eq (Work.CoreResiduals.BiotSavart.lintegral_ball_norm_rpow s hs ρ hρ)

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.contDiff_div_and_support =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-- The trace as a linear functional on the endomorphisms of `ℝ³`, i.e. the linear map
`A ↦ trace A` underlying `FiniteTimeSingularity.div`. -/
noncomputable def divTrLin : (R3 →L[ℝ] R3) →ₗ[ℝ] ℝ :=
  (LinearMap.trace ℝ R3).comp (ContinuousLinearMap.coeLM ℝ)

/-- **The trace as a continuous linear functional on `ℝ³ →L[ℝ] ℝ³`.**  The space `ℝ³ →L[ℝ] ℝ³` is
finite-dimensional, so every linear functional on it is continuous. -/
noncomputable def divTrCLM : (R3 →L[ℝ] R3) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap divTrLin

/-- The defining value of `divTrCLM`: it is the trace. -/
theorem divTrCLM_apply (A : R3 →L[ℝ] R3) : divTrCLM A = A.trace ℝ R3 := rfl

/-- `div` is the continuous linear functional `divTrCLM` applied to the derivative. -/
theorem div_eq_divTrCLM (Ψ : R3 → R3) (x : R3) :
    FiniteTimeSingularity.div Ψ x = divTrCLM (fderiv ℝ Ψ x) := rfl

/-- **The derivative vanishes off the (topological) support.**  If `x` is outside `tsupport Ψ` then
`Ψ` vanishes on a whole neighbourhood of `x`, hence is differentiable there with derivative `0`. -/
theorem fderiv_eq_zero_of_notMem_tsupport {Ψ : R3 → R3} {x : R3} (hx : x ∉ tsupport Ψ) :
    fderiv ℝ Ψ x = 0 := by
  have hmem : (tsupport Ψ)ᶜ ∈ 𝓝 x := (isClosed_tsupport Ψ).isOpen_compl.mem_nhds hx
  have hev : Ψ =ᶠ[𝓝 x] fun _ : R3 => 0 := by
    filter_upwards [hmem] with y hy
    by_contra h
    exact hy (subset_tsupport Ψ (Function.mem_support.mpr h))
  rw [hev.fderiv_eq, fderiv_const_apply (0 : R3)]

theorem contDiff_div_and_support {Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (hc : HasCompactSupport Ψ) :
    (∀ n : ℕ, ContDiff ℝ n (fun x => FiniteTimeSingularity.div Ψ x)) ∧
      HasCompactSupport (fun x => FiniteTimeSingularity.div Ψ x) := by
  have hdiv : (fun x => FiniteTimeSingularity.div Ψ x)
      = fun x => divTrCLM (fderiv ℝ Ψ x) := by
    funext x
    exact div_eq_divTrCLM Ψ x
  constructor
  · intro n
    rw [hdiv]
    have hf : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ Ψ) :=
      (hΨ (n + 1)).fderiv_right (by simp)
    exact (ContinuousLinearMap.contDiff divTrCLM).comp hf
  · rw [hdiv]
    refine hc.mono' ?_
    intro x hx
    by_contra hx'
    exact (Function.mem_support.mp hx) (by rw [fderiv_eq_zero_of_notMem_tsupport hx']; simp)

end

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.convolution_inv_norm_fderiv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Convolution Topology

namespace Work.FTS.BSSwirl

noncomputable section

/-- The Newtonian kernel `z ↦ ‖z‖⁻¹` is locally integrable on `ℝ³`: in dimension `3` the
singularity at the origin is summable (`∫_{B(0,ρ)} ‖z‖⁻¹ dz = 2πρ² < ∞`). -/
theorem locallyIntegrable_inv_norm_kernel :
    LocallyIntegrable (fun z : R3 => (‖z‖)⁻¹) volume := by
  refine MeasureTheory.locallyIntegrable_of_norm_le_rpow (f := fun z : R3 => (‖z‖)⁻¹)
    (C := 1) (α := 1) ?_ ?_ ?_ ?_
  · simp
  · simp
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)), Real.rpow_neg_one,
      one_mul]
  · exact (Measurable.inv measurable_norm).aestronglyMeasurable

theorem convolution_inv_norm_fderiv {k : Work.FTS.BSSwirl.R3 → ℝ}
    (hk : ContDiff ℝ 1 k) (hc : HasCompactSupport k) (y v : Work.FTS.BSSwirl.R3) :
    (fderiv ℝ (fun y' : Work.FTS.BSSwirl.R3 => ∫ t, (‖y' - t‖)⁻¹ * k t) y) v
      = ∫ x, (‖x - y‖)⁻¹ * (fderiv ℝ k x) v := by
  have hMk : LocallyIntegrable (fun z : R3 => (‖z‖)⁻¹) volume :=
    locallyIntegrable_inv_norm_kernel
  -- The potential is the convolution of `k` with the Newtonian kernel.
  have hconv : (fun y' : R3 => ∫ t, (‖y' - t‖)⁻¹ * k t)
      = convolution k (fun z : R3 => (‖z‖)⁻¹) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext y'
    rw [MeasureTheory.convolution_lsmul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [smul_eq_mul, mul_comm]
  -- Its derivative, as computed by the convolution calculus.
  have hderiv := hc.hasFDerivAt_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk hMk y
  -- Integrability of the `ℝ³ →L[ℝ] ℝ`-valued integrand, so that evaluation at `v` commutes
  -- with the integral.
  have hcf : HasCompactSupport (fderiv ℝ k) := hc.fderiv ℝ
  have hcont : Continuous (fderiv ℝ k) := hk.continuous_fderiv one_ne_zero
  have hex : ConvolutionExists (fderiv ℝ k) (fun z : R3 => (‖z‖)⁻¹)
      (ContinuousLinearMap.precompL R3 (ContinuousLinearMap.lsmul ℝ ℝ)) volume :=
    HasCompactSupport.convolutionExists_left _ hcf hcont hMk
  have hint : Integrable (fun t : R3 => (ContinuousLinearMap.precompL R3
      (ContinuousLinearMap.lsmul ℝ ℝ)) ((fderiv ℝ k) t) ((fun z : R3 => (‖z‖)⁻¹) (y - t)))
      volume := hex y
  -- Evaluate the derivative at `v` and identify the integrand.
  have hval : (convolution (fderiv ℝ k) (fun z : R3 => (‖z‖)⁻¹)
        (ContinuousLinearMap.precompL R3 (ContinuousLinearMap.lsmul ℝ ℝ)) volume y) v
      = ∫ x, (‖x - y‖)⁻¹ * (fderiv ℝ k x) v := by
    rw [MeasureTheory.convolution_def]
    rw [ContinuousLinearMap.integral_apply hint]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
      norm_sub_rev, mul_comm]
  rw [hconv, hderiv.fderiv, hval]

end

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.eq_zero_of_forall_inner_test =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl

open MeasureTheory Metric Set Function

theorem eq_zero_of_forall_inner_test {V : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    (hV : Continuous V)
    (h : ∀ Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3, (∀ n : ℕ, ContDiff ℝ n Ψ) →
      HasCompactSupport Ψ → ∫ x, inner ℝ (V x) (Ψ x) = 0) :
    ∀ x, V x = 0 := by
  intro x₀
  -- It suffices to prove `⟪V x₀, c⟫ = 0` for every `c`; take `c = V x₀` at the end.
  have key : ∀ c : R3, inner ℝ (V x₀) c = 0 := by
    intro c
    -- The bound `|⟪V x₀, c⟫| ≤ δ ‖c‖` for every `δ > 0`.
    have bound : ∀ δ : ℝ, 0 < δ → |inner ℝ (V x₀) c| ≤ δ * ‖c‖ := by
      intro δ hδ
      -- the radius of the bump, from the continuity of `V` at `x₀`
      obtain ⟨η, hηpos, hη⟩ := Metric.continuousAt_iff.mp hV.continuousAt δ hδ
      -- a smooth bump supported in `ball x₀ η`, equal to `1` at `x₀`
      let f : ContDiffBump x₀ := ⟨η / 2, η, by linarith, by linarith⟩
      have hfrIn : f.rIn = η / 2 := rfl
      have hfrOut : f.rOut = η := rfl
      have hfx₀ : f x₀ = 1 :=
        f.one_of_mem_closedBall (mem_closedBall_self (by rw [hfrIn]; linarith))
      -- test against `Ψ = f • c`
      have hΨ : ∫ x, inner ℝ (V x) (f x • c) = 0 :=
        h (fun x : R3 => f x • c) (fun n => f.contDiff.smul_const c)
          (f.hasCompactSupport.smul_right (f' := fun _ : R3 => c))
      have hint : ∫ x, f x * inner ℝ (V x) c = 0 := by
        rw [← hΨ]
        refine integral_congr_ae ?_
        filter_upwards with x
        rw [real_inner_smul_right]
      -- the bump is continuous, integrable and has positive integral
      have hfcont : Continuous fun x : R3 => f x := f.continuous
      have hfint : Integrable (fun x : R3 => f x) :=
        hfcont.integrable_of_hasCompactSupport f.hasCompactSupport
      have hA : 0 < ∫ x, f x :=
        integral_pos_of_integrable_nonneg_nonzero (x := x₀) hfcont hfint (fun x => f.nonneg)
          (by rw [hfx₀]; norm_num)
      have hInt1 : Integrable (fun x : R3 => f x * inner ℝ (V x₀) c) := hfint.mul_const _
      have hInt2 : Integrable (fun x : R3 => f x * inner ℝ (V x) c) :=
        (hfcont.mul (hV.inner continuous_const)).integrable_of_hasCompactSupport
          (f.hasCompactSupport.mul_right (f' := fun x : R3 => inner ℝ (V x) c))
      -- the exact identity `⟪V x₀, c⟫ ∫ f = ∫ f (⟪V x₀, c⟫ - ⟪V x, c⟫)`
      have hkey : inner ℝ (V x₀) c * (∫ x, f x)
          = ∫ x, f x * (inner ℝ (V x₀) c - inner ℝ (V x) c) := by
        have hsub : (∫ x, f x * (inner ℝ (V x₀) c - inner ℝ (V x) c))
            = (∫ x, f x * inner ℝ (V x₀) c) - (∫ x, f x * inner ℝ (V x) c) := by
          rw [← integral_sub hInt1 hInt2]
          refine integral_congr_ae ?_
          filter_upwards with x
          rw [mul_sub]
        rw [hsub, integral_mul_const (inner ℝ (V x₀) c) (fun x : R3 => f x), hint, sub_zero]
        ring
      have hbd : |inner ℝ (V x₀) c| * (∫ x, f x) ≤ δ * ‖c‖ * (∫ x, f x) := by
        calc
          |inner ℝ (V x₀) c| * (∫ x, f x)
              = |inner ℝ (V x₀) c * (∫ x, f x)| := by rw [abs_mul, abs_of_pos hA]
          _ = |∫ x, f x * (inner ℝ (V x₀) c - inner ℝ (V x) c)| := by rw [hkey]
          _ ≤ ∫ x, |f x * (inner ℝ (V x₀) c - inner ℝ (V x) c)| :=
                abs_integral_le_integral_abs
          _ = ∫ x, f x * |inner ℝ (V x₀) c - inner ℝ (V x) c| := by
                refine integral_congr_ae ?_
                filter_upwards with x
                rw [abs_mul, abs_of_nonneg f.nonneg]
          _ ≤ ∫ x, f x * (δ * ‖c‖) := by
                refine integral_mono ?_ ?_ ?_
                · have habscont : Continuous
                      (fun x : R3 => |inner ℝ (V x₀) c - inner ℝ (V x) c|) :=
                    Continuous.abs <|
                      (continuous_const :
                          Continuous (fun _ : R3 => inner ℝ (V x₀) c)).sub
                        (hV.inner (continuous_const : Continuous (fun _ : R3 => c)))
                  exact (hfcont.mul habscont).integrable_of_hasCompactSupport
                    (f.hasCompactSupport.mul_right
                      (f' := fun x : R3 => |inner ℝ (V x₀) c - inner ℝ (V x) c|))
                · exact hfint.mul_const _
                · intro x
                  by_cases hfx : f x = 0
                  · simp [hfx]
                  · -- on the support of the bump, `V` is `δ`-close to `V x₀`
                    have hxball : dist x x₀ < η := by
                      have hx : x ∈ Function.support f := Function.mem_support.mpr hfx
                      rw [f.support_eq, hfrOut, mem_ball] at hx
                      exact hx
                    have hVbd : dist (V x) (V x₀) ≤ δ := le_of_lt (hη (x := x) hxball)
                    refine mul_le_mul_of_nonneg_left ?_ f.nonneg
                    calc |inner ℝ (V x₀) c - inner ℝ (V x) c|
                        = |inner ℝ (V x₀ - V x) c| := by rw [inner_sub_left]
                      _ ≤ ‖V x₀ - V x‖ * ‖c‖ := abs_real_inner_le_norm _ _
                      _ = dist (V x) (V x₀) * ‖c‖ := by rw [dist_eq_norm, norm_sub_rev]
                      _ ≤ δ * ‖c‖ := mul_le_mul_of_nonneg_right hVbd (norm_nonneg c)
          _ = δ * ‖c‖ * (∫ x, f x) := by
                rw [integral_mul_const (δ * ‖c‖) (fun x : R3 => f x)]
                ring
      exact le_of_mul_le_mul_right hbd hA
    -- `|⟪V x₀, c⟫| ≤ δ ‖c‖` for all `δ > 0`, so it vanishes
    have hz : |inner ℝ (V x₀) c| = 0 := by
      refine le_antisymm (le_of_forall_pos_le_add fun e he => ?_) (abs_nonneg _)
      have h1 := bound (e / (‖c‖ + 1)) (by positivity)
      have h2 : e / (‖c‖ + 1) * ‖c‖ ≤ e := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < ‖c‖ + 1)]
        nlinarith [norm_nonneg c]
      linarith
    exact abs_eq_zero.mp hz
  exact inner_self_eq_zero.mp (key (V x₀))

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.integrableOn_inv_norm_sub_closedBall =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Metric
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-- **The Newtonian kernel is integrable on a ball centred at the origin of `ℝ³`.**

This is the borderline case `s = -1 > -3` of the radial threshold in dimension three: the
weighted integral `∫₀^ρ t^(dim - 1) t^(-1) dt = ∫₀^ρ t dt` converges.  It is the
`integrableOn_ball_of_norm_le_rpow` instance with `C = 1`, `α = 1`. -/
theorem integrableOn_inv_norm_ball_zero (ρ : ℝ) :
    IntegrableOn (fun y : R3 => (‖y‖)⁻¹) (Metric.ball (0 : R3) ρ) volume := by
  have hdim : Module.finrank ℝ R3 = 3 := by
    simp only [R3]
    exact finrank_euclideanSpace_fin
  refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (μ := volume)
    (f := fun y : R3 => (‖y‖)⁻¹) (C := 1) (α := 1) (r := ρ) ?_ ?_ ?_ ?_
  · rw [hdim]; norm_num
  · rw [hdim]; norm_num
  · filter_upwards with x
    rw [norm_inv, norm_norm, Real.rpow_neg_one, one_mul]
  · measurability

/-- **`‖z - c‖⁻¹` is integrable on the closed ball of centre `c` and radius `r` in `ℝ³`.**

The Newtonian kernel is locally integrable in dimension three, and `Metric.closedBall c r` is
bounded; away from `c` the integrand is even bounded.  The proof reduces to the ball centred at
the origin (translation invariance of Lebesgue measure) and then to
`integrableOn_inv_norm_ball_zero`. -/
theorem integrableOn_inv_norm_sub_closedBall (c : Work.FTS.BSSwirl.R3) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun z : Work.FTS.BSSwirl.R3 => (‖z - c‖)⁻¹) (Metric.closedBall c r)
      MeasureTheory.volume := by
  rcases lt_or_ge r 0 with hr | hr
  · -- Degenerate ball: empty.
    rw [Metric.closedBall_eq_empty.mpr hr]
    exact integrableOn_empty
  · -- Translate the ball at the origin of radius `r + 1 > r` to the ball at `c`.
    have hset : (fun x : R3 => x + c) ⁻¹' Metric.ball c (r + 1) = Metric.ball (0 : R3) (r + 1) := by
      ext x
      simp [Metric.mem_ball, dist_eq_norm]
    have hpre : IntegrableOn ((fun z : R3 => (‖z - c‖)⁻¹) ∘ (fun x : R3 => x + c))
        ((fun x : R3 => x + c) ⁻¹' Metric.ball c (r + 1)) volume := by
      rw [hset]
      simpa [Function.comp_def] using integrableOn_inv_norm_ball_zero (r + 1)
    have hc : IntegrableOn (fun z : R3 => (‖z - c‖)⁻¹) (Metric.ball c (r + 1)) volume :=
      (MeasureTheory.MeasurePreserving.integrableOn_comp_preimage
        (measurePreserving_add_right volume c)
        (Homeomorph.measurableEmbedding (Homeomorph.addRight c))
        (f := fun z : R3 => (‖z - c‖)⁻¹) (s := Metric.ball c (r + 1))).mp hpre
    exact hc.mono_set (Metric.closedBall_subset_ball (by linarith))

end

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.integrable_inv_norm_smul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal

namespace Work.FTS.BSSwirl

theorem integrable_inv_norm_smul {ω : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3} {R M : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume) (u : Work.FTS.BSSwirl.R3) :
    MeasureTheory.Integrable (fun y => (‖u - y‖)⁻¹ • ω y) MeasureTheory.volume := by
  -- `‖·‖⁻¹` is locally integrable in dimension `3`, being dominated by `‖·‖ ^ (-1)`.
  have hbase : LocallyIntegrable (fun z : R3 => (‖z‖)⁻¹) volume := by
    refine MeasureTheory.locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) ?_ ?_ ?_ ?_
    · simp
    · simp
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)), Real.rpow_neg_one,
        one_mul]
    · exact (Measurable.inv measurable_norm).aestronglyMeasurable
  -- translation invariance moves the singularity from `0` to `u`
  have htrans : LocallyIntegrable (fun z : R3 => (‖u - z‖)⁻¹) volume := by
    let e : R3 ≃ₜ R3 :=
      { toFun := fun z => z - u
        invFun := fun z => z + u
        left_inv := fun z => by simp
        right_inv := fun z => by simp
        continuous_toFun := continuous_id.sub continuous_const
        continuous_invFun := continuous_id.add continuous_const }
    have hmap : Measure.map (⇑e) volume = volume := by
      have h := Measure.IsAddRightInvariant.map_add_right_eq_self (μ := (volume : Measure R3)) (-u)
      simpa [e, sub_eq_add_neg] using h
    have h1 : LocallyIntegrable (fun w : R3 => (‖w‖)⁻¹) (Measure.map (⇑e) volume) := by
      rw [hmap]; exact hbase
    have h2 := (locallyIntegrable_map_homeomorph e).mp h1
    have hae : ((fun w : R3 => (‖w‖)⁻¹) ∘ ⇑e) =ᵐ[volume] (fun z : R3 => (‖u - z‖)⁻¹) := by
      filter_upwards with z
      show (‖e z‖)⁻¹ = (‖u - z‖)⁻¹
      rw [show e z = z - u from rfl, norm_sub_rev]
    exact h2.congr hae
  -- hence it is integrable on the compact support ball
  have hIntBall : IntegrableOn (fun z : R3 => (‖u - z‖)⁻¹) (Metric.closedBall (0 : R3) R)
      volume := by
    have hbig : IntegrableOn (fun z : R3 => (‖u - z‖)⁻¹)
        (Metric.closedBall u (|R| + ‖u‖ + 1)) volume :=
      htrans.integrableOn_isCompact (isCompact_closedBall u _)
    refine hbig.mono_set ?_
    intro y hy
    rw [Metric.mem_closedBall] at hy ⊢
    have h2 : dist 0 u = ‖u‖ := dist_zero_left u
    have habs : R ≤ |R| := le_abs_self R
    linarith [dist_triangle y 0 u, hy, habs, norm_nonneg u, h2]
  have hf_meas : AEStronglyMeasurable (fun y : R3 => (‖u - y‖)⁻¹ • ω y)
      (volume.restrict (Metric.closedBall (0 : R3) R)) := by
    have hm : Measurable (fun y : R3 => (‖u - y‖)⁻¹) :=
      (measurable_const.sub measurable_id).norm.inv
    exact (hm.aestronglyMeasurable.restrict).smul hmeas.restrict
  have hg : Integrable (fun y : R3 => M * (‖u - y‖)⁻¹)
      (volume.restrict (Metric.closedBall (0 : R3) R)) :=
    hIntBall.const_mul M
  have hbound : ∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : R3) R)),
      ‖(‖u - y‖)⁻¹ • ω y‖ ≤ M * (‖u - y‖)⁻¹ := by
    filter_upwards with y
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    calc (‖u - y‖)⁻¹ * ‖ω y‖ ≤ (‖u - y‖)⁻¹ * M :=
          mul_le_mul_of_nonneg_left (hbdd y) (inv_nonneg.mpr (norm_nonneg _))
      _ = M * (‖u - y‖)⁻¹ := by ring
  have hIntOn : IntegrableOn (fun y : R3 => (‖u - y‖)⁻¹ • ω y) (Metric.closedBall (0 : R3) R)
      volume :=
    Integrable.mono' hg hf_meas hbound
  -- the integrand vanishes off the ball, so `IntegrableOn` upgrades to `Integrable`
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp hIntOn
  intro y hy
  rw [Function.mem_support] at hy
  exact hsupp y (fun h => hy (by rw [h, smul_zero]))

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.integral_deriv_deriv_fcut_over_norm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS.BSSwirl

noncomputable section

/-- **Polar-coordinate reduction of a radial integral on `ℝ³`.**  For any `F : ℝ → ℝ`,

  `∫_{ℝ³} F ‖x‖ / ‖x‖ dx = 4π ∫_0^∞ y * F y dy`,

because `MeasureTheory.integral_fun_norm_addHaar` turns the left-hand side into
`3 • volume.real (ball 0 1) • ∫_0^∞ y^{3-1} • F y / y dy`, and then
`volume.real (ball 0 1) = 4π/3` while `y^2 * (F y / y) = y * F y` pointwise (the latter
identity includes `y = 0`, where both sides vanish). -/
private lemma integral_norm_radial_div (F : ℝ → ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin 3), F ‖x‖ / ‖x‖ = 4 * Real.pi * ∫ y in Set.Ioi (0 : ℝ), y * F y := by
  rw [MeasureTheory.integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (fun y : ℝ => F y / y)]
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
    simp [finrank_euclideanSpace]
  rw [hfin]
  norm_num
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (Metric.ball 0 1)
      = 4 * Real.pi / 3 := by
    rw [Measure.real_def, EuclideanSpace.volume_ball_fin_three]
    rw [show ENNReal.ofReal (1 : ℝ) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)
        = ENNReal.ofReal (Real.pi * 4 / 3) by simp]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [hvol]
  have hcongr : (∫ y in Set.Ioi (0 : ℝ), y ^ 2 * (F y / y))
      = ∫ y in Set.Ioi (0 : ℝ), y * F y := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy' : y ≠ 0 := ne_of_gt hy
    field_simp
  rw [hcongr]
  ring

/-- The `F = fcut''` case of `integral_norm_radial_div`. -/
private lemma integral_norm_radial_fcut_deriv2 :
    ∫ x : EuclideanSpace ℝ (Fin 3), deriv (deriv fcut) ‖x‖ / ‖x‖
      = 4 * Real.pi * ∫ y in Set.Ioi (0 : ℝ), y * deriv (deriv fcut) y :=
  integral_norm_radial_div (fun y => deriv (deriv fcut) y)

/-- **The `-4π` normalisation of the smooth cutoff.**  The radial second derivative of the
smooth step `fcut`, weighted by `‖w‖⁻¹`, integrates over `ℝ³` to `-4π`, the fundamental
solution of the Laplacian. -/
theorem integral_deriv_deriv_fcut_over_norm :
    ∫ w : EuclideanSpace ℝ (Fin 3), deriv (deriv Work.FTS.BSSwirl.fcut) ‖w‖ / ‖w‖ = -4 * Real.pi := by
  rw [integral_norm_radial_fcut_deriv2, integral_Ioi_mul_deriv_deriv_fcut]
  ring

end

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.integral_div_eq_zero_compact =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS.BSSwirl

/-- The directional derivative of a compactly supported `C¹` function is integrable: it is
continuous (`ContDiff.continuous_fderiv_apply`) and has compact support
(`HasCompactSupport.fderiv_apply`). -/
lemma integrable_fderiv_apply {h : R3 → ℝ} (hh : ContDiff ℝ 1 h) (hcs : HasCompactSupport h)
    (v : R3) : Integrable (fun x => (fderiv ℝ h x) v) := by
  have hcont : Continuous (fun x : R3 => (fderiv ℝ h x) v) :=
    (hh.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  exact hcont.integrable_of_hasCompactSupport (hcs.fderiv_apply ℝ v)

/-- **The directional derivative of a compactly supported `C¹` function integrates to zero.**
This is the divergence theorem with no boundary term in one direction, obtained from the
integration-by-parts identity `∫ h · (fderiv 1) = - ∫ (fderiv h) · 1` with the constant
function `1`. -/
lemma integral_fderiv_apply_eq_zero {h : R3 → ℝ} (hh : ContDiff ℝ 1 h)
    (hcs : HasCompactSupport h) (v : R3) : ∫ x, (fderiv ℝ h x) v = 0 := by
  -- Integrability of the three products occurring in the integration-by-parts identity.
  have hint : Integrable (fun x : R3 => (fderiv ℝ h x) v * (1:ℝ)) := by
    simpa using integrable_fderiv_apply hh hcs v
  have hzero : Integrable (fun x : R3 => h x * (fderiv ℝ (fun _ : R3 => (1:ℝ)) x) v) := by
    have h1 : (fun x : R3 => h x * (fderiv ℝ (fun _ : R3 => (1:ℝ)) x) v) = fun _ => (0:ℝ) := by
      funext x
      simp
    rw [h1]
    exact integrable_zero _ _ _
  have hhint : Integrable (fun x : R3 => h x * (1:ℝ)) := by
    simpa using hh.continuous.integrable_of_hasCompactSupport hcs
  -- Integration by parts for Fréchet derivatives, with the second function constant `1`.
  have key := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (E := R3) (F := ℝ) (G := ℝ) (W := ℝ) (f := h) (g := fun _ : R3 => (1:ℝ)) (v := v)
    (B := ContinuousLinearMap.mul ℝ ℝ) hint hzero hhint
    (fun x _ => (hh.differentiable one_ne_zero).differentiableAt)
    (fun x _ => differentiableAt_const (1:ℝ))
  have hL : ∫ x, (ContinuousLinearMap.mul ℝ ℝ) (h x) ((fderiv ℝ (fun _ : R3 => (1:ℝ)) x) v)
      = 0 := by
    simp
  rw [hL] at key
  simpa using key

/-- **The divergence of a compactly supported `C¹` vector field on `ℝ³` has zero integral.**

`div G x` is the trace of `fderiv ℝ G x`; expanded in the standard orthonormal basis it is the
sum of the directional derivatives of the scalar functions `y ↦ ⟪b i, G y⟫`, each of which
integrates to zero (`integral_fderiv_apply_eq_zero`). -/
theorem integral_div_eq_zero_compact {G : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    (hG : ContDiff ℝ 1 G) (hcs : HasCompactSupport G) :
    ∫ x, FiniteTimeSingularity.div G x = 0 := by
  set b := EuclideanSpace.basisFun (Fin 3) ℝ with hb
  -- The trace of the derivative, expanded in the orthonormal basis `b`.
  have hderiv : ∀ x, FiniteTimeSingularity.div G x
      = ∑ i, (fderiv ℝ (fun y => inner ℝ (b i) (G y)) x) (b i) := by
    intro x
    rw [show FiniteTimeSingularity.div G x = (fderiv ℝ G x).trace ℝ R3 from rfl]
    rw [show (fderiv ℝ G x).trace ℝ R3
        = LinearMap.trace ℝ R3 (fderiv ℝ G x).toLinearMap from rfl]
    rw [LinearMap.trace_eq_sum_inner _ b]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [fderiv_inner_apply ℝ (differentiableAt_const (b i))
        ((hG.differentiable one_ne_zero) x) (b i)]
    simp
  -- The scalar functions `y ↦ ⟪b i, G y⟫` are again `C¹` with compact support.
  have hcont : ∀ i, ContDiff ℝ 1 (fun y => inner ℝ (b i) (G y)) := fun i => by
    have h : ContDiff ℝ 1 (fun y => ((innerSL ℝ) (b i)) (G y)) :=
      ((innerSL ℝ (b i) : R3 →L[ℝ] ℝ).contDiff).comp hG
    simpa only [innerSL_apply_apply] using h
  have hsupp : ∀ i, HasCompactSupport (fun y => inner ℝ (b i) (G y)) := fun i => by
    have h := hcs.comp_left (g := (innerSL ℝ (b i) : R3 →L[ℝ] ℝ)) (by simp)
    simpa only [Function.comp_def, innerSL_apply_apply] using h
  calc ∫ x, FiniteTimeSingularity.div G x
      = ∫ x, ∑ i, (fderiv ℝ (fun y => inner ℝ (b i) (G y)) x) (b i) := by
        refine integral_congr_ae ?_
        filter_upwards with x
        rw [hderiv x]
    _ = ∑ i, ∫ x, (fderiv ℝ (fun y => inner ℝ (b i) (G y)) x) (b i) := by
        rw [integral_finsetSum]
        intro i _
        exact integrable_fderiv_apply (hcont i) (hsupp i) (b i)
    _ = 0 := by
        refine Finset.sum_eq_zero (fun i _ => ?_)
        exact integral_fderiv_apply_eq_zero (hcont i) (hsupp i) (b i)

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.sum_e_cross_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.BSSwirl.sum_e_cross_eq`

The identity expanding the curl-type sum `∑ i, e i × (⟪v, e i⟫ • w)` of the Biot--Savart
computation for a swirl vorticity: the standard basis vectors `e i = Pi.single i 1` of `ℝ³`
resolve every vector `v`, i.e.

  `∑ i, e i × (⟪v, e i⟫ • w) = v × w`

in `Fin 3 → ℝ`.  Indeed `crossProduct` is bilinear, so the left-hand side is
`∑ i, ⟪v, e i⟫ • (e i × w)`, and `v = ∑ i, ⟪v, e i⟫ • e i` expands `v × w` in the same way.
The statement below is the scalar-multiplied form in which the swirl computation consumes it,

  `∑ i, e i × (c • (⟪y - x, e i⟫ • w)) = c • (w × (x - y))`,

the point being that `w × (x - y) = (y - x) × w` by antisymmetry of the cross product.

Both the general identity (`sum_single_cross`) and the requested theorem are proved by the
finite coordinate computation in the standard basis, exactly as Mathlib proves its own
cross-product identities.
-/

namespace Work.FTS.BSSwirl

noncomputable section

/-- **The cross product computed on the standard basis.**  For vectors `a v : Fin 3 → ℝ`,
`∑ i, e i × (a i • v) = a × v`, where `e i = Pi.single i 1`.

This is the identity `a × v = ∑ i, a i • (e i × v)` obtained by expanding `a` in the standard
basis of `ℝ³` and using the bilinearity of the cross product.  It is proved directly in
coordinates (`cross_apply`), the vectors being functions `Fin 3 → ℝ`. -/
theorem sum_single_cross (a v : Fin 3 → ℝ) :
    (∑ i : Fin 3, crossProduct (Pi.single i (1 : ℝ)) (a i • v)) = crossProduct a v := by
  rw [Fin.sum_univ_three]
  simp only [cross_apply]
  ext j
  fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Fin.reduceFinMk,
      smul_eq_mul] <;> ring

theorem sum_e_cross_eq (x y w : Work.FTS.BSSwirl.R3) (c : ℝ) :
    (∑ i : Fin 3, crossProduct ((FiniteTimeSingularity.e i).ofLp)
        (c • (inner ℝ (y - x) (FiniteTimeSingularity.e i) • w.ofLp)))
      = c • crossProduct w.ofLp (x - y).ofLp := by
  -- `⟪y - x, e i⟫ = (y - x).ofLp i`: the coordinates of `y - x` are the pairings against `e i`.
  have hinner : ∀ i : Fin 3, inner ℝ (y - x) (FiniteTimeSingularity.e i) = (y - x).ofLp i := by
    intro i
    rw [show FiniteTimeSingularity.e i = EuclideanSpace.single i 1 from rfl]
    rw [EuclideanSpace.inner_single_right]
    simp
  simp only [hinner]
  -- `(e i).ofLp = Pi.single i 1`, i.e. `e i` is the `i`-th standard basis vector of `ℝ³`.
  simp only [FiniteTimeSingularity.e, WithLp.ofLp_toLp]
  -- Bilinearity of `crossProduct` moves the scalar out of the summand and the sum out of the
  -- scalar multiplication; the remaining sum is `sum_single_cross`.
  have hsum : (∑ i : Fin 3, crossProduct (Pi.single i (1 : ℝ)) (c • ((y - x).ofLp i • w.ofLp)))
      = c • crossProduct (y - x).ofLp w.ofLp := by
    calc (∑ i : Fin 3, crossProduct (Pi.single i (1 : ℝ)) (c • ((y - x).ofLp i • w.ofLp)))
        = ∑ i : Fin 3, c • crossProduct (Pi.single i (1 : ℝ)) ((y - x).ofLp i • w.ofLp) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [map_smul, map_smul]
      _ = c • ∑ i : Fin 3, crossProduct (Pi.single i (1 : ℝ)) ((y - x).ofLp i • w.ofLp) := by
          rw [← Finset.smul_sum]
      _ = c • crossProduct (y - x).ofLp w.ofLp := by rw [sum_single_cross]
  rw [hsum]
  -- Antisymmetry of the cross product turns `(y - x) × w` into `w × (x - y)`.
  have hsign : crossProduct (y - x).ofLp w.ofLp = crossProduct w.ofLp (x - y).ofLp := by
    have h1 : (x - y).ofLp = -((y - x).ofLp) := by
      rw [WithLp.ofLp_sub, WithLp.ofLp_sub, neg_sub]
    rw [h1, map_neg, cross_anticomm]
  rw [hsign]

end

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.tendsto_fcut_div_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-- `‖·‖⁻¹` is locally integrable on `ℝ³`: it is a Riesz kernel of order `1` in dimension `3`,
so it is dominated by `‖·‖ ^ (-1)` with `1 < 3`. -/
private lemma locallyIntegrable_inv_norm_fts :
    LocallyIntegrable (fun z : R3 => (‖z‖)⁻¹) volume := by
  refine MeasureTheory.locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) ?_ ?_ ?_ ?_
  · simp
  · simp
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)), Real.rpow_neg_one,
      one_mul]
  · exact (Measurable.inv measurable_norm).aestronglyMeasurable

/-- **The truncation of the singular kernel `‖z‖⁻¹` converges to the kernel itself.**

`∫ z, fcut(‖z‖/ε)/‖z‖ · g z  →  ∫ z, ‖z‖⁻¹ · g z` as `ε → 0⁺`, for `g` continuous with compact
support.  Dominated convergence: pointwise `fcut(‖z‖/ε) → 1` for `z ≠ 0`, and the integrand is
dominated by `‖z‖⁻¹ |g z|`, integrable because `g` is supported in a ball and `‖·‖⁻¹` is locally
integrable. -/
theorem tendsto_fcut_div_mul {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) :
    Filter.Tendsto (fun ε : ℝ => ∫ z, Work.FTS.BSSwirl.fcut (‖z‖ / ε) / ‖z‖ * g z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ z, ‖z‖⁻¹ * g z)) := by
  -- A ball containing the support of `g`, and a bound for `|g|`.
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : R3)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : R3) R).exists_bound_of_continuousOn hg.continuousOn
  have hM0 : (0 : ℝ) ≤ max C 1 := le_trans zero_le_one (le_max_right _ _)
  have hbdd : ∀ z : R3, |g z| ≤ max C 1 := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : R3) R
    · have h := hC z hz
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_max_left _ _)
    · have hz0 : g z = 0 := by
        by_contra h
        exact hz (hR (subset_tsupport g h))
      rw [hz0, abs_zero]
      exact le_trans zero_le_one (le_max_right _ _)
  -- The dominating function.
  set bound : R3 → ℝ :=
    (Metric.closedBall (0 : R3) R).indicator (fun z => max C 1 * (‖z‖)⁻¹) with hbounddef
  have hbound_int : Integrable bound := by
    rw [hbounddef, MeasureTheory.integrable_indicator_iff measurableSet_closedBall]
    exact (locallyIntegrable_inv_norm_fts.integrableOn_isCompact
      (isCompact_closedBall (0 : R3) R)).const_mul _
  -- Measurability of the integrand.
  have hF_meas : ∀ᶠ ε : ℝ in (𝓝[>] (0 : ℝ)),
      AEStronglyMeasurable (fun z : R3 => fcut (‖z‖ / ε) / ‖z‖ * g z) volume := by
    refine Filter.Eventually.of_forall (fun ε => ?_)
    have h1 : Measurable (fun z : R3 => fcut (‖z‖ / ε)) :=
      (contDiff_fcut 0).continuous.measurable.comp ((continuous_norm.div_const ε).measurable)
    exact ((h1.div measurable_norm).mul hg.measurable).aestronglyMeasurable
  -- Pointwise domination by `bound`.
  have h_bound : ∀ᶠ ε : ℝ in (𝓝[>] (0 : ℝ)),
      ∀ᵐ z ∂(volume : Measure (R3)), ‖fcut (‖z‖ / ε) / ‖z‖ * g z‖ ≤ bound z := by
    refine Filter.Eventually.of_forall
      (fun ε => Filter.Eventually.of_forall (fun z => ?_))
    have hnorm : ‖fcut (‖z‖ / ε) / ‖z‖ * g z‖ = |fcut (‖z‖ / ε)| * (‖z‖)⁻¹ * |g z| := by
      simp only [norm_mul, norm_div, Real.norm_eq_abs]
      rw [abs_of_nonneg (norm_nonneg z), div_eq_mul_inv]
    rw [hnorm]
    by_cases hz : z ∈ Metric.closedBall (0 : R3) R
    · rw [hbounddef, Set.indicator_of_mem hz]
      have ha : |fcut (‖z‖ / ε)| ≤ 1 :=
        abs_le.mpr ⟨by linarith [fcut_nonneg (‖z‖ / ε)], fcut_le_one _⟩
      have hc0 : (0 : ℝ) ≤ (‖z‖)⁻¹ := inv_nonneg.mpr (norm_nonneg z)
      have hmain : |fcut (‖z‖ / ε)| * (‖z‖)⁻¹ * |g z| ≤ max C 1 * (‖z‖)⁻¹ := by
        calc |fcut (‖z‖ / ε)| * (‖z‖)⁻¹ * |g z|
            = (|fcut (‖z‖ / ε)| * (‖z‖)⁻¹) * |g z| := by ring
          _ ≤ (1 * (‖z‖)⁻¹) * max C 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_right ha hc0) (hbdd z) (abs_nonneg _)
                (mul_nonneg zero_le_one hc0)
          _ = max C 1 * (‖z‖)⁻¹ := by ring
      exact hmain
    · rw [hbounddef, Set.indicator_of_notMem hz]
      have hz0 : g z = 0 := by
        by_contra h
        exact hz (hR (subset_tsupport g h))
      simp [hz0]
  -- The pointwise limit (for *every* `z`, including `z = 0`).
  have h_lim : ∀ᵐ z ∂(volume : Measure (R3)),
      Tendsto (fun ε : ℝ => fcut (‖z‖ / ε) / ‖z‖ * g z) (𝓝[>] (0 : ℝ))
        (𝓝 ((‖z‖)⁻¹ * g z)) := by
    refine Filter.Eventually.of_forall (fun z => ?_)
    by_cases hz : z = 0
    · subst hz
      simp only [norm_zero, zero_div, fcut_zero, inv_zero]
      exact tendsto_const_nhds
    · have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have htend : Tendsto (fun ε : ℝ => ‖z‖ / ε) (𝓝[>] (0 : ℝ)) atTop := by
        have h2 := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hpos
        simpa [div_eq_mul_inv] using h2
      have hfcut : Tendsto fcut atTop (𝓝 (1 : ℝ)) :=
        tendsto_nhds_of_eventually_eq
          ((Filter.eventually_ge_atTop (2 : ℝ)).mono (fun t ht => fcut_of_two_le ht))
      have h1 : Tendsto (fun ε : ℝ => fcut (‖z‖ / ε)) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
        hfcut.comp htend
      have h2 := (h1.div_const ‖z‖).mul_const (g z)
      simpa [div_eq_mul_inv, one_mul] using h2
  exact tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (R3)))
    bound hF_meas h_bound hbound_int h_lim

end

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.BSSwirl.tendsto_integral_norm_sub_translate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Metric Filter Topology
open scoped Topology ENNReal NNReal

namespace Work.FTS.BSSwirl

noncomputable section

/-- **The translations of `ℝ³` tend to the identity in the compact-open topology.**  Equivalently:
for every compact `K` and every open `U ⊇ K`, the translate `z ↦ z + h` maps `K` into `U` for all
`h` close enough to `0` (take the thickening of `K` inside `U`, which exists by compactness). -/
theorem tendsto_continuousMap_addRight :
    Filter.Tendsto (fun h : R3 => (⟨fun z => z + h, continuous_id.add continuous_const⟩ : C(R3, R3)))
      (nhds 0) (nhds (⟨id, continuous_id⟩ : C(R3, R3))) := by
  rw [ContinuousMap.tendsto_nhds_compactOpen]
  intro K hK U hU hKU
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  filter_upwards [Metric.ball_mem_nhds (0 : R3) hε] with h hh x hx
  exact hεU (Metric.cthickening_mono (le_of_lt (by simpa [dist_eq_norm] using hh)) K
    (Metric.mem_cthickening_of_dist_le (x + h) x ‖h‖ K hx (by simp [dist_eq_norm])))

theorem tendsto_integral_norm_sub_translate {E : Type*} [NormedAddCommGroup E]
    (A : Work.FTS.BSSwirl.R3 → E) (hA : MeasureTheory.Integrable A MeasureTheory.volume) :
    Filter.Tendsto (fun h : Work.FTS.BSSwirl.R3 =>
      MeasureTheory.integral MeasureTheory.volume (fun z => ‖A (z + h) - A z‖))
      (nhds 0) (nhds 0) := by
  -- `A` as an element `F` of `L¹(ℝ³; E)`.
  have hmem : MemLp A (1 : ℝ≥0∞) volume := memLp_one_iff_integrable.mpr hA
  let F : Lp E (1 : ℝ≥0∞) volume := hmem.toLp A
  have hFcoe : (↑↑F : R3 → E) =ᵐ[volume] A := hmem.coeFn_toLp
  -- Continuity of the measure-preserving action on `L¹` at `(F, id)`, combined with the
  -- compact-open continuity of the translations.
  have hcont : Tendsto (fun h : R3 =>
      Lp.compMeasurePreserving (fun z => z + h) (measurePreserving_add_right volume h) F)
      (nhds 0) (nhds F) := by
    have h := Filter.Tendsto.compMeasurePreservingLp (μ := volume) (ν := volume)
      (f := fun _ : R3 => F) (f₀ := F)
      (g := fun h : R3 => (⟨fun z => z + h, continuous_id.add continuous_const⟩ : C(R3, R3)))
      (g₀ := (⟨id, continuous_id⟩ : C(R3, R3))) tendsto_const_nhds tendsto_continuousMap_addRight
      (fun h => measurePreserving_add_right volume h) (MeasurePreserving.id volume) (by norm_num)
    simpa using h
  -- Therefore the `L¹`-distance of the translate from `F` tends to `0`.
  have hnorm : Tendsto (fun h : R3 => ‖Lp.compMeasurePreserving (fun z => z + h)
      (measurePreserving_add_right volume h) F - F‖) (nhds 0) (nhds 0) := by
    have h2 : Tendsto (fun h : R3 => Lp.compMeasurePreserving (fun z => z + h)
        (measurePreserving_add_right volume h) F - F) (nhds 0) (nhds 0) := by
      have h3 := hcont.sub (tendsto_const_nhds (x := F))
      simpa using h3
    simpa using h2.norm
  -- That `L¹`-distance is precisely the integral appearing in the statement.
  have key : ∀ h : R3, ‖Lp.compMeasurePreserving (fun z => z + h)
      (measurePreserving_add_right volume h) F - F‖ = ∫ z, ‖A (z + h) - A z‖ := by
    intro h
    have hX : (↑↑(Lp.compMeasurePreserving (fun z => z + h) (measurePreserving_add_right volume h) F)
        : R3 → E) =ᵐ[volume] (fun z => A (z + h)) := by
      have h2 := Lp.coeFn_compMeasurePreserving F (measurePreserving_add_right volume h)
      have h3 := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hFcoe
      filter_upwards [h2, h3] with z Hz2 Hz3
      rw [Hz2, Hz3]
      rfl
    rw [Lp.norm_def]
    have hae : (↑↑(Lp.compMeasurePreserving (fun z => z + h)
          (measurePreserving_add_right volume h) F - F) : R3 → E)
        =ᵐ[volume] (fun z => A (z + h) - A z) :=
      (Lp.coeFn_sub (Lp.compMeasurePreserving (fun z => z + h)
        (measurePreserving_add_right volume h) F) F).trans (hX.sub hFcoe)
    have hint : Integrable (fun z => A (z + h) - A z) volume := (hA.comp_add_right h).sub hA
    rw [eLpNorm_congr_ae hae, eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hint]
    exact ENNReal.toReal_ofReal (integral_nonneg fun z => norm_nonneg _)
  exact (tendsto_congr' (Eventually.of_forall key)).mp hnorm

end

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.ClassC.NormPieces.prodIntegrableNonneg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.ClassC.NormPieces

theorem prodIntegrableNonneg {f : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hslice : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ : ℝ => f z θ) Work.Spaces.Iθ)
    (hnn : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ f z θ)
    (hint : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, f z θ)
      Work.Spaces.Iz) :
    MeasureTheory.Integrable (Function.uncurry f)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∫ p, Function.uncurry f p
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, f z θ := by
  classical
  set S : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) with hSdef
  have hS_open : IsOpen S := isOpen_Ioi.prod isOpen_Ioo
  have hS_meas : MeasurableSet S := hS_open.measurableSet
  -- `S` is contained in `Iz ×ˢ Iθ`
  have hS_sub : S ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
    rintro ⟨z, θ⟩ hz
    simp only [Set.mem_prod, Work.Spaces.Iz, Work.Spaces.Iθ, Set.mem_Ici, Set.mem_Icc,
      Set.mem_Ioi, Set.mem_Ioo, hSdef] at hz ⊢
    exact ⟨le_of_lt hz.1, le_of_lt hz.2.1, le_of_lt hz.2.2⟩
  -- the complement of `S` inside `Iz ×ˢ Iθ` is a null set
  have hdiff_null : (Measure.prod volume volume)
      ((Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) \ S) = 0 := by
    have hA : (Measure.prod volume volume)
        (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
      rw [Measure.prod_prod]; simp
    have hB : (Measure.prod volume volume)
        ((Set.univ : Set ℝ) ×ˢ ({0, Real.pi / 2} : Set ℝ)) = 0 := by
      rw [Measure.prod_prod]
      have h2 : volume ({0, Real.pi / 2} : Set ℝ) = 0 :=
        Set.Finite.measure_zero ((Set.finite_singleton (Real.pi / 2)).insert 0) volume
      rw [h2, mul_zero]
    refine measure_mono_null (fun p hp => ?_) (measure_union_null hA hB)
    obtain ⟨z, θ⟩ := p
    rw [Set.mem_sdiff] at hp
    obtain ⟨hpin, hpnot⟩ := hp
    have hzin := hpin.1
    have hθin := hpin.2
    simp only [Work.Spaces.Iz, Work.Spaces.Iθ, Set.mem_Ici, Set.mem_Icc] at hzin hθin
    rw [hSdef] at hpnot
    simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hpnot
    simp only [Set.mem_union, Set.mem_prod, Set.mem_singleton_iff, Set.mem_insert_iff,
      Set.mem_univ, true_and, and_true]
    have hz0 : 0 ≤ z := hzin
    have hθ0 : 0 ≤ θ := hθin.1
    have hθpi : θ ≤ Real.pi / 2 := hθin.2
    have hnot : ¬ (0 < z ∧ 0 < θ ∧ θ < Real.pi / 2) := hpnot
    rcases lt_or_ge 0 z with hz | hz
    · right
      have h2 : ¬ (0 < θ ∧ θ < Real.pi / 2) := fun hc => hnot ⟨hz, hc.1, hc.2⟩
      rcases eq_or_lt_of_le hθ0 with h | h
      · left; exact h.symm
      · right
        exact le_antisymm hθpi (not_lt.mp (fun hlt => h2 ⟨h, hlt⟩))
    · left; exact le_antisymm hz hz0
  have hae_set : Work.Spaces.Iz ×ˢ Work.Spaces.Iθ
      =ᵐ[Measure.prod volume volume] S := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨hdiff_null, ?_⟩
    rw [show S \ (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) = ∅ from by
      rw [Set.sdiff_eq_empty]; exact hS_sub]
    exact measure_empty
  -- rewrite the product measure as the restriction to `S`
  have hμν : (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)
      = (Measure.prod volume volume).restrict S := by
    rw [Measure.prod_restrict Work.Spaces.Iz Work.Spaces.Iθ]
    exact Measure.restrict_congr_set hae_set
  have hsm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [hμν]
    exact hcont.aestronglyMeasurable hS_meas
  -- almost every `z ∈ Iz` is positive
  have hIzeq : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · refine measure_mono_null (fun z hz => ?_) (measure_singleton 0)
      simp only [Set.mem_sdiff, Work.Spaces.Iz, Set.mem_Ici, Set.mem_Ioi,
        Set.mem_singleton_iff] at hz ⊢
      exact le_antisymm (not_lt.mp hz.2) hz.1
    · rw [show Set.Ioi (0 : ℝ) \ Work.Spaces.Iz = ∅ from by
        rw [Set.sdiff_eq_empty]
        intro z hz
        simpa [Work.Spaces.Iz] using le_of_lt hz]
      exact measure_empty
  have hpos : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 < z := by
    rw [Measure.restrict_congr_set hIzeq]
    exact ae_restrict_mem (μ := volume) (s := Set.Ioi (0 : ℝ)) isOpen_Ioi.measurableSet
  have hslice_ae : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      Integrable (fun θ : ℝ => f z θ) (volume.restrict Work.Spaces.Iθ) :=
    hpos.mono (fun z hz => hslice z hz)
  -- the norm-integral coincides a.e. with the given iterated integral
  have hae_norm : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, f z θ)
      =ᵐ[volume.restrict Work.Spaces.Iz]
      (fun z : ℝ => ∫ θ, ‖f z θ‖ ∂(volume.restrict Work.Spaces.Iθ)) := by
    filter_upwards [hpos] with z hz
    have h1 : (fun θ : ℝ => ‖f z θ‖)
        =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ : ℝ => f z θ) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact Real.norm_of_nonneg (hnn z θ hz hθ)
    exact (integral_congr_ae h1).symm
  have hint_norm : Integrable
      (fun z : ℝ => ∫ θ, ‖f z θ‖ ∂(volume.restrict Work.Spaces.Iθ))
      (volume.restrict Work.Spaces.Iz) :=
    hint.congr hae_norm
  have hfint : Integrable (Function.uncurry f)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (integrable_prod_iff hsm).mpr ⟨hslice_ae, hint_norm⟩
  refine ⟨hfint, ?_⟩
  exact (MeasureTheory.integral_integral (f := fun z θ => f z θ) hfint).symm

end Work.FTS.ClassC.NormPieces
end
-- ===== merged: Submission.Work.FTS.ClassC.eFam_sin_two_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open Work.FTS.PhiStar.Gegenbauer

/-- On `[0,1]` both the Gegenbauer polynomial `gC n` and its derivative are bounded by `6 ^ n`.
Proved by two-step induction from the recurrence `(n+2) C_{n+2} = (2n+5) x C_{n+1} - (n+3) C_n`
and its derivative; the numerical estimates are `13n + 33 ≤ 36 (n+2)` for the values and
`25n + 63 ≤ 36 (n+2)` for the derivatives. -/
lemma gC_bound_pair : ∀ n : ℕ,
    (∀ x ∈ Set.Icc (0 : ℝ) 1, |gC n x| ≤ (6 : ℝ) ^ n) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (gC n) x| ≤ (6 : ℝ) ^ n) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro x _
        rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
        norm_num
      · intro x _
        rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
        simp
  | one =>
      have hderiv : deriv (fun x : ℝ => 3 * x) = fun _ : ℝ => 3 := by
        funext x
        rw [deriv_const_mul_field]
        simp
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [show gC 1 = (fun x : ℝ => 3 * x) from rfl]
        rw [abs_of_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ 3 * x)]
        nlinarith [hx.2]
      · intro x _
        rw [show gC 1 = (fun x : ℝ => 3 * x) from rfl, hderiv]
        norm_num
  | more n ih ih' =>
      have hcoef : (0 : ℝ) ≤ 2 * (n : ℝ) + 5 := by positivity
      have hcoef3 : (0 : ℝ) ≤ (n : ℝ) + 3 := by positivity
      have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hpowpos : (0 : ℝ) < (6 : ℝ) ^ n := by positivity
      have hp1 : (6 : ℝ) ^ (n + 1) = 6 * (6 : ℝ) ^ n := by rw [pow_succ]; ring
      have hp2 : (6 : ℝ) ^ (n + 2) = 36 * (6 : ℝ) ^ n := by
        rw [pow_succ, pow_succ]; ring
      have hncast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      constructor
      · intro x hx
        rcases hx with ⟨hx0, hx1⟩
        have hb1 : |gC (n + 1) x| ≤ (6 : ℝ) ^ (n + 1) := ih'.1 x ⟨hx0, hx1⟩
        have hb0 : |gC n x| ≤ (6 : ℝ) ^ n := ih.1 x ⟨hx0, hx1⟩
        have heq : gC (n + 2) x
            = ((2 * (n : ℝ) + 5) * x * gC (n + 1) x - ((n : ℝ) + 3) * gC n x)
                / ((n : ℝ) + 2) := by
          rw [eq_div_iff (ne_of_gt hden), mul_comm]
          exact gC_rec n x
        have hnum : |(2 * (n : ℝ) + 5) * x * gC (n + 1) x - ((n : ℝ) + 3) * gC n x|
            ≤ (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + ((n : ℝ) + 3) * (6 : ℝ) ^ n := by
          have ha : |(2 * (n : ℝ) + 5) * x * gC (n + 1) x|
              = (2 * (n : ℝ) + 5) * (x * |gC (n + 1) x|) := by
            simp only [abs_mul, abs_of_nonneg hx0, abs_of_nonneg hcoef]
            ring
          have hb : |((n : ℝ) + 3) * gC n x| = ((n : ℝ) + 3) * |gC n x| := by
            rw [abs_mul, abs_of_nonneg hcoef3]
          have h1 : x * |gC (n + 1) x| ≤ (6 : ℝ) ^ (n + 1) := by
            have h := mul_le_mul hx1 hb1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
            simpa using h
          have h2 : (2 * (n : ℝ) + 5) * (x * |gC (n + 1) x|)
              ≤ (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) := mul_le_mul_of_nonneg_left h1 hcoef
          have h3 : ((n : ℝ) + 3) * |gC n x| ≤ ((n : ℝ) + 3) * (6 : ℝ) ^ n :=
            mul_le_mul_of_nonneg_left hb0 hcoef3
          calc |(2 * (n : ℝ) + 5) * x * gC (n + 1) x - ((n : ℝ) + 3) * gC n x|
              ≤ |(2 * (n : ℝ) + 5) * x * gC (n + 1) x| + |((n : ℝ) + 3) * gC n x| :=
                abs_sub _ _
            _ = (2 * (n : ℝ) + 5) * (x * |gC (n + 1) x|) + ((n : ℝ) + 3) * |gC n x| := by
                rw [ha, hb]
            _ ≤ (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + ((n : ℝ) + 3) * (6 : ℝ) ^ n := by
                linarith [h2, h3]
        have hfin : (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + ((n : ℝ) + 3) * (6 : ℝ) ^ n
            ≤ (6 : ℝ) ^ (n + 2) * ((n : ℝ) + 2) := by
          rw [hp1, hp2]
          nlinarith [hpowpos, hncast]
        rw [heq, abs_div, abs_of_pos hden]
        have h2 : |(2 * (n : ℝ) + 5) * x * gC (n + 1) x - ((n : ℝ) + 3) * gC n x|
              / ((n : ℝ) + 2)
            ≤ ((2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + ((n : ℝ) + 3) * (6 : ℝ) ^ n)
              / ((n : ℝ) + 2) := div_le_div_of_nonneg_right hnum (le_of_lt hden)
        have h3 : ((2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + ((n : ℝ) + 3) * (6 : ℝ) ^ n)
              / ((n : ℝ) + 2) ≤ (6 : ℝ) ^ (n + 2) := by
          rw [div_le_iff₀ hden]
          exact hfin
        linarith [h2, h3]
      · intro x hx
        rcases hx with ⟨hx0, hx1⟩
        have hb1 : |gC (n + 1) x| ≤ (6 : ℝ) ^ (n + 1) := ih'.1 x ⟨hx0, hx1⟩
        have hd1 : |deriv (gC (n + 1)) x| ≤ (6 : ℝ) ^ (n + 1) := ih'.2 x ⟨hx0, hx1⟩
        have hd0 : |deriv (gC n) x| ≤ (6 : ℝ) ^ n := ih.2 x ⟨hx0, hx1⟩
        have heq : deriv (gC (n + 2)) x
            = ((2 * (n : ℝ) + 5) * gC (n + 1) x + (2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x
                - ((n : ℝ) + 3) * deriv (gC n) x) / ((n : ℝ) + 2) := by
          rw [eq_div_iff (ne_of_gt hden), mul_comm]
          exact gC_rec_deriv n x
        have hta : |(2 * (n : ℝ) + 5) * gC (n + 1) x|
            = (2 * (n : ℝ) + 5) * |gC (n + 1) x| := by
          rw [abs_mul, abs_of_nonneg hcoef]
        have htb : |(2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x|
            = (2 * (n : ℝ) + 5) * (x * |deriv (gC (n + 1)) x|) := by
          simp only [abs_mul, abs_of_nonneg hx0, abs_of_nonneg hcoef]
          ring
        have htc : |((n : ℝ) + 3) * deriv (gC n) x| = ((n : ℝ) + 3) * |deriv (gC n) x| := by
          rw [abs_mul, abs_of_nonneg hcoef3]
        have h1 : x * |deriv (gC (n + 1)) x| ≤ (6 : ℝ) ^ (n + 1) := by
          have h := mul_le_mul hx1 hd1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
          simpa using h
        have h2 : (2 * (n : ℝ) + 5) * |gC (n + 1) x| ≤ (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) :=
          mul_le_mul_of_nonneg_left hb1 hcoef
        have h3 : (2 * (n : ℝ) + 5) * (x * |deriv (gC (n + 1)) x|)
            ≤ (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) := mul_le_mul_of_nonneg_left h1 hcoef
        have h4 : ((n : ℝ) + 3) * |deriv (gC n) x| ≤ ((n : ℝ) + 3) * (6 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left hd0 hcoef3
        have hnum : |(2 * (n : ℝ) + 5) * gC (n + 1) x + (2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x
              - ((n : ℝ) + 3) * deriv (gC n) x|
            ≤ (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1)
              + ((n : ℝ) + 3) * (6 : ℝ) ^ n := by
          calc |(2 * (n : ℝ) + 5) * gC (n + 1) x + (2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x
                - ((n : ℝ) + 3) * deriv (gC n) x|
              ≤ |(2 * (n : ℝ) + 5) * gC (n + 1) x + (2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x|
                + |((n : ℝ) + 3) * deriv (gC n) x| := abs_sub _ _
            _ ≤ (|(2 * (n : ℝ) + 5) * gC (n + 1) x| + |(2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x|)
                + |((n : ℝ) + 3) * deriv (gC n) x| := by
                have hAB := abs_add_le ((2 * (n : ℝ) + 5) * gC (n + 1) x)
                  ((2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x)
                linarith [hAB]
            _ = (2 * (n : ℝ) + 5) * |gC (n + 1) x| + (2 * (n : ℝ) + 5) * (x * |deriv (gC (n + 1)) x|)
                + ((n : ℝ) + 3) * |deriv (gC n) x| := by
                rw [hta, htb, htc]
            _ ≤ (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1)
                + ((n : ℝ) + 3) * (6 : ℝ) ^ n := by
                linarith [h2, h3, h4]
        have hfin : (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1)
              + ((n : ℝ) + 3) * (6 : ℝ) ^ n ≤ (6 : ℝ) ^ (n + 2) * ((n : ℝ) + 2) := by
          rw [hp1, hp2]
          nlinarith [hpowpos, hncast]
        rw [heq, abs_div, abs_of_pos hden]
        have h2' : |(2 * (n : ℝ) + 5) * gC (n + 1) x + (2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x
              - ((n : ℝ) + 3) * deriv (gC n) x| / ((n : ℝ) + 2)
            ≤ ((2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1)
              + ((n : ℝ) + 3) * (6 : ℝ) ^ n) / ((n : ℝ) + 2) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hden)
        have h3' : ((2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1)
              + ((n : ℝ) + 3) * (6 : ℝ) ^ n) / ((n : ℝ) + 2) ≤ (6 : ℝ) ^ (n + 2) := by
          rw [div_le_iff₀ hden]
          exact hfin
        linarith [h2', h3']

/-- For an odd index `2m+1`, the bound `|gC (2m+1) x| ≤ 6^(2m+1) · x` on `[0,1]`, obtained from
`gC (2m+1) 0 = 0` and the derivative bound of `gC_bound_pair` by the mean value theorem. -/
lemma gC_odd_le_self (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |gC (2 * m + 1) x| ≤ (6 : ℝ) ^ (2 * m + 1) * x := by
  rcases lt_or_eq_of_le hx.1 with hpos | hzero
  · have hxne : x ≠ 0 := ne_of_gt hpos
    have hcont : ContinuousOn (gC (2 * m + 1)) (Set.Icc (0 : ℝ) x) :=
      (contDiff_gC (2 * m + 1)).continuous.continuousOn
    have hdiff : DifferentiableOn ℝ (gC (2 * m + 1)) (Set.Ioo (0 : ℝ) x) :=
      ((contDiff_gC (2 * m + 1)).differentiable (by norm_num)).differentiableOn
    obtain ⟨c, hc, hceq⟩ := exists_deriv_eq_slope (gC (2 * m + 1)) hpos hcont hdiff
    have hcI : c ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_of_lt hc.1, le_trans (le_of_lt hc.2) hx.2⟩
    have hb : |deriv (gC (2 * m + 1)) c| ≤ (6 : ℝ) ^ (2 * m + 1) :=
      (gC_bound_pair (2 * m + 1)).2 c hcI
    have hmul : deriv (gC (2 * m + 1)) c * x = gC (2 * m + 1) x := by
      rw [hceq]
      simp only [sub_zero, gC_odd_zero m]
      exact div_mul_cancel₀ _ hxne
    calc |gC (2 * m + 1) x| = |deriv (gC (2 * m + 1)) c * x| := by rw [hmul]
      _ = |deriv (gC (2 * m + 1)) c| * |x| := abs_mul _ _
      _ = |deriv (gC (2 * m + 1)) c| * x := by rw [abs_of_nonneg hx.1]
      _ ≤ (6 : ℝ) ^ (2 * m + 1) * x := mul_le_mul_of_nonneg_right hb hx.1
  · rw [← hzero, gC_odd_zero m, abs_zero]
    simp

theorem eFam_sin_two_bound (m : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
    |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ A * Real.sin (2 * θ) := by
  refine ⟨(6 : ℝ) ^ (2 * m + 1) / 2, by positivity, ?_⟩
  intro θ hθ
  rcases hθ with ⟨hθ0, hθ1⟩
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsin0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ0, by linarith [hpi]⟩
  have hcos0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hpi], hθ1⟩
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hb := gC_odd_le_self m (show Real.sin θ ∈ Set.Icc (0 : ℝ) 1 from ⟨hsin0, hsin1⟩)
  have hefam : eFam m θ = Real.cos θ * gC (2 * m + 1) (Real.sin θ) := rfl
  calc |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      = |Real.cos θ| * |gC (2 * m + 1) (Real.sin θ)| := by rw [hefam, abs_mul]
    _ = Real.cos θ * |gC (2 * m + 1) (Real.sin θ)| := by rw [abs_of_nonneg hcos0]
    _ ≤ Real.cos θ * ((6 : ℝ) ^ (2 * m + 1) * Real.sin θ) := mul_le_mul_of_nonneg_left hb hcos0
    _ = ((6 : ℝ) ^ (2 * m + 1) / 2) * Real.sin (2 * θ) := by
        rw [Real.sin_two_mul]; ring

end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassC.radGreen_far_limits =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

open Work.FTS.EllExist (rgK rgP rgQ rgA rgB rgG1 rgG2)

/-- `radGreen` written with the two indicial branches `rgG1`, `rgG2` of
`Work.FTS.EllExist.RadGreenDefs`. -/
theorem radGreen_eq_rgG (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m c z = rgK α m * (rgG1 α m c z + rgG2 α m c z) := by
  rw [Work.FTS.EllExist.radGreen_eq]
  simp only [Work.FTS.EllExist.rgG1, Work.FTS.EllExist.rgG2]

/-- `C / z → 0` at `+∞`. -/
private theorem tendsto_const_div_atTop (C : ℝ) :
    Tendsto (fun z : ℝ => C / z) atTop (nhds 0) :=
  Filter.Tendsto.div_atTop (tendsto_const_nhds : Tendsto (fun _ : ℝ => C) atTop (nhds C))
    (tendsto_id : Tendsto (fun z : ℝ => z) atTop atTop)

/-- `|x - y| ≤ |x| + |y|`. -/
private theorem abs_sub_le_abs_add' (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self x, neg_abs_le x, le_abs_self y, neg_abs_le y]

theorem radGreen_far_limits {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) {c : ℝ → ℝ}
    (hcont : ContinuousOn c (Set.Ioi 0))
    (hdec : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t)
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1))
    (hderiv : ∀ z : ℝ, 0 < z → HasDerivAt (Work.FTS.PhiStar.Radial.radGreen α m c)
      (deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) z) :
    Filter.Tendsto (fun z => z * (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2)
        Filter.atTop (nhds 0)
      ∧ Filter.Tendsto (fun z => z * (Work.FTS.PhiStar.Radial.radGreen α m c z)
          * (z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z)) Filter.atTop (nhds 0) := by
  obtain ⟨CA, hCA0, hAb⟩ := rgA_growth hα hα4 m hcont hdec h0
  obtain ⟨C2, hC20, hBb⟩ := rgB_far_bound hα hα4 m hdec hinf
  have hKpos : 0 < rgK α m := Work.FTS.EllExist.rgK_pos hα m
  have hK0 : 0 ≤ rgK α m := hKpos.le
  have hq0 : 0 ≤ rgQ α m := (Work.FTS.EllExist.rgQ_pos hα m).le
  have hp0 : 0 ≤ rgP α m := Work.FTS.EllExist.rgP_nonneg hα m
  have hCAD : 0 ≤ CA + C2 := by linarith
  -- ## (i) the two branches, in the normalised form
  have hG1le : ∀ z : ℝ, 1 ≤ z → |rgG1 α m c z| ≤ CA / z := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    have hA := hAb z hz1
    have hcomb : z ^ (-(rgQ α m)) * z ^ (rgQ α m - 1) = z ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hz0]
      congr 1
      ring
    simp only [Work.FTS.EllExist.rgG1]
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz0 _)]
    calc z ^ (-(rgQ α m)) * |rgA α m c z|
        ≤ z ^ (-(rgQ α m)) * (CA * z ^ (rgQ α m - 1)) :=
          mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hz0.le _)
      _ = CA * (z ^ (-(rgQ α m)) * z ^ (rgQ α m - 1)) := by ring
      _ = CA / z := by rw [hcomb, Real.rpow_neg_one, div_eq_mul_inv]
  have hG2le : ∀ z : ℝ, 1 ≤ z → |rgG2 α m c z| ≤ C2 / z := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    have hB := hBb z hz1
    simp only [Work.FTS.EllExist.rgG2]
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz0 _)]
    exact hB
  have hzG1le : ∀ z : ℝ, 1 ≤ z → z * |rgG1 α m c z| ≤ CA := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    calc z * |rgG1 α m c z| ≤ z * (CA / z) := mul_le_mul_of_nonneg_left (hG1le z hz1) hz0.le
      _ = CA := by field_simp
  have hzG2le : ∀ z : ℝ, 1 ≤ z → z * |rgG2 α m c z| ≤ C2 := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    calc z * |rgG2 α m c z| ≤ z * (C2 / z) := mul_le_mul_of_nonneg_left (hG2le z hz1) hz0.le
      _ = C2 := by field_simp
  -- ## (ii) the pointwise bounds for `radGreen`, `z·radGreen` and `z·∂_z radGreen`
  have hBnd_rad : ∀ z : ℝ, 1 ≤ z →
      |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ (rgK α m * (CA + C2)) / z := by
    intro z hz1
    rw [radGreen_eq_rgG α m c z, abs_mul, abs_of_nonneg hK0]
    calc rgK α m * |rgG1 α m c z + rgG2 α m c z|
        ≤ rgK α m * (|rgG1 α m c z| + |rgG2 α m c z|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hK0
      _ ≤ rgK α m * (CA / z + C2 / z) :=
          mul_le_mul_of_nonneg_left (add_le_add (hG1le z hz1) (hG2le z hz1)) hK0
      _ = (rgK α m * (CA + C2)) / z := by ring
  have hBnd_zrad : ∀ z : ℝ, 1 ≤ z →
      |z * Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ rgK α m * (CA + C2) := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    rw [radGreen_eq_rgG α m c z]
    rw [show z * (rgK α m * (rgG1 α m c z + rgG2 α m c z))
        = rgK α m * (z * rgG1 α m c z + z * rgG2 α m c z) from by ring,
      abs_mul, abs_of_nonneg hK0]
    have e1 : |z * rgG1 α m c z| = z * |rgG1 α m c z| := by rw [abs_mul, abs_of_pos hz0]
    have e2 : |z * rgG2 α m c z| = z * |rgG2 α m c z| := by rw [abs_mul, abs_of_pos hz0]
    calc rgK α m * |z * rgG1 α m c z + z * rgG2 α m c z|
        ≤ rgK α m * (|z * rgG1 α m c z| + |z * rgG2 α m c z|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hK0
      _ = rgK α m * (z * |rgG1 α m c z| + z * |rgG2 α m c z|) := by rw [e1, e2]
      _ ≤ rgK α m * (CA + C2) :=
          mul_le_mul_of_nonneg_left (add_le_add (hzG1le z hz1) (hzG2le z hz1)) hK0
  have hBnd_zd : ∀ z : ℝ, 1 ≤ z →
      |z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z|
        ≤ (rgK α m * (rgP α m * C2 + rgQ α m * CA)) / z := by
    intro z hz1
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
    have hd := radGreen_deriv1_form hα m hcont h0 hinf z hz0
    rw [hd, abs_mul, abs_of_nonneg hK0]
    have e1 : |rgP α m * rgG2 α m c z| = rgP α m * |rgG2 α m c z| := by
      rw [abs_mul, abs_of_nonneg hp0]
    have e2 : |rgQ α m * rgG1 α m c z| = rgQ α m * |rgG1 α m c z| := by
      rw [abs_mul, abs_of_nonneg hq0]
    calc rgK α m * |rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z|
        ≤ rgK α m * (|rgP α m * rgG2 α m c z| + |rgQ α m * rgG1 α m c z|) :=
          mul_le_mul_of_nonneg_left (abs_sub_le_abs_add' _ _) hK0
      _ = rgK α m * (rgP α m * |rgG2 α m c z| + rgQ α m * |rgG1 α m c z|) := by rw [e1, e2]
      _ ≤ rgK α m * (rgP α m * (C2 / z) + rgQ α m * (CA / z)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left (hG2le z hz1) hp0)
              (mul_le_mul_of_nonneg_left (hG1le z hz1) hq0)) hK0
      _ = (rgK α m * (rgP α m * C2 + rgQ α m * CA)) / z := by ring
  -- ## (iii) the two limits
  have hBnn : 0 ≤ rgK α m * (CA + C2) := mul_nonneg hK0 hCAD
  refine ⟨?_, ?_⟩
  · refine squeeze_zero_norm'
      (a := fun z : ℝ => ((rgK α m * (CA + C2)) * (rgK α m * (CA + C2))) / z) ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz1
      calc ‖z * (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2‖
          = |z * Work.FTS.PhiStar.Radial.radGreen α m c z|
              * |Work.FTS.PhiStar.Radial.radGreen α m c z| := by
            rw [Real.norm_eq_abs,
              show z * (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2
                = (z * Work.FTS.PhiStar.Radial.radGreen α m c z)
                    * Work.FTS.PhiStar.Radial.radGreen α m c z from by ring,
              abs_mul]
        _ ≤ (rgK α m * (CA + C2)) * ((rgK α m * (CA + C2)) / z) :=
            mul_le_mul (hBnd_zrad z hz1) (hBnd_rad z hz1) (abs_nonneg _) hBnn
        _ = ((rgK α m * (CA + C2)) * (rgK α m * (CA + C2))) / z := by ring
    · simpa using tendsto_const_div_atTop ((rgK α m * (CA + C2)) * (rgK α m * (CA + C2)))
  · refine squeeze_zero_norm'
      (a := fun z : ℝ =>
        ((rgK α m * (CA + C2)) * (rgK α m * (rgP α m * C2 + rgQ α m * CA))) / z) ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz1
      calc ‖z * Work.FTS.PhiStar.Radial.radGreen α m c z
              * (z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z)‖
          = |z * Work.FTS.PhiStar.Radial.radGreen α m c z|
              * |z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ (rgK α m * (CA + C2))
              * ((rgK α m * (rgP α m * C2 + rgQ α m * CA)) / z) :=
            mul_le_mul (hBnd_zrad z hz1) (hBnd_zd z hz1) (abs_nonneg _) hBnn
        _ = ((rgK α m * (CA + C2)) * (rgK α m * (rgP α m * C2 + rgQ α m * CA))) / z := by
            ring
    · simpa using tendsto_const_div_atTop
        ((rgK α m * (CA + C2)) * (rgK α m * (rgP α m * C2 + rgQ α m * CA)))

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.radGreen_near_limits =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.EllExist

/-! ### helpers -/

/-- A function bounded by `C · z ^ d` (`d > 0`) on `(0,1)` tends to `0` at `0` within `(0,∞)`. -/
private lemma tendsto_zero_of_bound {F : ℝ → ℝ} {C d : ℝ} (hd : 0 < d) (hC : 0 ≤ C)
    (hb : ∀ z ∈ Set.Ioo (0 : ℝ) 1, ‖F z‖ ≤ C * z ^ d) :
    Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmaj : Filter.Tendsto (fun z : ℝ => C * z ^ d) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have ht := (Real.continuousAt_rpow_const 0 d (Or.inr hd.le)).tendsto
    rw [Real.zero_rpow (ne_of_gt hd)] at ht
    have ht2 := ht.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
    have h3 := ht2.const_mul C
    simpa using h3
  refine squeeze_zero' (Filter.Eventually.of_forall fun z => norm_nonneg (F z)) ?_ hmaj
  have hmemb : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin 0 (Set.Ioi 0) := by
    rw [show Set.Ioo (0 : ℝ) 1 = Set.Ioi 0 ∩ Set.Iio 1 from by
      ext z
      simp only [Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio, Set.mem_inter_iff]]
    exact inter_mem_nhdsWithin _ (Iio_mem_nhds one_pos)
  exact Filter.mem_of_superset hmemb fun z hz => hb z hz

/-- The tail kernel `rgF2 α m c t = c t · t^{-p-1}` is integrable on all of `(0,∞)` as soon as it
is integrable on `(0,1)` and on `(1,∞)`. -/
private lemma rgF2_integrableOn_Ioi {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (h0' : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioi 0) := by
  have hnear : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioo 0 1) := by
    rw [show rgF2 α m c = fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1) from rfl]
    exact h0'
  have hfar : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioi 1) := by
    rw [show rgF2 α m c = fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1) from rfl]
    exact hinf
  have hsing : MeasureTheory.IntegrableOn (rgF2 α m c) ({1} : Set ℝ) :=
    MeasureTheory.integrableOn_singleton (f := rgF2 α m c) (x := 1)
      (by finiteness) (by rw [measure_singleton]; exact ENNReal.zero_lt_top)
  have hIoc : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioc 0 1) := by
    rw [← Set.Ioo_union_right (show (0 : ℝ) < 1 by norm_num)]
    exact hnear.union hsing
  have h' : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioc 0 1 ∪ Set.Ioi 1) :=
    hIoc.union hfar
  rwa [show Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 from by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, _⟩ | h2)
      · exact h1
      · linarith
    · intro hx
      by_cases h' : x ≤ 1
      · exact Or.inl ⟨hx, h'⟩
      · exact Or.inr (lt_of_not_ge h')] at h'

/-- `(z^d)^2 / z^3 = z^{2d-3}` for `z > 0`. -/
private lemma rpow_sq_div_cube {z d : ℝ} (hz : 0 < z) : (z ^ d) ^ 2 / z ^ 3 = z ^ (2 * d - 3) := by
  rw [← Real.rpow_mul_natCast hz.le d 2, ← Real.rpow_natCast z 3, ← Real.rpow_sub hz]
  congr 1
  push_cast
  ring

/-- `z^d · z^d / z^3 = z^{2d-3}` for `z > 0`. -/
private lemma rpow_mul_self_div_cube {z d : ℝ} (hz : 0 < z) :
    z ^ d * z ^ d / z ^ 3 = z ^ (2 * d - 3) := by
  rw [← Real.rpow_add hz, ← Real.rpow_natCast z 3, ← Real.rpow_sub hz]
  congr 1
  push_cast
  ring

/-! ### the theorem -/

theorem radGreen_near_limits {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ}
    (hcont : ContinuousOn c (Set.Ioi 0))
    (hvy : ∃ K p : ℝ, 0 < K ∧ 3 / 2 < p ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → |c t| ≤ K * t ^ p)
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1))
    (hderiv : ∀ z : ℝ, 0 < z → HasDerivAt (Work.FTS.PhiStar.Radial.radGreen α m c)
      (deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) z) :
    Filter.Tendsto (fun z => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 / z ^ 3)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
      ∧ Filter.Tendsto (fun z => deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
          * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨Kc, pc, hKc, hpc32, hvy⟩ := hvy
  have hqpos : 0 < rgQ α m := rgQ_pos hα m
  have hKpos : 0 < rgK α m := rgK_pos hα m
  have hppos : 0 < rgP α m := rgP_pos hα hm
  have hpnn : 0 ≤ rgP α m := hppos.le
  -- the three constants of the estimate
  set Cf : ℝ := ∫ t in Set.Ioi 0, ‖rgF2 α m c t‖ with hCfdef
  set c1 : ℝ := Kc / (pc + rgQ α m) with hc1def
  set d : ℝ := min pc (rgP α m) with hddef
  set A : ℝ := rgK α m * (rgP α m * Cf + rgQ α m * c1) with hAdef
  set B : ℝ := rgK α m * (c1 + Cf) with hBdef
  have hpc : 0 < pc := by linarith
  have hc1nn : 0 ≤ c1 := by
    rw [hc1def]
    exact div_nonneg hKc.le (add_nonneg hpc.le hqpos.le)
  have hCfnn : 0 ≤ Cf := by
    rw [hCfdef]
    exact integral_nonneg fun t => norm_nonneg _
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg hKpos.le (add_nonneg (mul_nonneg hpnn hCfnn) (mul_nonneg hqpos.le hc1nn))
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg hKpos.le (add_nonneg hc1nn hCfnn)
  have hdpos : 0 < d := by rw [hddef]; exact lt_min hpc hppos
  have hd32 : (3 : ℝ) / 2 < d := by
    rw [hddef]
    exact lt_min hpc32 (by linarith [rgP_ge hα hα4 hm])
  have hdpc : d ≤ pc := by rw [hddef]; exact min_le_left _ _
  have hdp : d ≤ rgP α m := by rw [hddef]; exact min_le_right _ _
  -- integrability of the tail kernel on all of `(0,∞)`
  have h2 : MeasureTheory.IntegrableOn (rgF2 α m c) (Set.Ioi 0) :=
    rgF2_integrableOn_Ioi h0' hinf
  -- the two branch bounds
  have hbd1 : ∀ z : ℝ, 0 < z → z ≤ 1 →
      |rgG1 α m c z| ≤ Kc * z ^ pc / (pc + rgQ α m) :=
    rgG1_near_bound hα hKc hpc hvy
  have hbd2 : ∀ z : ℝ, 0 < z →
      |rgG2 α m c z| ≤ (∫ t in Set.Ioi 0, ‖rgF2 α m c t‖) * z ^ (rgP α m) :=
    rgG2_near_bound h2
  have hG1 : ∀ z : ℝ, 0 < z → z ≤ 1 → |rgG1 α m c z| ≤ c1 * z ^ d := by
    intro z hz0 hz1
    have hpcδ : z ^ pc ≤ z ^ d := Real.rpow_le_rpow_of_exponent_ge hz0 hz1 hdpc
    calc |rgG1 α m c z| ≤ Kc * z ^ pc / (pc + rgQ α m) := hbd1 z hz0 hz1
      _ = c1 * z ^ pc := by rw [hc1def]; ring_nf
      _ ≤ c1 * z ^ d := mul_le_mul_of_nonneg_left hpcδ hc1nn
  have hG2 : ∀ z : ℝ, 0 < z → z ≤ 1 → |rgG2 α m c z| ≤ Cf * z ^ d := by
    intro z hz0 hz1
    have hpδ : z ^ (rgP α m) ≤ z ^ d := Real.rpow_le_rpow_of_exponent_ge hz0 hz1 hdp
    have h1 : |rgG2 α m c z| ≤ Cf * z ^ (rgP α m) := by
      have hp := hbd2 z hz0
      rwa [← hCfdef] at hp
    calc |rgG2 α m c z| ≤ Cf * z ^ (rgP α m) := h1
      _ ≤ Cf * z ^ d := mul_le_mul_of_nonneg_left hpδ hCfnn
  -- `radGreen` is `rgK (g₁ + g₂)` and hence `O(z^d)`
  have hgeq : ∀ z : ℝ, Work.FTS.PhiStar.Radial.radGreen α m c z
      = rgK α m * (rgG1 α m c z + rgG2 α m c z) := by
    intro z
    rw [radGreen_eq]
    simp only [rgG1, rgG2]
  have hG : ∀ z : ℝ, 0 < z → z ≤ 1 →
      ‖Work.FTS.PhiStar.Radial.radGreen α m c z‖ ≤ B * z ^ d := by
    intro z hz0 hz1
    have h1 := hG1 z hz0 hz1
    have h2' := hG2 z hz0 hz1
    rw [Real.norm_eq_abs, hgeq z, abs_mul, abs_of_pos hKpos]
    calc rgK α m * |rgG1 α m c z + rgG2 α m c z|
        ≤ rgK α m * (|rgG1 α m c z| + |rgG2 α m c z|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hKpos.le
      _ ≤ rgK α m * (c1 * z ^ d + Cf * z ^ d) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2') hKpos.le
      _ = B * z ^ d := by rw [hBdef]; ring
  -- and the combination `rgK (p g₂ - q g₁)` occurring in the derivative is `O(z^d)` too
  have hT : ∀ z : ℝ, 0 < z → z ≤ 1 →
      ‖rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z)‖ ≤ A * z ^ d := by
    intro z hz0 hz1
    have h1 := hG1 z hz0 hz1
    have h2' := hG2 z hz0 hz1
    have h2n : ‖rgG2 α m c z‖ ≤ Cf * z ^ d := by rw [Real.norm_eq_abs]; exact h2'
    have h1n : ‖rgG1 α m c z‖ ≤ c1 * z ^ d := by rw [Real.norm_eq_abs]; exact h1
    rw [norm_mul, Real.norm_of_nonneg hKpos.le]
    calc rgK α m * ‖rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z‖
        ≤ rgK α m * (rgP α m * (Cf * z ^ d) + rgQ α m * (c1 * z ^ d)) := by
          apply mul_le_mul_of_nonneg_left _ hKpos.le
          calc ‖rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z‖
              = ‖rgP α m * rgG2 α m c z + -(rgQ α m * rgG1 α m c z)‖ := by
                rw [sub_eq_add_neg]
            _ ≤ ‖rgP α m * rgG2 α m c z‖ + ‖-(rgQ α m * rgG1 α m c z)‖ := norm_add_le _ _
            _ = rgP α m * ‖rgG2 α m c z‖ + rgQ α m * ‖rgG1 α m c z‖ := by
                simp only [norm_neg, norm_mul, Real.norm_of_nonneg hpnn,
                  Real.norm_of_nonneg hqpos.le]
            _ ≤ rgP α m * (Cf * z ^ d) + rgQ α m * (c1 * z ^ d) :=
                add_le_add (mul_le_mul_of_nonneg_left h2n hpnn)
                  (mul_le_mul_of_nonneg_left h1n hqpos.le)
      _ = A * z ^ d := by rw [hAdef]; ring
  -- the explicit first derivative rewrites the second limit into a polynomial expression
  have hder : ∀ z : ℝ, 0 < z →
      deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
          * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 2
        = (rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z))
            * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 3 := by
    intro z hz0
    have hz0ne : z ≠ 0 := ne_of_gt hz0
    have hmain : z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
        = rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z) :=
      radGreen_deriv1_form hα m hcont h0 hinf z hz0
    have hd : deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
        = rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z) / z := by
      rw [eq_div_iff hz0ne, mul_comm]
      exact hmain
    rw [hd, div_mul_eq_mul_div, div_div, show z * z ^ 2 = z ^ 3 from by ring]
  have hQ : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      ‖(Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 / z ^ 3‖
        ≤ B ^ 2 * z ^ (2 * d - 3) := by
    intro z hz
    have hz0 : 0 < z := hz.1
    have hz1 : z ≤ 1 := le_of_lt hz.2
    have hz3 : (0 : ℝ) < z ^ 3 := pow_pos hz0 3
    have hb := hG z hz0 hz1
    have hsq : (z ^ d) ^ 2 / z ^ 3 = z ^ (2 * d - 3) := rpow_sq_div_cube hz0
    calc ‖(Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 / z ^ 3‖
        = ‖Work.FTS.PhiStar.Radial.radGreen α m c z‖ ^ 2 / z ^ 3 := by
          rw [norm_div, norm_pow, Real.norm_of_nonneg hz3.le]
      _ ≤ (B * z ^ d) ^ 2 / z ^ 3 := by
          apply div_le_div_of_nonneg_right _ hz3.le
          exact pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = B ^ 2 * z ^ (2 * d - 3) := by
          rw [mul_pow, mul_div_assoc, hsq]
  have hQ2 : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      ‖deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
          * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 2‖ ≤ A * B * z ^ (2 * d - 3) := by
    intro z hz
    have hz0 : 0 < z := hz.1
    have hz1 : z ≤ 1 := le_of_lt hz.2
    have hz3 : (0 : ℝ) < z ^ 3 := pow_pos hz0 3
    have hb := hG z hz0 hz1
    have hTb := hT z hz0 hz1
    rw [hder z hz0]
    calc ‖(rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z))
            * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 3‖
        = ‖rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z)‖
            * ‖Work.FTS.PhiStar.Radial.radGreen α m c z‖ / z ^ 3 := by
          rw [norm_div, norm_mul, Real.norm_of_nonneg hz3.le]
      _ ≤ (A * z ^ d) * (B * z ^ d) / z ^ 3 := by
          apply div_le_div_of_nonneg_right _ hz3.le
          exact mul_le_mul hTb hb (norm_nonneg _)
            (mul_nonneg hAnn (Real.rpow_nonneg hz0.le d))
      _ = A * B * z ^ (2 * d - 3) := by
          have h1 : (A * z ^ d) * (B * z ^ d) = A * B * (z ^ d * z ^ d) := by ring
          rw [h1, mul_div_assoc, rpow_mul_self_div_cube hz0]
  exact ⟨tendsto_zero_of_bound (F := fun z => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 / z ^ 3)
      (C := B ^ 2) (d := 2 * d - 3) (by linarith) (sq_nonneg B) hQ,
    tendsto_zero_of_bound (F := fun z => deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
        * Work.FTS.PhiStar.Radial.radGreen α m c z / z ^ 2)
      (C := A * B) (d := 2 * d - 3) (by linarith) (mul_nonneg hAnn hBnn) hQ2⟩

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.CmpSupp.lintegral_psiSeries_le_Iz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.CmpSupp

/-- Almost every `z ∈ Iz = [0,∞)` satisfies `0 < z`. -/
theorem ae_mem_Ioi_of_Iz :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [MeasureTheory.ae_restrict_iff (p := fun z : ℝ => 0 < z)
    (by exact measurableSet_Ioi)]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0} : Set ℝ)) ?_
    (MeasureTheory.measure_singleton 0)
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  push Not at hx
  simp only [Set.mem_singleton_iff]
  simp only [Work.Spaces.Iz, Set.mem_Ici] at hx
  exact le_antisymm hx.2 hx.1

/-- Almost every `θ ∈ Iθ = [0,π/2]` lies in the open interval `(0,π/2)`. -/
theorem ae_mem_Ioo_of_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [MeasureTheory.ae_restrict_iff
    (p := fun θ : ℝ => θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (by exact measurableSet_Ioo)]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0, Real.pi / 2} : Set ℝ)) ?_
    ((Set.toFinite ({0, Real.pi / 2} : Set ℝ)).measure_zero MeasureTheory.volume)
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  push Not at hx
  simp only [Work.Spaces.Iθ, Set.mem_Icc] at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hx with ⟨⟨h1, h2⟩, h3⟩
  rcases lt_or_eq_of_le h1 with h | h
  · right
    by_contra hne
    exact h3 ⟨h, lt_of_le_of_ne h2 hne⟩
  · exact Or.inl h.symm

theorem lintegral_psiSeries_le_Iz {α : ℝ} {F : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hconv : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ) Filter.atTop
        (nhds (Work.FTS.PhiStar.Series.psiSeries α F z θ)))
    (hmeas : ∀ N : ℕ, AEMeasurable (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hbd : ∀ N : ℕ, (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) ≤ ENNReal.ofReal C) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) ≤ ENNReal.ofReal C := by
  -- ## Step 1: Fatou's lemma in the angular variable, for each `z > 0`.
  have htheta : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ Filter.liminf (fun N : ℕ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Filter.atTop := by
    intro z hz
    have hfat := MeasureTheory.lintegral_liminf_le'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) (u := Filter.atTop)
      (f := fun (N : ℕ) (θ : ℝ) => ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (fun N => Work.FTS.ClassC.lplst_theta_integrand_aemeasurable α F N z)
    -- the pointwise identification of the `liminf` with the angular energy of `psiSeries`
    have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Filter.liminf (fun N : ℕ => ENNReal.ofReal
          ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Filter.atTop
        = ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      intro θ hθ
      have hc : Continuous (fun x : ℝ => ENNReal.ofReal
          (x ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
        ENNReal.continuous_ofReal.comp
          (((continuous_id.pow 2).mul continuous_const).mul continuous_const)
      exact (hc.continuousAt.tendsto.comp (hconv z hz θ hθ)).liminf_eq
    have hae : (fun θ : ℝ => Filter.liminf (fun N : ℕ => ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Filter.atTop)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
      ae_mem_Ioo_of_Iθ.mono fun θ hθ => hpt θ hθ
    rw [MeasureTheory.lintegral_congr_ae hae] at hfat
    exact hfat
  -- ## Step 2: Fatou's lemma in the radial variable.
  have hzfat := MeasureTheory.lintegral_liminf_le'
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz) (u := Filter.atTop)
    (f := fun (N : ℕ) (z : ℝ) => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
      ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
    hmeas
  -- ## Step 3: compare the target with the (radial) `liminf` of the angular energies.
  have hmono : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
      ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, Filter.liminf (fun N : ℕ => ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Filter.atTop :=
    MeasureTheory.lintegral_mono_ae <| ae_mem_Ioi_of_Iz.mono fun z hz => htheta z hz
  -- ## Step 4: the uniform bound on the truncations bounds the `liminf`.
  have hbound : Filter.liminf (fun N : ℕ => ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Filter.atTop
      ≤ ENNReal.ofReal C := by
    have hbdd : Filter.IsBoundedUnder (fun x1 x2 : ℝ≥0∞ => x2 ≤ x1) Filter.atTop
        (fun N : ℕ => ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
      Filter.isBoundedUnder_of ⟨0, fun _ => bot_le⟩
    exact Filter.liminf_le_of_frequently_le (Filter.Eventually.of_forall hbd).frequently hbdd
  calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, Filter.liminf (fun N : ℕ => ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Filter.atTop := hmono
    _ ≤ Filter.liminf (fun N : ℕ => ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Filter.atTop := hzfat
    _ ≤ ENNReal.ofReal C := hbound

end Work.FTS.ClassCHon.CmpSupp
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.Zpz.radGreen_Dz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz

/-
# `Work.FTS.ClassCHon.Zpz.radGreen_Dz`

`radGreen α m c` (`Work.FTS.PhiStar.Radial.radGreen`, the explicit decaying-at-`∞` solution of the
mode-`m` radial Euler equation `-α²z²a'' - α(5+α)z a' + λ_m a = c`, with
`λ_m = 2m(2m+5)`) is the Euler Green function

  `radGreen α m c z = K·(z^{-q}·∫_0^z c t^{q-1} + z^{p}·∫_z^∞ c t^{-p-1})`,
  `K = 1/(α(4m+5))`, `q = (2m+5)/α`, `p = 2m/α`.

The claim is that the `t ∂_t`-weighted source `t ↦ t·c'(t)` is again handled by the *same* Green
function, one order up: `z·∂_z(radGreen α m c) z = radGreen α m (t·c') z`.  The reason is that
`D = z∂_z` commutes with the Euler operator `R = -(α²D² + 5αD)`; on the explicit formula this is
the pair of integration-by-parts identities

  `∫_0^z c'(t) t^q dt = c(z)z^q - q·∫_0^z c t^{q-1}dt`   (boundary `c t^q → 0` at `0⁺`),
  `∫_z^∞ c'(t)t^{-p}dt = -c(z)z^{-p} + p·∫_z^∞ c t^{-p-1}dt`  (boundary `c t^{-p} → 0` at `∞`),

whose boundary terms vanish (`Work.FTS.ClassCHon.Zpz.rpow_mul_tendsto_zero_lower` /
`..._upper`) thanks to the two integrability hypotheses `h0` (which kills a non-zero limit at `0⁺`
because `1/t` is not integrable there) and `hinf` (same at `∞`).

The first derivative of `radGreen` is taken from the existing
`Work.FTS.ClassC.radGreen_deriv1_form`,
`z·∂_z(radGreen α m c) z = K·(p·rgG2 - q·rgG1) = K·(p·z^p·rgB - q·z^{-q}·rgA)`, and the right-hand
side is unfolded with `Work.FTS.EllExist.radGreen_eq`; the two integration-by-parts identities
(`Work.FTS.ClassCHon.Zpz.radGreen_ibp_lower` / `..._upper`) then turn the two sides into the same
expression.
-/

theorem radGreen_Dz {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hcd : ∀ t : ℝ, 0 < t → HasDerivAt c (deriv c t) t)
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1))
    (hd0 : MeasureTheory.IntegrableOn
      (fun t => t * deriv c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1))
    (hdinf : MeasureTheory.IntegrableOn
      (fun t => t * deriv c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z →
      z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
        = Work.FTS.PhiStar.Radial.radGreen α m (fun t => t * deriv c t) z := by
  intro z hz
  have hcont : ContinuousOn c (Set.Ioi 0) :=
    fun t ht => (hcd t ht).continuousAt.continuousWithinAt
  have hliml := rpow_mul_tendsto_zero_lower (q := Work.FTS.EllExist.rgQ α m)
    (c := c) hcd h0 hd0
  have hlimu := rpow_mul_tendsto_zero_upper (p := Work.FTS.EllExist.rgP α m)
    (c := c) hcd hinf hdinf
  have hlow := radGreen_ibp_lower (α := α) (c := c)
    hα m hcd hliml h0 hd0 hdinf z hz
  have hup := radGreen_ibp_upper (α := α) (c := c)
    hα m hcd hlimu hinf hd0 hdinf z hz
  have hL := Work.FTS.ClassC.radGreen_deriv1_form (α := α) (c := c)
    hα m hcont h0 hinf z hz
  have hR := Work.FTS.EllExist.radGreen_eq α m (fun t => t * deriv c t) z
  rw [hL, hR]
  simp only [Work.FTS.EllExist.rgG1, Work.FTS.EllExist.rgG2]
  rw [hlow, hup]
  have hzq : z ^ (-(Work.FTS.EllExist.rgQ α m)) * z ^ (Work.FTS.EllExist.rgQ α m) = 1 := by
    rw [← Real.rpow_add hz, neg_add_cancel, Real.rpow_zero]
  have hzp : z ^ (Work.FTS.EllExist.rgP α m) * z ^ (-(Work.FTS.EllExist.rgP α m)) = 1 := by
    rw [← Real.rpow_add hz, add_neg_cancel, Real.rpow_zero]
  have h1 : z ^ (-(Work.FTS.EllExist.rgQ α m)) * (c z * z ^ (Work.FTS.EllExist.rgQ α m))
      = c z := by
    rw [show z ^ (-(Work.FTS.EllExist.rgQ α m)) * (c z * z ^ (Work.FTS.EllExist.rgQ α m))
        = c z * (z ^ (-(Work.FTS.EllExist.rgQ α m)) * z ^ (Work.FTS.EllExist.rgQ α m))
        from by ring, hzq, mul_one]
  have h2 : z ^ (Work.FTS.EllExist.rgP α m) * (c z * z ^ (-(Work.FTS.EllExist.rgP α m)))
      = c z := by
    rw [show z ^ (Work.FTS.EllExist.rgP α m) * (c z * z ^ (-(Work.FTS.EllExist.rgP α m)))
        = c z * (z ^ (Work.FTS.EllExist.rgP α m) * z ^ (-(Work.FTS.EllExist.rgP α m)))
        from by ring, hzp, mul_one]
  have hgoal :
      Work.FTS.EllExist.rgP α m * (z ^ (Work.FTS.EllExist.rgP α m)
            * Work.FTS.EllExist.rgB α m c z)
          - Work.FTS.EllExist.rgQ α m * (z ^ (-(Work.FTS.EllExist.rgQ α m))
            * Work.FTS.EllExist.rgA α m c z)
        = z ^ (-(Work.FTS.EllExist.rgQ α m))
            * (c z * z ^ (Work.FTS.EllExist.rgQ α m)
              - Work.FTS.EllExist.rgQ α m * Work.FTS.EllExist.rgA α m c z)
          + z ^ (Work.FTS.EllExist.rgP α m) * (-(c z * z ^ (-(Work.FTS.EllExist.rgP α m)))
              + Work.FTS.EllExist.rgP α m * Work.FTS.EllExist.rgB α m c z) := by
    rw [mul_sub, mul_add, mul_neg, h1, h2]
    ring
  rw [hgoal]
  ring

end Work.FTS.ClassCHon.Zpz
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.pth2_slice_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

theorem pth2_slice_integrable (G : ℝ → ℝ → ℝ)
    (hinn : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  intro z hz
  -- `w z ≠ 0` for `z > 0`, so the factor `(w z)^2` can be divided out.
  have hw : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
  have hc : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hw
  refine (hinn z hz).mul_const ((Work.Spaces.w z) ^ 2)⁻¹ |>.congr ?_
  filter_upwards with θ
  rw [show (Work.Spaces.pth (Work.Spaces.pth G) z θ ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) * ((Work.Spaces.w z) ^ 2)⁻¹
      = (Work.Spaces.pth (Work.Spaces.pth G) z θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
        * ((Work.Spaces.w z) ^ 2 * ((Work.Spaces.w z) ^ 2)⁻¹) by ring,
    mul_inv_cancel₀ hc, mul_one]

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.thetaPoincare =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open MeasureTheory Set Filter
open scoped Real Topology


end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.slice_int_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

open scoped Real Topology Interval
open MeasureTheory Set Filter

theorem slice_int_bound {D : ℝ → ℝ} {c l u : ℝ} (hlu : l ≤ u) (hl : 0 < l)
    (hu : u < Real.pi / 2) (hul : u - l ≤ Real.pi / 4) (hcont : ContinuousOn D (Set.uIcc l u))
    (hc : ∀ t ∈ Set.Icc l u, |c - t| ≤ Real.pi / 4)
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ => D θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ) :
    |∫ t in l..u, (c - t) * D t| ≤ (Real.pi / 4) * Real.sqrt (Real.pi / 4) *
      Real.sqrt (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  -- abbreviate the constant `π/4` so that the arithmetic at the end is painless
  set P : ℝ := Real.pi / 4 with hP
  have hPnn : 0 ≤ P := by rw [hP]; positivity
  -- `D` is continuous on the closed interval `[l, u]`
  have hcontIcc : ContinuousOn D (Set.Icc l u) := by
    rwa [Set.uIcc_of_le hlu] at hcont
  -- the interval `[l, u]` lies inside `Iθ = [0, π/2]`
  have hsub : Set.Icc l u ⊆ Work.Spaces.Iθ := by
    intro t ht
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨le_trans (le_of_lt hl) ht.1, le_of_lt (lt_of_le_of_lt ht.2 hu)⟩
  -- on `[l, u]` the weight `sin(2θ)^{-η}` dominates `1`
  have hthEta : ∀ t ∈ Set.Icc l u, (1 : ℝ) ≤ Work.FTS.EllipticEst.thEta t := by
    intro t ht
    have ht0 : 0 < Real.sin (2 * t) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith [ht.1, hl]
      · linarith [ht.2, hu]
    have hle : Real.sin (2 * t) ≤ 1 := Real.sin_le_one _
    have hneg : -(Work.Spaces.eta) ≤ 0 := by linarith [Work.Spaces.eta_nonneg]
    have h := Real.rpow_le_rpow_of_nonpos ht0 hle hneg
    rw [Real.one_rpow] at h
    simpa [Work.FTS.EllipticEst.thEta] using h
  have hIntD2 : IntegrableOn (fun t : ℝ => D t ^ 2) (Set.Icc l u) :=
    (hcontIcc.pow 2).integrableOn_compact isCompact_Icc
  have hIntD2w : IntegrableOn (fun t : ℝ => D t ^ 2 * Work.FTS.EllipticEst.thEta t)
      (Set.Icc l u) := hint.mono_set hsub
  -- the `L²`-norm over `[l, u]` is dominated by the weighted one over `Iθ`
  have hX : ∫ t in l..u, D t ^ 2 ≤
      ∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    have hconv : ∫ t in l..u, D t ^ 2 = ∫ t in Set.Icc l u, D t ^ 2 := by
      rw [intervalIntegral.integral_of_le hlu, integral_Icc_eq_integral_Ioc]
    rw [hconv]
    have h1 : ∫ t in Set.Icc l u, D t ^ 2 ≤
        ∫ t in Set.Icc l u, D t ^ 2 * Work.FTS.EllipticEst.thEta t :=
      setIntegral_mono_on hIntD2 hIntD2w measurableSet_Icc
        (fun t ht => le_mul_of_one_le_right (sq_nonneg _) (hthEta t ht))
    have h2 : ∫ t in Set.Icc l u, D t ^ 2 * Work.FTS.EllipticEst.thEta t ≤
        ∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      refine setIntegral_mono_set hint ?_ ?_
      · filter_upwards [ae_restrict_mem (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
          with θ hθ
        exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
      · exact Filter.Eventually.of_forall (fun x hx => hsub hx)
    exact le_trans h1 h2
  -- Cauchy–Schwarz for the interval integral, applied to `((c - ·) D, 1)`
  have hf_cont : ContinuousOn (fun t : ℝ => (c - t) * D t) (Set.uIcc l u) :=
    ((continuous_const.sub continuous_id).continuousOn).mul hcont
  have hg_cont : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.uIcc l u) :=
    continuous_const.continuousOn
  have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt l u hlu
    (f := fun t : ℝ => (c - t) * D t) (g := fun _ : ℝ => (1 : ℝ)) hf_cont hg_cont
  have h_one : ∫ t in l..u, (1 : ℝ) ^ 2 = u - l := by
    rw [show (1 : ℝ) ^ 2 = 1 by norm_num, intervalIntegral.integral_const]
    simp
  -- the pointwise bound on the integrand, from `|c - t| ≤ P`
  have hpt : ∀ t ∈ Set.Icc l u, ((c - t) * D t) ^ 2 ≤ P ^ 2 * D t ^ 2 := by
    intro t ht
    have h1 : |c - t| ≤ P := hc t ht
    have h2 : (c - t) ^ 2 ≤ P ^ 2 := by
      have h3 := abs_le.mp h1
      nlinarith [h3.1, h3.2]
    calc ((c - t) * D t) ^ 2 = (c - t) ^ 2 * D t ^ 2 := by ring
      _ ≤ P ^ 2 * D t ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have hmono : ∫ t in l..u, ((c - t) * D t) ^ 2 ≤ P ^ 2 * ∫ t in l..u, D t ^ 2 := by
    have hg2 : ContinuousOn (fun t : ℝ => P ^ 2 * D t ^ 2) (Set.uIcc l u) :=
      continuousOn_const.mul (hcont.pow 2)
    have hb := intervalIntegral.integral_mono_on hlu
      ((hf_cont.pow 2).intervalIntegrable (μ := volume))
      (hg2.intervalIntegrable (μ := volume)) hpt
    rwa [intervalIntegral.integral_const_mul] at hb
  have hsqrt : Real.sqrt (P ^ 2 * ∫ t in l..u, D t ^ 2) =
      P * Real.sqrt (∫ t in l..u, D t ^ 2) := by
    rw [show P ^ 2 * ∫ t in l..u, D t ^ 2 = (P * P) * ∫ t in l..u, D t ^ 2 by ring,
      Real.sqrt_mul (mul_nonneg hPnn hPnn), Real.sqrt_mul_self (x := P) hPnn]
  have hXS : Real.sqrt (∫ t in l..u, D t ^ 2) ≤
      Real.sqrt (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
    Real.sqrt_le_sqrt hX
  calc |∫ t in l..u, (c - t) * D t|
      = |∫ t in l..u, (c - t) * D t * 1| := by
        congr 1
        exact intervalIntegral.integral_congr (fun t _ => (mul_one _).symm)
    _ ≤ Real.sqrt (∫ t in l..u, ((c - t) * D t) ^ 2) * Real.sqrt (∫ t in l..u, (1 : ℝ) ^ 2) :=
        hcs
    _ = Real.sqrt (∫ t in l..u, ((c - t) * D t) ^ 2) * Real.sqrt (u - l) := by rw [h_one]
    _ ≤ Real.sqrt (P ^ 2 * ∫ t in l..u, D t ^ 2) * Real.sqrt P :=
        mul_le_mul (Real.sqrt_le_sqrt hmono) (Real.sqrt_le_sqrt hul)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = P * Real.sqrt (∫ t in l..u, D t ^ 2) * Real.sqrt P := by rw [hsqrt]
    _ ≤ P * Real.sqrt (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ) *
          Real.sqrt P :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXS hPnn) (Real.sqrt_nonneg P)
    _ = P * Real.sqrt P *
          Real.sqrt (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by ring

end Work.FTS.EllSol.EllPkgAux.MollSmooth
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.K5c

/-! ## The smooth bump -/

/-- The standard smooth bump `T(1 - t²)`, supported in `[-1,1]`. -/
def sBump (t : ℝ) : ℝ := Real.smoothTransition (1 - t ^ 2)

theorem sBump_nonneg (t : ℝ) : 0 ≤ sBump t := by
  unfold sBump
  by_cases h : 1 - t ^ 2 ≤ 0
  · rw [Real.smoothTransition.zero_of_nonpos h]
  · exact (Real.smoothTransition.pos_of_pos (not_le.mp h)).le

theorem sBump_pos_of_abs_lt_one {t : ℝ} (ht : |t| < 1) : 0 < sBump t := by
  unfold sBump
  refine Real.smoothTransition.pos_of_pos ?_
  rw [abs_lt] at ht
  nlinarith [ht.1, ht.2]

theorem sBump_eq_zero_of_one_le_abs {t : ℝ} (ht : 1 ≤ |t|) : sBump t = 0 := by
  unfold sBump
  refine Real.smoothTransition.zero_of_nonpos ?_
  have h : (1 : ℝ) ≤ t ^ 2 := by
    have h2 : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith [abs_nonneg t, ht]
  linarith

theorem sBump_even (t : ℝ) : sBump (-t) = sBump t := by
  unfold sBump
  rw [neg_sq]

theorem sBump_le_one (t : ℝ) : sBump t ≤ 1 := by
  unfold sBump
  by_cases h : 1 - t ^ 2 ≤ 0
  · rw [Real.smoothTransition.zero_of_nonpos h]; norm_num
  · by_cases h1 : 1 ≤ 1 - t ^ 2
    · rw [Real.smoothTransition.one_of_one_le h1]
    · exact Real.smoothTransition.le_one _

theorem sBump_continuous : Continuous sBump :=
  Real.smoothTransition.continuous.comp (by fun_prop)

/-- The total mass of the bump. -/
def sMass : ℝ := ∫ t in (-1 : ℝ)..1, sBump t

theorem sMass_pos : 0 < sMass := by
  rw [sMass]
  refine (intervalIntegral.integral_pos_iff_support_of_nonneg_ae
    (μ := MeasureTheory.volume) (a := (-1 : ℝ)) (b := 1)
    (Filter.Eventually.of_forall fun t => sBump_nonneg t)
    (sBump_continuous.intervalIntegrable (-1) 1)).mpr ⟨by norm_num, ?_⟩
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ Function.support sBump ∩ Set.Ioc (-1 : ℝ) 1 := by
    intro t ht
    refine ⟨Function.mem_support.mpr (ne_of_gt (sBump_pos_of_abs_lt_one ?_)),
      ⟨by linarith [ht.1], le_of_lt ht.2⟩⟩
    rw [abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmono : MeasureTheory.volume (Set.Ioo (0 : ℝ) 1)
      ≤ MeasureTheory.volume (Function.support sBump ∩ Set.Ioc (-1 : ℝ) 1) :=
    measure_mono hsub
  have hpos : (0 : ENNReal) < MeasureTheory.volume (Set.Ioo (0 : ℝ) 1) := by
    rw [Real.volume_Ioo]; norm_num
  exact lt_of_lt_of_le hpos hmono

theorem sBump_eq_indicator : sBump = Set.indicator (Set.Ioc (-1 : ℝ) 1) sBump := by
  funext t
  by_cases ht : t ∈ Set.Ioc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht]
    rw [Set.mem_Ioc, not_and_or] at ht
    rcases ht with h | h
    · exact sBump_eq_zero_of_one_le_abs (le_trans (by linarith) (neg_le_abs t))
    · exact sBump_eq_zero_of_one_le_abs (le_trans (by linarith) (le_abs_self t))

theorem sMass_eq_integral : (∫ t : ℝ, sBump t) = sMass := by
  rw [sMass, intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  conv_lhs => rw [sBump_eq_indicator]
  exact MeasureTheory.integral_indicator (μ := MeasureTheory.volume)
    (f := (sBump : ℝ → ℝ)) (s := Set.Ioc (-1 : ℝ) 1) measurableSet_Ioc

/-- The normalised bump of radius `ε`. -/
def sKer (ε t : ℝ) : ℝ := (ε * sMass)⁻¹ * sBump (t / ε)

theorem sKer_nonneg {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 ≤ sKer ε t := by
  rw [sKer]
  exact mul_nonneg (inv_nonneg.mpr (mul_nonneg hε.le sMass_pos.le)) (sBump_nonneg _)

theorem sKer_eq_zero_of_le_abs {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : ε ≤ |t|) :
    sKer ε t = 0 := by
  rw [sKer, sBump_eq_zero_of_one_le_abs ?_, mul_zero]
  rw [abs_div, abs_of_pos hε, le_div_iff₀ hε, one_mul]
  exact ht

theorem sKer_even (ε t : ℝ) : sKer ε (-t) = sKer ε t := by
  simp only [sKer, neg_div, sBump_even]

theorem sKer_integral_eq_one {ε : ℝ} (hε : 0 < ε) : (∫ t : ℝ, sKer ε t) = 1 := by
  have h1 : (∫ t : ℝ, sBump (t / ε)) = ε * sMass := by
    have h3 : (∫ t : ℝ, sBump (t / ε)) = ∫ t : ℝ, sBump (ε⁻¹ * t) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show sBump (t / ε) = sBump (ε⁻¹ * t)
      rw [div_eq_inv_mul, mul_comm]
    rw [h3, MeasureTheory.Measure.integral_comp_mul_left (g := sBump) (a := ε⁻¹), inv_inv,
      abs_of_pos hε, sMass_eq_integral, smul_eq_mul, mul_comm]
  unfold sKer
  rw [MeasureTheory.integral_const_mul, h1, inv_mul_cancel₀ (mul_pos hε sMass_pos).ne']

/-! ## The doubly-odd extension and the mollifications -/

/-- The extension of the slice `s ↦ u z s` odd about both `0` and `π/2` (on the range
`(-π/2, π)` relevant for the angular mollification at scales `ε ≤ 1/2`). -/
def Qext (u : ℝ → ℝ → ℝ) (z s : ℝ) : ℝ :=
  if 0 ≤ s ∧ s ≤ Real.pi / 2 then u z s
  else if s < 0 then -u z (-s) else -u z (Real.pi - s)

theorem Qext_of_mem (u : ℝ → ℝ → ℝ) (z s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    Qext u z s = u z s := by
  rw [Qext, if_pos (Set.mem_Icc.mp hs)]

theorem Qext_neg_of_pos (u : ℝ → ℝ → ℝ) (z s : ℝ) (hs : 0 < s) :
    Qext u z (-s) = -u z s := by
  rw [Qext, if_neg (fun h => by linarith [h.1, hs]), if_pos (by linarith [hs]), neg_neg]

theorem Qext_pihalf_odd (u : ℝ → ℝ → ℝ) (z s : ℝ) (hs : 0 < s) (hs' : s ≤ Real.pi / 2) :
    Qext u z (Real.pi / 2 - s) = -Qext u z (Real.pi / 2 + s) := by
  rw [Qext, if_pos ⟨by linarith [hs], by linarith [hs']⟩]
  rw [Qext, if_neg (fun h => by linarith [h.2, hs]), if_neg (by linarith [Real.pi_pos, hs]),
    show Real.pi - (Real.pi / 2 + s) = Real.pi / 2 - s by ring, neg_neg]

/-- The angular mollification of the datum `u` at scale `ε`. -/
def thMoll (u : ℝ → ℝ → ℝ) (ε z θ : ℝ) : ℝ :=
  ∫ s : ℝ, sKer ε (θ - s) * Qext u z s

/-- The logarithmic-radial mollification of the angular mollification. -/
def zmoll (u : ℝ → ℝ → ℝ) (δ ε z θ : ℝ) : ℝ :=
  ∫ t : ℝ, sKer δ (Real.log z - t) * thMoll u ε (Real.exp t) θ

end Work.FTS.EllSol.PkgK5.K5c
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.TraceEngine.agmonCutChainPos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5.TraceEngine

open MeasureTheory Set Filter
open scoped Real Topology

local notation "σ" => Work.FTS.EllipticEst.thEta

theorem agmonCutChainPos {m P A B : ℝ → ℝ}
    (hAgmon : ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      (1 / 200) * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
          + 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
    (hm : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt m (2 * P θ) θ)
    (hP : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt P (A θ + B θ) θ)
    (hAB : ContinuousOn (fun θ : ℝ => A θ + B θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hmpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < m θ)
    (hCS : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), P θ ^ 2 ≤ m θ * A θ)
    (htr0 : Filter.Tendsto m (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htr1 : Filter.Tendsto m (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hA : MeasureTheory.IntegrableOn (fun θ : ℝ => A θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hmI : MeasureTheory.IntegrableOn (fun θ : ℝ => m θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hB : MeasureTheory.IntegrableOn (fun θ : ℝ => B θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (1 / 200) * (∫ θ in Work.Spaces.Iθ, A θ * Work.FTS.EllipticEst.thEta θ)
      ≤ 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, m θ * Work.FTS.EllipticEst.thEta θ)
        - ∫ θ in Work.Spaces.Iθ, B θ * Work.FTS.EllipticEst.thEta θ := by
  classical
  set g : ℝ → ℝ := fun θ => Real.sqrt (m θ) with hg
  -- The pointwise facts about `√m` supplied by the sibling `sqrt_m_calc`.
  have hSMC := Work.FTS.EllSol.PkgK5.InterpTrace.sqrt_m_calc hm hP hAB hmpos hCS
  have hC2g : ContDiffOn ℝ 2 g (Set.Ioo (0:ℝ) (Real.pi/2)) := by rw [hg]; exact hSMC.1
  have hderivsq_le : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), (deriv g θ)^2 ≤ A θ := by
    intro θ hθ; rw [hg]; exact hSMC.2.1 θ hθ
  have hident : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      (deriv g θ)^2 + g θ * deriv (deriv g) θ = A θ + B θ := by
    intro θ hθ; rw [hg]; exact hSMC.2.2 θ hθ
  -- The closed interval differs from the open interval by a null set.
  have hsub : Set.Ioo (0:ℝ) (Real.pi/2) ⊆ Work.Spaces.Iθ := by
    intro θ hθ; rw [Work.Spaces.Iθ, Set.mem_Icc]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hσnn : ∀ θ, θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) → 0 ≤ σ θ :=
    fun θ hθ => Work.FTS.EllipticEst.thEta_nonneg (hsub hθ)
  have hμ : (volume : Measure ℝ).restrict Work.Spaces.Iθ
      = (volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) (Real.pi/2)) := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := (0:ℝ)) (b := Real.pi/2))).symm
  have hmem : Set.Ioo (0:ℝ) (Real.pi/2)
      ∈ MeasureTheory.ae ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
    rw [hμ]; exact MeasureTheory.self_mem_ae_restrict measurableSet_Ioo
  -- Continuity of the weight and of the two profiles on the open interval.
  have hσcont : ContinuousOn σ (Set.Ioo (0:ℝ) (Real.pi/2)) := by
    unfold Work.FTS.EllipticEst.thEta
    refine ContinuousOn.rpow_const ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro θ hθ
      left
      exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])).ne'
  have hmcont : ContinuousOn m (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    fun θ hθ => (hm θ hθ).continuousAt.continuousWithinAt
  have hPcont : ContinuousOn P (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    fun θ hθ => (hP θ hθ).continuousAt.continuousWithinAt
  have hderivg : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), deriv g θ = P θ / Real.sqrt (m θ) := by
    intro θ hθ
    have h := (hm θ hθ).sqrt (hmpos θ hθ).ne'
    rw [hg]
    rw [h.deriv]
    exact mul_div_mul_left (P θ) (Real.sqrt (m θ)) (by norm_num)
  -- Endpoint vanishing of `√m`, from `m → 0`.
  have hlim0 : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    rw [hg]
    have h := (Real.continuous_sqrt.tendsto 0).comp htr0
    simpa [Function.comp_def, Real.sqrt_zero] using h
  have hlim1 : Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    rw [hg]
    have h := (Real.continuous_sqrt.tendsto 0).comp htr1
    simpa [Function.comp_def, Real.sqrt_zero] using h
  -- The a.e. identities of the three Agmon integrands.
  have haeI1 : (fun θ : ℝ => (deriv g θ) ^ 2 * σ θ)
      ≤ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ] (fun θ : ℝ => A θ * σ θ) := by
    filter_upwards [hmem] with θ hθ
    exact mul_le_mul_of_nonneg_right (hderivsq_le θ hθ) (hσnn θ hθ)
  have haeI2 : (fun θ : ℝ => g θ * deriv (deriv g) θ * σ θ)
      =ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (A θ + B θ - (deriv g θ) ^ 2) * σ θ) := by
    filter_upwards [hmem] with θ hθ
    have h1 := hident θ hθ
    have h2 : g θ * deriv (deriv g) θ = A θ + B θ - (deriv g θ) ^ 2 := by linarith
    rw [h2]
  have haeI3 : (fun θ : ℝ => (g θ) ^ 2 * σ θ)
      =ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ] (fun θ : ℝ => m θ * σ θ) := by
    filter_upwards [hmem] with θ hθ
    rw [hg]
    rw [Real.sq_sqrt (le_of_lt (hmpos θ hθ))]
  -- Integrability of the three Agmon integrands for `f = √m`.
  have hInt2 : MeasureTheory.IntegrableOn (fun θ : ℝ => (g θ) ^ 2 * σ θ) Work.Spaces.Iθ := by
    have hae : (fun θ : ℝ => m θ * σ θ) =ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ]
        (fun θ : ℝ => (g θ) ^ 2 * σ θ) := by
      filter_upwards [hmem] with θ hθ
      rw [hg]
      rw [Real.sq_sqrt (le_of_lt (hmpos θ hθ))]
    exact hmI.congr hae
  have hABI : Integrable (fun θ : ℝ => (A θ + B θ) * σ θ)
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
    have h := hA.add hB
    refine h.congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [Pi.add_apply]
    ring
  have hInt1 : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv g θ) ^ 2 * σ θ) Work.Spaces.Iθ := by
    have hsqrtcont : ContinuousOn (fun θ : ℝ => Real.sqrt (m θ)) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      Real.continuous_sqrt.comp_continuousOn hmcont
    have hdivcont : ContinuousOn (fun θ : ℝ => P θ / Real.sqrt (m θ))
        (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      hPcont.div hsqrtcont (fun θ hθ => (Real.sqrt_pos.mpr (hmpos θ hθ)).ne')
    have hGcont : ContinuousOn (fun θ : ℝ => (P θ / Real.sqrt (m θ)) ^ 2 * σ θ)
        (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      (hdivcont.pow 2).mul hσcont
    have hGasm : AEStronglyMeasurable (fun θ : ℝ => (P θ / Real.sqrt (m θ)) ^ 2 * σ θ)
        ((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) (Real.pi/2))) :=
      hGcont.aestronglyMeasurable measurableSet_Ioo
    have hAoo : Integrable (fun θ : ℝ => A θ * σ θ)
        ((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) (Real.pi/2))) :=
      hA.mono_set hsub
    have hbound : ∀ᵐ θ ∂((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) (Real.pi/2))),
        ‖(P θ / Real.sqrt (m θ)) ^ 2 * σ θ‖ ≤ A θ * σ θ := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
      have hm0 : 0 < m θ := hmpos θ hθ
      have hs0 : 0 ≤ σ θ := hσnn θ hθ
      have hsq : (P θ / Real.sqrt (m θ)) ^ 2 = P θ ^ 2 / m θ := by
        rw [div_pow, Real.sq_sqrt (le_of_lt hm0)]
      have hle : (P θ / Real.sqrt (m θ)) ^ 2 ≤ A θ := by
        rw [hsq, div_le_iff₀ hm0]
        linarith [hCS θ hθ]
      have hnn : 0 ≤ (P θ / Real.sqrt (m θ)) ^ 2 * σ θ := mul_nonneg (sq_nonneg _) hs0
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_right hle hs0
    have hGint : Integrable (fun θ : ℝ => (P θ / Real.sqrt (m θ)) ^ 2 * σ θ)
        ((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) (Real.pi/2))) :=
      hAoo.mono' hGasm hbound
    have hae : (fun θ : ℝ => (deriv g θ) ^ 2 * σ θ)
        =ᵐ[(volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) (Real.pi/2))]
        (fun θ : ℝ => (P θ / Real.sqrt (m θ)) ^ 2 * σ θ) := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
      rw [hderivg θ hθ]
    have hIoo : Integrable (fun θ : ℝ => (deriv g θ) ^ 2 * σ θ)
        ((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) (Real.pi/2))) :=
      hGint.congr hae.symm
    rw [MeasureTheory.IntegrableOn, hμ]
    exact hIoo
  have hInt3 : MeasureTheory.IntegrableOn (fun θ : ℝ => g θ * deriv (deriv g) θ * σ θ)
      Work.Spaces.Iθ := by
    have hbase : Integrable (fun θ : ℝ => (A θ + B θ - (deriv g θ) ^ 2) * σ θ)
        ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
      have h := hABI.sub hInt1
      refine h.congr (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [Pi.sub_apply]
      ring
    refine hbase.congr ?_
    filter_upwards [hmem] with θ hθ
    have h1 := hident θ hθ
    have h2 : g θ * deriv (deriv g) θ = A θ + B θ - (deriv g θ) ^ 2 := by linarith
    rw [h2]
  -- The Agmon inequality for `f = √m`.
  have hAgm := hAgmon g hC2g hlim0 hlim1 hInt1 hInt2 hInt3
  have hsplit : (∫ θ in Work.Spaces.Iθ, (A θ + B θ) * σ θ)
      = (∫ θ in Work.Spaces.Iθ, A θ * σ θ) + (∫ θ in Work.Spaces.Iθ, B θ * σ θ) := by
    calc (∫ θ in Work.Spaces.Iθ, (A θ + B θ) * σ θ)
        = (∫ θ in Work.Spaces.Iθ, (A θ * σ θ + B θ * σ θ)) :=
            MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
      _ = (∫ θ in Work.Spaces.Iθ, A θ * σ θ) + (∫ θ in Work.Spaces.Iθ, B θ * σ θ) :=
            MeasureTheory.integral_add hA hB
  have hI1le : (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * σ θ)
      ≤ (∫ θ in Work.Spaces.Iθ, A θ * σ θ) := MeasureTheory.integral_mono_ae hInt1 hA haeI1
  have hI3eq : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * σ θ)
      = (∫ θ in Work.Spaces.Iθ, m θ * σ θ) := MeasureTheory.integral_congr_ae haeI3
  have hI2eq : (∫ θ in Work.Spaces.Iθ, g θ * deriv (deriv g) θ * σ θ)
      = (∫ θ in Work.Spaces.Iθ, A θ * σ θ) + (∫ θ in Work.Spaces.Iθ, B θ * σ θ)
        - (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * σ θ) := by
    calc (∫ θ in Work.Spaces.Iθ, g θ * deriv (deriv g) θ * σ θ)
        = (∫ θ in Work.Spaces.Iθ, (A θ + B θ - (deriv g θ) ^ 2) * σ θ) :=
            MeasureTheory.integral_congr_ae haeI2
      _ = (∫ θ in Work.Spaces.Iθ, ((A θ + B θ) * σ θ - (deriv g θ) ^ 2 * σ θ)) :=
            MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
      _ = (∫ θ in Work.Spaces.Iθ, (A θ + B θ) * σ θ)
            - (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * σ θ) :=
            MeasureTheory.integral_sub hABI hInt1
      _ = ((∫ θ in Work.Spaces.Iθ, A θ * σ θ) + (∫ θ in Work.Spaces.Iθ, B θ * σ θ))
            - (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * σ θ) := by
            rw [hsplit]
  -- The final arithmetic.
  have hfin : (1 / 200) * (∫ θ in Work.Spaces.Iθ, A θ * σ θ)
      ≤ 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, m θ * σ θ)
        - (∫ θ in Work.Spaces.Iθ, B θ * σ θ) := by
    rw [hI2eq, hI3eq] at hAgm
    linarith
  exact hfin

end Work.FTS.EllSol.PkgK5.TraceEngine
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.TraceEngine.slice_rate_thEta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5.TraceEngine

open MeasureTheory Set Filter
open scoped Real

/-- Elementary AM–GM bound: for `w > 0` with `w⁻¹ ≤ 1`,
`|g| ≤ ½ g² w + ½`.  Indeed `2 ab ≤ a² + b²` with `a = |g| √w`, `b = 1/√w`. -/
private lemma amgm_abs_le (g w : ℝ) (hw : 0 < w) (hw1 : w⁻¹ ≤ 1) :
    |g| ≤ (1 / 2) * (g ^ 2 * w) + 1 / 2 := by
  set s := Real.sqrt w with hs
  have hs2 : s ^ 2 = w := by rw [hs, Real.sq_sqrt hw.le]
  have hsne : s ≠ 0 := by rw [hs]; exact ne_of_gt (Real.sqrt_pos.mpr hw)
  have h2 := two_mul_le_add_sq (|g| * s) (s⁻¹)
  have hAB : (|g| * s) * s⁻¹ = |g| := by rw [mul_assoc, mul_inv_cancel₀ hsne, mul_one]
  have h2' : 2 * |g| ≤ g ^ 2 * w + w⁻¹ := by
    have h2'' : 2 * ((|g| * s) * s⁻¹) ≤ (|g| * s) ^ 2 + (s⁻¹) ^ 2 := by
      calc 2 * ((|g| * s) * s⁻¹) = 2 * (|g| * s) * s⁻¹ := by ring
        _ ≤ (|g| * s) ^ 2 + (s⁻¹) ^ 2 := h2
    rw [hAB, mul_pow, sq_abs, hs2, inv_pow, hs2] at h2''
    linarith
  linarith

/- Weighted slicewise rate bound at both endpoints of `(0,π/2)`, for the weight
`thEta θ = sin(2θ)^{-η}`, `η = 99/100`.

Intended proof route (both endpoints identical):
1. From `hint`, `deriv f` is integrable on `Ioo 0 (π/2)` and on every sub-interval (AM–GM:
   `|g| ≤ ((g^2 * thEta) + thEta⁻¹)/2`, and `thEta⁻¹ = sin(2θ)^η ≤ 1` is bounded, hence integrable
   on the finite-measure set).
2. `Work.FTS.EllipticEst.TT.sliceFtcKey` gives the two antiderivative relations
   `f θ - c = ∫ s in Ioo 0 θ, deriv f s` and `f θ - c' = -∫ s in Ioo θ (π/2), deriv f s`.
3. `Work.EllipticEst.Core.weightedCS` (weight `w := thEta`, `g := deriv f`, on `s := Ioo 0 θ`,
   which is measurable, with `thEta > 0` and continuous there) gives
   `(∫ s in Ioo 0 θ, deriv f s)^2 ≤ (∫ s in Ioo 0 θ, (deriv f s)^2 * thEta s) * (∫ s in Ioo 0 θ, (thEta s)⁻¹)`
   and `(thEta s)⁻¹ = sin(2s)^η ≤ 1` on `Ioo 0 θ`, so the last factor is `≤ θ`.
4. The constant `c` is `0`: step 3 gives `(f θ - c)^2 ≤ θ * K` with
   `K = ∫ s in Ioo 0 (π/2), (deriv f s)^2 * thEta s` fixed, so `f - c → 0` at `0⁺`
   (`Work.FTS.EllipticEst.TT.sqBoundTendstoPos`, or `Filter.Tendsto` by squeeze), while `f → 0`
   by `htr0`, whence `c = 0` (unique limits). Same at `π/2` with `htr1`.
   This is exactly the pattern of `Work.FTS.EllipticEst.EllTwoAsm.LightSliceRate` (the weight
   `sin(2θ)^a`, `0 < a < 1` case), but that result is NOT applicable here: it needs
   `∫ (deriv f)^2 sin(2θ)^a` with `0 < a < 1` and only yields the weaker factor `C θ^{1-a}`
   instead of `θ`. -/
theorem slice_rate_thEta (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    (htr0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htr1 : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hint : MeasureTheory.IntegrableOn
      (fun s : ℝ => (deriv f s) ^ 2 * Work.FTS.EllipticEst.thEta s) (Set.Ioo 0 (Real.pi / 2))) :
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (f θ) ^ 2 ≤ θ * ∫ s in Set.Ioo 0 θ, (deriv f s) ^ 2 * Work.FTS.EllipticEst.thEta s) ∧
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (f θ) ^ 2 ≤ (Real.pi / 2 - θ) *
        ∫ s in Set.Ioo θ (Real.pi / 2), (deriv f s) ^ 2 * Work.FTS.EllipticEst.thEta s) := by
  have hη0 : (0 : ℝ) < Work.Spaces.eta := Work.Spaces.eta_pos
  -- ## Elementary facts about the weight `thEta`
  have hthEta_pos : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 < Work.FTS.EllipticEst.thEta t := by
    intro t ht
    exact Real.rpow_pos_of_pos (Work.FTS.EllipticEst.sin_two_pos ht) _
  have hthEta_eq : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.thEta t = ((Real.sin (2 * t)) ^ Work.Spaces.eta)⁻¹ := by
    intro t ht
    simp only [Work.FTS.EllipticEst.thEta]
    exact Real.rpow_neg (le_of_lt (Work.FTS.EllipticEst.sin_two_pos ht)) _
  have hthEta_inv : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.FTS.EllipticEst.thEta t)⁻¹ = (Real.sin (2 * t)) ^ Work.Spaces.eta := by
    intro t ht
    rw [hthEta_eq t ht, inv_inv]
  have hthEta_inv_le : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.FTS.EllipticEst.thEta t)⁻¹ ≤ 1 := by
    intro t ht
    rw [hthEta_inv t ht]
    exact Work.FTS.EllipticEst.sin_two_rpow_le_one hη0.le ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hthEta_cont : ContinuousOn (fun t : ℝ => Work.FTS.EllipticEst.thEta t)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h : ContinuousOn (fun t : ℝ => (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun t ht => Or.inl (ne_of_gt (Work.FTS.EllipticEst.sin_two_pos ht)))
    simpa only [Work.FTS.EllipticEst.thEta] using h
  -- ## Integrability of the dual weight and its integral bounds
  have hthEta_inv_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => (Work.FTS.EllipticEst.thEta t)⁻¹) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => (Real.sin (2 * t)) ^ Work.Spaces.eta)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (Work.FTS.EllipticEst.integrableOn_sin_two_rpow hη0.le).1.mono_set Set.Ioo_subset_Icc_self
    refine hbase.congr_fun ?_ measurableSet_Ioo
    intro t ht
    exact (hthEta_inv t ht).symm
  have hIntInvL : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ t in Set.Ioo 0 θ, (Work.FTS.EllipticEst.thEta t)⁻¹) ≤ θ := by
    intro θ hθ
    have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 θ) :=
      MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    calc (∫ t in Set.Ioo 0 θ, (Work.FTS.EllipticEst.thEta t)⁻¹)
        ≤ ∫ t in Set.Ioo 0 θ, (1 : ℝ) := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ hone ?_
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
            exact inv_nonneg.mpr (le_of_lt (Real.rpow_pos_of_pos
              (Work.FTS.EllipticEst.sin_two_pos ⟨ht.1, lt_trans ht.2 hθ.2⟩) _))
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
            exact hthEta_inv_le t ⟨ht.1, lt_trans ht.2 hθ.2⟩
      _ = θ := by
          rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
            ENNReal.toReal_ofReal (sub_nonneg.mpr hθ.1.le)]
          simp
  have hIntInvR : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ t in Set.Ioo θ (Real.pi / 2), (Work.FTS.EllipticEst.thEta t)⁻¹)
        ≤ Real.pi / 2 - θ := by
    intro θ hθ
    have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo θ (Real.pi / 2)) :=
      MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    calc (∫ t in Set.Ioo θ (Real.pi / 2), (Work.FTS.EllipticEst.thEta t)⁻¹)
        ≤ ∫ t in Set.Ioo θ (Real.pi / 2), (1 : ℝ) := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ hone ?_
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
            exact inv_nonneg.mpr (le_of_lt (Real.rpow_pos_of_pos
              (Work.FTS.EllipticEst.sin_two_pos ⟨lt_trans hθ.1 ht.1, ht.2⟩) _))
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
            exact hthEta_inv_le t ⟨lt_trans hθ.1 ht.1, ht.2⟩
      _ = Real.pi / 2 - θ := by
          rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
            ENNReal.toReal_ofReal (sub_nonneg.mpr hθ.2.le)]
          simp
  -- ## `deriv f` is integrable (AM–GM against the dual weight)
  have hderiv_int : MeasureTheory.IntegrableOn (fun t : ℝ => deriv f t)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hA : MeasureTheory.IntegrableOn
        (fun t : ℝ => (1 / 2) * ((deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hint.const_mul (1 / 2)
    have hB : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 / 2 : ℝ))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    have hF := hA.add hB
    refine MeasureTheory.Integrable.mono' hF ((measurable_deriv f).aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs]
    exact amgm_abs_le (deriv f t) (Work.FTS.EllipticEst.thEta t)
      (hthEta_pos t ht) (hthEta_inv_le t ht)
  have hderiv_sub : ∀ a b : ℝ, Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      MeasureTheory.IntegrableOn (fun t : ℝ => deriv f t) (Set.Ioo a b) :=
    fun a b h => hderiv_int.mono_set h
  -- ## The two antiderivative relations
  obtain ⟨⟨cL, hKeyL⟩, ⟨cR, hKeyR⟩⟩ := Work.FTS.EllipticEst.TT.sliceFtcKey f hf hderiv_sub
  have hderiv_cont : ContinuousOn (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hKnn : 0 ≤ ∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
      (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun t ht => mul_nonneg (sq_nonneg _) (le_of_lt (hthEta_pos t ht)))
  -- ## Left endpoint: Cauchy–Schwarz against the dual weight
  have hboundL : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (f θ - cL) ^ 2 ≤ θ * ∫ t in Set.Ioo 0 θ,
        (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
    intro θ hθ
    have hsub : Set.Ioo (0 : ℝ) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      fun t ht => ⟨ht.1, lt_trans ht.2 hθ.2⟩
    have hcs := Work.EllipticEst.Core.weightedCS (s := Set.Ioo (0 : ℝ) θ) measurableSet_Ioo
        (w := fun t : ℝ => Work.FTS.EllipticEst.thEta t) (g := fun t : ℝ => deriv f t)
        (fun t ht => hthEta_pos t (hsub ht))
        (hthEta_cont.mono hsub)
        (hderiv_cont.mono hsub)
        (hint.mono_set hsub)
        (hthEta_inv_int.mono_set hsub)
    have hAnn : 0 ≤ ∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo
        (fun t ht => mul_nonneg (sq_nonneg _) (le_of_lt (hthEta_pos t (hsub ht))))
    rw [hKeyL θ hθ]
    calc (∫ t in Set.Ioo 0 θ, deriv f t) ^ 2
        ≤ (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            * (∫ t in Set.Ioo 0 θ, (Work.FTS.EllipticEst.thEta t)⁻¹) := hcs
      _ ≤ (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) * θ :=
          mul_le_mul_of_nonneg_left (hIntInvL θ hθ) hAnn
      _ = θ * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by ring
  have hmonoL : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
        ≤ ∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
    intro θ hθ
    refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (le_of_lt (hthEta_pos t ht))
    · filter_upwards with t ht
      exact ⟨ht.1, lt_trans ht.2 hθ.2⟩
  have hcL0 : cL = 0 := by
    have hlim : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds cL) :=
      (Work.FTS.EllipticEst.TT.sqBoundTendstoPos (p := (1 : ℝ)) one_pos).1 f cL
        (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) hKnn
        (fun θ hθ => by
          calc (f θ - cL) ^ 2
              ≤ θ * (∫ t in Set.Ioo 0 θ,
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := hboundL θ hθ
            _ ≤ θ * (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
                mul_le_mul_of_nonneg_left (hmonoL θ hθ) (le_of_lt hθ.1)
            _ = (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) * θ ^ (1 : ℝ) := by
                rw [Real.rpow_one]; ring)
    exact tendsto_nhds_unique hlim htr0
  -- ## Right endpoint
  have hboundR : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (f θ - cR) ^ 2 ≤ (Real.pi / 2 - θ) * ∫ t in Set.Ioo θ (Real.pi / 2),
        (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
    intro θ hθ
    have hsub : Set.Ioo θ (Real.pi / 2) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      fun t ht => ⟨lt_trans hθ.1 ht.1, ht.2⟩
    have hcs := Work.EllipticEst.Core.weightedCS (s := Set.Ioo θ (Real.pi / 2)) measurableSet_Ioo
        (w := fun t : ℝ => Work.FTS.EllipticEst.thEta t) (g := fun t : ℝ => deriv f t)
        (fun t ht => hthEta_pos t (hsub ht))
        (hthEta_cont.mono hsub)
        (hderiv_cont.mono hsub)
        (hint.mono_set hsub)
        (hthEta_inv_int.mono_set hsub)
    have hAnn : 0 ≤ ∫ t in Set.Ioo θ (Real.pi / 2),
        (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo
        (fun t ht => mul_nonneg (sq_nonneg _) (le_of_lt (hthEta_pos t (hsub ht))))
    rw [hKeyR θ hθ, neg_sq]
    calc (∫ t in Set.Ioo θ (Real.pi / 2), deriv f t) ^ 2
        ≤ (∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            * (∫ t in Set.Ioo θ (Real.pi / 2), (Work.FTS.EllipticEst.thEta t)⁻¹) := hcs
      _ ≤ (∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            * (Real.pi / 2 - θ) := mul_le_mul_of_nonneg_left (hIntInvR θ hθ) hAnn
      _ = (Real.pi / 2 - θ) * (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by ring
  have hmonoR : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
        ≤ ∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
    intro θ hθ
    refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (le_of_lt (hthEta_pos t ht))
    · filter_upwards with t ht
      exact ⟨lt_trans hθ.1 ht.1, ht.2⟩
  have hcR0 : cR = 0 := by
    have hlim : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds cR) :=
      (Work.FTS.EllipticEst.TT.sqBoundTendstoPos (p := (1 : ℝ)) one_pos).2 f cR
        (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) hKnn
        (fun θ hθ => by
          calc (f θ - cR) ^ 2
              ≤ (Real.pi / 2 - θ) * (∫ t in Set.Ioo θ (Real.pi / 2),
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := hboundR θ hθ
            _ ≤ (Real.pi / 2 - θ) * (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
                mul_le_mul_of_nonneg_left (hmonoR θ hθ) (by linarith [hθ.2])
            _ = (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) * (Real.pi / 2 - θ) ^ (1 : ℝ) := by
                rw [Real.rpow_one]; ring)
    exact tendsto_nhds_unique hlim htr1
  constructor
  · intro θ hθ
    have h := hboundL θ hθ
    rw [hcL0] at h
    simpa using h
  · intro θ hθ
    have h := hboundR θ hθ
    rw [hcR0] at h
    simpa using h

end Work.FTS.EllSol.PkgK5.TraceEngine
end
-- ===== merged: Submission.Work.FTS.EllSol.VopAux.SliceTraceDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.VopAux

set_option autoImplicit false

/-- The angular integrand attached to a single slice `u`:
`(u θ)² sin(2θ)^{-η} + ∑_{1 ≤ i ≤ K} (D_θ^i u θ)² sin(2θ)^{-γ}`. -/
def sliceW (K : ℕ) (α : ℝ) (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
    + ∑ i ∈ Finset.Icc 1 K,
        (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ

/-- The integral over `Iθ` of the slice functional `sliceW`. -/
def sliceF (K : ℕ) (α : ℝ) (u : ℝ → ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, sliceW K α u θ


/-- The slice functional `sliceW` is nonnegative on `Iθ`. -/
theorem sliceW_nonneg (K : ℕ) (α : ℝ) (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ sliceW K α u θ := by
  rw [sliceW]
  refine add_nonneg (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)) ?_
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθ)

/-- `sliceF` is nonnegative. -/
theorem sliceF_nonneg (K : ℕ) (α : ℝ) (u : ℝ → ℝ) : 0 ≤ sliceF K α u := by
  rw [sliceF]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ => ?_
  exact sliceW_nonneg K α u hθ


end Work.FTS.EllSol.VopAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.sf_LopIter_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open Filter
open scoped Topology



end Work.FTS.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.sin_sq_mul_Wt_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

/-- **The angular weight comparison behind the level-six slots.**

For `α ≤ 1`, `θ ∈ Iθ` and `sin(2θ) > 0` one has

  `sin(2θ)² · Wt(α,z,θ)² ≤ (w z / sin(2θ)^{η/2})²`,

i.e. the `γ`-weighted square slot `sin²·Wt² = w²·sin^{2-γ}` of the `ℋ⁶`-integrand is dominated by
the `η`-weighted one `w²·sin^{-η}`: after cancelling `w²` the claim is
`sin(2θ)^{2-γ} ≤ sin(2θ)^{-η}`, which holds because `2 - γ + η ≥ 0` (`γ = 1 + α/10 ≤ 11/10`,
`η = 99/100`) and `sin(2θ) ≤ 1`. -/
theorem sin_sq_mul_Wt_sq_le (α : ℝ) (hα1 : α ≤ 1) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hs : 0 < Real.sin (2 * θ)) :
    (Real.sin (2 * θ)) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
      ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
  set s := Real.sin (2 * θ) with hsdef
  have hs0 : 0 < s := by rw [hsdef]; exact hs
  have hsle : s ≤ 1 := by rw [hsdef]; exact Real.sin_le_one (2 * θ)
  have hexp : 0 ≤ 2 - Work.Spaces.gam α + Work.Spaces.eta := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
  -- the exponent comparison `s ^ (2 - γ) ≤ s ^ (-η)`
  have hkey : s ^ (2 - Work.Spaces.gam α) ≤ s ^ (-(Work.Spaces.eta)) := by
    have h1 : s ^ (2 - Work.Spaces.gam α + Work.Spaces.eta) ≤ 1 :=
      Real.rpow_le_one hs0.le hsle hexp
    calc s ^ (2 - Work.Spaces.gam α)
        = s ^ ((2 - Work.Spaces.gam α + Work.Spaces.eta) + (-(Work.Spaces.eta))) := by
          congr 1; ring
      _ = s ^ (2 - Work.Spaces.gam α + Work.Spaces.eta) * s ^ (-(Work.Spaces.eta)) :=
          Real.rpow_add hs0 _ _
      _ ≤ 1 * s ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hs0.le _)
      _ = s ^ (-(Work.Spaces.eta)) := one_mul _
  -- the two algebraic normalisations of the two sides
  have hγsq : (s ^ (-(Work.Spaces.gam α / 2))) ^ 2 = s ^ (-(Work.Spaces.gam α)) := by
    calc (s ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = s ^ (-(Work.Spaces.gam α / 2)) * s ^ (-(Work.Spaces.gam α / 2)) := by rw [pow_two]
      _ = s ^ (-(Work.Spaces.gam α / 2) + -(Work.Spaces.gam α / 2)) :=
          (Real.rpow_add hs0 _ _).symm
      _ = s ^ (-(Work.Spaces.gam α)) := by congr 1; ring
  have hηsq : ((s ^ (Work.Spaces.eta / 2))⁻¹) ^ 2 = s ^ (-(Work.Spaces.eta)) := by
    have h1 : (s ^ (Work.Spaces.eta / 2))⁻¹ = s ^ (-(Work.Spaces.eta / 2)) :=
      (Real.rpow_neg hs0.le _).symm
    calc ((s ^ (Work.Spaces.eta / 2))⁻¹) ^ 2
        = (s ^ (Work.Spaces.eta / 2))⁻¹ * (s ^ (Work.Spaces.eta / 2))⁻¹ := by rw [pow_two]
      _ = s ^ (-(Work.Spaces.eta / 2)) * s ^ (-(Work.Spaces.eta / 2)) := by rw [h1]
      _ = s ^ (-(Work.Spaces.eta / 2) + -(Work.Spaces.eta / 2)) :=
          (Real.rpow_add hs0 _ _).symm
      _ = s ^ (-(Work.Spaces.eta)) := by congr 1; ring
  have hWt : (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * s ^ (-(Work.Spaces.gam α)) := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, ← hsdef, mul_pow, hγsq]
  have hR : (Work.Spaces.w z / s ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * s ^ (-(Work.Spaces.eta)) := by
    rw [div_eq_mul_inv, mul_pow, hηsq]
  rw [hWt, hR]
  have hs2 : s ^ (2 : ℕ) * s ^ (-(Work.Spaces.gam α)) = s ^ (2 - Work.Spaces.gam α) := by
    rw [← Real.rpow_natCast s 2, ← Real.rpow_add hs0]
    congr 1
  calc s ^ 2 * ((Work.Spaces.w z) ^ 2 * s ^ (-(Work.Spaces.gam α)))
      = (Work.Spaces.w z) ^ 2 * (s ^ 2 * s ^ (-(Work.Spaces.gam α))) := by ring
    _ = (Work.Spaces.w z) ^ 2 * s ^ (2 - Work.Spaces.gam α) := by rw [hs2]
    _ ≤ (Work.Spaces.w z) ^ 2 * s ^ (-(Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_left hkey (sq_nonneg _)

end Work.FTS.EllipticEst.Cert
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Gsing_tendsto_atTop_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Gsing α F z → 0` as `z → ∞`

`Work.Elliptic.Gsing α F = Gstar α F + Gbar α F` is the singular part of Elgindi's §'The
singular term'.  Both summands are integrals of the angular moment `F_*`, and we show each of
them tends to `0` at `+∞` from `Work.Spaces.L2Mem F` alone (that is, `∫_0^∞ ∫_θ F(z,θ)² < ∞`).

The reduction is through the pointwise majorant of `F_*` supplied by Cauchy–Schwarz:

  `|F_*(s)| ≤ gsingMaj F s := √(π/2 · ∫_θ F(s,θ)² dθ)`,   `∫_0^∞ (gsingMaj F s)² < ∞`.

* `Gstar α F = -(1/(4α)) L₁₂(F)` and `L₁₂(F)(z) = 3 ∫_z^∞ F_*(s)/s ds`
  (`Work.Elliptic.L12_eq_radial`), a tail of an `L¹` function:
  `L12_tendsto_atTop_zero`.
* `Gbar α F z = -(3/(4α)) z^{-5/α} ∫_0^z s^{5/α-1} F_*(s) ds`, the weighted Hardy transform,
  which vanishes at `+∞` by `harOp_tendsto_zero`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The angular slice of `F` and the pointwise majorant of `F_*` -/

/-- The angular `L²` density `∫_θ F(s,θ)² dθ` of `F`. -/
def gsingSlice (F : ℝ → ℝ → ℝ) (s : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, (F s θ) ^ 2

/-- The Cauchy–Schwarz majorant `√(π/2 · ∫_θ F(s,θ)²)` of `|F_*(F)(s)|`. -/
def gsingMaj (F : ℝ → ℝ → ℝ) (s : ℝ) : ℝ := Real.sqrt (Real.pi / 2 * gsingSlice F s)

lemma gsingSlice_nonneg (F : ℝ → ℝ → ℝ) (s : ℝ) : 0 ≤ gsingSlice F s :=
  integral_nonneg fun _ => sq_nonneg _

lemma gsingMaj_nonneg (F : ℝ → ℝ → ℝ) (s : ℝ) : 0 ≤ gsingMaj F s :=
  Real.sqrt_nonneg _

/-- `gsingMaj F` is the square root of the `L¹` function `(π/2) · gsingSlice F`. -/
lemma gsingMaj_sq (F : ℝ → ℝ → ℝ) (s : ℝ) :
    (gsingMaj F s) ^ 2 = Real.pi / 2 * gsingSlice F s := by
  rw [gsingMaj, Real.sq_sqrt (mul_nonneg (by positivity) (gsingSlice_nonneg F s))]

/-- Cauchy–Schwarz for the angular moment (`Work.Elliptic.Fstar_sq_le`): `|F_*|` is dominated by
`gsingMaj`. -/
lemma abs_Fstar_le_gsingMaj (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) {s : ℝ} (hs : 0 < s) :
    |Work.Elliptic.Fstar F s| ≤ gsingMaj F s := by
  have h : (Work.Elliptic.Fstar F s) ^ 2
      ≤ Real.pi / 2 * gsingSlice F s := by
    simpa [gsingSlice] using Work.Elliptic.Fstar_sq_le F s (hL2.1 s (le_of_lt hs))
  calc |Work.Elliptic.Fstar F s| = Real.sqrt ((Work.Elliptic.Fstar F s) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (Real.pi / 2 * gsingSlice F s) := Real.sqrt_le_sqrt h
    _ = gsingMaj F s := rfl

/-- The angular slice of an `L2Mem` function is integrable on `(0,∞)`. -/
lemma integrableOn_gsingSlice (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) :
    IntegrableOn (gsingSlice F) (Set.Ioi 0) := by
  have h2 : IntegrableOn (gsingSlice F) (Set.Ici (0 : ℝ)) := hL2.2
  exact MeasureTheory.IntegrableOn.mono_set h2 Set.Ioi_subset_Ici_self

/-- `M²` is integrable for `M = gsingMaj F`. -/
lemma integrableOn_gsingMaj_sq (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) :
    IntegrableOn (fun s => (gsingMaj F s) ^ 2) (Set.Ioi 0) := by
  have h := (integrableOn_gsingSlice F hL2).const_mul (Real.pi / 2)
  refine MeasureTheory.IntegrableOn.congr_fun h (fun s _ => ?_) measurableSet_Ioi
  exact (gsingMaj_sq F s).symm

/-- `gsingMaj F` is a.e. measurable. -/
lemma aemeasurable_gsingMaj (F : ℝ → ℝ → ℝ) (hL2 : Work.Spaces.L2Mem F) :
    AEMeasurable (gsingMaj F) (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have h1 : AEMeasurable (fun s => Real.pi / 2 * gsingSlice F s)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    ((integrableOn_gsingSlice F hL2).aestronglyMeasurable.const_mul
      (Real.pi / 2)).aemeasurable
  exact (Real.continuous_sqrt.comp_aestronglyMeasurable h1.aestronglyMeasurable).aemeasurable

/-! ## The Hardy form of `Gbar` -/

/-- `Gbar α F z = -(3/(4α)) · z^{-5/α} ∫_0^z s^{5/α-1} F_*(s) ds`, i.e. `Gbar α F` is
`-(3/(4α))` times the weighted Hardy transform of the angular moment. -/
lemma Gbar_eq_harOp_form (α : ℝ) (hα : α ≠ 0) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Gbar α F z = -(3 / (4 * α)) * (z ^ (-(5 / α))
      * ∫ s in (0 : ℝ)..z, s ^ (5 / α - 1) * Work.Elliptic.Fstar F s) := by
  have hint : ∫ s in (0 : ℝ)..z, s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s
      = ∫ s in (0 : ℝ)..z, s ^ (5 / α - 1) * Work.Elliptic.Fstar F s :=
    intervalIntegral.integral_congr (fun s _ => by rw [div_sub_one hα])
  rw [Work.Elliptic.Gbar, hint]
  ring

/-! ## The target -/

theorem Gsing_tendsto_atTop_zero (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hL2 : Work.Spaces.L2Mem F) :
    Filter.Tendsto (fun z : ℝ => Work.Elliptic.Gsing α F z) Filter.atTop (nhds (0 : ℝ)) := by
  have hαne : α ≠ 0 := hα.ne'
  have hGstar : Filter.Tendsto (fun z : ℝ => Work.Elliptic.Gstar α F z) Filter.atTop
      (nhds (0 : ℝ)) := by
    have h := L12_tendsto_atTop_zero F hL2
    have hfun : (fun z : ℝ => Work.Elliptic.Gstar α F z)
        = fun z : ℝ => -(1 / (4 * α)) * Work.Elliptic.L12 F z := funext fun z => rfl
    rw [hfun]
    simpa using h.const_mul (-(1 / (4 * α)))
  have hGbar : Filter.Tendsto (fun z : ℝ => Work.Elliptic.Gbar α F z) Filter.atTop
      (nhds (0 : ℝ)) := by
    have h := GsingAux.harOp_tendsto_zero (5 / α) (by positivity) (Work.Elliptic.Fstar F)
      (gsingMaj F)
      (gsingMaj_nonneg F) (integrableOn_gsingMaj_sq F hL2) (aemeasurable_gsingMaj F hL2)
      (fun s hs => abs_Fstar_le_gsingMaj F hL2 hs)
    have hfun : (fun z : ℝ => Work.Elliptic.Gbar α F z) = fun z : ℝ => -(3 / (4 * α))
        * (z ^ (-(5 / α))
          * ∫ s in (0 : ℝ)..z, s ^ (5 / α - 1) * Work.Elliptic.Fstar F s) :=
      funext fun z => Gbar_eq_harOp_form α hαne F z
    rw [hfun]
    simpa using h.const_mul (-(3 / (4 * α)))
  have hsum : Filter.Tendsto
      (fun z : ℝ => Work.Elliptic.Gstar α F z + Work.Elliptic.Gbar α F z)
      Filter.atTop (nhds (0 + 0)) := hGstar.add hGbar
  simpa [Work.Elliptic.Gsing] using hsum

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Ae.ZeroHardy.sliceZeroLimitHardy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Ae.ZeroHardy

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false

/-!
# The two-derivative weighted Hardy inequality for slices with vanishing endpoint limits

For `g` of class `C²` on `(0, π/2)` whose one-sided limits at `0` and `π/2` both vanish and whose
second derivative is square-integrable against the weight `σ θ = sin(2θ)^{-η}` (`η = 99/100`),
we prove

  `∫⁻_θ ofReal (g θ² σ θ) ≤ ofReal C · ∫⁻_θ ofReal (g'' θ² σ θ)`.

This is the analytic core of the slice part of Elgindi's Step 1/2 in the `AeData` class
(`Work.FTS.EllipticEst.H2W.Ae`).

The proof is the one recorded in
`Submission/Work/FTS/EllipticEst/H2W/Ae/SliceTwo/NOTES_greenSliceBound.md`:

* for `a < θ < b` inside the interval, the *interior Green identity* expresses `g θ` as the
  weighted average `c₁ g a + c₂ g b` minus the two second-derivative integrals against the
  Green kernel `ψ₁ t = c₁ (t - a)`, `ψ₂ t = c₂ (b - t)`, and `|ψᵢ| ≤ (b-a)/4`;
* the two endpoint limits remove `|g a|`, `|g b|`;
* Cauchy–Schwarz turns `(∫ |g''|)²` into `(∫ g''² σ)(∫ σ^{-1})`.
-/

/-! ## Elementary helpers -/

/-- AM–GM: `x y ≤ (x+y)²/4` for `x, y ≥ 0`. -/
private lemma mul_le_sq_div_four {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y ≤ (x + y) ^ 2 / 4 := by
  nlinarith [sq_nonneg (x - y)]

private lemma sEta_nonneg_sl {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (Work.FTS.EllipticEst.sin_two_nonneg hθ) _

private lemma sEta_zero_left : Work.FTS.EllipticEst.sEta 0 = 0 := by
  simp only [Work.FTS.EllipticEst.sEta, mul_zero, Real.sin_zero]
  rw [Real.zero_rpow (by
    rw [Work.Spaces.eta]; norm_num)]

private lemma sEta_zero_right : Work.FTS.EllipticEst.sEta (Real.pi / 2) = 0 := by
  simp only [Work.FTS.EllipticEst.sEta]
  rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
  rw [Real.zero_rpow (by
    rw [Work.Spaces.eta]; norm_num)]

/-! ## The interior Green identity -/

/-- **The interior Green identity.**  For `a < θ < b` inside `(0, π/2)` and `g` of class `C²`
there, the value `g θ` is the weighted average `c₁ g a + c₂ g b` minus the second-derivative
integrals against the Green kernel. -/
private theorem green_identity {g : ℝ → ℝ} {a θ b : ℝ} (haθ : a < θ) (hθb : θ < b)
    (hsm : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (ha : 0 < a) (hb : b < Real.pi / 2) :
    g θ = ((b - θ) / (b - a)) * g a + ((θ - a) / (b - a)) * g b
      - (∫ t in a..θ, (((b - θ) / (b - a)) * (t - a))
          * deriv (fun s => deriv g s) t)
      - (∫ t in θ..b, (((θ - a) / (b - a)) * (b - t))
          * deriv (fun s => deriv g s) t) := by
  have hπ : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hba : (0 : ℝ) < b - a := by linarith
  set c₁ : ℝ := (b - θ) / (b - a) with hc₁
  set c₂ : ℝ := (θ - a) / (b - a) with hc₂
  have hsub1 : Set.uIcc a θ ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hsub2 : Set.uIcc θ b ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  -- differentiability
  have hdg : DifferentiableOn ℝ g (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.differentiableOn (by norm_num)
  have hdg1c : ContDiffOn ℝ 1 (deriv g) (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdg1 : DifferentiableOn ℝ (deriv g) (Set.Ioo 0 (Real.pi / 2)) :=
    hdg1c.differentiableOn (by norm_num)
  have hdg2c : ContDiffOn ℝ 0 (deriv (fun s => deriv g s)) (Set.Ioo 0 (Real.pi / 2)) :=
    hdg1c.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont2 : ContinuousOn (deriv (fun s => deriv g s)) (Set.Ioo 0 (Real.pi / 2)) :=
    hdg2c.continuousOn
  have hg_at1 : ∀ x ∈ Set.uIcc a θ, HasDerivAt g (deriv g x) x := fun x hx =>
    hdg.hasDerivAt (isOpen_Ioo.mem_nhds (hsub1 hx))
  have hv_at1 : ∀ x ∈ Set.uIcc a θ, HasDerivAt (deriv g) (deriv (fun s => deriv g s) x) x :=
    fun x hx => hdg1.hasDerivAt (isOpen_Ioo.mem_nhds (hsub1 hx))
  have hg_at2 : ∀ x ∈ Set.uIcc θ b, HasDerivAt g (deriv g x) x := fun x hx =>
    hdg.hasDerivAt (isOpen_Ioo.mem_nhds (hsub2 hx))
  have hv_at2 : ∀ x ∈ Set.uIcc θ b, HasDerivAt (deriv g) (deriv (fun s => deriv g s) x) x :=
    fun x hx => hdg1.hasDerivAt (isOpen_Ioo.mem_nhds (hsub2 hx))
  -- the kernels
  have hker1 : ∀ x ∈ Set.uIcc a θ, HasDerivAt (fun t : ℝ => c₁ * (t - a)) c₁ x := by
    intro x _
    have h : HasDerivAt (fun t : ℝ => t - a) 1 x := (hasDerivAt_id x).sub_const a
    simpa using h.const_mul c₁
  have hker2 : ∀ x ∈ Set.uIcc θ b, HasDerivAt (fun t : ℝ => c₂ * (b - t)) (-c₂) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => b - t) (-1) x :=
      (hasDerivAt_id x).const_sub b
    simpa using h1.const_mul c₂
  have hker1' : IntervalIntegrable (fun _ : ℝ => c₁) MeasureTheory.volume a θ :=
    intervalIntegrable_const
  have hker2' : IntervalIntegrable (fun _ : ℝ => -c₂) MeasureTheory.volume θ b :=
    intervalIntegrable_const
  have hint1 : IntervalIntegrable (deriv g) MeasureTheory.volume a θ :=
    (hdg1.continuousOn.mono hsub1).intervalIntegrable
  have hint2 : IntervalIntegrable (deriv g) MeasureTheory.volume θ b :=
    (hdg1.continuousOn.mono hsub2).intervalIntegrable
  have hinv1 : IntervalIntegrable (deriv (fun s => deriv g s)) MeasureTheory.volume a θ :=
    (hcont2.mono hsub1).intervalIntegrable
  have hinv2 : IntervalIntegrable (deriv (fun s => deriv g s)) MeasureTheory.volume θ b :=
    (hcont2.mono hsub2).intervalIntegrable
  -- the two integrations by parts
  have hIBP1 : (∫ x in a..θ, (c₁ * (x - a)) * deriv (fun s => deriv g s) x)
      = (c₁ * (θ - a)) * deriv g θ - (c₁ * (a - a)) * deriv g a
        - ∫ x in a..θ, c₁ * deriv g x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hker1 hv_at1 hker1' hinv1
  have hIBP2 : (∫ x in θ..b, (c₂ * (b - x)) * deriv (fun s => deriv g s) x)
      = (c₂ * (b - b)) * deriv g b - (c₂ * (b - θ)) * deriv g θ
        - ∫ x in θ..b, (-c₂) * deriv g x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hker2 hv_at2 hker2' hinv2
  -- the fundamental theorem of calculus
  have hFTC1 : (∫ x in a..θ, deriv g x) = g θ - g a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hg_at1 hint1
  have hFTC2 : (∫ x in θ..b, deriv g x) = g b - g θ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hg_at2 hint2
  -- the combination
  have hkey : (∫ x in a..θ, (c₁ * (x - a)) * deriv (fun s => deriv g s) x)
        + (∫ x in θ..b, (c₂ * (b - x)) * deriv (fun s => deriv g s) x)
      = -g θ + c₁ * g a + c₂ * g b := by
    rw [hIBP1, hIBP2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hFTC1, hFTC2]
    have h1 : c₁ * (θ - a) = c₂ * (b - θ) := by
      rw [hc₁, hc₂]; field_simp
    have h2 : c₁ + c₂ = 1 := by rw [hc₁, hc₂]; field_simp; ring
    have haa : c₁ * (a - a) = 0 := by ring
    rw [h1, haa, hc₁, hc₂]
    field_simp
    ring
  calc g θ = c₁ * g a + c₂ * g b
        - ((∫ x in a..θ, (c₁ * (x - a)) * deriv (fun s => deriv g s) x)
            + (∫ x in θ..b, (c₂ * (b - x)) * deriv (fun s => deriv g s) x)) := by
        linarith [hkey]
    _ = ((b - θ) / (b - a)) * g a + ((θ - a) / (b - a)) * g b
        - (∫ t in a..θ, (((b - θ) / (b - a)) * (t - a))
            * deriv (fun s => deriv g s) t)
        - (∫ t in θ..b, (((θ - a) / (b - a)) * (b - t))
            * deriv (fun s => deriv g s) t) := by
        rw [hc₁, hc₂]
        ring_nf

/-! ## Two elementary absolute-value helpers -/

private lemma abs_add_three (x y z : ℝ) : |x + y + z| ≤ |x| + |y| + |z| := by
  calc |x + y + z| ≤ |x + y| + |z| := abs_add_le _ _
    _ ≤ (|x| + |y|) + |z| := by linarith [abs_add_le x y]
    _ = |x| + |y| + |z| := by ring

private lemma abs_sum_four_sub (x y z w : ℝ) : |x + y - z - w| ≤ |x| + |y| + |z| + |w| := by
  have h1 : x + y - z - w = x + y + -z + -w := by ring
  rw [h1]
  calc |x + y + -z + -w| ≤ |x + y| + |-z| + |-w| := abs_add_three _ _ _
    _ ≤ (|x| + |y|) + |-z| + |-w| := by linarith [abs_add_le x y]
    _ = |x| + |y| + |z| + |w| := by rw [abs_neg, abs_neg]

/-! ## The pointwise Green bound -/

/-- **Pointwise bound of a slice by its second derivative.**  If both one-sided limits of `g`
vanish and `|g''|` is integrable on `(0, π/2)`, then
`|g θ| ≤ (π/4) ∫_{Ioc 0 (π/2)} |g''|` on the interval. -/
private theorem greenBound {g : ℝ → ℝ} (hsm : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun t => |deriv (fun s => deriv g s) t|)
      (Set.Ioc 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hL : Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |g θ| ≤ (Real.pi / 4) * ∫ t in Set.Ioc 0 (Real.pi / 2),
        |deriv (fun s => deriv g s) t| := by
  intro θ hθ
  obtain ⟨hθ0, hθL⟩ := hθ
  set L : ℝ := Real.pi / 2 with hLdef
  have hLpi : L = Real.pi / 2 := hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith [Real.pi_pos]
  set M : ℝ := ∫ t in Set.Ioc 0 L, |deriv (fun s => deriv g s) t| with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun t _ => abs_nonneg _)
  -- continuity of the second derivative on the sub-intervals
  have hdg1c : ContDiffOn ℝ 1 (deriv g) (Set.Ioo 0 L) := by
    rw [hLpi]; exact hsm.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont2 : ContinuousOn (deriv (fun s => deriv g s)) (Set.Ioo 0 L) := by
    have h2 : ContDiffOn ℝ 0 (deriv (fun s => deriv g s)) (Set.Ioo 0 L) :=
      hdg1c.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact h2.continuousOn
  -- the two-boundary estimate
  have hstep : ∀ a b : ℝ, 0 < a → a < θ → θ < b → b < L →
      |g θ| ≤ |g a| + |g b| + (L / 2) * M := by
    intro a b ha haθ hθb hb
    have hsub1 : Set.uIcc a θ ⊆ Set.Ioo 0 L := by
      intro x hx
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith, by linarith⟩
      · exact ⟨by linarith, by linarith⟩
    have hsub2 : Set.uIcc θ b ⊆ Set.Ioo 0 L := by
      intro x hx
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith, by linarith⟩
      · exact ⟨by linarith, by linarith⟩
    have hid := green_identity haθ hθb hsm ha (by linarith [hb, hLpi])
    have hba : 0 < b - a := by linarith
    -- the two Green kernels are bounded by `(b-a)/4 ≤ L/4`
    have hψ1 : ∀ t ∈ Set.uIcc a θ, |(((b - θ) / (b - a)) * (t - a))| ≤ (b - a) / 4 := by
      intro t ht
      have ht' : a ≤ t ∧ t ≤ θ := by
        rw [Set.mem_uIcc] at ht
        rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, h2⟩
        · exfalso; linarith
      have hc0 : 0 ≤ (b - θ) / (b - a) := div_nonneg (by linarith) (le_of_lt hba)
      have ht0 : 0 ≤ t - a := by linarith [ht'.1]
      rw [abs_of_nonneg (mul_nonneg hc0 ht0)]
      have hAM := mul_le_sq_div_four (x := b - θ) (y := θ - a) (by linarith) (by linarith)
      have h1 : (b - θ) / (b - a) * (t - a) ≤ (b - θ) / (b - a) * (θ - a) :=
        mul_le_mul_of_nonneg_left (by linarith [ht'.2]) hc0
      have h2 : (b - θ) / (b - a) * (θ - a) ≤ (b - a) / 4 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hba]
        nlinarith [hAM]
      linarith
    have hψ2 : ∀ t ∈ Set.uIcc θ b, |(((θ - a) / (b - a)) * (b - t))| ≤ (b - a) / 4 := by
      intro t ht
      have ht' : θ ≤ t ∧ t ≤ b := by
        rw [Set.mem_uIcc] at ht
        rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, h2⟩
        · exfalso; linarith
      have hc0 : 0 ≤ (θ - a) / (b - a) := div_nonneg (by linarith) (le_of_lt hba)
      have ht0 : 0 ≤ b - t := by linarith [ht'.2]
      rw [abs_of_nonneg (mul_nonneg hc0 ht0)]
      have hAM := mul_le_sq_div_four (x := b - θ) (y := θ - a) (by linarith) (by linarith)
      have h1 : (θ - a) / (b - a) * (b - t) ≤ (θ - a) / (b - a) * (b - θ) :=
        mul_le_mul_of_nonneg_left (by linarith [ht'.1]) hc0
      have h2 : (θ - a) / (b - a) * (b - θ) ≤ (b - a) / 4 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hba]
        nlinarith [hAM]
      linarith
    -- integrability of the pieces
    have hIp1 : IntervalIntegrable
        (fun t => |(((b - θ) / (b - a)) * (t - a)) * deriv (fun s => deriv g s) t|)
        MeasureTheory.volume a θ := ((continuousOn_const.mul
          (continuousOn_id.sub continuousOn_const)).mul (hcont2.mono hsub1)).abs.intervalIntegrable
    have hIp2 : IntervalIntegrable
        (fun t => |(((θ - a) / (b - a)) * (b - t)) * deriv (fun s => deriv g s) t|)
        MeasureTheory.volume θ b := ((continuousOn_const.mul
          (continuousOn_const.sub continuousOn_id)).mul (hcont2.mono hsub2)).abs.intervalIntegrable
    have hIg1 : IntervalIntegrable (fun t => |deriv (fun s => deriv g s) t|)
        MeasureTheory.volume a θ := (hcont2.mono hsub1).abs.intervalIntegrable
    have hIg2 : IntervalIntegrable (fun t => |deriv (fun s => deriv g s) t|)
        MeasureTheory.volume θ b := (hcont2.mono hsub2).abs.intervalIntegrable
    -- the two integral bounds
    have hI1 : |∫ t in a..θ, (((b - θ) / (b - a)) * (t - a))
        * deriv (fun s => deriv g s) t| ≤ (L / 4) * M := by
      have h1 : |∫ t in a..θ, (((b - θ) / (b - a)) * (t - a))
          * deriv (fun s => deriv g s) t|
          ≤ ∫ t in a..θ, |(((b - θ) / (b - a)) * (t - a))
            * deriv (fun s => deriv g s) t| :=
        intervalIntegral.abs_integral_le_integral_abs (le_of_lt haθ)
      have h2 : (∫ t in a..θ, |(((b - θ) / (b - a)) * (t - a))
            * deriv (fun s => deriv g s) t|)
          ≤ ∫ t in a..θ, (L / 4) * |deriv (fun s => deriv g s) t| := by
        refine intervalIntegral.integral_mono_on (le_of_lt haθ) hIp1
          (hIg1.const_mul (L / 4)) (fun t ht => ?_)
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact le_trans (hψ1 t (Set.Icc_subset_uIcc ht)) (by linarith)
      have h3 : (∫ t in a..θ, (L / 4) * |deriv (fun s => deriv g s) t|)
          = (L / 4) * ∫ t in a..θ, |deriv (fun s => deriv g s) t| :=
        intervalIntegral.integral_const_mul _ _
      have h4 : (∫ t in a..θ, |deriv (fun s => deriv g s) t|) ≤ M := by
        rw [hMdef, intervalIntegral.integral_of_le (le_of_lt haθ)]
        refine MeasureTheory.setIntegral_mono_set hint
          (Filter.Eventually.of_forall fun t => abs_nonneg _) ?_
        exact Filter.Eventually.of_forall fun t ht =>
          ⟨by linarith [ht.1, ha], by linarith [ht.2, hθL]⟩
      calc |∫ t in a..θ, (((b - θ) / (b - a)) * (t - a))
            * deriv (fun s => deriv g s) t|
          ≤ ∫ t in a..θ, |(((b - θ) / (b - a)) * (t - a))
              * deriv (fun s => deriv g s) t| := h1
        _ ≤ ∫ t in a..θ, (L / 4) * |deriv (fun s => deriv g s) t| := h2
        _ = (L / 4) * ∫ t in a..θ, |deriv (fun s => deriv g s) t| := h3
        _ ≤ (L / 4) * M := mul_le_mul_of_nonneg_left h4 (by linarith)
    have hI2 : |∫ t in θ..b, (((θ - a) / (b - a)) * (b - t))
        * deriv (fun s => deriv g s) t| ≤ (L / 4) * M := by
      have h1 : |∫ t in θ..b, (((θ - a) / (b - a)) * (b - t))
          * deriv (fun s => deriv g s) t|
          ≤ ∫ t in θ..b, |(((θ - a) / (b - a)) * (b - t))
            * deriv (fun s => deriv g s) t| :=
        intervalIntegral.abs_integral_le_integral_abs (le_of_lt hθb)
      have h2 : (∫ t in θ..b, |(((θ - a) / (b - a)) * (b - t))
            * deriv (fun s => deriv g s) t|)
          ≤ ∫ t in θ..b, (L / 4) * |deriv (fun s => deriv g s) t| := by
        refine intervalIntegral.integral_mono_on (le_of_lt hθb) hIp2
          (hIg2.const_mul (L / 4)) (fun t ht => ?_)
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact le_trans (hψ2 t (Set.Icc_subset_uIcc ht)) (by linarith)
      have h3 : (∫ t in θ..b, (L / 4) * |deriv (fun s => deriv g s) t|)
          = (L / 4) * ∫ t in θ..b, |deriv (fun s => deriv g s) t| :=
        intervalIntegral.integral_const_mul _ _
      have h4 : (∫ t in θ..b, |deriv (fun s => deriv g s) t|) ≤ M := by
        rw [hMdef, intervalIntegral.integral_of_le (le_of_lt hθb)]
        refine MeasureTheory.setIntegral_mono_set hint
          (Filter.Eventually.of_forall fun t => abs_nonneg _) ?_
        exact Filter.Eventually.of_forall fun t ht =>
          ⟨by linarith [ht.1, hθ0], by linarith [ht.2, hb, hLpi]⟩
      calc |∫ t in θ..b, (((θ - a) / (b - a)) * (b - t))
            * deriv (fun s => deriv g s) t|
          ≤ ∫ t in θ..b, |(((θ - a) / (b - a)) * (b - t))
              * deriv (fun s => deriv g s) t| := h1
        _ ≤ ∫ t in θ..b, (L / 4) * |deriv (fun s => deriv g s) t| := h2
        _ = (L / 4) * ∫ t in θ..b, |deriv (fun s => deriv g s) t| := h3
        _ ≤ (L / 4) * M := mul_le_mul_of_nonneg_left h4 (by linarith)
    -- the coefficients are at most `1`
    have hcoe1 : |((b - θ) / (b - a)) * g a| ≤ |g a| := by
      rw [abs_mul]
      have hc : |(b - θ) / (b - a)| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg (by linarith) (le_of_lt hba)), div_le_one hba]
        linarith
      calc |(b - θ) / (b - a)| * |g a| ≤ 1 * |g a| := by gcongr
        _ = |g a| := one_mul _
    have hcoe2 : |((θ - a) / (b - a)) * g b| ≤ |g b| := by
      rw [abs_mul]
      have hc : |(θ - a) / (b - a)| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg (by linarith) (le_of_lt hba)), div_le_one hba]
        linarith
      calc |(θ - a) / (b - a)| * |g b| ≤ 1 * |g b| := by gcongr
        _ = |g b| := one_mul _
    rw [hid]
    have htri := abs_sum_four_sub (((b - θ) / (b - a)) * g a) (((θ - a) / (b - a)) * g b)
      (∫ t in a..θ, (((b - θ) / (b - a)) * (t - a)) * deriv (fun s => deriv g s) t)
      (∫ t in θ..b, (((θ - a) / (b - a)) * (b - t)) * deriv (fun s => deriv g s) t)
    linarith [htri, hcoe1, hcoe2, hI1, hI2]
  -- pass to the limit at the two endpoints
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨δ₁, hδ1pos, hδ1⟩ : ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ t ∈ Set.Ioo 0 δ₁, |g t| < ε / 2 := by
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), g t ∈ Metric.ball (0 : ℝ) (ε / 2) :=
      h0.eventually (Metric.ball_mem_nhds (0 : ℝ) hε2)
    have hmem : {t : ℝ | g t ∈ Metric.ball (0 : ℝ) (ε / 2)}
        ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := hev
    rw [Metric.mem_nhdsWithin_iff] at hmem
    obtain ⟨δ, hδ, hsub⟩ := hmem
    refine ⟨δ, hδ, fun t ht => ?_⟩
    have ht' : t ∈ Metric.ball (0 : ℝ) δ ∩ Set.Ioi 0 := by
      refine ⟨?_, ht.1⟩
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
      exact ht.2
    have hgt : g t ∈ Metric.ball (0 : ℝ) (ε / 2) := hsub ht'
    rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hgt
  obtain ⟨δ₂, hδ2pos, hδ2⟩ : ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ t ∈ Set.Ioo (L - δ₂) L, |g t| < ε / 2 := by
    have hev : ∀ᶠ t in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        g t ∈ Metric.ball (0 : ℝ) (ε / 2) :=
      hL.eventually (Metric.ball_mem_nhds (0 : ℝ) hε2)
    have hmem : {t : ℝ | g t ∈ Metric.ball (0 : ℝ) (ε / 2)}
        ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := hev
    rw [Metric.mem_nhdsWithin_iff] at hmem
    obtain ⟨δ, hδ, hsub⟩ := hmem
    refine ⟨δ, hδ, fun t ht => ?_⟩
    have htd : dist t (Real.pi / 2) < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith [ht.2]), neg_sub]
      linarith [ht.1]
    have ht' : t ∈ Metric.ball (Real.pi / 2) δ ∩ Set.Iio (Real.pi / 2) :=
      ⟨by rwa [Metric.mem_ball], ht.2⟩
    have hgt : g t ∈ Metric.ball (0 : ℝ) (ε / 2) := hsub ht'
    rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hgt
  set a : ℝ := min (θ / 2) (δ₁ / 2) with hadef
  set b : ℝ := L - min (δ₂ / 2) ((L - θ) / 2) with hbdef
  have ha_pos : 0 < a := by
    rw [hadef]; exact lt_min (by linarith) (by linarith)
  have haθ : a < θ := by
    rw [hadef]
    calc min (θ / 2) (δ₁ / 2) ≤ θ / 2 := min_le_left _ _
      _ < θ := by linarith
  have ha_δ : a < δ₁ := by
    rw [hadef]
    calc min (θ / 2) (δ₁ / 2) ≤ δ₁ / 2 := min_le_right _ _
      _ < δ₁ := by linarith
  have hb_L : b < L := by
    rw [hbdef]
    have : 0 < min (δ₂ / 2) ((L - θ) / 2) := lt_min (by linarith) (by linarith)
    linarith
  have hθb : θ < b := by
    rw [hbdef]
    have : min (δ₂ / 2) ((L - θ) / 2) ≤ (L - θ) / 2 := min_le_right _ _
    linarith
  have hb_δ : L - b < δ₂ := by
    rw [hbdef]
    have : min (δ₂ / 2) ((L - θ) / 2) ≤ δ₂ / 2 := min_le_left _ _
    linarith
  have hga : |g a| < ε / 2 := hδ1 a ⟨ha_pos, ha_δ⟩
  have hgb : |g b| < ε / 2 := hδ2 b ⟨by linarith, hb_L⟩
  have hmain := hstep a b ha_pos haθ hθb hb_L
  have hLM : (L / 2) * M
      = (Real.pi / 4) * ∫ t in Set.Ioc 0 (Real.pi / 2), |deriv (fun s => deriv g s) t| := by
    rw [hMdef, hLpi]
    ring
  linarith [hmain, hLM, hga, hgb]

/-- Conversion between the interval integral `∫_0^{π/2}` and the set integral over `Iθ`. -/
private lemma interval_eq_Iθ {f : ℝ → ℝ} :
    (∫ x in (0 : ℝ)..Real.pi / 2, f x) = ∫ x in Work.Spaces.Iθ, f x := by
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  show (∫ x in Set.Ioc 0 (Real.pi / 2), f x) = ∫ x in Set.Icc 0 (Real.pi / 2), f x
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume))]

/-! ## The target: the two-derivative weighted Hardy inequality -/

theorem sliceZeroLimitHardy : ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℝ,
    ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv g t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ →
    Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ENNReal.ofReal C * ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((deriv (fun t => deriv g t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
  refine ⟨10 ^ 6, by norm_num, ?_⟩
  intro g hsm hint h0 hL
  set L : ℝ := Real.pi / 2 with hLdef
  have hLpi : L = Real.pi / 2 := hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith [Real.pi_pos]
  set G2 : ℝ → ℝ := fun θ => deriv (fun t => deriv g t) θ with hG2def
  -- ## integrability of the two weights on `Ioc 0 L`
  have hsinpos : ∀ θ ∈ Set.Ioo 0 L, 0 < Real.sin (2 * θ) := by
    intro θ hθ
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) ?_
    rw [hLpi] at hθ
    linarith [hθ.2]
  have hA : MeasureTheory.IntegrableOn
      (fun θ => (G2 θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) (Set.Ioc 0 L) := by
    rw [hLpi]
    exact hint.mono_set Set.Ioc_subset_Icc_self
  have hB : MeasureTheory.IntegrableOn (fun θ => (Work.FTS.EllipticEst.sEta θ)⁻¹)
      (Set.Ioc 0 L) := by
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => Real.sin (2 * θ) ^ (Work.Spaces.eta)) (Set.Ioc 0 L) := by
      rw [hLpi]
      exact (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (p := Work.Spaces.eta)
        (by norm_num [Work.Spaces.eta])).1.mono_set Set.Ioc_subset_Icc_self
    refine h1.congr_fun (fun θ hθ => ?_) measurableSet_Ioc
    show Real.sin (2 * θ) ^ (Work.Spaces.eta) = (Work.FTS.EllipticEst.sEta θ)⁻¹
    rw [Work.FTS.EllipticEst.sEta]
    have h2θ0 : 0 ≤ 2 * θ := by rw [Set.mem_Ioc] at hθ; linarith [hθ.1]
    have h2θπ : 2 * θ ≤ Real.pi := by
      rw [Set.mem_Ioc] at hθ
      rw [hLpi] at hθ
      linarith [hθ.2]
    rw [Real.rpow_neg (Real.sin_nonneg_of_nonneg_of_le_pi h2θ0 h2θπ), inv_inv]
  -- ## `|G2|` is integrable on `Ioc 0 L`
  have hL1 : MeasureTheory.IntegrableOn (fun θ => |G2 θ|) (Set.Ioc 0 L) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun θ => (1 / 2) * ((G2 θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          + (Work.FTS.EllipticEst.sEta θ)⁻¹)) (Set.Ioc 0 L) := (hA.add hB).const_mul (1 / 2)
    refine MeasureTheory.Integrable.mono' hdom
      ((measurable_deriv (fun t : ℝ => deriv g t)).abs.aestronglyMeasurable) ?_
    have hmem : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioc 0 L)), θ ∈ Set.Ioo 0 L := by
      rw [MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Ioc (μ := MeasureTheory.volume) (a := 0) (b := L)).symm]
      exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
    filter_upwards [hmem] with θ hθ
    have hs : 0 < Work.FTS.EllipticEst.sEta θ := Real.rpow_pos_of_pos (hsinpos θ hθ) _
    rw [Real.norm_eq_abs, abs_abs]
    have hAM := two_mul_le_add_sq (|G2 θ| * Work.FTS.EllipticEst.sEta θ) (1 : ℝ)
    rw [mul_one, one_pow, mul_pow, sq_abs] at hAM
    have hkey : 2 * |G2 θ| ≤ (G2 θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (Work.FTS.EllipticEst.sEta θ)⁻¹ := by
      refine (mul_le_mul_iff_of_pos_right hs).mp ?_
      have hspos : Work.FTS.EllipticEst.sEta θ ≠ 0 := ne_of_gt hs
      have e : ((G2 θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + (Work.FTS.EllipticEst.sEta θ)⁻¹)
          * Work.FTS.EllipticEst.sEta θ
          = (G2 θ) ^ 2 * (Work.FTS.EllipticEst.sEta θ) ^ 2 + 1 := by
        rw [add_mul, inv_mul_cancel₀ hspos]
        ring
      rw [e]
      linarith [hAM]
    linarith [hkey]
  -- ## the three integrals
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, (G2 θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hAdef
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.sEta θ)⁻¹ with hBdef
  set M : ℝ := ∫ θ in Work.Spaces.Iθ, |G2 θ| with hMdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_sl hθ))
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => inv_nonneg.mpr (sEta_nonneg_sl hθ))
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => abs_nonneg _)
  have hBpi : B ≤ Real.pi / 2 := by
    rw [hBdef]
    have h2 := (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (p := Work.Spaces.eta)
      (by norm_num [Work.Spaces.eta])).2
    refine le_trans (le_of_eq ?_) h2
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [Work.FTS.EllipticEst.sEta,
      Real.rpow_neg (Work.FTS.EllipticEst.sin_two_nonneg hθ), inv_inv]
  -- ## Cauchy–Schwarz for `M`
  have hA' : MeasureTheory.IntegrableOn
      (fun s => |G2 s| ^ 2 * Work.FTS.EllipticEst.sEta s) (Set.Ioc 0 (Real.pi / 2)) := by
    have hh := hA
    rw [hLpi] at hh
    exact hh.congr_fun (fun t _ => by rw [sq_abs]) measurableSet_Ioc
  have hB' : MeasureTheory.IntegrableOn
      (fun s => (Work.FTS.EllipticEst.sEta s)⁻¹) (Set.Ioc 0 (Real.pi / 2)) := by
    have hh := hB
    rw [hLpi] at hh
    exact hh
  have hCS : M ^ 2 ≤ A * B := by
    have h := Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul
      (f := fun t => |G2 t|) (σ := Work.FTS.EllipticEst.sEta) (a := 0) (b := Real.pi / 2)
      (le_of_lt (by linarith [Real.pi_pos]))
      (fun t ht => Real.rpow_pos_of_pos
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])) _)
      hA' hB'
    rw [interval_eq_Iθ (f := fun t => |G2 t|), interval_eq_Iθ
        (f := fun t => |G2 t| ^ 2 * Work.FTS.EllipticEst.sEta t),
      interval_eq_Iθ (f := fun t => (Work.FTS.EllipticEst.sEta t)⁻¹)] at h
    rw [hMdef, hAdef, hBdef]
    simpa only [sq_abs] using h
  -- ## the pointwise bound and the lintegral chain
  have hbd := greenBound hsm hL1 h0 hL
  have hMconv : (∫ t in Set.Ioc 0 (Real.pi / 2), |G2 t|) = M := by
    rw [hMdef]
    show (∫ t in Set.Ioc 0 (Real.pi / 2), |G2 t|) = ∫ t in Work.Spaces.Iθ, |G2 t|
    rw [Work.Spaces.Iθ]
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume)).symm]
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ENNReal.ofReal (((Real.pi / 4) ^ 2 * M ^ 2) * Work.FTS.EllipticEst.sEta θ) := by
    intro θ hθ
    obtain ⟨hθ0, hθL⟩ := Set.mem_Icc.mp hθ
    refine ENNReal.ofReal_le_ofReal ?_
    rcases eq_or_lt_of_le hθ0 with h0θ | h0θ
    · rw [← h0θ, sEta_zero_left]
      simp
    rcases eq_or_lt_of_le hθL with hπθ | hπθ
    · have hz : Work.FTS.EllipticEst.sEta L = 0 := by
        rw [hLpi]; exact sEta_zero_right
      rw [hπθ, hz]
      simp
    · have hb := hbd θ ⟨h0θ, by linarith [hπθ, hLpi]⟩
      rw [hMconv] at hb
      have hs : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg_sl hθ
      have hsq : (g θ) ^ 2 ≤ ((Real.pi / 4) * M) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      calc (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
          ≤ ((Real.pi / 4) * M) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
            mul_le_mul_of_nonneg_right hsq hs
        _ = ((Real.pi / 4) ^ 2 * M ^ 2) * Work.FTS.EllipticEst.sEta θ := by ring
  have hintnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ => ((Real.pi / 4) ^ 2 * M ^ 2) * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (by positivity) (sEta_nonneg_sl hθ))
  have hintIθ : MeasureTheory.IntegrableOn
      (fun θ => ((Real.pi / 4) ^ 2 * M ^ 2) * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have := Work.FTS.EllipticEst.integrableOn_thEta.1
    exact this.const_mul _
  have hintnneg : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ => (G2 θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_sl hθ))
  calc ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (((Real.pi / 4) ^ 2 * M ^ 2) * Work.FTS.EllipticEst.sEta θ) :=
        MeasureTheory.lintegral_mono_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
    _ = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
          ((Real.pi / 4) ^ 2 * M ^ 2) * Work.FTS.EllipticEst.sEta θ) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintIθ hintnn).symm
    _ = ENNReal.ofReal (((Real.pi / 4) ^ 2 * M ^ 2)
          * ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ ENNReal.ofReal (((Real.pi / 4) ^ 2 * M ^ 2) * 10000) := by
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_left Work.FTS.EllipticEst.integrableOn_thEta.2 (by positivity)
    _ ≤ ENNReal.ofReal (10 ^ 6) * ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((G2 θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hintnneg]
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10 ^ 6)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hgoal : ((Real.pi / 4) ^ 2 * M ^ 2) * 10000 ≤ 10 ^ 6 * A := by
          have hpi4 : (Real.pi / 4) ^ 2 ≤ 1 := by nlinarith [Real.pi_pos, Real.pi_le_four]
          have hB2 : B ≤ 2 := by linarith [hBpi, Real.pi_le_four]
          have hM2' : M ^ 2 ≤ A * 2 := le_trans hCS (mul_le_mul_of_nonneg_left hB2 hA0)
          have h1 : (Real.pi / 4) ^ 2 * M ^ 2 ≤ A * 2 := by
            calc (Real.pi / 4) ^ 2 * M ^ 2 ≤ 1 * M ^ 2 :=
                  mul_le_mul_of_nonneg_right hpi4 (sq_nonneg M)
              _ = M ^ 2 := one_mul _
              _ ≤ A * 2 := hM2'
          calc ((Real.pi / 4) ^ 2 * M ^ 2) * 10000 ≤ (A * 2) * 10000 :=
                mul_le_mul_of_nonneg_right h1 (by norm_num)
            _ ≤ 10 ^ 6 * A := by nlinarith [hA0]
        simpa only [← hAdef] using hgoal

end

end Work.FTS.EllipticEst.H2W.Ae.ZeroHardy
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeW.cotFluxIdentity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeW

/-!
# The angular cot-flux identity for the weight `sin(2θ)^{-η}`

For `f : ℝ → ℝ` of class `C¹` on the open interval `(0, π/2)` and `0 < a < b < π/2`,

  `∫_a^b sin(2θ)^{-(η+2)} f²
    = (1/(4η)) ∫_a^b sin(2θ)^{-η} (f')²
      - (1/2) [ cos(2θ) sin(2θ)^{-(η+1)} f² ]_a^b
      - (1/(4η)) ∫_a^b sin(2θ)^{-η} (f' - 2η cot(2θ) f)²,  η = 99/100.

The identity is the fundamental theorem of calculus for the primitive

  `G θ = -(1/2) cos(2θ) sin(2θ)^{-(η+1)} f(θ)²`

whose derivative is `sin(2θ)^{-(η+2)} f² - K θ`, where

  `K θ = cos(2θ) sin(2θ)^{-(η+1)} f f' - η cos²(2θ) sin(2θ)^{-(η+2)} f²`

is the "flux" integrand; the *difference* of the two integrands of the right-hand side is
the pointwise identity `sin(2θ)^{-η}(f')² - sin(2θ)^{-η}(f' - 2η cot(2θ) f)² = 4η K`
(a difference of two squares), which is why no second derivative of `f` is needed.
-/













end Work.FTS.EllipticEst.H2W.AeW
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.integrableOn_sq_mul_sEta_of_bdd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W


end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonSliceLimitZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The moment identity at the left endpoint.**  Let `u` be `C²` on `(0, π/2)`, bounded there
together with `deriv u` by `C`, with `Lzero1 u · sinCos2` integrable on `Iθ` and with limit `L`
at `0⁺`.  Then

  `∫_θ (Lzero1 u)(θ) · sin θ cos²θ = -L`.

The proof integrates the primitive `Φ θ = -sinCos2 θ · u'(θ) + cos θ cos(2θ) · u(θ)` of the
integrand and evaluates the boundary terms: the one at `π/2` vanishes (the factor `cos θ`
vanishes, and `sinCos2 · u'` is a bounded function times a vanishing one) while the one at `0⁺`
is `L`; the fact that no *interior* term survives is exactly `LzeroAdj (sinCos2) = 0`. -/
theorem sliceMoment_eq_neg_limit {u : ℝ → ℝ} {C L : ℝ} (hC : 0 ≤ C)
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |u θ| ≤ C ∧ |deriv u θ| ≤ C)
    (hL : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hlim : Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    (∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) = -L := by
  -- the primitive `Φ` and the integrand `ψ`
  set ψ : ℝ → ℝ := fun θ => Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ
    with hψ
  set Φ : ℝ → ℝ := fun θ => -(Work.Elliptic.sinCos2 θ) * deriv u θ
      + Real.cos θ * Real.cos (2 * θ) * u θ with hΦ
  have hder : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt Φ (ψ θ) θ := by
    intro θ hθ
    rw [hΦ, hψ]
    exact Work.FTS.EllipticEst.remov.coerc.phi_slice_hasDerivAt hsm θ hθ
  have hpsiIcc : MeasureTheory.IntegrableOn ψ (Set.Icc 0 (Real.pi / 2)) := by
    rw [hψ]
    simpa only [Work.Spaces.Iθ] using hL
  -- `Φ` has one-sided limits at both endpoints
  obtain ⟨⟨β, hβ⟩, ⟨γ, hγ⟩⟩ :=
    Work.FTS.EllipticEst.remov.coerc.hasDerivAt_tendsto_at_ends (L := Real.pi / 2)
      (by positivity) hder hpsiIcc
  -- the "good" term `θ ↦ cos θ cos(2θ) u θ` tends to `L` at `0⁺`
  have hcosu0 : Filter.Tendsto (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ) * u θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) := by
    have hc : ContinuousAt (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ)) 0 := by fun_prop
    have h1 : Filter.Tendsto (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Real.cos 0 * Real.cos (2 * 0))) :=
      hc.continuousWithinAt
    have h2 := h1.mul hlim
    have h3 : Real.cos 0 * Real.cos (2 * 0) * L = L := by simp
    simpa [h3] using h2
  -- hence `sinCos2 θ · u'(θ) → L - β` at `0⁺`
  have hw0 : Filter.Tendsto (fun θ : ℝ => Work.Elliptic.sinCos2 θ * deriv u θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (L - β)) := by
    have hdiff : Filter.Tendsto
        (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ) * u θ - Φ θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (L - β)) := hcosu0.sub hβ
    rw [show (fun θ : ℝ => Work.Elliptic.sinCos2 θ * deriv u θ)
        = fun θ : ℝ => Real.cos θ * Real.cos (2 * θ) * u θ - Φ θ from by
      funext θ; rw [hΦ]; ring]
    exact hdiff
  -- `|sinCos2 θ| ≤ θ` near `0⁺`
  have hbound0 : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      |Work.Elliptic.sinCos2 θ| ≤ (1 : ℝ) * θ := by
    have hlt1 : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), θ < 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin, hlt1] with θ hθ hθ1
    have hθ0 : 0 < θ := hθ
    have hsin : Real.sin θ ≤ θ := Real.sin_le hθ0.le
    have hc2 : Real.cos θ ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
    rw [Work.Elliptic.sinCos2, abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ))]
    have hsinabs : |Real.sin θ| = Real.sin θ :=
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le
        (by linarith [hθ1, Real.pi_gt_three]))
    rw [hsinabs]
    calc Real.sin θ * Real.cos θ ^ 2 ≤ θ * 1 :=
          mul_le_mul hsin hc2 (sq_nonneg _) hθ0.le
      _ = 1 * θ := by ring
  -- integrability of `(u')²` on `(0, π/2)` from the bound on `u'`
  have hsq_oo : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.of_bound (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) ?_
      ?_ (C ^ 2) ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact ((measurable_deriv u).pow_const 2).aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (deriv u θ))]
      calc (deriv u θ) ^ 2 = |deriv u θ| ^ 2 := (sq_abs (deriv u θ)).symm
        _ ≤ C ^ 2 := by
            rw [pow_two, pow_two]
            exact mul_self_le_mul_self (abs_nonneg (deriv u θ)) ((hb θ hθ).2)
  have hf_int0 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) (Set.Ioo 0 1) :=
    hsq_oo.mono_set (fun θ hθ => ⟨hθ.1, by linarith [hθ.2, Real.pi_gt_three]⟩)
  have hLβ : L - β = 0 :=
    Work.FTS.EllipticEst.remov.coerc.mul_sq_vanishing (f := fun θ => deriv u θ)
      (φ := Work.Elliptic.sinCos2) (C := 1) (by norm_num) hbound0 hf_int0 hw0
  have hΦ0 : Filter.Tendsto Φ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) := by
    have hβeq : β = L := by linarith
    rw [hβeq] at hβ
    exact hβ
  -- at `(π/2)⁻`: `cos θ cos(2θ) u θ → 0` because `u` is bounded and `cos θ → 0`
  have hcosu1 : Filter.Tendsto (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ) * u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hc : Filter.Tendsto (fun θ : ℝ => |Real.cos θ|)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have hcont : ContinuousAt (fun θ : ℝ => Real.cos θ) (Real.pi / 2) :=
        Real.continuous_cos.continuousAt
      have h1 : Filter.Tendsto Real.cos
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds (Real.cos (Real.pi / 2))) := hcont.continuousWithinAt
      have h2 : Filter.Tendsto (fun θ : ℝ => |Real.cos θ|)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds |Real.cos (Real.pi / 2)|) := by
        simpa only [Real.norm_eq_abs] using h1.norm
      simpa [Real.cos_pi_div_two] using h2
    have ha : Filter.Tendsto (fun θ : ℝ => C * |Real.cos θ|)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      simpa using hc.const_mul C
    refine squeeze_zero_norm' ?_ ha
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Ioi_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2))]
      with θ hθhi hθlo
    have hbθ : |u θ| ≤ C := (hb θ ⟨hθlo, hθhi⟩).1
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hcos2 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one (2 * θ)
    calc |Real.cos θ| * |Real.cos (2 * θ)| * |u θ| ≤ |Real.cos θ| * 1 * C :=
          mul_le_mul (mul_le_mul le_rfl hcos2 (abs_nonneg _) (abs_nonneg _)) hbθ
            (abs_nonneg _) (by positivity)
      _ = C * |Real.cos θ| := by ring
  have hw1 : Filter.Tendsto (fun θ : ℝ => Work.Elliptic.sinCos2 θ * deriv u θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (0 - γ)) := by
    have hdiff : Filter.Tendsto
        (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ) * u θ - Φ θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (0 - γ)) := hcosu1.sub hγ
    rw [show (fun θ : ℝ => Work.Elliptic.sinCos2 θ * deriv u θ)
        = fun θ : ℝ => Real.cos θ * Real.cos (2 * θ) * u θ - Φ θ from by
      funext θ; rw [hΦ]; ring]
    exact hdiff
  -- `|sinCos2 θ| ≤ π/2 - θ` near `(π/2)⁻`
  have hbound1 : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      |Work.Elliptic.sinCos2 θ| ≤ (1 : ℝ) * (Real.pi / 2 - θ) := by
    have hgt : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        Real.pi / 2 - 1 < θ :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Ioi_mem_nhds (by linarith [Real.pi_gt_three] : Real.pi / 2 - 1 < Real.pi / 2))
    filter_upwards [self_mem_nhdsWithin, hgt] with θ hθ hθ1
    have hθlt : θ < Real.pi / 2 := hθ
    have ht : 0 < Real.pi / 2 - θ := by linarith
    have ht1 : Real.pi / 2 - θ ≤ 1 := by linarith
    have hcos : Real.cos θ = Real.sin (Real.pi / 2 - θ) := (Real.sin_pi_div_two_sub θ).symm
    have hsin_le1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hsin_nn : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ1, Real.pi_gt_three])
        (by linarith [hθlt, Real.pi_pos])
    rw [Work.Elliptic.sinCos2, abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ))]
    rw [abs_of_nonneg hsin_nn]
    have h2 : Real.cos θ ^ 2 = Real.sin (Real.pi / 2 - θ) ^ 2 := by rw [hcos]
    have hsin_le : Real.sin (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := Real.sin_le ht.le
    have hsin_nn2 : 0 ≤ Real.sin (Real.pi / 2 - θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht.le (by linarith [hθ1, Real.pi_gt_three])
    have h3 : Real.sin (Real.pi / 2 - θ) ^ 2 ≤ (Real.pi / 2 - θ) ^ 2 := by
      nlinarith [hsin_le, hsin_nn2]
    have h4 : (Real.pi / 2 - θ) ^ 2 ≤ Real.pi / 2 - θ := by nlinarith [ht, ht1]
    have h5 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 * Real.sin (Real.pi / 2 - θ) ^ 2 := by
      rw [h2]
      exact mul_le_mul hsin_le1 le_rfl (sq_nonneg _) zero_le_one
    calc Real.sin θ * Real.cos θ ^ 2 ≤ 1 * Real.sin (Real.pi / 2 - θ) ^ 2 := h5
      _ ≤ 1 * (Real.pi / 2 - θ) ^ 2 := by linarith
      _ ≤ 1 * (Real.pi / 2 - θ) := by linarith
  have hf_int1 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2)
      (Set.Ioo (Real.pi / 2 - 1) (Real.pi / 2)) :=
    hsq_oo.mono_set (fun θ hθ => ⟨by linarith [hθ.1, Real.pi_gt_three], hθ.2⟩)
  have hγ0 : 0 - γ = 0 :=
    Work.FTS.EllipticEst.remov.coerc.mul_sq_vanishing_right (f := fun θ => deriv u θ)
      (φ := Work.Elliptic.sinCos2) (b := Real.pi / 2) (C := 1) (by norm_num)
      hbound1 hf_int1 hw1
  have hΦ1 : Filter.Tendsto Φ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hγeq : γ = 0 := by linarith
    rw [hγeq] at hγ
    exact hγ
  -- the fundamental theorem of calculus on `0..π/2`
  have hInt : IntervalIntegrable ψ volume 0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact hpsiIcc.mono_set Set.Ioc_subset_Icc_self
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (a := (0 : ℝ)) (b := Real.pi / 2) (f := Φ) (f' := ψ)
    (by positivity : (0 : ℝ) < Real.pi / 2) hder hInt hΦ0 hΦ1
  have hmain : (∫ θ in Work.Spaces.Iθ, ψ θ) = -L := by
    have h1 : (∫ θ in Work.Spaces.Iθ, ψ θ) = ∫ y in (0 : ℝ)..Real.pi / 2, ψ y := by
      rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2),
        Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [h1, hFTC]; ring
  rwa [hψ] at hmain


end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.LopIterSinSqDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-- The coefficient recursion attached to `L = sin(2θ) ∂_θ` and the special function
`sin(2θ)²`:  `gfun 0 = 1` and
`gfun (i+1) θ = 4 cos(2θ) gfun i θ + sin(2θ) · deriv (gfun i) θ`, so that (see
`LopIter_sin_sq_factor`) one has `L^i (sin(2θ)²) = fun θ => sin(2θ)² · gfun i θ`. -/
noncomputable def gfun : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | (n + 1) => fun θ => 4 * Real.cos (2 * θ) * gfun n θ
      + Real.sin (2 * θ) * deriv (gfun n) θ

@[simp] theorem gfun_zero : gfun 0 = fun _ : ℝ => 1 := rfl

@[simp] theorem gfun_succ (n : ℕ) :
    gfun (n + 1) = fun θ => 4 * Real.cos (2 * θ) * gfun n θ
      + Real.sin (2 * θ) * deriv (gfun n) θ := rfl

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Lop_iter_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped ContDiff

namespace Work.FTS.EllipticEst

/-- The iterated Leibniz rule for the angular operator `L = D_θ = sin(2θ) ∂_θ` (here
`LopIter i f = (L^i) f = (Work.Spaces.Lop^[i]) f`): for `f`, `g` smooth at `θ`,

`L^i (f * g) θ = ∑_{a ≤ i} C(i,a) · (L^a f θ) · (L^{i-a} g θ)`.

Proof route: this is the pointwise specialisation of the already available
`Work.Spaces.Lop_iter_mul_eqOn` (in `Submission/Work/Spaces/DthIter_mul.lean`), which gives the
identity as a `Set.EqOn` on any open set where `f` and `g` are `C^∞`; `ContDiffAt ℝ ⊤ f θ`
supplies such an open neighbourhood.  (Alternatively: induction using `Work.Spaces.Lop_mul` and
`Work.Spaces.leibniz_step`.) -/
theorem Lop_iter_mul {f g : ℝ → ℝ} {i : ℕ} {θ : ℝ} (hf : ContDiffAt ℝ ⊤ f θ)
    (hg : ContDiffAt ℝ ⊤ g θ) :
    Work.FTS.EllipticEst.LopIter i (f * g) θ = ∑ a ∈ Finset.range (i + 1),
      (i.choose a : ℝ) * (Work.FTS.EllipticEst.LopIter a f θ)
        * (Work.FTS.EllipticEst.LopIter (i - a) g θ) := by
  -- `ContDiffAt ℝ ⊤ f θ` = analytic at `θ`, hence `C^∞` on an open neighbourhood of `θ`
  -- (the neighbourhood being reasonably shrunk so that both `f` and `g` qualify).
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (le_refl (⊤ : ℕ∞ω))
    (fun h => absurd h (ne_of_gt (WithTop.coe_lt_top (⊤ : ℕ∞))))
  obtain ⟨v, hv, hgv⟩ := hg.contDiffOn (le_refl (⊤ : ℕ∞ω))
    (fun h => absurd h (ne_of_gt (WithTop.coe_lt_top (⊤ : ℕ∞))))
  obtain ⟨W, hWU, hWopen, hθW⟩ := mem_nhds_iff.mp (Filter.inter_mem hu hv)
  -- the iterated Leibniz rule on the open set `W`
  have hmain := Work.Spaces.Lop_iter_mul_eqOn f g W hWopen
    (hfu.mono (fun x hx => (hWU hx).1)) (hgv.mono (fun x hx => (hWU hx).2)) i hθW
  simp only [Work.FTS.EllipticEst.LopIter]
  rw [hmain]
  apply Finset.sum_congr rfl
  intro a ha
  ring

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.SlicePoincare =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Elementary facts about the angular weight `sEta θ = sin(2θ)^{-η}`

The weight is `≥ 0` on the slice `Iθ = [0,π/2]`, and `≥ 1` on the open interval `(0,π/2)`
(because `0 < sin(2θ) ≤ 1` and the exponent `-η` is nonpositive). -/

theorem sp_sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  apply Real.rpow_nonneg
  apply Real.sin_nonneg_of_nonneg_of_le_pi (x := 2 * θ) (by linarith [hθ.1])
  linarith [hθ.2, Real.pi_pos]


/-! ## The derivative Poincaré inequality

This is the main step: a function `u` of class `C²` on `(0,π/2)`, continuous on `[0,π/2]`,
vanishing at both endpoints, satisfies `∫ (u')² ≤ (π/2)² ∫ (u'')² σ`.

The proof is the *two-point* (Rolle) form of the Hardy/Poincaré argument: Rolle gives an
interior point `θ₀` with `u'(θ₀) = 0`; the fundamental theorem of calculus on the interior
interval between `θ₀` and `θ` gives `u'(θ) = ∫_{θ₀}^{θ} u''`, and Cauchy–Schwarz against the
weight `σ^{-1} = sin(2θ)^{η} ≤ 1` bounds the last integral by `(π/2) ∫ (u'')² σ` uniformly in
`θ`.  Integrating the resulting *pointwise* bound over `(0,π/2)` (a set of measure `π/2`)
gives the claim. -/

theorem slice_deriv_sq_le {u : ℝ → ℝ}
    (hC : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (h0 : u 0 = 0) (hpi : u (Real.pi / 2) = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 2 *
          (∫ θ in Work.Spaces.Iθ,
            (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  set R : ℝ := ∫ θ in Work.Spaces.Iθ,
    (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hRdef
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  -- ## continuity of the two derivatives on the open interval
  have hdC1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hC.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont_d : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hC.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont_g : ContinuousOn (deriv (deriv u)) (Set.Ioo 0 (Real.pi / 2)) :=
    hdC1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hderiv_has : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (deriv u) x) x := by
    intro x hx
    exact (((hdC1.differentiableOn (by norm_num)).differentiableAt
      (Ioo_mem_nhds hx.1 hx.2))).hasDerivAt
  -- ## `R ≥ 0`: the integrand is a product of nonnegative factors on `Iθ`
  have hRnn : 0 ≤ R := by
    rw [hRdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (sp_sEta_nonneg hθ)
  -- ## Rolle: an interior critical point of `u`
  obtain ⟨θ₀, hθ₀S, hθ₀d⟩ := exists_deriv_eq_zero hpi2 hcont (by rw [h0, hpi])
  -- ## the intervals between two interior points are contained in `(0,π/2)`
  have hsub : ∀ ⦃a b : ℝ⦄, a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun a b ha hb x hx =>
      ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩
  have hsubIoo : ∀ ⦃a b : ℝ⦄, a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun a b ha hb x hx => ⟨lt_trans ha.1 hx.1, lt_trans hx.2 hb.2⟩
  -- ## the fundamental theorem of calculus on the interior interval between `θ₀` and `θ`
  have hFTC : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv u θ - deriv u θ₀ = ∫ x in θ₀..θ, deriv (deriv u) x := by
    intro θ hθ
    rcases le_total θ₀ θ with hle | hle
    · have hcs : ContinuousOn (deriv u) (Set.Icc θ₀ θ) :=
        hcont_d.mono (hsub hθ₀S hθ)
      have hder : ∀ x ∈ Set.Ioo θ₀ θ, HasDerivAt (deriv u) (deriv (deriv u) x) x :=
        fun x hx => hderiv_has x (hsubIoo hθ₀S hθ hx)
      have hi : IntervalIntegrable (deriv (deriv u)) volume θ₀ θ :=
        (hcont_g.mono (hsub hθ₀S hθ)).intervalIntegrable_of_Icc hle
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcs hder hi).symm
    · have hcs : ContinuousOn (deriv u) (Set.Icc θ θ₀) :=
        hcont_d.mono (hsub hθ hθ₀S)
      have hder : ∀ x ∈ Set.Ioo θ θ₀, HasDerivAt (deriv u) (deriv (deriv u) x) x :=
        fun x hx => hderiv_has x (hsubIoo hθ hθ₀S hx)
      have hi : IntervalIntegrable (deriv (deriv u)) volume θ θ₀ :=
        (hcont_g.mono (hsub hθ hθ₀S)).intervalIntegrable_of_Icc hle
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcs hder hi
      rw [intervalIntegral.integral_symm θ θ₀, h]
      ring
  -- ## the pointwise bound `(u' θ)² ≤ (π/2) · R`
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2 ≤ (Real.pi / 2) * R := by
    intro θ hθ
    have h1 : deriv u θ - deriv u θ₀ = ∫ x in θ₀..θ, deriv (deriv u) x := hFTC θ hθ
    have h2 : (deriv u θ) ^ 2 = (∫ x in θ₀..θ, deriv (deriv u) x) ^ 2 := by
      rw [← h1, hθ₀d]; ring
    have ha : 0 ≤ min θ₀ θ := le_min (le_of_lt hθ₀S.1) (le_of_lt hθ.1)
    have hb : max θ₀ θ ≤ Real.pi / 2 := max_le (le_of_lt hθ₀S.2) (le_of_lt hθ.2)
    have hab : min θ₀ θ ≤ max θ₀ θ := min_le_max
    have hcs := cs_interval_le hcont_g hint (a := min θ₀ θ)
      (b := max θ₀ θ) ha hb hab
    rw [h2, hRdef]
    rcases le_total θ₀ θ with hle | hle
    · rwa [min_eq_left hle, max_eq_right hle] at hcs
    · rw [min_eq_right hle, max_eq_left hle] at hcs
      rw [intervalIntegral.integral_symm θ θ₀, neg_sq]
      exact hcs
  -- ## integrability on the open interval `(0,π/2)` (finite measure, bounded integrand)
  have hvolS : (volume : Measure ℝ).real (Set.Ioo (0 : ℝ) (Real.pi / 2)) = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Ioo, sub_zero,
      ENNReal.toReal_ofReal (by positivity)]
  have hint_fin : IsFiniteMeasure (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  have hmeas : AEStronglyMeasurable (fun θ => (deriv u θ) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (hcont_d.aestronglyMeasurable isOpen_Ioo.measurableSet).pow 2
  have hptS : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      (deriv u θ) ^ 2 ≤ (Real.pi / 2) * R :=
    (ae_restrict_iff' isOpen_Ioo.measurableSet).mpr (Eventually.of_forall hpt)
  have hIntS : IntegrableOn (fun θ => (deriv u θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (integrable_const ((Real.pi / 2) * R)).mono' hmeas
      (hptS.mono fun θ hθ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hθ)
  -- ## transfer to `Iθ = [0,π/2]`, which differs from `(0,π/2)` by a null set
  have hpairab : ∀ᵐ x : ℝ, x ∉ ({(0 : ℝ), Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using
      Set.Finite.measure_zero (by simp) MeasureTheory.volume
  have haeeq : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume]
      Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    filter_upwards [hpairab] with x hx
    refine propext ⟨?_, ?_⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc] at h
      rw [Set.mem_Ioo]
      exact ⟨lt_of_le_of_ne h.1 (fun hc => hx (Or.inl hc.symm)),
             lt_of_le_of_ne h.2 (fun hc => hx (Or.inr hc))⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      rw [Set.mem_Ioo] at h
      exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  refine ⟨hIntS.congr_set_ae haeeq, ?_⟩
  have hmono : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2)
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ((Real.pi / 2) * R) :=
    integral_mono_ae hIntS (integrable_const _) hptS
  calc (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2 :=
        MeasureTheory.setIntegral_congr_set haeeq
    _ ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ((Real.pi / 2) * R) := hmono
    _ = (Real.pi / 2) * ((Real.pi / 2) * R) := by
        rw [MeasureTheory.setIntegral_const, hvolS]
        simp
    _ = (Real.pi / 2) ^ 2 * R := by ring

theorem SlicePoincare : ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ → ℝ,
    ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) →
    ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
    u 0 = 0 → u (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
      ≤ K * (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) ∧
    (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
      ≤ K * (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  refine ⟨(Real.pi / 2) ^ 4, by positivity, fun u hC hcont h0 hpi hint => ?_⟩
  obtain ⟨hInt1, hb1⟩ := slice_deriv_sq_le hC hcont h0 hpi hint
  obtain ⟨hInt2, hb2⟩ := slice_u_sq_le hC hcont h0 hInt1
  -- `R ≥ 0` for the integral against `sEta`
  have hRnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (sp_sEta_nonneg hθ)
  refine ⟨hInt1, hInt2, ?_, ?_⟩
  · calc (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := hb1
      _ ≤ (Real.pi / 2) ^ 4 *
            (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
          apply mul_le_mul_of_nonneg_right _ hRnn
          nlinarith [Real.pi_gt_three, sq_nonneg ((Real.pi / 2) ^ 2 - 1)]
  · calc (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 2 * (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) := hb2
      _ ≤ (Real.pi / 2) ^ 2 * ((Real.pi / 2) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
          mul_le_mul_of_nonneg_left hb1 (by positivity)
      _ = (Real.pi / 2) ^ 4 *
            (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by ring

end Work.FTS.EllipticEst.Mine
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.Support.integrableOn_of_mul_thEta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine.Support

open MeasureTheory

/-- **Removing the angular weight `sin(2θ)^{-η}`.**  If `f` is continuous and nonnegative on
`(0, π/2)` and `f · thEta` is integrable on `Iθ = [0, π/2]` (where
`thEta θ = sin(2θ)^{-η}`, `η = 99/100`), then `f` is integrable on `Iθ` (with an honest, non-junk
integral) and `∫_{Iθ} f ≤ ∫_{Iθ} f · thEta`, because `thEta ≥ 1` on `(0,π/2)` while `{0, π/2}` is
null.  Route: `Integrable.mono'` with `g := f * thEta` on `volume.restrict Iθ`, using
`ContinuousOn.aestronglyMeasurable` transported from the measurable set `Ioo 0 (π/2)` (a.e. equal to
`Iθ`), and `setIntegral_mono_ae` for the integral comparison. -/
theorem integrableOn_of_mul_thEta {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)))
    (hnn : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ f θ)
    (h : MeasureTheory.IntegrableOn (fun θ => f θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn f Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, f θ)
        ≤ ∫ θ in Work.Spaces.Iθ, f θ * Work.FTS.EllipticEst.thEta θ := by
  -- `(0, π/2)` and `Iθ = [0, π/2]` differ by the null set `{0, π/2}`, so they carry the same
  -- restricted measure.
  have hIoo_eq : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc
  have hres : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set hIoo_eq
  -- `thEta ≥ 1` on `(0, π/2)`.
  have hone : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      1 ≤ Work.FTS.EllipticEst.thEta θ := by
    intro θ hθ
    have h1 : 0 < Real.sin (2 * θ) := Work.FTS.EllipticEst.sin_two_pos hθ
    have h2 : Real.sin (2 * θ) ≤ 1 := Work.FTS.EllipticEst.sin_two_le_one θ
    have h3 : (Real.sin (2 * θ)) ^ (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Real.rpow_le_rpow_of_exponent_ge h1 h2 (by linarith [Work.Spaces.eta_nonneg])
    simpa [Work.FTS.EllipticEst.thEta, Real.rpow_zero] using h3
  -- A.e. strong measurability of `f`, transported from the open interval.
  have haesm : AEStronglyMeasurable f (volume.restrict Work.Spaces.Iθ) := by
    rw [← hres]
    exact hf.aestronglyMeasurable measurableSet_Ioo
  -- The a.e. domination `‖f‖ ≤ f · thEta`.
  have hbound : ∀ᵐ θ ∂volume.restrict Work.Spaces.Iθ,
      ‖f θ‖ ≤ f θ * Work.FTS.EllipticEst.thEta θ := by
    rw [← hres]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hfθ : 0 ≤ f θ := hnn θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg hfθ]
    exact le_mul_of_one_le_right hfθ (hone θ hθ)
  have hf_int : Integrable f (volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Integrable.mono' h haesm hbound
  -- The a.e. comparison `f ≤ f · thEta` for the integrals.
  have hle_ae : f ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => f θ * Work.FTS.EllipticEst.thEta θ) := by
    rw [← hres]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hfθ : 0 ≤ f θ := hnn θ hθ
    exact le_mul_of_one_le_right hfθ (hone θ hθ)
  exact ⟨hf_int, MeasureTheory.setIntegral_mono_ae_restrict hf_int h hle_ae⟩

end Work.FTS.EllipticEst.Mine.Support
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.TraceDefs =====
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

/-- The fixed cutoff `χ(θ) = smoothTransition (2θ - 1)`: it is `0` for `θ ≤ 1/2` and `1` for
`θ ≥ 1`. -/
def chi (θ : ℝ) : ℝ := Real.smoothTransition (2 * θ - 1)

/-- `χ` is of class `C^n` for every `n`. -/
theorem chi_contDiff (n : ℕ) : ContDiff ℝ n chi := by
  have h1 : ContDiff ℝ n Real.smoothTransition :=
    Real.smoothTransition.contDiff (n := (n : ℕ∞))
  have h2 : ContDiff ℝ n (fun θ : ℝ => 2 * θ - 1) := by fun_prop
  exact h1.comp h2


/-- `χ` vanishes on `(-∞, 1/2]`. -/
theorem chi_zero {θ : ℝ} (h : θ ≤ 1 / 2) : chi θ = 0 := by
  rw [chi, Real.smoothTransition.zero_of_nonpos (by linarith)]


/-- `χ` is nonnegative. -/
theorem chi_nonneg (θ : ℝ) : 0 ≤ chi θ := Real.smoothTransition.nonneg _

/-- `χ` is bounded by `1`. -/
theorem chi_le_one (θ : ℝ) : chi θ ≤ 1 := Real.smoothTransition.le_one _




end Work.FTS.EllipticEst.Prop
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.TraceLeftPieces.plainIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop.TraceLeftPieces

set_option autoImplicit false

/-- On the open angular interval `(0, π/2)` the angular weight `sin(2θ)^{-η}` is `≥ 1`,
because `sin(2θ) ∈ (0,1]` there and the exponent `-η` is `≤ 0`. -/
private lemma one_le_thEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  have hpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hη : -(Work.Spaces.eta) ≤ 0 := by
    have := Work.Spaces.eta_pos
    linarith
  have h := Real.rpow_le_rpow_of_exponent_ge (x := Real.sin (2 * θ)) (y := 0)
    (z := -(Work.Spaces.eta)) hpos hle hη
  simpa [Work.FTS.EllipticEst.thEta] using h




end Work.FTS.EllipticEst.Prop.TraceLeftPieces
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.RPFresh

open MeasureTheory Set intervalIntegral
open scoped Real Topology

set_option autoImplicit false

/-- The angular weight `σ θ = sin(2θ)^{-η}` (`η = 99/100`); definitionally `thEta`. -/
noncomputable def sg (θ : ℝ) : ℝ := (Real.sin (2*θ))^(-(Work.Spaces.eta))



theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2*θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem sg_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sg θ :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _



end Work.FTS.EllipticEst.RPFresh
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TanTheta.Defs =====
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
set_option linter.unusedSimpArgs false


/-- The product weight `Wg z θ = w z / sin(2θ)^{η/2}` of the statement of `tanTheta_bound`. -/
abbrev Wg (z θ : ℝ) : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)

/-- The coefficient `Acoef θ = ((1-η)/2)·cos 2θ + 2 sin²θ` of the `I₄`-identity.  It is
positive, and dominates `((1-η)/2)·sin²θ`. -/
def Acoef (θ : ℝ) : ℝ :=
  ((1 - Work.Spaces.eta) / 2) * Real.cos (2 * θ) + 2 * (Real.sin θ) ^ 2








theorem one_sub_eta_pos : 0 < 1 - Work.Spaces.eta := by
  rw [Work.Spaces.eta]; norm_num


end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Baux.angV_ident =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `k`-th angular identity in the divided-profile variable `v = u / cos θ`

`Work.FTS.EllipticEst.remov.Lzero1_iteratedDeriv_eq` expands the `k`-fold derivative of the
slice ODE `Lzero1 u = g` as the Leibniz expansion of `∂_θ^{k+1}(tan θ · u)`:

`u^{(k+2)} = ∑_{i≤k+1} C(k+1,i) (tan)^{(i)} u^{(k+1-i)} - 6 u^{(k)} - g^{(k)}`.

The present lemma is the same statement with the *product written in the `v`-variable*:
because `tan θ · u θ = sin θ · v θ` on `(0, π/2)` (where `v = sv u = u / cos θ`), the Leibniz
expansion of `∂_θ^{k+1}(tan θ · u)` equals that of `∂_θ^{k+1}(sin θ · v)`, and the latter is
`∑_{j≤k+1} C(k+1,j) (sin)^{(k+1-j)} v^{(j)}`.  Since the two products agree on an *open*
interval, the congruence is `Set.EqOn.iteratedDeriv_of_isOpen` — no extra regularity beyond
`C^{k+2}` of `u` is needed (the differentiability of `v = u/cos` on the interval is automatic).

This is the form in which the angular coercivity estimate consumes the ODE, the derivative
`u^{(k+2)}` on the left being replaced by the top-order term in `v` plus lower order terms.
-/

open scoped Real Topology

namespace Work.FTS.EllipticEst.remov.Baux

/-- The `k`-th derivative of the slice ODE `Lzero1 u = g`, with the product `tan θ · u`
rewritten as `sin θ · v`, `v = u / cos θ`. -/
theorem angV_ident (k : ℕ) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      iteratedDeriv (k + 2) u θ
        = (∑ j ∈ Finset.range (k + 2), ((k + 1).choose j : ℝ)
              * iteratedDeriv (k + 1 - j) Real.sin θ * iteratedDeriv j (sv u) θ)
          - 6 * iteratedDeriv k u θ - iteratedDeriv k g θ := by
  intro θ hθ
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  -- regularity at `θ`: `u` is `C^{k+1}` there, hence so is `v = u / cos`
  have huk2 : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞) u θ := hu.contDiffAt (hU.mem_nhds hθ)
  have huk1 : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) u θ :=
    huk2.of_le (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
  have htan : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) Real.tan θ :=
    (Real.contDiffAt_tan (n := ((k + 1 : ℕ) : WithTop ℕ∞))).mpr hcos
  have hsin : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) Real.sin θ := Real.contDiff_sin.contDiffAt
  have hsv : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (sv u) θ :=
    huk1.div (Real.contDiff_cos.contDiffAt) hcos
  -- Leibniz for the two products
  have hA : iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
      = ∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ)
          * iteratedDeriv i Real.tan θ * iteratedDeriv (k + 1 - i) u θ :=
    iteratedDeriv_mul htan huk1
  have hB : iteratedDeriv (k + 1) (fun t => sv u t * Real.sin t) θ
      = ∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ)
          * iteratedDeriv i (sv u) θ * iteratedDeriv (k + 1 - i) Real.sin θ :=
    iteratedDeriv_mul hsv hsin
  -- the two products agree on the (open) interval
  have hEqOn : Set.EqOn (fun t => Real.tan t * u t) (fun t => sv u t * Real.sin t)
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro t ht
    have hc : Real.cos t ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
    show Real.tan t * u t = sv u t * Real.sin t
    rw [Real.tan_eq_sin_div_cos]
    simp only [sv]
    field_simp
  have hEq : iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
      = iteratedDeriv (k + 1) (fun t => sv u t * Real.sin t) θ :=
    Set.EqOn.iteratedDeriv_of_isOpen hEqOn hU (k + 1) hθ
  -- hence the two Leibniz expansions coincide (only the order of the last two factors differs)
  have hsum : (∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ)
        * iteratedDeriv i Real.tan θ * iteratedDeriv (k + 1 - i) u θ)
      = ∑ j ∈ Finset.range (k + 2), ((k + 1).choose j : ℝ)
          * iteratedDeriv (k + 1 - j) Real.sin θ * iteratedDeriv j (sv u) θ := by
    rw [← hA, hEq, hB]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [Work.FTS.EllipticEst.remov.Lzero1_iteratedDeriv_eq k hu hg θ hθ, hsum]

end Work.FTS.EllipticEst.remov.Baux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.HardyFin.PrimitiveFin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The finite-order primitive form of `∂_x^k (f/x)`

Finite-order version of `Work.FTS.H2.DivQ.divSinPrimitive`: with `f` of class `C^N` on `(0,x₁]`
for a *finite* `N ≥ k+2`, `f → 0` at `0⁺` and `∫_0^{x₁} x^{2k-γ}(f^{(k+1)})² < ∞` (`γ > -1`), we
get the primitive identity `x^{k+1}(f/x)^{(k)}(x) = ∫_0^x s^k f^{(k+1)}(s) ds` and the boundary
control `x^{2k+1-γ}((f/x)^{(k)}(x))² ≤ (1+γ)^{-1}∫_0^x s^{2k-γ}(f^{(k+1)})²`, both on `(0,x₁)`.
-/

namespace Work.FTS.EllipticEst.remov.HardyFin

open MeasureTheory Set Filter
open scoped Topology

/-- `V_j(x) = x^{j+1}·∂_x^j (f/x)(x)`, the family whose derivative is `x^j f^{(j+1)}`. -/
private noncomputable def finV (f : ℝ → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  x ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) x

theorem divSinPrimitive_fin (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ) (N : ℕ)
    (hN : k + 2 ≤ N) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) f (Set.Ioc 0 x₁) →
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
  have hfA : ContDiffOn ℝ (((k + 2 : ℕ)) : WithTop ℕ∞) f (Set.Ioc 0 x₁) :=
    hf.of_le (by exact_mod_cast hN)
  obtain ⟨hVd, hVr⟩ := divSinPrimitiveDeriv_fin x₁ hx₁ k f hfA
  obtain ⟨hψint, hGcont, hGd⟩ := primitiveDerivData_fin k γ x₁ hx₁ hγ f hf (by omega) hint
  have hGt : Filter.Tendsto (fun u : ℝ => ∫ s in (0 : ℝ)..u, s ^ k * iteratedDeriv (k + 1) f s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := Work.FTS.H2.DivQ.hardyIter_tendsto_zero hx₁ hψint
    refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (intervalIntegral.integral_of_le hδ.le).symm
  have hvan : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      Filter.Tendsto (fun x : ℝ => x ^ j * iteratedDeriv j f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    divSinPrimitiveVanish_fin k γ x₁ hx₁ hγ N (by omega) f hf hint
  have hVd' : ∀ (j : ℕ) (x : ℝ), j ≤ k → x ∈ Set.Ioo 0 x₁ →
      HasDerivAt (finV f j) (x ^ j * iteratedDeriv (j + 1) f x) x := by
    intro j x hj hx
    change HasDerivAt (fun t : ℝ => t ^ (j + 1) * iteratedDeriv j (fun y : ℝ => f y / y) t)
      (x ^ j * iteratedDeriv (j + 1) f x) x
    exact hVd j x hj hx
  have hVr' : ∀ (j : ℕ) (y : ℝ), j + 1 ≤ k → y ∈ Set.Ioo 0 x₁ →
      finV f (j + 1) y = y ^ (j + 1) * iteratedDeriv (j + 1) f y - (j + 1) * finV f j y := by
    intro j y hj hy
    have h := hVr j y (by omega) hy
    have hgoal : finV f (j + 1) y
        = y ^ (j + 2) * iteratedDeriv (j + 1) (fun y : ℝ => f y / y) y := by
      simp only [finV]
    rw [hgoal, h]
    simp only [finV]
  -- the vanishings kill the boundary term
  have hVtend : ∀ j ≤ k,
      Filter.Tendsto (finV f j) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hEq : finV f 0 =ᶠ[nhdsWithin 0 (Set.Ioi 0)] f := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [finV, iteratedDeriv_zero, Nat.zero_add, pow_one]
        rw [mul_comm x (f x / x), div_mul_cancel₀ (f x) (ne_of_gt hx)]
      exact hf0.congr' hEq.symm
    | succ n ih =>
      intro hn
      have hn' : n ≤ k := by omega
      have h1 : Filter.Tendsto (fun y : ℝ => y ^ (n + 1) * iteratedDeriv (n + 1) f y)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := hvan (n + 1) (by omega) hn
      have h2 : Filter.Tendsto (fun y : ℝ => (n + 1) * finV f n y)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have h := (ih hn').const_mul ((n + 1 : ℕ) : ℝ)
        simpa using h
      have h3 := h1.sub h2
      have hstep : finV f (n + 1) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          fun y : ℝ => y ^ (n + 1) * iteratedDeriv (n + 1) f y - (n + 1) * finV f n y := by
        filter_upwards [Ioo_mem_nhdsGT hx₁] with y hy
        exact hVr' n y hn hy
      simpa using h3.congr' hstep.symm
  have hVk : Filter.Tendsto (finV f k) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := hVtend k le_rfl
  -- the identity
  have hVg : ∀ x ∈ Set.Ioo (0 : ℝ) x₁, finV f k x
      = ∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s := by
    have ha : x₁ / 2 ∈ Set.Ioo (0 : ℝ) x₁ := ⟨by linarith, by linarith⟩
    have hconst : ∀ x ∈ Set.Ioo (0 : ℝ) x₁,
        finV f k x - (∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s)
          = finV f k (x₁ / 2)
            - (∫ s in (0 : ℝ)..(x₁ / 2), s ^ k * iteratedDeriv (k + 1) f s) := by
      intro x hx
      have hder : ∀ y ∈ Set.uIcc (x₁ / 2) x,
          HasDerivAt (fun z : ℝ => finV f k z
            - (∫ s in (0 : ℝ)..z, s ^ k * iteratedDeriv (k + 1) f s)) 0 y := by
        intro y hy
        have hyI : y ∈ Set.Ioo (0 : ℝ) x₁ := by
          rw [Set.mem_uIcc] at hy
          rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨lt_of_lt_of_le (by linarith) h1, lt_of_le_of_lt h2 hx.2⟩
          · exact ⟨lt_of_lt_of_le hx.1 h1, lt_of_le_of_lt h2 (by linarith)⟩
        have h := (hVd' k y le_rfl hyI).sub (hGd y hyI)
        rw [sub_self] at h
        change HasDerivAt (fun z : ℝ => finV f k z
          - (∫ s in (0 : ℝ)..z, s ^ k * iteratedDeriv (k + 1) f s)) 0 y
        exact h
      have hint0 : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (x₁ / 2) x :=
        intervalIntegrable_const
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint0
      simp only [intervalIntegral.integral_const, smul_eq_mul] at hftc
      linarith
    have hlim : Filter.Tendsto (fun x : ℝ => finV f k x
        - (∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 - 0)) := hVk.sub hGt
    have hlimc : Filter.Tendsto (fun x : ℝ => finV f k x
        - (∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (finV f k (x₁ / 2)
          - (∫ s in (0 : ℝ)..(x₁ / 2), s ^ k * iteratedDeriv (k + 1) f s))) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hx₁] with x hx
      exact (hconst x hx).symm
    have hzero : finV f k (x₁ / 2)
        - (∫ s in (0 : ℝ)..(x₁ / 2), s ^ k * iteratedDeriv (k + 1) f s) = 0 := by
      have h := tendsto_nhds_unique hlim hlimc
      linarith
    intro x hx
    have h := hconst x hx
    linarith
  refine ⟨?_, ?_⟩
  · intro x hx
    simpa [finV] using hVg x hx
  · intro x hx
    set A : ℝ := iteratedDeriv k (fun y : ℝ => f y / y) x with hA
    set J : ℝ := ∫ s in (0 : ℝ)..x, s ^ k * iteratedDeriv (k + 1) f s with hJ
    set I0 : ℝ := ∫ s in (0 : ℝ)..x,
      s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2 with hI0
    have hx0 : 0 < x := hx.1
    have hxle : x ≤ x₁ := le_of_lt hx.2
    have hId : x ^ (k + 1) * A = J := by
      rw [hA, hJ]
      simpa [finV] using hVg x hx
    have hi1 : MeasureTheory.IntegrableOn (fun s : ℝ =>
        s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2) (Set.Ioc 0 x) :=
      hint.mono_set (fun s hs => ⟨hs.1, le_trans hs.2 hxle⟩)
    have hi2 : MeasureTheory.IntegrableOn
        (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioc 0 x) :=
      hψint.mono_set (fun s hs => ⟨hs.1, le_trans hs.2 hxle⟩)
    have hCS := Work.FTS.H2.DivQ.csWeightedInterval k γ x hx0 hγ
      (fun s : ℝ => iteratedDeriv (k + 1) f s) hi1 hi2
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

end Work.FTS.EllipticEst.remov.HardyFin
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoRight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The right-end limit -/


end

end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.bPairDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-- The level-`0` weight `ρ z θ = w(z)² · sin(2θ)^{-η}`: the angular weight `sEta` times the
*square* of the radial weight `w`. -/
def Wt (z θ : ℝ) : ℝ := (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ

theorem measurableSet_Iz : MeasurableSet Work.Spaces.Iz := by
  rw [Work.Spaces.Iz]; exact measurableSet_Ici

theorem measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

/-- The angular weight `sEta θ = sin(2θ)^{-η}` is nonnegative on `Iθ`. -/
theorem sEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
    by linarith [hθ.2, Real.pi_pos]⟩) _

/-- The level-`0` weight is nonnegative on `Iθ`. -/
theorem Wt_nonneg {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Wt z θ :=
  mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ)

/-- The level-`0` weight vanishes on the axis `z = 0` (totalised division). -/
theorem Wt_zero_left (θ : ℝ) : Wt 0 θ = 0 := by
  simp only [Wt, Work.Spaces.w]
  norm_num

/-- The angular weight is integrable on `Iθ` (`η = 99/100 < 1`). -/
theorem integrableOn_sEta :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])).1
  simpa only [Work.FTS.EllipticEst.sEta] using h

/-- At level `0` the `HkIntegrand` is the single `Wt`-weighted square. -/
theorem HkIntegrand_zero_eq_Wt (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ = (g z θ) ^ 2 * Wt z θ := by
  have hkey : Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp [Work.Spaces.HkIntegrand]
  rw [hkey, Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ]
  simp only [Wt, Work.FTS.EllipticEst.sEta]
  ring

/-- The angular slices of `HkMem α 0 g`, in `Wt`-form. -/
theorem HkMem_zero_slice_Wt {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 g) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun θ => (g z θ) ^ 2 * Wt z θ) Work.Spaces.Iθ :=
  (hmem.1 z hz).congr_fun
    (fun θ hθ => HkIntegrand_zero_eq_Wt α g z hθ) measurableSet_Iθ



/-- At level `0` the `HkIntegrand` does not depend on the parameter `α` (its mixed-derivative
sum is empty). -/
theorem HkIntegrand_zero_eq_indep (α α' : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ = Work.Spaces.HkIntegrand α' 0 g z θ := by
  simp [Work.Spaces.HkIntegrand]

/-- `HkMem _ 0 g` is independent of the parameter `α`. -/
theorem HkMem_zero_congr {α α' : ℝ} {g : ℝ → ℝ → ℝ} :
    Work.Spaces.HkMem α 0 g ↔ Work.Spaces.HkMem α' 0 g := by
  constructor
  · intro h
    refine ⟨fun z hz => (h.1 z hz).congr_fun
        (fun θ _ => HkIntegrand_zero_eq_indep α α' g z θ) measurableSet_Iθ, ?_⟩
    exact h.2.congr_fun (fun z _ => MeasureTheory.setIntegral_congr_fun measurableSet_Iθ
      (fun θ _ => HkIntegrand_zero_eq_indep α α' g z θ)) measurableSet_Iz
  · intro h
    refine ⟨fun z hz => (h.1 z hz).congr_fun
        (fun θ _ => HkIntegrand_zero_eq_indep α' α g z θ) measurableSet_Iθ, ?_⟩
    exact h.2.congr_fun (fun z _ => MeasureTheory.setIntegral_congr_fun measurableSet_Iθ
      (fun θ _ => HkIntegrand_zero_eq_indep α' α g z θ)) measurableSet_Iz

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.sliceLeftUniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The *uniform* left-half slice estimate for `(u / cos)''`

For every `γ ∈ [1, 3/2]`, every `u` of class `C³` on `(0, π/2)` continuous on `[0, π/2]`
with `u 0 = u (π/2) = 0`, whose second, first and zeroth derivatives against the weights
`sin(2θ)^{-η}`, `1`, `1` are `θ`-integrable on `Iθ = [0, π/2]`, the second derivative of
the quotient `v = u / cos θ` is square integrable on the left half `[0, π/4]` against the
weight `sin(2θ)^{2-γ}`, and

  `∫_{[0,π/4]} (v'')² sin(2θ)^{2-γ} ≤ C (∫_{Iθ} (u'')² sin(2θ)^{-η} + ∫_{Iθ} (u')² + ∫_{Iθ} u²)`

with a **single constant `C = 2000` independent of `γ`** (and of `u`, `g`); this is the
uniform-in-`γ` form of `Work.FTS.EllipticEst.remov.slice_left_le`, where `γ` is quantified
*inside* the existential.  The pointwise core is the quotient-rule identity

  `(u/cos)'' = u''/cos + 2 u' sin/cos² + u (1 + sin²)/cos³`

(`deriv_deriv_div_cos` below) together with the elementary arithmetic estimate
`quarter_arith`; on `[0, π/4]` one has `1/2 ≤ cos θ ≤ 1`, `sin²θ ≤ 1`, `sin(2θ)^{-η} ≥ 1`
and `sin(2θ)^{2-γ} ≤ 1`.  No use is made of the equation `L₀u = g` or of the boundary
conditions, so the three integrability hypotheses on `Iθ` are only used to dominate the
right-hand side.
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

theorem sliceLeftUniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ), 1 ≤ γ → γ ≤ 3 / 2 →
      ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      (MeasureTheory.IntegrableOn (fun θ =>
            (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ)) (Set.Icc 0 (Real.pi / 4)) ∧
        (∫ θ in Set.Icc 0 (Real.pi / 4),
            (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))) := by
  refine ⟨2000, by norm_num, ?_⟩
  intro γ u g hγ1 hγ2 h3 hcont hu0 hpi hL hInt2 hInt1 hInt0
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 4) ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hpt := sec_second_deriv_le u γ hγ1 hγ2 h3
  have hHIθ : MeasureTheory.IntegrableOn
      (fun θ => 2000 * ((deriv (deriv u) θ) ^ 2 * sEta θ + (deriv u θ) ^ 2 + (u θ) ^ 2))
      Work.Spaces.Iθ := ((hInt2.add hInt1).add hInt0).const_mul 2000
  have hHIcc : MeasureTheory.IntegrableOn
      (fun θ => 2000 * ((deriv (deriv u) θ) ^ 2 * sEta θ + (deriv u θ) ^ 2 + (u θ) ^ 2))
      (Set.Icc 0 (Real.pi / 4)) := hHIθ.mono_set hsub
  have hH0 : ∀ x ∈ Work.Spaces.Iθ,
      0 ≤ 2000 * ((deriv (deriv u) x) ^ 2 * sEta x + (deriv u x) ^ 2 + (u x) ^ 2) := by
    intro x hx
    have hsx : 0 ≤ sEta x := by
      rw [sEta]
      exact Real.rpow_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
          (by linarith [hx.2, Real.pi_pos])) _
    have h1 : 0 ≤ (deriv (deriv u) x) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (deriv u x) ^ 2 := sq_nonneg _
    have h4 : 0 ≤ (u x) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg h1 hsx]
  have hG0 : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 4),
      0 ≤ (deriv (fun t => deriv (fun s => u s / Real.cos s) t) x) ^ 2 *
        Real.rpow (Real.sin (2 * x)) (2 - γ) := by
    intro x hx
    refine mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ?_ _)
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
      (by linarith [hx.2, Real.pi_pos])
  have hGmeas : MeasureTheory.AEStronglyMeasurable
      (fun θ => (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ))
      (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 4))) := by
    have h1 : Measurable
        (fun θ : ℝ => deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) :=
      measurable_deriv (fun t => deriv (fun s => u s / Real.cos s) t)
    have h2 : Continuous (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
        (fun x => Or.inr (by linarith))
    exact ((h1.aestronglyMeasurable.pow 2).mul h2.measurable.aestronglyMeasurable)
  have hGint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) (Set.Icc 0 (Real.pi / 4)) :=
    integrableOn_of_le measurableSet_Icc hHIcc hG0 hGmeas (fun x hx => hpt x hx)
  constructor
  · exact hGint
  · calc (∫ θ in Set.Icc 0 (Real.pi / 4),
          (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 - γ))
        ≤ ∫ θ in Work.Spaces.Iθ,
            2000 * ((deriv (deriv u) θ) ^ 2 * sEta θ + (deriv u θ) ^ 2 + (u θ) ^ 2) :=
          setIntegral_le_of_pointwise hsub measurableSet_Icc measurableSet_Icc hGint hHIθ
            (fun x hx => hpt x hx) hH0
      _ = 2000 * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
          rw [MeasureTheory.integral_const_mul]
          congr 1
          have hsplit1 : (∫ a in Work.Spaces.Iθ,
                (deriv (deriv u) a) ^ 2 * sEta a + (deriv u a) ^ 2)
              = (∫ a in Work.Spaces.Iθ, (deriv (deriv u) a) ^ 2 * sEta a)
                + (∫ a in Work.Spaces.Iθ, (deriv u a) ^ 2) :=
            MeasureTheory.integral_add hInt2 hInt1
          have hsplit2 : (∫ a in Work.Spaces.Iθ,
                ((deriv (deriv u) a) ^ 2 * sEta a + (deriv u a) ^ 2) + (u a) ^ 2)
              = (∫ a in Work.Spaces.Iθ, (deriv (deriv u) a) ^ 2 * sEta a + (deriv u a) ^ 2)
                + (∫ a in Work.Spaces.Iθ, (u a) ^ 2) :=
            MeasureTheory.integral_add (hInt2.add hInt1) hInt0
          rw [hsplit2, hsplit1]

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.slice_cs_weighted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-- `(x ^ a) ^ 2 = x ^ (2 * a)` for `x > 0`. -/
private lemma rpow_sq_of_pos (x a : ℝ) (hx : 0 < x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [pow_two, ← Real.rpow_add hx, show a + a = 2 * a by ring]

theorem slice_cs_weighted {g : ℝ → ℝ} (hg : ContinuousOn g Work.Spaces.Iθ)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, |g θ|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := by
  -- ## Step 0: the two endpoints form a null set, hence the integral over `Iθ = [0, π/2]`
  -- equals the integral over the open interval `Ioo 0 (π/2)`, where `sin (2·) > 0`.
  have hpair : MeasureTheory.volume ({(0 : ℝ), Real.pi / 2} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) MeasureTheory.volume
  have hpairab : ∀ᵐ (x : ℝ), x ∉ ({(0 : ℝ), Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  have hst : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo 0 (Real.pi / 2) := by
    filter_upwards [hpairab] with x hx
    refine propext ⟨?_, ?_⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc] at h
      rw [Set.mem_Ioo]
      exact ⟨lt_of_le_of_ne h.1 (fun hc => hx (Or.inl hc.symm)),
        lt_of_le_of_ne h.2 (fun hc => hx (Or.inr hc))⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      rw [Set.mem_Ioo] at h
      exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hms : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set hst
  rw [hms]
  -- ## Step 1: Cauchy–Schwarz over `Ioo 0 (π/2)`.
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hIoomeas : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hη : 0 ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) :=
    fun θ hθ => sin_two_pos hθ
  have hsincont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hwcont : ContinuousOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsincont.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ)))
  have hvcont : ContinuousOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsincont.rpow_const (fun θ hθ => Or.inr (by rw [Work.Spaces.eta]; norm_num))
  have hucont : ContinuousOn
      (fun θ : ℝ => |g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hg.mono hsub).abs.mul hwcont
  have huaesm : AEStronglyMeasurable
      (fun θ : ℝ => |g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hucont.aestronglyMeasurable hIoomeas
  have hvaesm : AEStronglyMeasurable
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hvcont.aestronglyMeasurable hIoomeas
  -- the two squares are exactly the two weights of the statement
  have hEq1 : Set.EqOn (fun θ : ℝ => (g θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (fun θ : ℝ => (|g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro θ hθ
    have hx : 0 < Real.sin (2 * θ) := hsinpos θ hθ
    show (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = (|g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
    rw [mul_pow, sq_abs, rpow_sq_of_pos _ _ hx,
      show 2 * (-(Work.Spaces.eta / 2)) = -(Work.Spaces.eta) by ring]
  have hEq2 : Set.EqOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
      (fun θ : ℝ => ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro θ hθ
    show (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
      = ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
    rw [rpow_sq_of_pos _ _ (hsinpos θ hθ),
      show 2 * (Work.Spaces.eta / 2) = Work.Spaces.eta by ring]
  have hu2int : MeasureTheory.Integrable
      (fun θ : ℝ => (|g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (hint.mono_set hsub).congr_fun hEq1 hIoomeas
  have hv2int : MeasureTheory.Integrable
      (fun θ : ℝ => ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    ((integrableOn_sin_two_rpow hη).1.mono_set hsub).congr_fun hEq2 hIoomeas
  have humem : MeasureTheory.MemLp
      (fun θ : ℝ => |g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) 2
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (MeasureTheory.memLp_two_iff_integrable_sq huaesm).mpr hu2int
  have hvmems : MeasureTheory.MemLp
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) 2
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hvaesm).mpr hv2int
  have hcs := Work.Spaces.cs_integral humem hvmems
  -- ## Step 2: identify the three integrals of the Cauchy–Schwarz inequality
  have e1 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (|g x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2)))
          * (Real.sin (2 * x)) ^ (Work.Spaces.eta / 2))
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), |g x| := by
    refine MeasureTheory.setIntegral_congr_fun hIoomeas ?_
    intro x hx
    have hx' : 0 < Real.sin (2 * x) := hsinpos x hx
    show (|g x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2)))
        * (Real.sin (2 * x)) ^ (Work.Spaces.eta / 2) = |g x|
    rw [mul_assoc, ← Real.rpow_add hx',
      show -(Work.Spaces.eta / 2) + Work.Spaces.eta / 2 = 0 by ring, Real.rpow_zero,
      mul_one]
  have e2 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (|g x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2))) ^ 2)
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (g x) ^ 2 * Work.FTS.EllipticEst.thEta x := by
    refine MeasureTheory.setIntegral_congr_fun hIoomeas ?_
    intro x hx
    have hx' : 0 < Real.sin (2 * x) := hsinpos x hx
    show (|g x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = (g x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))
    rw [mul_pow, sq_abs, rpow_sq_of_pos _ _ hx',
      show 2 * (-(Work.Spaces.eta / 2)) = -(Work.Spaces.eta) by ring]
  have e3 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ((Real.sin (2 * x)) ^ (Work.Spaces.eta / 2)) ^ 2)
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (Real.sin (2 * x)) ^ (Work.Spaces.eta) := by
    refine MeasureTheory.setIntegral_congr_fun hIoomeas ?_
    intro x hx
    show ((Real.sin (2 * x)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * x)) ^ (Work.Spaces.eta)
    rw [rpow_sq_of_pos _ _ (hsinpos x hx),
      show 2 * (Work.Spaces.eta / 2) = Work.Spaces.eta by ring]
  rw [e1, e2, e3] at hcs
  exact hcs

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.divSinIterMidBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

/-! ## Elementary facts about the angular operator

The whole estimate lives on the middle region `[π/8, 3π/8]`, where `sin(2θ) ∈ [1/√2, 1]`.
The only calculus input is the recursion for the iterates of `D_θ` applied to the quotient
`h / sin 2θ`, which holds on the open interval `(0, π/2)`. -/

/-- The `θ`-coefficient function `2 cos 2θ` of the quotient recursion. -/
private def cfun : ℝ → ℝ := fun θ => 2 * Real.cos (2 * θ)

private lemma cfun_analytic : ContDiff ℝ (⊤ : WithTop ℕ∞) cfun := by
  show ContDiff ℝ (⊤ : WithTop ℕ∞) (fun θ : ℝ => 2 * Real.cos (2 * θ))
  fun_prop

private lemma cfun_periodic : Function.Periodic cfun Real.pi := by
  intro x
  show 2 * Real.cos (2 * (x + Real.pi)) = 2 * Real.cos (2 * x)
  rw [show 2 * (x + Real.pi) = 2 * x + 2 * Real.pi by ring, Real.cos_periodic]

private lemma cfun_contDiffOn (n : ℕ) :
    ContDiffOn ℝ (n : WithTop ℕ∞) cfun (Set.Ioo 0 (Real.pi / 2)) := by
  show ContDiffOn ℝ (n : WithTop ℕ∞) (fun θ : ℝ => 2 * Real.cos (2 * θ)) _
  fun_prop

/-- `Dth1Iter (n+1) f = Dth1Iter n (Dth1 f)`. -/
private lemma Dth1Iter_succ_eq (n : ℕ) (f : ℝ → ℝ) :
    Work.Elliptic.Dth1Iter (n + 1) f = Work.Elliptic.Dth1Iter n (Work.Elliptic.Dth1 f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show Work.Elliptic.Dth1 (Work.Elliptic.Dth1Iter (n + 1) f)
        = Work.Elliptic.Dth1 (Work.Elliptic.Dth1Iter n (Work.Elliptic.Dth1 f))
      rw [ih]

private lemma deriv_sin_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) := by
  have h1 : HasDerivAt (fun θ' : ℝ => (2 : ℝ) * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = Real.cos (2 * θ) * 2 := by
    have h3 := (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    simpa [Function.comp_def] using h3.deriv
  rw [h2]; ring

/-- A function smooth on the open angular interval is `C^n` there for every finite `n`. -/
private lemma contDiffOn_finite {h : ℝ → ℝ} (n : ℕ)
    (hsm : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (n : WithTop ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) :=
  hsm.of_le (WithTop.coe_le_coe.mpr le_top)

/-- The derivative of a function smooth on the open angular interval is `C^n` there. -/
private lemma contDiffOn_deriv {h : ℝ → ℝ} (n : ℕ)
    (hsm : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (deriv h) (Set.Ioo 0 (Real.pi / 2)) :=
  (contDiffOn_finite (n + 1) hsm).deriv_of_isOpen isOpen_Ioo (le_of_eq (by norm_cast))

/-- The angular quotient of a function smooth on the open angular interval is `C^n` there. -/
private lemma contDiffOn_SinQ {h : ℝ → ℝ} (n : ℕ)
    (hsm : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (Work.Elliptic.SinQ h) (Set.Ioo 0 (Real.pi / 2)) := by
  show ContDiffOn ℝ (n : WithTop ℕ∞) (fun θ => h θ / Real.sin (2 * θ)) _
  have hs : ContDiffOn ℝ (n : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  refine (contDiffOn_finite n hsm).div hs ?_
  intro x hx
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
    (by linarith [hx.2, Real.pi_pos]))

/-- `D_θ (h / sin 2θ) = ∂_θ h - 2 cos 2θ · (h / sin 2θ)` on `(0, π/2)`. -/
private lemma Dth1_SinQ_eqOn {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) h (Set.Ioo 0 (Real.pi / 2))) :
    Set.EqOn (Work.Elliptic.Dth1 (Work.Elliptic.SinQ h))
      (fun θ => deriv h θ - cfun θ * Work.Elliptic.SinQ h θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hsinU : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun x : ℝ => Real.sin (2 * x))
      (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  have hne : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * x) ≠ 0 := fun x hx =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
      (by linarith [hx.2, Real.pi_pos]))
  have hgU : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (Work.Elliptic.SinQ h)
      (Set.Ioo 0 (Real.pi / 2)) := by
    show ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun x => h x / Real.sin (2 * x)) _
    exact hsm.div hsinU hne
  have hneθ : ∀ᶠ x in 𝓝 θ, Real.sin (2 * x) ≠ 0 := by
    have hc : ContinuousAt (fun x : ℝ => Real.sin (2 * x)) θ := by fun_prop
    exact hc.eventually_ne (hne θ hθ)
  have heq : (fun x : ℝ => Real.sin (2 * x) * Work.Elliptic.SinQ h x) =ᶠ[𝓝 θ] h := by
    filter_upwards [hneθ] with x hx
    simp only [Work.Elliptic.SinQ]
    rw [mul_comm, div_mul_cancel₀ _ hx]
  have hdeq : deriv (fun x : ℝ => Real.sin (2 * x) * Work.Elliptic.SinQ h x) θ
      = deriv h θ := heq.deriv_eq
  have dsin : DifferentiableAt ℝ (fun x : ℝ => Real.sin (2 * x)) θ := by fun_prop
  have dg : DifferentiableAt ℝ (Work.Elliptic.SinQ h) θ :=
    (hgU.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp)
  have hprod : deriv (fun x : ℝ => Real.sin (2 * x) * Work.Elliptic.SinQ h x) θ
      = deriv (fun x : ℝ => Real.sin (2 * x)) θ * Work.Elliptic.SinQ h θ
        + Real.sin (2 * θ) * deriv (Work.Elliptic.SinQ h) θ :=
    deriv_mul dsin dg
  rw [deriv_sin_two θ] at hprod
  show Real.sin (2 * θ) * deriv (Work.Elliptic.SinQ h) θ
    = deriv h θ - cfun θ * Work.Elliptic.SinQ h θ
  rw [← hdeq, hprod]
  simp only [cfun]
  ring

/-- **The recursion for the iterates of the angular quotient.**  On the open interval
`(0, π/2)`,

  `D_θ^i (h/sin 2θ) = D_θ^{i-1}(∂_θh) - ∑_{k<i} C(i-1,k)·D_θ^k(2cos 2θ)·D_θ^{i-1-k}(h/sin2θ)`,

for `h` smooth on `(0, π/2)` and `i ≥ 1`.  This is the `C^∞`-on-the-open-interval
version of `Work.Elliptic.DivSinRec` (which asks for analyticity on a neighbourhood of the
closed interval); the proof only ever uses finite smoothness on `(0, π/2)`. -/
private theorem divSinRecOpen {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) h (Set.Ioo 0 (Real.pi / 2)))
    (i : ℕ) (hi : 1 ≤ i) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ =
        Work.Elliptic.Dth1Iter (i - 1) (deriv h) θ -
          ∑ a ∈ Finset.range i, (Nat.choose (i - 1) a : ℝ) *
            (Work.Elliptic.Dth1Iter a cfun θ
              * Work.Elliptic.Dth1Iter (i - 1 - a) (Work.Elliptic.SinQ h) θ) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  intro θ hθ
  simp only [Nat.add_sub_cancel]
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hder : ContDiffOn ℝ (j : WithTop ℕ∞) (deriv h) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_deriv j hsm
  have hSinQ : ContDiffOn ℝ (j : WithTop ℕ∞) (Work.Elliptic.SinQ h)
      (Set.Ioo 0 (Real.pi / 2)) := contDiffOn_SinQ j hsm
  have hc : ContDiffOn ℝ (j : WithTop ℕ∞) cfun (Set.Ioo 0 (Real.pi / 2)) :=
    cfun_contDiffOn j
  have hcV : ContDiffOn ℝ (j : WithTop ℕ∞)
      (fun x => cfun x * Work.Elliptic.SinQ h x) (Set.Ioo 0 (Real.pi / 2)) := hc.mul hSinQ
  have hev : Work.Elliptic.Dth1 (Work.Elliptic.SinQ h) =ᶠ[𝓝 θ]
      (fun x => deriv h x - cfun x * Work.Elliptic.SinQ h x) := by
    filter_upwards [hU.mem_nhds hθ] with x hx
    exact Dth1_SinQ_eqOn hsm hx
  calc Work.Elliptic.Dth1Iter (j + 1) (Work.Elliptic.SinQ h) θ
      = Work.Elliptic.Dth1Iter j (Work.Elliptic.Dth1 (Work.Elliptic.SinQ h)) θ := by
        rw [Dth1Iter_succ_eq]
    _ = Work.Elliptic.Dth1Iter j
          (fun x => deriv h x - cfun x * Work.Elliptic.SinQ h x) θ :=
        Work.FTS.EllipticEst.TT.Dth1Iter_eventuallyEq j hev
    _ = Work.Elliptic.Dth1Iter j (deriv h) θ
          - Work.Elliptic.Dth1Iter j (fun x => cfun x * Work.Elliptic.SinQ h x) θ :=
        (Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterSubEqOn j hder hcV) hθ
    _ = Work.Elliptic.Dth1Iter j (deriv h) θ
          - ∑ a ∈ Finset.range (j + 1), (Nat.choose j a : ℝ) *
              (Work.Elliptic.Dth1Iter a cfun θ
                * Work.Elliptic.Dth1Iter (j - a) (Work.Elliptic.SinQ h) θ) := by
        rw [Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterMulEqOn j hc hSinQ hθ]

/-! ## A universal bound for the coefficients `D_θ^k (2 cos 2θ)`, `k ≤ 3` -/

/-- There is a universal constant bounding `|D_θ^k (2 cos 2θ)|` for `k ≤ 3` on all of `ℝ`.
The function `2 cos 2θ` is `π`-periodic and smooth, so each iterate is too, and a continuous
periodic function is bounded. -/
private lemma coeffBound :
    ∃ cw : ℝ, 0 ≤ cw ∧ ∀ m : ℕ, m ≤ 3 → ∀ θ : ℝ,
      |Work.Elliptic.Dth1Iter m cfun θ| ≤ cw := by
  obtain ⟨c0, h0, hb0⟩ :=
    Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterBddOfPeriodicSmooth
      cfun_analytic cfun_periodic 0
  obtain ⟨c1, h1, hb1⟩ :=
    Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterBddOfPeriodicSmooth
      cfun_analytic cfun_periodic 1
  obtain ⟨c2, h2, hb2⟩ :=
    Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterBddOfPeriodicSmooth
      cfun_analytic cfun_periodic 2
  obtain ⟨c3, h3, hb3⟩ :=
    Work.FTS.EllipticEst.remov.SliceTopAux.Dth1IterBddOfPeriodicSmooth
      cfun_analytic cfun_periodic 3
  refine ⟨max (max c0 c1) (max c2 c3), ?_, ?_⟩
  · exact le_trans h0 (le_max_of_le_left (le_max_left c0 c1))
  · intro m hm θ
    interval_cases m
    · exact le_trans (hb0 θ) (le_trans (le_max_left c0 c1)
        (le_max_left (max c0 c1) (max c2 c3)))
    · exact le_trans (hb1 θ) (le_trans (le_max_right c0 c1)
        (le_max_left (max c0 c1) (max c2 c3)))
    · exact le_trans (hb2 θ) (le_trans (le_max_left c2 c3)
        (le_max_right (max c0 c1) (max c2 c3)))
    · exact le_trans (hb3 θ) (le_trans (le_max_right c2 c3)
        (le_max_right (max c0 c1) (max c2 c3)))

/-! ## The sequence of constants

`Kacc cw j` is the "table" of constants for the levels `≤ j`, and `Kf cw j = Kacc cw j j` is
the constant at level `j`.  The recursion `Kf cw (j+1) = 1 + cw ∑_{a≤j} C(j,a) Kf cw (j-a)`
is exactly what the strong induction produces. -/

private def Kacc (cw : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | (j + 1), l =>
      if l = j + 1 then 1 + cw * ∑ a ∈ Finset.range (j + 1),
        ((j.choose a : ℝ) * Kacc cw j (j - a))
      else Kacc cw j l

private def Kf (cw : ℝ) (j : ℕ) : ℝ := Kacc cw j j

private lemma Kacc_eq_Kf (cw : ℝ) : ∀ j l : ℕ, l ≤ j → Kacc cw j l = Kf cw l := by
  intro j
  induction j with
  | zero =>
      intro l hl
      interval_cases l
      rfl
  | succ j ih =>
      intro l hl
      rcases eq_or_lt_of_le hl with rfl | hlt
      · rfl
      · have hne : l ≠ j + 1 := by omega
        rw [show Kacc cw (j + 1) l = Kacc cw j l from by
          simp only [Kacc]
          rw [ite_eq_right hne]]
        exact ih l (by omega)

private lemma Kf_succ (cw : ℝ) (j : ℕ) :
    Kf cw (j + 1) = 1 + cw * ∑ a ∈ Finset.range (j + 1),
      (j.choose a : ℝ) * Kf cw (j - a) := by
  have hunf : Kf cw (j + 1) = 1 + cw * ∑ a ∈ Finset.range (j + 1),
      (j.choose a : ℝ) * Kacc cw j (j - a) := by
    show Kacc cw (j + 1) (j + 1) = _
    simp only [Kacc, ite_true]
  rw [hunf]
  have hs : (∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) * Kacc cw j (j - a))
      = ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) * Kf cw (j - a) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Kacc_eq_Kf cw j (j - a) (Nat.sub_le j a)]
  rw [hs]

private lemma Kf_nonneg {cw : ℝ} (hcw : 0 ≤ cw) : ∀ l : ℕ, 0 ≤ Kf cw l := by
  intro l
  induction l using Nat.strong_induction_on with
  | h l ih =>
      rcases Nat.eq_zero_or_pos l with h0 | hpos
      · rw [h0]
        norm_num [Kf, Kacc]
      · obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
        rw [Kf_succ]
        have hs : 0 ≤ ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) * Kf cw (j - a) :=
          Finset.sum_nonneg (fun a _ => mul_nonneg (Nat.cast_nonneg _) (ih (j - a) (by omega)))
        have := mul_nonneg hcw hs
        linarith

/-! ## The comparison quantity `|V| + ∑_{m<j} |U_m|` and its monotonicity -/

private def Abound (h : ℝ → ℝ) (θ : ℝ) (j : ℕ) : ℝ :=
  |Work.Elliptic.SinQ h θ| + ∑ m ∈ Finset.range j, |Work.Elliptic.Dth1Iter m (deriv h) θ|

private lemma Abound_nonneg (h : ℝ → ℝ) (θ : ℝ) (j : ℕ) : 0 ≤ Abound h θ j :=
  add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

private lemma Abound_mono {h : ℝ → ℝ} {θ : ℝ} {l j : ℕ} (hlj : l ≤ j) :
    Abound h θ l ≤ Abound h θ j := by
  show |Work.Elliptic.SinQ h θ| + ∑ i ∈ Finset.range l,
      |Work.Elliptic.Dth1Iter i (deriv h) θ| ≤
    |Work.Elliptic.SinQ h θ| + ∑ i ∈ Finset.range j,
      |Work.Elliptic.Dth1Iter i (deriv h) θ|
  exact add_le_add le_rfl
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hlj)
      (fun i _ _ => abs_nonneg _))

private lemma Abound_term_le {h : ℝ → ℝ} {θ : ℝ} {m j : ℕ} (hm : m < j) :
    |Work.Elliptic.Dth1Iter m (deriv h) θ| ≤ Abound h θ j := by
  show |Work.Elliptic.Dth1Iter m (deriv h) θ| ≤
    |Work.Elliptic.SinQ h θ| + ∑ i ∈ Finset.range j, |Work.Elliptic.Dth1Iter i (deriv h) θ|
  refine le_trans (Finset.single_le_sum
    (f := fun i => |Work.Elliptic.Dth1Iter i (deriv h) θ|)
    (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hm)) ?_
  exact le_add_of_nonneg_left (abs_nonneg _)

private lemma abs_sub_le_abs_add_abs (A B : ℝ) : |A - B| ≤ |A| + |B| := by
  rw [abs_le]
  constructor <;> linarith [neg_abs_le A, neg_abs_le B, le_abs_self A, le_abs_self B]

/-- **The strong induction.**  For a slice `h` smooth on `(0, π/2)` and a constant `cw`
bounding `|D_θ^k (2 cos 2θ)|` for `k ≤ 3`, the iterate `D_θ^j (h/sin 2θ)` is bounded by
`Kf cw j · (|h/sin 2θ| + ∑_{m<j} |D_θ^m(∂_θh)|)` on `(0, π/2)`, for every `j ≤ 4`. -/
private lemma iterBound_aux {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) h (Set.Ioo 0 (Real.pi / 2)))
    {cw : ℝ} (hcw0 : 0 ≤ cw)
    (hcwb : ∀ m : ℕ, m ≤ 3 → ∀ θ : ℝ, |Work.Elliptic.Dth1Iter m cfun θ| ≤ cw) :
    ∀ j : ℕ, j ≤ 4 → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Elliptic.Dth1Iter j (Work.Elliptic.SinQ h) θ| ≤ Kf cw j * Abound h θ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj4 θ hθ
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0]
      simp only [Work.Elliptic.Dth1Iter_zero, Abound, Finset.range_zero, Finset.sum_empty,
        add_zero]
      rw [show Kf cw 0 = 1 from by simp only [Kf, Kacc], one_mul]
    · have hrec := divSinRecOpen hsm j hpos θ hθ
      have htri : |Work.Elliptic.Dth1Iter j (Work.Elliptic.SinQ h) θ| ≤
          |Work.Elliptic.Dth1Iter (j - 1) (deriv h) θ| +
            |∑ a ∈ Finset.range j, (Nat.choose (j - 1) a : ℝ) *
              (Work.Elliptic.Dth1Iter a cfun θ
                * Work.Elliptic.Dth1Iter (j - 1 - a) (Work.Elliptic.SinQ h) θ)| := by
        rw [hrec]
        exact abs_sub_le_abs_add_abs _ _
      have habs : |∑ a ∈ Finset.range j, (Nat.choose (j - 1) a : ℝ) *
            (Work.Elliptic.Dth1Iter a cfun θ
              * Work.Elliptic.Dth1Iter (j - 1 - a) (Work.Elliptic.SinQ h) θ)|
          ≤ ∑ a ∈ Finset.range j, (Nat.choose (j - 1) a : ℝ) * cw *
              (Kf cw (j - 1 - a) * Abound h θ j) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        apply Finset.sum_le_sum
        intro a ha
        have haj : a < j := Finset.mem_range.mp ha
        have ha3 : a ≤ 3 := by omega
        have hca : |Work.Elliptic.Dth1Iter a cfun θ| ≤ cw := hcwb a ha3 θ
        have hIHa : |Work.Elliptic.Dth1Iter (j - 1 - a) (Work.Elliptic.SinQ h) θ|
            ≤ Kf cw (j - 1 - a) * Abound h θ (j - 1 - a) :=
          ih (j - 1 - a) (by omega) (by omega) θ hθ
        have hKf0 : 0 ≤ Kf cw (j - 1 - a) := Kf_nonneg hcw0 _
        have hAmono : Abound h θ (j - 1 - a) ≤ Abound h θ j := Abound_mono (by omega)
        calc |(Nat.choose (j - 1) a : ℝ) * (Work.Elliptic.Dth1Iter a cfun θ
                * Work.Elliptic.Dth1Iter (j - 1 - a) (Work.Elliptic.SinQ h) θ)|
            = (Nat.choose (j - 1) a : ℝ) * |Work.Elliptic.Dth1Iter a cfun θ| *
                |Work.Elliptic.Dth1Iter (j - 1 - a) (Work.Elliptic.SinQ h) θ| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
              ring
          _ ≤ (Nat.choose (j - 1) a : ℝ) * cw *
                |Work.Elliptic.Dth1Iter (j - 1 - a) (Work.Elliptic.SinQ h) θ| := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hca (Nat.cast_nonneg _)) (abs_nonneg _)
          _ ≤ (Nat.choose (j - 1) a : ℝ) * cw *
                (Kf cw (j - 1 - a) * Abound h θ j) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Nat.cast_nonneg _) hcw0)
              exact le_trans hIHa (mul_le_mul_of_nonneg_left hAmono hKf0)
      have hsum_eq : ∑ a ∈ Finset.range j, (Nat.choose (j - 1) a : ℝ) * cw *
            (Kf cw (j - 1 - a) * Abound h θ j)
          = (cw * ∑ a ∈ Finset.range j, (Nat.choose (j - 1) a : ℝ) * Kf cw (j - 1 - a))
              * Abound h θ j := by
        rw [show (∑ a ∈ Finset.range j, (Nat.choose (j - 1) a : ℝ) * cw *
              (Kf cw (j - 1 - a) * Abound h θ j))
            = ∑ a ∈ Finset.range j, ((Nat.choose (j - 1) a : ℝ) * cw * Kf cw (j - 1 - a))
                * Abound h θ j
          from Finset.sum_congr rfl (fun a _ => by ring)]
        rw [← Finset.sum_mul]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun a _ => by ring)
      have hKfrec : Kf cw j = 1 + cw * ∑ a ∈ Finset.range j,
          (Nat.choose (j - 1) a : ℝ) * Kf cw (j - 1 - a) := by
        have h := Kf_succ cw (j - 1)
        rw [show j - 1 + 1 = j from by omega] at h
        exact h
      have hUle : |Work.Elliptic.Dth1Iter (j - 1) (deriv h) θ| ≤ Abound h θ j :=
        Abound_term_le (by omega)
      calc |Work.Elliptic.Dth1Iter j (Work.Elliptic.SinQ h) θ|
          ≤ |Work.Elliptic.Dth1Iter (j - 1) (deriv h) θ| +
            |∑ a ∈ Finset.range j, (Nat.choose (j - 1) a : ℝ) *
              (Work.Elliptic.Dth1Iter a cfun θ
                * Work.Elliptic.Dth1Iter (j - 1 - a) (Work.Elliptic.SinQ h) θ)| := htri
        _ ≤ Abound h θ j + ∑ a ∈ Finset.range j, (Nat.choose (j - 1) a : ℝ) * cw *
              (Kf cw (j - 1 - a) * Abound h θ j) := add_le_add hUle habs
        _ = (1 + cw * ∑ a ∈ Finset.range j,
              (Nat.choose (j - 1) a : ℝ) * Kf cw (j - 1 - a)) * Abound h θ j := by
              rw [hsum_eq]; ring
        _ = Kf cw j * Abound h θ j := by rw [hKfrec]

/-! ## The passage from the absolute-value bound to the squared bound -/

private lemma Abound_sq_le (h : ℝ → ℝ) (θ : ℝ) (i : ℕ) :
    (Abound h θ i) ^ 2 ≤ ((i : ℝ) + 1) *
      ((Work.Elliptic.SinQ h θ) ^ 2
        + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2) := by
  classical
  let G : ℕ → ℝ := fun m =>
    if m = 0 then |Work.Elliptic.SinQ h θ| else |Work.Elliptic.Dth1Iter (m - 1) (deriv h) θ|
  have hG0 : G 0 = |Work.Elliptic.SinQ h θ| := by simp only [G, ite_true]
  have hGs : ∀ m : ℕ, G (m + 1) = |Work.Elliptic.Dth1Iter m (deriv h) θ| := by
    intro m
    show (if m + 1 = 0 then |Work.Elliptic.SinQ h θ|
      else |Work.Elliptic.Dth1Iter (m + 1 - 1) (deriv h) θ|) = _
    rw [ite_eq_right (Nat.succ_ne_zero m), Nat.add_sub_cancel]
  have hsum : Abound h θ i = ∑ m ∈ Finset.range (i + 1), G m := by
    rw [Finset.sum_range_succ']
    simp only [hG0, hGs, Abound]
    ring
  have hsum2 : ∑ m ∈ Finset.range (i + 1), (G m) ^ 2
      = (Work.Elliptic.SinQ h θ) ^ 2
        + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2 := by
    rw [Finset.sum_range_succ']
    simp only [hG0, hGs, sq_abs]
    ring
  have hsq : (∑ m ∈ Finset.range (i + 1), G m) ^ 2
      ≤ ((i : ℝ) + 1) * ∑ m ∈ Finset.range (i + 1), (G m) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1)) (f := G)
    rw [Finset.card_range] at h
    push_cast at h
    exact h
  calc (Abound h θ i) ^ 2 = (∑ m ∈ Finset.range (i + 1), G m) ^ 2 := by rw [hsum]
    _ ≤ ((i : ℝ) + 1) * ∑ m ∈ Finset.range (i + 1), (G m) ^ 2 := hsq
    _ = ((i : ℝ) + 1) * ((Work.Elliptic.SinQ h θ) ^ 2
          + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2) := by
        rw [hsum2]

/-- **The pointwise iterate bound on the middle region.**  For every slice `h` smooth on
`(0, π/2)` there is a universal constant `K` with: for every `1 ≤ i ≤ 4` and every
`θ ∈ [π/8, 3π/8]`,

  `(D_θ^i (h / sin 2θ)(θ))² ≤ K · ( (h θ / sin 2θ)² + ∑_{m < i} (D_θ^m (∂_θ h)(θ))² )`,

where `D_θ = sin(2θ) ∂_θ` (`Work.Elliptic.Dth1Iter`).

Route.  On the open interval `(0, π/2)` one has `D_θ (h/sin 2θ) = ∂_θh − 2cos 2θ·(h/sin 2θ)`
(quotient rule), so writing `V = h/sin 2θ`, `U_m = D_θ^m(∂_θh)`, `c_k = D_θ^k(2cos 2θ)`, the
`D_θ`-Leibniz rule (`Dth1IterMulEqOn`) and additivity (`Dth1IterSubEqOn`) give, for `i ≥ 1`,

  `D_θ^i V = U_{i-1} − ∑_{k<i} C(i-1,k)·c_k·D_θ^{i-1-k}V`

on `(0, π/2)`.  With `|c_k| ≤ Cw` for `k ≤ 3` (`Dth1IterBddOfPeriodicSmooth` applied to the
`π`-periodic smooth `θ ↦ 2cos 2θ`), a strong induction gives
`|D_θ^j V| ≤ K_j (|V| + ∑_{m<j} |U_m|)` for `j ≤ 4` with universal constants `K_j`, and
`(A + B)² ≤ (j+1)(A² + B²)` for the finite sum converts this to the stated squared bound. -/
theorem divSinIterMidBound :
    ∃ K : ℝ, 0 < K ∧ ∀ (h : ℝ → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      ∀ i : ℕ, i ∈ Finset.Icc 1 4 → ∀ θ : ℝ,
        θ ∈ Set.Icc (Real.pi / 8) (3 * Real.pi / 8) →
        (Work.Elliptic.Dth1Iter i (fun η => h η / Real.sin (2 * η)) θ) ^ 2
          ≤ K * ((h θ / Real.sin (2 * θ)) ^ 2
              + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2) := by
  obtain ⟨cw, hcw0, hcwb⟩ := coeffBound
  refine ⟨(∑ j ∈ Finset.range 5, (Kf cw j) ^ 2 * ((j : ℝ) + 1)) + 1, ?_, ?_⟩
  · have : 0 ≤ ∑ j ∈ Finset.range 5, (Kf cw j) ^ 2 * ((j : ℝ) + 1) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (by positivity))
    linarith
  · intro h hsm i hi θ hθ
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hi4 : i ≤ 4 := (Finset.mem_Icc.mp hi).2
    have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := by
      have hp := Real.pi_pos
      constructor <;> linarith [hθ.1, hθ.2]
    have hbnd := iterBound_aux hsm hcw0 hcwb i hi4 θ hθIoo
    have hKi0 : 0 ≤ Kf cw i := Kf_nonneg hcw0 i
    have hAb0 : 0 ≤ Abound h θ i := Abound_nonneg h θ i
    have hS0 : 0 ≤ (Work.Elliptic.SinQ h θ) ^ 2
        + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2 :=
      add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hA := Abound_sq_le h θ i
    have hstep1 : (Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ) ^ 2
        ≤ (Kf cw i * Abound h θ i) ^ 2 := by
      have h1 : |Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ| ≤ Kf cw i * Abound h θ i :=
        hbnd
      have h3 : |Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ| ^ 2
          ≤ (Kf cw i * Abound h θ i) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      rwa [sq_abs] at h3
    have hstep2 : (Kf cw i * Abound h θ i) ^ 2
        ≤ (Kf cw i) ^ 2 * (((i : ℝ) + 1) * ((Work.Elliptic.SinQ h θ) ^ 2
            + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2)) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hA (sq_nonneg _)
    have hterm : (Kf cw i) ^ 2 * ((i : ℝ) + 1)
        ≤ ∑ j ∈ Finset.range 5, (Kf cw j) ^ 2 * ((j : ℝ) + 1) :=
      Finset.single_le_sum (f := fun j => (Kf cw j) ^ 2 * ((j : ℝ) + 1))
        (fun j _ => mul_nonneg (sq_nonneg _) (by positivity))
        (Finset.mem_range.mpr (by omega))
    have hstep3 : (Kf cw i) ^ 2 * (((i : ℝ) + 1) * ((Work.Elliptic.SinQ h θ) ^ 2
          + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2))
        ≤ ((∑ j ∈ Finset.range 5, (Kf cw j) ^ 2 * ((j : ℝ) + 1)) + 1)
            * ((Work.Elliptic.SinQ h θ) ^ 2
              + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2) := by
      have hle : (Kf cw i) ^ 2 * ((i : ℝ) + 1)
          ≤ (∑ j ∈ Finset.range 5, (Kf cw j) ^ 2 * ((j : ℝ) + 1)) + 1 := by
        have h1 : 0 ≤ ∑ j ∈ Finset.range 5, (Kf cw j) ^ 2 * ((j : ℝ) + 1) :=
          Finset.sum_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (by positivity))
        linarith [hterm]
      have := mul_le_mul_of_nonneg_right hle hS0
      calc (Kf cw i) ^ 2 * (((i : ℝ) + 1) * ((Work.Elliptic.SinQ h θ) ^ 2
              + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2))
          = ((Kf cw i) ^ 2 * ((i : ℝ) + 1)) * ((Work.Elliptic.SinQ h θ) ^ 2
              + ∑ m ∈ Finset.range i, (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2) := by ring
        _ ≤ _ := this
    exact le_trans hstep1 (le_trans hstep2 hstep3)

end

end Work.FTS.H2.DivQ
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.RGWeak.Fgen_algebra =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR.RGWeak

open Work.EllipticEst.ModalSolution.RadGreenWeak

theorem Fgen_algebra {α : ℝ} (hα : 0 < α) (m : ℕ) {c ψ : ℝ → ℝ} :
    ∀ t : ℝ, 0 < t →
      Work.EllipticEst.ModalSolution.RadGreenWeak.srcM α m c t *
          Work.FTS.H2.ModalSolR.RGWeak.Fgen α (Work.EllipticEst.ModalSolution.RadGreenWeak.sM α m) ψ t
        - Work.EllipticEst.ModalSolution.RadGreenWeak.srcP α m c t *
          Work.FTS.H2.ModalSolR.RGWeak.Fgen α (Work.EllipticEst.ModalSolution.RadGreenWeak.sP α m) ψ t
      = α * (4 * (m : ℝ) + 5) *
          (c t * ψ t * Work.EllipticEst.ModalSolution.RadGreenWeak.wgt α t) := by
  intro t ht
  have hα0 : α ≠ 0 := ne_of_gt hα
  -- The two indicial exponents, as opaque atoms (so that `ring` can reassociate products;
  -- it cannot see through the division by `α`), together with their values `-(2m+5)/α`, `2m/α`.
  set M : ℝ := -(2 * (m : ℝ) + 5) / α with hM
  set P : ℝ := 2 * (m : ℝ) / α with hP
  have hsM : sM α m = M := by rw [hM]; rfl
  have hsP : sP α m = P := by rw [hP]; rfl
  -- `srcM`, `srcP` in terms of `M`, `P`: the exponents `(2m+5)/α = -M`, `-(2m)/α = -P`.
  have hsrcM : srcM α m c t = c t * t ^ (-M - 1) := by
    simp only [srcM]
    rw [show (2 * (m : ℝ) + 5) / α - 1 = -M - 1 from by rw [hM]; ring]
  have hsrcP : srcP α m c t = c t * t ^ (-P - 1) := by
    simp only [srcP]
    rw [show -(2 * (m : ℝ) / α) - 1 = -P - 1 from by rw [hP]]
  -- Merging the powers of `t`: `t^{-R-1}·(t^R·X - R·t^{R-1}·Y) = X/t - R·Y/t²`.
  have hcomb (R : ℝ) : t ^ (-R - 1) * (t ^ R * deriv ψ t - R * t ^ (R - 1) * ψ t)
      = deriv ψ t * t ^ (-1:ℝ) - R * ψ t * t ^ (-2:ℝ) := by
    rw [mul_sub]
    rw [show t ^ (-R - 1) * (t ^ R * deriv ψ t)
          = deriv ψ t * (t ^ (-R - 1) * t ^ R) from by ring,
        show t ^ (-R - 1) * (R * t ^ (R - 1) * ψ t)
          = R * ψ t * (t ^ (-R - 1) * t ^ (R - 1)) from by ring]
    rw [show t ^ (-R - 1) * t ^ R = t ^ (-1:ℝ) from by rw [← Real.rpow_add ht]; congr 1; ring,
        show t ^ (-R - 1) * t ^ (R - 1) = t ^ (-2:ℝ) from by rw [← Real.rpow_add ht]; congr 1; ring]
  have htermM : srcM α m c t * Fgen α M ψ t
      = c t * pwt α t * (deriv ψ t * t ^ (-1:ℝ) - M * ψ t * t ^ (-2:ℝ)) := by
    rw [hsrcM, Fgen]
    rw [show (c t * t ^ (-M - 1)) * (pwt α t * (t ^ M * deriv ψ t - M * t ^ (M - 1) * ψ t))
        = c t * pwt α t
            * (t ^ (-M - 1) * (t ^ M * deriv ψ t - M * t ^ (M - 1) * ψ t)) from by ring]
    rw [hcomb M]
  have htermP : srcP α m c t * Fgen α P ψ t
      = c t * pwt α t * (deriv ψ t * t ^ (-1:ℝ) - P * ψ t * t ^ (-2:ℝ)) := by
    rw [hsrcP, Fgen]
    rw [show (c t * t ^ (-P - 1)) * (pwt α t * (t ^ P * deriv ψ t - P * t ^ (P - 1) * ψ t))
        = c t * pwt α t
            * (t ^ (-P - 1) * (t ^ P * deriv ψ t - P * t ^ (P - 1) * ψ t)) from by ring]
    rw [hcomb P]
  -- The difference of the two brackets kills the `deriv ψ t` terms and leaves `(P - M)ψ t/t²`.
  have hdiff : (deriv ψ t * t ^ (-1:ℝ) - M * ψ t * t ^ (-2:ℝ))
      - (deriv ψ t * t ^ (-1:ℝ) - P * ψ t * t ^ (-2:ℝ))
      = (P - M) * ψ t * t ^ (-2:ℝ) := by ring
  set D : ℝ := (4 * (m : ℝ) + 5) / α with hD
  have hPM : P - M = D := by rw [hP, hM, hD]; field_simp; ring
  have hαD : α ^ 2 * D = α * (4 * (m : ℝ) + 5) := by rw [hD]; field_simp
  have ht2 : t ^ 2 * t ^ (-2:ℝ) = 1 := by
    rw [show t ^ (-2:ℝ) = (t ^ (2:ℕ))⁻¹ by
          rw [Real.rpow_neg (le_of_lt ht), Real.rpow_two]]
    exact mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt ht))
  calc srcM α m c t * Fgen α (sM α m) ψ t - srcP α m c t * Fgen α (sP α m) ψ t
      = c t * pwt α t *
          ((deriv ψ t * t ^ (-1:ℝ) - M * ψ t * t ^ (-2:ℝ))
            - (deriv ψ t * t ^ (-1:ℝ) - P * ψ t * t ^ (-2:ℝ))) := by
        rw [hsM, hsP, htermM, htermP, ← mul_sub]
    _ = c t * pwt α t * ((P - M) * ψ t * t ^ (-2:ℝ)) := by rw [hdiff]
    _ = α * (4 * (m : ℝ) + 5) * (c t * ψ t * wgt α t) := by
        rw [hPM, pwt]
        calc c t * (α ^ 2 * (t ^ 2 * wgt α t)) * (D * ψ t * t ^ (-2:ℝ))
            = (α ^ 2 * D) * (t ^ 2 * t ^ (-2:ℝ)) * (c t * ψ t * wgt α t) := by ring
          _ = (α * (4 * (m : ℝ) + 5)) * 1 * (c t * ψ t * wgt α t) := by rw [hαD, ht2]
          _ = α * (4 * (m : ℝ) + 5) * (c t * ψ t * wgt α t) := by ring

end Work.FTS.H2.ModalSolR.RGWeak
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.RGWeak.qm_formula =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR.RGWeak

open Work.EllipticEst.ModalSolution.RadGreenWeak
open Work.FTS.PhiStar.Radial
open MeasureTheory Set Filter
open scoped Real Topology

theorem qm_formula {α : ℝ} (hα : 0 < α) (m : ℕ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hvan : ∀ z : ℝ, z ∉ Set.Ioo a b → ψ z = 0 ∧ deriv ψ z = 0) :
    ∀ t ∈ Set.Icc a b,
      (∫ z in t..b, z ^ (Work.EllipticEst.ModalSolution.RadGreenWeak.sM α m) *
          (Work.EllipticEst.ModalSolution.RadGreenWeak.wgt α z *
            Work.EllipticEst.ModalSolution.RadGreenWeak.Lneg α ψ z))
        = - Work.FTS.PhiStar.Radial.lamR m *
            (∫ z in t..b, z ^ (Work.EllipticEst.ModalSolution.RadGreenWeak.sM α m) *
              (Work.EllipticEst.ModalSolution.RadGreenWeak.wgt α z * ψ z))
          + Work.FTS.H2.ModalSolR.RGWeak.Fgen α (Work.EllipticEst.ModalSolution.RadGreenWeak.sM α m) ψ t := by
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
  have htb : t ≤ b := ht.2
  have hψon : ContDiffOn ℝ 2 ψ (Set.Ioi 0) := hψ.contDiffOn
  have hs : α ^ 2 * (sM α m) ^ 2 + 5 * α * (sM α m) = lamR m :=
    indicial_sM (ne_of_gt hα) m
  have hFb : Fgen α (sM α m) ψ b = 0 := by
    obtain ⟨h0, h1⟩ := hvan b (by simp [Set.mem_Ioo])
    exact Fgen_eq_zero h0 h1
  have hsub : Set.Icc t b ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ht0 hz.1
  have hpow : ContinuousOn (fun z : ℝ => z ^ (sM α m)) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (sM α m) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hwgtc : ContinuousOn (wgt α) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (qW α) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hLc : ContinuousOn (Lneg α ψ) (Set.Ioi 0) :=
    Work.EllipticEst.ModalSolution.RGW.Lneg_continuousOn α hψon
  have hcontA : ContinuousOn (fun z => z ^ (sM α m) * (wgt α z * Lneg α ψ z)) (Set.Icc t b) :=
    (hpow.mono hsub).mul ((hwgtc.mono hsub).mul (hLc.mono hsub))
  have hcontB : ContinuousOn (fun z => z ^ (sM α m) * wgt α z * ψ z) (Set.Icc t b) :=
    ((hpow.mono hsub).mul (hwgtc.mono hsub)).mul
      ((hψ.continuous.continuousOn).mono hsub)
  have hIntA : IntervalIntegrable (fun z => z ^ (sM α m) * (wgt α z * Lneg α ψ z)) volume t b :=
    hcontA.intervalIntegrable_of_Icc htb
  have hIntB : IntervalIntegrable (fun z => z ^ (sM α m) * wgt α z * ψ z) volume t b :=
    hcontB.intervalIntegrable_of_Icc htb
  have hIntBc : IntervalIntegrable (fun z => lamR m * (z ^ (sM α m) * wgt α z * ψ z)) volume t b :=
    hIntB.const_mul (lamR m)
  have hIntD : IntervalIntegrable
      (fun z => z ^ (sM α m) * (wgt α z * Lneg α ψ z)
        + lamR m * (z ^ (sM α m) * wgt α z * ψ z)) volume t b :=
    hIntA.add hIntBc
  have hderiv : ∀ x ∈ Set.uIcc t b,
      HasDerivAt (Fgen α (sM α m) ψ)
        (-(x ^ (sM α m) * (wgt α x * Lneg α ψ x)
          + lamR m * (x ^ (sM α m) * wgt α x * ψ x))) x := by
    intro x hx
    rw [Set.uIcc_of_le htb] at hx
    exact Fgen_hasDerivAt hα hs hψon x (lt_of_lt_of_le ht0 hx.1)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hIntD.neg
  have hsplit :
      ∫ x in t..b, -(x ^ (sM α m) * (wgt α x * Lneg α ψ x)
          + lamR m * (x ^ (sM α m) * wgt α x * ψ x))
        = -((∫ x in t..b, x ^ (sM α m) * (wgt α x * Lneg α ψ x))
            + lamR m * (∫ x in t..b, x ^ (sM α m) * wgt α x * ψ x)) := by
    rw [intervalIntegral.integral_neg,
        intervalIntegral.integral_add (f := fun z => z ^ (sM α m) * (wgt α z * Lneg α ψ z))
          (g := fun z => lamR m * (z ^ (sM α m) * wgt α z * ψ z)) hIntA hIntBc,
        intervalIntegral.integral_const_mul]
  have hval : ∫ x in t..b, x ^ (sM α m) * (wgt α x * Lneg α ψ x)
      = Fgen α (sM α m) ψ t - lamR m * (∫ x in t..b, x ^ (sM α m) * wgt α x * ψ x) := by
    have h := hFTC
    rw [hsplit, hFb, zero_sub] at h
    linarith
  have hcongr : ∫ x in t..b, x ^ (sM α m) * (wgt α x * ψ x)
      = ∫ x in t..b, x ^ (sM α m) * wgt α x * ψ x :=
    intervalIntegral.integral_congr (fun x _ => by ring)
  rw [hcongr, hval]
  ring

end Work.FTS.H2.ModalSolR.RGWeak
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.RGWeak.qp_formula =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR.RGWeak

open Work.EllipticEst.ModalSolution.RadGreenWeak
open Work.FTS.PhiStar.Radial
open MeasureTheory Set Filter
open scoped Real Topology

theorem qp_formula {α : ℝ} (hα : 0 < α) (m : ℕ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hvan : ∀ z : ℝ, z ∉ Set.Ioo a b → ψ z = 0 ∧ deriv ψ z = 0) :
    ∀ t ∈ Set.Icc a b,
      (∫ z in a..t, z ^ (Work.EllipticEst.ModalSolution.RadGreenWeak.sP α m) *
          (Work.EllipticEst.ModalSolution.RadGreenWeak.wgt α z *
            Work.EllipticEst.ModalSolution.RadGreenWeak.Lneg α ψ z))
        = - Work.FTS.PhiStar.Radial.lamR m *
            (∫ z in a..t, z ^ (Work.EllipticEst.ModalSolution.RadGreenWeak.sP α m) *
              (Work.EllipticEst.ModalSolution.RadGreenWeak.wgt α z * ψ z))
          - Work.FTS.H2.ModalSolR.RGWeak.Fgen α (Work.EllipticEst.ModalSolution.RadGreenWeak.sP α m) ψ t := by
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
  have hat : a ≤ t := ht.1
  have hψon : ContDiffOn ℝ 2 ψ (Set.Ioi 0) := hψ.contDiffOn
  have hs : α ^ 2 * (sP α m) ^ 2 + 5 * α * (sP α m) = lamR m :=
    indicial_sP (ne_of_gt hα) m
  have hFa : Fgen α (sP α m) ψ a = 0 := by
    obtain ⟨h0, h1⟩ := hvan a (by simp [Set.mem_Ioo])
    exact Fgen_eq_zero h0 h1
  have hsub : Set.Icc a t ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ha hz.1
  have hpow : ContinuousOn (fun z : ℝ => z ^ (sP α m)) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (sP α m) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hwgtc : ContinuousOn (wgt α) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (qW α) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hLc : ContinuousOn (Lneg α ψ) (Set.Ioi 0) :=
    Work.EllipticEst.ModalSolution.RGW.Lneg_continuousOn α hψon
  have hcontA : ContinuousOn (fun z => z ^ (sP α m) * (wgt α z * Lneg α ψ z))
      (Set.Icc a t) :=
    (hpow.mono hsub).mul ((hwgtc.mono hsub).mul (hLc.mono hsub))
  have hcontB : ContinuousOn (fun z => z ^ (sP α m) * wgt α z * ψ z) (Set.Icc a t) :=
    ((hpow.mono hsub).mul (hwgtc.mono hsub)).mul
      ((hψ.continuous.continuousOn).mono hsub)
  have hIntA : IntervalIntegrable
      (fun z => z ^ (sP α m) * (wgt α z * Lneg α ψ z)) volume a t :=
    hcontA.intervalIntegrable_of_Icc hat
  have hIntB : IntervalIntegrable (fun z => z ^ (sP α m) * wgt α z * ψ z) volume a t :=
    hcontB.intervalIntegrable_of_Icc hat
  have hIntBc : IntervalIntegrable
      (fun z => lamR m * (z ^ (sP α m) * wgt α z * ψ z)) volume a t :=
    hIntB.const_mul (lamR m)
  have hIntD : IntervalIntegrable
      (fun z => z ^ (sP α m) * (wgt α z * Lneg α ψ z)
        + lamR m * (z ^ (sP α m) * wgt α z * ψ z)) volume a t :=
    hIntA.add hIntBc
  have hderiv : ∀ x ∈ Set.uIcc a t,
      HasDerivAt (Fgen α (sP α m) ψ)
        (-(x ^ (sP α m) * (wgt α x * Lneg α ψ x)
          + lamR m * (x ^ (sP α m) * wgt α x * ψ x))) x := by
    intro x hx
    rw [Set.uIcc_of_le hat] at hx
    exact Fgen_hasDerivAt hα hs hψon x (lt_of_lt_of_le ha hx.1)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hIntD.neg
  have hsplit :
      ∫ x in a..t, -(x ^ (sP α m) * (wgt α x * Lneg α ψ x)
          + lamR m * (x ^ (sP α m) * wgt α x * ψ x))
        = -((∫ x in a..t, x ^ (sP α m) * (wgt α x * Lneg α ψ x))
            + lamR m * (∫ x in a..t, x ^ (sP α m) * wgt α x * ψ x)) := by
    rw [intervalIntegral.integral_neg,
        intervalIntegral.integral_add (f := fun z => z ^ (sP α m) * (wgt α z * Lneg α ψ z))
          (g := fun z => lamR m * (z ^ (sP α m) * wgt α z * ψ z)) hIntA hIntBc,
        intervalIntegral.integral_const_mul]
  have hval : ∫ x in a..t, x ^ (sP α m) * (wgt α x * Lneg α ψ x)
      = - lamR m * (∫ x in a..t, x ^ (sP α m) * wgt α x * ψ x)
        - Fgen α (sP α m) ψ t := by
    have h := hFTC
    rw [hsplit, hFa, sub_zero] at h
    linarith
  have hcongr : ∫ x in a..t, x ^ (sP α m) * (wgt α x * ψ x)
      = ∫ x in a..t, x ^ (sP α m) * wgt α x * ψ x :=
    intervalIntegral.integral_congr (fun x _ => by ring)
  rw [hcongr, hval]

end Work.FTS.H2.ModalSolR.RGWeak
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.tailFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

open scoped Real
open MeasureTheory Set

/-- Every basis function `eFam m = cos · C^{(3/2)}_{2m+1}(sin ·)` is `C²`: it is the
composition of a polynomial with `sin` and `cos`. -/
lemma eFam_contDiff_two (m : ℕ) : ContDiff ℝ 2 (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  rw [show Work.FTS.PhiStar.Gegenbauer.eFam m
      = (fun θ : ℝ => Real.cos θ
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)) from rfl]
  refine Real.contDiff_cos.mul ?_
  exact ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).of_le (by norm_num)).comp
    Real.contDiff_sin

/-- The tail data of a finite modal sum `θ ↦ ∑_{m ∈ s} a m · eFam m θ`: it is `C²` on `Iθ`,
it vanishes at both endpoints (each `eFam m` does), and the three weights `cos θ`, its square
and its square divided by `cos θ` of the sum, of its derivative and of `sum / cos θ` are all
integrable on `Iθ`.  (The last one is integrable because the quotient is bounded: on `Iθ`
the equality `eFam m θ = cos θ · gC (2m+1) (sin θ)` cancels the `cos θ`; where `cos θ`
vanishes — only at `θ = π/2` — both sides of the integrand are `0`.) -/
theorem tailFacts (a : ℕ → ℝ) (s : Finset ℕ) :
    ContDiffOn ℝ 2 (fun θ => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        (Set.Icc 0 (Real.pi / 2))
    ∧ (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m 0) = 0
    ∧ (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2)) = 0
    ∧ MeasureTheory.IntegrableOn
        (fun θ => (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
          * Real.cos θ) Work.Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ')
            θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn
        (fun θ => ((∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) / Real.cos θ) ^ 2
          * Real.cos θ) Work.Spaces.Iθ := by
  have hF : ContDiff ℝ 2
      (fun θ => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
    ContDiff.sum (fun m _ => contDiff_const.mul (eFam_contDiff_two m))
  refine ⟨hF.contDiffOn, ?_, ?_, ?_, ?_, ?_⟩
  · -- vanishing at `θ = 0`
    simp only [Work.FTS.PhiStar.Series.eFam_zero, mul_zero, Finset.sum_const_zero]
  · -- vanishing at `θ = π/2`
    simp only [Work.FTS.PhiStar.Series.eFam_pi_half, mul_zero, Finset.sum_const_zero]
  · -- integrability of the `cos θ`-weighted square
    exact (((hF.continuous.pow 2).mul Real.continuous_cos).continuousOn).integrableOn_compact
      isCompact_Icc
  · -- integrability of the `cos θ`-weighted square of the derivative
    have hderiv : Continuous (deriv
        (fun θ => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)) :=
      hF.continuous_deriv (by norm_num)
    exact (((hderiv.pow 2).mul Real.continuous_cos).continuousOn).integrableOn_compact
      isCompact_Icc
  · -- integrability of the `cos θ`-weighted square of the quotient by `cos θ`
    set G : ℝ → ℝ :=
      fun θ => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
      with hGdef
    have hGcont : Continuous G := by
      refine continuous_finsetSum _ (fun m _ => ?_)
      exact continuous_const.mul
        (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
          Real.continuous_sin)
    refine MeasureTheory.IntegrableOn.congr_fun
      ((((hGcont.pow 2).mul Real.continuous_cos).continuousOn).integrableOn_compact
        isCompact_Icc) ?_ measurableSet_Icc
    intro θ hθ
    change G θ ^ 2 * Real.cos θ
        = ((∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) / Real.cos θ) ^ 2
          * Real.cos θ
    have hFG : (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        = Real.cos θ * G θ := by
      rw [hGdef, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      simp only [Work.FTS.PhiStar.Gegenbauer.eFam]
      ring
    by_cases hc : Real.cos θ = 0
    · -- the only zero of `cos` on `Iθ` is `θ = π/2`, where both sides vanish
      have hθpi : θ = Real.pi / 2 := by
        by_contra hne
        have hlt : θ < Real.pi / 2 := lt_of_le_of_ne hθ.2 hne
        have hmem : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
          ⟨by linarith [hθ.1, Real.pi_pos], hlt⟩
        have hpos := Real.cos_pos_of_mem_Ioo hmem
        linarith [hc]
      subst hθpi
      simp only [hFG, hc, zero_mul, mul_zero]
    · rw [hFG, mul_div_cancel_left₀ _ hc]

end Work.FTS.H2.ModalSolR
end
-- ===== merged: Submission.Work.FTS.H2.MuEstimateScaled =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

/-- `y ≤ z → α^z ≤ α^y` for `0 < α ≤ 1`; a private copy of
`Work.Construction.rpow_le_of_le_one` to avoid importing the `Apriori` chapter. -/
private theorem rpow_le_of_le_one' {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {y z : ℝ}
    (hyz : y ≤ z) : α ^ z ≤ α ^ y := by
  have h : α ^ z = α ^ y * α ^ (z - y) := by
    rw [← Real.rpow_add hα]
    ring_nf
  rw [h]
  calc α ^ y * α ^ (z - y) ≤ α ^ y * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hα.le y)
        exact Real.rpow_le_one hα.le hα1 (by linarith)
    _ = α ^ y := by ring

/-- `1 ≤ α^c` for `c ≤ 0` when `0 < α ≤ 1`. -/
private theorem one_le_rpow_of_nonpos {α c : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hc : c ≤ 0) :
    1 ≤ α ^ c := by
  have h := rpow_le_of_le_one' hα hα1 (show c ≤ (0 : ℝ) from hc)
  rwa [Real.rpow_zero] at h

/-- The pure arithmetic of the *scaled* `muestimate`: for `0 < α ≤ 1` and `X ≥ 0`,
`(1/(2α))(2α² + 2α^{-1/2}X + 2α^{-3/2}X² + X) ≤ 4(α + α^{-3/2}X + α^{-5/2}X²)`.
The middle factor `α^{-1/2}X` is the `√α·X` of the scaled hypothesis, since
`√α = α^{1/2} ≤ α^{-1/2}` for `α ≤ 1`. -/
private theorem mu_arith_scaled {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    (1 / (2 * α)) * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
        + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X)
      ≤ 4 * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by
  have hX2 : 0 ≤ X ^ 2 := sq_nonneg X
  have hone1 : 1 ≤ α ^ (-(1 / 2 : ℝ)) :=
    one_le_rpow_of_nonpos hα hα1 (by norm_num)
  have e1 : α * α ^ (-(3 / 2 : ℝ)) = α ^ (-(1 / 2 : ℝ)) := by
    nth_rewrite 1 [← Real.rpow_one α]
    rw [← Real.rpow_add hα]
    norm_num
  have e2 : α * α ^ (-(5 / 2 : ℝ)) = α ^ (-(3 / 2 : ℝ)) := by
    nth_rewrite 1 [← Real.rpow_one α]
    rw [← Real.rpow_add hα]
    norm_num
  have hA : 2 * α ^ 2 ≤ 8 * α ^ 2 := by linarith [sq_nonneg α]
  have hXle : X ≤ α ^ (-(1 / 2 : ℝ)) * X := by
    calc X = 1 * X := by ring
      _ ≤ α ^ (-(1 / 2 : ℝ)) * X := mul_le_mul_of_nonneg_right hone1 hX
  have hB : 2 * (α ^ (-(1 / 2 : ℝ)) * X) + X ≤ 8 * (α ^ (-(1 / 2 : ℝ)) * X) := by
    linarith
  have hC : 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) ≤ 8 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
    have hW : 0 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) hX2
    exact mul_le_mul_of_nonneg_right (by norm_num) hW
  have hfin : 8 * (α * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2))
      = 8 * α ^ 2 + 8 * (α ^ (-(1 / 2 : ℝ)) * X) + 8 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
    rw [show α * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2)
        = α * α + (α * α ^ (-(3 / 2 : ℝ))) * X + (α * α ^ (-(5 / 2 : ℝ))) * X ^ 2 by ring]
    rw [e1, e2]
    ring
  have hB8 : 2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X) + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X
      ≤ 8 * (α * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2)) := by
    linarith [hA, hB, hC, hfin]
  have hkey : (1 / (2 * α)) * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
        + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X)
      ≤ (1 / (2 * α))
        * (8 * (α * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2))) :=
    mul_le_mul_of_nonneg_left hB8 (by positivity)
  have hsimp : (1 / (2 * α))
        * (8 * (α * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2)))
      = 4 * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by
    field_simp
    ring
  linarith [hkey, hsimp]

/-- The triangle inequality `|(1/(2α))((A+B) - Cc)| ≤ (1/(2α)) C₀ (2α² + 2α^{-1/2}X + 2α^{-3/2}X² + X)`
with `X ≥ 0`, from the three scaled hypotheses. -/
private theorem core (C₀ α A B Cc X : ℝ) (hC₀ : 0 < C₀) (hα : 0 < α) (hα1 : α ≤ 1)
    (hX : 0 ≤ X)
    (h1 : |A| ≤ C₀ * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2))
    (h2 : |B| ≤ C₀ * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2))
    (h3 : |Cc| ≤ C₀ * X) :
    |(1 / (2 * α)) * (A + B) - (1 / (2 * α)) * Cc|
      ≤ 4 * C₀ * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by
  -- `√α = α^{1/2} ≤ α^{-1/2}` for `0 < α ≤ 1`
  have hsqrt : Real.sqrt α ≤ α ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    exact rpow_le_of_le_one' hα hα1 (by norm_num)
  have hSX : Real.sqrt α * X ≤ α ^ (-(1 / 2 : ℝ)) * X :=
    mul_le_mul_of_nonneg_right hsqrt hX
  have h1' : |A| ≤ C₀ * (α ^ 2 + α ^ (-(1 / 2 : ℝ)) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) :=
    le_trans h1 (mul_le_mul_of_nonneg_left (by linarith) hC₀.le)
  have h2' : |B| ≤ C₀ * (α ^ 2 + α ^ (-(1 / 2 : ℝ)) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) :=
    le_trans h2 (mul_le_mul_of_nonneg_left (by linarith) hC₀.le)
  -- triangle inequality for the three integrals
  have htri : |A + B - Cc| ≤ |A| + |B| + |Cc| := by
    calc |A + B - Cc| = |(A + B) + -Cc| := by ring_nf
      _ ≤ |A + B| + |-Cc| := abs_add_le _ _
      _ ≤ |A| + |B| + |Cc| := by
          rw [abs_neg]
          linarith [abs_add_le A B]
  have hstep : |A + B - Cc|
      ≤ C₀ * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
          + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X) := by
    have hsum : |A| + |B| + |Cc|
        ≤ C₀ * (α ^ 2 + α ^ (-(1 / 2 : ℝ)) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)
          + C₀ * (α ^ 2 + α ^ (-(1 / 2 : ℝ)) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)
          + C₀ * X := by
      linarith [h1', h2', h3]
    have heq : C₀ * (α ^ 2 + α ^ (-(1 / 2 : ℝ)) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)
          + C₀ * (α ^ 2 + α ^ (-(1 / 2 : ℝ)) * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) + C₀ * X
        = C₀ * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
            + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X) := by ring
    linarith [htri, hsum, heq]
  have hbound : |(1 / (2 * α)) * (A + B) - (1 / (2 * α)) * Cc|
      ≤ (1 / (2 * α)) * (C₀ * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
          + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X)) := by
    have hrs : (1 / (2 * α)) * (A + B) - (1 / (2 * α)) * Cc
        = (1 / (2 * α)) * ((A + B) - Cc) := by ring
    rw [hrs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * α))]
    exact mul_le_mul_of_nonneg_left hstep (by positivity)
  have harith := mu_arith_scaled hα hα1 hX
  have hfac : (1 / (2 * α)) * (C₀ * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
        + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X))
      = C₀ * ((1 / (2 * α)) * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
        + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X)) := by ring
  have hfinal : C₀ * ((1 / (2 * α)) * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
        + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X))
      ≤ 4 * C₀ * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by
    have h := mul_le_mul_of_nonneg_left harith hC₀.le
    calc C₀ * ((1 / (2 * α)) * (2 * α ^ 2 + 2 * (α ^ (-(1 / 2 : ℝ)) * X)
          + 2 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) + X))
        ≤ C₀ * (4 * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2)) := h
      _ = 4 * C₀ * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by ring
  linarith [hbound, hfac, hfinal]


end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.AngSlot.sfun_Lop_iter_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.CoreAux.AngSlot

open scoped Real
open Work.FTS.PhiStar.LinvFlat

/-- The basic angular profile `S2 θ = sin (2θ)`. -/
private noncomputable def S2 : ℝ → ℝ := fun θ => Real.sin (2 * θ)

/-- The constant function `1` is a trigonometric polynomial. -/
private lemma TP_one : LopTrig.TP (fun _ : ℝ => (1 : ℝ)) := by
  have h : (fun θ : ℝ => Real.sin (2 * θ) * Real.sin (2 * θ)
      + Real.cos (2 * θ) * Real.cos (2 * θ)) = (fun _ : ℝ => (1 : ℝ)) := by
    funext θ
    rw [← sq (Real.sin (2 * θ)), ← sq (Real.cos (2 * θ)), Real.sin_sq_add_cos_sq]
  rw [← h]
  exact LopTrig.TP.add (LopTrig.TP.mul LopTrig.TP.sin2 LopTrig.TP.sin2)
    (LopTrig.TP.mul LopTrig.TP.cos2 LopTrig.TP.cos2)

/-- **Divisibility of the `Lop`-iterates of `sin (2·)`.**  For every `r` there is a trigonometric
polynomial `P` with `Lop^[r] (sin 2·) = sin (2·) · P` as functions. -/
private lemma Lop_iter_sin2_div (r : ℕ) : ∃ P : ℝ → ℝ,
    LopTrig.TP P ∧ (Work.Spaces.Lop^[r]) S2 = S2 * P := by
  induction r with
  | zero =>
      refine ⟨fun _ => (1 : ℝ), TP_one, ?_⟩
      funext θ
      show S2 θ = S2 θ * 1
      ring
  | succ r ih =>
      obtain ⟨P, hP, hdiv⟩ := ih
      refine ⟨deriv S2 * P + S2 * deriv P, ?_, ?_⟩
      · exact LopTrig.TP.add (LopTrig.TP.mul (LopTrig.TP_deriv LopTrig.TP.sin2) hP)
          (LopTrig.TP.mul LopTrig.TP.sin2 (LopTrig.TP_deriv hP))
      · rw [Function.iterate_succ_apply', hdiv]
        funext θ
        rw [show Work.Spaces.Lop (S2 * P) θ = S2 θ * deriv (S2 * P) θ from rfl,
          LopTrig.deriv_mul_TP (f := S2) (g := P) LopTrig.TP.sin2 hP]
        simp only [Pi.add_apply, Pi.mul_apply]

/-- **The iterates of `Lop` applied to `sin (2·)` are divisible by `sin (2·)`, with a constant
uniform for the finitely many orders `≤ n`.**

With `Lop u = sin(2θ)·u'` one has `Lop^r (sin 2·) = sin(2·) · P_r` for a trigonometric polynomial
`P_r` (the class `Work.FTS.PhiStar.LinvFlat.LopTrig.TP` of
`Submission/Work/FTS/PhiStar/LinvFlat/Lop_iter_sin_cos_bound.lean` is closed under `Lop` and under
`deriv`), hence the bound.  This is the angular coefficient bound used by the Leibniz expansion
of `D_θ^j` in terms of `∂_θ`-slots. -/
theorem sfun_Lop_iter_le (n : ℕ) : ∃ A : ℝ, 0 < A ∧ ∀ r : ℕ, r ≤ n →
    ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Spaces.Lop^[r]) (fun θ' => Real.sin (2 * θ')) θ| ≤ A * Real.sin (2 * θ) := by
  -- choose the trigonometric polynomials `P r` dividing the iterates
  have hex : ∀ r : ℕ, ∃ P : ℝ → ℝ, LopTrig.TP P ∧ (Work.Spaces.Lop^[r]) S2 = S2 * P :=
    Lop_iter_sin2_div
  choose P hP using hex
  -- and bound each of them
  have hbdd : ∀ r : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ θ : ℝ, |P r θ| ≤ M :=
    fun r => LopTrig.TP_bdd (hP r).1
  choose M hM using hbdd
  refine ⟨1 + ∑ s ∈ Finset.range (n + 1), M s, ?_, ?_⟩
  · have hnn : 0 ≤ ∑ r ∈ Finset.range (n + 1), M r :=
      Finset.sum_nonneg fun r _ => (hM r).1
    linarith
  · intro r hr θ hθ
    have hsin : 0 ≤ Real.sin (2 * θ) := by
      refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
      · have : (0 : ℝ) ≤ θ := hθ.1
        linarith
      · have : θ ≤ Real.pi / 2 := hθ.2
        linarith
    have hdivr : (Work.Spaces.Lop^[r]) (fun θ' : ℝ => Real.sin (2 * θ')) θ
        = Real.sin (2 * θ) * P r θ := by
      have h1 : (fun θ' : ℝ => Real.sin (2 * θ')) = S2 := rfl
      rw [h1, (hP r).2]
      rfl
    have hMr : M r ≤ ∑ s ∈ Finset.range (n + 1), M s :=
      Finset.single_le_sum (fun i _ => (hM i).1) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
    have hA : M r ≤ 1 + ∑ s ∈ Finset.range (n + 1), M s := by
      have hnn : 0 ≤ ∑ s ∈ Finset.range (n + 1), M s :=
        Finset.sum_nonneg fun s _ => (hM s).1
      linarith
    rw [hdivr, abs_mul, abs_of_nonneg hsin]
    calc Real.sin (2 * θ) * |P r θ| ≤ Real.sin (2 * θ) * M r :=
          mul_le_mul_of_nonneg_left ((hM r).2 θ) hsin
      _ ≤ Real.sin (2 * θ) * (1 + ∑ s ∈ Finset.range (n + 1), M s) :=
          mul_le_mul_of_nonneg_left hA hsin
      _ = (1 + ∑ s ∈ Finset.range (n + 1), M s) * Real.sin (2 * θ) := by ring

end Work.FTS.PhiStar.CoreAux.AngSlot
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.LopIter_continuousOn_of_contDiff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.CoreAux

/-- **The regularity bookkeeping of the iterated angular operator.**  If `u` is of class `C^{p+i}`
on `ℝ` then `Lop^[i] u` is of class `C^p`: each iteration `Lop u = sin(2·) · u'` costs exactly
one order of differentiability. -/
theorem Lop_iter_contDiff (i p : ℕ) (u : ℝ → ℝ) (h : ContDiff ℝ (p + i : ℕ) u) :
    ContDiff ℝ (p : ℕ) (Work.Spaces.Lop^[i] u) := by
  induction i generalizing p with
  | zero => simpa using h
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    -- `h` has order `p + (i+1)`; rewrite it as `(p+1) + i` to apply the induction hypothesis
    -- with the shifted `p + 1`.
    have h' : ContDiff ℝ (p + 1 + i : ℕ) u := (show p + (i + 1) = p + 1 + i by omega) ▸ h
    have hd : ContDiff ℝ (p + 1 : ℕ) (Work.Spaces.Lop^[i] u) := ih (p + 1) h'
    have hdp : ContDiff ℝ (p : ℕ) (deriv (Work.Spaces.Lop^[i] u)) := ContDiff.deriv' hd
    have hsin : ContDiff ℝ (p : ℕ) (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
    change ContDiff ℝ (p : ℕ)
      (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Lop^[i] u) θ)
    exact hsin.mul hdp

theorem LopIter_continuousOn_of_contDiff (m : ℕ) (c : ℝ → ℝ) (hc : ContDiff ℝ (m : ℕ∞) c) : ∀ i ≤ m, ContinuousOn (Work.FTS.EllipticEst.LopIter i c) Work.Spaces.Iθ := by
  intro i hi
  -- Regard `hc` as a `C^m` hypothesis with `m` cast from `ℕ`, and split `m = (m - i) + i`.
  have hci : ContDiff ℝ (m : ℕ) c := hc
  have h' : ContDiff ℝ ((m - i) + i : ℕ) c := by
    rw [Nat.sub_add_cancel hi]; exact hci
  have hcd : ContDiff ℝ (m - i : ℕ) (Work.Spaces.Lop^[i] c) := Lop_iter_contDiff i (m - i) c h'
  change ContinuousOn (Work.Spaces.Lop^[i] c) Work.Spaces.Iθ
  exact hcd.continuous.continuousOn

end Work.FTS.PhiStar.CoreAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.MomentLamEFam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

/-- The `λ_m`-weighted eigenfunction `λ_m e_m(θ)` has vanishing moment against `sin θ cos²θ` over
`Iθ = [0, π/2]`, and the corresponding integrand is integrable on `Iθ`.

This is the `m`-th component of the *moment* condition

  `∫_θ (λ_m e_m(θ)) · sin θ cos²θ dθ = 0`,

which is what makes the kernel direction of `Lzero` (i.e. `m = 0`) drop out of every mode
expansion.

The reason is the orthogonality `eFam_orthogonal`: `Iθ` is `[0, π/2]`, which differs from the
integration range `(0, π/2)` only by the two endpoints (a null set), and pointwise

  `λ_m e_m(θ) · sin θ cos²θ = (λ_m / 3) · e_m(θ) · e_0(θ) · cos θ`

because `e_0(θ) = 3 sin θ cos θ` (`eFam_zero_apply`) and the self-adjoint weight of the family is
`cos θ dθ`.  For `m ≠ 0` the last integral vanishes by `eFam_orthogonal`; for `m = 0` it does not,
but then the prefactor `λ_0 = 0` kills it.  Integrability is continuity on the compact interval
`Iθ`: `e_m(θ) = cos θ · C^{(3/2)}_{2m+1}(sin θ)` is a polynomial in `sin θ, cos θ`. -/
theorem MomentLamEFam (m : ℕ) :
    (∫ θ in Work.Spaces.Iθ,
      (Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * Work.Elliptic.sinCos2 θ) = 0
    ∧ MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  constructor
  · -- the vanishing of the moment: reduce to the orthogonality of `eFam m` against `eFam 0`
    have hkey : Work.FTS.PhiStar.Gegenbauer.lam m *
        (∫ θ in (0 : ℝ)..(Real.pi / 2),
          Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ
            * Real.cos θ) = 0 := by
      by_cases hm : m = 0
      · -- `m = 0`: the prefactor `lam 0 = 0` kills the term (the `m = 0` moment does not vanish)
        subst hm
        simp [Work.FTS.PhiStar.Gegenbauer.lam]
      · -- `m ≠ 0`: orthogonality of the eigenfunctions with respect to `cos θ dθ`
        rw [Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal m 0 hm, mul_zero]
    -- the two integrands differ by the pointwise identity `e_0(θ) cos θ = 3 sin θ cos²θ`
    have hpt : ∀ θ : ℝ,
        (Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            * Work.Elliptic.sinCos2 θ
          = (Work.FTS.PhiStar.Gegenbauer.lam m / 3)
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ
                * Real.cos θ) := by
      intro θ
      rw [Work.FTS.PhiStar.Series.eFam_zero_apply]
      simp only [Work.Elliptic.sinCos2]
      ring
    have hpile : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    -- move from the closed set `Iθ = Icc 0 (π/2)` to the interval integral `0..π/2`
    have hmain : (∫ θ in Work.Spaces.Iθ,
          (Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            * Work.Elliptic.sinCos2 θ)
        = (Work.FTS.PhiStar.Gegenbauer.lam m / 3)
          * (∫ θ in (0 : ℝ)..(Real.pi / 2),
              Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ
                * Real.cos θ) := by
      rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
        (intervalIntegral.integral_of_le hpile).symm]
      rw [show (∫ θ in (0 : ℝ)..(Real.pi / 2),
            (Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
              * Work.Elliptic.sinCos2 θ)
          = ∫ θ in (0 : ℝ)..(Real.pi / 2),
              (Work.FTS.PhiStar.Gegenbauer.lam m / 3)
                * (Work.FTS.PhiStar.Gegenbauer.eFam m θ
                    * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ)
        from intervalIntegral.integral_congr (fun θ _ => hpt θ)]
      rw [intervalIntegral.integral_const_mul]
    rw [hmain]
    have hdiv : (Work.FTS.PhiStar.Gegenbauer.lam m / 3) *
        (∫ θ in (0 : ℝ)..(Real.pi / 2),
          Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ
            * Real.cos θ)
        = (Work.FTS.PhiStar.Gegenbauer.lam m *
          (∫ θ in (0 : ℝ)..(Real.pi / 2),
            Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ
              * Real.cos θ)) / 3 := by ring
    rw [hdiv, hkey, zero_div]
  · -- integrability: the integrand is continuous (a polynomial in `sin θ`, `cos θ`) and `Iθ`
    -- is compact
    have heFam : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
      change Continuous (fun θ : ℝ => Real.cos θ *
        Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
      exact Real.continuous_cos.mul
        ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp
          Real.continuous_sin)
    have hsinCos2 : Continuous Work.Elliptic.sinCos2 := by
      change Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)
    have hcont : Continuous (fun θ : ℝ =>
        (Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * Work.Elliptic.sinCos2 θ) :=
      (heFam.const_mul (Work.FTS.PhiStar.Gegenbauer.lam m)).mul hsinCos2
    simpa only [Work.Spaces.Iθ] using
      hcont.integrableOn_Icc (a := (0 : ℝ)) (b := Real.pi / 2)

end Work.FTS.PhiStar.FlatWAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.WeightedL2Aux.rgA_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real

namespace Work.FTS.PhiStar.Honesty.WeightedL2Aux

set_option autoImplicit false

local notation "rgQ" => Work.FTS.EllExist.rgQ
local notation "rgF1" => Work.FTS.EllExist.rgF1
local notation "rgA" => Work.FTS.EllExist.rgA

/-- `(a/t²)² = a²/t⁴`, for every `t` (both sides vanish at `t = 0`). -/
private lemma div_sq_sq (a t : ℝ) : (a / t ^ 2) ^ 2 = a ^ 2 / t ^ 4 := by
  rw [div_pow]; ring_nf

/-- `(a/t²)·t^{q+1} = a·t^{q-1}` for `t > 0`. -/
private lemma div_sq_mul_rpow (a q t : ℝ) (ht : 0 < t) :
    (a / t ^ 2) * t ^ (q + 1) = a * t ^ (q - 1) := by
  have h : t ^ 2 = t ^ (2 : ℝ) := (Real.rpow_natCast t 2).symm
  rw [h, div_eq_mul_inv, mul_assoc, ← Real.rpow_neg (le_of_lt ht) 2, ← Real.rpow_add ht]
  congr 1; ring_nf

/-- `(t^{q+1})² = t^{2q+2}` for `t > 0`. -/
private lemma rpow_add_one_sq (q t : ℝ) (ht : 0 < t) :
    (t ^ (q + 1)) ^ 2 = t ^ (2 * q + 2) := by
  have h1 : (t ^ (q + 1)) ^ 2 = (t ^ (q + 1)) ^ (2 : ℝ) :=
    (Real.rpow_natCast (t ^ (q + 1)) 2).symm
  have h2 : (t ^ (q + 1)) ^ (2 : ℝ) = t ^ ((q + 1) * (2 : ℝ)) :=
    (Real.rpow_mul ht.le (q + 1) (2 : ℝ)).symm
  rw [h1, h2]; congr 1; ring

theorem rgA_sq_le {α : ℝ} {m : ℕ} {d : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hd : AEMeasurable d)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2) (Set.Ioi 1))
    {z : ℝ} (hz : 0 < z) :
    (Work.FTS.EllExist.rgA α m d z) ^ 2
      ≤ ((∫ t in Set.Ioo (0:ℝ) 1, (d t) ^ 2 / t ^ 4)
          + (∫ t in Set.Ioi (1:ℝ), (d t) ^ 2)) * (z ^ (2 * Work.FTS.EllExist.rgQ α m + 3) / (2 * Work.FTS.EllExist.rgQ α m + 3)) := by
  have hq28 : 28 ≤ rgQ α m := Work.FTS.EllExist.rgQ_ge hα hα4 hm
  set A : ℝ := ∫ t in Set.Ioo (0:ℝ) 1, (d t) ^ 2 / t ^ 4 with hAdef
  set B : ℝ := ∫ t in Set.Ioi (1:ℝ), (d t) ^ 2 with hBdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards with t
    positivity
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards with t
    positivity
  -- the near-field weight is integrable on `(0,1]` and on `(1,z]`
  have hnear01 : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2 / t ^ 4) (Set.Ioc (0:ℝ) 1) :=
    hnear.congr_set_ae (Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := 1)).symm
  have hfar1z : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2 / t ^ 4) (Set.Ioc (1:ℝ) z) := by
    have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2) (Set.Ioc (1:ℝ) z) :=
      hfar.mono_set (fun x hx => hx.1)
    have haesm : AEStronglyMeasurable (fun t : ℝ => (d t) ^ 2 / t ^ 4)
        (volume.restrict (Set.Ioc (1:ℝ) z)) :=
      (((hd.pow_const 2).div (aemeasurable_id.pow_const 4)).restrict
        (s := Set.Ioc (1:ℝ) z)).aestronglyMeasurable
    refine MeasureTheory.Integrable.mono' hbase haesm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht4 : (0:ℝ) < t ^ 4 := by
      have : (0:ℝ) < t := lt_trans one_pos ht.1
      positivity
    have ht4one : (1:ℝ) ≤ t ^ 4 := one_le_pow₀ (n := 4) ht.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ ht4]
    nlinarith [sq_nonneg (d t), ht4one]
  -- integrability of the near-field weight on the whole `(0,z]`
  have hne_int : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2 / t ^ 4) (Set.Ioc (0:ℝ) z) := by
    rcases le_or_gt z 1 with hz1 | hz1
    · have h : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2 / t ^ 4) (Set.Ioo (0:ℝ) z) :=
        hnear.mono_set (fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hz1⟩)
      exact h.congr_set_ae (Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := z)).symm
    · rw [← Set.Ioc_union_Ioc_eq_Ioc zero_le_one hz1.le]
      exact hnear01.union hfar1z
  -- the value of the near-field integral is at most `A + B`
  have hInt_le : (∫ t in Set.Ioc (0:ℝ) z, (d t) ^ 2 / t ^ 4) ≤ A + B := by
    rcases le_or_gt z 1 with hz1 | hz1
    · have h2 : (∫ t in Set.Ioo (0:ℝ) z, (d t) ^ 2 / t ^ 4) ≤ A := by
        rw [hAdef]
        refine MeasureTheory.setIntegral_mono_set hnear ?_ ?_
        · filter_upwards with x; positivity
        · filter_upwards with x hx
          exact ⟨hx.1, lt_of_lt_of_le hx.2 hz1⟩
      rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
      linarith
    · have hdisj : Disjoint (Set.Ioc (0:ℝ) 1) (Set.Ioc (1:ℝ) z) := by
        rw [Set.disjoint_left]
        rintro x hx1 hx2
        linarith [hx1.2, hx2.1]
      rw [← Set.Ioc_union_Ioc_eq_Ioc zero_le_one hz1.le,
        MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hnear01 hfar1z]
      have hEq1 : (∫ t in Set.Ioc (0:ℝ) 1, (d t) ^ 2 / t ^ 4) = A := by
        rw [hAdef, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      have hle2 : (∫ t in Set.Ioc (1:ℝ) z, (d t) ^ 2 / t ^ 4) ≤ B := by
        have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2) (Set.Ioc (1:ℝ) z) :=
          hfar.mono_set (fun x hx => hx.1)
        have hm1 : (∫ t in Set.Ioc (1:ℝ) z, (d t) ^ 2 / t ^ 4) ≤
            ∫ t in Set.Ioc (1:ℝ) z, (d t) ^ 2 := by
          refine MeasureTheory.setIntegral_mono_on hfar1z hbase measurableSet_Ioc ?_
          intro t ht
          have ht4 : (0:ℝ) < t ^ 4 := by
            have : (0:ℝ) < t := lt_trans one_pos ht.1
            positivity
          have ht4one : (1:ℝ) ≤ t ^ 4 := one_le_pow₀ (n := 4) ht.1.le
          rw [div_le_iff₀ ht4]
          nlinarith [sq_nonneg (d t), ht4one]
        have hm2 : (∫ t in Set.Ioc (1:ℝ) z, (d t) ^ 2) ≤ B := by
          rw [hBdef]
          refine MeasureTheory.setIntegral_mono_set hfar ?_ ?_
          · filter_upwards with x; positivity
          · filter_upwards with x hx; exact hx.1
        linarith
      linarith
  -- Cauchy–Schwarz on `0..z`
  have hF1int : IntervalIntegrable (rgF1 α m d) volume (0:ℝ) z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mpr
      (Work.FTS.PhiStar.Honesty.rgF1_integrableOn_Ioc hα hα4 hm hd hnear hfar z hz)
  have hf2 : IntervalIntegrable (fun t : ℝ => (d t / t ^ 2) ^ 2) volume (0:ℝ) z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mpr
      (hne_int.congr_fun (fun t _ => (div_sq_sq (d t) t).symm) measurableSet_Ioc)
  have hg2 : IntervalIntegrable (fun t : ℝ => (t ^ (rgQ α m + 1)) ^ 2) volume (0:ℝ) z := by
    refine IntervalIntegrable.congr ?_
      (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := z)
        (r := 2 * rgQ α m + 2) (by linarith))
    intro t ht
    rw [Set.uIoc_of_le hz.le] at ht
    exact (rpow_add_one_sq (rgQ α m) t ht.1).symm
  have hfg : IntervalIntegrable (fun t : ℝ => (d t / t ^ 2) * t ^ (rgQ α m + 1)) volume (0:ℝ) z := by
    refine IntervalIntegrable.congr ?_ hF1int
    intro t ht
    rw [Set.uIoc_of_le hz.le] at ht
    show rgF1 α m d t = (d t / t ^ 2) * t ^ (rgQ α m + 1)
    rw [Work.FTS.EllExist.rgF1]
    exact (div_sq_mul_rpow (d t) (rgQ α m) t ht.1).symm
  have hcs := Work.FTS.PhiStar.Honesty.sq_intervalIntegral_mul_le hz.le hf2 hg2 hfg
  have hLHS : (∫ t in (0:ℝ)..z, (d t / t ^ 2) * t ^ (rgQ α m + 1)) = rgA α m d z := by
    show (∫ t in (0:ℝ)..z, (d t / t ^ 2) * t ^ (rgQ α m + 1)) = ∫ t in (0:ℝ)..z, rgF1 α m d t
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with t ht
    rw [Set.uIoc_of_le hz.le] at ht
    rw [Work.FTS.EllExist.rgF1]
    exact div_sq_mul_rpow (d t) (rgQ α m) t ht.1
  have hI1 : (∫ t in (0:ℝ)..z, (d t / t ^ 2) ^ 2)
      = ∫ t in Set.Ioc (0:ℝ) z, (d t) ^ 2 / t ^ 4 := by
    rw [intervalIntegral.integral_of_le hz.le]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => div_sq_sq (d t) t)
  have hI2 : (∫ t in (0:ℝ)..z, (t ^ (rgQ α m + 1)) ^ 2)
      = z ^ (2 * rgQ α m + 3) / (2 * rgQ α m + 3) := by
    have hbase := integral_rpow (a := (0:ℝ)) (b := z) (r := 2 * rgQ α m + 2) (Or.inl (by linarith))
    have hcong : (∫ t in (0:ℝ)..z, (t ^ (rgQ α m + 1)) ^ 2)
        = ∫ t in (0:ℝ)..z, t ^ (2 * rgQ α m + 2) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with t ht
      rw [Set.uIoc_of_le hz.le] at ht
      exact rpow_add_one_sq (rgQ α m) t ht.1
    rw [hcong, hbase,
      show 2 * rgQ α m + 2 + 1 = 2 * rgQ α m + 3 from by ring,
      Real.zero_rpow (by linarith : (2 * rgQ α m + 3 : ℝ) ≠ 0)]
    ring
  calc (rgA α m d z) ^ 2
      = (∫ t in (0:ℝ)..z, (d t / t ^ 2) * t ^ (rgQ α m + 1)) ^ 2 := by rw [hLHS]
    _ ≤ (∫ t in (0:ℝ)..z, (d t / t ^ 2) ^ 2)
          * (∫ t in (0:ℝ)..z, (t ^ (rgQ α m + 1)) ^ 2) := hcs
    _ = (∫ t in Set.Ioc (0:ℝ) z, (d t) ^ 2 / t ^ 4)
          * (z ^ (2 * rgQ α m + 3) / (2 * rgQ α m + 3)) := by rw [hI1, hI2]
    _ ≤ (A + B) * (z ^ (2 * rgQ α m + 3) / (2 * rgQ α m + 3)) :=
        mul_le_mul_of_nonneg_right hInt_le (by positivity)
    _ = ((∫ t in Set.Ioo (0:ℝ) 1, (d t) ^ 2 / t ^ 4)
          + (∫ t in Set.Ioi (1:ℝ), (d t) ^ 2)) * (z ^ (2 * rgQ α m + 3) / (2 * rgQ α m + 3)) := by
        rw [hAdef, hBdef]

end Work.FTS.PhiStar.Honesty.WeightedL2Aux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.integrableOn_tailSetIntegral_Ioi_one =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

open scoped ENNReal

/-- Bochner-integral form of the tail Fubini identity on `(1,∞)`: for `Q` integrable on
`(1,∞)` with `Q ≥ 0` a.e. and `t ↦ Q t * t` integrable, the function
`z ↦ ∫_z^∞ Q t dt` is integrable on `(1,∞)` and
`∫_1^∞ (∫_z^∞ Q t dt) dz = ∫_1^∞ Q t (t - 1) dt`.

The proof passes to `ℝ≥0∞`-valued `lintegral`s (`ofReal_integral_eq_lintegral_ofReal`), applies
the Tonelli-type identity `lintegral_tail_swap_Ioi_one` there, and returns with
`integral_eq_lintegral_of_nonneg_ae`; finiteness of the `lintegral` comes from the integrability
of `t ↦ Q t * (t - 1)`, which is `(Q t * t) - Q t`. -/
theorem integrableOn_tailSetIntegral_Ioi_one {Q : ℝ → ℝ}
    (hQ : MeasureTheory.IntegrableOn Q (Set.Ioi (1 : ℝ)))
    (hQnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))] Q)
    (hQt : MeasureTheory.IntegrableOn (fun t : ℝ => Q t * t) (Set.Ioi (1 : ℝ))) :
    MeasureTheory.IntegrableOn (fun z : ℝ => ∫ t in Set.Ioi z, Q t) (Set.Ioi (1 : ℝ)) ∧
      (∫ z in Set.Ioi (1 : ℝ), (∫ t in Set.Ioi z, Q t))
        = ∫ t in Set.Ioi (1 : ℝ), Q t * (t - 1) := by
  have hSmeas : MeasurableSet (Set.Ioi (1 : ℝ)) := measurableSet_Ioi
  -- (1) the integrand `t ↦ Q t * (t - 1)` is integrable: it is `(Q t * t) - Q t`
  have hQ1 : MeasureTheory.IntegrableOn (fun t : ℝ => Q t * (t - 1)) (Set.Ioi (1 : ℝ)) := by
    refine (hQt.sub hQ).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply]
    ring
  -- (2) the tail integral is nonnegative on `(1,∞)`
  have hGnn : ∀ z ∈ Set.Ioi (1 : ℝ), 0 ≤ ∫ t in Set.Ioi z, Q t := by
    intro z hz
    have hz' : (1 : ℝ) < z := hz
    have hsub : Set.Ioi z ⊆ Set.Ioi (1 : ℝ) := fun y hy => lt_trans hz' hy
    exact integral_nonneg_of_ae (ae_restrict_of_ae_restrict_of_subset hsub hQnn)
  -- (3) `ofReal` of the tail integral is the tail `lintegral` of `ofReal Q`
  have hinner : ∀ z ∈ Set.Ioi (1 : ℝ),
      ENNReal.ofReal (∫ t in Set.Ioi z, Q t)
        = ∫⁻ t in Set.Ioi z, ENNReal.ofReal (Q t) := by
    intro z hz
    have hz' : (1 : ℝ) < z := hz
    have hsub : Set.Ioi z ⊆ Set.Ioi (1 : ℝ) := fun y hy => lt_trans hz' hy
    exact ofReal_integral_eq_lintegral_ofReal (hQ.mono_set hsub)
      (ae_restrict_of_ae_restrict_of_subset hsub hQnn)
  -- (4) the `lintegral` identity (Tonelli on the triangle `1 < z < t`)
  have hkey : ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (∫ t in Set.Ioi z, Q t)
      = ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (Q t * (t - 1)) := by
    have hQme : AEMeasurable (fun t : ℝ => ENNReal.ofReal (Q t))
        (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
      hQ.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    have hswap := lintegral_tail_swap_Ioi_one
      (P := fun _ : ℝ => (1 : ENNReal)) (Q := fun t : ℝ => ENNReal.ofReal (Q t))
      aemeasurable_const hQme (fun _ => ENNReal.one_ne_top) (fun _ => ENNReal.ofReal_ne_top)
    calc ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (∫ t in Set.Ioi z, Q t)
        = ∫⁻ z in Set.Ioi (1 : ℝ), (∫⁻ t in Set.Ioi z, ENNReal.ofReal (Q t)) :=
          setLIntegral_congr_fun hSmeas (fun z hz => hinner z hz)
      _ = ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (Q t)
            * (∫⁻ z in (Set.Ioi (1 : ℝ) ∩ Set.Iio t), (1 : ENNReal)) := by
          simpa using hswap
      _ = ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (Q t * (t - 1)) := by
          apply setLIntegral_congr_fun hSmeas
          intro t ht
          have ht1 : (1 : ℝ) < t := ht
          change ENNReal.ofReal (Q t) * (∫⁻ z in (Set.Ioi (1 : ℝ) ∩ Set.Iio t), (1 : ENNReal))
            = ENNReal.ofReal (Q t * (t - 1))
          rw [show (Set.Ioi (1 : ℝ) ∩ Set.Iio t) = Set.Ioo (1 : ℝ) t from rfl,
            setLIntegral_one, Real.volume_Ioo]
          rw [← ENNReal.ofReal_mul' (show (0 : ℝ) ≤ t - 1 by linarith)]
  -- (5) the right-hand `lintegral` is finite
  have hQ1nn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))]
      (fun t : ℝ => Q t * (t - 1)) := by
    filter_upwards [hQnn, ae_restrict_mem hSmeas] with t htQ htS
    exact mul_nonneg htQ (by simp only [Set.mem_Ioi] at htS; linarith)
  have hfin : ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (Q t * (t - 1)) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal hQ1nn).mp (Integrable.hasFiniteIntegral hQ1)
  have hGlinn : ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (∫ t in Set.Ioi z, Q t) < ⊤ := by
    rw [hkey]; exact hfin
  -- (6) the tail integral is continuous (hence a.e. strongly measurable) on `(1,∞)`
  have hGcont : ContinuousOn (fun z : ℝ => ∫ t in Set.Ioi z, Q t) (Set.Ioi (1 : ℝ)) :=
    hQ.continuousOn_Ici_primitive_Ioi.mono
      (Set.Ioi_subset_Ici_self : Set.Ioi (1 : ℝ) ⊆ Set.Ici (1 : ℝ))
  have hGmeas : AEStronglyMeasurable (fun z : ℝ => ∫ t in Set.Ioi z, Q t)
      (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
    hGcont.aestronglyMeasurable hSmeas
  -- (7) nonnegativity of the tail integral a.e. on `(1,∞)`
  have hGnn_ae : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))]
      (fun z : ℝ => ∫ t in Set.Ioi z, Q t) :=
    (ae_restrict_mem hSmeas).mono (fun z hz => hGnn z hz)
  refine ⟨?_, ?_⟩
  · exact ⟨hGmeas, (hasFiniteIntegral_iff_ofReal hGnn_ae).mpr hGlinn⟩
  · have e1 : ∫ z in Set.Ioi (1 : ℝ), (∫ t in Set.Ioi z, Q t)
        = ENNReal.toReal (∫⁻ z in Set.Ioi (1 : ℝ),
            ENNReal.ofReal (∫ t in Set.Ioi z, Q t)) :=
      integral_eq_lintegral_of_nonneg_ae hGnn_ae hGmeas
    have e2 : ∫ t in Set.Ioi (1 : ℝ), Q t * (t - 1)
        = ENNReal.toReal (∫⁻ t in Set.Ioi (1 : ℝ),
            ENNReal.ofReal (Q t * (t - 1))) :=
      integral_eq_lintegral_of_nonneg_ae hQ1nn (Integrable.aestronglyMeasurable hQ1)
    rw [e1, e2, hkey]

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.radGreenI_deriv_bounds_cpt =====
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

open Work.FTS.PhiStar.Series (rgiA rgiB rgiF1 rgiF2 rgiK rgiSn rgiSp rgiD1)

set_option maxHeartbeats 2000000

/-! ## Auxiliary facts -/

/-- The explicit second derivative of the Green function (the derivative of `rgiD1`). -/
private def rgiD2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (y : ℝ) : ℝ :=
  rgiK α m *
    (((rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y
        + (rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y)
      + ((rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y
        + (rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y))))

private lemma hasDerivAt_rgiD1 {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hA : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (rgiA α m c) (rgiF1 α m c z) z)
    (hB : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (rgiB α m c) (-(rgiF2 α m c z)) z) :
    ∀ y : ℝ, 0 < y → HasDerivAt (rgiD1 α m c) (rgiD2 α m c y) y := by
  have hp1 : ∀ y ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun t : ℝ => rgiSn α m * t ^ (rgiSn α m - 1))
        (rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) y := by
    intro y hy
    have h := (Real.hasDerivAt_rpow_const (x := y) (p := rgiSn α m - 1)
      (Or.inl (ne_of_gt hy))).const_mul (rgiSn α m)
    rwa [show rgiSn α m - 1 - 1 = rgiSn α m - 2 from by ring] at h
  have hp2 : ∀ y ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun t : ℝ => rgiSp α m * t ^ (rgiSp α m - 1))
        (rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) y := by
    intro y hy
    have h := (Real.hasDerivAt_rpow_const (x := y) (p := rgiSp α m - 1)
      (Or.inl (ne_of_gt hy))).const_mul (rgiSp α m)
    rwa [show rgiSp α m - 1 - 1 = rgiSp α m - 2 from by ring] at h
  intro y hy
  have hres : HasDerivAt (fun t : ℝ => rgiK α m * ((rgiSn α m * t ^ (rgiSn α m - 1)) * rgiA α m c t
        + (rgiSp α m * t ^ (rgiSp α m - 1)) * rgiB α m c t))
      (rgiK α m * (((rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y
          + (rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y)
        + ((rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y
          + (rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y))))) y :=
    (((hp1 y hy).mul (hA y hy)).add ((hp2 y hy).mul (hB y hy))).const_mul (rgiK α m)
  have hfun : (fun t : ℝ => rgiK α m * ((rgiSn α m * t ^ (rgiSn α m - 1)) * rgiA α m c t
      + (rgiSp α m * t ^ (rgiSp α m - 1)) * rgiB α m c t)) = rgiD1 α m c := rfl
  rw [hfun] at hres
  exact hres

/-- `rgiA` vanishes below the support of `c`. -/
private lemma rgiA_eq_zero_of_lt {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {a y : ℝ}
    (hvan : ∀ t : ℝ, t < a → c t = 0) (hy : 0 < y) (hya : y < a) : rgiA α m c y = 0 := by
  have hzero : ∫ t in (0 : ℝ)..y, rgiF1 α m c t = ∫ t in (0 : ℝ)..y, (0 : ℝ) :=
    intervalIntegral.integral_congr_ae
      (Filter.Eventually.of_forall fun t ht => by
        rw [Set.uIoc_of_le hy.le] at ht
        have hlt : t < a := by linarith [ht.2]
        simp only [rgiF1, hvan t hlt, zero_mul])
  rw [rgiA, hzero, intervalIntegral.integral_zero]

/-- The arithmetic constant for the first conjunct. -/
private lemma key_const {α M : ℝ} {m : ℕ} (hα : 0 < α) (hm : 1 ≤ m) (hM : 0 ≤ M) :
    rgiK α m * (M / ((2 * (m : ℝ) + 5) / α) + M / (2 * (m : ℝ) / α))
      ≤ M / (m * (4 * (m : ℝ) + 5)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hαne : α ≠ 0 := ne_of_gt hα
  have h5 : (2 * (m : ℝ) + 5) ≠ 0 := by positivity
  have h2m : (2 * (m : ℝ)) ≠ 0 := by positivity
  have h45 : (4 * (m : ℝ) + 5) ≠ 0 := by positivity
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have heq : rgiK α m * (M / ((2 * (m : ℝ) + 5) / α) + M / (2 * (m : ℝ) / α))
      = M / (4 * (m : ℝ) + 5) * (1 / (2 * (m : ℝ) + 5) + 1 / (2 * (m : ℝ))) := by
    simp only [rgiK]
    field_simp
  rw [heq]
  have hcoef : 1 / (2 * (m : ℝ) + 5) + 1 / (2 * (m : ℝ)) ≤ 1 / (m : ℝ) := by
    have h1 : 1 / (2 * (m : ℝ) + 5) ≤ 1 / (2 * (m : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    have h2 : 1 / (2 * (m : ℝ)) + 1 / (2 * (m : ℝ)) = 1 / (m : ℝ) := by
      rw [← add_div]
      field_simp
      norm_num
    linarith [h1, h2]
  calc M / (4 * (m : ℝ) + 5) * (1 / (2 * (m : ℝ) + 5) + 1 / (2 * (m : ℝ)))
      ≤ M / (4 * (m : ℝ) + 5) * (1 / (m : ℝ)) := mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ = M / (m * (4 * (m : ℝ) + 5)) := by
        field_simp

/-- The arithmetic constant for the second conjunct. -/
private lemma key_const2 {α M a : ℝ} {m : ℕ} (hα : 0 < α) (ha : 0 < a) :
    rgiK α m * (M / a + M / a) = 2 * M / (α * (4 * (m : ℝ) + 5) * a) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have h45 : (4 * (m : ℝ) + 5) ≠ 0 := by positivity
  have hane : a ≠ 0 := ne_of_gt ha
  simp only [rgiK]
  field_simp
  ring

/-- The arithmetic constant for the small-`y` case of the third conjunct. -/
private lemma key_const3 {α M a : ℝ} {m : ℕ} (hα : 0 < α) (hm : 1 ≤ m)
    (hM : 0 ≤ M) (ha : 0 < a) :
    rgiK α m * (M * (2 * (m : ℝ) / α - 1) / a ^ 2) ≤ 10 * M / (α ^ 2 * a ^ 2) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hαne : α ≠ 0 := ne_of_gt hα
  have h45 : (4 * (m : ℝ) + 5) ≠ 0 := by positivity
  have hane : a ≠ 0 := ne_of_gt ha
  have hle : rgiK α m * (M * (2 * (m : ℝ) / α - 1) / a ^ 2)
      = M * (2 * (m : ℝ) - α) / (α ^ 2 * (4 * (m : ℝ) + 5) * a ^ 2) := by
    simp only [rgiK]
    field_simp
  rw [hle]
  have hden : 0 < α ^ 2 * (4 * (m : ℝ) + 5) * a ^ 2 := by positivity
  have hden2 : 0 < α ^ 2 * a ^ 2 := by positivity
  have hnum : M * (2 * (m : ℝ) - α) ≤ 10 * M * (4 * (m : ℝ) + 5) := by nlinarith [hM, hmR, hα]
  calc M * (2 * (m : ℝ) - α) / (α ^ 2 * (4 * (m : ℝ) + 5) * a ^ 2)
      ≤ (10 * M * (4 * (m : ℝ) + 5)) / (α ^ 2 * (4 * (m : ℝ) + 5) * a ^ 2) :=
        div_le_div_of_nonneg_right hnum hden.le
    _ = 10 * M / (α ^ 2 * a ^ 2) := by
        field_simp

/-- The arithmetic constant for the large-`y` case of the third conjunct. -/
private lemma key_const4 {α M a : ℝ} {m : ℕ} (hα : 0 < α) (hM : 0 ≤ M) (ha : 0 < a) :
    rgiK α m * (M * (2 * (4 * (m : ℝ) + 5) / α) / a ^ 2) ≤ 10 * M / (α ^ 2 * a ^ 2) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have h45 : (4 * (m : ℝ) + 5) ≠ 0 := by positivity
  have hane : a ≠ 0 := ne_of_gt ha
  have hle : rgiK α m * (M * (2 * (4 * (m : ℝ) + 5) / α) / a ^ 2)
      = 2 * M / (α ^ 2 * a ^ 2) := by
    simp only [rgiK]
    field_simp
  rw [hle]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith [hM]

theorem radGreenI_deriv_bounds_cpt {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {m : ℕ}
    (hm : 1 ≤ m) {c : ℝ → ℝ} {M a b : ℝ} (hM0 : 0 ≤ M) (ha : 0 < a)
    (hc : ContinuousOn c (Set.Ioi 0)) (hb : ∀ t : ℝ, |c t| ≤ M)
    (hsupp : ∀ t : ℝ, c t ≠ 0 → t ∈ Set.Icc a b)
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    (∀ z : ℝ, 0 < z →
      |Work.FTS.PhiStar.Radial.radGreenI α m c z| ≤ M / (m * (4 * (m : ℝ) + 5))) ∧
    (∀ y : ℝ, 0 < y → |Work.FTS.PhiStar.Series.rgiD1 α m c y|
      ≤ 2 * M / (α * (4 * (m : ℝ) + 5) * a)) ∧
    (∀ y : ℝ, 0 < y → |deriv (Work.FTS.PhiStar.Series.rgiD1 α m c) y|
      ≤ 10 * M / (α ^ 2 * a ^ 2)) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hmm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp : 0 < (2 * (m : ℝ) + 5) / α := div_pos (by positivity) hα
  have hq : 0 < 2 * (m : ℝ) / α := div_pos (by positivity) hα
  have hpne : (2 * (m : ℝ) + 5) / α ≠ 0 := ne_of_gt hp
  have hqne : 2 * (m : ℝ) / α ≠ 0 := ne_of_gt hq
  have hq1 : 1 ≤ 2 * (m : ℝ) / α := by rw [le_div_iff₀ hα]; nlinarith [hm1, hα4]
  have hq2 : 2 ≤ 2 * (m : ℝ) / α := by rw [le_div_iff₀ hα]; nlinarith [hm1, hα4]
  have hKpos : 0 < rgiK α m := by simp only [rgiK]; positivity
  have hKnonneg : 0 ≤ rgiK α m := hKpos.le
  have hvan : ∀ t : ℝ, t < a → c t = 0 := by
    intro t ht
    by_contra h
    have hmem := hsupp t h
    simp only [Set.mem_Icc] at hmem
    linarith [hmem.1]
  -- sign and absolute-value facts for the two indicial exponents
  have hSnneg : rgiSn α m < 0 := by
    simp only [rgiSn]
    exact div_neg_of_neg_of_pos (by linarith [hmm]) hα
  have hSn1neg : rgiSn α m - 1 < 0 := by linarith [hSnneg]
  have hSppos : 0 < rgiSp α m := by simp only [rgiSp]; exact hq
  have hSp1nn : 0 ≤ rgiSp α m - 1 := by simp only [rgiSp]; linarith [hq1]
  have hSp2nn : 0 ≤ rgiSp α m - 2 := by simp only [rgiSp]; linarith [hq2]
  have habsSn : |rgiSn α m| = (2 * (m : ℝ) + 5) / α := by
    rw [abs_of_neg hSnneg]
    simp only [rgiSn]
    ring
  have habsSp : |rgiSp α m| = 2 * (m : ℝ) / α := by
    rw [abs_of_pos hSppos]
    simp only [rgiSp]
  have habsSn1 : |rgiSn α m - 1| = (2 * (m : ℝ) + 5) / α + 1 := by
    rw [abs_of_neg hSn1neg]
    simp only [rgiSn]
    ring
  have habsSp1 : |rgiSp α m - 1| = 2 * (m : ℝ) / α - 1 := by
    rw [abs_of_nonneg hSp1nn]
    simp only [rgiSp]
  refine ⟨?_, ?_, ?_⟩
  · -- ### first conjunct
    intro z hz
    have hA := rgiA_abs_le (m := m) hα hM0 hb z hz
    have hB := rgiB_abs_le (m := m) hα hm hM0 hb z hz
    have hzSn : z ^ (rgiSn α m) * z ^ ((2 * (m : ℝ) + 5) / α) = 1 := by
      rw [← Real.rpow_add hz,
        show rgiSn α m + (2 * (m : ℝ) + 5) / α = 0 by simp only [rgiSn]; ring,
        Real.rpow_zero]
    have hzSp : z ^ (rgiSp α m) * z ^ (-(2 * (m : ℝ) / α)) = 1 := by
      rw [← Real.rpow_add hz,
        show rgiSp α m + (-(2 * (m : ℝ) / α)) = 0 by simp only [rgiSp]; ring,
        Real.rpow_zero]
    have hA' : z ^ (rgiSn α m) * |rgiA α m c z| ≤ M / ((2 * (m : ℝ) + 5) / α) := by
      calc z ^ (rgiSn α m) * |rgiA α m c z|
          ≤ z ^ (rgiSn α m)
              * (M * z ^ ((2 * (m : ℝ) + 5) / α) / ((2 * (m : ℝ) + 5) / α)) :=
            mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hz.le _)
        _ = (z ^ (rgiSn α m) * z ^ ((2 * (m : ℝ) + 5) / α))
              * (M / ((2 * (m : ℝ) + 5) / α)) := by ring
        _ = M / ((2 * (m : ℝ) + 5) / α) := by rw [hzSn, one_mul]
    have hB' : z ^ (rgiSp α m) * |rgiB α m c z| ≤ M / (2 * (m : ℝ) / α) := by
      calc z ^ (rgiSp α m) * |rgiB α m c z|
          ≤ z ^ (rgiSp α m) * (M * z ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α)) :=
            mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hz.le _)
        _ = (z ^ (rgiSp α m) * z ^ (-(2 * (m : ℝ) / α))) * (M / (2 * (m : ℝ) / α)) := by ring
        _ = M / (2 * (m : ℝ) / α) := by rw [hzSp, one_mul]
    simp only [Work.FTS.PhiStar.Series.radGreenI_eq_rgi]
    calc |rgiK α m * (z ^ (rgiSn α m) * rgiA α m c z + z ^ (rgiSp α m) * rgiB α m c z)|
        = rgiK α m * |z ^ (rgiSn α m) * rgiA α m c z + z ^ (rgiSp α m) * rgiB α m c z| := by
          rw [abs_mul, abs_of_pos hKpos]
      _ ≤ rgiK α m
            * (|z ^ (rgiSn α m) * rgiA α m c z| + |z ^ (rgiSp α m) * rgiB α m c z|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hKnonneg
      _ = rgiK α m
            * (z ^ (rgiSn α m) * |rgiA α m c z| + z ^ (rgiSp α m) * |rgiB α m c z|) := by
          rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz _),
            abs_of_pos (Real.rpow_pos_of_pos hz _)]
      _ ≤ rgiK α m * (M / ((2 * (m : ℝ) + 5) / α) + M / (2 * (m : ℝ) / α)) :=
          mul_le_mul_of_nonneg_left (add_le_add hA' hB') hKnonneg
      _ ≤ M / (m * (4 * (m : ℝ) + 5)) := key_const hα hm hM0
  · -- ### second conjunct
    intro y hy
    have hA := rgiA_abs_le (m := m) hα hM0 hb y hy
    have hB := rgiB_abs_le (m := m) hα hm hM0 hb y hy
    have htermA : |(rgiSn α m * y ^ (rgiSn α m - 1)) * rgiA α m c y| ≤ M / a := by
      by_cases hya : y < a
      · rw [rgiA_eq_zero_of_lt hvan hy hya, mul_zero, abs_zero]
        exact div_nonneg hM0 ha.le
      · have hay : a ≤ y := not_lt.mp hya
        have hySn : y ^ (rgiSn α m - 1) * y ^ ((2 * (m : ℝ) + 5) / α) = y ^ (-(1 : ℝ)) := by
          rw [← Real.rpow_add hy]
          congr 1
          simp only [rgiSn]; ring
        have habs : |(rgiSn α m * y ^ (rgiSn α m - 1)) * rgiA α m c y|
            = ((2 * (m : ℝ) + 5) / α) * y ^ (rgiSn α m - 1) * |rgiA α m c y| := by
          rw [abs_mul, abs_mul, habsSn, abs_of_pos (Real.rpow_pos_of_pos hy _)]
          try ring
        rw [habs]
        calc ((2 * (m : ℝ) + 5) / α) * y ^ (rgiSn α m - 1) * |rgiA α m c y|
            ≤ ((2 * (m : ℝ) + 5) / α) * y ^ (rgiSn α m - 1)
                * (M * y ^ ((2 * (m : ℝ) + 5) / α) / ((2 * (m : ℝ) + 5) / α)) :=
              mul_le_mul_of_nonneg_left hA (by positivity)
          _ = M * (y ^ (rgiSn α m - 1) * y ^ ((2 * (m : ℝ) + 5) / α)) := by
              field_simp
              try ring
          _ = M * y ^ (-(1 : ℝ)) := by rw [hySn]
          _ = M / y := by rw [Real.rpow_neg hy.le (1 : ℝ), Real.rpow_one, div_eq_mul_inv]
          _ ≤ M / a := div_le_div_of_nonneg_left hM0 ha hay
    have htermB : |(rgiSp α m * y ^ (rgiSp α m - 1)) * rgiB α m c y| ≤ M / a := by
      by_cases hya : y < a
      · have hB0 := rgiB_abs_le_small (m := m) hα hm hM0 ha hb hsupp y hy hya
        have hle1 : y ^ (rgiSp α m - 1) ≤ a ^ (rgiSp α m - 1) :=
          Real.rpow_le_rpow hy.le hya.le hSp1nn
        have h2 : a ^ (rgiSp α m - 1) * a ^ (-(2 * (m : ℝ) / α)) = a ^ (-(1 : ℝ)) := by
          rw [← Real.rpow_add ha]
          congr 1
          simp only [rgiSp]; ring
        have habs : |(rgiSp α m * y ^ (rgiSp α m - 1)) * rgiB α m c y|
            = (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1) * |rgiB α m c y| := by
          rw [abs_mul, abs_mul, habsSp, abs_of_pos (Real.rpow_pos_of_pos hy _)]
          try ring
        rw [habs]
        calc (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1) * |rgiB α m c y|
            ≤ (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1)
                * (M * a ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α)) :=
              mul_le_mul_of_nonneg_left hB0 (by positivity)
          _ = M * (y ^ (rgiSp α m - 1) * a ^ (-(2 * (m : ℝ) / α))) := by
              field_simp
              try ring
          _ ≤ M * a ^ (-(1 : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ hM0
              calc y ^ (rgiSp α m - 1) * a ^ (-(2 * (m : ℝ) / α))
                  ≤ a ^ (rgiSp α m - 1) * a ^ (-(2 * (m : ℝ) / α)) :=
                    mul_le_mul_of_nonneg_right hle1 (Real.rpow_nonneg ha.le _)
                _ = a ^ (-(1 : ℝ)) := h2
          _ = M / a := by rw [Real.rpow_neg ha.le (1 : ℝ), Real.rpow_one, div_eq_mul_inv]
      · have hay : a ≤ y := not_lt.mp hya
        have hySp : y ^ (rgiSp α m - 1) * y ^ (-(2 * (m : ℝ) / α)) = y ^ (-(1 : ℝ)) := by
          rw [← Real.rpow_add hy]
          congr 1
          simp only [rgiSp]; ring
        have habs : |(rgiSp α m * y ^ (rgiSp α m - 1)) * rgiB α m c y|
            = (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1) * |rgiB α m c y| := by
          rw [abs_mul, abs_mul, habsSp, abs_of_pos (Real.rpow_pos_of_pos hy _)]
          try ring
        rw [habs]
        calc (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1) * |rgiB α m c y|
            ≤ (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1)
                * (M * y ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α)) :=
              mul_le_mul_of_nonneg_left hB (by positivity)
          _ = M * (y ^ (rgiSp α m - 1) * y ^ (-(2 * (m : ℝ) / α))) := by
              field_simp
              try ring
          _ = M * y ^ (-(1 : ℝ)) := by rw [hySp]
          _ = M / y := by rw [Real.rpow_neg hy.le (1 : ℝ), Real.rpow_one, div_eq_mul_inv]
          _ ≤ M / a := div_le_div_of_nonneg_left hM0 ha hay
    rw [rgiD1]
    calc |rgiK α m * ((rgiSn α m * y ^ (rgiSn α m - 1)) * rgiA α m c y
            + (rgiSp α m * y ^ (rgiSp α m - 1)) * rgiB α m c y)|
        = rgiK α m * |(rgiSn α m * y ^ (rgiSn α m - 1)) * rgiA α m c y
            + (rgiSp α m * y ^ (rgiSp α m - 1)) * rgiB α m c y| := by
          rw [abs_mul, abs_of_pos hKpos]
      _ ≤ rgiK α m * (|(rgiSn α m * y ^ (rgiSn α m - 1)) * rgiA α m c y|
            + |(rgiSp α m * y ^ (rgiSp α m - 1)) * rgiB α m c y|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hKnonneg
      _ ≤ rgiK α m * (M / a + M / a) :=
          mul_le_mul_of_nonneg_left (add_le_add htermA htermB) hKnonneg
      _ = 2 * M / (α * (4 * (m : ℝ) + 5) * a) := key_const2 hα ha
  · -- ### third conjunct
    intro y hy
    rw [(hasDerivAt_rgiD1 (α := α) (m := m) (c := c)
      (fun z hz => Work.FTS.PhiStar.Series.rgiA_hasDerivAt hc h0 z hz)
      (fun z hz => Work.FTS.PhiStar.Series.rgiB_hasDerivAt hc hinf z hz) y hy).deriv]
    have hA := rgiA_abs_le (m := m) hα hM0 hb y hy
    have hB := rgiB_abs_le (m := m) hα hm hM0 hb y hy
    have hySn2 : y ^ (rgiSn α m - 2) * y ^ ((2 * (m : ℝ) + 5) / α) = y ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hy]
      congr 1
      simp only [rgiSn]; ring
    have hySn1 : y ^ (rgiSn α m - 1) * y ^ ((2 * (m : ℝ) + 5) / α - 1) = y ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hy]
      congr 1
      simp only [rgiSn]; ring
    have hySp2 : y ^ (rgiSp α m - 2) * y ^ (-(2 * (m : ℝ) / α)) = y ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hy]
      congr 1
      simp only [rgiSp]; ring
    have hySp1 : y ^ (rgiSp α m - 1) * y ^ (-(2 * (m : ℝ) / α) - 1) = y ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hy]
      congr 1
      simp only [rgiSp]; ring
    have ha2 : a ^ (-(2 : ℝ)) = 1 / a ^ 2 := by
      rw [Real.rpow_neg ha.le (2 : ℝ), Real.rpow_two, inv_eq_one_div]
    by_cases hya : y < a
    · -- small case: `y` is below the support
      have hA0 : rgiA α m c y = 0 := rgiA_eq_zero_of_lt hvan hy hya
      have hcy : c y = 0 := hvan y hya
      have hF1 : rgiF1 α m c y = 0 := by simp only [rgiF1, hcy, zero_mul]
      have hF2 : rgiF2 α m c y = 0 := by simp only [rgiF2, hcy, zero_mul]
      have hB0 := rgiB_abs_le_small (m := m) hα hm hM0 ha hb hsupp y hy hya
      have hD2 : rgiD2 α m c y
          = rgiK α m
              * ((rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y) := by
        simp only [rgiD2, hA0, hF1, hF2, mul_zero, add_zero, neg_zero, zero_add]
      rw [hD2]
      have hfac : y ^ (rgiSp α m - 2) * a ^ (-(2 * (m : ℝ) / α)) ≤ a ^ (-(2 : ℝ)) := by
        have h2 : a ^ (rgiSp α m - 2) * a ^ (-(2 * (m : ℝ) / α)) = a ^ (-(2 : ℝ)) := by
          rw [← Real.rpow_add ha]
          congr 1
          simp only [rgiSp]; ring
        calc y ^ (rgiSp α m - 2) * a ^ (-(2 * (m : ℝ) / α))
            ≤ a ^ (rgiSp α m - 2) * a ^ (-(2 * (m : ℝ) / α)) :=
              mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hy.le hya.le hSp2nn)
                (Real.rpow_nonneg ha.le _)
          _ = a ^ (-(2 : ℝ)) := h2
      have hmid : |(rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y|
          ≤ M * (2 * (m : ℝ) / α - 1) / a ^ 2 := by
        have habs : |(rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y|
            = (2 * (m : ℝ) / α) * ((2 * (m : ℝ) / α - 1) * y ^ (rgiSp α m - 2))
              * |rgiB α m c y| := by
          rw [abs_mul, abs_mul, abs_mul, habsSp, habsSp1,
            abs_of_pos (Real.rpow_pos_of_pos hy _)]
          try ring
        rw [habs]
        calc (2 * (m : ℝ) / α) * ((2 * (m : ℝ) / α - 1) * y ^ (rgiSp α m - 2))
              * |rgiB α m c y|
            ≤ (2 * (m : ℝ) / α) * ((2 * (m : ℝ) / α - 1) * y ^ (rgiSp α m - 2))
              * (M * a ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α)) :=
              mul_le_mul_of_nonneg_left hB0 (by positivity)
          _ = M * (2 * (m : ℝ) / α - 1)
                * (y ^ (rgiSp α m - 2) * a ^ (-(2 * (m : ℝ) / α))) := by
              field_simp
              try ring
          _ ≤ M * (2 * (m : ℝ) / α - 1) * a ^ (-(2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hfac (mul_nonneg hM0 (by linarith [hq1]))
          _ = M * (2 * (m : ℝ) / α - 1) / a ^ 2 := by rw [ha2]; ring
      calc |rgiK α m * ((rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y)|
          = rgiK α m
              * |(rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y| := by
            rw [abs_mul, abs_of_pos hKpos]
        _ ≤ rgiK α m * (M * (2 * (m : ℝ) / α - 1) / a ^ 2) :=
            mul_le_mul_of_nonneg_left hmid hKnonneg
        _ ≤ 10 * M / (α ^ 2 * a ^ 2) := key_const3 hα hm hM0 ha
    · -- large case: `a ≤ y`
      have hay : a ≤ y := not_lt.mp hya
      have hle2 : y ^ (-(2 : ℝ)) ≤ a ^ (-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ha hay (by norm_num)
      have hT1 : |(rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y|
          ≤ M * ((2 * (m : ℝ) + 5) / α + 1) / a ^ 2 := by
        have habs : |(rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y|
            = ((2 * (m : ℝ) + 5) / α)
              * (((2 * (m : ℝ) + 5) / α + 1) * y ^ (rgiSn α m - 2))
              * |rgiA α m c y| := by
          rw [abs_mul, abs_mul, abs_mul, habsSn, habsSn1,
            abs_of_pos (Real.rpow_pos_of_pos hy _)]
          try ring
        rw [habs]
        calc ((2 * (m : ℝ) + 5) / α) * (((2 * (m : ℝ) + 5) / α + 1) * y ^ (rgiSn α m - 2))
              * |rgiA α m c y|
            ≤ ((2 * (m : ℝ) + 5) / α) * (((2 * (m : ℝ) + 5) / α + 1) * y ^ (rgiSn α m - 2))
              * (M * y ^ ((2 * (m : ℝ) + 5) / α) / ((2 * (m : ℝ) + 5) / α)) :=
              mul_le_mul_of_nonneg_left hA (by positivity)
          _ = M * ((2 * (m : ℝ) + 5) / α + 1)
                * (y ^ (rgiSn α m - 2) * y ^ ((2 * (m : ℝ) + 5) / α)) := by
              field_simp
              try ring
          _ = M * ((2 * (m : ℝ) + 5) / α + 1) * y ^ (-(2 : ℝ)) := by rw [hySn2]
          _ ≤ M * ((2 * (m : ℝ) + 5) / α + 1) * a ^ (-(2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hle2 (by positivity)
          _ = M * ((2 * (m : ℝ) + 5) / α + 1) / a ^ 2 := by rw [ha2]; ring
      have hT2 : |(rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y|
          ≤ M * ((2 * (m : ℝ) + 5) / α) / a ^ 2 := by
        have habs : |(rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y|
            = ((2 * (m : ℝ) + 5) / α) * y ^ (rgiSn α m - 1)
              * (|c y| * y ^ ((2 * (m : ℝ) + 5) / α - 1)) := by
          rw [abs_mul, abs_mul, habsSn, abs_of_pos (Real.rpow_pos_of_pos hy _), rgiF1, abs_mul,
            abs_of_pos (Real.rpow_pos_of_pos hy _)]
          try ring
        rw [habs]
        calc ((2 * (m : ℝ) + 5) / α) * y ^ (rgiSn α m - 1)
              * (|c y| * y ^ ((2 * (m : ℝ) + 5) / α - 1))
            ≤ ((2 * (m : ℝ) + 5) / α) * y ^ (rgiSn α m - 1)
              * (M * y ^ ((2 * (m : ℝ) + 5) / α - 1)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_right (hb y) (Real.rpow_nonneg hy.le _)
          _ = M * ((2 * (m : ℝ) + 5) / α)
                * (y ^ (rgiSn α m - 1) * y ^ ((2 * (m : ℝ) + 5) / α - 1)) := by ring
          _ = M * ((2 * (m : ℝ) + 5) / α) * y ^ (-(2 : ℝ)) := by rw [hySn1]
          _ ≤ M * ((2 * (m : ℝ) + 5) / α) * a ^ (-(2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hle2 (by positivity)
          _ = M * ((2 * (m : ℝ) + 5) / α) / a ^ 2 := by rw [ha2]; ring
      have hT3 : |(rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y|
          ≤ M * (2 * (m : ℝ) / α - 1) / a ^ 2 := by
        have habs : |(rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y|
            = (2 * (m : ℝ) / α) * ((2 * (m : ℝ) / α - 1) * y ^ (rgiSp α m - 2))
              * |rgiB α m c y| := by
          rw [abs_mul, abs_mul, abs_mul, habsSp, habsSp1,
            abs_of_pos (Real.rpow_pos_of_pos hy _)]
          try ring
        rw [habs]
        calc (2 * (m : ℝ) / α) * ((2 * (m : ℝ) / α - 1) * y ^ (rgiSp α m - 2))
              * |rgiB α m c y|
            ≤ (2 * (m : ℝ) / α) * ((2 * (m : ℝ) / α - 1) * y ^ (rgiSp α m - 2))
              * (M * y ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α)) :=
              mul_le_mul_of_nonneg_left hB (by positivity)
          _ = M * (2 * (m : ℝ) / α - 1)
                * (y ^ (rgiSp α m - 2) * y ^ (-(2 * (m : ℝ) / α))) := by
              field_simp
              try ring
          _ = M * (2 * (m : ℝ) / α - 1) * y ^ (-(2 : ℝ)) := by rw [hySp2]
          _ ≤ M * (2 * (m : ℝ) / α - 1) * a ^ (-(2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hle2 (mul_nonneg hM0 (by linarith [hq1]))
          _ = M * (2 * (m : ℝ) / α - 1) / a ^ 2 := by rw [ha2]; ring
      have hT4 : |(rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y))|
          ≤ M * (2 * (m : ℝ) / α) / a ^ 2 := by
        have habs : |(rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y))|
            = (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1)
              * (|c y| * y ^ (-(2 * (m : ℝ) / α) - 1)) := by
          rw [abs_mul, abs_mul, habsSp, abs_of_pos (Real.rpow_pos_of_pos hy _), abs_neg, rgiF2,
            abs_mul, abs_of_pos (Real.rpow_pos_of_pos hy _)]
          try ring
        rw [habs]
        calc (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1)
              * (|c y| * y ^ (-(2 * (m : ℝ) / α) - 1))
            ≤ (2 * (m : ℝ) / α) * y ^ (rgiSp α m - 1)
              * (M * y ^ (-(2 * (m : ℝ) / α) - 1)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_right (hb y) (Real.rpow_nonneg hy.le _)
          _ = M * (2 * (m : ℝ) / α)
                * (y ^ (rgiSp α m - 1) * y ^ (-(2 * (m : ℝ) / α) - 1)) := by ring
          _ = M * (2 * (m : ℝ) / α) * y ^ (-(2 : ℝ)) := by rw [hySp1]
          _ ≤ M * (2 * (m : ℝ) / α) * a ^ (-(2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hle2 (by positivity)
          _ = M * (2 * (m : ℝ) / α) / a ^ 2 := by rw [ha2]; ring
      have hsum : |(rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y|
            + |(rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y|
            + |(rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y|
            + |(rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y))|
          ≤ M * (2 * (4 * (m : ℝ) + 5) / α) / a ^ 2 := by
        have harith : M * ((2 * (m : ℝ) + 5) / α + 1) / a ^ 2
              + M * ((2 * (m : ℝ) + 5) / α) / a ^ 2
              + M * (2 * (m : ℝ) / α - 1) / a ^ 2 + M * (2 * (m : ℝ) / α) / a ^ 2
            = M * (2 * (4 * (m : ℝ) + 5) / α) / a ^ 2 := by ring
        linarith [hT1, hT2, hT3, hT4, harith]
      have e1 := abs_add_le ((rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y)
        ((rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y)
      have e2 := abs_add_le ((rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y)
        ((rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y)))
      have e3 := abs_add_le (((rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y)
          + ((rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y))
        (((rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y)
          + ((rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y))))
      have htri : |rgiD2 α m c y| ≤ rgiK α m * (M * (2 * (4 * (m : ℝ) + 5) / α) / a ^ 2) := by
        simp only [rgiD2]
        rw [abs_mul, abs_of_pos hKpos]
        apply mul_le_mul_of_nonneg_left _ hKnonneg
        linarith [e1, e2, e3, hsum]
      calc |rgiD2 α m c y| ≤ rgiK α m * (M * (2 * (4 * (m : ℝ) + 5) / α) / a ^ 2) := htri
        _ ≤ 10 * M / (α ^ 2 * a ^ 2) := key_const4 hα hM0 ha

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.radGreen_secondTerm_sq_integrableOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter
open scoped ENNReal

/-- `ENNReal.ofReal` of a set integral of a nonnegative a.e.-strongly-measurable function is at
most the set lintegral of `ENNReal.ofReal` of the integrand. -/
lemma ofReal_setIntegral_le_setLIntegral' {f : ℝ → ℝ} {s : Set ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict s)) (hnn : 0 ≤ᵐ[volume.restrict s] f) :
    ENNReal.ofReal (∫ t in s, f t) ≤ ∫⁻ t in s, ENNReal.ofReal (f t) := by
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf]
  exact ENNReal.ofReal_toReal_le



end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.radGreen_supp_weight_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real
open MeasureTheory Set

namespace Work.FTS.PhiStar.Honesty

theorem radGreen_supp_weight_le {α : ℝ} (hα : 0 < α) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 ≤ M → ∀ {c : ℝ → ℝ},
      (∀ t : ℝ, t ∉ Set.Icc a b → c t = 0) → (∀ t : ℝ, |c t| ≤ M) →
      ∀ m : ℕ, 1 ≤ m → ∀ z : ℝ, 0 < z →
        |Work.FTS.PhiStar.Radial.radGreen α m c z|
          ≤ C * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
  refine ⟨RadGreenSupp.C α a b, RadGreenSupp.C_pos hα ha hab, ?_⟩
  intro M hM c hsupp hb m hm z hz
  -- ### abbreviations
  set K : ℝ := Work.FTS.EllExist.rgK α m with hKdef
  set P : ℝ := Work.FTS.EllExist.rgP α m with hPdef
  set Q : ℝ := Work.FTS.EllExist.rgQ α m with hQdef
  have hKpos : 0 < K := by rw [hKdef]; exact Work.FTS.EllExist.rgK_pos hα m
  have hPpos : 0 < P := by rw [hPdef]; exact Work.FTS.EllExist.rgP_pos hα hm
  have hQpos : 0 < Q := by rw [hQdef]; exact Work.FTS.EllExist.rgQ_pos hα m
  have hzK : 0 < z ^ (-Q) := Real.rpow_pos_of_pos hz _
  have hzP : 0 < z ^ P := Real.rpow_pos_of_pos hz _
  -- ### the decomposition of `radGreen`
  have hrad : Work.FTS.PhiStar.Radial.radGreen α m c z
      = K * (z ^ (-Q) * Work.FTS.EllExist.rgA α m c z
              + z ^ P * Work.FTS.EllExist.rgB α m c z) := by
    rw [Work.FTS.EllExist.radGreen_eq, ← hKdef, ← hPdef, ← hQdef]
  -- ### the elementary triangle-inequality step
  have hmain : |Work.FTS.PhiStar.Radial.radGreen α m c z|
      ≤ K * (z ^ (-Q) * |Work.FTS.EllExist.rgA α m c z|
              + z ^ P * |Work.FTS.EllExist.rgB α m c z|) := by
    rw [hrad, abs_mul, abs_of_pos hKpos]
    refine mul_le_mul_of_nonneg_left ?_ hKpos.le
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_mul, abs_of_pos hzK, abs_of_pos hzP]
  -- ### the three regimes
  by_cases hza : z ≤ a
  · -- ## regime 1: `z ≤ a`
    have hAz : Work.FTS.EllExist.rgA α m c z = 0 := by
      have h := RadGreenSupp.head_zero (c := c) (a := a) (b := b)
        (e := Work.FTS.EllExist.rgQ α m - 1) (z := z) ha hab hsupp hz hza
      simpa only [Work.FTS.EllExist.rgA, Work.FTS.EllExist.rgF1] using h
    have hBz : |Work.FTS.EllExist.rgB α m c z|
        ≤ M * a ^ (-(Work.FTS.EllExist.rgP α m)) / Work.FTS.EllExist.rgP α m := by
      have h := RadGreenSupp.tail_supp (c := c) (a := a) (b := b) (M := M)
        (p := Work.FTS.EllExist.rgP α m) (z := z) ha hab hM
        (Work.FTS.EllExist.rgP_pos hα hm) hsupp hb hz
      simpa only [Work.FTS.EllExist.rgB, Work.FTS.EllExist.rgF2, max_eq_right hza] using h
    calc |Work.FTS.PhiStar.Radial.radGreen α m c z|
        ≤ K * (z ^ (-Q) * |Work.FTS.EllExist.rgA α m c z|
                + z ^ P * |Work.FTS.EllExist.rgB α m c z|) := hmain
      _ = K * (z ^ P * |Work.FTS.EllExist.rgB α m c z|) := by rw [hAz]; ring
      _ ≤ K * (z ^ P * (M * a ^ (-P) / P)) := by
          refine mul_le_mul_of_nonneg_left ?_ hKpos.le
          exact mul_le_mul_of_nonneg_left hBz hzP.le
      _ = Work.FTS.EllExist.rgK α m
            * (z ^ Work.FTS.EllExist.rgP α m
                * (M * a ^ (-(Work.FTS.EllExist.rgP α m)) / Work.FTS.EllExist.rgP α m)) := by
          rw [hKdef, hPdef]
      _ ≤ RadGreenSupp.C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) :=
          RadGreenSupp.cmp1 hα ha hab hM hm hz hza
  · by_cases hzb : z ≤ b
    · -- ## regime 2: `a ≤ z ≤ b`
      have haz : a ≤ z := le_of_not_ge hza
      have hA : |Work.FTS.EllExist.rgA α m c z|
          ≤ M * z ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m := by
        have h := RadGreenSupp.head_supp (c := c) (a := a) (b := b) (M := M)
          (e := Work.FTS.EllExist.rgQ α m - 1) (z := z) ha hab hM
          (by linarith [Work.FTS.EllExist.rgQ_pos hα m]) hsupp hb hz
        have hexp : (Work.FTS.EllExist.rgQ α m - 1) + 1 = Work.FTS.EllExist.rgQ α m := by ring
        simpa only [Work.FTS.EllExist.rgA, Work.FTS.EllExist.rgF1, min_eq_left hzb, hexp] using h
      have hB : |Work.FTS.EllExist.rgB α m c z|
          ≤ M * z ^ (-(Work.FTS.EllExist.rgP α m)) / Work.FTS.EllExist.rgP α m := by
        have h := RadGreenSupp.tail_supp (c := c) (a := a) (b := b) (M := M)
          (p := Work.FTS.EllExist.rgP α m) (z := z) ha hab hM
          (Work.FTS.EllExist.rgP_pos hα hm) hsupp hb hz
        simpa only [Work.FTS.EllExist.rgB, Work.FTS.EllExist.rgF2, max_eq_left haz] using h
      calc |Work.FTS.PhiStar.Radial.radGreen α m c z|
          ≤ K * (z ^ (-Q) * |Work.FTS.EllExist.rgA α m c z|
                  + z ^ P * |Work.FTS.EllExist.rgB α m c z|) := hmain
        _ ≤ K * (z ^ (-Q) * (M * z ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m)
                + z ^ P * (M * z ^ (-(Work.FTS.EllExist.rgP α m))
                    / Work.FTS.EllExist.rgP α m)) := by
            refine mul_le_mul_of_nonneg_left ?_ hKpos.le
            exact add_le_add (mul_le_mul_of_nonneg_left hA hzK.le)
              (mul_le_mul_of_nonneg_left hB hzP.le)
        _ = Work.FTS.EllExist.rgK α m
              * (z ^ (-(Work.FTS.EllExist.rgQ α m))
                    * (M * z ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m)
                  + z ^ Work.FTS.EllExist.rgP α m
                    * (M * z ^ (-(Work.FTS.EllExist.rgP α m))
                        / Work.FTS.EllExist.rgP α m)) := by
            rw [hKdef, hPdef, hQdef]
        _ ≤ RadGreenSupp.C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) :=
            RadGreenSupp.cmp2 hα ha hab hM hm hz haz hzb
    · -- ## regime 3: `b ≤ z`
      have hbz : b ≤ z := le_of_not_ge hzb
      have hBz : Work.FTS.EllExist.rgB α m c z = 0 := by
        have h := RadGreenSupp.tail_zero (c := c) (a := a) (b := b)
          (e := -(Work.FTS.EllExist.rgP α m) - 1) (z := z) ha hab hsupp hz hbz
        simpa only [Work.FTS.EllExist.rgB, Work.FTS.EllExist.rgF2] using h
      have hAz : |Work.FTS.EllExist.rgA α m c z|
          ≤ M * b ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m := by
        have h := RadGreenSupp.head_supp (c := c) (a := a) (b := b) (M := M)
          (e := Work.FTS.EllExist.rgQ α m - 1) (z := z) ha hab hM
          (by linarith [Work.FTS.EllExist.rgQ_pos hα m]) hsupp hb hz
        have hexp : (Work.FTS.EllExist.rgQ α m - 1) + 1 = Work.FTS.EllExist.rgQ α m := by ring
        simpa only [Work.FTS.EllExist.rgA, Work.FTS.EllExist.rgF1, min_eq_right hbz, hexp] using h
      calc |Work.FTS.PhiStar.Radial.radGreen α m c z|
          ≤ K * (z ^ (-Q) * |Work.FTS.EllExist.rgA α m c z|
                  + z ^ P * |Work.FTS.EllExist.rgB α m c z|) := hmain
        _ = K * (z ^ (-Q) * |Work.FTS.EllExist.rgA α m c z|) := by rw [hBz]; ring
        _ ≤ K * (z ^ (-Q) * (M * b ^ Work.FTS.EllExist.rgQ α m
              / Work.FTS.EllExist.rgQ α m)) := by
            refine mul_le_mul_of_nonneg_left ?_ hKpos.le
            exact mul_le_mul_of_nonneg_left hAz hzK.le
        _ = Work.FTS.EllExist.rgK α m
              * (z ^ (-(Work.FTS.EllExist.rgQ α m))
                  * (M * b ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m)) := by
            rw [hKdef, hQdef]
        _ ≤ RadGreenSupp.C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) :=
            RadGreenSupp.cmp3 hα ha hab hM hm hz hbz

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgG1_cont_Ioi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS.PhiStar.Honesty

theorem rgG1_cont_Ioi {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ContinuousOn (fun z : ℝ => Work.FTS.EllExist.rgG1 α m c z) (Set.Ioi 0) := by
  -- the forward integrand is interval integrable on every `[0,z]`, `z > 0`
  have hF1 := rgF1_integrableOn_Ioc (α := α) (m := m) (c := c) hα hα4 hm hc hnear hfar
  have hII : ∀ z : ℝ, 0 < z →
      IntervalIntegrable (Work.FTS.EllExist.rgF1 α m c) volume (0 : ℝ) z :=
    fun z hz => (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mpr (hF1 z hz)
  -- hence the primitive `rgA z = ∫ t in 0..z, rgF1 α m c t` is continuous on `(0,∞)`
  have hA : ContinuousOn (fun z : ℝ => Work.FTS.EllExist.rgA α m c z) (Set.Ioi 0) := by
    simpa only [Work.FTS.EllExist.rgA] using
      Work.FTS.EllipticEst.Cert.GbarSin.continuousOn_primitive_Ioi hII
  -- and the prefactor `z ↦ z^{-q}` is continuous there
  have hr : ContinuousOn (fun z : ℝ => z ^ (-(Work.FTS.EllExist.rgQ α m))) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz))
  exact hr.mul hA

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.rgG1_pt_bound =====
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

set_option maxHeartbeats 1600000

/-! ### Auxiliary lemmas -/
private lemma setIntegral_Ioc_eq_interval {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (h : ∀ t ∈ Set.Ioc a b, f t = g t) :
    (∫ t in Set.Ioc a b, f t) = ∫ t in a..b, g t := by
  rw [intervalIntegral.integral_of_le hab]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc h

/-- `(x + y)² ≤ 2x² + 2y²`. -/
private lemma sq_add_le_two {x y : ℝ} : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

/-- `(t^{a/2})² = t^a` for `t > 0`. -/
private lemma rpow_half_sq {t : ℝ} (ht : 0 < t) {a : ℝ} :
    (t ^ (a / 2)) ^ 2 = t ^ a := by
  rw [sq, ← Real.rpow_add ht]
  congr 1
  ring


/-- **Pointwise bound for the decaying Green branch in the far field.**

With `q = rgQ α m ≥ 28`, `rgG1 α m c z = z^{-q} ∫_0^z c t t^{q-1} dt` and
`rgA α m c z = ∫_0^z c t t^{q-1} dt = ∫_0^1 rgF1 + ∫_1^z rgF1`, Cauchy–Schwarz on `(1,z]`
gives `(∫_1^z rgF1)² ≤ (∫_1^z (c t)² t^{q-1})(∫_1^z t^{q-1}) ≤ z^q ∫_1^z (c t)² t^{q-1}`,
and `(x + y)² ≤ 2x² + 2y²` then yields the pointwise bound. -/
theorem rgG1_pt_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ z : ℝ, 1 < z →
      (Work.FTS.EllExist.rgG1 α m c z) ^ 2
        ≤ 2 * (∫ t in (0 : ℝ)..1, Work.FTS.EllExist.rgF1 α m c t) ^ 2
              * z ^ (-(2 * Work.FTS.EllExist.rgQ α m))
          + 2 * z ^ (-(Work.FTS.EllExist.rgQ α m))
              * (∫ t in (1 : ℝ)..z, (c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)) := by
  obtain ⟨_, hF1_1z, -⟩ := rgHonest_aemeas hα hα4 hm hc hnear hfar
  have hq28 : 28 ≤ Work.FTS.EllExist.rgQ α m := Work.FTS.EllExist.rgQ_ge hα hα4 hm
  have hq1 : (1 : ℝ) < Work.FTS.EllExist.rgQ α m := by linarith
  have hqm1 : 0 < Work.FTS.EllExist.rgQ α m - 1 := by linarith
  have hqm1le : 0 ≤ Work.FTS.EllExist.rgQ α m - 1 := le_of_lt hqm1
  have h2qm1 : 0 < 2 * Work.FTS.EllExist.rgQ α m - 1 := by linarith
  -- abbreviations
  set A0 : ℝ := ∫ t in (0 : ℝ)..1, Work.FTS.EllExist.rgF1 α m c t with hA0
  set J : ℝ → ℝ := fun z => ∫ t in (1 : ℝ)..z, Work.FTS.EllExist.rgF1 α m c t with hJ
  set KK : ℝ → ℝ := fun z => ∫ t in (1 : ℝ)..z, (c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1) with hKK
  -- ### the splitting of the forward primitive
  have hsplit : ∀ z : ℝ, 1 ≤ z → Work.FTS.EllExist.rgA α m c z = A0 + J z := by
    intro z hz
    have h := rgA_integral_add_adjacent hα hα4 hm hc hnear hfar z hz
    simpa [hA0, hJ] using h
  -- ### integrability of `t^(q-1)` and of `(c t)^2 t^(q-1)` on `(1,z]`
  have hLint_Ioc : ∀ z : ℝ, 1 ≤ z →
      IntegrableOn (fun t : ℝ => t ^ (Work.FTS.EllExist.rgQ α m - 1)) (Set.Ioc (1 : ℝ) z) := by
    intro z hz
    have hcont : ContinuousOn (fun t : ℝ => t ^ (Work.FTS.EllExist.rgQ α m - 1)) (Set.Icc (1 : ℝ) z) :=
      continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
    exact (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hkIoc : ∀ z : ℝ, 1 ≤ z →
      IntegrableOn (fun t : ℝ => (c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)) (Set.Ioc (1 : ℝ) z) := by
    intro z hz
    have h1 : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioc (1 : ℝ) z) :=
      hfar.mono_set (fun t ht => ht.1)
    have hbdd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 : ℝ) z)),
        ‖t ^ (Work.FTS.EllExist.rgQ α m - 1)‖ ≤ z ^ (Work.FTS.EllExist.rgQ α m - 1) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht.1
      rw [Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
      exact Real.rpow_le_rpow ht0.le ht.2 hqm1le
    have haesm : AEStronglyMeasurable (fun t : ℝ => t ^ (Work.FTS.EllExist.rgQ α m - 1))
        (volume.restrict (Set.Ioc (1 : ℝ) z)) :=
      (measurable_id.pow_const (Work.FTS.EllExist.rgQ α m - 1)).aestronglyMeasurable
    have hb1 : Integrable (fun t : ℝ => t ^ (Work.FTS.EllExist.rgQ α m - 1) * (c t) ^ 2)
        (volume.restrict (Set.Ioc (1 : ℝ) z)) :=
      Integrable.bdd_mul h1 haesm hbdd
    exact hb1.congr (ae_of_all _ (fun t => mul_comm (t ^ (Work.FTS.EllExist.rgQ α m - 1)) ((c t) ^ 2)))
  -- ### nonnegativity of `KK`
  have hKKnn : ∀ z : ℝ, 1 ≤ z → 0 ≤ KK z := by
    intro z hz
    simp only [hKK]
    exact intervalIntegral.integral_nonneg hz
      (fun t ht => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_trans zero_le_one ht.1) _))
  -- ### Cauchy-Schwarz for `J`
  have hCS : ∀ z : ℝ, 1 ≤ z → (J z) ^ 2 ≤ KK z * (∫ t in (1 : ℝ)..z, t ^ (Work.FTS.EllExist.rgQ α m - 1)) := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
    have hf2 : Integrable (fun t : ℝ => (c t * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) ^ 2)
        (volume.restrict (Set.Ioc (1 : ℝ) z)) := by
      refine (hkIoc z hz).congr_fun_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht.1
      rw [mul_pow, rpow_half_sq ht0]
    have hg2 : Integrable (fun t : ℝ => (t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) ^ 2)
        (volume.restrict (Set.Ioc (1 : ℝ) z)) := by
      refine (hLint_Ioc z hz).congr_fun_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht.1
      rw [rpow_half_sq ht0]
    have hfg : Integrable (fun t : ℝ => (c t * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2))
        (volume.restrict (Set.Ioc (1 : ℝ) z)) := by
      refine (hF1_1z z hz).congr_fun_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht.1
      simp only [Work.FTS.EllExist.rgF1]
      rw [mul_assoc, ← Real.rpow_add ht0,
        show (Work.FTS.EllExist.rgQ α m - 1) / 2 + (Work.FTS.EllExist.rgQ α m - 1) / 2 = Work.FTS.EllExist.rgQ α m - 1 from by ring]
    have hcs := CSTools.sq_integral_mul_le (μ := volume.restrict (Set.Ioc (1 : ℝ) z)) hf2 hg2 hfg
    have e1 : (∫ t, (c t * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)
          ∂(volume.restrict (Set.Ioc (1 : ℝ) z))) = J z := by
      rw [setIntegral_Ioc_eq_interval hz
        (f := fun t => (c t * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2))
        (g := Work.FTS.EllExist.rgF1 α m c) (fun t ht => by
          have ht0 : 0 < t := lt_trans zero_lt_one ht.1
          simp only [Work.FTS.EllExist.rgF1]
          rw [mul_assoc, ← Real.rpow_add ht0,
            show (Work.FTS.EllExist.rgQ α m - 1) / 2 + (Work.FTS.EllExist.rgQ α m - 1) / 2 = Work.FTS.EllExist.rgQ α m - 1 from by ring])]
    have e2 : (∫ t, (c t * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) ^ 2
          ∂(volume.restrict (Set.Ioc (1 : ℝ) z))) = KK z := by
      rw [setIntegral_Ioc_eq_interval hz (f := fun t => (c t * t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) ^ 2)
        (g := fun t => (c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)) (fun t ht => by
          have ht0 : 0 < t := lt_trans zero_lt_one ht.1
          rw [mul_pow, rpow_half_sq ht0])]
    have e3 : (∫ t, (t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) ^ 2 ∂(volume.restrict (Set.Ioc (1 : ℝ) z)))
        = ∫ t in (1 : ℝ)..z, t ^ (Work.FTS.EllExist.rgQ α m - 1) := by
      rw [setIntegral_Ioc_eq_interval hz (f := fun t => (t ^ ((Work.FTS.EllExist.rgQ α m - 1) / 2)) ^ 2)
        (g := fun t => t ^ (Work.FTS.EllExist.rgQ α m - 1)) (fun t ht => by
          have ht0 : 0 < t := lt_trans zero_lt_one ht.1
          rw [rpow_half_sq ht0])]
    rw [e1, e2, e3] at hcs
    exact hcs
  -- ### the bound `∫_1^z t^{q-1} ≤ z^q`
  have hLz : ∀ z : ℝ, 1 ≤ z → (∫ t in (1 : ℝ)..z, t ^ (Work.FTS.EllExist.rgQ α m - 1)) ≤ z ^ Work.FTS.EllExist.rgQ α m := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
    have hcont : ContinuousOn (fun t : ℝ => t ^ (Work.FTS.EllExist.rgQ α m - 1)) (Set.Icc (1 : ℝ) z) :=
      continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
    have hi1 : IntervalIntegrable (fun t : ℝ => t ^ (Work.FTS.EllExist.rgQ α m - 1)) volume (1 : ℝ) z :=
      hcont.intervalIntegrable_of_Icc hz
    have hi2 : IntervalIntegrable (fun _ : ℝ => z ^ (Work.FTS.EllExist.rgQ α m - 1)) volume (1 : ℝ) z :=
      intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on hz hi1 hi2
      (fun t ht => Real.rpow_le_rpow (le_trans zero_le_one ht.1) ht.2 hqm1le)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hzq : (z - 1) * z ^ (Work.FTS.EllExist.rgQ α m - 1) ≤ z ^ Work.FTS.EllExist.rgQ α m := by
      have h1 : (z - 1) * z ^ (Work.FTS.EllExist.rgQ α m - 1) ≤ z * z ^ (Work.FTS.EllExist.rgQ α m - 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hz0.le _)
      have h2 : z * z ^ (Work.FTS.EllExist.rgQ α m - 1) = z ^ Work.FTS.EllExist.rgQ α m := by
        calc z * z ^ (Work.FTS.EllExist.rgQ α m - 1) = z ^ (1 : ℝ) * z ^ (Work.FTS.EllExist.rgQ α m - 1) := by rw [Real.rpow_one]
          _ = z ^ ((1 : ℝ) + (Work.FTS.EllExist.rgQ α m - 1)) := (Real.rpow_add hz0 1 (Work.FTS.EllExist.rgQ α m - 1)).symm
          _ = z ^ Work.FTS.EllExist.rgQ α m := by
                rw [show (1 : ℝ) + (Work.FTS.EllExist.rgQ α m - 1) = Work.FTS.EllExist.rgQ α m from by ring]
      linarith [h1, h2.le]
    linarith [hmono, hzq]
  -- ### the pointwise bound
  have hpt : ∀ z : ℝ, 1 < z →
      (Work.FTS.EllExist.rgG1 α m c z) ^ 2
        ≤ 2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) + 2 * z ^ (-(Work.FTS.EllExist.rgQ α m)) * KK z := by
    intro z hz
    have hz0 : 0 < z := lt_trans zero_lt_one hz
    have hz1 : 1 ≤ z := le_of_lt hz
    have hG : (Work.FTS.EllExist.rgG1 α m c z) ^ 2
        = z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * (Work.FTS.EllExist.rgA α m c z) ^ 2 := by
      simp only [Work.FTS.EllExist.rgG1, mul_pow]
      rw [show (z ^ (-(Work.FTS.EllExist.rgQ α m))) ^ 2 = z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) from by
            rw [sq, ← Real.rpow_add hz0]
            congr 1
            ring]
    have h1 : (Work.FTS.EllExist.rgA α m c z) ^ 2 ≤ 2 * A0 ^ 2 + 2 * (J z) ^ 2 := by
      rw [hsplit z hz1]
      exact sq_add_le_two
    have hExp : z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * z ^ Work.FTS.EllExist.rgQ α m = z ^ (-(Work.FTS.EllExist.rgQ α m)) := by
      rw [← Real.rpow_add hz0]
      congr 1
      ring
    have h3 : z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * (J z) ^ 2 ≤ z ^ (-(Work.FTS.EllExist.rgQ α m)) * KK z := by
      have h4 : (J z) ^ 2 ≤ KK z * z ^ Work.FTS.EllExist.rgQ α m :=
        le_trans (hCS z hz1) (mul_le_mul_of_nonneg_left (hLz z hz1) (hKKnn z hz1))
      have h5 : z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * (J z) ^ 2 ≤ z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * (KK z * z ^ Work.FTS.EllExist.rgQ α m) :=
        mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hz0.le _)
      have h6 : z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * (KK z * z ^ Work.FTS.EllExist.rgQ α m) = z ^ (-(Work.FTS.EllExist.rgQ α m)) * KK z := by
        rw [mul_comm (KK z) (z ^ Work.FTS.EllExist.rgQ α m), ← mul_assoc, hExp]
      linarith [h5, h6.le]
    calc (Work.FTS.EllExist.rgG1 α m c z) ^ 2
        = z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * (Work.FTS.EllExist.rgA α m c z) ^ 2 := hG
      _ ≤ z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * (2 * A0 ^ 2 + 2 * (J z) ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hz0.le _)
      _ = 2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) + 2 * (z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) * (J z) ^ 2) := by ring
      _ ≤ 2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) + 2 * (z ^ (-(Work.FTS.EllExist.rgQ α m)) * KK z) := by linarith [h3]
      _ = 2 * A0 ^ 2 * z ^ (-(2 * Work.FTS.EllExist.rgQ α m)) + 2 * z ^ (-(Work.FTS.EllExist.rgQ α m)) * KK z := by ring
  simpa [hA0, hJ, hKK] using hpt

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.psiAngBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real
open Filter

namespace Work.FTS.PhiStar.Series.Deleg

open Work.FTS.PhiStar.Gegenbauer (eFam gC gC_ode contDiff_gC)


/-! ## The target -/

theorem psiAngBounds :
    (∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
          ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))) ∧
    (∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |deriv (Work.FTS.PhiStar.Gegenbauer.eFam m) θ|
          ≤ 100 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 2) ∧
    (∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |iteratedDeriv 2 (Work.FTS.PhiStar.Gegenbauer.eFam m) θ|
          ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
              * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
            / (Real.cos θ) ^ 4) ∧
    (∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |deriv (fun θ' => Real.tan θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ|
          ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 3) := by
  have hsqr : ∀ m : ℕ, Real.sqrt (Npsi m) * Real.sqrt (Npsi m) = Npsi m :=
    fun m => Real.mul_self_sqrt (le_of_lt (Npsi_pos m))
  have hsqrt1 : ∀ m : ℕ, 1 ≤ Real.sqrt (Npsi m) := by
    intro m
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (Npsi_ge_one m)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m θ hθ
    show |eFam m θ| ≤ Real.sqrt (Npsi m)
    obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
    have he : eFam m θ = ug m (Real.sin θ) / Real.cos θ := by
      show Real.cos θ * gC (2 * m + 1) (Real.sin θ) = ug m (Real.sin θ) / Real.cos θ
      rw [gC_div_ug m hθ]
      field_simp
    rw [he, abs_div, abs_of_pos hc, div_le_iff₀ hc]
    exact ug_sin_bound m hθ
  · intro m θ hθ
    show |deriv (Work.FTS.PhiStar.Gegenbauer.eFam m) θ|
      ≤ 100 * Npsi m / (Real.cos θ) ^ 2
    obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
    have hsabs : |Real.sin θ| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith, hs1⟩
    rw [deriv_eFam m θ]
    calc |-Real.sin θ * gC (2 * m + 1) (Real.sin θ)
          + (Real.cos θ) ^ 2 * deriv (gC (2 * m + 1)) (Real.sin θ)|
        ≤ |Real.sin θ * gC (2 * m + 1) (Real.sin θ)|
          + |(Real.cos θ) ^ 2 * deriv (gC (2 * m + 1)) (Real.sin θ)| := by
            have h2 : |(-Real.sin θ) * gC (2 * m + 1) (Real.sin θ)|
                = |Real.sin θ * gC (2 * m + 1) (Real.sin θ)| := by
              simp only [abs_mul, abs_neg]
            rw [← h2]
            exact abs_add_le _ _
      _ = |Real.sin θ| * |gC (2 * m + 1) (Real.sin θ)|
          + |(Real.cos θ) ^ 2 * deriv (gC (2 * m + 1)) (Real.sin θ)| := by
            simp only [abs_mul]
      _ ≤ 1 * (Real.sqrt (Npsi m) / Real.cos θ)
          + (Npsi m + 2 * Real.sqrt (Npsi m) / Real.cos θ) := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul hsabs (gC_abs_bound m hθ) (abs_nonneg _) (by norm_num)
            · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.cos θ) ^ 2)]
              exact c2_mul_deriv_gC_bound m hθ
      _ = Npsi m + 3 * Real.sqrt (Npsi m) / Real.cos θ := by ring
      _ ≤ 100 * Npsi m / (Real.cos θ) ^ 2 := by
            have h := arith2 hc hc1 (hsqrt1 m)
            rw [Real.sq_sqrt (le_of_lt (Npsi_pos m))] at h
            exact h
  · intro m θ hθ
    show |iteratedDeriv 2 (Work.FTS.PhiStar.Gegenbauer.eFam m) θ|
      ≤ 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.cos θ) ^ 4
    obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
    have hi : iteratedDeriv 2 (eFam m) θ = deriv (deriv (eFam m)) θ := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [hi, deriv2_eFam m θ]
    have hlin : -Real.cos θ * gC (2 * m + 1) (Real.sin θ)
        - 3 * Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ)
        + (Real.cos θ) ^ 3 * deriv (deriv (gC (2 * m + 1))) (Real.sin θ)
        = Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ)
          - (Npsi m - 1) * (Real.cos θ * gC (2 * m + 1) (Real.sin θ)) := by
      have hode := (gC_ode (2 * m + 1)).2 (Real.sin θ)
      have hN : Npsi m - 2 = (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) := by
        rw [Npsi_eq_two]; ring
      have hkey : (Real.cos θ) ^ 2 * deriv (deriv (gC (2 * m + 1))) (Real.sin θ)
          = 4 * Real.sin θ * deriv (gC (2 * m + 1)) (Real.sin θ)
            - (Npsi m - 2) * gC (2 * m + 1) (Real.sin θ) := by
        have hh := hode
        rw [hsq, ← hN] at hh
        linarith
      linear_combination Real.cos θ * hkey
    rw [hlin]
    have hN1 : 0 ≤ Npsi m - 1 := by have h := Npsi_ge_one m; linarith
    calc |Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ)
          - (Npsi m - 1) * (Real.cos θ * gC (2 * m + 1) (Real.sin θ))|
        ≤ |Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ)|
          + |(Npsi m - 1) * (Real.cos θ * gC (2 * m + 1) (Real.sin θ))| :=
            abs_sub_le_add _ _
      _ ≤ (Npsi m + 2 * Real.sqrt (Npsi m) / Real.cos θ) / Real.cos θ
          + (Npsi m - 1) * Real.sqrt (Npsi m) := by
            refine add_le_add (scq_bound m hθ) ?_
            rw [abs_mul, abs_of_nonneg hN1, abs_mul, abs_of_nonneg (le_of_lt hc)]
            exact mul_le_mul_of_nonneg_left (c_mul_gC_bound m hθ) hN1
      _ = Npsi m / Real.cos θ + 2 * Real.sqrt (Npsi m) / (Real.cos θ) ^ 2
          + (Npsi m - 1) * Real.sqrt (Npsi m) := by
            have hcne : Real.cos θ ≠ 0 := ne_of_gt hc
            field_simp
            try ring
      _ ≤ 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.cos θ) ^ 4 := by
            have h := arith3 hc hc1 (hsqrt1 m)
            rw [Real.sq_sqrt (le_of_lt (Npsi_pos m))] at h
            exact h
  · intro m θ hθ
    show |deriv (fun θ' => Real.tan θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ|
      ≤ 1000 * Npsi m / (Real.cos θ) ^ 3
    obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
    rw [deriv_tan_eFam m (ne_of_gt hc)]
    calc |Real.cos θ * gC (2 * m + 1) (Real.sin θ)
          + Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ)|
        ≤ |Real.cos θ * gC (2 * m + 1) (Real.sin θ)|
          + |Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ)| :=
            abs_add_le _ _
      _ ≤ Real.sqrt (Npsi m)
          + (Npsi m + 2 * Real.sqrt (Npsi m) / Real.cos θ) / Real.cos θ := by
            refine add_le_add ?_ (scq_bound m hθ)
            rw [abs_mul, abs_of_nonneg (le_of_lt hc)]
            exact c_mul_gC_bound m hθ
      _ = Real.sqrt (Npsi m) + Npsi m / Real.cos θ
          + 2 * Real.sqrt (Npsi m) / (Real.cos θ) ^ 2 := by
            have hcne : Real.cos θ ≠ 0 := ne_of_gt hc
            field_simp
            try ring
      _ ≤ 1000 * Npsi m / (Real.cos θ) ^ 3 := by
            have h := arith4 hc hc1 (hsqrt1 m)
            rw [Real.sq_sqrt (le_of_lt (Npsi_pos m))] at h
            exact h

end Work.FTS.PhiStar.Series.Deleg
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsZero.Bridge.HintL =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsZero.Bridge

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# `HintL`: the `L₁₂`-weighted `(z,θ)`-integrand is integrable

The radial factor of the angular data `K(θ)Γ(θ)` is bounded by `3` on `Iθ = [0,π/2]`
(lemma `integrableOn_GamK` records its integrability), while the radial factor

  `z ↦ L₁₂(f)(z) / (1+z)²`

is dominated by `C / (1+z)²` for `z > 0`, where `C = ∫_{Ioi 0} |L12dens f|` is the `L¹`-mass
of the density: by `Work.FM.L12` the operator `L₁₂(f)(z) = ∫_{s > z} L12dens f s ds` is the
tail integral of the density, whence `|L₁₂(f)(z)| ≤ ∫_{s > z} |L12dens f s| ≤ C` for `z > 0`.
Since `z ↦ 1/(1+z)²` is integrable on `(0,∞)`, the product is integrable on
`Ioi 0 ×ˢ Iθ`; the dominating function is produced from `MeasureTheory.Integrable.mul_prod`
(Fubini for the product measure), and the measurability of the integrand from the continuity
of the tail integral (`Work.FTS.StrongEps.continuousOn_integral_Ioi`).
-/

theorem HintL {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hintL2 : MeasureTheory.IntegrableOn (Work.Construction.L12dens f) (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.Gam α p.2
        * (Work.Coercivity.L12f f p.1 / (1 + p.1) ^ 2))
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
  -- the `L¹`-mass of the density
  set C : ℝ := ∫ s in Set.Ioi 0, |Work.Construction.L12dens f s| with hCdef
  have hC0 : 0 ≤ C := integral_nonneg fun s => abs_nonneg (Work.Construction.L12dens f s)
  -- `L₁₂(f)` is the tail integral of the density, hence continuous on `[0,∞)` …
  have hcont0 : ContinuousOn (fun z : ℝ => ∫ s in Set.Ioi z, Work.Construction.L12dens f s)
      (Set.Ici 0) := Work.FTS.StrongEps.continuousOn_integral_Ioi hintL2
  have hcont : ContinuousOn (Work.Coercivity.L12f f) (Set.Ici 0) := hcont0
  have hfun : Work.Coercivity.L12f f
      = fun z : ℝ => ∫ s in Set.Ioi z, Work.Construction.L12dens f s := rfl
  -- … and bounded by `C` on `(0,∞)`.
  have hL12bd : ∀ z ∈ Set.Ioi (0:ℝ), |Work.Coercivity.L12f f z| ≤ C := by
    intro z hz
    have h1 : |∫ s in Set.Ioi z, Work.Construction.L12dens f s| ≤
        ∫ s in Set.Ioi z, |Work.Construction.L12dens f s| := by
      have := MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioi z)) (f := fun s => Work.Construction.L12dens f s)
      simpa only [Real.norm_eq_abs] using this
    have h2 : (∫ s in Set.Ioi z, |Work.Construction.L12dens f s|) ≤ C := by
      rw [hCdef]
      exact MeasureTheory.setIntegral_mono_set hintL2.abs
        (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (Filter.Eventually.of_forall (Set.Ioi_subset_Ioi hz.le))
    rw [hfun]
    exact le_trans h1 h2
  -- the angular factor is bounded by `3` on `Iθ`
  have hKG : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.K θ * Work.Spaces.Gam α θ| ≤ 3 := by
    intro θ hθ
    have hsin : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hb0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hsin (by positivity)
    have hb1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ), hsin]
    have hrp : (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) ≤ 1 :=
      Real.rpow_le_one hb0 hb1 (by linarith)
    have hK0 : 0 ≤ Work.Spaces.K θ := by rw [Work.Spaces.K]; positivity
    have hK3 : Work.Spaces.K θ ≤ 3 := by rw [Work.Spaces.K]; nlinarith [hb1]
    have hG0 : 0 ≤ Work.Spaces.Gam α θ := by rw [Work.Spaces.Gam]; exact Real.rpow_nonneg hb0 _
    rw [abs_of_nonneg (mul_nonneg hK0 hG0)]
    calc Work.Spaces.K θ * Work.Spaces.Gam α θ ≤ 3 * 1 := mul_le_mul hK3 hrp hG0 (by norm_num)
      _ = 3 := by norm_num
  -- continuity of the angular factor on `Iθ`, and of the two factors on the product set
  have hKGcont : ContinuousOn (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.Gam α θ)
      Work.Spaces.Iθ := by
    have hα3 : (0 : ℝ) ≤ α / 3 := by linarith
    have hu : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ :=
      (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
    have h1 : ContinuousOn (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
        Work.Spaces.Iθ := hu.rpow_const (fun θ _ => Or.inr hα3)
    have hK : ContinuousOn (fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ :=
      ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)).continuousOn
    have h2 : ContinuousOn (fun θ : ℝ =>
        (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) * (3 * Real.sin θ * Real.cos θ ^ 2))
        Work.Spaces.Iθ := h1.mul hK
    refine h2.congr (fun θ _ => ?_)
    simp only [Work.Spaces.K, Work.Spaces.Gam]
    ring
  have hKGprod : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.Gam α p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    hKGcont.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hRadcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Coercivity.L12f f p.1 / (1 + p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
    have hφ : ContinuousOn (fun z : ℝ => Work.Coercivity.L12f f z / (1 + z) ^ 2)
        (Set.Ioi 0) :=
      (hcont.mono Set.Ioi_subset_Ici_self).div
        (((continuous_const.add continuous_id).pow 2).continuousOn)
        (fun z hz => by
          have hz0 : (0:ℝ) < z := hz
          have h1 : (0:ℝ) < 1 + z := by linarith
          exact pow_ne_zero 2 (ne_of_gt h1))
    exact hφ.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.Gam α p.2
        * (Work.Coercivity.L12f f p.1 / (1 + p.1) ^ 2))
      (volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) :=
    (hKGprod.mul hRadcont).aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Icc)
  -- the dominating function `(1/(1+z)²)·(3C)` is integrable (Fubini on the product measure)
  have hrad : MeasureTheory.IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) (Set.Ioi 0) := by
    have h := integrableOn_add_rpow_Ioi_of_lt (a := (-2:ℝ)) (c := 0) (m := 1)
      (by norm_num) (by norm_num)
    refine h.congr_fun (fun z hz => ?_) measurableSet_Ioi
    show (z + 1) ^ (-2 : ℝ) = 1 / (1 + z) ^ 2
    rw [show (-2 : ℝ) = -(2:ℝ) by norm_num,
      Real.rpow_neg (by linarith [show (0:ℝ) < z from hz]), Real.rpow_two, inv_eq_one_div]
    ring
  have hIθfin : volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hconst : MeasureTheory.Integrable (fun _ : ℝ => 3 * C) (volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.integrableOn_const hIθfin
  have hmul := MeasureTheory.Integrable.mul_prod hrad hconst
  have hdom : MeasureTheory.Integrable (fun p : ℝ × ℝ => (1 / (1 + p.1) ^ 2) * (3 * C))
      (volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict] at hmul
    exact hmul
  -- the pointwise domination
  have hbound : ∀ᵐ p ∂(volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)),
      ‖Work.Spaces.K p.2 * Work.Spaces.Gam α p.2
        * (Work.Coercivity.L12f f p.1 / (1 + p.1) ^ 2)‖ ≤ (1 / (1 + p.1) ^ 2) * (3 * C) := by
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ioi.prod measurableSet_Icc) (fun p hp => ?_)
    have hpz : (0:ℝ) < p.1 := hp.1
    have h1z : (0:ℝ) < 1 + p.1 := by linarith
    have hpos : (0:ℝ) < (1 + p.1) ^ 2 := pow_pos h1z 2
    have hb1 : |Work.Coercivity.L12f f p.1| / (1 + p.1) ^ 2 ≤ C / (1 + p.1) ^ 2 :=
      div_le_div_of_nonneg_right (hL12bd p.1 hp.1) hpos.le
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hpos]
    calc |Work.Spaces.K p.2 * Work.Spaces.Gam α p.2|
          * (|Work.Coercivity.L12f f p.1| / (1 + p.1) ^ 2)
        ≤ 3 * (C / (1 + p.1) ^ 2) :=
          mul_le_mul (hKG p.2 hp.2) hb1 (by positivity) (by norm_num)
      _ = (1 / (1 + p.1) ^ 2) * (3 * C) := by ring
  exact MeasureTheory.Integrable.mono' hdom haesm hbound

end Work.FTS.StrongEps.EpsZero.Bridge
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.DzIter_eq_sum_scoef_of_contDiffOn_order =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6

open scoped Real Topology ContDiff
open Set Filter

noncomputable section

set_option autoImplicit false

/-!
# The Stirling expansion of `D_z^n` from `C^n` on an open set

`D_z = z ∂_z` and `∂_z` satisfy `∂_z ∘ D_z = D_z ∘ ∂_z + ∂_z`, so that

`D_z^n f = ∑_{k = 0}^{n} S(n,k) z^k ∂_z^k f`

with `S(n,k) = Work.Spaces.scoef n k` the Stirling numbers of the second kind.

The existing statements of this expansion ask for more differentiability than is needed:
`Work.Spaces.DzIter_eq_sum_scoef` wants the `z`-slice to be analytic, and
`Work.FTS.GalBasis.Xmb.DzIter_eq_sum_scoef_of_contDiffOn` wants `C^{n+1}` on the open set.
Here the hypothesis is exactly `C^n` on an open set `U ⊆ ℝ × ℝ`, which is what the
finite-order `C⁶`-interior machinery has available.

The induction is the usual one.  At level `n + 1` on the open set `U` we differentiate the
level-`n` expansion, which needs each `z ↦ ∂_z^k h(z,θ)`, `k ≤ n`, to be differentiable;
`C^{n+1}` supplies this (`k + 1 ≤ n + 1`), and `C^{n+1}` restricts to `C^n` for the
induction hypothesis.
-/

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

/-- `deriv` of the `k`-th iterated `z`-derivative of a `z`-slice is the `(k+1)`-st one. -/
private theorem deriv_pzIter_slice (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    deriv (fun z' => Work.Spaces.pzIter k h z' θ) z = Work.Spaces.pzIter (k + 1) h z θ := rfl

/-- **The Stirling expansion of `D_z^n` in the genuine smooth order**: for `h` of class
`C^n` on an open set `U ⊆ ℝ × ℝ`,
`D_z^n h = ∑_{k ≤ n} S(n,k) z^k ∂_z^k h` on `U`. -/
theorem DzIter_eq_sum_scoef_of_contDiffOn_order {h : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) :
    ∀ n : ℕ, ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry h) U →
      ∀ z θ, (z, θ) ∈ U →
        Work.Spaces.DzIter n h z θ
          = ∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ) * (z ^ k * Work.Spaces.pzIter k h z θ) := by
  intro n
  induction n with
  | zero =>
      intro _ z θ _
      rw [Finset.sum_range_one, show Work.Spaces.scoef 0 0 = 1 from rfl]
      norm_num
  | succ n ih =>
      intro hsm z θ hzθ
      -- the hypothesis of the induction hypothesis: `C^n ⊂ C^{n+1}`
      have hsm' : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry h) U :=
        hsm.of_le (Nat.cast_le.mpr (show n ≤ n + 1 by omega))
      -- differentiability of the `z`-slices of the iterated `z`-derivatives at `z`
      have hdiff : ∀ k : ℕ, k ≤ n →
          DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k h z' θ) z := fun k hk =>
        Work.FTS.GalBasis.Xmb.differentiableAt_slice_pzIter hU hsm (i := k) (by omega) hzθ
      have hd1 : ∀ k : ℕ, DifferentiableAt ℝ (fun z' : ℝ => z' ^ k) z := fun k =>
        differentiableAt_pow k
      have hd3 : ∀ k : ℕ, k ≤ n →
          DifferentiableAt ℝ (fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ) z :=
        fun k hk => (hd1 k).mul (hdiff k hk)
      -- the induction hypothesis, as an eventual equality near `z`
      have hsl : {z' : ℝ | (z', θ) ∈ U} ∈ 𝓝 z := by
        have hopen : IsOpen {z' : ℝ | (z', θ) ∈ U} :=
          hU.preimage (by fun_prop : Continuous fun z' : ℝ => (z', θ))
        exact hopen.mem_nhds hzθ
      have hev : (fun z' => Work.Spaces.DzIter n h z' θ)
          =ᶠ[𝓝 z] (fun z' => ∑ k ∈ Finset.range (n + 1),
              (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
        filter_upwards [hsl] with z' hz'
        exact ih hsm' z' θ hz'
      -- the derivative of each summand
      have hterm : ∀ k : ℕ, k ≤ n →
          deriv (fun z' : ℝ => (Work.Spaces.scoef n k : ℝ)
              * (z' ^ k * Work.Spaces.pzIter k h z' θ)) z
            = (Work.Spaces.scoef n k : ℝ)
                * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                    + z ^ k * Work.Spaces.pzIter (k + 1) h z θ) := by
        intro k hk
        rw [deriv_const_mul (d := fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ)
          (Work.Spaces.scoef n k : ℝ) ((hd1 k).mul (hdiff k hk))]
        congr 1
        have hmul := deriv_mul (c := fun z' : ℝ => z' ^ k)
          (d := fun z' : ℝ => Work.Spaces.pzIter k h z' θ) (hd1 k) (hdiff k hk)
        have hmul' : deriv (fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ) z
            = deriv (fun z' : ℝ => z' ^ k) z * Work.Spaces.pzIter k h z θ
              + z ^ k * deriv (fun z' : ℝ => Work.Spaces.pzIter k h z' θ) z := hmul
        rw [hmul', deriv_zpow, deriv_pzIter_slice]
      -- differentiate the whole sum
      have hderiv : deriv (fun z' => Work.Spaces.DzIter n h z' θ) z
          = ∑ k ∈ Finset.range (n + 1),
              (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                + z ^ k * Work.Spaces.pzIter (k + 1) h z θ) := by
        rw [Filter.EventuallyEq.deriv_eq hev]
        have hsumfun : (fun z' => ∑ k ∈ Finset.range (n + 1),
              (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ))
            = (∑ k ∈ Finset.range (n + 1),
                fun z' => (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
          funext z'
          simp [Finset.sum_apply]
        rw [hsumfun, deriv_sum (fun k hk => (hd3 k
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).const_mul (Work.Spaces.scoef n k : ℝ))]
        exact Finset.sum_congr rfl fun k hk =>
          hterm k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      calc Work.Spaces.DzIter (n + 1) h z θ
          = z * deriv (fun z' => Work.Spaces.DzIter n h z' θ) z := by
            simp [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
        _ = z * (∑ k ∈ Finset.range (n + 1),
              (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                + z ^ k * Work.Spaces.pzIter (k + 1) h z θ)) := by rw [hderiv]
        _ = ∑ k ∈ Finset.range (n + 1),
              (Work.Spaces.scoef n k : ℝ) * ((k : ℝ) * z ^ k * Work.Spaces.pzIter k h z θ
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

end

end Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.AngProfAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option maxHeartbeats 1600000

/-! ## Smoothness helpers for `dthU` on an open interval

`dthU φ = sin(2·)·φ'`; on an open set it preserves `C^∞` and its iterates are additive.
These are the two local facts used to differentiate `aProf α`. -/

lemma contDiffOn_dthU_open {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Spaces.dthU f) U := by
  have hd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv f) U :=
    hf.deriv_of_isOpen hU (by simp)
  have hsin : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ : ℝ => Real.sin (2 * θ)) U := by
    fun_prop
  have h := hsin.mul hd
  refine h.congr (fun θ _ => ?_)
  simp only [Work.Spaces.dthU]

lemma contDiffOn_dthU_iter_open {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) (m : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Spaces.dthU^[m] f) U := by
  induction m with
  | zero => simpa using hf
  | succ m ih => rw [Function.iterate_succ_apply']; exact contDiffOn_dthU_open hU ih

/-- Additivity of the `dthU`-iterates on an open set. -/
lemma dthU_iter_add_eqOn {U : Set ℝ} (hU : IsOpen U) {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U)
    (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g U) (m : ℕ) :
    ∀ θ ∈ U, (Work.Spaces.dthU^[m] (f + g)) θ
      = (Work.Spaces.dthU^[m] f) θ + (Work.Spaces.dthU^[m] g) θ := by
  induction m with
  | zero => intro θ _; simp
  | succ m ih =>
      intro θ hθ
      have hfU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Spaces.dthU^[m] f) U :=
        contDiffOn_dthU_iter_open hU hf m
      have hgU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Spaces.dthU^[m] g) U :=
        contDiffOn_dthU_iter_open hU hg m
      have hdiff_f : DifferentiableAt ℝ (Work.Spaces.dthU^[m] f) θ :=
        (hfU.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp)
      have hdiff_g : DifferentiableAt ℝ (Work.Spaces.dthU^[m] g) θ :=
        (hgU.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp)
      have hev : (Work.Spaces.dthU^[m] (f + g)) =ᶠ[𝓝 θ]
          (Work.Spaces.dthU^[m] f + Work.Spaces.dthU^[m] g) := by
        filter_upwards [hU.mem_nhds hθ] with x hx
        simp only [Pi.add_apply]
        exact ih x hx
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply']
      simp only [Work.Spaces.dthU_apply]
      rw [hev.deriv_eq, deriv_add hdiff_f hdiff_g]
      ring

/-- `Γ(θ) = (sin θ · cos²θ)^{α/3}` is `C^∞` on the open interval. -/
lemma contDiffOn_Gam_Ioo (α : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ : ℝ => Work.Spaces.Gam α θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hbase : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by
    intro θ hθ
    have h1 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have h := hbase.rpow (contDiffOn_const (c := α / 3)) hne
  refine h.congr (fun θ _ => ?_)
  simp only [Work.Spaces.Gam]

/-- The angular profile `aProf α` is `C^∞` on the open interval. -/
lemma contDiffOn_aProf (α : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ : ℝ => aProf α θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hgam := contDiffOn_Gam_Ioo α
  have hdth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun θ : ℝ => Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (contDiffOn_dthU_open isOpen_Ioo hgam).congr (fun θ _ => rfl)
  have hsin : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun θ : ℝ => 2 * Real.sin θ ^ 2 * Work.Spaces.Gam α θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ : ℝ => 2 * Real.sin θ ^ 2)
        (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
    exact h1.mul hgam
  have hsum := hdth.add hsin
  have hfin := hsum.const_smul (-(α / Work.Spaces.c α))
  refine hfin.congr (fun θ _ => ?_)
  simp only [aProf, smul_eq_mul, Pi.add_apply]

/-- `dthU φ` vanishes at the two endpoints of `Iθ`, for every `φ`. -/
lemma dthU_zero_left (φ : ℝ → ℝ) : Work.Spaces.dthU φ 0 = 0 := by
  rw [Work.Spaces.dthU_apply, show 2 * (0 : ℝ) = 0 from by ring, Real.sin_zero, zero_mul]

lemma dthU_zero_right (φ : ℝ → ℝ) : Work.Spaces.dthU φ (Real.pi / 2) = 0 := by
  rw [Work.Spaces.dthU_apply, show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi,
    zero_mul]

end Work.FTS.StrongPersist.L3Rhs.NfkAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.dthU_c2m_bound6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular bound `|D_θ^j (c2m)| ≤ 100000 · sin(2θ)²` for `1 ≤ j ≤ 6`

`Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound` supplies the four orders `1 ≤ j ≤ 4` for the
angular coefficient `Work.Construction.c2m θ = cos(2θ) - sin²θ` of the transport term.  This
file adds the two remaining orders `j = 5, 6` needed by
`Work.FTS.StrongPersist.dthU_c2m_bound6`.

With `u = sin(2θ)`, `v = cos(2θ)` (so that `c2m = (3v-1)/2`, `u' = 2v`, `v' = -2u` and
`D_θ = u ∂_θ`), the closed forms are

* `D_θ^5 c2m = 4224 u⁴v² - 768 u⁶ - 768 u²v⁴ = u²(4224 u²v² - 768 u⁴ - 768 v⁴)`, whence
  `|D_θ^5 c2m| ≤ 5760 u²` (only `|u|, |v| ≤ 1` are used);
* `D_θ^6 c2m = 39936 u⁴v³ - 26112 u⁶v - 3072 u²v⁵ = u²(39936 u²v³ - 26112 u⁴v - 3072 v⁵)`,
  whence `|D_θ^6 c2m| ≤ 69120 u²`.

The derivatives are obtained by explicit differentiation (`HasDerivAt` on the two
trigonometric factors), as in `dthU_c2m_bound`.
-/

namespace Work.FTS.StrongPersist

open Work.Spaces

/-! ## The fifth iterate `D_θ^5 c2m` -/

/-- `(θ ↦ 384 sin(2θ)⁴cos(2θ) - 192 sin(2θ)²cos(2θ)³)' = 4224 sin(2θ)³cos(2θ)²
- 768 sin(2θ)⁵ - 768 sin(2θ)cos(2θ)⁴`. -/
private lemma dthU_c2m_f4_deriv (θ : ℝ) :
    deriv (fun t : ℝ => (384 : ℝ) * (Real.sin (2 * t)) ^ 4 * Real.cos (2 * t)
        - 192 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 3) θ
      = 4224 * (Real.sin (2 * θ)) ^ 3 * (Real.cos (2 * θ)) ^ 2
        - 768 * (Real.sin (2 * θ)) ^ 5
        - 768 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 4 := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h2.sin
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h2.cos
  have hs4 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 4)
      (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 4
  have hs2 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hc3 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 3)
      (3 * (Real.cos (2 * θ)) ^ (3 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 3
  have hA : HasDerivAt (fun t : ℝ => (384 : ℝ) * (Real.sin (2 * t)) ^ 4 * Real.cos (2 * t))
      ((384 * (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2))) * Real.cos (2 * θ)
        + (384 * (Real.sin (2 * θ)) ^ 4) * (-Real.sin (2 * θ) * 2)) θ :=
    (hs4.const_mul 384).mul hc
  have hB : HasDerivAt (fun t : ℝ => (192 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 3)
      ((192 * (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2))) * (Real.cos (2 * θ)) ^ 3
        + (192 * (Real.sin (2 * θ)) ^ 2)
          * (3 * (Real.cos (2 * θ)) ^ (3 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs2.const_mul 192).mul hc3
  have hfin := hA.sub hB
  rw [show (fun t : ℝ => (384 : ℝ) * (Real.sin (2 * t)) ^ 4 * Real.cos (2 * t)
        - 192 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 3)
      = ((fun t : ℝ => (384 : ℝ) * (Real.sin (2 * t)) ^ 4 * Real.cos (2 * t))
        - (fun t : ℝ => (192 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 3)) from by
    funext t; rfl,
    hfin.deriv]
  ring

/-- `D_θ (384 u⁴v - 192 u²v³) = 4224 u⁴v² - 768 u⁶ - 768 u²v⁴`. -/
private lemma dthU_f4_eq :
    dthU (fun θ : ℝ => (384 : ℝ) * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)
        - 192 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3)
      = fun θ : ℝ => 4224 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 2
          - 768 * (Real.sin (2 * θ)) ^ 6
          - 768 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 4 := by
  funext θ
  rw [dthU_apply, dthU_c2m_f4_deriv θ]
  ring

/-! ## The sixth iterate `D_θ^6 c2m` -/

/-- `(θ ↦ 4224 sin(2θ)⁴cos(2θ)² - 768 sin(2θ)⁶ - 768 sin(2θ)²cos(2θ)⁴)' =
39936 sin(2θ)³cos(2θ)³ - 26112 sin(2θ)⁵cos(2θ) - 3072 sin(2θ)cos(2θ)⁵`. -/
private lemma dthU_c2m_f5_deriv (θ : ℝ) :
    deriv (fun t : ℝ => 4224 * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 2
        - 768 * (Real.sin (2 * t)) ^ 6
        - 768 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 4) θ
      = 39936 * (Real.sin (2 * θ)) ^ 3 * (Real.cos (2 * θ)) ^ 3
        - 26112 * (Real.sin (2 * θ)) ^ 5 * Real.cos (2 * θ)
        - 3072 * Real.sin (2 * θ) * (Real.cos (2 * θ)) ^ 5 := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := h2.sin
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := h2.cos
  have hs4 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 4)
      (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 4
  have hv2 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 2)
      (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 2
  have hs6 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 6)
      (6 * (Real.sin (2 * θ)) ^ (6 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 6
  have hs2 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2)) θ := hs.pow 2
  have hv4 : HasDerivAt (fun t : ℝ => (Real.cos (2 * t)) ^ 4)
      (4 * (Real.cos (2 * θ)) ^ (4 - 1) * (-Real.sin (2 * θ) * 2)) θ := hc.pow 4
  have hA : HasDerivAt (fun t : ℝ => (4224 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 2)
      ((4224 * (4 * (Real.sin (2 * θ)) ^ (4 - 1) * (Real.cos (2 * θ) * 2))) * (Real.cos (2 * θ)) ^ 2
        + (4224 * (Real.sin (2 * θ)) ^ 4)
          * (2 * (Real.cos (2 * θ)) ^ (2 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs4.const_mul 4224).mul hv2
  have hB : HasDerivAt (fun t : ℝ => (768 : ℝ) * (Real.sin (2 * t)) ^ 6)
      (768 * (6 * (Real.sin (2 * θ)) ^ (6 - 1) * (Real.cos (2 * θ) * 2))) θ :=
    hs6.const_mul 768
  have hC : HasDerivAt (fun t : ℝ => (768 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 4)
      ((768 * (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (Real.cos (2 * θ) * 2))) * (Real.cos (2 * θ)) ^ 4
        + (768 * (Real.sin (2 * θ)) ^ 2)
          * (4 * (Real.cos (2 * θ)) ^ (4 - 1) * (-Real.sin (2 * θ) * 2))) θ :=
    (hs2.const_mul 768).mul hv4
  have hfin := (hA.sub hB).sub hC
  rw [show (fun t : ℝ => 4224 * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 2
        - 768 * (Real.sin (2 * t)) ^ 6
        - 768 * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 4)
      = (((fun t : ℝ => (4224 : ℝ) * (Real.sin (2 * t)) ^ 4 * (Real.cos (2 * t)) ^ 2)
          - (fun t : ℝ => (768 : ℝ) * (Real.sin (2 * t)) ^ 6))
        - (fun t : ℝ => (768 : ℝ) * (Real.sin (2 * t)) ^ 2 * (Real.cos (2 * t)) ^ 4)) from by
    funext t; rfl,
    hfin.deriv]
  ring

/-- `D_θ (4224 u⁴v² - 768 u⁶ - 768 u²v⁴) = 39936 u⁴v³ - 26112 u⁶v - 3072 u²v⁵`. -/
private lemma dthU_f5_eq :
    dthU (fun θ : ℝ => 4224 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 2
        - 768 * (Real.sin (2 * θ)) ^ 6
        - 768 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 4)
      = fun θ : ℝ => 39936 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 3
          - 26112 * (Real.sin (2 * θ)) ^ 6 * Real.cos (2 * θ)
          - 3072 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 5 := by
  funext θ
  rw [dthU_apply, dthU_c2m_f5_deriv θ]
  ring

/-! ## The two iterates, as values -/

/-- `D_θ^5 c2m = 4224 sin(2θ)⁴cos(2θ)² - 768 sin(2θ)⁶ - 768 sin(2θ)²cos(2θ)⁴`. -/
private lemma dthU_c2m_iter_five (θ : ℝ) :
    (dthU^[5]) Work.Construction.c2m θ
      = 4224 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 2
        - 768 * (Real.sin (2 * θ)) ^ 6
        - 768 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 4 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ_apply',
    show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ_apply',
    show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply',
    show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
    Function.iterate_one,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f1_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f2_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f3_eq,
    dthU_f4_eq]

/-- `D_θ^6 c2m = 39936 sin(2θ)⁴cos(2θ)³ - 26112 sin(2θ)⁶cos(2θ) - 3072 sin(2θ)²cos(2θ)⁵`. -/
private lemma dthU_c2m_iter_six (θ : ℝ) :
    (dthU^[6]) Work.Construction.c2m θ
      = 39936 * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 3
        - 26112 * (Real.sin (2 * θ)) ^ 6 * Real.cos (2 * θ)
        - 3072 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 5 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, Function.iterate_succ_apply',
    show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ_apply',
    show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ_apply',
    show (3 : ℕ) = 2 + 1 from rfl, Function.iterate_succ_apply',
    show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
    Function.iterate_one,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f1_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f2_eq,
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_f3_eq,
    dthU_f4_eq, dthU_f5_eq]

/-! ## The two pointwise bounds -/

/-- `|c · u^a · v^b| ≤ c` when `c ≥ 0` and `|u|, |v| ≤ 1`. -/
private lemma abs_mul_pow_pow_le {c u v : ℝ} (hc : 0 ≤ c) (hu : |u| ≤ 1) (hv : |v| ≤ 1)
    (a b : ℕ) : |c * u ^ a * v ^ b| ≤ c := by
  have h1 : |u| ^ a ≤ 1 := pow_le_one₀ (abs_nonneg u) hu
  have h2 : |v| ^ b ≤ 1 := pow_le_one₀ (abs_nonneg v) hv
  have hp : |u| ^ a * |v| ^ b ≤ 1 := by
    have := mul_le_mul h1 h2 (pow_nonneg (abs_nonneg v) b) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using this
  calc |c * u ^ a * v ^ b| = c * (|u| ^ a * |v| ^ b) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_pow, abs_pow]; ring
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left hp hc
    _ = c := by ring

/-- `|D_θ^5 c2m θ| ≤ 100000 sin(2θ)²`. -/
private lemma dthU_c2m_iter_five_bound (θ : ℝ) :
    |(dthU^[5]) Work.Construction.c2m θ| ≤ 100000 * (Real.sin (2 * θ)) ^ 2 := by
  rw [dthU_c2m_iter_five]
  have hu2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (2 * θ), sq_nonneg (Real.cos (2 * θ))]
  have hv2 : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (2 * θ), sq_nonneg (Real.sin (2 * θ))]
  have hu4 : (Real.sin (2 * θ)) ^ 4 ≤ 1 := by
    nlinarith [hu2, sq_nonneg (Real.sin (2 * θ))]
  have hv4 : (Real.cos (2 * θ)) ^ 4 ≤ 1 := by
    nlinarith [hv2, sq_nonneg (Real.cos (2 * θ))]
  have huv : (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [hu2, hv2, sq_nonneg (Real.sin (2 * θ)), sq_nonneg (Real.cos (2 * θ))]
  have hkey : (4224 : ℝ) * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 2
        - 768 * (Real.sin (2 * θ)) ^ 6
        - 768 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 4
      = (Real.sin (2 * θ)) ^ 2
        * (4224 * ((Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2)
          - 768 * (Real.sin (2 * θ)) ^ 4 - 768 * (Real.cos (2 * θ)) ^ 4) := by
    ring
  rw [hkey, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
  have hX : |(4224 : ℝ) * ((Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 2)
      - 768 * (Real.sin (2 * θ)) ^ 4 - 768 * (Real.cos (2 * θ)) ^ 4| ≤ 100000 := by
    rw [abs_le]
    constructor <;>
      nlinarith [huv, hu4, hv4, sq_nonneg (Real.sin (2 * θ)), sq_nonneg (Real.cos (2 * θ)),
        mul_nonneg (sq_nonneg (Real.sin (2 * θ))) (sq_nonneg (Real.cos (2 * θ)))]
  have := mul_le_mul_of_nonneg_left hX (sq_nonneg (Real.sin (2 * θ)))
  linarith [this]

/-- `|D_θ^6 c2m θ| ≤ 100000 sin(2θ)²`. -/
private lemma dthU_c2m_iter_six_bound (θ : ℝ) :
    |(dthU^[6]) Work.Construction.c2m θ| ≤ 100000 * (Real.sin (2 * θ)) ^ 2 := by
  rw [dthU_c2m_iter_six]
  have hu2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (2 * θ), sq_nonneg (Real.cos (2 * θ))]
  have hv2 : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (2 * θ), sq_nonneg (Real.sin (2 * θ))]
  have hu : |Real.sin (2 * θ)| ≤ 1 := (sq_le_one_iff_abs_le_one _).mp hu2
  have hv : |Real.cos (2 * θ)| ≤ 1 := (sq_le_one_iff_abs_le_one _).mp hv2
  have hkey : (39936 : ℝ) * (Real.sin (2 * θ)) ^ 4 * (Real.cos (2 * θ)) ^ 3
        - 26112 * (Real.sin (2 * θ)) ^ 6 * Real.cos (2 * θ)
        - 3072 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 5
      = (Real.sin (2 * θ)) ^ 2
        * (39936 * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
          - 26112 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)
          - 3072 * (Real.cos (2 * θ)) ^ 5) := by
    ring
  rw [hkey, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
  have hm1 : |(39936 : ℝ) * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3| ≤ 39936 :=
    abs_mul_pow_pow_le (by norm_num) hu hv 2 3
  have hm2 : |(26112 : ℝ) * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)| ≤ 26112 := by
    simpa using abs_mul_pow_pow_le (c := (26112 : ℝ)) (u := Real.sin (2 * θ))
      (v := Real.cos (2 * θ)) (by norm_num) hu hv 4 1
  have hm3 : |(3072 : ℝ) * (Real.cos (2 * θ)) ^ 5| ≤ 3072 := by
    simpa using abs_mul_pow_pow_le (c := (3072 : ℝ)) (u := Real.cos (2 * θ)) (v := (1 : ℝ))
      (by norm_num) hv (by norm_num) 5 0
  have htri1 : |(39936 : ℝ) * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
      - 26112 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)|
      ≤ |(39936 : ℝ) * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3|
        + |(26112 : ℝ) * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)| := by
    have h := abs_add_le ((39936 : ℝ) * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3)
      (-((26112 : ℝ) * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)))
    simpa [sub_eq_add_neg] using h
  have htri2 : |((39936 : ℝ) * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
      - 26112 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)) - 3072 * (Real.cos (2 * θ)) ^ 5|
      ≤ |(39936 : ℝ) * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
          - 26112 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)|
        + |(3072 : ℝ) * (Real.cos (2 * θ)) ^ 5| := by
    have h := abs_add_le ((39936 : ℝ) * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
      - 26112 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ))
      (-((3072 : ℝ) * (Real.cos (2 * θ)) ^ 5))
    simpa [sub_eq_add_neg] using h
  have hX : |(39936 : ℝ) * (Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ)) ^ 3
      - 26112 * (Real.sin (2 * θ)) ^ 4 * Real.cos (2 * θ)
      - 3072 * (Real.cos (2 * θ)) ^ 5| ≤ 100000 := by
    linarith [htri1, htri2, hm1, hm2, hm3]
  have := mul_le_mul_of_nonneg_left hX (sq_nonneg (Real.sin (2 * θ)))
  linarith [this]

theorem dthU_c2m_bound6 : ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ), 1 ≤ j → j ≤ 6 → ∀ θ : ℝ,
    |(Work.Spaces.dthU^[j] Work.Construction.c2m) θ| ≤ C * (Real.sin (2 * θ)) ^ 2 := by
  refine ⟨100000, by norm_num, ?_⟩
  intro j hj1 hj6 θ
  interval_cases j
  · have h := Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound 1 le_rfl (by norm_num) θ
    nlinarith [h, sq_nonneg (Real.sin (2 * θ))]
  · have h := Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound 2 (by norm_num) (by norm_num) θ
    nlinarith [h, sq_nonneg (Real.sin (2 * θ))]
  · have h := Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound 3 (by norm_num) (by norm_num) θ
    nlinarith [h, sq_nonneg (Real.sin (2 * θ))]
  · have h := Work.FTS.Nonlinear.FstarPkg.dthU_c2m_bound 4 (by norm_num) (by norm_num) θ
    nlinarith [h, sq_nonneg (Real.sin (2 * θ))]
  · exact dthU_c2m_iter_five_bound θ
  · exact dthU_c2m_iter_six_bound θ

end Work.FTS.StrongPersist
end
-- ===== merged: Submission.Work.FTS.Top.Rescale.Basic =====
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

/-! ## The `C¹` reparametrisation -/

/-- **`ContDiffOn` is preserved by the time rescaling** (a reparametrisation: the field
`(timeScale c u).uncurry` is `smulCLM c ∘ u.uncurry ∘ timeCLM c`). -/
theorem contDiffOn_uncurry_timeScale {c : ℝ} {s t : Set (R3 × ℝ)} {u : R3 → ℝ → R3}
    (hΦ : Set.MapsTo (timeCLM c) s t) (h : ContDiffOn ℝ 1 u.uncurry t) :
    ContDiffOn ℝ 1 (timeScale c u).uncurry s := by
  have hlin : ContDiffOn ℝ 1 (fun z : R3 × ℝ => timeCLM c z) s := (timeCLM c).contDiff.contDiffOn
  have h1 : ContDiffOn ℝ 1 (fun z => u.uncurry (timeCLM c z)) s := h.comp hlin hΦ
  have h2 : ContDiffOn ℝ 1 (fun z => c • u.uncurry (timeCLM c z)) s := h1.const_smul c
  have hEq : (timeScale c u).uncurry = fun z : R3 × ℝ => c • u.uncurry (timeCLM c z) := rfl
  rw [hEq]
  exact h2

/-- **`ContDiffOn` is preserved by the time rescaling of the pressure** (the scalar version). -/
theorem contDiffOn_uncurry_timeScaleP {c : ℝ} {s t : Set (R3 × ℝ)} {p : R3 → ℝ → ℝ}
    (hΦ : Set.MapsTo (timeCLM c) s t) (h : ContDiffOn ℝ 1 p.uncurry t) :
    ContDiffOn ℝ 1 (timeScaleP c p).uncurry s := by
  have hlin : ContDiffOn ℝ 1 (fun z : R3 × ℝ => timeCLM c z) s := (timeCLM c).contDiff.contDiffOn
  have h1 : ContDiffOn ℝ 1 (fun z => p.uncurry (timeCLM c z)) s := h.comp hlin hΦ
  have h2 : ContDiffOn ℝ 1 (fun z => c ^ 2 • p.uncurry (timeCLM c z)) s := h1.const_smul (c ^ 2)
  have hEq : (timeScaleP c p).uncurry = fun z : R3 × ℝ => c ^ 2 • p.uncurry (timeCLM c z) := rfl
  rw [hEq]
  exact h2

/-! ## Slices of a jointly `C¹` field at interior times -/

/-- If `u.uncurry` is `C¹` on the slab `ℝ³ × V` with `V` open, then at every time
`t ∈ V` both slices through `(x,t)` are differentiable: `t' ↦ u x t'` at `t` and `x' ↦ u x' t` at
`x`.  (Openness is only used to upgrade `ContDiffWithinAt` to `ContDiffAt`.)  This is what makes
the `deriv`-based `timeDeriv` and the `fderiv`-based `directionalDeriv` comparable with the
derivatives of the rescaled field. -/
theorem differentiableAt_slice_of_contDiffOn {u : R3 → ℝ → R3} {V : Set ℝ} (hV : IsOpen V)
    {t : ℝ} {x : R3} (h : ContDiffOn ℝ 1 u.uncurry (Set.univ ×ˢ V)) (ht : t ∈ V) :
    DifferentiableAt ℝ (u x) t ∧ DifferentiableAt ℝ (u · t) x := by
  have hmem : (x, t) ∈ Set.univ ×ˢ V := ⟨trivial, ht⟩
  have hopen : IsOpen (Set.univ ×ˢ V : Set (R3 × ℝ)) := isOpen_univ.prod hV
  have hca : ContDiffAt ℝ 1 u.uncurry (x, t) :=
    (h.contDiffWithinAt hmem).contDiffAt (hopen.mem_nhds hmem)
  have hd : DifferentiableAt ℝ u.uncurry (x, t) := hca.differentiableAt (by norm_num)
  have hleft : DifferentiableAt ℝ (fun s : ℝ => (x, s)) t :=
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) (E := R3) (F := ℝ) x t).differentiableAt
  have hright : DifferentiableAt ℝ (fun y : R3 => (y, t)) x :=
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) (E := R3) (F := ℝ) x t).differentiableAt
  refine ⟨?_, ?_⟩
  · show DifferentiableAt ℝ (fun s : ℝ => u.uncurry (x, s)) t
    exact hd.comp t hleft
  · show DifferentiableAt ℝ (fun y : R3 => u.uncurry (y, t)) x
    exact hd.comp x hright

/-! ## The Euler equation is invariant under the time rescaling -/

/-- **The Euler equation is preserved by the time rescaling.**  If `(p,u)` solves
`∂ₜu + (u·∇)u + ∇p = 0` at every `(x,t')` with `t' ∈ Ioo 0 T`, then the rescaled pair
`(timeScaleP c p, timeScale c u)` solves it at every `(x,t)` with `t ∈ Ioo 0 1`, provided
`0 < c` and `c ≤ T` (so that `c·t < T`).

All three terms of the equation are multiplied by the *same* factor `c²`, and the equation at
`(x, c·t)` is the given one. -/
theorem euler_eq_timeScale {c T : ℝ} (hc : 0 < c) (hcT : c ≤ T)
    {p : R3 → ℝ → ℝ} {u : R3 → ℝ → R3}
    (hcu : ContDiffOn ℝ 1 u.uncurry (Set.univ ×ˢ Set.Ioo 0 T))
    (heq : ∀ x, ∀ t ∈ Set.Ioo 0 T,
      timeDeriv u x t + directionalDeriv u u x t + spaceGrad p x t = 0) :
    ∀ x, ∀ t ∈ Set.Ioo 0 1,
      timeDeriv (timeScale c u) x t + directionalDeriv (timeScale c u) (timeScale c u) x t
        + spaceGrad (timeScaleP c p) x t = 0 := by
  intro x t ht
  have hct : c * t ∈ Set.Ioo 0 T :=
    ⟨mul_pos hc ht.1, by nlinarith [ht.2, hc, hcT]⟩
  have hd1 : DifferentiableAt ℝ (u x) (c * t) :=
    (differentiableAt_slice_of_contDiffOn isOpen_Ioo hcu hct).1
  have hsum : timeDeriv u x (c * t) + directionalDeriv u u x (c * t) + spaceGrad p x (c * t) = 0 :=
    heq x (c * t) hct
  rw [timeDeriv_timeScale c u x t hd1, directionalDeriv_timeScale,
    Work.FTS.Top.Rescale.spaceGrad_timeScaleP,
    ← smul_add, ← smul_add, hsum, smul_zero]

/-! ## The datum classes are preserved by the value scaling -/

/-- The `edist`/`dist` bridge for `HolderWith`. -/
theorem holderWith_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C r : ℝ≥0} {f : X → Y}
    (h : ∀ x y, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (r : ℝ)) : HolderWith C r f := by
  intro x y
  rw [edist_dist, edist_dist, ENNReal.coe_nnreal_eq,
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg,
    ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x y)

/-- **Oddness is preserved by the value scaling** `v ↦ (fun x => c • v x)`: multiplying each
component by the same constant preserves the parity profile of `IsOdd`. -/
theorem isOdd_const_smul {c : ℝ} {v : R3 → R3} (h : IsOdd v) :
    IsOdd (fun x => c • v x) := by
  have hsmul : ∀ (i : Fin 3) (y : R3),
      (((fun x : R3 => c • v x) y).ofLp i) = c * ((v y).ofLp i) := by
    intro i y
    simp only [PiLp.smul_apply, smul_eq_mul]
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x₁ x₂
    obtain ⟨ha, hb, hc⟩ := h1 x₁ x₂
    refine ⟨?_, ?_, ?_⟩
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x, x₁, x₂]).ofLp 0))
            = fun x : ℝ => c * ((v !₂[x, x₁, x₂]).ofLp 0) from by
          funext t; exact hsmul 0 _]
      exact ha.const_smul c
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x, x₁, x₂]).ofLp 1))
            = fun x : ℝ => c * ((v !₂[x, x₁, x₂]).ofLp 1) from by
          funext t; exact hsmul 1 _]
      exact hb.const_smul c
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x, x₁, x₂]).ofLp 2))
            = fun x : ℝ => c * ((v !₂[x, x₁, x₂]).ofLp 2) from by
          funext t; exact hsmul 2 _]
      exact hc.const_smul c
  · intro x₀ x₂
    obtain ⟨ha, hb, hc⟩ := h2 x₀ x₂
    refine ⟨?_, ?_, ?_⟩
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x₀, x, x₂]).ofLp 0))
            = fun x : ℝ => c * ((v !₂[x₀, x, x₂]).ofLp 0) from by
          funext t; exact hsmul 0 _]
      exact ha.const_smul c
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x₀, x, x₂]).ofLp 1))
            = fun x : ℝ => c * ((v !₂[x₀, x, x₂]).ofLp 1) from by
          funext t; exact hsmul 1 _]
      exact hb.const_smul c
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x₀, x, x₂]).ofLp 2))
            = fun x : ℝ => c * ((v !₂[x₀, x, x₂]).ofLp 2) from by
          funext t; exact hsmul 2 _]
      exact hc.const_smul c
  · intro x₀ x₁
    obtain ⟨ha, hb, hc⟩ := h3 x₀ x₁
    refine ⟨?_, ?_, ?_⟩
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x₀, x₁, x]).ofLp 0))
            = fun x : ℝ => c * ((v !₂[x₀, x₁, x]).ofLp 0) from by
          funext t; exact hsmul 0 _]
      exact ha.const_smul c
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x₀, x₁, x]).ofLp 1))
            = fun x : ℝ => c * ((v !₂[x₀, x₁, x]).ofLp 1) from by
          funext t; exact hsmul 1 _]
      exact hb.const_smul c
    · rw [show (fun x : ℝ => (((fun x : R3 => c • v x) !₂[x₀, x₁, x]).ofLp 2))
            = fun x : ℝ => c * ((v !₂[x₀, x₁, x]).ofLp 2) from by
          funext t; exact hsmul 2 _]
      exact hc.const_smul c

/-- **The `C^{1,α}` class is preserved by the value scaling** `v ↦ (fun x => c • v x)`:
`fderiv (c • v) = c • fderiv v` (`fderiv_const_smul_field`), scaled boundedness and scaled
Holder continuity. -/
theorem isContDiffHolder_const_smul {α : ℝ≥0} {c : ℝ} {v : R3 → R3}
    (h : IsContDiffHolder ℝ α v) : IsContDiffHolder ℝ α (fun x => c • v x) := by
  obtain ⟨hcd, hbdd, hholder⟩ := h
  refine ⟨hcd.const_smul c, ?_, ?_⟩
  · rw [IsBoundedFun, IsBoundedFunOn, Set.image_univ] at hbdd ⊢
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbdd
    rw [isBounded_iff_forall_norm_le]
    refine ⟨‖c‖ * C, fun y hy => ?_⟩
    obtain ⟨x, rfl⟩ := hy
    rw [fderiv_const_smul_apply c v x, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC (fderiv ℝ v x) (Set.mem_range_self x)) (norm_nonneg c)
  · obtain ⟨C, hC⟩ := hholder
    refine ⟨‖c‖₊ * C, holderWith_of_dist_le fun x y => ?_⟩
    rw [fderiv_const_smul_apply c v x, fderiv_const_smul_apply c v y]
    calc dist (c • fderiv ℝ v x) (c • fderiv ℝ v y)
        = ‖c‖ * dist (fderiv ℝ v x) (fderiv ℝ v y) := dist_smul₀ c (fderiv ℝ v x) (fderiv ℝ v y)
      _ ≤ ‖c‖ * ((C : ℝ) * dist x y ^ (α : ℝ)) :=
          mul_le_mul_of_nonneg_left (hC.dist_le x y) (norm_nonneg c)
      _ = ((‖c‖₊ * C : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ) := by
          rw [NNReal.coe_mul, coe_nnnorm]
          ring

end Work.FTS.Top
end
-- ===== merged: Submission.Work.FTS.Top.Rescale.isContDiffHolderOn_uncurry_timeScale =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology ENNReal

namespace Work.FTS.Top.Rescale

/-!
# The strip `C^{1,α}` class is preserved by the time rescaling

`(timeScale c u).uncurry z = c • u.uncurry (timeCLM c z)` for `z : R3 × ℝ`, where
`timeCLM c (x,t) = (x, c*t)` is a continuous linear map.  So the target below is a special case of
the generic reparametrisation lemma `isContDiffHolderOn_comp_clm` proved in this file:
`IsContDiffHolderOn` is stable under postcomposition with a continuous linear map `A` on the values
and precomposition with a continuous linear map `Φ` on the variables carrying the new set `s` into
the old set `t`.

The four blocks of the original route are:

* `contDiffOn_comp_clm` (in `CompCLM.Base`) — the `C¹` block, `ContDiffOn.comp` with the smooth `Φ`
  followed by `ContDiffOn` of the continuous linear map `A`;
* `fderivWithin_comp_clm` (in `CompCLM.Base`) — the within-derivative formula
  `fderivWithin ℝ (fun z => A (g (Φ z))) s z = A ∘L (fderivWithin ℝ g t (Φ z) ∘L Φ)`, obtained
  from the within chain rule (`HasFDerivWithinAt.comp`, twice) together with
  `HasFDerivWithinAt.fderivWithin`; the hypothesis "`s` is uniquely differentiable within at each
  of its points" (`huniq`) is exactly what pins the within-derivative down;
* `isBoundedFunOn_fderivWithin_comp_clm` (below) — the boundedness block, from
  `‖A ∘L (D ∘L Φ)‖ ≤ ‖A‖ * ‖D‖ * ‖Φ‖` and the boundedness of `fderivWithin ℝ g t` on `t`;
* `holderOn_fderivWithin_comp_clm` (below) — the Hölder block, from
  `dist (Φ z) (Φ w) ≤ ‖Φ‖ * dist z w` and the Hölder bound for that derivative, with the exponent
  `α`.

Nothing from `Submission.Work.SolutionDelivery.*` is imported.
-/

/-- **From the norm form to `HolderOnWith`.**  The Hölder block below produces a norm inequality;
`HolderOn` is defined through `HolderOnWith`, which is stated in `edist` coordinates.  Since `edist`
on a (pseudo)metric space is `ENNReal.ofReal` of the distance, this is `ENNReal.ofReal` applied to
the hypothesis, together with `ENNReal.ofReal_mul` and `ENNReal.ofReal_rpow_of_nonneg`. -/
theorem holderOnWith_of_norm_le {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y]
    {C r : NNReal} {f : X → Y} {s : Set X}
    (h : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ (C : ℝ) * dist x y ^ (r : ℝ)) :
    HolderOnWith C r f s := by
  intro x hx y hy
  rw [edist_dist, edist_dist, dist_eq_norm]
  calc ENNReal.ofReal ‖f x - f y‖
      ≤ ENNReal.ofReal ((C : ℝ) * dist x y ^ (r : ℝ)) := ENNReal.ofReal_le_ofReal (h x hx y hy)
    _ = ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (dist x y ^ (r : ℝ)) :=
        ENNReal.ofReal_mul (by positivity)
    _ = ↑C * ENNReal.ofReal (dist x y) ^ (r : ℝ) := by
        rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity), ENNReal.ofReal_coe_nnreal]

/-- **The boundedness block.**  If `fderivWithin ℝ g t` is bounded on `t`, then the
within-derivative of `z ↦ A (g (Φ z))` is bounded on `s`.

Indeed, on `s` that derivative is `A ∘L (D (Φ z) ∘L Φ)` with `‖D (Φ z)‖ ≤ R'`, so it is bounded by
`2 * (‖A‖ * R' * ‖Φ‖)`. -/
theorem isBoundedFunOn_fderivWithin_comp_clm {s t : Set (R3 × ℝ)}
    {g : R3 × ℝ → R3}
    (A : R3 →L[ℝ] R3)
    (Φ : (R3 × ℝ) →L[ℝ] (R3 × ℝ))
    (hΦ : MapsTo Φ s t) (huniq : ∀ z ∈ s, UniqueDiffWithinAt ℝ s z)
    (hg : DifferentiableOn ℝ g t)
    (hbdd : IsBoundedFunOn (fderivWithin ℝ g t) t) :
    IsBoundedFunOn (fderivWithin ℝ (fun z => A (g (Φ z))) s) s := by
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : (R3 × ℝ) →L[ℝ] R3)).1 hbdd
  set R' := max R 0 with hR'def
  have hR'0 : 0 ≤ R' := le_max_right _ _
  refine (Metric.isBounded_iff_subset_closedBall (0 : (R3 × ℝ) →L[ℝ] R3)).2
    ⟨2 * (‖A‖ * R' * ‖Φ‖), ?_⟩
  rintro x ⟨z, hz, rfl⟩
  have hD : ‖fderivWithin ℝ g t (Φ z)‖ ≤ R' := by
    have hmem := hR ⟨Φ z, hΦ hz, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hmem
    exact le_trans hmem (le_max_left _ _)
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero,
    fderivWithin_comp_clm A Φ hΦ huniq hg z hz]
  have hstep : ‖A ∘L (fderivWithin ℝ g t (Φ z) ∘L Φ)‖ ≤ ‖A‖ * R' * ‖Φ‖ := by
    calc ‖A ∘L (fderivWithin ℝ g t (Φ z) ∘L Φ)‖
        ≤ ‖A‖ * ‖fderivWithin ℝ g t (Φ z) ∘L Φ‖ := ContinuousLinearMap.opNorm_comp_le A _
      _ ≤ ‖A‖ * (‖fderivWithin ℝ g t (Φ z)‖ * ‖Φ‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ Φ) (norm_nonneg _)
      _ ≤ ‖A‖ * (R' * ‖Φ‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hD (norm_nonneg _)) (norm_nonneg _)
      _ = ‖A‖ * R' * ‖Φ‖ := by ring
  have hnn : 0 ≤ ‖A‖ * R' * ‖Φ‖ :=
    mul_nonneg (mul_nonneg (norm_nonneg _) hR'0) (norm_nonneg _)
  linarith [hstep, hnn]

/-- **The Hölder block.**  If the within-derivative of `g` is `α`-Hölder on `t`, then so is the
within-derivative of `z ↦ A (g (Φ z))` on `s`, with constant `‖A‖ * ‖Φ‖ * C * ‖Φ‖ ^ α`. -/
theorem holderOn_fderivWithin_comp_clm {α : NNReal} {s t : Set (R3 × ℝ)}
    {g : R3 × ℝ → R3}
    (A : R3 →L[ℝ] R3)
    (Φ : (R3 × ℝ) →L[ℝ] (R3 × ℝ))
    (hΦ : MapsTo Φ s t) (huniq : ∀ z ∈ s, UniqueDiffWithinAt ℝ s z)
    (hg : DifferentiableOn ℝ g t)
    (hholder : HolderOn α (fderivWithin ℝ g t) t) :
    HolderOn α (fderivWithin ℝ (fun z => A (g (Φ z))) s) s := by
  obtain ⟨C, hC⟩ := hholder
  refine ⟨Real.toNNReal (‖A‖ * ‖Φ‖ * (C : ℝ) * ‖Φ‖ ^ (α : ℝ)), ?_⟩
  apply holderOnWith_of_norm_le
  intro x hx y hy
  rw [Real.coe_toNNReal _ (by positivity)]
  rw [fderivWithin_comp_clm A Φ hΦ huniq hg x hx, fderivWithin_comp_clm A Φ hΦ huniq hg y hy]
  set X := fderivWithin ℝ g t (Φ x) with hX
  set Y := fderivWithin ℝ g t (Φ y) with hY
  have hbound : ‖X - Y‖ ≤ (C : ℝ) * dist (Φ x) (Φ y) ^ (α : ℝ) := by
    have h := norm_le_of_holderOnWith hC (Φ x) (hΦ hx) (Φ y) (hΦ hy)
    rwa [← hX, ← hY] at h
  have hdist : dist (Φ x) (Φ y) ≤ ‖Φ‖ * dist x y := by
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖Φ x - Φ y‖ = ‖Φ (x - y)‖ := by rw [map_sub]
      _ ≤ ‖Φ‖ * ‖x - y‖ := ContinuousLinearMap.le_opNorm Φ (x - y)
  have hdistα : dist (Φ x) (Φ y) ^ (α : ℝ) ≤ ‖Φ‖ ^ (α : ℝ) * dist x y ^ (α : ℝ) := by
    calc dist (Φ x) (Φ y) ^ (α : ℝ)
        ≤ (‖Φ‖ * dist x y) ^ (α : ℝ) := Real.rpow_le_rpow dist_nonneg hdist (by positivity)
      _ = ‖Φ‖ ^ (α : ℝ) * dist x y ^ (α : ℝ) := Real.mul_rpow (norm_nonneg _) dist_nonneg
  have hsub : A ∘L X ∘L Φ - A ∘L Y ∘L Φ = A ∘L (X - Y) ∘L Φ := by
    apply ContinuousLinearMap.ext
    intro v
    simp
  rw [hsub]
  calc ‖A ∘L (X - Y) ∘L Φ‖
      ≤ ‖A ∘L (X - Y)‖ * ‖Φ‖ := ContinuousLinearMap.opNorm_comp_le (A ∘L (X - Y)) Φ
    _ ≤ (‖A‖ * ‖X - Y‖) * ‖Φ‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le A (X - Y)) (norm_nonneg _)
    _ ≤ (‖A‖ * ((C : ℝ) * dist (Φ x) (Φ y) ^ (α : ℝ))) * ‖Φ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbound (norm_nonneg _)) (norm_nonneg _)
    _ ≤ (‖A‖ * ((C : ℝ) * (‖Φ‖ ^ (α : ℝ) * dist x y ^ (α : ℝ)))) * ‖Φ‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdistα C.coe_nonneg) (norm_nonneg _))
          (norm_nonneg _)
    _ = (‖A‖ * ‖Φ‖ * (C : ℝ) * ‖Φ‖ ^ (α : ℝ)) * dist x y ^ (α : ℝ) := by ring

/-- **The reparametrisation lemma**: `IsContDiffHolderOn` is stable under postcomposition with a
continuous linear map `A` and precomposition with a continuous linear map `Φ` carrying `s` into
`t`. -/
theorem isContDiffHolderOn_comp_clm {α : NNReal} {s t : Set (R3 × ℝ)}
    {g : R3 × ℝ → R3}
    (A : R3 →L[ℝ] R3)
    (Φ : (R3 × ℝ) →L[ℝ] (R3 × ℝ))
    (hΦ : MapsTo Φ s t) (huniq : ∀ z ∈ s, UniqueDiffWithinAt ℝ s z)
    (h : IsContDiffHolderOn ℝ α g t) :
    IsContDiffHolderOn ℝ α (fun z => A (g (Φ z))) s :=
  ⟨contDiffOn_comp_clm A Φ hΦ h.1,
   isBoundedFunOn_fderivWithin_comp_clm A Φ hΦ huniq (h.1.differentiableOn (by norm_num)) h.2.1,
   holderOn_fderivWithin_comp_clm A Φ hΦ huniq (h.1.differentiableOn (by norm_num)) h.2.2⟩

/-
The strip `C^{1,α}` class is preserved by the time rescaling.

`(timeScale c u).uncurry z = c • u.uncurry (timeCLM c z)` for `z : R3 × ℝ`, where
`timeCLM c (x,t) = (x, c*t)` is a continuous linear map (`Work.FTS.Top.timeCLM`; the identity is
`Work.FTS.Top.timeScale_uncurry`).  So this is a reparametrisation result for `IsContDiffHolderOn`.

IMPORTANT: prove it self-containedly in this file.  Do NOT import `Submission.Work.SolutionDelivery.*`
(that subtree is on the lead's drop list and is not a supported dependency); you may read
`Submission/Work/SolutionDelivery/Scaling/isContDiffHolderOn_rescale.lean` for technique only.

Structure of the proof:

* the `C¹` block: `ContDiffOn.comp` with the smooth `timeCLM c`, then `ContDiffOn.const_smul`;
* for `s` uniquely differentiable within at each of its points, the within chain rule gives, for
  `z ∈ s`, `fderivWithin ℝ (fun z => A (g (Φ z))) s z = A ∘L (fderivWithin ℝ g t (Φ z) ∘L Φ)` for
  `A = smulCLM c` and `Φ = timeCLM c` (use `HasFDerivWithinAt.comp` twice, then
  `HasFDerivWithinAt.fderivWithin`);
* boundedness block: `‖A ∘L (D ∘L Φ)‖ ≤ ‖A‖ * ‖D‖ * ‖Φ‖` and boundedness of `fderivWithin ℝ g t`
  on `t`; Holder block: `dist (Φ z) (Φ w) ≤ ‖Φ‖ * dist z w` and the Holder bound for that
  derivative, with the exponent `α`.

Useful: `ContinuousLinearMap.contDiff`, `ContinuousLinearMap.opNorm_comp_le`,
`ContinuousLinearMap.le_opNorm`, `Real.mul_rpow`, `Real.rpow_le_rpow`, `dist_nonneg`,
`ContinuousLinearMap.norm_smul_le`.  The statement holds for every `c`, including `c = 0`
(where `timeScale 0 u = 0`).  Namespace `Work.FTS.Top`.
-/
theorem isContDiffHolderOn_uncurry_timeScale {α : NNReal} {c : ℝ}
    {s t : Set (Work.FTS.Top.R3 × ℝ)} {u : Work.FTS.Top.R3 → ℝ → Work.FTS.Top.R3}
    (hΦ : Set.MapsTo (Work.FTS.Top.timeCLM c) s t)
    (huniq : ∀ z ∈ s, UniqueDiffWithinAt ℝ s z)
    (h : IsContDiffHolderOn ℝ α u.uncurry t) :
    IsContDiffHolderOn ℝ α (Work.FTS.Top.timeScale c u).uncurry s := by
  have hmain := isContDiffHolderOn_comp_clm (Work.FTS.Top.smulCLM c) (Work.FTS.Top.timeCLM c)
    hΦ huniq h
  simpa only [Work.FTS.Top.timeScale_uncurry] using hmain

end Work.FTS.Top.Rescale
end
-- ===== merged: Submission.Work.FTS_EllLimOK.VopTransfer.exists_LopIter_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.VopTransfer

/-- A function which is `C^k` for every `k : ℕ` (finite order smoothness — note that `⊤` in
this Mathlib means *analytic*, which is not assumed) has `C^k` iterates of the angular
operator `Lop u = sin(2θ) · u'`.

Proved by induction on the number of iterates: the derivative of a `C^{k+1}` function is
`C^k` (`ContDiff.deriv'`), and `sin(2·)` is smooth. -/
private lemma contDiff_lopIter (u : ℝ → ℝ) (hu : ∀ k : ℕ, ContDiff ℝ k u) :
    ∀ r k : ℕ, ContDiff ℝ k (Work.Spaces.Lop^[r] u) := by
  intro r
  induction r with
  | zero => intro k; simpa using hu k
  | succ r ih =>
    intro k
    rw [Function.iterate_succ_apply']
    have h2 : ContDiff ℝ k (deriv (Work.Spaces.Lop^[r] u)) :=
      ContDiff.deriv' (ih (k + 1))
    exact (by fun_prop : ContDiff ℝ k (fun θ : ℝ => Real.sin (2 * θ))).mul h2

theorem exists_LopIter_bound (u : ℝ → ℝ) (hu : ∀ k : ℕ, ContDiff ℝ k u) (A : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ≤ A, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.EllipticEst.LopIter r u θ| ≤ B := by
  have hsmooth : ∀ r k : ℕ, ContDiff ℝ k (Work.Spaces.Lop^[r] u) := contDiff_lopIter u hu
  have hcont : ∀ r : ℕ, Continuous (Work.Spaces.Lop^[r] u) := fun r => (hsmooth r 0).continuous
  -- every iterate is continuous, hence bounded on the compact interval `Iθ = [0, π/2]`
  choose C hC using fun r : ℕ =>
    IsCompact.exists_bound_of_continuousOn isCompact_Icc (hcont r).continuousOn
  refine ⟨∑ r ∈ Finset.range (A + 1), max 0 (C r), ?_, ?_⟩
  · exact Finset.sum_nonneg fun r _ => le_max_left _ _
  · intro r hr θ hθ
    show |(Work.Spaces.Lop^[r] u) θ| ≤ _
    have hmem : r ∈ Finset.range (A + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hr)
    have h1 : |(Work.Spaces.Lop^[r] u) θ| ≤ max 0 (C r) := by
      have h := hC r θ hθ
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_max_right _ _)
    exact le_trans h1 (Finset.single_le_sum (fun i _ => le_max_left (0 : ℝ) (C i)) hmem)

end Work.FTS_EllLimOK.VopTransfer
end
-- ===== merged: Submission.Work.FTS_FinalLeaves.SolFire.N0_congr_of_agreeOnQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_FinalLeaves.SolFire

set_option autoImplicit false

/-!
# `N₀` only sees the values on the open quadrant

`Work.Construction.N0 α F g` is built from the angular integral `L₁₂ g`, the pointwise
values of `g`, and the pointwise derivatives `∂_θF`, `z∂_zF`, `z∂_zg` of the two profiles.
The first only sees `g` almost everywhere on the angular interval `[0, π/2]` (the two
endpoints are null), and the derivatives only see the values of a function on an open
neighbourhood of the point at which they are evaluated — which, for a point of the open
quadrant `z > 0`, `0 < θ < π/2`, is contained in the open quadrant.

Hence `N₀` is a *local* expression: two pairs `(F, g)` and `(F', g')` that agree on the
open quadrant give the same value of `N₀` at every point of the open quadrant.
-/

/-- On the angular interval `[0, π/2]`, the open interval `(0, π/2)` has full measure:
the two excluded endpoints form a null set. -/
private lemma ae_mem_Ioo_of_mem_Icc :
    ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) →
      0 < θ ∧ θ < Real.pi / 2 := by
  have hne : (volume : Measure ℝ) ({0, Real.pi / 2} : Set ℝ) = 0 :=
    ((Set.finite_singleton (Real.pi / 2)).insert 0).measure_zero volume
  have hset : {θ : ℝ | ¬ (θ ∉ ({0, Real.pi / 2} : Set ℝ))} = ({0, Real.pi / 2} : Set ℝ) := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, not_not]
  have hmem : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({0, Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff, hset]
    exact hne
  filter_upwards [hmem] with θ hθ hθI
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hθ
  simp only [Set.mem_Icc] at hθI
  exact ⟨lt_of_le_of_ne hθI.1 (fun hh => hθ.1 hh.symm),
    lt_of_le_of_ne hθI.2 hθ.2⟩

/-- The `L₁₂`-density at a point `s > 0` only sees the profile almost everywhere on `Iθ`. -/
private lemma L12dens_congr {a b : ℝ → ℝ → ℝ} {s : ℝ}
    (h : ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → a s θ = b s θ) :
    Work.FM.L12dens Work.Spaces.K a s = Work.FM.L12dens Work.Spaces.K b s := by
  simp only [Work.FM.L12dens]
  refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
  filter_upwards [ae_mem_Ioo_of_mem_Icc] with θ hθ hθI
  obtain ⟨h1, h2⟩ := hθ hθI
  rw [h θ h1 h2]

/-- `L₁₂` at a positive radius only sees the values of the profile on the open quadrant. -/
private lemma L12_congr {a b : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → a z' θ' = b z' θ') :
    Work.Construction.L12 a z = Work.Construction.L12 b z := by
  simp only [Work.Construction.L12, Work.FM.L12]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro s hs
  have hs0 : 0 < s := lt_trans hz hs
  exact L12dens_congr fun θ h1 h2 => h s θ hs0 h1 h2

/-- `∂_z` only sees the values of the profile on the open quadrant. -/
private lemma pz_congr {a b : ℝ → ℝ → ℝ}
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → a z' θ' = b z' θ') :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pz a z θ = Work.Spaces.pz b z θ := by
  intro z θ hz h1 h2
  have heq : (fun z' : ℝ => a z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => b z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h z' θ hz' h1 h2
  simp only [Work.Spaces.pz]
  exact heq.deriv_eq

/-- `∂_θ` only sees the values of the profile on the open quadrant. -/
private lemma pth_congr {a b : ℝ → ℝ → ℝ}
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → a z' θ' = b z' θ') :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth a z θ = Work.Spaces.pth b z θ := by
  intro z θ hz h1 h2
  have heq : (fun θ' : ℝ => a z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => b z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨h1, h2⟩)]
      with θ' hθ'
    exact h z θ' hz hθ'.1 hθ'.2
  simp only [Work.Spaces.pth]
  exact heq.deriv_eq

theorem N0_congr_of_agreeOnQ {α : ℝ} {F F' g g' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hF : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → F z' θ' = F' z' θ')
    (hg : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → g z' θ' = g' z' θ') :
    Work.Construction.N0 α F g z θ = Work.Construction.N0 α F' g' z θ := by
  have hL12 : Work.Construction.L12 g z = Work.Construction.L12 g' z := L12_congr hz hg
  have hgpt : g z θ = g' z θ := hg z θ hz hθ hθ2
  have hpthF : Work.Spaces.pth F z θ = Work.Spaces.pth F' z θ := pth_congr hF z θ hz hθ hθ2
  have hpzF : Work.Spaces.pz F z θ = Work.Spaces.pz F' z θ := pz_congr hF z θ hz hθ hθ2
  have hpzg : Work.Spaces.pz g z θ = Work.Spaces.pz g' z θ := pz_congr hg z θ hz hθ hθ2
  have hDzF : Work.Spaces.Dz F z θ = Work.Spaces.Dz F' z θ := by
    simp only [Work.Spaces.Dz, hpzF]
  have hDzg : Work.Spaces.Dz g z θ = Work.Spaces.Dz g' z θ := by
    simp only [Work.Spaces.Dz, hpzg]
  simp only [Work.Construction.N0]
  rw [hL12, hgpt, hpthF, hDzF, hDzg]

end Work.FTS_FinalLeaves.SolFire
end
-- ===== merged: Submission.Work.FTS_FinalLeaves.SolFire.N_congr_of_agreeOnQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `N` is local on the open quadrant

The nonlinear term `N` of the modulation chapter (`Work.Construction.N`, the paper's
`\eqref{N}`) is built from three kinds of ingredients:

* pointwise evaluations of `F` and of `Φ̃ = Φ - (1/(4α)) sin(2θ) L₁₂(F)` at `(z,θ)`
  (`Rop`, `Uop`, `Vop`, and the two angular-moment terms),
* the *first* partial derivatives `∂_z`, `∂_θ` of `F` and of `Φ̃` (`pz`, `pth`; the
  operators `Dz`, `Dth` are pointwise multiples of these),
* the angular moment `(F,K)_{L²_θ}(z) = ∫_0^{π/2} F(z,θ) K(θ) dθ`.

All of these depend on `F`, `Φ` only through their values on the open quadrant
`Qd = (0,∞) × (0,π/2)` — the derivatives because `deriv` is local and `Qd` is open, and
the two integral quantities (`L₁₂` and `(F,K)`) because the complement of `Qd` inside the
domain has measure zero (`Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ`).  This module
records that fact: two profiles that agree on the open quadrant give the same `N`.

The statements of the helper lemmas are phrased with the predicate `AgreeQ` ("agree
pointwise on the open quadrant"), which is exactly the hypothesis of the target theorem.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_FinalLeaves.SolFire

/-- `AgreeQ f f'`: the profiles `f` and `f'` agree at every point of the open quadrant
`(0,∞) × (0,π/2)`.  This is the hypothesis of `N_congr_of_agreeOnQ`; the operators of the
modulation chapter only see the values of a profile on that set. -/
def AgreeQ (f f' : ℝ → ℝ → ℝ) : Prop :=
  ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = f' z θ

theorem AgreeQ.symm {f f' : ℝ → ℝ → ℝ} (h : AgreeQ f f') : AgreeQ f' f :=
  fun z θ hz hθ hθ2 => (h z θ hz hθ hθ2).symm

/-- The open quadrant is open, so `deriv` sees only the values of a profile on it. -/
theorem isOpen_Qd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo

theorem mem_Qd {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ, hθ2⟩

/-! ## Locality of the first partial derivatives -/

/-- Profiles agreeing on the open quadrant have the same `z`-slice derivative at every
point of the quadrant. -/
lemma pz_agreeQ {f f' : ℝ → ℝ → ℝ} (h : AgreeQ f f') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.pz f z θ = Work.Spaces.pz f' z θ :=
  Work.Spaces.pz_congr_of_isOpen isOpen_Qd
    (fun y hy => h y.1 y.2 hy.1 hy.2.1 hy.2.2) (mem_Qd hz hθ hθ2)

/-- Profiles agreeing on the open quadrant have the same `θ`-slice derivative at every
point of the quadrant. -/
lemma pth_agreeQ {f f' : ℝ → ℝ → ℝ} (h : AgreeQ f f') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.pth f z θ = Work.Spaces.pth f' z θ :=
  Work.Spaces.pth_congr_of_isOpen isOpen_Qd
    (fun y hy => h y.1 y.2 hy.1 hy.2.1 hy.2.2) (mem_Qd hz hθ hθ2)

/-- `D_z = z ∂_z` is local on the open quadrant. -/
lemma Dz_agreeQ {f f' : ℝ → ℝ → ℝ} (h : AgreeQ f f') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ := by
  simp only [Work.Spaces.Dz, pz_agreeQ h hz hθ hθ2]


/-! ## Locality of `Uop`, `Vop`, `Rop` -/

/-- `Uop α Ψ = -3Ψ - α z ∂_zΨ` is local on the open quadrant. -/
lemma Uop_agreeQ {α : ℝ} {Ψ Ψ' : ℝ → ℝ → ℝ} (h : AgreeQ Ψ Ψ') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Construction.Uop α Ψ z θ = Work.Construction.Uop α Ψ' z θ := by
  simp only [Work.Construction.Uop, h z θ hz hθ hθ2, pz_agreeQ h hz hθ hθ2]

/-- `Vop Ψ = ∂_θΨ - tan θ · Ψ` is local on the open quadrant. -/
lemma Vop_agreeQ {Ψ Ψ' : ℝ → ℝ → ℝ} (h : AgreeQ Ψ Ψ') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Construction.Vop Ψ z θ = Work.Construction.Vop Ψ' z θ := by
  simp only [Work.Construction.Vop, h z θ hz hθ hθ2, pth_agreeQ h hz hθ hθ2]

/-- `ℛ(Ψ) = (2 sin θ Ψ + α sin θ z ∂_zΨ + cos θ ∂_θΨ)/cos θ` is local on the open
quadrant. -/
lemma Rop_agreeQ {α : ℝ} {Ψ Ψ' : ℝ → ℝ → ℝ} (h : AgreeQ Ψ Ψ') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Construction.Rop α Ψ z θ = Work.Construction.Rop α Ψ' z θ := by
  simp only [Work.Construction.Rop, h z θ hz hθ hθ2, pz_agreeQ h hz hθ hθ2,
    pth_agreeQ h hz hθ hθ2]

/-! ## Locality of `L₁₂`, `Θ`, `Φ̃` and of the angular moment `(F,K)` -/

/-- `L₁₂` only sees the values of a profile on the open quadrant
(`Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ`, transported to `Construction.L12`). -/
lemma L12_agreeQ {f f' : ℝ → ℝ → ℝ} (h : AgreeQ f f') {z : ℝ} (hz : 0 < z) :
    Work.Construction.L12 f z = Work.Construction.L12 f' z :=
  Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ (a := f) (b := f') (z := z)
    (le_of_lt hz) h

/-- `Θ = (1/(4α)) sin(2θ) L₁₂(F)` is local on the open quadrant. -/
lemma Theta_agreeQ {α : ℝ} {F F' : ℝ → ℝ → ℝ} (hF : AgreeQ F F') {z θ : ℝ}
    (hz : 0 < z) (_hθ : 0 < θ) (_hθ2 : θ < Real.pi / 2) :
    Work.Construction.Theta α F z θ = Work.Construction.Theta α F' z θ := by
  simp only [Work.Construction.Theta, L12_agreeQ hF hz]

/-- `Φ̃ = Φ - Θ` is local on the open quadrant. -/
lemma PhiTil_agreeQ {α : ℝ} {F F' Φ Φ' : ℝ → ℝ → ℝ}
    (hF : AgreeQ F F') (hΦ : AgreeQ Φ Φ') :
    AgreeQ (Work.Construction.PhiTil α F Φ) (Work.Construction.PhiTil α F' Φ') :=
  fun z θ hz hθ hθ2 => by
    simp only [Work.Construction.PhiTil, Theta_agreeQ hF hz hθ hθ2, hΦ z θ hz hθ hθ2]

/-- The angular moment `(F,K)_{L²_θ}(z) = ∫_0^{π/2} F(z,θ) K(θ) dθ` is local on the open
quadrant: at a fixed `z > 0` the two profiles agree for every `θ ∈ (0,π/2)`, i.e. almost
everywhere on `Iθ = [0,π/2]`. -/
lemma FK_agreeQ {F F' : ℝ → ℝ → ℝ} (hF : AgreeQ F F') {z : ℝ} (hz : 0 < z) :
    Work.Construction.FK F z = Work.Construction.FK F' z := by
  simp only [Work.Construction.FK]
  refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
  filter_upwards [Work.FTS.GalFields.RHS.ae_mem_Ioo_of_mem_Iθ_gal] with θ hθ hθI
  obtain ⟨h1, h2⟩ := hθ hθI
  rw [hF z θ hz h1 h2]

/-! ## The target -/

/-- **`N` is local on the open quadrant**: profiles `(F, Φ)` and `(F', Φ')` that agree
pointwise on `(0,∞) × (0,π/2)` give the same `N` at every point of that quadrant. -/
theorem N_congr_of_agreeOnQ {α : ℝ} {F F' Φ Φ' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hF : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → F z' θ' = F' z' θ')
    (hΦ : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → Φ z' θ' = Φ' z' θ') :
    Work.Construction.N α F Φ z θ = Work.Construction.N α F' Φ' z θ := by
  have hFT : AgreeQ F F' := hF
  have hΦT : AgreeQ Φ Φ' := hΦ
  have hPT : AgreeQ (Work.Construction.PhiTil α F Φ)
      (Work.Construction.PhiTil α F' Φ') := PhiTil_agreeQ hFT hΦT
  have hRop : Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α F' Φ') z θ :=
    Rop_agreeQ (α := α) hPT hz hθ hθ2
  have hUop : Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α F' Φ') z θ :=
    Uop_agreeQ (α := α) hPT hz hθ hθ2
  have hVop : Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α F' Φ') z θ :=
    Vop_agreeQ hPT hz hθ hθ2
  have hFz := hF z θ hz hθ hθ2
  have hpthF := pth_agreeQ hFT hz hθ hθ2
  have hDzF := Dz_agreeQ hFT hz hθ hθ2
  have hFK := FK_agreeQ hFT hz
  simp only [Work.Construction.N, hRop, hUop, hVop, hFz, hpthF, hDzF, hFK]

end Work.FTS_FinalLeaves.SolFire
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.SysAux.PieceCalc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.SysAux.PieceCalc` — calculus for separable data on the open quadrant

Every function occurring in `explicit_piece_bounds` is an analytic function of `(z,θ)` on the
open quadrant `Q0 = (0,∞) × (0,π/2)` that is a finite sum of products `A(z)·B(θ)`.  This file
provides the two calculus tools needed to exploit that structure:

* **congruence** of `D_z^j D_θ^i` under agreement on an open set
  (`DzIter_congr_of_isOpen`, `DthIter_congr_of_isOpen`, `mixed_congr_of_isOpen`) — used to
  replace the explicit expression of a piece by its simplified closed form;
* **additivity** of `D_z^j D_θ^i` over a sum of two analytic functions
  (`DthIter_add_eqOn`, `DzIter_add_eqOn`, `mixed_add`) — used to split a finite sum of
  products into its summands.

Everything rests on `[propext, Classical.choice, Quot.sound]` only (the imports
`Spaces.CurrySmooth` and `Spaces.Defs` are `sorry`-free).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.SysAux

set_option autoImplicit false

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
def Q0 : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

theorem isOpen_Q0 : IsOpen Q0 := isOpen_Ioi.prod isOpen_Ioo

/-! ## §1  `D_θ` and `D_z` lower the order of differentiability -/

/-- `D_θ` of a function analytic on an open set is analytic there. -/
theorem contDiffOn_uncurry_Dth_of_contDiffOn {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {G : ℝ → ℝ → ℝ} (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dth G)
      = (fun p : ℝ × ℝ => Real.sin (2 * p.2)) * Function.uncurry (Work.Spaces.pth G) := by
    funext p
    obtain ⟨z, θ⟩ := p
    rfl
  rw [hfun]
  exact ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn).mul
    (Work.Spaces.contDiffOn_uncurry_pth hV h)

/-- `D_z` of a function analytic on an open set is analytic there. -/
theorem contDiffOn_uncurry_Dz_of_contDiffOn {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {G : ℝ → ℝ → ℝ} (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dz G)
      = (fun p : ℝ × ℝ => p.1) * Function.uncurry (Work.Spaces.pz G) := by
    funext p
    obtain ⟨z, θ⟩ := p
    rfl
  rw [hfun]
  exact (contDiffOn_fst : ContDiffOn ℝ ⊤ (Prod.fst : ℝ × ℝ → ℝ) V).mul
    (Work.Spaces.contDiffOn_uncurry_pz hV h)

/-- `D_θ^i` of a function analytic on an open set is analytic there. -/
theorem contDiffOn_uncurry_DthIter_of_contDiffOn {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {G : ℝ → ℝ → ℝ} (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) (i : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DthIter i G)) V := by
  induction i with
  | zero => exact h
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ]
      exact contDiffOn_uncurry_Dth_of_contDiffOn hV ih

/-- `D_z^j` of a function analytic on an open set is analytic there. -/
theorem contDiffOn_uncurry_DzIter_of_contDiffOn {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {G : ℝ → ℝ → ℝ} (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) (j : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter j G)) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ]
      exact contDiffOn_uncurry_Dz_of_contDiffOn hV ih

/-! ## §2  Congruence of the iterated operators on an open set -/

/-- `D_θ` respects agreement on an open set. -/
theorem Dth_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) {z θ : ℝ}
    (hz : (z, θ) ∈ V) : Work.Spaces.Dth f z θ = Work.Spaces.Dth g z θ := by
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V :=
    (Continuous.prodMk_right z).continuousAt.eventually (hV.mem_nhds hz)
  have hev : (fun θ' => f z θ') =ᶠ[𝓝 θ] (fun θ' => g z θ') :=
    hnb.mono (fun θ' hθ' => h hθ')
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [hev.deriv_eq]

/-- `D_z` respects agreement on an open set. -/
theorem Dz_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) {z θ : ℝ}
    (hz : (z, θ) ∈ V) : Work.Spaces.Dz f z θ = Work.Spaces.Dz g z θ := by
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
    (Continuous.prodMk_left θ).continuousAt.eventually (hV.mem_nhds hz)
  have hev : (fun z' => f z' θ) =ᶠ[𝓝 z] (fun z' => g z' θ) :=
    hnb.mono (fun z' hz' => h hz')
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [hev.deriv_eq]

/-- `D_θ^i` respects agreement on an open set. -/
theorem DthIter_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (i : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ V → Work.Spaces.DthIter i f z θ = Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => intro z θ hz; exact h hz
  | succ i ih =>
      intro z θ hz
      exact Dth_congr_of_isOpen hV (fun p hp => ih p.1 p.2 hp) hz

/-- `D_z^j` respects agreement on an open set. -/
theorem DzIter_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (j : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ V → Work.Spaces.DzIter j f z θ = Work.Spaces.DzIter j g z θ := by
  induction j with
  | zero => intro z θ hz; exact h hz
  | succ j ih =>
      intro z θ hz
      exact Dz_congr_of_isOpen hV (fun p hp => ih p.1 p.2 hp) hz

/-- **`mixed` respects agreement on an open set.** -/
theorem mixed_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (j i : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ V → Work.Spaces.mixed j i f z θ = Work.Spaces.mixed j i g z θ := by
  have h1 := DthIter_congr_of_isOpen hV h i
  intro z θ hz
  simp only [Work.Spaces.mixed]
  exact DzIter_congr_of_isOpen hV (fun p hp => h1 p.1 p.2 hp) j z θ hz

/-! ## §3  Additivity of the iterated operators over a sum -/

/-- `D_θ` of a sum of two analytic functions. -/
theorem Dth_add_pt {V : Set (ℝ × ℝ)} (hV : IsOpen V) {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ ⊤ (Function.uncurry u) V) (hv : ContDiffOn ℝ ⊤ (Function.uncurry v) V)
    {z θ : ℝ} (h : (z, θ) ∈ V) :
    Work.Spaces.Dth (u + v) z θ = Work.Spaces.Dth u z θ + Work.Spaces.Dth v z θ := by
  have hdu : DifferentiableAt ℝ (fun θ' : ℝ => u z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hu.differentiableOn (n := ⊤) (by simp)).differentiableAt (hV.mem_nhds h))
  have hdv : DifferentiableAt ℝ (fun θ' : ℝ => v z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hv.differentiableOn (n := ⊤) (by simp)).differentiableAt (hV.mem_nhds h))
  show Real.sin (2 * θ) * deriv (fun θ' => (u + v) z θ') θ
      = Real.sin (2 * θ) * deriv (fun θ' => u z θ') θ
        + Real.sin (2 * θ) * deriv (fun θ' => v z θ') θ
  rw [show (fun θ' : ℝ => (u + v) z θ') = (fun θ' : ℝ => u z θ') + (fun θ' => v z θ')
      from by funext θ'; rfl, deriv_add hdu hdv]
  ring

/-- `D_z` of a sum of two analytic functions. -/
theorem Dz_add_pt {V : Set (ℝ × ℝ)} (hV : IsOpen V) {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ ⊤ (Function.uncurry u) V) (hv : ContDiffOn ℝ ⊤ (Function.uncurry v) V)
    {z θ : ℝ} (h : (z, θ) ∈ V) :
    Work.Spaces.Dz (u + v) z θ = Work.Spaces.Dz u z θ + Work.Spaces.Dz v z θ := by
  have hdu : DifferentiableAt ℝ (fun z' : ℝ => u z' θ) z :=
    Work.Spaces.differentiableAt_curry_left
      ((hu.differentiableOn (n := ⊤) (by simp)).differentiableAt (hV.mem_nhds h))
  have hdv : DifferentiableAt ℝ (fun z' : ℝ => v z' θ) z :=
    Work.Spaces.differentiableAt_curry_left
      ((hv.differentiableOn (n := ⊤) (by simp)).differentiableAt (hV.mem_nhds h))
  show z * deriv (fun z' => (u + v) z' θ) z
      = z * deriv (fun z' => u z' θ) z + z * deriv (fun z' => v z' θ) z
  rw [show (fun z' : ℝ => (u + v) z' θ) = (fun z' : ℝ => u z' θ) + (fun z' => v z' θ)
      from by funext z'; rfl, deriv_add hdu hdv]
  ring

/-- `D_θ^i` of a sum of two analytic functions. -/
theorem DthIter_add_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (hg : ContDiffOn ℝ ⊤ (Function.uncurry g) V)
    (i : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ V →
      Work.Spaces.DthIter i (f + g) z θ
        = Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => intro z θ hz; rfl
  | succ i ih =>
      intro z θ hz
      have hf' := contDiffOn_uncurry_DthIter_of_contDiffOn hV hf i
      have hg' := contDiffOn_uncurry_DthIter_of_contDiffOn hV hg i
      have hEq : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (f + g)))
          (Function.uncurry (Work.Spaces.DthIter i f + Work.Spaces.DthIter i g)) V := by
        intro p hp
        obtain ⟨z', θ'⟩ := p
        exact ih z' θ' hp
      show Work.Spaces.Dth (Work.Spaces.DthIter i (f + g)) z θ
          = Work.Spaces.Dth (Work.Spaces.DthIter i f) z θ
            + Work.Spaces.Dth (Work.Spaces.DthIter i g) z θ
      rw [Dth_congr_of_isOpen hV hEq hz]
      exact Dth_add_pt hV hf' hg' hz

/-- `D_z^j` of a sum of two analytic functions. -/
theorem DzIter_add_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (hg : ContDiffOn ℝ ⊤ (Function.uncurry g) V)
    (j : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ V →
      Work.Spaces.DzIter j (f + g) z θ
        = Work.Spaces.DzIter j f z θ + Work.Spaces.DzIter j g z θ := by
  induction j with
  | zero => intro z θ hz; rfl
  | succ j ih =>
      intro z θ hz
      have hf' := contDiffOn_uncurry_DzIter_of_contDiffOn hV hf j
      have hg' := contDiffOn_uncurry_DzIter_of_contDiffOn hV hg j
      have hEq : Set.EqOn (Function.uncurry (Work.Spaces.DzIter j (f + g)))
          (Function.uncurry (Work.Spaces.DzIter j f + Work.Spaces.DzIter j g)) V := by
        intro p hp
        obtain ⟨z', θ'⟩ := p
        exact ih z' θ' hp
      show Work.Spaces.Dz (Work.Spaces.DzIter j (f + g)) z θ
          = Work.Spaces.Dz (Work.Spaces.DzIter j f) z θ
            + Work.Spaces.Dz (Work.Spaces.DzIter j g) z θ
      rw [Dz_congr_of_isOpen hV hEq hz]
      exact Dz_add_pt hV hf' hg' hz

/-- **`mixed` is additive over a sum of two analytic functions.** -/
theorem mixed_add {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (hg : ContDiffOn ℝ ⊤ (Function.uncurry g) V)
    (j i : ℕ) {z θ : ℝ} (h : (z, θ) ∈ V) :
    Work.Spaces.mixed j i (f + g) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ := by
  have hEq : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (f + g)))
      (Function.uncurry (Work.Spaces.DthIter i f + Work.Spaces.DthIter i g)) V := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    exact DthIter_add_eqOn hV hf hg i z' θ' hp
  have h1 := DzIter_congr_of_isOpen hV hEq j z θ h
  have h2 := DzIter_add_eqOn hV (contDiffOn_uncurry_DthIter_of_contDiffOn hV hf i)
    (contDiffOn_uncurry_DthIter_of_contDiffOn hV hg i) j z θ h
  simp only [Work.Spaces.mixed]
  rw [h1, h2]

/-! ## §4  Analyticity of a separable product -/

/-- A product `A(z)·B(θ)` of an analytic function of `z` on `(0,∞)` with an analytic
function of `θ` on `(0,π/2)` is analytic on the open quadrant. -/
theorem contDiffOn_uncurry_sep {n : WithTop ℕ∞} {A B : ℝ → ℝ}
    (hA : ContDiffOn ℝ n A (Set.Ioi 0)) (hB : ContDiffOn ℝ n B (Set.Ioo 0 (π / 2))) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => A z * B θ)) Q0 := by
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => A p.1) Q0 := by
    have hc := hA.comp (contDiffOn_fst (s := Q0)) (fun p hp => hp.1)
    have hfun : (A ∘ Prod.fst) = fun p : ℝ × ℝ => A p.1 := by
      funext p
      obtain ⟨z, θ⟩ := p
      rfl
    rwa [hfun] at hc
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => B p.2) Q0 := by
    have hc := hB.comp (contDiffOn_snd (s := Q0)) (fun p hp => hp.2)
    have hfun : (B ∘ Prod.snd) = fun p : ℝ × ℝ => B p.2 := by
      funext p
      obtain ⟨z, θ⟩ := p
      rfl
    rwa [hfun] at hc
  have h3 : ContDiffOn ℝ n (fun p : ℝ × ℝ => A p.1 * B p.2) Q0 := h1.mul h2
  have hfun : Function.uncurry (fun z θ => A z * B θ) = fun p : ℝ × ℝ => A p.1 * B p.2 := by
    funext p
    obtain ⟨z, θ⟩ := p
    rfl
  rwa [hfun]

end Work.FTS_RegExport.RXT.SysAux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.SysAux.piece_t_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS_RegExport.RXT.SysAux

set_option autoImplicit false

/-! ### Derivative facts about the three angular profiles -/


/-- `d/dθ (sin θ)² = sin 2θ`. -/
theorem hasDerivAt_sin_sq (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Real.sin θ ^ 2) (Real.sin (2 * θ)) θ := by
  have h := (Real.hasDerivAt_sin θ).pow 2
  rw [Real.sin_two_mul]
  convert h using 1
  rw [show (2 : ℕ) - 1 = 1 by norm_num, pow_one]
  ring

theorem deriv_sin_sq (θ : ℝ) :
    deriv (fun θ : ℝ => Real.sin θ ^ 2) θ = Real.sin (2 * θ) :=
  (hasDerivAt_sin_sq θ).deriv


/-- `d/dθ (sin 2θ)² = 4 sin 2θ cos 2θ`. -/
theorem hasDerivAt_sin_two_sq (θ : ℝ) :
    HasDerivAt (fun η : ℝ => Real.sin (2 * η) ^ 2)
      (4 * Real.sin (2 * θ) * Real.cos (2 * θ)) θ := by
  have h : HasDerivAt (fun η : ℝ => Real.sin (2 * η)) (2 * Real.cos (2 * θ)) θ := by
    have h0 : HasDerivAt (fun η : ℝ => Real.sin (2 * η))
        (Real.cos (2 * θ) * (2 * 1)) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
    have h1 : Real.cos (2 * θ) * (2 * 1) = 2 * Real.cos (2 * θ) := by ring
    rwa [h1] at h0
  have h2 : HasDerivAt (fun η : ℝ => Real.sin (2 * η) ^ 2)
      (2 * Real.sin (2 * θ) ^ (2 - 1) * (2 * Real.cos (2 * θ))) θ := h.pow 2
  have h3 : 2 * Real.sin (2 * θ) ^ (2 - 1) * (2 * Real.cos (2 * θ))
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
    rw [show (2 : ℕ) - 1 = 1 by norm_num, pow_one]
    ring
  rwa [h3] at h2

theorem deriv_sin_two_sq (θ : ℝ) :
    deriv (fun η : ℝ => Real.sin (2 * η) ^ 2) θ
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) :=
  (hasDerivAt_sin_two_sq θ).deriv


/-- `d/dθ (cos 2θ − sin²θ) = -3 sin 2θ`. -/
theorem hasDerivAt_c2m (θ : ℝ) :
    HasDerivAt Work.Construction.c2m (-3 * Real.sin (2 * θ)) θ := by
  have hc : HasDerivAt (fun η : ℝ => Real.cos (2 * η))
      ((-Real.sin (2 * θ)) * (2 * 1)) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  have hs : HasDerivAt (fun η : ℝ => Real.sin η ^ 2) (Real.sin (2 * θ)) θ :=
    hasDerivAt_sin_sq θ
  have h : HasDerivAt Work.Construction.c2m
      ((-Real.sin (2 * θ)) * (2 * 1) - Real.sin (2 * θ)) θ := hc.sub hs
  have h2 : (-Real.sin (2 * θ)) * (2 * 1) - Real.sin (2 * θ)
      = -3 * Real.sin (2 * θ) := by ring
  rwa [h2] at h

theorem deriv_c2m (θ : ℝ) :
    deriv Work.Construction.c2m θ = -3 * Real.sin (2 * θ) :=
  (hasDerivAt_c2m θ).deriv


/-- `d/dθ (-3 (sin 2θ)²) = -12 sin 2θ cos 2θ`. -/
theorem deriv_neg3_sin_two_sq (θ : ℝ) :
    deriv (fun x : ℝ => -3 * Real.sin (2 * x) ^ 2) θ
      = -12 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
  rw [deriv_const_mul_field, deriv_sin_two_sq]
  ring


/-! ### The iterates `TIter i` evaluated on the three profiles -/



theorem TIter_one_const (θ : ℝ) : TIter 1 (fun _ : ℝ => (1 : ℝ)) θ = 0 := by
  change Real.sin (2 * θ) * deriv (fun _ : ℝ => (1 : ℝ)) θ = 0
  simp [deriv_const]

theorem TIter_one_c2m (θ : ℝ) :
    TIter 1 Work.Construction.c2m θ = -3 * Real.sin (2 * θ) ^ 2 := by
  change Real.sin (2 * θ) * deriv Work.Construction.c2m θ = -3 * Real.sin (2 * θ) ^ 2
  rw [deriv_c2m]
  ring

theorem TIter_one_sinsq (θ : ℝ) :
    TIter 1 (fun θ : ℝ => Real.sin θ ^ 2) θ = Real.sin (2 * θ) ^ 2 := by
  change Real.sin (2 * θ) * deriv (fun y : ℝ => Real.sin y ^ 2) θ
    = Real.sin (2 * θ) ^ 2
  rw [deriv_sin_sq]
  ring

theorem TIter_two_const (θ : ℝ) : TIter 2 (fun _ : ℝ => (1 : ℝ)) θ = 0 := by
  have h1 : TIter 1 (fun _ : ℝ => (1 : ℝ)) = fun _ : ℝ => (0 : ℝ) := by
    funext x
    change Real.sin (2 * x) * deriv (fun _ : ℝ => (1 : ℝ)) x = 0
    simp [deriv_const]
  change Real.sin (2 * θ) * deriv (TIter 1 (fun _ : ℝ => (1 : ℝ))) θ = 0
  rw [h1]
  simp [deriv_const]

theorem TIter_two_c2m (θ : ℝ) :
    TIter 2 Work.Construction.c2m θ = -12 * Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ) := by
  have h1 : TIter 1 Work.Construction.c2m = fun x : ℝ => -3 * Real.sin (2 * x) ^ 2 := by
    funext x
    change Real.sin (2 * x) * deriv Work.Construction.c2m x = -3 * Real.sin (2 * x) ^ 2
    rw [deriv_c2m]
    ring
  change Real.sin (2 * θ) * deriv (TIter 1 Work.Construction.c2m) θ
    = -12 * Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ)
  rw [h1, deriv_neg3_sin_two_sq]
  ring

theorem TIter_two_sinsq (θ : ℝ) :
    TIter 2 (fun θ : ℝ => Real.sin θ ^ 2) θ
      = 4 * Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ) := by
  have h1 : TIter 1 (fun θ : ℝ => Real.sin θ ^ 2) = fun x : ℝ => Real.sin (2 * x) ^ 2 := by
    funext x
    change Real.sin (2 * x) * deriv (fun y : ℝ => Real.sin y ^ 2) x
      = Real.sin (2 * x) ^ 2
    rw [deriv_sin_sq]
    ring
  change Real.sin (2 * θ) * deriv (TIter 1 (fun θ : ℝ => Real.sin θ ^ 2)) θ
    = 4 * Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ)
  rw [h1, deriv_sin_two_sq]
  ring

/-! ### Bounds on the evaluated profiles -/

theorem abs_c2m_le_twelve (θ : ℝ) : |Work.Construction.c2m θ| ≤ 12 := by
  have hc1 : Real.cos (2 * θ) ≤ 1 := Real.cos_le_one (2 * θ)
  have hc0 : -1 ≤ Real.cos (2 * θ) := Real.neg_one_le_cos (2 * θ)
  have hs1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hs0 : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  rw [Work.Construction.c2m_eq, abs_le]
  constructor <;> linarith

theorem abs_sinsq_le_four (θ : ℝ) : |Real.sin θ ^ 2| ≤ 4 := by
  rw [abs_of_nonneg (sq_nonneg (Real.sin θ))]
  nlinarith [Real.sin_sq_le_one θ]

theorem abs_neg3_sin_two_sq_le (θ : ℝ) :
    |(-3 : ℝ) * Real.sin (2 * θ) ^ 2| ≤ 12 := by
  have hs1 : Real.sin (2 * θ) ^ 2 ≤ 1 := Real.sin_sq_le_one (2 * θ)
  have hs0 : 0 ≤ Real.sin (2 * θ) ^ 2 := sq_nonneg _
  rw [abs_le]
  constructor <;> linarith

theorem abs_neg12_sin_two_sq_mul_cos_le (θ : ℝ) :
    |(-12 : ℝ) * Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ)| ≤ 12 := by
  have hs1 : Real.sin (2 * θ) ^ 2 ≤ 1 := Real.sin_sq_le_one (2 * θ)
  have hs0 : 0 ≤ Real.sin (2 * θ) ^ 2 := sq_nonneg _
  have hc1 : Real.cos (2 * θ) ≤ 1 := Real.cos_le_one (2 * θ)
  have hc0 : -1 ≤ Real.cos (2 * θ) := Real.neg_one_le_cos (2 * θ)
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_four_sin_two_sq_mul_cos_le (θ : ℝ) :
    |4 * Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ)| ≤ 4 := by
  have hs1 : Real.sin (2 * θ) ^ 2 ≤ 1 := Real.sin_sq_le_one (2 * θ)
  have hs0 : 0 ≤ Real.sin (2 * θ) ^ 2 := sq_nonneg _
  have hc1 : Real.cos (2 * θ) ≤ 1 := Real.cos_le_one (2 * θ)
  have hc0 : -1 ≤ Real.cos (2 * θ) := Real.neg_one_le_cos (2 * θ)
  rw [abs_le]
  constructor <;> nlinarith

/-! ### The target -/

theorem piece_t_bounds : ∀ i : ℕ, i ≤ 2 → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
    (|TIter i (fun _ : ℝ => 1) θ| ≤ 1) ∧
    (|TIter i Work.Construction.c2m θ| ≤ 12) ∧
    (|TIter i (fun θ : ℝ => Real.sin θ ^ 2) θ| ≤ 4) := by
  intro i hi θ hθ hθ2
  interval_cases i
  · refine ⟨?_, ?_, ?_⟩
    · simp
    · simpa only [TIter_zero] using abs_c2m_le_twelve θ
    · simpa only [TIter_zero] using abs_sinsq_le_four θ
  · refine ⟨?_, ?_, ?_⟩
    · rw [TIter_one_const]; norm_num
    · rw [TIter_one_c2m]; exact abs_neg3_sin_two_sq_le θ
    · rw [TIter_one_sinsq]; exact abs_sinsq_le_four (2 * θ)
  · refine ⟨?_, ?_, ?_⟩
    · rw [TIter_two_const]; norm_num
    · rw [TIter_two_c2m]; exact abs_neg12_sin_two_sq_mul_cos_le θ
    · rw [TIter_two_sinsq]; exact abs_four_sin_two_sq_mul_cos_le θ

end Work.FTS_RegExport.RXT.SysAux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.SysAux.piece_z_bounds_ab =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `piece_z_bounds_ab` — the radial one-variable bounds for `A1` and `B1`

`ZIter j A = (z ∂_z)^j A` is the one-variable version of the radial operator `D_z`
(`Work.FTS_RegExport.RXT.SysAux.PieceDefs`).  Here we bound its first three iterates for the
two radial profiles of the forcing decomposition,

  `A₁(z) = 2z(1-z)/(1+z)³`  and  `B₁(z) = 2z/(1+z)²`,

by `30·z/(1+z)²` respectively `10·z/(1+z)²` for `z > 0`.  Everything is completely explicit:
the iterates are the rational functions

  `ZIter 0 A₁ = 2z(1-z)/(1+z)³`,  `ZIter 1 A₁ = 2z(1-4z+z²)/(1+z)⁴`,
  `ZIter 2 A₁ = 2z(1-11z+11z²-z³)/(1+z)⁵`,
  `ZIter 0 B₁ = 2z/(1+z)²`,  `ZIter 1 B₁ = 2z(1-z)/(1+z)³`,  `ZIter 2 B₁ = 2z(1-4z+z²)/(1+z)⁴`,

and the bounds follow from the elementary estimates `|1-z| ≤ 1+z`, `|1-4z+z²| ≤ 4(1+z)²`,
`|1-11z+11z²-z³| ≤ 11(1+z)³` for `z > 0`.
-/

open scoped Real Topology

namespace Work.FTS_RegExport.RXT.SysAux

set_option autoImplicit false

/-! ### The explicit derivatives -/

private lemma deriv_f (z : ℝ) (hz : 0 < z) :
    deriv (fun w : ℝ => 2 * w * (1 - w) / (1 + w) ^ 3) z
      = 2 * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4 := by
  have hden : (1 + z) ^ 3 ≠ 0 := by positivity
  have h : HasDerivAt (fun w : ℝ => 2 * w * (1 - w) / (1 + w) ^ 3)
      (2 * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4) z := by
    have h1 : HasDerivAt (fun w : ℝ => 1 + w) (1 : ℝ) z := (hasDerivAt_id' z).const_add 1
    have h2 : HasDerivAt (fun w : ℝ => (1 + w) ^ 3) (3 * (1 + z) ^ 2) z := by
      simpa using h1.fun_pow 3
    have ha : HasDerivAt (fun w : ℝ => 2 * w) (2 : ℝ) z := by
      simpa using (hasDerivAt_id' z).const_mul 2
    have hb : HasDerivAt (fun w : ℝ => 1 - w) (-1 : ℝ) z := by
      simpa using (hasDerivAt_id' z).const_sub 1
    have h3 : HasDerivAt (fun w : ℝ => 2 * w * (1 - w)) (2 - 4 * z) z := by
      have hm := ha.mul hb
      convert hm using 1
      ring
    have h4 := h3.div h2 hden
    convert h4 using 1
    field_simp
    ring
  rw [h.deriv]

private lemma deriv_g (z : ℝ) (hz : 0 < z) :
    deriv (fun w : ℝ => 2 * w / (1 + w) ^ 2) z = 2 * (1 - z) / (1 + z) ^ 3 := by
  have hden : (1 + z) ^ 2 ≠ 0 := by positivity
  have h : HasDerivAt (fun w : ℝ => 2 * w / (1 + w) ^ 2) (2 * (1 - z) / (1 + z) ^ 3) z := by
    have h1 : HasDerivAt (fun w : ℝ => 1 + w) (1 : ℝ) z := (hasDerivAt_id' z).const_add 1
    have h2 : HasDerivAt (fun w : ℝ => (1 + w) ^ 2) (2 * (1 + z)) z := by
      have hp := h1.fun_pow 2
      simpa using hp
    have ha : HasDerivAt (fun w : ℝ => 2 * w) (2 : ℝ) z := by
      simpa using (hasDerivAt_id' z).const_mul 2
    have h4 := ha.div h2 hden
    convert h4 using 1
    field_simp
    ring
  rw [h.deriv]

private lemma deriv_e1 (z : ℝ) (hz : 0 < z) :
    deriv (fun w : ℝ => 2 * w * (1 - 4 * w + w ^ 2) / (1 + w) ^ 4) z
      = 2 * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) / (1 + z) ^ 5 := by
  have hden : (1 + z) ^ 4 ≠ 0 := by positivity
  have h : HasDerivAt (fun w : ℝ => 2 * w * (1 - 4 * w + w ^ 2) / (1 + w) ^ 4)
      (2 * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) / (1 + z) ^ 5) z := by
    have h1 : HasDerivAt (fun w : ℝ => 1 + w) (1 : ℝ) z := (hasDerivAt_id' z).const_add 1
    have h2 : HasDerivAt (fun w : ℝ => (1 + w) ^ 4) (4 * (1 + z) ^ 3) z := by
      simpa using h1.fun_pow 4
    have ha : HasDerivAt (fun w : ℝ => 2 * w) (2 : ℝ) z := by
      simpa using (hasDerivAt_id' z).const_mul 2
    have hb1 : HasDerivAt (fun w : ℝ => 1 - 4 * w) (-4 : ℝ) z := by
      simpa using ((hasDerivAt_id' z).const_mul 4).const_sub 1
    have hb2 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 z
    have hb : HasDerivAt (fun w : ℝ => 1 - 4 * w + w ^ 2) (-4 + 2 * z) z := hb1.add hb2
    have h3 : HasDerivAt (fun w : ℝ => 2 * w * (1 - 4 * w + w ^ 2)) (2 - 16 * z + 6 * z ^ 2) z := by
      have hm := ha.mul hb
      convert hm using 1
      ring
    have h4 := h3.div h2 hden
    convert h4 using 1
    field_simp
    ring
  rw [h.deriv]

/-! ### The explicit iterates -/

private lemma ZIter_f_one (z : ℝ) (hz : 0 < z) :
    ZIter 1 (fun z : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3) z
      = 2 * z * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4 := by
  rw [ZIter_succ_apply, ZIter_zero]
  have hd : deriv (fun z : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3) z
      = 2 * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4 := deriv_f z hz
  rw [hd]
  ring

private lemma ZIter_f_two (z : ℝ) (hz : 0 < z) :
    ZIter 2 (fun z : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3) z
      = 2 * z * (1 - 11 * z + 11 * z ^ 2 - z ^ 3) / (1 + z) ^ 5 := by
  rw [ZIter_succ_apply]
  have hev : (fun w => ZIter 1 (fun w : ℝ => 2 * w * (1 - w) / (1 + w) ^ 3) w)
      =ᶠ[𝓝 z] fun w => 2 * w * (1 - 4 * w + w ^ 2) / (1 + w) ^ 4 := by
    filter_upwards [eventually_gt_nhds hz] with w hw
    exact ZIter_f_one w hw
  have hd : deriv (ZIter 1 (fun z : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3)) z
      = deriv (fun w : ℝ => 2 * w * (1 - 4 * w + w ^ 2) / (1 + w) ^ 4) z := hev.deriv_eq
  rw [hd, deriv_e1 z hz]
  ring

private lemma ZIter_g_one (z : ℝ) (hz : 0 < z) :
    ZIter 1 (fun z : ℝ => 2 * z / (1 + z) ^ 2) z = 2 * z * (1 - z) / (1 + z) ^ 3 := by
  rw [ZIter_succ_apply, ZIter_zero]
  have hd : deriv (fun z : ℝ => 2 * z / (1 + z) ^ 2) z = 2 * (1 - z) / (1 + z) ^ 3 :=
    deriv_g z hz
  rw [hd]
  ring

private lemma ZIter_g_two (z : ℝ) (hz : 0 < z) :
    ZIter 2 (fun z : ℝ => 2 * z / (1 + z) ^ 2) z
      = 2 * z * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4 := by
  rw [ZIter_succ_apply]
  have hev : (fun w => ZIter 1 (fun w : ℝ => 2 * w / (1 + w) ^ 2) w)
      =ᶠ[𝓝 z] fun w => 2 * w * (1 - w) / (1 + w) ^ 3 := by
    filter_upwards [eventually_gt_nhds hz] with w hw
    exact ZIter_g_one w hw
  have hd : deriv (ZIter 1 (fun z : ℝ => 2 * z / (1 + z) ^ 2)) z
      = deriv (fun w : ℝ => 2 * w * (1 - w) / (1 + w) ^ 3) z := hev.deriv_eq
  rw [hd, deriv_f z hz]
  ring

/-! ### The master estimate -/

/-- `|Nz| ≤ C·z·(1+z)^m` gives `|Nz/(1+z)^(m+2)| ≤ C·z/(1+z)²` for `z > 0`. -/
private lemma div_bound (z : ℝ) (hz : 0 < z) (m : ℕ) (C Nz : ℝ)
    (hN : |Nz| ≤ C * z * (1 + z) ^ m) :
    |Nz / (1 + z) ^ (m + 2)| ≤ C * (z / (1 + z) ^ 2) := by
  have hz1 : 0 < 1 + z := by linarith
  have hden : 0 < (1 + z) ^ (m + 2) := by positivity
  have hm0 : (1 + z) ^ m ≠ 0 := by positivity
  rw [abs_div, abs_of_pos hden]
  have hsplit : (1 + z) ^ (m + 2) = (1 + z) ^ m * (1 + z) ^ 2 := by rw [pow_add]
  calc |Nz| / (1 + z) ^ (m + 2)
      ≤ C * z * (1 + z) ^ m / ((1 + z) ^ m * (1 + z) ^ 2) := by
        rw [hsplit]
        exact div_le_div_of_nonneg_right hN (by positivity)
    _ = C * (z / (1 + z) ^ 2) := by field_simp

/-! ### Elementary absolute-value bounds -/

private lemma abs_one_sub (z : ℝ) (hz : 0 < z) : |1 - z| ≤ 1 + z := by
  rw [abs_le]
  constructor <;> linarith

private lemma abs_quad (z : ℝ) (hz : 0 < z) : |1 - 4 * z + z ^ 2| ≤ 4 * (1 + z) ^ 2 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg z]

private lemma abs_cubic (z : ℝ) (hz : 0 < z) :
    |1 - 11 * z + 11 * z ^ 2 - z ^ 3| ≤ 11 * (1 + z) ^ 3 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg z, mul_pos hz hz, sq_nonneg (z - 1)]

/-! ### The numerator estimates -/

private lemma hN_f_30 (z : ℝ) (hz : 0 < z) :
    |2 * z * (1 - z)| ≤ 30 * z * (1 + z) ^ 1 := by
  rw [pow_one]
  have hz2 : (0 : ℝ) ≤ 2 * z := by linarith
  calc |2 * z * (1 - z)| = 2 * z * |1 - z| := by rw [abs_mul, abs_of_nonneg hz2]
    _ ≤ 2 * z * (1 + z) := mul_le_mul_of_nonneg_left (abs_one_sub z hz) hz2
    _ ≤ 30 * z * (1 + z) := by nlinarith

private lemma hN_e1_30 (z : ℝ) (hz : 0 < z) :
    |2 * z * (1 - 4 * z + z ^ 2)| ≤ 30 * z * (1 + z) ^ 2 := by
  have hz2 : (0 : ℝ) ≤ 2 * z := by linarith
  calc |2 * z * (1 - 4 * z + z ^ 2)| = 2 * z * |1 - 4 * z + z ^ 2| := by
        rw [abs_mul, abs_of_nonneg hz2]
    _ ≤ 2 * z * (4 * (1 + z) ^ 2) := mul_le_mul_of_nonneg_left (abs_quad z hz) hz2
    _ ≤ 30 * z * (1 + z) ^ 2 := by nlinarith

private lemma hN_e2_30 (z : ℝ) (hz : 0 < z) :
    |2 * z * (1 - 11 * z + 11 * z ^ 2 - z ^ 3)| ≤ 30 * z * (1 + z) ^ 3 := by
  have hz2 : (0 : ℝ) ≤ 2 * z := by linarith
  have hz3 : (0 : ℝ) ≤ z * (1 + z) ^ 3 := by positivity
  calc |2 * z * (1 - 11 * z + 11 * z ^ 2 - z ^ 3)|
        = 2 * z * |1 - 11 * z + 11 * z ^ 2 - z ^ 3| := by rw [abs_mul, abs_of_nonneg hz2]
    _ ≤ 2 * z * (11 * (1 + z) ^ 3) := mul_le_mul_of_nonneg_left (abs_cubic z hz) hz2
    _ ≤ 30 * z * (1 + z) ^ 3 := by nlinarith

private lemma hN_g_10 (z : ℝ) (hz : 0 < z) :
    |2 * z| ≤ 10 * z * (1 + z) ^ 0 := by
  rw [pow_zero, mul_one]
  have hz2 : (0 : ℝ) ≤ 2 * z := by linarith
  rw [abs_of_nonneg hz2]
  linarith

private lemma hN_f_10 (z : ℝ) (hz : 0 < z) :
    |2 * z * (1 - z)| ≤ 10 * z * (1 + z) ^ 1 := by
  rw [pow_one]
  have hz2 : (0 : ℝ) ≤ 2 * z := by linarith
  calc |2 * z * (1 - z)| = 2 * z * |1 - z| := by rw [abs_mul, abs_of_nonneg hz2]
    _ ≤ 2 * z * (1 + z) := mul_le_mul_of_nonneg_left (abs_one_sub z hz) hz2
    _ ≤ 10 * z * (1 + z) := by nlinarith

private lemma hN_e1_10 (z : ℝ) (hz : 0 < z) :
    |2 * z * (1 - 4 * z + z ^ 2)| ≤ 10 * z * (1 + z) ^ 2 := by
  have hz2 : (0 : ℝ) ≤ 2 * z := by linarith
  calc |2 * z * (1 - 4 * z + z ^ 2)| = 2 * z * |1 - 4 * z + z ^ 2| := by
        rw [abs_mul, abs_of_nonneg hz2]
    _ ≤ 2 * z * (4 * (1 + z) ^ 2) := mul_le_mul_of_nonneg_left (abs_quad z hz) hz2
    _ ≤ 10 * z * (1 + z) ^ 2 := by nlinarith

theorem piece_z_bounds_ab : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
    (|ZIter j (fun z : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3) z| ≤ 30 * (z / (1 + z) ^ 2)) ∧
    (|ZIter j (fun z : ℝ => 2 * z / (1 + z) ^ 2) z| ≤ 10 * (z / (1 + z) ^ 2)) := by
  intro j hj z hz
  interval_cases j
  · constructor
    · simp only [ZIter_zero]
      exact div_bound z hz 1 30 (2 * z * (1 - z)) (hN_f_30 z hz)
    · simp only [ZIter_zero]
      exact div_bound z hz 0 10 (2 * z) (hN_g_10 z hz)
  · constructor
    · rw [ZIter_f_one z hz]
      exact div_bound z hz 2 30 (2 * z * (1 - 4 * z + z ^ 2)) (hN_e1_30 z hz)
    · rw [ZIter_g_one z hz]
      exact div_bound z hz 1 10 (2 * z * (1 - z)) (hN_f_10 z hz)
  · constructor
    · rw [ZIter_f_two z hz]
      exact div_bound z hz 3 30 (2 * z * (1 - 11 * z + 11 * z ^ 2 - z ^ 3)) (hN_e2_30 z hz)
    · rw [ZIter_g_two z hz]
      exact div_bound z hz 2 10 (2 * z * (1 - 4 * z + z ^ 2)) (hN_e1_10 z hz)

end Work.FTS_RegExport.RXT.SysAux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.SysAux.piece_z_bounds_rho =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.SysAux.piece_z_bounds_rho`

The `ρ`-weighted `z`-jet bounds for the two explicit radial profiles of the forcing
(`explicit_piece_bounds`): for `j ≤ 2` and `z > 0`,

* `|(z∂_z)^j (z²/(1+z)³)| ≤ 10 z²/(1+z)²`  and  `≤ 10 z/(1+z)²`,
* `|(z∂_z)^j (z²/(1+z)⁴)| ≤ 10 z²/(1+z)²`.

The strategy is to compute the two-derivative jets explicitly and then pass to the
substitution `u = z/(1+z) ∈ (0,1)`, in which every one of the six rational functions becomes
`u²(1-u)^d · c(u)` with `d ∈ {1,2}` and a *bounded* polynomial factor `c` (explicitly
`1`, `2-3u`, `4-15u+12u²`, `2(1-2u)`, `4(1-5u+5u²)`).  The two targets are then exactly `10u²`
and `10u(1-u)`, and the bounds reduce to `(1-u)^d ≤ 1` and `|c(u)| ≤ 10`.
-/

namespace Work.FTS_RegExport.RXT.SysAux

/-! ## Derivatives of the explicit radial pieces -/

private theorem deriv_zsq (z : ℝ) : deriv (fun z : ℝ => z ^ 2) z = 2 * z := by
  have h := deriv_pow (f := fun z' : ℝ => z') (x := z) differentiableAt_id 2
  rw [show (fun z' : ℝ => z') ^ 2 = (fun z' : ℝ => z' ^ 2) from rfl] at h
  have h1 : deriv (fun z' : ℝ => z') z = 1 := deriv_id z
  rw [h, h1]
  ring

private theorem deriv_one_add_pow (k : ℕ) (z : ℝ) :
    deriv (fun z : ℝ => (1 + z) ^ k) z = (k : ℝ) * (1 + z) ^ (k - 1) := by
  have h := deriv_pow (f := fun z : ℝ => 1 + z) (x := z) (by fun_prop) k
  rw [show (fun z : ℝ => 1 + z) ^ k = (fun z : ℝ => (1 + z) ^ k) from rfl] at h
  rw [h]
  have h1 : deriv (fun z : ℝ => 1 + z) z = 1 := by
    rw [deriv_const_add (1 : ℝ)]
    exact deriv_id z
  rw [h1, mul_one]

private theorem deriv_rho3 (z : ℝ) (hz : 0 < z) :
    deriv (fun z : ℝ => z ^ 2 / (1 + z) ^ 3) z = (2 * z - z ^ 2) / (1 + z) ^ 4 := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  rw [deriv_fun_div (c := fun z : ℝ => z ^ 2) (d := fun z : ℝ => (1 + z) ^ 3)
    (by fun_prop) (by fun_prop) (by positivity)]
  rw [deriv_zsq z, deriv_one_add_pow 3 z]
  field_simp
  ring

private theorem deriv_num_b (z : ℝ) :
    deriv (fun z : ℝ => z ^ 2 * (2 - z)) z = 4 * z - 3 * z ^ 2 := by
  rw [deriv_fun_mul (c := fun z : ℝ => z ^ 2) (d := fun z : ℝ => 2 - z)
    (by fun_prop) (by fun_prop)]
  rw [deriv_zsq z]
  have h2 : deriv (fun z : ℝ => 2 - z) z = -1 := by
    rw [deriv_const_sub (2 : ℝ)]
    simp
  rw [h2]
  ring

private theorem deriv_3b (z : ℝ) (hz : 0 < z) :
    deriv (fun z : ℝ => z ^ 2 * (2 - z) / (1 + z) ^ 4) z
      = z * (4 - 7 * z + z ^ 2) / (1 + z) ^ 5 := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  rw [deriv_fun_div (c := fun z : ℝ => z ^ 2 * (2 - z)) (d := fun z : ℝ => (1 + z) ^ 4)
    (by fun_prop) (by fun_prop) (by positivity)]
  rw [deriv_num_b z, deriv_one_add_pow 4 z]
  field_simp
  ring

private theorem deriv_rho4 (z : ℝ) (hz : 0 < z) :
    deriv (fun z : ℝ => z ^ 2 / (1 + z) ^ 4) z = 2 * z * (1 - z) / (1 + z) ^ 5 := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  rw [deriv_fun_div (c := fun z : ℝ => z ^ 2) (d := fun z : ℝ => (1 + z) ^ 4)
    (by fun_prop) (by fun_prop) (by positivity)]
  rw [deriv_zsq z, deriv_one_add_pow 4 z]
  field_simp
  ring

private theorem deriv_num_d (z : ℝ) :
    deriv (fun z : ℝ => 2 * z ^ 2 * (1 - z)) z = 4 * z - 6 * z ^ 2 := by
  rw [deriv_fun_mul (c := fun z : ℝ => 2 * z ^ 2) (d := fun z : ℝ => 1 - z)
    (by fun_prop) (by fun_prop)]
  rw [deriv_const_mul_field (2 : ℝ), deriv_zsq z]
  have h2 : deriv (fun z : ℝ => 1 - z) z = -1 := by
    rw [deriv_const_sub (1 : ℝ)]
    simp
  rw [h2]
  ring

private theorem deriv_4b (z : ℝ) (hz : 0 < z) :
    deriv (fun z : ℝ => 2 * z ^ 2 * (1 - z) / (1 + z) ^ 5) z
      = 4 * z * (1 - 3 * z + z ^ 2) / (1 + z) ^ 6 := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  rw [deriv_fun_div (c := fun z : ℝ => 2 * z ^ 2 * (1 - z)) (d := fun z : ℝ => (1 + z) ^ 5)
    (by fun_prop) (by fun_prop) (by positivity)]
  rw [deriv_num_d z, deriv_one_add_pow 5 z]
  field_simp
  ring

/-! ## The explicit jets of the two profiles -/

private theorem ZIter_rho3_one (z : ℝ) (hz : 0 < z) :
    ZIter 1 (fun z : ℝ => z ^ 2 / (1 + z) ^ 3) z = z ^ 2 * (2 - z) / (1 + z) ^ 4 := by
  rw [ZIter_succ_apply, ZIter_zero, deriv_rho3 z hz]
  ring

private theorem ZIter_rho3_two (z : ℝ) (hz : 0 < z) :
    ZIter 2 (fun z : ℝ => z ^ 2 / (1 + z) ^ 3) z
      = z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5 := by
  rw [ZIter_succ_apply]
  have heq : Set.EqOn (ZIter 1 (fun z : ℝ => z ^ 2 / (1 + z) ^ 3))
      (fun z : ℝ => z ^ 2 * (2 - z) / (1 + z) ^ 4) (Set.Ioi 0) :=
    fun w hw => ZIter_rho3_one w hw
  have hderiv : deriv (ZIter 1 (fun z : ℝ => z ^ 2 / (1 + z) ^ 3)) z
      = deriv (fun z : ℝ => z ^ 2 * (2 - z) / (1 + z) ^ 4) z :=
    heq.deriv isOpen_Ioi hz
  rw [hderiv, deriv_3b z hz]
  ring

private theorem ZIter_rho4_one (z : ℝ) (hz : 0 < z) :
    ZIter 1 (fun z : ℝ => z ^ 2 / (1 + z) ^ 4) z = 2 * z ^ 2 * (1 - z) / (1 + z) ^ 5 := by
  rw [ZIter_succ_apply, ZIter_zero, deriv_rho4 z hz]
  ring

private theorem ZIter_rho4_two (z : ℝ) (hz : 0 < z) :
    ZIter 2 (fun z : ℝ => z ^ 2 / (1 + z) ^ 4) z
      = 4 * z ^ 2 * (z ^ 2 - 3 * z + 1) / (1 + z) ^ 6 := by
  rw [ZIter_succ_apply]
  have heq : Set.EqOn (ZIter 1 (fun z : ℝ => z ^ 2 / (1 + z) ^ 4))
      (fun z : ℝ => 2 * z ^ 2 * (1 - z) / (1 + z) ^ 5) (Set.Ioi 0) :=
    fun w hw => ZIter_rho4_one w hw
  have hderiv : deriv (ZIter 1 (fun z : ℝ => z ^ 2 / (1 + z) ^ 4)) z
      = deriv (fun z : ℝ => 2 * z ^ 2 * (1 - z) / (1 + z) ^ 5) z :=
    heq.deriv isOpen_Ioi hz
  rw [hderiv, deriv_4b z hz]
  ring

/-! ## The substituted variable `u = z/(1+z)` and the bounded polynomial factors -/

private lemma abs_c2 (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) : |2 - 3 * u| ≤ 10 := by
  rw [abs_le]; constructor <;> nlinarith

private lemma abs_c3 (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) : |4 - 15 * u + 12 * u ^ 2| ≤ 10 := by
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (u - 5 / 8), mul_nonneg (le_of_lt hu0) (by linarith : (0 : ℝ) ≤ 1 - u)]
  · nlinarith [sq_nonneg (u - 5 / 8), mul_nonneg (le_of_lt hu0) (by linarith : (0 : ℝ) ≤ 1 - u)]

private lemma abs_c4 (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) : |2 * (1 - 2 * u)| ≤ 10 := by
  rw [abs_le]; constructor <;> nlinarith

private lemma abs_c5 (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    |4 * (1 - 5 * u + 5 * u ^ 2)| ≤ 10 := by
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (u - 1 / 2), mul_nonneg (le_of_lt hu0) (by linarith : (0 : ℝ) ≤ 1 - u)]
  · nlinarith [sq_nonneg (u - 1 / 2), mul_nonneg (le_of_lt hu0) (by linarith : (0 : ℝ) ≤ 1 - u)]

/-- `|u²(1-u)c| ≤ 10u²` for `u ∈ (0,1)`, `|c| ≤ 10`. -/
private lemma bound_u_sq_d1 {u c : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hc : |c| ≤ 10) :
    |u ^ 2 * (1 - u) * c| ≤ 10 * u ^ 2 := by
  have h1u : (0 : ℝ) < 1 - u := by linarith
  have habs : |u ^ 2 * (1 - u) * c| = u ^ 2 * ((1 - u) * |c|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ 2), abs_of_pos h1u]
    ring
  rw [habs]
  have hle : (1 - u) * |c| ≤ 10 := by
    have := mul_le_mul (by linarith : (1 - u) ≤ 1) hc (abs_nonneg c) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using this
  calc u ^ 2 * ((1 - u) * |c|) ≤ u ^ 2 * 10 := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 10 * u ^ 2 := by ring

/-- `|u²(1-u)²c| ≤ 10u²` for `u ∈ (0,1)`, `|c| ≤ 10`. -/
private lemma bound_u_sq_d2 {u c : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hc : |c| ≤ 10) :
    |u ^ 2 * (1 - u) ^ 2 * c| ≤ 10 * u ^ 2 := by
  have h1u : (0 : ℝ) < 1 - u := by linarith
  have h1u2 : (1 - u) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (le_of_lt hu0) (by linarith : (0 : ℝ) ≤ 2 - u)]
  have habs : |u ^ 2 * (1 - u) ^ 2 * c| = u ^ 2 * ((1 - u) ^ 2 * |c|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 - u) ^ 2)]
    ring
  rw [habs]
  have hle : (1 - u) ^ 2 * |c| ≤ 10 := by
    have := mul_le_mul h1u2 hc (abs_nonneg c) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using this
  calc u ^ 2 * ((1 - u) ^ 2 * |c|) ≤ u ^ 2 * 10 := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 10 * u ^ 2 := by ring

/-- `|u²(1-u)c| ≤ 10u(1-u)` for `u ∈ (0,1)`, `|c| ≤ 10`. -/
private lemma bound_u_lin_d1 {u c : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hc : |c| ≤ 10) :
    |u ^ 2 * (1 - u) * c| ≤ 10 * (u * (1 - u)) := by
  have h1u : (0 : ℝ) < 1 - u := by linarith
  have huc : u * |c| ≤ 10 := by
    have h1 : u * |c| ≤ 1 * |c| := mul_le_mul_of_nonneg_right (le_of_lt hu1) (abs_nonneg c)
    linarith
  have habs : |u ^ 2 * (1 - u) * c| = (u * (1 - u)) * (u * |c|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ 2), abs_of_pos h1u]
    ring
  rw [habs]
  calc (u * (1 - u)) * (u * |c|) ≤ (u * (1 - u)) * 10 :=
        mul_le_mul_of_nonneg_left huc (by positivity)
    _ = 10 * (u * (1 - u)) := by ring

/-! ## The nine bounds -/

private lemma b3_0_sq (z : ℝ) (hz : 0 < z) :
    |z ^ 2 / (1 + z) ^ 3| ≤ 10 * (z ^ 2 / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : z ^ 2 / (1 + z) ^ 3 = u ^ 2 * (1 - u) * 1 := by rw [hu]; field_simp; try ring
  have hrhs : z ^ 2 / (1 + z) ^ 2 = u ^ 2 := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_sq_d1 hu0 hu1 (by norm_num)

private lemma b3_0_lin (z : ℝ) (hz : 0 < z) :
    |z ^ 2 / (1 + z) ^ 3| ≤ 10 * (z / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : z ^ 2 / (1 + z) ^ 3 = u ^ 2 * (1 - u) * 1 := by rw [hu]; field_simp; try ring
  have hrhs : z / (1 + z) ^ 2 = u * (1 - u) := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_lin_d1 hu0 hu1 (by norm_num)

private lemma b3_1_sq (z : ℝ) (hz : 0 < z) :
    |z ^ 2 * (2 - z) / (1 + z) ^ 4| ≤ 10 * (z ^ 2 / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : z ^ 2 * (2 - z) / (1 + z) ^ 4 = u ^ 2 * (1 - u) * (2 - 3 * u) := by
    rw [hu]; field_simp; try ring
  have hrhs : z ^ 2 / (1 + z) ^ 2 = u ^ 2 := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_sq_d1 hu0 hu1 (abs_c2 u hu0 hu1)

private lemma b3_1_lin (z : ℝ) (hz : 0 < z) :
    |z ^ 2 * (2 - z) / (1 + z) ^ 4| ≤ 10 * (z / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : z ^ 2 * (2 - z) / (1 + z) ^ 4 = u ^ 2 * (1 - u) * (2 - 3 * u) := by
    rw [hu]; field_simp; try ring
  have hrhs : z / (1 + z) ^ 2 = u * (1 - u) := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_lin_d1 hu0 hu1 (abs_c2 u hu0 hu1)

private lemma b3_2_sq (z : ℝ) (hz : 0 < z) :
    |z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5| ≤ 10 * (z ^ 2 / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5
      = u ^ 2 * (1 - u) * (4 - 15 * u + 12 * u ^ 2) := by
    rw [hu]; field_simp; try ring
  have hrhs : z ^ 2 / (1 + z) ^ 2 = u ^ 2 := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_sq_d1 hu0 hu1 (abs_c3 u hu0 hu1)

private lemma b3_2_lin (z : ℝ) (hz : 0 < z) :
    |z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5| ≤ 10 * (z / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5
      = u ^ 2 * (1 - u) * (4 - 15 * u + 12 * u ^ 2) := by
    rw [hu]; field_simp; try ring
  have hrhs : z / (1 + z) ^ 2 = u * (1 - u) := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_lin_d1 hu0 hu1 (abs_c3 u hu0 hu1)

private lemma b4_0_sq (z : ℝ) (hz : 0 < z) :
    |z ^ 2 / (1 + z) ^ 4| ≤ 10 * (z ^ 2 / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : z ^ 2 / (1 + z) ^ 4 = u ^ 2 * (1 - u) ^ 2 * 1 := by rw [hu]; field_simp; try ring
  have hrhs : z ^ 2 / (1 + z) ^ 2 = u ^ 2 := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_sq_d2 hu0 hu1 (by norm_num)

private lemma b4_1_sq (z : ℝ) (hz : 0 < z) :
    |2 * z ^ 2 * (1 - z) / (1 + z) ^ 5| ≤ 10 * (z ^ 2 / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : 2 * z ^ 2 * (1 - z) / (1 + z) ^ 5 = u ^ 2 * (1 - u) ^ 2 * (2 * (1 - 2 * u)) := by
    rw [hu]; field_simp; try ring
  have hrhs : z ^ 2 / (1 + z) ^ 2 = u ^ 2 := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_sq_d2 hu0 hu1 (abs_c4 u hu0 hu1)

private lemma b4_2_sq (z : ℝ) (hz : 0 < z) :
    |4 * z ^ 2 * (z ^ 2 - 3 * z + 1) / (1 + z) ^ 6| ≤ 10 * (z ^ 2 / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : 4 * z ^ 2 * (z ^ 2 - 3 * z + 1) / (1 + z) ^ 6
      = u ^ 2 * (1 - u) ^ 2 * (4 * (1 - 5 * u + 5 * u ^ 2)) := by
    rw [hu]; field_simp; try ring
  have hrhs : z ^ 2 / (1 + z) ^ 2 = u ^ 2 := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_sq_d2 hu0 hu1 (abs_c5 u hu0 hu1)

theorem piece_z_bounds_rho : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
    (|ZIter j (fun z : ℝ => z ^ 2 / (1 + z) ^ 3) z| ≤ 10 * (z ^ 2 / (1 + z) ^ 2)) ∧
    (|ZIter j (fun z : ℝ => z ^ 2 / (1 + z) ^ 3) z| ≤ 10 * (z / (1 + z) ^ 2)) ∧
    (|ZIter j (fun z : ℝ => z ^ 2 / (1 + z) ^ 4) z| ≤ 10 * (z ^ 2 / (1 + z) ^ 2)) := by
  intro j hj z hz
  interval_cases j
  · exact ⟨b3_0_sq z hz, b3_0_lin z hz, b4_0_sq z hz⟩
  · rw [ZIter_rho3_one z hz, ZIter_rho4_one z hz]
    exact ⟨b3_1_sq z hz, b3_1_lin z hz, b4_1_sq z hz⟩
  · rw [ZIter_rho3_two z hz, ZIter_rho4_two z hz]
    exact ⟨b3_2_sq z hz, b3_2_lin z hz, b4_2_sq z hz⟩

end Work.FTS_RegExport.RXT.SysAux
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB2.BrNegFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB2

open scoped Real Topology
open Set Filter

/-! ## The lower half-strip and reflection calculus

The target `BrNegFacts` concerns the reflected-negated function
`(w,θ) ↦ -P w (-θ)` on the lower half-strip `(0,∞) × (-π/2, 0)`, where `P` is only known
to be `C²` on the open quadrant `Qd = (0,∞) × (0,π/2)`.  Everything here is the
elementary calculus of the substitution `θ ↦ -θ` composed with the outer sign change. -/

/-- The lower half-strip `(0,∞) × (-π/2, 0)`. -/
private def Qdn : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2)) 0

private lemma isOpen_Qd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo



private lemma mem_Qd_of_neg {w θ : ℝ} (hw : 0 < w) (h1 : -(Real.pi / 2) < θ) (h2 : θ < 0) :
    (w, -θ) ∈ Work.Construction.Qd := by
  refine ⟨hw, ?_, ?_⟩
  · linarith
  · linarith

/-! ### First-order reflection identities (pure `deriv` calculus) -/

/-- The `z`-derivative of the reflection-negation only sees the reflection: no
differentiability is needed (the result is unconditional). -/
private lemma pz_neg_reflect (Q : ℝ → ℝ → ℝ) (w θ : ℝ) :
    Work.Spaces.pz (fun w θ => -Q w (-θ)) w θ = -Work.Spaces.pz Q w (-θ) := by
  simp only [Work.Spaces.pz]
  exact deriv.neg

/-- The `θ`-derivative of the reflection, at the level of `deriv`. -/
private lemma deriv_reflect (Q : ℝ → ℝ → ℝ) (w θ : ℝ)
    (h : DifferentiableAt ℝ (fun u => Q w u) (-θ)) :
    deriv (fun θ' => Q w (-θ')) θ = -deriv (fun u => Q w u) (-θ) := by
  change deriv ((fun u => Q w u) ∘ (fun θ' : ℝ => -θ')) θ = -deriv (fun u => Q w u) (-θ)
  have h1 : HasDerivAt (fun u => Q w u) (deriv (fun u => Q w u) (-θ)) (-θ) := h.hasDerivAt
  have h2 : HasDerivAt (fun θ' : ℝ => -θ') (-1) θ := hasDerivAt_neg θ
  rw [(h1.comp θ h2).deriv, mul_neg_one]


/-- The `θ`-derivative of the reflection-negation. -/
private lemma pth_neg_reflect (Q : ℝ → ℝ → ℝ) (w θ : ℝ)
    (h : DifferentiableAt ℝ (fun u => Q w u) (-θ)) :
    Work.Spaces.pth (fun w θ => -Q w (-θ)) w θ = Work.Spaces.pth Q w (-θ) := by
  have h1 : deriv (fun θ' => -Q w (-θ')) θ = -deriv (fun θ' => Q w (-θ')) θ := deriv.neg
  simp only [Work.Spaces.pth]
  rw [h1, deriv_reflect Q w θ h, neg_neg]

/-! ### Differentiability of the slices, from `C²`-regularity on the open quadrant -/

section SliceDiff

variable {P : ℝ → ℝ → ℝ}

private lemma differentiableAt_uncurry_of_Qd (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) :
    DifferentiableAt ℝ (Function.uncurry P) p :=
  (hP.differentiableOn (n := 2) (by norm_num)).differentiableAt (isOpen_Qd.mem_nhds hp)

private lemma differentiableAt_slice_P (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {w θ : ℝ} (hw : 0 < w) (h1 : -(Real.pi / 2) < θ) (h2 : θ < 0) :
    DifferentiableAt ℝ (fun u => P w u) (-θ) :=
  Work.Spaces.differentiableAt_curry_right
    (differentiableAt_uncurry_of_Qd hP (mem_Qd_of_neg hw h1 h2))

private lemma differentiableAt_uncurry_pz_of_Qd (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) :
    DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pz P)) p :=
  ((Work.Spaces.uncurry_partial_c1 isOpen_Qd hP).1.differentiableOn (by norm_num)).differentiableAt
    (isOpen_Qd.mem_nhds hp)

private lemma differentiableAt_uncurry_pth_of_Qd (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {p : ℝ × ℝ} (hp : p ∈ Work.Construction.Qd) :
    DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth P)) p :=
  ((Work.Spaces.uncurry_partial_c1 isOpen_Qd hP).2.differentiableOn (by norm_num)).differentiableAt
    (isOpen_Qd.mem_nhds hp)

private lemma differentiableAt_slice_pz (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {w θ : ℝ} (hw : 0 < w) (h1 : -(Real.pi / 2) < θ) (h2 : θ < 0) :
    DifferentiableAt ℝ (fun u => Work.Spaces.pz P w u) (-θ) :=
  Work.Spaces.differentiableAt_curry_right
    (differentiableAt_uncurry_pz_of_Qd hP (mem_Qd_of_neg hw h1 h2))

private lemma differentiableAt_slice_pth (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {w θ : ℝ} (hw : 0 < w) (h1 : -(Real.pi / 2) < θ) (h2 : θ < 0) :
    DifferentiableAt ℝ (fun u => Work.Spaces.pth P w u) (-θ) :=
  Work.Spaces.differentiableAt_curry_right
    (differentiableAt_uncurry_pth_of_Qd hP (mem_Qd_of_neg hw h1 h2))

/-- The `θ`-derivative of `Pn` equals that of `P` at the reflected point, on the strip. -/
private lemma pth_neg_reflect_of_neg (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    {w θ : ℝ} (hw : 0 < w) (h1 : -(Real.pi / 2) < θ) (h2 : θ < 0) :
    Work.Spaces.pth (fun w θ => -P w (-θ)) w θ = Work.Spaces.pth P w (-θ) :=
  pth_neg_reflect P w θ (differentiableAt_slice_P hP hw h1 h2)

/-- The function identity `pz Pn = fun w θ => -pz P w (-θ)` (unconditional). -/
private lemma pz_neg_reflect_funext (P : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun w θ => -P w (-θ)) = fun w θ => -Work.Spaces.pz P w (-θ) := by
  funext w θ
  exact pz_neg_reflect P w θ

end SliceDiff

theorem BrNegFacts {P : ℝ → ℝ → ℝ}
    (hP : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd) :
    ContDiffOn ℝ 2 (Function.uncurry (fun w θ => -P w (-θ)))
        (Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2)) 0) ∧
    (∀ w θ, 0 < w → -(Real.pi / 2) < θ → θ < 0 →
      Work.Spaces.pz (fun w θ => -P w (-θ)) w θ = -Work.Spaces.pz P w (-θ) ∧
      Work.Spaces.pth (fun w θ => -P w (-θ)) w θ = Work.Spaces.pth P w (-θ) ∧
      Work.Spaces.pz (Work.Spaces.pz (fun w θ => -P w (-θ))) w θ
        = -Work.Spaces.pz (Work.Spaces.pz P) w (-θ) ∧
      Work.Spaces.pth (Work.Spaces.pz (fun w θ => -P w (-θ))) w θ
        = Work.Spaces.pth (Work.Spaces.pz P) w (-θ) ∧
      Work.Spaces.pz (Work.Spaces.pth (fun w θ => -P w (-θ))) w θ
        = Work.Spaces.pz (Work.Spaces.pth P) w (-θ) ∧
      Work.Spaces.pth (Work.Spaces.pth (fun w θ => -P w (-θ))) w θ
        = -Work.Spaces.pth (Work.Spaces.pth P) w (-θ)) := by
  have hcont : ContDiffOn ℝ 2 (Function.uncurry (fun w θ => -P w (-θ))) Qdn := by
    have hR : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (p.1, -p.2)) Qdn :=
      (by fun_prop : ContDiff ℝ 2 (fun p : ℝ × ℝ => (p.1, -p.2))).contDiffOn
    have hmap : Set.MapsTo (fun p : ℝ × ℝ => (p.1, -p.2)) Qdn Work.Construction.Qd := by
      rintro ⟨w, θ⟩ ⟨hw, h1, h2⟩
      exact mem_Qd_of_neg hw h1 h2
    have hcomp : ContDiffOn ℝ 2
        ((Function.uncurry P) ∘ (fun p : ℝ × ℝ => (p.1, -p.2))) Qdn :=
      hP.comp hR hmap
    have hneg := hcomp.neg
    refine hneg.congr ?_
    intro p _
    rfl
  refine ⟨hcont, ?_⟩
  intro w θ hw h1 h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `∂_z (-P(w,-θ)) = -(∂_z P)(w,-θ)`
    exact pz_neg_reflect P w θ
  · -- `∂_θ (-P(w,-θ)) = (∂_θ P)(w,-θ)`
    exact pth_neg_reflect_of_neg hP hw h1 h2
  · -- `∂_z∂_z (-P(w,-θ)) = -(∂_z∂_z P)(w,-θ)`
    rw [pz_neg_reflect_funext P]
    exact pz_neg_reflect (Work.Spaces.pz P) w θ
  · -- `∂_θ∂_z (-P(w,-θ)) = (∂_θ∂_z P)(w,-θ)`
    rw [pz_neg_reflect_funext P]
    exact pth_neg_reflect (Work.Spaces.pz P) w θ (differentiableAt_slice_pz hP hw h1 h2)
  · -- `∂_z∂_θ (-P(w,-θ)) = (∂_z∂_θ P)(w,-θ)`
    have hev : (fun w' => Work.Spaces.pth (fun w θ => -P w (-θ)) w' θ)
        =ᶠ[𝓝 w] (fun w' => Work.Spaces.pth P w' (-θ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hw] with w' hw'
      exact pth_neg_reflect_of_neg hP hw' h1 h2
    simpa only [Work.Spaces.pz] using hev.deriv_eq
  · -- `∂_θ∂_θ (-P(w,-θ)) = -(∂_θ∂_θ P)(w,-θ)`
    have hev : (fun θ' => Work.Spaces.pth (fun w θ => -P w (-θ)) w θ')
        =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pth P w (-θ')) := by
      filter_upwards [isOpen_Ioo.mem_nhds ⟨h1, h2⟩] with θ' hθ'
      exact pth_neg_reflect_of_neg hP hw hθ'.1 hθ'.2
    have hd : deriv (fun θ' => Work.Spaces.pth P w (-θ')) θ
        = -Work.Spaces.pth (Work.Spaces.pth P) w (-θ) :=
      deriv_reflect (Work.Spaces.pth P) w θ (differentiableAt_slice_pth hP hw h1 h2)
    simpa only [Work.Spaces.pth] using hev.deriv_eq.trans hd

end Work.FTS_StreamBdry.SB2
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB3.P2Aux.bslOp_Dz_comm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_StreamBdry.SB3.P2Aux

namespace BslDzAux

/-! ## Smoothness of the partials of a `C^n` function

The two lemmas below make the finite-order regularity of the partial derivatives available:
`∂_z f` (resp. `∂_θ f`) loses exactly one order of differentiability.  The proofs identify the
partial with the evaluation of `fderiv` on a basis vector, use `ContDiffAt.fderiv_right`, and
transfer the resulting `ContDiffAt` statement back along the eventual equality
`pz f =ᶠ fun q => (fderiv ℝ (uncurry f) q) (1,0)` (valid where `f` is differentiable, which is
eventual by `ContDiffAt.eventually`). -/

/-- `∂_z` lowers the order of differentiability by one. -/
theorem contDiffAt_uncurry_pz_succ {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ} (n : ℕ)
    (h : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry f) p) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz f)) p := by
  have hfd : ContDiffAt ℝ (n : WithTop ℕ∞) (fderiv ℝ (Function.uncurry f)) p :=
    h.fderiv_right (by push_cast; rfl)
  have hev : ∀ᶠ y in 𝓝 p, DifferentiableAt ℝ (Function.uncurry f) y :=
    (h.eventually (by
      intro hh
      exact ENat.natCast_ne_top (n + 1) (WithTop.coe_injective hh))).mono
      (fun y hy => hy.differentiableAt (by norm_num))
  have heq : (fun q : ℝ × ℝ => Work.Spaces.pz f q.1 q.2)
      =ᶠ[𝓝 p] (fun q : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) q) (1, 0)) := by
    filter_upwards [hev] with q hq
    exact Work.Spaces.pz_eq_fderiv hq
  exact (hfd.clm_apply contDiffAt_const).congr_of_eventuallyEq heq

/-- `∂_θ` lowers the order of differentiability by one. -/
theorem contDiffAt_uncurry_pth_succ {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ} (n : ℕ)
    (h : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry f) p) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pth f)) p := by
  have hfd : ContDiffAt ℝ (n : WithTop ℕ∞) (fderiv ℝ (Function.uncurry f)) p :=
    h.fderiv_right (by push_cast; rfl)
  have hev : ∀ᶠ y in 𝓝 p, DifferentiableAt ℝ (Function.uncurry f) y :=
    (h.eventually (by
      intro hh
      exact ENat.natCast_ne_top (n + 1) (WithTop.coe_injective hh))).mono
      (fun y hy => hy.differentiableAt (by norm_num))
  have heq : (fun q : ℝ × ℝ => Work.Spaces.pth f q.1 q.2)
      =ᶠ[𝓝 p] (fun q : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) q) (0, 1)) := by
    filter_upwards [hev] with q hq
    exact Work.Spaces.pth_eq_fderiv hq
  exact (hfd.clm_apply contDiffAt_const).congr_of_eventuallyEq heq

/-! ## The factor `z` is invisible to `∂_θ` -/

/-- Multiplication by the radial variable is constant in `θ`, hence invisible to `∂_θ`. -/
lemma pth_z_mul (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z' θ' => z' * X z' θ') z θ = z * Work.Spaces.pth X z θ := by
  show deriv (fun θ' => z * X z θ') θ = z * deriv (fun θ' => X z θ') θ
  rw [deriv_const_mul_field]

/-- The same, for two angular derivatives. -/
lemma pthIter_two_z_mul (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 (fun z' θ' => z' * X z' θ') z θ
      = z * Work.Spaces.pthIter 2 X z θ := by
  have hfun : Work.Spaces.pth (fun z' θ' => z' * X z' θ')
      = fun z' θ' => z' * Work.Spaces.pth X z' θ' :=
    funext fun z' => funext fun θ' => pth_z_mul X z' θ'
  show Work.Spaces.pth (Work.Spaces.pth (fun z' θ' => z' * X z' θ')) z θ
      = z * Work.Spaces.pth (Work.Spaces.pth X) z θ
  rw [hfun, pth_z_mul]

/-! ## Congruence of the partials along an eventual equality -/

/-- Functions agreeing near `(z,θ)` have the same `∂_θ` there. -/
lemma pth_congr_of_eventuallyEq {f g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : (fun p : ℝ × ℝ => f p.1 p.2) =ᶠ[𝓝 (z, θ)] (fun p : ℝ × ℝ => g p.1 p.2)) :
    Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  have hnb : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => g z θ') :=
    (Continuous.prodMk_right z).continuousAt.eventually h
  exact hnb.deriv_eq

/-- Functions agreeing near `(z,θ)` have the same `∂_z` there. -/
lemma pz_congr_of_eventuallyEq {f g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : (fun p : ℝ × ℝ => f p.1 p.2) =ᶠ[𝓝 (z, θ)] (fun p : ℝ × ℝ => g p.1 p.2)) :
    Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
  have hnb : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => g z' θ) :=
    (Continuous.prodMk_left θ).continuousAt.eventually h
  exact hnb.deriv_eq

/-- Functions agreeing near `(z,θ)` have the same `D_z` there. -/
lemma Dz_congr_of_eventuallyEq {f g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : (fun p : ℝ × ℝ => f p.1 p.2) =ᶠ[𝓝 (z, θ)] (fun p : ℝ × ℝ => g p.1 p.2)) :
    Work.Spaces.Dz f z θ = Work.Spaces.Dz g z θ := by
  show z * Work.Spaces.pz f z θ = z * Work.Spaces.pz g z θ
  rw [pz_congr_of_eventuallyEq h]

/-! ## Clairaut at order two -/

/-- The order-two mixed partials of a `C³` function agree: `∂_z ∂_θ² f = ∂_θ² ∂_z f`. -/
theorem pz_pthIter_two_comm {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h2 : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ))
    (h2p : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth f)) (z, θ)) :
    Work.Spaces.pz (Work.Spaces.pthIter 2 f) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz f) z θ := by
  have hev : (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pth f) p.1 p.2)
      =ᶠ[𝓝 (z, θ)] (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2) := by
    filter_upwards [(h2.eventually (by decide : (2 : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞)))] with y hy
    exact Work.Spaces.pz_pth_comm hy
  have h1 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth f)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth f)) z θ :=
    Work.Spaces.pz_pth_comm h2p
  have h3 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth f)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz f)) z θ :=
    pth_congr_of_eventuallyEq hev
  rw [show Work.Spaces.pthIter 2 f = Work.Spaces.pth (Work.Spaces.pth f) from rfl,
    show Work.Spaces.pthIter 2 (Work.Spaces.pz f)
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz f)) from rfl, h1, h3]

/-! ## The individual slots of `Lzero` -/

/-- `∂_z` distributes over the three slots of `Lzero`. -/
lemma pz_Lzero {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hd1 : DifferentiableAt ℝ (fun s => Work.Spaces.pthIter 2 f s θ) z)
    (hd2 : DifferentiableAt ℝ
      (fun s => Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ') s θ) z)
    (hd3 : DifferentiableAt ℝ (fun s => f s θ) z) :
    Work.Spaces.pz (Work.Elliptic.Lzero f) z θ
      = -Work.Spaces.pz (Work.Spaces.pthIter 2 f) z θ
        + Work.Spaces.pz (Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ')) z θ
        - 6 * Work.Spaces.pz f z θ := by
  have hmain : deriv ((-(fun s => Work.Spaces.pthIter 2 f s θ))
        + (fun s => Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ') s θ)
        - (fun s => 6 * f s θ)) z
      = -(Work.Spaces.pz (Work.Spaces.pthIter 2 f) z θ)
        + Work.Spaces.pz (Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ')) z θ
        - 6 * Work.Spaces.pz f z θ := by
    rw [deriv_sub (hd1.neg.add hd2) (hd3.const_mul 6), deriv_add hd1.neg hd2, deriv.neg,
      deriv_const_mul_field]
    simp only [Work.Spaces.pz]
  show deriv (fun s => Work.Elliptic.Lzero f s θ) z = _
  rw [show (fun s => Work.Elliptic.Lzero f s θ)
      = (-(fun s => Work.Spaces.pthIter 2 f s θ))
        + (fun s => Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ') s θ)
        - (fun s => 6 * f s θ) from rfl]
  exact hmain

/-- `∂_z ∂_θ` of the `tan θ ·` slot equals `∂_θ` of `tan θ · ∂_z` (Clairaut plus the fact
that the `z`-derivative of the coefficient `tan θ` vanishes). -/
lemma pz_pth_tan_mul {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h2T : ContDiffAt ℝ 2 (Function.uncurry (fun z θ' => Real.tan θ' * f z θ')) (z, θ)) :
    Work.Spaces.pz (Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ')) z θ
      = Work.Spaces.pth (fun z θ' => Real.tan θ' * Work.Spaces.pz f z θ') z θ := by
  have hfun : Work.Spaces.pz (fun z θ' => Real.tan θ' * f z θ')
      = fun z θ' => Real.tan θ' * Work.Spaces.pz f z θ' := by
    funext z' θ'
    show deriv (fun s => Real.tan θ' * f s θ') z' = Real.tan θ' * deriv (fun s => f s θ') z'
    rw [deriv_const_mul_field]
  rw [Work.Spaces.pz_pth_comm h2T, hfun]

/-- The `tan θ ·` slot of `Lzero (D_z f)`, in terms of `∂_z f`. -/
lemma pth_tan_Dz (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z θ' => Real.tan θ' * Work.Spaces.Dz f z θ') z θ
      = z * Work.Spaces.pth (fun z θ' => Real.tan θ' * Work.Spaces.pz f z θ') z θ := by
  have hfun : (fun z θ' => Real.tan θ' * Work.Spaces.Dz f z θ')
      = fun z θ' => z * (Real.tan θ' * Work.Spaces.pz f z θ') := by
    funext z' θ'; simp only [Work.Spaces.Dz]; ring
  rw [hfun]
  exact pth_z_mul (fun z θ' => Real.tan θ' * Work.Spaces.pz f z θ') z θ

/-! ## `Lzero` commutes with `D_z` -/

/-- `Lzero` has `θ`-only coefficients, so it commutes with `D_z = z ∂_z`: at a point where `f`
is `C³` and `cos θ ≠ 0`, `Lzero (D_z f) = D_z (Lzero f)`. -/
theorem Lzero_Dz_comm {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h3 : ContDiffAt ℝ 3 (Function.uncurry f) (z, θ)) (hcos : Real.cos θ ≠ 0) :
    Work.Elliptic.Lzero (Work.Spaces.Dz f) z θ = Work.Spaces.Dz (Work.Elliptic.Lzero f) z θ := by
  have h2 : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) := h3.of_le (by norm_num)
  have h1 : ContDiffAt ℝ 1 (Function.uncurry f) (z, θ) := h3.of_le (by norm_num)
  have h2p : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth f)) (z, θ) :=
    contDiffAt_uncurry_pth_succ 2 h3
  have h1pp : ContDiffAt ℝ 1 (Function.uncurry (Work.Spaces.pthIter 2 f)) (z, θ) :=
    contDiffAt_uncurry_pth_succ 1 h2p
  have h2T : ContDiffAt ℝ 2 (Function.uncurry (fun z θ' => Real.tan θ' * f z θ')) (z, θ) := by
    have hproj : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => p.2) (z, θ) := contDiff_snd.contDiffAt
    have htan : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.tan p.2) (z, θ) :=
      ContDiffAt.comp (z, θ) (g := Real.tan) (f := fun p : ℝ × ℝ => p.2)
        (Real.contDiffAt_tan.mpr hcos) hproj
    exact htan.mul h2
  have h1T : ContDiffAt ℝ 1
      (Function.uncurry (Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ'))) (z, θ) :=
    contDiffAt_uncurry_pth_succ 1 h2T
  have hd1 : DifferentiableAt ℝ (fun s => Work.Spaces.pthIter 2 f s θ) z :=
    (Work.Elliptic.contDiffAt_uncurry_slice_fst (Work.Spaces.pthIter 2 f) z θ h1pp).differentiableAt
      (by norm_num)
  have hd2 : DifferentiableAt ℝ
      (fun s => Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ') s θ) z :=
    (Work.Elliptic.contDiffAt_uncurry_slice_fst
      (Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ')) z θ h1T).differentiableAt (by norm_num)
  have hd3 : DifferentiableAt ℝ (fun s => f s θ) z :=
    (Work.Elliptic.contDiffAt_uncurry_slice_fst f z θ h1).differentiableAt (by norm_num)
  have e1 : Work.Spaces.pthIter 2 (Work.Spaces.Dz f) z θ
      = z * Work.Spaces.pthIter 2 (Work.Spaces.pz f) z θ := by
    rw [show Work.Spaces.Dz f = fun z θ' => z * Work.Spaces.pz f z θ' from rfl]
    exact pthIter_two_z_mul (Work.Spaces.pz f) z θ
  have e2 : Work.Spaces.pth (fun z θ' => Real.tan θ' * Work.Spaces.Dz f z θ') z θ
      = z * Work.Spaces.pth (fun z θ' => Real.tan θ' * Work.Spaces.pz f z θ') z θ :=
    pth_tan_Dz f z θ
  have e3 : Work.Spaces.Dz f z θ = z * Work.Spaces.pz f z θ := rfl
  have e4 : Work.Spaces.pz (Work.Spaces.pthIter 2 f) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz f) z θ := pz_pthIter_two_comm h2 h2p
  have e5 : Work.Spaces.pz (Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ')) z θ
      = Work.Spaces.pth (fun z θ' => Real.tan θ' * Work.Spaces.pz f z θ') z θ :=
    pz_pth_tan_mul h2T
  have e6 : Work.Spaces.pz (Work.Elliptic.Lzero f) z θ
      = -Work.Spaces.pz (Work.Spaces.pthIter 2 f) z θ
        + Work.Spaces.pz (Work.Spaces.pth (fun z θ' => Real.tan θ' * f z θ')) z θ
        - 6 * Work.Spaces.pz f z θ := pz_Lzero hd1 hd2 hd3
  show -(Work.Spaces.pthIter 2 (Work.Spaces.Dz f) z θ)
        + Work.Spaces.pth (fun z θ' => Real.tan θ' * Work.Spaces.Dz f z θ') z θ
        - 6 * (Work.Spaces.Dz f z θ)
      = z * Work.Spaces.pz (Work.Elliptic.Lzero f) z θ
  rw [e6, e4, e5, e1, e2, e3]
  ring

/-! ## `bslOp` in terms of `D_z` -/

/-- `bslOp α f = -α²D_z² f - 5αD_z f + Lzero f` at a point where `f` is `C²`. -/
lemma bslOp_eq_Dz_form {α : ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h2 : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    Work.Elliptic.bslOp α f z θ
      = -(α ^ 2) * Work.Spaces.DzIter 2 f z θ - (5 * α) * Work.Spaces.Dz f z θ
        + Work.Elliptic.Lzero f z θ := by
  have h : Work.Spaces.DzIter 2 f z θ = z * Work.Spaces.pz f z θ
      + z ^ 2 * Work.Spaces.pzIter 2 f z θ := by
    rw [Work.FTS_RegExport.RXT.dziter_two_fb h2]
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
  have h' : Work.Spaces.Dz f z θ = z * Work.Spaces.pz f z θ := rfl
  rw [Work.Elliptic.bslOp_apply, h, h']
  ring

/-- Multiplication by `z` is `D_z` on the first slot of the `D_z`-expansion of `bslOp`. -/
lemma Dz_lin_expand {α : ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hd1 : DifferentiableAt ℝ (fun s => Work.Spaces.DzIter 2 f s θ) z)
    (hd2 : DifferentiableAt ℝ (fun s => Work.Spaces.Dz f s θ) z)
    (hd3 : DifferentiableAt ℝ (fun s => Work.Elliptic.Lzero f s θ) z) :
    Work.Spaces.Dz (fun z θ => -(α ^ 2) * Work.Spaces.DzIter 2 f z θ
        - (5 * α) * Work.Spaces.Dz f z θ + Work.Elliptic.Lzero f z θ) z θ
      = -(α ^ 2) * Work.Spaces.DzIter 3 f z θ - (5 * α) * Work.Spaces.DzIter 2 f z θ
        + Work.Spaces.Dz (Work.Elliptic.Lzero f) z θ := by
  have hderiv : deriv (((fun s => -(α ^ 2) * Work.Spaces.DzIter 2 f s θ)
        - (fun s => (5 * α) * Work.Spaces.Dz f s θ))
        + (fun s => Work.Elliptic.Lzero f s θ)) z
      = -(α ^ 2) * deriv (fun s => Work.Spaces.DzIter 2 f s θ) z
        - (5 * α) * deriv (fun s => Work.Spaces.Dz f s θ) z
        + deriv (fun s => Work.Elliptic.Lzero f s θ) z := by
    rw [deriv_add ((hd1.const_mul _).sub (hd2.const_mul _)) hd3,
      deriv_sub (hd1.const_mul _) (hd2.const_mul _), deriv_const_mul_field, deriv_const_mul_field]
  show z * deriv (fun s => -(α ^ 2) * Work.Spaces.DzIter 2 f s θ
        - (5 * α) * Work.Spaces.Dz f s θ + Work.Elliptic.Lzero f s θ) z = _
  rw [show (fun s => -(α ^ 2) * Work.Spaces.DzIter 2 f s θ
        - (5 * α) * Work.Spaces.Dz f s θ + Work.Elliptic.Lzero f s θ)
      = ((fun s => -(α ^ 2) * Work.Spaces.DzIter 2 f s θ)
        - (fun s => (5 * α) * Work.Spaces.Dz f s θ))
        + (fun s => Work.Elliptic.Lzero f s θ) from rfl,
    hderiv,
    show Work.Spaces.DzIter 3 f z θ = z * deriv (fun s => Work.Spaces.DzIter 2 f s θ) z from rfl,
    show Work.Spaces.DzIter 2 f z θ = z * deriv (fun s => Work.Spaces.Dz f s θ) z from rfl,
    show Work.Spaces.Dz (Work.Elliptic.Lzero f) z θ
      = z * deriv (fun s => Work.Elliptic.Lzero f s θ) z from rfl]
  ring

end BslDzAux

open BslDzAux

/-- `bslOp` commutes with `D_z = z ∂_z`: pointwise on the open quadrant, for a function that is
`C^3` at the point (`bslOp = -α²D_z² - 5αD_z + Lzero`, and `Lzero` has `θ`-only coefficients). -/
theorem bslOp_Dz_comm {α : ℝ} {Q : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hmem : (z, θ) ∈ Work.Construction.Qd)
    (hQ : ContDiffAt ℝ 3 (Function.uncurry Q) (z, θ)) :
    Work.Elliptic.bslOp α (Work.Spaces.Dz Q) z θ
      = Work.Spaces.Dz (Work.Elliptic.bslOp α Q) z θ := by
  have hθ1 : 0 < θ := hmem.2.1
  have hθ2 : θ < π / 2 := hmem.2.2
  have hcos : Real.cos θ ≠ 0 := by
    have hpos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact ne_of_gt hpos
  have h1 : ContDiffAt ℝ 1 (Function.uncurry Q) (z, θ) := hQ.of_le (by norm_num)
  have h2pz : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pz Q)) (z, θ) :=
    contDiffAt_uncurry_pz_succ 2 hQ
  have h1pz : ContDiffAt ℝ 1 (Function.uncurry (Work.Spaces.pz Q)) (z, θ) :=
    h2pz.of_le (by norm_num)
  have h1pz2 : ContDiffAt ℝ 1 (Function.uncurry (Work.Spaces.pzIter 2 Q)) (z, θ) :=
    contDiffAt_uncurry_pz_succ 1 h2pz
  have h2pth : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth Q)) (z, θ) :=
    contDiffAt_uncurry_pth_succ 2 hQ
  have h1pth2 : ContDiffAt ℝ 1 (Function.uncurry (Work.Spaces.pthIter 2 Q)) (z, θ) :=
    contDiffAt_uncurry_pth_succ 1 h2pth
  have h2T : ContDiffAt ℝ 2 (Function.uncurry (fun z θ' => Real.tan θ' * Q z θ')) (z, θ) := by
    have hproj : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => p.2) (z, θ) := contDiff_snd.contDiffAt
    have htan : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.tan p.2) (z, θ) :=
      ContDiffAt.comp (z, θ) (g := Real.tan) (f := fun p : ℝ × ℝ => p.2)
        (Real.contDiffAt_tan.mpr hcos) hproj
    exact htan.mul (hQ.of_le (by norm_num))
  have h1T : ContDiffAt ℝ 1
      (Function.uncurry (Work.Spaces.pth (fun z θ' => Real.tan θ' * Q z θ'))) (z, θ) :=
    contDiffAt_uncurry_pth_succ 1 h2T
  -- `C²`-regularity of `D_z Q`
  have h2Dz : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.Dz Q)) (z, θ) := by
    have hfst : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => p.1) (z, θ) := contDiff_fst.contDiffAt
    exact hfst.mul h2pz
  have h1pzDz : ContDiffAt ℝ 1 (Function.uncurry (Work.Spaces.pz (Work.Spaces.Dz Q))) (z, θ) :=
    contDiffAt_uncurry_pz_succ 1 h2Dz
  -- differentiability of the slices appearing in the two expansions
  have hsliceQ : DifferentiableAt ℝ (fun s => Q s θ) z :=
    (Work.Elliptic.contDiffAt_uncurry_slice_fst Q z θ h1).differentiableAt (by norm_num)
  have hpz1 : DifferentiableAt ℝ (fun s => Work.Spaces.pz Q s θ) z :=
    (Work.Elliptic.contDiffAt_uncurry_slice_fst (Work.Spaces.pz Q) z θ h1pz).differentiableAt
      (by norm_num)
  have hpz2 : DifferentiableAt ℝ (fun s => Work.Spaces.pzIter 2 Q s θ) z :=
    (Work.Elliptic.contDiffAt_uncurry_slice_fst (Work.Spaces.pzIter 2 Q) z θ h1pz2).differentiableAt
      (by norm_num)
  have hpzDz : DifferentiableAt ℝ (fun s => Work.Spaces.pz (Work.Spaces.Dz Q) s θ) z :=
    (Work.Elliptic.contDiffAt_uncurry_slice_fst (Work.Spaces.pz (Work.Spaces.Dz Q)) z θ
      h1pzDz).differentiableAt (by norm_num)
  have hd1 : DifferentiableAt ℝ (fun s => Work.Spaces.DzIter 2 Q s θ) z := by
    have : (fun s : ℝ => Work.Spaces.DzIter 2 Q s θ)
        = fun s : ℝ => s * Work.Spaces.pz (Work.Spaces.Dz Q) s θ := rfl
    rw [this]
    exact differentiableAt_id.mul hpzDz
  have hd2 : DifferentiableAt ℝ (fun s => Work.Spaces.Dz Q s θ) z := by
    have : (fun s : ℝ => Work.Spaces.Dz Q s θ) = fun s : ℝ => s * Work.Spaces.pz Q s θ := rfl
    rw [this]
    exact differentiableAt_id.mul hpz1
  have hd3 : DifferentiableAt ℝ (fun s => Work.Elliptic.Lzero Q s θ) z :=
    (((Work.Elliptic.contDiffAt_uncurry_slice_fst (Work.Spaces.pthIter 2 Q) z θ
          h1pth2).differentiableAt (by norm_num)).neg.add
      ((Work.Elliptic.contDiffAt_uncurry_slice_fst
          (Work.Spaces.pth (fun z θ' => Real.tan θ' * Q z θ')) z θ h1T).differentiableAt
        (by norm_num))).sub (hsliceQ.const_mul 6)
  -- the `bslOp α Q = -α²D_z²Q - 5αD_zQ + Lzero Q` identity on a neighbourhood
  have hev : (fun p : ℝ × ℝ => Work.Elliptic.bslOp α Q p.1 p.2)
      =ᶠ[𝓝 (z, θ)] (fun p : ℝ × ℝ => -(α ^ 2) * Work.Spaces.DzIter 2 Q p.1 p.2
        - (5 * α) * Work.Spaces.Dz Q p.1 p.2 + Work.Elliptic.Lzero Q p.1 p.2) := by
    filter_upwards [(hQ.eventually (by decide : (3 : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞))).mono
      (fun y hy => hy.of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num))] with p hp
    exact bslOp_eq_Dz_form hp
  have hL : Work.Elliptic.bslOp α (Work.Spaces.Dz Q) z θ
      = -(α ^ 2) * Work.Spaces.DzIter 3 Q z θ - (5 * α) * Work.Spaces.DzIter 2 Q z θ
        + Work.Elliptic.Lzero (Work.Spaces.Dz Q) z θ := by
    have := bslOp_eq_Dz_form (α := α) h2Dz
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using this
  have hR : Work.Spaces.Dz (Work.Elliptic.bslOp α Q) z θ
      = -(α ^ 2) * Work.Spaces.DzIter 3 Q z θ - (5 * α) * Work.Spaces.DzIter 2 Q z θ
        + Work.Spaces.Dz (Work.Elliptic.Lzero Q) z θ := by
    rw [Dz_congr_of_eventuallyEq (f := Work.Elliptic.bslOp α Q)
      (g := fun z θ => -(α ^ 2) * Work.Spaces.DzIter 2 Q z θ
        - (5 * α) * Work.Spaces.Dz Q z θ + Work.Elliptic.Lzero Q z θ) hev]
    exact Dz_lin_expand hd1 hd2 hd3
  have hcomm : Work.Elliptic.Lzero (Work.Spaces.Dz Q) z θ
      = Work.Spaces.Dz (Work.Elliptic.Lzero Q) z θ := Lzero_Dz_comm hQ hcos
  rw [hL, hR, hcomm]

end Work.FTS_StreamBdry.SB3.P2Aux
end
end
-- ===== merged: Submission.Work.Spaces.pz_mixed_mul_le_4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## The arithmetic of the explicit constant -/

/-- The binomial constant of the Leibniz rule is at most `257` as soon as `k,j ≤ 4`:
`1 + ∑_{a≤j} ∑_{c≤k} C(j,a) C(k,c) = 1 + 2^j·2^k ≤ 1 + 2^4·2^4 = 257`. -/
lemma one_add_choose_double_sum_le (k j : ℕ) (hk : k ≤ 4) (hj : j ≤ 4) :
    (1 : ℝ) + ∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (k + 1),
      (j.choose a : ℝ) * (k.choose c : ℝ) ≤ 257 := by
  have h1 : (∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)) = (2 : ℝ) ^ j := by
    rw [← Nat.cast_sum, Nat.sum_range_choose j, Nat.cast_pow]; norm_num
  have h2 : (∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ)) = (2 : ℝ) ^ k := by
    rw [← Nat.cast_sum, Nat.sum_range_choose k, Nat.cast_pow]; norm_num
  rw [← Finset.sum_mul_sum, h1, h2]
  have h2j : (2 : ℝ) ^ j ≤ 16 := by
    calc (2 : ℝ) ^ j ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hj
      _ = 16 := by norm_num
  have h2k : (2 : ℝ) ^ k ≤ 16 := by
    calc (2 : ℝ) ^ k ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hk
      _ = 16 := by norm_num
  nlinarith [mul_le_mul h2j h2k (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)
    (by norm_num : (0 : ℝ) ≤ 16)]

/-! ## The Leibniz bound with the explicit constant `257` -/


end Work.Spaces
end
end

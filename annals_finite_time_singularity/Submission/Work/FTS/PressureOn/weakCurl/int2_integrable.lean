import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.Physical.Clock.integrableOn_A =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Asymptotics
open scoped Topology ENNReal

namespace Work.FTS.Physical.Clock

/-- **The modulated amplitude is antitone.**  The function `τ ↦ A τ · e^{τ/2}` is antitone on
`[0,∞)`: its derivative is `A τ · e^{τ/2} · (1/2 - (1 + μ τ)) ≤ 0` by the lower modulation bound
`1 ≤ 2 (1 + μ τ)`.  This is the integrated form of `A' = -(1+μ) A` with `1 + μ ≥ 1/2`. -/
private theorem antitoneOn_A_mul_exp (C : Work.FTS.Physical.PhysClock) :
    AntitoneOn (fun τ : ℝ => C.A τ * Real.exp (τ / 2)) (Set.Ici 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (D := Set.Ici 0) (convex_Ici 0)
    (f := fun τ : ℝ => C.A τ * Real.exp (τ / 2))
    (f' := fun x : ℝ => (-(1 + C.mu x) * C.A x) * Real.exp (x / 2)
      + C.A x * (Real.exp (x / 2) * (1 / 2))) ?_ ?_ ?_
  · exact C.hAcont.mul (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn
  · intro x hx
    have hx0 : 0 ≤ x := le_of_lt (mem_Ioi.mp (by simpa only [interior_Ici] using hx))
    exact ((C.hAderiv x hx0).mul (((hasDerivAt_id x).div_const 2).exp)).hasDerivWithinAt
  · intro x hx
    have hx0 : 0 ≤ x := le_of_lt (mem_Ioi.mp (by simpa only [interior_Ici] using hx))
    have hA0 : 0 ≤ C.A x := (C.hApos x hx0).le
    have hE : 0 ≤ Real.exp (x / 2) := (Real.exp_pos _).le
    have hm : 0 ≤ 1 / 2 + C.mu x := by linarith [C.hmu_lo x hx0]
    have hkey : (-(1 + C.mu x) * C.A x) * Real.exp (x / 2)
        + C.A x * (Real.exp (x / 2) * (1 / 2))
        = -(C.A x * Real.exp (x / 2) * (1 / 2 + C.mu x)) := by ring
    rw [hkey]
    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg hA0 hE) hm)



end Work.FTS.Physical.Clock
end
-- ===== merged: Submission.Work.FTS.Physical.Pressure.contDiffOn_radialPrim =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.Physical.Pressure

/-!
# Joint `C¹` regularity of the radial primitive

`Work.FTS.Physical.radialPrim G x t = ∫ s in 0..1, ⟪G (s • x) t, x⟫` is the explicit primitive of a
curl-free field used to produce the pressure of the reconstructed Euler solution.  This module
proves that it is jointly `C¹` in `(x,t)` as soon as `G` is jointly `C¹`.

The proof is differentiation under the integral sign: for a jointly `C¹` integrand `K` on a product
`u ×ˢ s` (with `u ∋ [a,b]` and `s` open) the parametric integral `x ↦ ∫ t in a..b, K t x` is `C¹`
on `s`, with derivative `x ↦ ∫ t in a..b, ∂₂K(t,x)`.  The two ingredients are

* `hasFDerivAt_intervalIntegral` — the derivative exists and is the integral of the derivative
  (Mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le''`, with the domination bound coming
  from the compactness of `[a,b] × closedBall x₀ ρ`);
* `continuousOn_intervalIntegral_fderiv` — that derivative is continuous in `x`, by dominated
  convergence along the compact strip.

They are assembled in `contDiffOn_intervalIntegral`, and instantiated at `K s (x,t) = ⟪G(s•x,t),x⟫`.

The final theorem is stated with the integral written out, because `Work.FTS.Physical.radialPrim` is
*defined* in the umbrella module `Submission.Work.FTS.Physical.Pressure`, which imports the present
module (it re-exports this lemma as `Work.FTS.Physical.contDiffOn_radialPrim`); importing it here
would create an import cycle.  The two statements are definitionally equal, since `radialPrim` is
definitionally `∫ s in 0..1, ⟪G (s • x) t, x⟫`, so consumers may use either phrasing.
-/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

section General

variable [ProperSpace X]






end General

/-! ## The radial primitive of a joint `C¹` field -/



end Work.FTS.Physical.Pressure
end
-- ===== merged: Submission.Work.FTS.Physical.Pressure.hasFDerivAt_radialPrim =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Topology

set_option autoImplicit false

namespace Work.FTS.Physical.Pressure



end Work.FTS.Physical.Pressure
end
-- ===== merged: Submission.Work.FTS.Physical.Pressure.vorticity_materialAccel_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity
open scoped Matrix

set_option autoImplicit false

namespace Work.FTS.Physical.Pressure



end Work.FTS.Physical.Pressure
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.cocompact_bound_vec =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A continuous `ℝ³ → ℝ³` map vanishing at infinity is bounded

This is the vector-valued counterpart of `Work.FTS.PressureOn.Auxiliary.tendsto_cocompact_bound_scalar`:
if `Φ : ℝ³ → ℝ³` is continuous and `Φ → 0` along the cocompact filter (i.e. `Φ` *vanishes at
infinity*), then `‖Φ‖` is bounded on all of `ℝ³`.

The argument has nothing to do with the codomain being a normed space: from `hΦ0` the set
`{x | ‖Φ x‖ < 1}` is a neighbourhood of infinity, so its complement is contained in a compact
`K`; `‖Φ‖` is bounded on the compact `K` by `IsCompact.exists_bound_of_continuousOn`, and the
two bounds are combined with `max`.
-/

namespace Work.FTS.PressureOn.Auxiliary

theorem cocompact_bound_vec {Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hΦ : Continuous Φ)
    (hΦ0 : Filter.Tendsto Φ (Filter.cocompact (EuclideanSpace ℝ (Fin 3))) (nhds 0)) :
    ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C := by
  -- `hΦ0` gives that the preimage of the unit ball around `0` is a neighbourhood of infinity:
  -- its complement is contained in a compact set `K`.
  have hmem : {x : EuclideanSpace ℝ (Fin 3) | ‖Φ x‖ < 1}
      ∈ Filter.cocompact (EuclideanSpace ℝ (Fin 3)) := by
    have h := hΦ0 (Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin 3)) one_pos)
    rw [Filter.mem_map] at h
    rwa [show Φ ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1
        = {x : EuclideanSpace ℝ (Fin 3) | ‖Φ x‖ < 1} from by
      ext x; simp [Metric.mem_ball]] at h
  obtain ⟨K, hKc, hKsub⟩ := Filter.mem_cocompact.1 hmem
  -- `‖Φ‖` is bounded on the compact set `K` by continuity.
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hΦ.continuousOn
  refine ⟨max M 1, fun x => ?_⟩
  by_cases hx : x ∈ K
  · exact (hM x hx).trans (le_max_left _ _)
  · have h := hKsub (by simpa using hx)
    exact (le_of_lt h).trans (le_max_right _ _)

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.convolution_laplaceTraceVec_comm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter
open scoped Topology Pointwise Convolution
open FiniteTimeSingularity

namespace Work.FTS.PressureOn.Auxiliary

/-- **Differentiation under the convolution integral.**  For a smooth compactly supported
`ρ : ℝ³ → ℝ` and a `C¹` map `V : ℝ³ → H` into a normed space `H` over `ℝ`,

  `(d/dx) ∫ t, ρ t • V (x - t) = ∫ t, ρ t • fderiv ℝ V (x - t)`.

The derivative of the convolution therefore falls on the convolved factor; `ρ` only has to be
continuous and compactly supported for the domination of the integrand. -/
private theorem hasFDerivAt_convolution_smul {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : EuclideanSpace ℝ (Fin 3) → ℝ) (V : EuclideanSpace ℝ (Fin 3) → H)
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (hV : ContDiff ℝ 1 V)
    (x₀ : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (fun y => ∫ t, ρ t • V (y - t))
      (∫ t, ρ t • fderiv ℝ V (x₀ - t)) x₀ := by
  have h3 : ∀ a x, HasFDerivAt (fun y => V (y - a)) (fderiv ℝ V (x - a)) x := fun a x => by
    simpa [Function.comp_def, Pi.sub_apply] using
      (hV.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub (hasFDerivAt_const a x))
  obtain ⟨C₀, hC₀⟩ : ∃ C, ∀ z ∈ ((-tsupport ρ) + closedBall x₀ 1), ‖fderiv ℝ V z‖ ≤ C :=
    ((hρc.isCompact.neg.add (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn
      (hV.continuous_fderiv one_ne_zero).continuousOn)
  set C := max C₀ 0 with hCdef
  have hC : ∀ z ∈ ((-tsupport ρ) + closedBall x₀ 1), ‖fderiv ℝ V z‖ ≤ C :=
    fun z hz => le_trans (hC₀ z hz) (le_max_left _ _)
  have hC0 : 0 ≤ C := le_max_right _ _
  have hbound : ∀ a : EuclideanSpace ℝ (Fin 3), ∀ x ∈ ball x₀ 1,
      ‖ρ a • fderiv ℝ V (x - a)‖ ≤ C * ‖ρ a‖ := by
    intro a x hx
    rw [norm_smul]
    by_cases ha : a ∈ tsupport ρ
    · have hz : x - a ∈ ((-tsupport ρ) + closedBall x₀ 1) := by
        refine Set.mem_add.mpr ⟨-a, ?_, x, ball_subset_closedBall hx, by abel⟩
        exact Set.mem_neg.mpr (by simpa using ha)
      calc ‖ρ a‖ * ‖fderiv ℝ V (x - a)‖ ≤ ‖ρ a‖ * C :=
            mul_le_mul_of_nonneg_left (hC _ hz) (norm_nonneg _)
        _ = C * ‖ρ a‖ := by ring
    · have h0 : ρ a = 0 := by
        by_contra h
        exact ha (subset_tsupport ρ (Function.mem_support.mpr h))
      simp [h0]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball x₀ 1)
    (bound := fun a => C * ‖ρ a‖)
    (F := fun y t => ρ t • V (y - t)) (F' := fun y t => ρ t • fderiv ℝ V (y - t))
    (ball_mem_nhds x₀ zero_lt_one) ?_ ?_ ?_ (Filter.Eventually.of_forall hbound) ?_ ?_
  · exact Filter.Eventually.of_forall fun y =>
      (hρ.continuous.smul (hV.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact Continuous.integrable_of_hasCompactSupport
      (hρ.continuous.smul (hV.continuous.comp (continuous_const.sub continuous_id)))
      (hρc.smul_right (f' := fun t => V (x₀ - t)))
  · exact ((hρ.continuous.smul
      ((hV.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)))).aestronglyMeasurable
  · exact ((continuous_norm.comp hρ.continuous).integrable_of_hasCompactSupport hρc.norm).const_mul C
  · exact Filter.Eventually.of_forall fun a x _ => (h3 a x).const_smul (ρ a)

theorem convolution_laplaceTraceVec_comm (ρ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hρ : ∀ n : ℕ, ContDiff ℝ n ρ) (hρc : HasCompactSupport ρ) (hW : ∀ n : ℕ, ContDiff ℝ n W) :
    (fun x => MeasureTheory.convolution ρ (Work.FTS.PressureOn.laplaceTraceVec W)
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
      = Work.FTS.PressureOn.laplaceTraceVec
          (fun x => MeasureTheory.convolution ρ W
            (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x) := by
  -- the directional derivative fields `z ↦ ∂W(z) e i` are `C¹`
  have hVi : ∀ i : Fin 3,
      ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin 3) => fderiv ℝ W z (e i)) := fun i => by
    have h4 : ContDiff ℝ 1 (fderiv ℝ W) := (hW 2).fderiv_right (m := 1) (by norm_num)
    simpa [Function.comp_def] using
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3)) (e i)).contDiff.comp h4
  -- integrability of the `(ℝ³ →L[ℝ] ℝ³)`-valued integrand, for `integral_apply`
  have hConC : ∀ (i : Fin 3) (x : EuclideanSpace ℝ (Fin 3)),
      Integrable (fun t => ρ t • fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) => fderiv ℝ W z (e i))
        (x - t)) MeasureTheory.volume := fun i x =>
    Continuous.integrable_of_hasCompactSupport
      ((hρ 1).continuous.smul ((hVi i).continuous_fderiv one_ne_zero |>.comp (continuous_const.sub continuous_id)))
      (hρc.smul_right (f' := fun t => fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ W z (e i)) (x - t)))
  -- integrability of the vector-valued integrand, for the sum/integral exchange
  have hCon : ∀ (i : Fin 3) (x : EuclideanSpace ℝ (Fin 3)),
      Integrable (fun t => ρ t • (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ W z (e i)) (x - t) (e i))) MeasureTheory.volume := fun i x =>
    Continuous.integrable_of_hasCompactSupport
      ((hρ 1).continuous.smul (((hVi i).continuous_fderiv one_ne_zero |>.comp
        (continuous_const.sub continuous_id)).clm_apply continuous_const))
      (hρc.smul_right (f' := fun t => fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ W z (e i)) (x - t) (e i)))
  funext x
  rw [MeasureTheory.convolution_lsmul]
  have hWa : (fun y => MeasureTheory.convolution ρ W
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume y)
      = fun y => ∫ t, ρ t • W (y - t) := by
    funext y
    rw [MeasureTheory.convolution_lsmul]
  rw [hWa]
  -- the `i`-th diagonal second derivative of the convolution
  have key2 : ∀ i : Fin 3,
      fderiv ℝ (fun w => fderiv ℝ (fun y => ∫ t, ρ t • W (y - t)) w (e i)) x (e i)
        = ∫ t, ρ t • (fderiv ℝ (fun z => fderiv ℝ W z (e i)) (x - t) (e i)) := by
    intro i
    have h1 : ∀ w, fderiv ℝ (fun y => ∫ t, ρ t • W (y - t)) w
        = ∫ t, ρ t • fderiv ℝ W (w - t) :=
      fun w => (hasFDerivAt_convolution_smul ρ W hρc (hρ 1) (hW 1) w).fderiv
    have hint1 : ∀ w, Integrable (fun t => ρ t • fderiv ℝ W (w - t)) MeasureTheory.volume := by
      intro w
      exact Continuous.integrable_of_hasCompactSupport
        ((hρ 1).continuous.smul (((hW 1).continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)))
        (hρc.smul_right (f' := fun t => fderiv ℝ W (w - t)))
    have h2 : (fun w => fderiv ℝ (fun y => ∫ t, ρ t • W (y - t)) w (e i))
        = fun w => ∫ t, ρ t • (fderiv ℝ W (w - t) (e i)) := by
      funext w
      rw [h1 w, ContinuousLinearMap.integral_apply (hint1 w)]
      simp only [smul_apply]
    have hf := (hasFDerivAt_convolution_smul ρ (fun z : EuclideanSpace ℝ (Fin 3) => fderiv ℝ W z (e i))
        hρc (hρ 1) (hVi i) x).fderiv
    rw [h2, hf, ContinuousLinearMap.integral_apply (hConC i x)]
    simp only [smul_apply]
  have hR2 : Work.FTS.PressureOn.laplaceTraceVec (fun y => ∫ t, ρ t • W (y - t)) x
      = ∑ i : Fin 3, ∫ t, ρ t • (fderiv ℝ (fun z => fderiv ℝ W z (e i)) (x - t) (e i)) := by
    simp only [Work.FTS.PressureOn.laplaceTraceVec]
    exact Finset.sum_congr rfl fun i _ => key2 i
  have hL2 : ∫ t, ρ t • Work.FTS.PressureOn.laplaceTraceVec W (x - t)
      = ∑ i : Fin 3, ∫ t, ρ t • (fderiv ℝ (fun z => fderiv ℝ W z (e i)) (x - t) (e i)) := by
    have hsplit : (fun t => ρ t • Work.FTS.PressureOn.laplaceTraceVec W (x - t))
        = fun t => ∑ i : Fin 3, ρ t • (fderiv ℝ (fun z => fderiv ℝ W z (e i)) (x - t) (e i)) := by
      funext t
      simp only [Work.FTS.PressureOn.laplaceTraceVec, Finset.smul_sum]
    rw [hsplit, MeasureTheory.integral_finsetSum]
    exact fun i _ => hCon i x
  rw [hR2, hL2]

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.curlCurl_apply =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

/-- The coordinate form of the identity.  `A i k` is the vector `S i k` of the main statement,
written in coordinates, so that `crossProduct` (which acts on `Fin 3 → ℝ`) applies directly.

For a tensor symmetric in its first two indices the `j`-th component of the "trace"
`∑ᵢ A i i` equals the trace `∑ᵢ (A i j) i` minus the `j`-th component of the double curl
`∑_k e_k × (∑_i e_i × A i k)`. -/
theorem curlCurl_core (A : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (h : ∀ i k l : Fin 3, A i k l = A k i l) (j : Fin 3) :
    (∑ i : Fin 3, A i i j)
      = (∑ i : Fin 3, A i j i)
        - ∑ k : Fin 3, crossProduct (Pi.single k (1 : ℝ) : Fin 3 → ℝ)
            (fun l : Fin 3 => ∑ i : Fin 3,
              crossProduct (Pi.single i (1 : ℝ) : Fin 3 → ℝ) (A i k) l) j := by
  fin_cases j <;>
    simp only [Fin.sum_univ_three] <;>
    simp [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Pi.single_eq_same, Pi.single_eq_of_ne] <;>
    (try ring_nf) <;>
    simp only [h 1 0, h 2 0, h 2 1] <;>
    ring

theorem curlCurl_apply (S : Fin 3 → Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hsymm : ∀ i k l : Fin 3, (S i k) l = (S k i) l) (j : Fin 3) :
    (∑ i : Fin 3, (S i i) j)
      = (∑ i : Fin 3, (S i j) i)
        - ∑ k : Fin 3, (crossProduct (WithLp.ofLp (FiniteTimeSingularity.e k))
            (fun l : Fin 3 => ∑ i : Fin 3,
              crossProduct (WithLp.ofLp (FiniteTimeSingularity.e i))
                (WithLp.ofLp (S i k)) l)) j :=
  curlCurl_core (fun i k l => (S i k).ofLp l) hsymm j

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.gradient_comp_normSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

/-- The gradient of `x ↦ F (‖x‖ ^ 2)` on `ℝ³` at `z` is `2 * F' (‖z‖ ^ 2) • innerSL ℝ z`
(i.e. the map `v ↦ 2 F'(‖z‖²) ⟪z, v⟫`).  Proved by the chain rule from
`hasStrictFDerivAt_norm_sq`. -/
theorem gradient_comp_normSq (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (z : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 3) => F (‖x‖ ^ 2)) z
      = (2 * deriv F (‖z‖ ^ 2)) • (innerSL ℝ z) := by
  -- `F` is differentiable, so `HasDerivAt F (deriv F (‖z‖²)) (‖z‖²)`.
  have hdF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hderiv : HasDerivAt F (deriv F (‖z‖ ^ 2)) (‖z‖ ^ 2) :=
    (hdF (‖z‖ ^ 2)).hasDerivAt
  -- the strict derivative of `x ↦ ‖x‖ ^ 2` at `z`.
  have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖ ^ 2)
      (2 • innerSL ℝ z) z := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  -- the chain rule.
  have h2 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 3) => F (‖x‖ ^ 2))
      ((ContinuousLinearMap.toSpanSingleton ℝ (deriv F (‖z‖ ^ 2))) ∘SL (2 • innerSL ℝ z)) z :=
    hderiv.hasFDerivAt.comp z h1
  rw [h2.fderiv]
  -- identify `toSpanSingleton ℝ c ∘SL (2 • innerSL ℝ z)` with `(2 * c) • innerSL ℝ z`.
  ext v
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply]
  ring

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.gradient_smooth_norm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

/-- For a function `u` on `ℝ³` which is `C^∞`, its gradient `∇u = (toDual ℝ ℝ³).symm ∘ fderiv ℝ u`
is again `C^∞` (in every finite order), and its pointwise norm equals the operator norm of the
Fréchet derivative `fderiv ℝ u x` (the Fréchet–Riesz isometry `toDual ℝ ℝ³`). -/
theorem gradient_smooth_norm (u : EuclideanSpace ℝ (Fin 3) → ℝ) (hu : ∀ n : ℕ, ContDiff ℝ n u) :
    (∀ n : ℕ, ContDiff ℝ n (fun x => gradient u x)) ∧
      (∀ x, ‖gradient u x‖ = ‖fderiv ℝ u x‖) := by
  constructor
  · -- `∇u = (toDual ℝ ℝ³).symm ∘ fderiv ℝ u`; the derivative of a `C^{n+1}` function is `C^n`
    -- (`contDiff_succ_iff_fderiv`), and composing with a continuous linear isometry preserves the
    -- order of smoothness.
    intro n
    have hfd : ContDiff ℝ n (fderiv ℝ u) :=
      ((contDiff_succ_iff_fderiv (𝕜 := ℝ) (f := u) (n := (n : WithTop ℕ∞))).mp
        (hu (n + 1))).2.2
    have hcomp : ContDiff ℝ n
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm ∘ (fderiv ℝ u)) :=
      (LinearIsometryEquiv.contDiff _).comp hfd
    simpa [gradient, Function.comp_def] using hcomp
  · -- `gradient` is the inverse of the linear isometry equivalence `toDual ℝ ℝ³`, hence
    -- norm-preserving.
    intro x
    exact LinearIsometryEquiv.norm_map
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm (fderiv ℝ u x)

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.integral_inner_eq_inner_integral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

/-- The inner product against a fixed vector `c` commutes with the Bochner integral: the map
`y ↦ ⟪c, y⟫` is a continuous linear functional (`innerSL ℝ c`), and for such a functional the
integral of the composition is the composition with the integral, provided the integrand is
integrable — here `ψ` is continuous with compact support.

This is the linearity of the Bochner integral against a continuous linear functional, recorded
as a standalone lemma for the pressure construction. -/
theorem integral_inner_eq_inner_integral (c : EuclideanSpace ℝ (Fin 3))
    (ψ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, inner ℝ c (ψ x) = inner ℝ c (∫ x, ψ x) := by
  have hint : MeasureTheory.Integrable ψ := hψ.integrable_of_hasCompactSupport hψc
  have h := ContinuousLinearMap.integral_comp_comm (innerSL ℝ c) hint
  simpa using h

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.normSq_hessian =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

/-- The Hessian of the radial function `x ↦ F (‖x‖ ^ 2)` on a real inner product space.

For a `C²` function `F : ℝ → ℝ` the second Fréchet derivative of `x ↦ F (‖x‖ ^ 2)` at `z`,
evaluated on the pair `(u, v)`, is

`2 * F'(‖z‖ ^ 2) * ⟪u, v⟫ + 4 * F''(‖z‖ ^ 2) * ⟪z, u⟫ * ⟪z, v⟫`.

This is the classical formula `∇²(F∘‖·‖²) = 2F'(‖z‖²) I + 4F''(‖z‖²) z zᵀ`, written in the
`fderiv`-of-`fderiv` form used by the pressure reconstruction. -/
theorem normSq_hessian_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (z u v : E) :
    (fderiv ℝ (fun w : E => fderiv ℝ (fun x : E => F (‖x‖ ^ 2)) w v) z) u
      = 2 * deriv F (‖z‖ ^ 2) * inner ℝ u v
        + 4 * deriv (deriv F) (‖z‖ ^ 2) * (inner ℝ z u * inner ℝ z v) := by
  -- the one-dimensional derivative of `deriv F` at `‖z‖ ^ 2`
  have hderiv : HasDerivAt (deriv F) (deriv (deriv F) (‖z‖ ^ 2)) (‖z‖ ^ 2) := by
    rw [hasDerivAt_iff_hasFDerivAt, toSpanSingleton_deriv]
    exact (hF.differentiable_deriv_two (‖z‖ ^ 2)).hasFDerivAt
  -- `x ↦ ‖x‖ ^ 2` has derivative `2 • innerSL ℝ x` at `x` (with the scalar pinned to `ℝ`)
  have hsq : HasFDerivAt (fun x : E => ‖x‖ ^ 2) ((2:ℝ) • innerSL ℝ z) z := by
    have h := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
    rwa [← Nat.cast_smul_eq_nsmul ℝ 2 (innerSL ℝ z)] at h
  -- the derivative of `w ↦ deriv F (‖w‖ ^ 2)`
  have hr : HasFDerivAt (fun w : E => deriv F (‖w‖ ^ 2))
      ((deriv (deriv F) (‖z‖ ^ 2)) • ((2:ℝ) • innerSL ℝ z)) z := by
    simpa only [Function.comp_def] using hderiv.comp_hasFDerivAt z hsq
  -- the gradient of `x ↦ F (‖x‖ ^ 2)`
  have hfd : ∀ w : E, fderiv ℝ (fun x : E => F (‖x‖ ^ 2)) w
      = (deriv F (‖w‖ ^ 2)) • ((2:ℝ) • innerSL ℝ w) := by
    intro w
    have hsqw : HasFDerivAt (fun x : E => ‖x‖ ^ 2) ((2:ℝ) • innerSL ℝ w) w := by
      have h := (hasStrictFDerivAt_norm_sq w).hasFDerivAt
      rwa [← Nat.cast_smul_eq_nsmul ℝ 2 (innerSL ℝ w)] at h
    have h1 : HasDerivAt F (deriv F (‖w‖ ^ 2)) (‖w‖ ^ 2) := by
      rw [hasDerivAt_iff_hasFDerivAt, toSpanSingleton_deriv]
      exact ((hF.differentiable (by norm_num)) (‖w‖ ^ 2)).hasFDerivAt
    have h2 := h1.comp_hasFDerivAt w hsqw
    rw [show fderiv ℝ (fun x : E => F (‖x‖ ^ 2)) w
          = fderiv ℝ (F ∘ fun x : E => ‖x‖ ^ 2) w from rfl]
    rw [h2.fderiv]
  -- rewrite the inner derivative as `w ↦ deriv F (‖w‖ ^ 2) * (2 * ⟪w, v⟫)`
  rw [show (fun w : E => fderiv ℝ (fun x : E => F (‖x‖ ^ 2)) w v)
        = (fun w : E => deriv F (‖w‖ ^ 2) * (2 * inner ℝ w v)) from by
      funext w
      rw [hfd w]
      simp [innerSL_apply_apply, smul_eq_mul]]
  rw [show (fun w : E => deriv F (‖w‖ ^ 2) * (2 * inner ℝ w v))
        = (fun w : E => deriv F (‖w‖ ^ 2)) * (fun w : E => 2 * inner ℝ w v) from rfl]
  -- the derivative of `w ↦ 2 * ⟪w, v⟫`
  have hb : HasFDerivAt (fun w : E => 2 * inner ℝ w v) ((2:ℝ) • innerSL ℝ v) z := by
    have hd0 : HasFDerivAt (fun w : E => inner ℝ w v) (innerSL ℝ v) z := by
      have h : (fun w : E => inner ℝ w v) = ⇑(innerSL ℝ v) := by
        funext w; rw [innerSL_apply_apply, real_inner_comm]
      rw [h]; exact (innerSL ℝ v).hasFDerivAt
    simpa using hd0.const_mul (2:ℝ)
  -- product rule and evaluation
  have hprod := hr.mul hb
  rw [hprod.fderiv]
  simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, real_inner_comm u v]
  ring

theorem normSq_hessian (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (z u v : EuclideanSpace ℝ (Fin 3)) :
    (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 3) => F (‖x‖ ^ 2)) w v) z) u
      = 2 * deriv F (‖z‖ ^ 2) * inner ℝ u v
        + 4 * deriv (deriv F) (‖z‖ ^ 2) * (inner ℝ z u * inner ℝ z v) :=
  normSq_hessian_aux F hF z u v

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.Clamp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect

noncomputable section

/-- **Clamping of the time variable into `[0,S]`**: `clampt S s = max 0 (min s S)`. -/
noncomputable def clampt (S s : ℝ) : ℝ := max 0 (min s S)


theorem clampt_nonneg (S s : ℝ) : 0 ≤ clampt S s := le_max_left _ _

theorem clampt_le_max (S s : ℝ) : clampt S s ≤ max S 0 := by
  rw [clampt]
  exact max_le (le_max_right S 0) (le_trans (min_le_right s S) (le_max_left S 0))

theorem clampt_mem_Icc {S : ℝ} (hS : 0 ≤ S) (s : ℝ) : clampt S s ∈ Set.Icc (0 : ℝ) S := by
  refine ⟨clampt_nonneg S s, ?_⟩
  have h := clampt_le_max S s
  rwa [max_eq_left hS] at h

theorem clampt_eq_self_of_mem {S s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) S) : clampt S s = s := by
  rw [clampt, min_eq_left hs.2, max_eq_right hs.1]


/-- `clampt S` is `1`-Lipschitz. -/
theorem lipschitzWith_clampt (S : ℝ) : LipschitzWith 1 (clampt S) := by
  have h1 : LipschitzWith 1 fun s : ℝ => min s S := LipschitzWith.min_const LipschitzWith.id S
  have h2 : LipschitzWith 1 fun s : ℝ => max 0 (min s S) := LipschitzWith.const_max h1 0
  change LipschitzWith 1 fun s : ℝ => max 0 (min s S)
  exact h2

/-- `|clampt S s − clampt S t| ≤ |s − t|`. -/
theorem abs_clampt_sub_le (S s t : ℝ) : |clampt S s - clampt S t| ≤ |s - t| := by
  have h : dist (clampt S s) (clampt S t) ≤ 1 * dist s t :=
    (lipschitzWith_clampt S).dist_le_mul s t
  simpa [Real.dist_eq] using h


/-- Near an interior time the clamp is the identity, as an eventual equality. -/
theorem eventuallyEq_clampt {S t : ℝ} (ht : t ∈ Set.Ioo 0 S) :
    (fun s : ℝ => clampt S s) =ᶠ[𝓝 t] id := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact clampt_eq_self_of_mem (Set.Ioo_subset_Icc_self hs)

/-- Near an interior time the clamp is the identity, within the closed right filter. -/
theorem eventuallyEq_clampt_Ici {S t : ℝ} (ht : t ∈ Set.Ioo 0 S) :
    (fun s : ℝ => clampt S s) =ᶠ[𝓝[Set.Ici t] t] id := by
  filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds ht)] with s hs
  exact clampt_eq_self_of_mem (Set.Ioo_subset_Icc_self hs)

/-- **The clamped time field**: `v x s` for `s ∈ [0,S]`, extended constantly outside. -/
noncomputable def extendTime (v : R3 → ℝ → R3) (S : ℝ) : R3 → ℝ → R3 :=
  fun x s => v x (clampt S s)

theorem extendTime_apply (v : R3 → ℝ → R3) (S : ℝ) (x : R3) (s : ℝ) :
    extendTime v S x s = v x (clampt S s) := rfl


/-- The clamped field agrees with the original near every interior time. -/
theorem eventuallyEq_extendTime {v : R3 → ℝ → R3} {S t : ℝ} (ht : t ∈ Set.Ioo 0 S) (x : R3) :
    (fun s : ℝ => extendTime v S x s) =ᶠ[𝓝 t] (fun s => v x s) := by
  filter_upwards [eventuallyEq_clampt ht] with s hs
  rw [extendTime_apply, hs]; rfl

theorem eventuallyEq_extendTime_Ici {v : R3 → ℝ → R3} {S t : ℝ} (ht : t ∈ Set.Ioo 0 S) (x : R3) :
    (fun s : ℝ => extendTime v S x s) =ᶠ[𝓝[Set.Ici t] t] (fun s => v x s) := by
  filter_upwards [eventuallyEq_clampt_Ici ht] with s hs
  rw [extendTime_apply, hs]; rfl

/-- The time derivative of the clamped field is the time derivative of the original at an interior
time. -/
theorem timeDeriv_extendTime {v : R3 → ℝ → R3} {S t : ℝ} (ht : t ∈ Set.Ioo 0 S) (x : R3) :
    FiniteTimeSingularity.timeDeriv (extendTime v S) x t
      = FiniteTimeSingularity.timeDeriv v x t :=
  (eventuallyEq_extendTime ht x).deriv_eq



end

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.contDiffOn_prod_Ico_of_Icc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

theorem contDiffOn_prod_Ico_of_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ} {T : ℝ} {g : E × ℝ → F}
    (h : ∀ S ∈ Set.Ioo 0 T, ContDiffOn ℝ n g (Set.univ ×ˢ Set.Icc 0 S)) :
    ContDiffOn ℝ n g (Set.univ ×ˢ Set.Ico 0 T) := by
  refine contDiffOn_of_locally_contDiffOn ?_
  rintro ⟨y, t⟩ ⟨-, ht⟩
  obtain ⟨ht0, htT⟩ := ht
  -- pick an intermediate cutoff `S` with `t < S < T`
  obtain ⟨S, htS, hST⟩ : ∃ S : ℝ, t < S ∧ S < T := ⟨(t + T) / 2, by linarith, by linarith⟩
  have hS0 : 0 < S := lt_of_le_of_lt ht0 htS
  refine ⟨Set.univ ×ˢ Set.Ioo (-1) S, isOpen_univ.prod isOpen_Ioo, ⟨trivial, ?_⟩, ?_⟩
  · exact ⟨by linarith, htS⟩
  · refine (h S ⟨hS0, hST⟩).mono ?_
    rintro ⟨a, b⟩ ⟨⟨-, hb⟩, ⟨-, hb'⟩⟩
    exact ⟨trivial, ⟨hb.1, le_of_lt hb'.2⟩⟩

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.contDiffWithinAt_one_of_hasFDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

theorem contDiffWithinAt_one_of_hasFDerivAt {f : Work.FTS.PressureOn.R3 × ℝ → ℝ}
    {f' : Work.FTS.PressureOn.R3 × ℝ → (Work.FTS.PressureOn.R3 × ℝ →L[ℝ] ℝ)}
    {s : Set (Work.FTS.PressureOn.R3 × ℝ)} {z : Work.FTS.PressureOn.R3 × ℝ} (hs : s ∈ nhds z)
    (h : ∀ y ∈ s, HasFDerivAt f (f' y) y) (hc : ContinuousOn f' s) :
    ContDiffWithinAt ℝ 1 f s z := by
  -- `s` is a neighbourhood of `z`, so `C¹` at `z` implies `C¹` within `s` at `z`; and
  -- `C¹` at a point is exactly the existence of a derivative field that is continuous on a
  -- neighbourhood of the point and differentiates `f` at every point of it.
  exact ((contDiffAt_one_iff (𝕜 := ℝ) (f := f) (x := z)).mpr ⟨f', s, hs, hc, h⟩).contDiffWithinAt

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.contDiff_slice_of_isContDiffHolderOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

theorem contDiff_slice_of_isContDiffHolderOn {α : NNReal}
    {v : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {S τ : ℝ}
    (hstrip : IsContDiffHolderOn ℝ α v.uncurry (Set.univ ×ˢ Set.Icc 0 S))
    (hτ : τ ∈ Set.Icc 0 S) : ContDiff ℝ 1 (v · τ) := by
  -- The slice `x ↦ v x τ` is the composition of `v.uncurry` with the embedding
  -- `x ↦ (x, τ)`, which maps `univ` into the strip `univ ×ˢ Icc 0 S`.
  have h : ContDiffOn ℝ 1 (fun x : Work.FTS.PressureOn.R3 => (x, τ)) Set.univ := by fun_prop
  have h2 : ContDiffOn ℝ 1 (fun x : Work.FTS.PressureOn.R3 => v.uncurry (x, τ)) Set.univ :=
    hstrip.1.comp h (by intro x _; exact ⟨trivial, hτ⟩)
  rw [contDiffOn_univ] at h2
  exact h2

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.hasDerivAt_of_hasDerivWithinAt_Ici =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

theorem hasDerivAt_of_hasDerivWithinAt_Ici {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {g : ℝ → E} {c : ℝ → E} {T t : ℝ}
    (ht : t ∈ Set.Ioo 0 T) (hg : ContinuousOn g (Set.Icc 0 T))
    (hc : ContinuousOn c (Set.Ico 0 T))
    (hderiv : ∀ s ∈ Set.Ico 0 T, HasDerivWithinAt g (c s) (Set.Ici s) s) :
    HasDerivAt g (c t) t := by
  obtain ⟨ht0, htT⟩ := ht
  -- Work on a closed interval `[a, b] ⊆ (0, T)` containing `t` in its interior.
  let a : ℝ := t / 2
  let b : ℝ := (t + T) / 2
  have ha0 : 0 < a := by dsimp only [a]; linarith
  have hat : a < t := by dsimp only [a]; linarith
  have htb : t < b := by dsimp only [b]; linarith
  have hbT : b < T := by dsimp only [b]; linarith
  -- The primitive of `c`, which is differentiable on `(0, T)` with derivative `c`.
  let P : ℝ → E := fun s => ∫ u in (0 : ℝ)..s, c u
  have hcIoo : ContinuousOn c (Set.Ioo 0 T) := hc.mono fun x hx => ⟨le_of_lt hx.1, hx.2⟩
  have hcAt : ∀ x ∈ Set.Ioo 0 T, ContinuousAt c x :=
    fun x hx => isOpen_Ioo.continuousOn_iff.mp hcIoo hx
  have hPderiv : ∀ x ∈ Set.Ioo 0 T, HasDerivAt P (c x) x := by
    intro x hx
    have hint : IntervalIntegrable c MeasureTheory.volume (0 : ℝ) x :=
      ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hx.1)
        (hc.mono fun y hy => ⟨hy.1, lt_of_le_of_lt hy.2 hx.2⟩)
    have hmeas : StronglyMeasurableAtFilter c (nhds x) MeasureTheory.volume :=
      (hcIoo.stronglyMeasurableAtFilter isOpen_Ioo) x hx
    exact intervalIntegral.integral_hasDerivAt_right hint hmeas (hcAt x hx)
  -- Hence `g - P` has vanishing right derivative on `[a, b)`.
  have hFderiv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt (g - P) 0 (Set.Ici x) x := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo 0 T :=
      ⟨lt_of_lt_of_le ha0 hx.1, lt_of_lt_of_le hx.2 (le_of_lt hbT)⟩
    have hgx : HasDerivWithinAt g (c x) (Set.Ici x) x :=
      hderiv x ⟨le_of_lt (lt_of_lt_of_le ha0 hx.1), lt_of_lt_of_le hx.2 (le_of_lt hbT)⟩
    have hPx : HasDerivWithinAt P (c x) (Set.Ici x) x := (hPderiv x hxIoo).hasDerivWithinAt
    simpa only [sub_self] using hgx.sub hPx
  have hPcont : ContinuousOn P (Set.Icc a b) := by
    intro x hx
    exact ((hPderiv x ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt hx.2 hbT⟩).continuousAt).continuousWithinAt
  have hFcont : ContinuousOn (g - P) (Set.Icc a b) :=
    (hg.mono fun x hx => ⟨le_trans (le_of_lt ha0) hx.1, le_trans hx.2 (le_of_lt hbT)⟩).sub hPcont
  -- So `g - P` is constant on `[a, b]`.
  have hseg : ∀ x ∈ Set.Icc a b, ‖(g - P) x - (g - P) a‖ ≤ 0 * (x - a) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment hFcont hFderiv (fun x hx => by simp)
  have hconst : ∀ x ∈ Set.Icc a b, g x - P x = g a - P a := by
    intro x hx
    have h := hseg x hx
    simp only [Pi.sub_apply, zero_mul] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  -- Near `t`, `g` is a translate of `P`, hence differentiable with derivative `c t`.
  have hPt : HasDerivAt P (c t) t := hPderiv t ⟨ht0, htT⟩
  have hmain : HasDerivAt (fun x => (g a - P a) + P x) (c t) t := hPt.const_add (g a - P a)
  refine hmain.congr_of_eventuallyEq ?_
  have hmem : Set.Ioo a b ∈ nhds t := IsOpen.mem_nhds isOpen_Ioo ⟨hat, htb⟩
  filter_upwards [hmem] with x hx
  exact sub_eq_iff_eq_add.mp (hconst x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.hasDerivAt_slice_of_hasFDerivAt_uncurry =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

theorem hasDerivAt_slice_of_hasFDerivAt_uncurry {v : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {x : Work.FTS.PressureOn.R3} {t : ℝ}
    (h : HasFDerivAt (Function.uncurry v) (fderiv ℝ (Function.uncurry v) (x, t)) (x, t)) :
    HasDerivAt (fun s => v x s) ((fderiv ℝ (Function.uncurry v) (x, t)) (0, 1)) t := by
  have hslice : HasFDerivAt (fun s : ℝ => (x, s))
      (ContinuousLinearMap.inr ℝ Work.FTS.PressureOn.R3 ℝ) t :=
    hasFDerivAt_prodMk_right x t
  have hcomp := h.comp t hslice
  have hd := hcomp.hasDerivAt
  simp only [ContinuousLinearMap.comp_apply] at hd
  exact hd

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.hasFDerivAt_uncurry_of_partials_corrected =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter Asymptotics
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect

/-- **The corrected form of `hasFDerivAt_uncurry_of_partials`.**  If

* `y ↦ q y t` is differentiable at `x` with derivative `L`;
* `s ↦ q x s` is differentiable at `t` with derivative `c`;
* `s ↦ q p.1 s` is differentiable for `p` in a *neighbourhood of `(x,t)` in the product space*,
  with derivative `deriv (fun s' => q p.1 s') p.2`;
* that derivative function is continuous at `(x,t)`,

then the uncurried map `p ↦ q p.1 p.2` is differentiable at `(x,t)` with derivative
`L ∘ fst + smulRight snd c`. -/
theorem hasFDerivAt_uncurry_of_partials'
    {q : R3 → ℝ → ℝ} {x : R3} {t : ℝ} {L : R3 →L[ℝ] ℝ} {c : ℝ}
    (hx : HasFDerivAt (fun y => q y t) L x) (ht : HasDerivAt (fun s => q x s) c t)
    (h2 : ∀ᶠ p in nhds (x, t),
      HasDerivAt (fun s' => q p.1 s') (deriv (fun s' => q p.1 s') p.2) p.2)
    (hcont2 : ContinuousAt (fun p : R3 × ℝ => deriv (fun s' => q p.1 s') p.2) (x, t)) :
    HasFDerivAt (fun p : R3 × ℝ => q p.1 p.2)
      (L.comp (ContinuousLinearMap.fst ℝ R3 ℝ)
        + ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ R3 ℝ) c) (x, t) := by
  -- * the `x`-direction: compose `hx` with the projection
  have hA : HasFDerivAt (fun p : R3 × ℝ => q p.1 t)
      (L.comp (ContinuousLinearMap.fst ℝ R3 ℝ)) (x, t) := by
    have h := hx.comp (x, t) (hasFDerivAt_fst (𝕜 := ℝ) (E := R3) (F := ℝ) (p := (x, t)))
    simpa [Function.comp_def] using h
  have hAlo : (fun p : R3 × ℝ => q p.1 t - q x t - L (p.1 - x))
      =o[nhds (x, t)] (fun p : R3 × ℝ => p - (x, t)) := by
    have h := hasFDerivAt_iff_isLittleO.mp hA
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', Prod.fst_sub] using h
  -- * the `t`-direction: mean value theorem on a *uniform* box around `(x,t)`
  have hBlo : (fun p : R3 × ℝ => q p.1 p.2 - q p.1 t - (p.2 - t) * c)
      =o[nhds (x, t)] (fun p : R3 × ℝ => p - (x, t)) := by
    refine IsLittleO.of_bound fun ε hε => ?_
    -- a uniform differentiability box for the slices
    obtain ⟨δ₁, hδ₁0, hδ₁⟩ := Metric.mem_nhds_iff.mp h2
    -- a uniform continuity radius for the derivative of the slices
    obtain ⟨δ₂, hδ₂0, hδ₂raw⟩ := (Metric.continuousAt_iff.mp hcont2) ε hε
    have hδ₂ : ∀ p : R3 × ℝ, dist p (x, t) < δ₂ →
        dist (deriv (fun s' => q p.1 s') p.2) c < ε := by
      intro p hp
      have := hδ₂raw hp
      simpa [ht.deriv] using this
    have hδmin : 0 < min δ₁ δ₂ := lt_min hδ₁0 hδ₂0
    filter_upwards [Metric.ball_mem_nhds (x, t) (ε := min δ₁ δ₂) hδmin] with p hp
    rw [Metric.mem_ball, Prod.dist_eq] at hp
    have hp1 : dist p.1 x < min δ₁ δ₂ := lt_of_le_of_lt (le_max_left _ _) hp
    have hp2 : dist p.2 t < min δ₁ δ₂ := lt_of_le_of_lt (le_max_right _ _) hp
    have hp1₁ : dist p.1 x < δ₁ := lt_of_lt_of_le hp1 (min_le_left _ _)
    have hp1₂ : dist p.1 x < δ₂ := lt_of_lt_of_le hp1 (min_le_right _ _)
    have hmem₁ : ∀ u : ℝ, |u - t| < min δ₁ δ₂ → dist (p.1, u) (x, t) < δ₁ := by
      intro u hu
      rw [Prod.dist_eq]
      exact max_lt hp1₁ (by rw [Real.dist_eq]; exact lt_of_lt_of_le hu (min_le_left _ _))
    have hmem₂ : ∀ u : ℝ, |u - t| < min δ₁ δ₂ → dist (p.1, u) (x, t) < δ₂ := by
      intro u hu
      rw [Prod.dist_eq]
      exact max_lt hp1₂ (by rw [Real.dist_eq]; exact lt_of_lt_of_le hu (min_le_right _ _))
    have hmvt : ‖(q p.1 p.2 - p.2 * c) - (q p.1 t - t * c)‖ ≤ ε * ‖p.2 - t‖ := by
      refine Convex.norm_image_sub_le_of_norm_deriv_le
        (f := fun u : ℝ => q p.1 u - u * c)
        (s := Set.Ioo (t - min δ₁ δ₂) (t + min δ₁ δ₂)) (x := t) (y := p.2) (C := ε) ?_ ?_
        (convex_Ioo _ _) ?_ ?_
      · -- differentiability of the slice, shifted by `c * ·`, on the whole interval
        intro u hu
        rw [Set.mem_Ioo] at hu
        have hu' : |u - t| < min δ₁ δ₂ := by
          rw [abs_lt]; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
        have hm : (p.1, u) ∈ Metric.ball (x, t) δ₁ := by
          rw [Metric.mem_ball]; exact hmem₁ u hu'
        exact ((hδ₁ hm).sub ((hasDerivAt_id u).mul_const c)).differentiableAt
      · -- bound on the derivative on the interval
        intro u hu
        rw [Set.mem_Ioo] at hu
        have hu' : |u - t| < min δ₁ δ₂ := by
          rw [abs_lt]; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
        have hm : (p.1, u) ∈ Metric.ball (x, t) δ₁ := by
          rw [Metric.mem_ball]; exact hmem₁ u hu'
        have hu1 : HasDerivAt (fun s' : ℝ => q p.1 s') (deriv (fun s' : ℝ => q p.1 s') u) u :=
          hδ₁ hm
        have hfun : (fun u' : ℝ => q p.1 u' - u' * c)
            = ((fun s' : ℝ => q p.1 s') - fun y : ℝ => y * c) := by funext u'; rfl
        have hder' : deriv ((fun s' : ℝ => q p.1 s') - fun y : ℝ => y * c) u
            = deriv (fun s' : ℝ => q p.1 s') u - c := by
          have h := (hu1.sub ((hasDerivAt_id u).mul_const c)).deriv
          simpa [id_eq] using h
        rw [hfun, hder', Real.norm_eq_abs]
        exact le_of_lt (hδ₂ ⟨p.1, u⟩ (hmem₂ u hu'))
      · exact ⟨by linarith, by linarith⟩
      · rw [Set.mem_Ioo]
        have : |p.2 - t| < min δ₁ δ₂ := by rwa [Real.dist_eq] at hp2
        obtain ⟨h1, h2'⟩ := abs_lt.mp this
        exact ⟨by linarith, by linarith⟩
    have heq : (q p.1 p.2 - p.2 * c) - (q p.1 t - t * c)
        = q p.1 p.2 - q p.1 t - (p.2 - t) * c := by ring
    rw [heq] at hmvt
    have hnorm : ‖p.2 - t‖ ≤ ‖p - (x, t)‖ := by
      calc ‖p.2 - t‖ = |p.2 - t| := Real.norm_eq_abs _
        _ = dist p.2 t := by rw [Real.dist_eq]
        _ ≤ dist p (x, t) := by rw [Prod.dist_eq]; exact le_max_right _ _
        _ = ‖p - (x, t)‖ := dist_eq_norm p (x, t)
    exact le_trans hmvt (mul_le_mul_of_nonneg_left hnorm (le_of_lt hε))
  -- * assemble the two little-o estimates
  rw [hasFDerivAt_iff_isLittleO]
  refine (hAlo.add hBlo).congr_left fun p => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
  ring

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.lamb_lipschitz_near =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

/-- **The norm bound for the cross product**: `‖a × b‖ ≤ ‖a‖ ‖b‖`.  It follows from the identity
`‖a × b‖ = ‖a‖ ‖b‖ sin ∠(a,b)` of `InnerProductGeometry.norm_ofLp_crossProduct`. -/
private lemma norm_crossVec_le (a b : R3) : ‖crossVec a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h := InnerProductGeometry.norm_ofLp_crossProduct a b
  have hsin : Real.sin (InnerProductGeometry.angle a b) ≤ 1 := Real.sin_le_one _
  have hnn : 0 ≤ ‖a‖ * ‖b‖ := mul_nonneg (norm_nonneg a) (norm_nonneg b)
  calc ‖crossVec a b‖ = ‖a‖ * ‖b‖ * Real.sin (InnerProductGeometry.angle a b) := h
    _ ≤ ‖a‖ * ‖b‖ * 1 := mul_le_mul_of_nonneg_left hsin hnn
    _ = ‖a‖ * ‖b‖ := by ring

/-- **Bilinearity of the cross product**, in the form of the difference identity
`a × b - a' × b' = (a - a') × b + a' × (b - b')`. -/
private lemma crossVec_sub_sub (a a' b b' : R3) :
    crossVec a b - crossVec a' b' = crossVec (a - a') b + crossVec a' (b - b') := by
  rw [WithLp.ext_iff]
  simp only [crossVec_apply, WithLp.ofLp_sub, WithLp.ofLp_add, map_sub]
  simp

/-- **The Lamb vector difference bound**: splitting the difference of the two cross products and
applying the norm bound to each term. -/
private lemma norm_lamb_sub_le (u ω : R3 → ℝ → R3) (y : R3) (s t : ℝ) :
    ‖lamb u ω y s - lamb u ω y t‖
      ≤ ‖u y s - u y t‖ * ‖ω y s‖ + ‖u y t‖ * ‖ω y s - ω y t‖ := by
  have h1 : lamb u ω y s = crossVec (u y s) (ω y s) := rfl
  have h2 : lamb u ω y t = crossVec (u y t) (ω y t) := rfl
  rw [h1, h2, crossVec_sub_sub]
  calc ‖crossVec (u y s - u y t) (ω y s) + crossVec (u y t) (ω y s - ω y t)‖
      ≤ ‖crossVec (u y s - u y t) (ω y s)‖ + ‖crossVec (u y t) (ω y s - ω y t)‖ :=
        norm_add_le _ _
    _ ≤ ‖u y s - u y t‖ * ‖ω y s‖ + ‖u y t‖ * ‖ω y s - ω y t‖ :=
        add_le_add (norm_crossVec_le _ _) (norm_crossVec_le _ _)

theorem lamb_lipschitz_near {u ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {t B C : ℝ}
    (hu : ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖u y s - u y t‖ ≤ C * |s - t|)
    (hω : ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖ω y s - ω y t‖ ≤ C * |s - t|)
    (hub : ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖u y s‖ ≤ B)
    (hωb : ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖ω y s‖ ≤ B) :
    ∃ C' : ℝ, ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1),
      ‖Work.FTS.PressureOn.lamb u ω y s - Work.FTS.PressureOn.lamb u ω y t‖ ≤ C' * |s - t| := by
  -- the auxiliary point `t + 1/2`, at distance `1/2 < 1` from `t`
  have hmem : t + 1 / 2 ∈ Set.Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  refine ⟨C * B + (B + C / 2) * C, fun y s hs => ?_⟩
  -- the base point `t` is controlled from the auxiliary point
  have hut : ‖u y t‖ ≤ B + C / 2 := by
    have h1 := hub y (t + 1 / 2) hmem
    have h2 : ‖u y (t + 1 / 2) - u y t‖ ≤ C / 2 := by
      calc ‖u y (t + 1 / 2) - u y t‖ ≤ C * |(t + 1 / 2) - t| := hu y (t + 1 / 2) hmem
        _ = C / 2 := by
            rw [show (t + 1 / 2) - t = 1 / 2 by ring, abs_of_pos (by norm_num)]
            ring
    calc ‖u y t‖ = ‖u y (t + 1 / 2) - (u y (t + 1 / 2) - u y t)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖u y (t + 1 / 2)‖ + ‖u y (t + 1 / 2) - u y t‖ := norm_sub_le _ _
      _ ≤ B + C / 2 := add_le_add h1 h2
  -- the two product estimates; the nonnegativity of `C * |s - t|` comes from the hypotheses
  have h1 : ‖u y s - u y t‖ * ‖ω y s‖ ≤ (C * |s - t|) * B :=
    mul_le_mul (hu y s hs) (hωb y s hs) (norm_nonneg _) (le_trans (norm_nonneg _) (hu y s hs))
  have h2 : ‖u y t‖ * ‖ω y s - ω y t‖ ≤ (B + C / 2) * (C * |s - t|) :=
    mul_le_mul hut (hω y s hs) (norm_nonneg _) (le_trans (norm_nonneg _) hut)
  calc ‖lamb u ω y s - lamb u ω y t‖
      ≤ ‖u y s - u y t‖ * ‖ω y s‖ + ‖u y t‖ * ‖ω y s - ω y t‖ := norm_lamb_sub_le u ω y s t
    _ ≤ (C * |s - t|) * B + (B + C / 2) * (C * |s - t|) := add_le_add h1 h2
    _ = (C * B + (B + C / 2) * C) * |s - t| := by ring

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.weakDiv_pair =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `weakDiv_pair` — the divergence pairing of the pair `(q, Φ)` is additive

Writing `Φ := ∂ₜu − u×ω` (here `lamb u ω`), the weak divergence identity for `Φ` is the
*difference* of the weak divergence identity for `∂ₜu` (`hdiv`, vanishing because the slices
`u · s` are divergence-free) and the weak Poisson identity for the Lamb vector (`hpois`, the
defining property of the Newtonian potential `q = pressurePotential (lamb u ω · t)`):

  `∫ ⟪∂ₜu − u×ω, ∇φ⟫ = ∫ ⟪∂ₜu, ∇φ⟫ − ∫ ⟪u×ω, ∇φ⟫ = 0 − ∫ q Δφ = −∫ q Δφ`.

The only analytic input is that both pairings against the gradient of a compactly supported smooth
test function are integrable: `∇φ` is compactly supported and continuous, so each pairing is the
product of a continuous function with a compactly supported one.
-/

open MeasureTheory Filter Set Topology

namespace Work.FTS.PressureOn.Connect

theorem weakDiv_pair {u ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {t : ℝ}
    {φ : Work.FTS.PressureOn.R3 → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ)
    (hφcs : HasCompactSupport φ)
    (hAc : Continuous fun x => Work.FTS.PressureOn.lamb u ω x t)
    (hBc : Continuous fun x => FiniteTimeSingularity.timeDeriv u x t)
    (hdiv : ∫ x, inner ℝ (FiniteTimeSingularity.timeDeriv u x t) (gradient φ x) = 0)
    (hpois : ∫ x, Work.FTS.PressureOn.pressurePotential (Work.FTS.PressureOn.lamb u ω · t) x
        * Work.FTS.PressureOn.laplaceTrace φ x
      = ∫ x, inner ℝ (Work.FTS.PressureOn.lamb u ω x t) (gradient φ x)) :
    ∫ x, inner ℝ (FiniteTimeSingularity.timeDeriv u x t
        - Work.FTS.PressureOn.lamb u ω x t) (gradient φ x)
      = -∫ x, Work.FTS.PressureOn.pressurePotential (Work.FTS.PressureOn.lamb u ω · t) x
          * Work.FTS.PressureOn.laplaceTrace φ x := by
  -- `∇φ` is continuous and compactly supported.
  have hgradcont : Continuous (fun x => gradient φ x) := by
    have h : Continuous fun x => (InnerProductSpace.toDual ℝ Work.FTS.PressureOn.R3).symm
        (fderiv ℝ φ x) :=
      (InnerProductSpace.toDual ℝ Work.FTS.PressureOn.R3).symm.continuous.comp
        ((hφ 1).continuous_fderiv (by norm_num))
    simpa [gradient, Function.comp_def] using h
  have hgradcs : HasCompactSupport (fun x => gradient φ x) := by
    have h := (hφcs.fderiv ℝ).comp_left
      (g := fun L : Work.FTS.PressureOn.R3 →L[ℝ] ℝ =>
        (InnerProductSpace.toDual ℝ Work.FTS.PressureOn.R3).symm L) (by simp)
    simpa [gradient, Function.comp_def] using h
  -- The two pairings with `∇φ` are continuous with compact support, hence integrable.
  have hcsA : HasCompactSupport
      (fun x => inner ℝ (FiniteTimeSingularity.timeDeriv u x t) (gradient φ x)) :=
    hgradcs.mono fun x hx => by
      rw [Function.mem_support] at hx ⊢
      intro hg
      exact hx (by simp [hg])
  have hcsB : HasCompactSupport
      (fun x => inner ℝ (Work.FTS.PressureOn.lamb u ω x t) (gradient φ x)) :=
    hgradcs.mono fun x hx => by
      rw [Function.mem_support] at hx ⊢
      intro hg
      exact hx (by simp [hg])
  have hA : Integrable
      (fun x => inner ℝ (FiniteTimeSingularity.timeDeriv u x t) (gradient φ x)) :=
    (hBc.inner hgradcont).integrable_of_hasCompactSupport hcsA
  have hB : Integrable
      (fun x => inner ℝ (Work.FTS.PressureOn.lamb u ω x t) (gradient φ x)) :=
    (hAc.inner hgradcont).integrable_of_hasCompactSupport hcsB
  -- Split the integral of the difference.
  have hsub : (∫ x, inner ℝ (FiniteTimeSingularity.timeDeriv u x t
        - Work.FTS.PressureOn.lamb u ω x t) (gradient φ x))
      = (∫ x, inner ℝ (FiniteTimeSingularity.timeDeriv u x t) (gradient φ x))
        - (∫ x, inner ℝ (Work.FTS.PressureOn.lamb u ω x t) (gradient φ x)) := by
    rw [← integral_sub hA hB]
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [inner_sub_left]
  rw [hsub, hdiv, hpois]
  ring

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.CurlGrad.fderiv_normed_convolution_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- The statement below uses the bare names `volume` and `Measure`; bring them into scope.
open MeasureTheory

namespace Work.FTS.PressureOn.CurlGrad

/-- **Differentiating a convolution with a normed bump function.**  For `ψ : ℝ³ → ℝ` of class
`C¹` with compact support and any bump function `ρ : ContDiffBump (0 : ℝ³)`, the Fréchet derivative
of the convolution `ρ.normed volume ⋆ ψ` is the convolution of `ρ.normed volume` with the
derivative of `ψ`:

`fderiv ℝ (ρ.normed volume ⋆ ψ) x v = ((ρ.normed volume) ⋆ (fun y => fderiv ℝ ψ y v)) x`.

Please declare it in `namespace Work.FTS.PressureOn.CurlGrad` so that its full name is
`Work.FTS.PressureOn.CurlGrad.fderiv_normed_convolution_eq`.

Proof hints: `HasCompactSupport.hasFDerivAt_convolution_right`
(`Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`) with `L := ContinuousLinearMap.lsmul ℝ ℝ`,
`f := ρ.normed volume` (locally integrable: it is a bump function times a constant) and `g := ψ`
(compact support and `ContDiff ℝ 1`), then `HasFDerivAt.fderiv`;
`MeasureTheory.convolution_precompR_apply` (`Mathlib/Analysis/Convolution.lean`) evaluates the
`ContinuousLinearMap.precompR`-convolution at `v` and turns it into the scalar convolution of
`fun y => fderiv ℝ ψ y v`; `MeasureTheory.convolution_def` unfolds the definition.  Note the
convolution is `MeasureTheory.convolution f g L μ = fun x => ∫ t, L (f t) (g (x - t)) ∂μ`, so the
scalar convolution here is `∫ t, ρ.normed volume t * (fderiv ℝ ψ (x - t) v) ∂volume`. -/
theorem fderiv_normed_convolution_eq {ρ : ContDiffBump (0 : Work.FTS.PressureOn.R3)}
    {ψ : Work.FTS.PressureOn.R3 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ)
    (x v : Work.FTS.PressureOn.R3) :
    fderiv ℝ (MeasureTheory.convolution (ρ.normed volume) ψ (ContinuousLinearMap.lsmul ℝ ℝ)
        volume) x v
      = MeasureTheory.convolution (ρ.normed volume) (fun y => fderiv ℝ ψ y v)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  -- `ρ.normed volume` is a constant multiple of the bump function `ρ`, hence locally integrable.
  have hρi : MeasureTheory.LocallyIntegrable (ρ.normed (volume : Measure Work.FTS.PressureOn.R3))
      volume := ρ.integrable_normed.locallyIntegrable
  -- Differentiate the convolution in the second argument (which is `C¹` with compact support).
  have hdiff := hψcs.hasFDerivAt_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ) hρi hψ x
  rw [hdiff.fderiv]
  -- Evaluate the `precompR`-convolution at `v`, turning it into the scalar convolution.
  exact MeasureTheory.convolution_precompR_apply (L := ContinuousLinearMap.lsmul ℝ ℝ) hρi
    (hψcs.fderiv ℝ) (hψ.continuous_fderiv one_ne_zero) x v

end Work.FTS.PressureOn.CurlGrad
end
-- ===== merged: Submission.Work.FTS.PressureOn.CurlGrad.vorticity_gradient_eq_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity
open scoped Gradient

namespace Work.FTS.PressureOn.CurlGrad

/-!
# The curl of a gradient vanishes

Auxiliary facts for `vorticity_gradient_eq_zero`: the coordinates of Mathlib's gradient in the
standard basis, the differentiability of the gradient of a `C²` function, the coordinate formula
for the derivative of a gradient field (the `(i,j)` entry of `D(∇φ)(x)` is the mixed second
partial `∂ᵢ∂ⱼφ`), and the symmetry of the second derivative.
-/

/-- **Coordinates of a gradient.**  In the standard basis `e j` of `ℝ³`, the `j`-th coordinate of
the gradient `∇φ` is the partial derivative `∂ⱼφ`. -/
theorem gradient_apply_coord {φ : Work.FTS.PressureOn.R3 → ℝ} (y : Work.FTS.PressureOn.R3)
    (j : Fin 3) :
    (gradient φ y) j = fderiv ℝ φ y (FiniteTimeSingularity.e j) := by
  rw [← EuclideanSpace.basisFun_inner,
    show (EuclideanSpace.basisFun (Fin 3) ℝ) j = FiniteTimeSingularity.e j from
      (Work.Cyl.basisVec_eq_basisFun j).symm,
    inner_gradient_right]
  simp

/-- **The gradient of a `C²` function is differentiable.**  Its derivative at `x` is the second
derivative `fderiv ℝ (fderiv ℝ φ) x` of `φ`, transported to a map `ℝ³ → ℝ³` across the Riesz
identification `R3 ≃ₗᵢ⋆[ℝ] StrongDual ℝ R3`. -/
theorem hasFDerivAt_gradient {φ : Work.FTS.PressureOn.R3 → ℝ} {x : Work.FTS.PressureOn.R3}
    (hφ : ContDiffAt ℝ 2 φ x) :
    HasFDerivAt (gradient φ)
      (((InnerProductSpace.toDual ℝ Work.FTS.PressureOn.R3).symm.toContinuousLinearEquiv.toContinuousLinearMap :
          StrongDual ℝ Work.FTS.PressureOn.R3 →L[ℝ] Work.FTS.PressureOn.R3).comp
        (fderiv ℝ (fderiv ℝ φ) x)) x := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ φ) x := hφ.fderiv_right (m := 1) (by norm_num)
  have hfd : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) x :=
    (h1.differentiableAt (by norm_num)).hasFDerivAt
  exact (LinearIsometryEquiv.hasFDerivAt
    (InnerProductSpace.toDual ℝ Work.FTS.PressureOn.R3).symm (x := (fderiv ℝ φ) x)).comp x hfd

/-- **The derivative of a gradient in coordinates.**  For `φ` of class `C²` at `x`, the `(i,j)`
entry of the Jacobian of `∇φ` at `x` is the mixed second partial derivative `∂ᵢ∂ⱼφ`. -/
theorem fderiv_gradient_apply_coord {φ : Work.FTS.PressureOn.R3 → ℝ}
    {x : Work.FTS.PressureOn.R3} (hφ : ContDiffAt ℝ 2 φ x) (i j : Fin 3) :
    (fderiv ℝ (gradient φ) x (FiniteTimeSingularity.e i)) j
      = (fderiv ℝ (fderiv ℝ φ) x (FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e j) := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ φ) x := hφ.fderiv_right (m := 1) (by norm_num)
  have hfd : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) x :=
    (h1.differentiableAt (by norm_num)).hasFDerivAt
  have hd : DifferentiableAt ℝ (gradient φ) x := (hasFDerivAt_gradient hφ).differentiableAt
  have hcc : (fderiv ℝ (gradient φ) x (FiniteTimeSingularity.e i)) j
      = fderiv ℝ (fun y => (gradient φ y) j) x (FiniteTimeSingularity.e i) := by
    rw [Work.Cyl.fderiv_coord (gradient φ) x hd j, ContinuousLinearMap.comp_apply,
      PiLp.proj_apply]
  have hcongr : (fun y => (gradient φ y) j)
      = (fun y => fderiv ℝ φ y (FiniteTimeSingularity.e j)) :=
    funext fun y => gradient_apply_coord y j
  rw [hcc, hcongr]
  have hclm : HasFDerivAt (fun y => fderiv ℝ φ y (FiniteTimeSingularity.e j))
      ((fderiv ℝ (fderiv ℝ φ) x).flip (FiniteTimeSingularity.e j)) x := by
    have h := hfd.clm_apply (hasFDerivAt_const (FiniteTimeSingularity.e j) x)
    simpa using h
  rw [hclm.fderiv]
  simp

/-- **The second derivative of a `C²` function is symmetric.** -/
theorem sndFDeriv_symm {φ : Work.FTS.PressureOn.R3 → ℝ} {x : Work.FTS.PressureOn.R3}
    (hφ : ContDiffAt ℝ 2 φ x) (i j : Fin 3) :
    (fderiv ℝ (fderiv ℝ φ) x (FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e j)
      = (fderiv ℝ (fderiv ℝ φ) x (FiniteTimeSingularity.e j)) (FiniteTimeSingularity.e i) :=
  (hφ.isSymmSndFDerivAt (by norm_num)).eq (FiniteTimeSingularity.e i) (FiniteTimeSingularity.e j)

/-- **The curl of a gradient vanishes.**  For `φ : ℝ³ → ℝ` of class `C²` at `x` (in the sense of
`ContDiffAt`), `vorticity (gradient φ) x = 0`, where `vorticity` is the curl
(`FiniteTimeSingularity.vorticity`, defined in `ChallengeDeps.lean` as `∑ i, e i ⨯₃ ∂ᵢu`) and
`gradient` is Mathlib's gradient.

Please declare it in `namespace Work.FTS.PressureOn.CurlGrad` so that its full name is
`Work.FTS.PressureOn.CurlGrad.vorticity_gradient_eq_zero`.

Proof hints (all available in this workspace):
* the coordinate form of the curl `Work.Cyl.vorticity_eq_coordinates` and
  `Work.Cyl.fderiv_apply_coord` (`((fderiv ℝ u x) (basisVec i)).ofLp j =
  Cyl.pd i (fun y => (u y).ofLp j) x`), in `Submission/Work/Cyl/Basic.lean` and
  `Submission/Work/Cyl/Coords.lean`;
* `inner_gradient_left : ⟪∇ f x, y⟫ = fderiv ℝ f x y` (Mathlib,
  `Mathlib/Analysis/Calculus/Gradient/Basic.lean`) identifies `(gradient φ y) j =
  fderiv ℝ φ y (basisVec j)`;
* the mixed second derivatives of `φ` commute at `x`: `ContDiffAt.isSymmSndFDerivAt`
  (`Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`), i.e.
  `fderiv ℝ (fderiv ℝ φ) x v w = fderiv ℝ (fderiv ℝ φ) x w v` for `φ ∈ C²` at `x`; the relocation
  `fderiv ℝ (fun y => fderiv ℝ φ y (e j)) x (e i) = (fderiv ℝ (fderiv ℝ φ) x (e i)) (e j)` comes
  from `HasFDerivAt.clm_apply` / `fderiv_clm_apply`
  (`Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`), applied to `c := fun y => fderiv ℝ φ y` and
  the constant `u := fun _ => e j`.

With these, each of the three coordinates of `vorticity (gradient φ) x` is a difference
`∂ᵢ∂ⱼφ - ∂ⱼ∂ᵢφ = 0`. -/
theorem vorticity_gradient_eq_zero {φ : Work.FTS.PressureOn.R3 → ℝ}
    {x : Work.FTS.PressureOn.R3} (hφ : ContDiffAt ℝ 2 φ x) :
    FiniteTimeSingularity.vorticity (gradient φ) x = 0 := by
  have hsymm : ∀ i j : Fin 3,
      (fderiv ℝ (fderiv ℝ φ) x (FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e j)
        = (fderiv ℝ (fderiv ℝ φ) x (FiniteTimeSingularity.e j))
            (FiniteTimeSingularity.e i) :=
    fun i j => sndFDeriv_symm hφ i j
  rw [Work.Cyl.vorticity_eq_coordinates]
  apply PiLp.ext
  intro j
  fin_cases j
  · show ((fderiv ℝ (gradient φ) x) (FiniteTimeSingularity.e 1)).ofLp 2
        - ((fderiv ℝ (gradient φ) x) (FiniteTimeSingularity.e 2)).ofLp 1 = 0
    rw [fderiv_gradient_apply_coord hφ 1 2, hsymm 1 2, fderiv_gradient_apply_coord hφ 2 1]
    simp
  · show ((fderiv ℝ (gradient φ) x) (FiniteTimeSingularity.e 2)).ofLp 0
        - ((fderiv ℝ (gradient φ) x) (FiniteTimeSingularity.e 0)).ofLp 2 = 0
    rw [fderiv_gradient_apply_coord hφ 2 0, hsymm 2 0, fderiv_gradient_apply_coord hφ 0 2]
    simp
  · show ((fderiv ℝ (gradient φ) x) (FiniteTimeSingularity.e 0)).ofLp 1
        - ((fderiv ℝ (gradient φ) x) (FiniteTimeSingularity.e 1)).ofLp 0 = 0
    rw [fderiv_gradient_apply_coord hφ 0 1, hsymm 0 1, fderiv_gradient_apply_coord hφ 1 0]
    simp

end Work.FTS.PressureOn.CurlGrad
end
-- ===== merged: Submission.Work.FTS.PressureOn.Green.integrableOn_newtonKernel_ball =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Green

open MeasureTheory Metric

/-- The Newtonian kernel in `ℝ³` decays exactly like `(4π)⁻¹‖x‖⁻¹`; in particular
`‖newtonKernel x‖ ≤ (4π)⁻¹‖x‖ ^ (-1 : ℝ)` with equality for every `x`. -/
theorem norm_newtonKernel_eq (x : Work.FTS.PressureOn.R3) :
    ‖Work.FTS.PressureOn.newtonKernel x‖ = (4 * Real.pi)⁻¹ * ‖x‖ ^ (-1 : ℝ) := by
  rw [Work.FTS.PressureOn.newtonKernel, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (by positivity), Real.rpow_neg_one, mul_inv]

/-- The Newtonian kernel is measurable (indeed Borel measurable: it is `(4π‖x‖)⁻¹` and `inv` is
Borel measurable on `ℝ`, with the convention `0⁻¹ = 0`). -/
theorem measurable_newtonKernel : Measurable Work.FTS.PressureOn.newtonKernel := by
  have : Measurable fun x : Work.FTS.PressureOn.R3 => (4 * Real.pi * ‖x‖)⁻¹ :=
    Measurable.inv ((measurable_const (a := 4 * Real.pi)).mul continuous_norm.measurable)
  exact this

/-- **The Newtonian kernel is integrable on every ball centred at the origin of `ℝ³`.**  This is
the borderline `n = 3` case of the classical criterion: `‖x‖ ^ (-α)` is integrable near `0` in
dimension `d` exactly when `α < d`, and here `α = 1 < 3`.  The precise statement is the locally
integrable case `locallyIntegrable_of_norm_le_rpow` of the layer-cake formula. -/
theorem integrableOn_newtonKernel_ball (R : ℝ) :
    MeasureTheory.IntegrableOn (fun z : Work.FTS.PressureOn.R3 => Work.FTS.PressureOn.newtonKernel z)
      (Metric.ball (0 : Work.FTS.PressureOn.R3) R) := by
  have hfinrank : Module.finrank ℝ Work.FTS.PressureOn.R3 = 3 := by simp [Work.FTS.PressureOn.R3]
  refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (μ := volume) (F := ℝ)
    (C := (4 * Real.pi)⁻¹) (α := 1) (r := R) ?_ ?_ ?_ ?_
  · rw [hfinrank]; norm_num
  · rw [hfinrank]; norm_num
  · filter_upwards
    intro x
    exact le_of_eq (norm_newtonKernel_eq x)
  · exact measurable_newtonKernel.aestronglyMeasurable

end Work.FTS.PressureOn.Green
end
-- ===== merged: Submission.Work.FTS.PressureOn.Green.integral_exp_neg_normSq_R3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Gaussian integral on `ℝ³`

`∫ w : ℝ³, exp (-‖w‖ ^ 2) = π * √π`.

The type `R3 = EuclideanSpace ℝ (Fin 3)` is `WithLp 2 (Fin 3 → ℝ)`, and the map
`WithLp.toLp 2` from `Fin 3 → ℝ` to `R3` is volume preserving
(`PiLp.volume_preserving_toLp`).  On `Fin 3 → ℝ` the Gaussian splits as a product over
the three coordinates (`integral_fintype_prod_volume_eq_pow`), and each factor is the
one-dimensional Gaussian integral `∫ x, exp (-x ^ 2) = √π` (`integral_gaussian`).
-/

open MeasureTheory

namespace Work.FTS.PressureOn.Green


end Work.FTS.PressureOn.Green
end
-- ===== merged: Submission.Work.FTS.PressureOn.Green.laplaceTrace_exp_neg_mul_normSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Green

/-- The first derivative of the Gaussian profile `y ↦ exp (-(c‖y‖²))`.  It is
`-2c·exp(-(c‖z‖²))·⟪z,·⟫`; here the linear functional is written as
`Real.exp (-(c‖z‖²)) • ((-c) • (2 • innerSL ℝ z))` so that no rewriting is needed in the
second-derivative computation. -/
theorem hasFDerivAt_exp_neg_mul_normSq (c : ℝ) (z : Work.FTS.PressureOn.R3) :
    HasFDerivAt (fun y : Work.FTS.PressureOn.R3 => Real.exp (-(c * ‖y‖ ^ 2)))
      (Real.exp (-(c * ‖z‖ ^ 2)) • ((-c) • (2 • innerSL ℝ z))) z := by
  have h1 : HasFDerivAt (fun y : Work.FTS.PressureOn.R3 => ‖y‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Work.FTS.PressureOn.R3 => c * ‖y‖ ^ 2)
      (c • (2 • innerSL ℝ z)) z :=
    h1.const_mul c
  have h3 : HasFDerivAt (fun y : Work.FTS.PressureOn.R3 => -(c * ‖y‖ ^ 2))
      (-(c • (2 • innerSL ℝ z))) z :=
    h2.neg
  have h4 := h3.exp
  convert h4 using 1
  rw [neg_smul]

/-- The diagonal entry `∂ᵢ∂ᵢ` of the Hessian of the Gaussian profile, in the standard basis
`FiniteTimeSingularity.e`:
`∂ᵢ∂ᵢ (exp(-(c‖·‖²))) z = -2c·exp(-(c‖z‖²)) + 4c²·exp(-(c‖z‖²))·(zᵢ)²`. -/
theorem fderiv_fderiv_exp_neg_mul_normSq_diag (c : ℝ) (z : Work.FTS.PressureOn.R3) (i : Fin 3) :
    fderiv ℝ (fun w : Work.FTS.PressureOn.R3 =>
        fderiv ℝ (fun y : Work.FTS.PressureOn.R3 => Real.exp (-(c * ‖y‖ ^ 2))) w
          (FiniteTimeSingularity.e i)) z (FiniteTimeSingularity.e i)
      = -2 * c * Real.exp (-(c * ‖z‖ ^ 2))
        + 4 * c ^ 2 * Real.exp (-(c * ‖z‖ ^ 2)) * (z i) ^ 2 := by
  -- The first derivative, as an explicit function of the base point.
  have hfun : (fun w : Work.FTS.PressureOn.R3 =>
        fderiv ℝ (fun y : Work.FTS.PressureOn.R3 => Real.exp (-(c * ‖y‖ ^ 2))) w
          (FiniteTimeSingularity.e i))
      = fun w : Work.FTS.PressureOn.R3 =>
          Real.exp (-(c * ‖w‖ ^ 2)) * ((-2 * c) * (innerSL ℝ (FiniteTimeSingularity.e i)) w) := by
    funext w
    have h1 : HasFDerivAt (fun y : Work.FTS.PressureOn.R3 => ‖y‖ ^ 2) (2 • innerSL ℝ w) w :=
      (hasStrictFDerivAt_norm_sq w).hasFDerivAt
    have h2 : HasFDerivAt (fun y : Work.FTS.PressureOn.R3 => c * ‖y‖ ^ 2)
        (c • (2 • innerSL ℝ w)) w :=
      h1.const_mul c
    have h3 : HasFDerivAt (fun y : Work.FTS.PressureOn.R3 => -(c * ‖y‖ ^ 2))
        (-(c • (2 • innerSL ℝ w))) w :=
      h2.neg
    rw [(h3.exp).fderiv]
    simp only [neg_apply, smul_apply, innerSL_apply_apply]
    rw [real_inner_comm (FiniteTimeSingularity.e i) w]
    ring
  rw [hfun]
  -- Product rule for `w ↦ exp(-(c‖w‖²)) · ((-2c)·⟪eᵢ,w⟫)`.
  have hA : HasFDerivAt (fun w : Work.FTS.PressureOn.R3 => Real.exp (-(c * ‖w‖ ^ 2)))
      (Real.exp (-(c * ‖z‖ ^ 2)) • ((-c) • (2 • innerSL ℝ z))) z :=
    hasFDerivAt_exp_neg_mul_normSq c z
  have hB : HasFDerivAt
      (fun w : Work.FTS.PressureOn.R3 => (-2 * c) * (innerSL ℝ (FiniteTimeSingularity.e i)) w)
      ((-2 * c) • innerSL ℝ (FiniteTimeSingularity.e i)) z :=
    (ContinuousLinearMap.hasFDerivAt (innerSL ℝ (FiniteTimeSingularity.e i))).const_mul (-2 * c)
  have hprod : HasFDerivAt (fun w : Work.FTS.PressureOn.R3 =>
        Real.exp (-(c * ‖w‖ ^ 2)) * ((-2 * c) * (innerSL ℝ (FiniteTimeSingularity.e i)) w))
      (Real.exp (-(c * ‖z‖ ^ 2)) • ((-2 * c) • innerSL ℝ (FiniteTimeSingularity.e i))
        + (-2 * c * (innerSL ℝ (FiniteTimeSingularity.e i)) z) •
          (Real.exp (-(c * ‖z‖ ^ 2)) • ((-c) • (2 • innerSL ℝ z)))) z := hA.mul hB
  rw [hprod.fderiv]
  simp only [add_apply, smul_apply, innerSL_apply_apply]
  have hee : inner ℝ (FiniteTimeSingularity.e i) (FiniteTimeSingularity.e i) = 1 := by
    rw [FiniteTimeSingularity.e, PiLp.inner_apply]
    simp [Pi.single_apply]
  have hze : inner ℝ z (FiniteTimeSingularity.e i) = z i := by
    rw [FiniteTimeSingularity.e, PiLp.inner_apply]
    simp [Pi.single_apply]
  have hez : inner ℝ (FiniteTimeSingularity.e i) z = z i := by
    rw [real_inner_comm, hze]
  rw [hee, hze, hez]
  ring

/-- **The Laplacian of the Gaussian profile**: for the Gaussian `y ↦ exp(-(c‖y‖²))` the trace of
the Hessian (in the standard basis of `ℝ³`) is `(4c²‖z‖² - 6c)·exp(-(c‖z‖²))`.

This is the one-dimensional-in-`r` computation `Δ exp(-cr²) = (4c²r² - 6c) exp(-cr²)` written in
`ℝ³`: the three diagonal entries `-2c·exp + 4c²·exp·zᵢ²` sum to `-6c·exp + 4c²·exp·‖z‖²`. -/
theorem laplaceTrace_exp_neg_mul_normSq (c : ℝ) (z : Work.FTS.PressureOn.R3) :
    Work.FTS.PressureOn.laplaceTrace (fun y : Work.FTS.PressureOn.R3 => Real.exp (-(c * ‖y‖ ^ 2))) z
      = (4 * c ^ 2 * ‖z‖ ^ 2 - 6 * c) * Real.exp (-(c * ‖z‖ ^ 2)) := by
  have hsum : ∑ i : Fin 3, (z i) ^ 2 = ‖z‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (by positivity)]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [Work.FTS.PressureOn.laplaceTrace]
  rw [Finset.sum_congr rfl (fun i _ => fderiv_fderiv_exp_neg_mul_normSq_diag c z i)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  norm_num
  ring

end Work.FTS.PressureOn.Green
end
-- ===== merged: Submission.Work.FTS.PressureOn.Green.newtonKernel_eq_integral_exp_neg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Green


end Work.FTS.PressureOn.Green
end
-- ===== merged: Submission.Work.FTS.PressureOn.MollDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn

noncomputable section

/-- The pairing `⟨D, f⟩ = ∫ ⟪Φ, f⟫ + ∫ q · div f` of the distribution `D := Φ - ∇q` against the
test field `f`.  (`hdiv` says `⟨D, ∇φ⟩ = 0` and `hcurl` that `⟨D, ∇×ψ⟩ = 0`.) -/
def Dpair (q : R3 → ℝ) (Φ : R3 → R3) (f : R3 → R3) : ℝ :=
  (∫ x, inner ℝ (Φ x) (f x)) + ∫ x, q x * FiniteTimeSingularity.div f x

theorem Dpair_apply (q : R3 → ℝ) (Φ : R3 → R3) (f : R3 → R3) :
    Dpair q Φ f = (∫ x, inner ℝ (Φ x) (f x)) + ∫ x, q x * FiniteTimeSingularity.div f x :=
  rfl

/-- The mollifier bump at scale `n`: the `ContDiffBump` at the origin with `rIn = 1/(n+2)` and
`rOut = 1/(n+1)`. -/
noncomputable def bump (n : ℕ) : ContDiffBump (0 : R3) :=
  ⟨1 / ((n : ℝ) + 2), 1 / ((n : ℝ) + 1),
    by positivity,
    by
      rw [one_div, one_div, inv_lt_inv₀ (by positivity) (by positivity)]
      linarith⟩

/-- The normalised bump at scale `n`: a smooth nonnegative function with `∫ rho n = 1`. -/
noncomputable def rho (n : ℕ) : R3 → ℝ := (bump n).normed MeasureTheory.volume

/-- Scalar mollification at scale `n`. -/
noncomputable def moll (n : ℕ) (g : R3 → ℝ) : R3 → ℝ :=
  MeasureTheory.convolution (rho n) g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume

/-- Vector mollification at scale `n`. -/
noncomputable def mollV (n : ℕ) (G : R3 → R3) : R3 → R3 :=
  MeasureTheory.convolution (rho n) G (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume

end

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Metric
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-! ## The profile `χ` -/

/-- The smooth profile `χ(t) = smoothTransition (2 - t)`: it is `1` for `t ≤ 1`, `0` for `t ≥ 2`,
and takes its values in `[0,1]`. -/
noncomputable def radialCut (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

theorem radialCut_eq_one {t : ℝ} (ht : t ≤ 1) : radialCut t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem radialCut_eq_zero {t : ℝ} (ht : 2 ≤ t) : radialCut t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem radialCut_nonneg (t : ℝ) : 0 ≤ radialCut t := Real.smoothTransition.nonneg _

theorem radialCut_le_one (t : ℝ) : radialCut t ≤ 1 := Real.smoothTransition.le_one _

theorem contDiff_radialCut (n : ℕ∞) : ContDiff ℝ n radialCut :=
  (Real.smoothTransition.contDiff (n := n)).comp (contDiff_const.sub contDiff_id)




/-! ## The rescaled cutoffs in `ℝ³` -/

/-- `kernelCut ε x = χ(‖x‖²/ε²)`: `1` for `‖x‖ ≤ ε` and `0` for `√2 ε ≤ ‖x‖`. -/
noncomputable def kernelCut (ε : ℝ) (x : R3) : ℝ := radialCut (‖x‖ ^ 2 / ε ^ 2)

/-- `smallCut ε x = 1 - χ(‖x‖²/ε²)`: `0` for `‖x‖ ≤ ε` and `1` for `√2 ε ≤ ‖x‖`.  It is the
cutoff that removes the singularity of the Newtonian kernel at the origin. -/
noncomputable def smallCut (ε : ℝ) (x : R3) : ℝ := 1 - radialCut (‖x‖ ^ 2 / ε ^ 2)

/-- `outerCut R x = χ(‖x‖²/R²)`: `1` for `‖x‖ ≤ R` and `0` for `√2 R ≤ ‖x‖`. -/
noncomputable def outerCut (R : ℝ) (x : R3) : ℝ := radialCut (‖x‖ ^ 2 / R ^ 2)

@[simp] theorem kernelCut_apply (ε : ℝ) (x : R3) : kernelCut ε x = radialCut (‖x‖ ^ 2 / ε ^ 2) :=
  rfl

@[simp] theorem smallCut_apply (ε : ℝ) (x : R3) :
    smallCut ε x = 1 - radialCut (‖x‖ ^ 2 / ε ^ 2) := rfl

@[simp] theorem outerCut_apply (R : ℝ) (x : R3) : outerCut R x = radialCut (‖x‖ ^ 2 / R ^ 2) := rfl

theorem contDiff_kernelCut (ε : ℝ) (hε : 0 < ε) (n : ℕ∞) : ContDiff ℝ n (kernelCut ε) :=
  (contDiff_radialCut n).comp ((contDiff_norm_sq (𝕜 := ℝ) (n := n)).div_const (ε ^ 2))

theorem contDiff_smallCut (ε : ℝ) (hε : 0 < ε) (n : ℕ∞) : ContDiff ℝ n (smallCut ε) :=
  contDiff_const.sub (contDiff_kernelCut ε hε n)

theorem contDiff_outerCut (R : ℝ) (hR : 0 < R) (n : ℕ∞) : ContDiff ℝ n (outerCut R) :=
  (contDiff_radialCut n).comp ((contDiff_norm_sq (𝕜 := ℝ) (n := n)).div_const (R ^ 2))








theorem outerCut_eq_one {R : ℝ} (hR : 0 < R) {x : R3} (hx : ‖x‖ ≤ R) : outerCut R x = 1 := by
  refine radialCut_eq_one ?_
  rw [div_le_one (by positivity)]
  nlinarith [norm_nonneg x]

theorem outerCut_eq_zero {R : ℝ} (hR : 0 < R) {x : R3} (hx : 2 * R ≤ ‖x‖) : outerCut R x = 0 := by
  refine radialCut_eq_zero ?_
  rw [le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg x]


theorem smallCut_nonneg (ε : ℝ) (x : R3) : 0 ≤ smallCut ε x := by
  rw [smallCut_apply]; linarith [radialCut_le_one (‖x‖ ^ 2 / ε ^ 2)]

theorem smallCut_le_one (ε : ℝ) (x : R3) : smallCut ε x ≤ 1 := by
  rw [smallCut_apply]; linarith [radialCut_nonneg (‖x‖ ^ 2 / ε ^ 2)]

theorem outerCut_nonneg (R : ℝ) (x : R3) : 0 ≤ outerCut R x := radialCut_nonneg _

theorem outerCut_le_one (R : ℝ) (x : R3) : outerCut R x ≤ 1 := radialCut_le_one _

theorem hasCompactSupport_outerCut {R : ℝ} (hR : 0 < R) : HasCompactSupport (outerCut R) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := closedBall 0 (2 * R))
    (isCompact_closedBall 0 (2 * R)) ?_
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  push Not at h
  exact hx (outerCut_eq_zero hR (le_of_lt h))

/-! ## The one-dimensional profiles -/

/-- The one-dimensional profile `ρ_ε(r) = 1 - χ(r²/ε²)`, so that
`smallCut ε x = rhoProfile ε ‖x‖`. -/
noncomputable def rhoProfile (ε : ℝ) (r : ℝ) : ℝ := 1 - radialCut (r ^ 2 / ε ^ 2)

@[simp] theorem rhoProfile_apply (ε r : ℝ) : rhoProfile ε r = 1 - radialCut (r ^ 2 / ε ^ 2) := rfl


theorem rhoProfile_eq_zero {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : r ^ 2 ≤ ε ^ 2) :
    rhoProfile ε r = 0 := by
  rw [rhoProfile_apply, radialCut_eq_one (by
    rw [div_le_one (by positivity)]
    exact hr), sub_self]

theorem rhoProfile_eq_one {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : 2 * ε ^ 2 ≤ r ^ 2) :
    rhoProfile ε r = 1 := by
  rw [rhoProfile_apply, radialCut_eq_zero (by
    rw [le_div_iff₀ (by positivity)]
    linarith), sub_zero]



/-- **The mass kernel** `massKernel ε x = (4π‖x‖)⁻¹ ρ_ε''(‖x‖)`: the (classical) Laplacian of the
truncated Newtonian kernel `x ↦ smallCut ε x * (4π‖x‖)⁻¹`, away from the origin, where
`ρ_ε(r) = 1 - χ(r²/ε²)`. -/
noncomputable def massKernel (ε : ℝ) (x : R3) : ℝ :=
  newtonKernel x * deriv (deriv (rhoProfile ε)) ‖x‖

theorem massKernel_eq (ε : ℝ) (x : R3) :
    massKernel ε x = newtonKernel x * deriv (deriv (rhoProfile ε)) ‖x‖ := rfl

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.KI.laplaceTrace_comp_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `laplaceTrace` is invariant under translations

The Laplace trace `laplaceTrace φ x = ∑ᵢ ∂ᵢ∂ᵢ φ(x)` of a function on `ℝ³` is unchanged by
precomposing `φ` with a translation: with `φ = fun z => ψ (z + y)` the translated function attains
at `x` the same value of the trace that `ψ` attains at `x + y`.  This is the second-derivative
chain rule for the translation `z ↦ z + y` (whose Fréchet derivative is the identity), applied
twice.

The pointwise input is Mathlib's unconditional `fderiv_comp_add_right`
(`fderiv 𝕜 (fun x ↦ f (x + a)) x = fderiv 𝕜 f (x + a)`), which holds for the *total* `fderiv`
without any differentiability hypothesis; the two rewrites therefore close the sum coordinatewise.
-/

namespace Work.FTS.PressureOn.PoissonAux.KI

theorem laplaceTrace_comp_add (ψ : R3 → ℝ) (hψ : ContDiff ℝ 2 ψ) (y x : R3) :
    laplaceTrace (fun z : R3 => ψ (z + y)) x = laplaceTrace ψ (x + y) := by
  rw [laplaceTrace, laplaceTrace]
  have _hψ : ContDiff ℝ 2 ψ := hψ
  refine Finset.sum_congr rfl fun i _ => ?_
  -- first derivative: `fderiv ℝ (fun z => ψ (z + y)) w = fderiv ℝ ψ (w + y)`
  have h1 : (fun w : R3 => fderiv ℝ (fun z : R3 => ψ (z + y)) w (FiniteTimeSingularity.e i))
      = fun w : R3 => fderiv ℝ ψ (w + y) (FiniteTimeSingularity.e i) := by
    funext w
    simp only [fderiv_comp_add_right]
  rw [h1]
  -- second derivative: differentiate the translated first-derivative field
  have h2 : fderiv ℝ (fun w : R3 => fderiv ℝ ψ (w + y) (FiniteTimeSingularity.e i)) x
      = fderiv ℝ (fun w : R3 => fderiv ℝ ψ w (FiniteTimeSingularity.e i)) (x + y) :=
    fderiv_comp_add_right
      (f := fun v : R3 => fderiv ℝ ψ v (FiniteTimeSingularity.e i)) (a := y)
  exact congrArg (fun L : R3 →L[ℝ] ℝ => L (FiniteTimeSingularity.e i)) h2

end Work.FTS.PressureOn.PoissonAux.KI
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.gradient_newtonKernel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.PoissonAux

open Work.FTS.PressureOn

/-! ## Two derivatives on `ℝ³`

Everything is done through Fréchet derivatives, since `gradient` is *defined* as the Riesz
representative of `fderiv`.  The two ingredients are

* `∇‖·‖ z = ‖z‖⁻¹ • z` at `z ≠ 0` (`hasFDerivAt_norm_R3`); and
* the inverse rule, giving `∇(‖·‖⁻¹) z = -(‖z‖²)⁻¹‖z‖⁻¹ • z` (`hasFDerivAt_inv_norm_R3`).

The Newtonian kernel `(4π‖z‖)⁻¹` is `(4π)⁻¹ * ‖z‖⁻¹`, so the chain rule gives the stated
gradient.  At `z = 0` the kernel is *not* differentiable (its value there is `0` but it blows
up nearby), so there both sides are `0` for the junk-value reasons built into `fderiv`. -/

/-- The Fréchet derivative of the norm on `ℝ³` at a nonzero point: since `‖·‖ = √(‖·‖²)` and
`fderiv (‖·‖²) z = 2 ⟪z, ·⟫`, the derivative is `⟪‖z‖⁻¹ • z, ·⟫`. -/
private lemma hasFDerivAt_norm_R3 (z : R3) (hz : z ≠ 0) :
    HasFDerivAt (fun x : R3 => ‖x‖) (innerSL ℝ (‖z‖⁻¹ • z)) z := by
  have hz' : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hz
  have hsq : HasFDerivAt (fun x : R3 => ‖x‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt t) (1 / (2 * Real.sqrt (‖z‖ ^ 2)))
      (‖z‖ ^ 2) :=
    Real.hasDerivAt_sqrt (pow_ne_zero 2 hz')
  have hcomp : HasFDerivAt (fun x : R3 => Real.sqrt (‖x‖ ^ 2))
      ((ContinuousLinearMap.toSpanSingleton ℝ (1 / (2 * Real.sqrt (‖z‖ ^ 2))))
        ∘SL (2 • innerSL ℝ z)) z :=
    hsqrt.hasFDerivAt.comp z hsq
  have heq : (fun x : R3 => Real.sqrt (‖x‖ ^ 2)) = fun x => ‖x‖ := by
    funext x; exact Real.sqrt_sq (norm_nonneg x)
  rw [heq] at hcomp
  convert hcomp using 1
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_apply, smul_eq_mul, innerSL_apply_apply, Real.sqrt_sq (norm_nonneg z),
    real_inner_smul_left]
  field_simp
  ring

/-- The Fréchet derivative of `‖·‖⁻¹` at a nonzero point, by the inverse rule applied to the
norm: `∇(‖·‖⁻¹) z = -(‖z‖²)⁻¹ • ∇‖·‖ z`. -/
private lemma hasFDerivAt_inv_norm_R3 (z : R3) (hz : z ≠ 0) :
    HasFDerivAt (fun x : R3 => ‖x‖⁻¹)
      (innerSL ℝ (( -(‖z‖ ^ 2)⁻¹ * ‖z‖⁻¹) • z)) z := by
  have hz' : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hz
  have hnorm := hasFDerivAt_norm_R3 z hz
  have hinv : HasDerivAt (fun t : ℝ => t⁻¹) (-(‖z‖ ^ 2)⁻¹) (‖z‖) := hasDerivAt_inv hz'
  have hcomp : HasFDerivAt (fun x : R3 => ‖x‖⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(‖z‖ ^ 2)⁻¹))
        ∘SL (innerSL ℝ (‖z‖⁻¹ • z))) z :=
    hinv.hasFDerivAt.comp z hnorm
  convert hcomp using 1
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, innerSL_apply_apply, real_inner_smul_left]
  ring

/-- The Newtonian kernel is not differentiable at the origin: it vanishes there but blows up
along any ray.  Hence its `gradient` there is the junk value `0`. -/
private lemma not_differentiableAt_newtonKernel_zero :
    ¬ DifferentiableAt ℝ newtonKernel 0 := by
  intro hd
  have hct : ContinuousAt newtonKernel 0 := hd.continuousAt
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hct 1 (by norm_num)
  have hk0 : newtonKernel 0 = 0 := by simp [newtonKernel]
  -- a point of small norm at which the kernel is large
  set r : ℝ := min δ 1 / (8 * Real.pi) with hrdef
  have h8pi : (1 : ℝ) < 8 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hrpos : 0 < r := by rw [hrdef]; positivity
  have hrlt : r < δ := by
    rw [hrdef]
    refine lt_of_le_of_lt (div_le_div_of_nonneg_right (min_le_left δ 1) (by positivity)) ?_
    exact div_lt_self hδpos h8pi
  have henorm : ‖(FiniteTimeSingularity.e 0 : R3)‖ = 1 := by simp [FiniteTimeSingularity.e]
  set y : R3 := r • (FiniteTimeSingularity.e 0) with hydef
  have hyval : newtonKernel y = (4 * Real.pi * r)⁻¹ := by
    rw [hydef, newtonKernel, norm_smul, henorm, mul_one, Real.norm_eq_abs, abs_of_pos hrpos]
  have hyball : y ∈ Metric.ball (0 : R3) δ := by
    rw [Metric.mem_ball, dist_zero_right, hydef, norm_smul, henorm, mul_one,
      Real.norm_eq_abs, abs_of_pos hrpos]
    exact hrlt
  have hb := hδ hyball
  rw [hk0, dist_zero_right, Real.norm_eq_abs] at hb
  -- the kernel is at least `2` there
  have h4 : 4 * Real.pi * r ≤ 1 / 2 := by
    rw [hrdef]
    have : 4 * Real.pi * (min δ 1 / (8 * Real.pi)) = min δ 1 / 2 := by field_simp; ring
    rw [this]; linarith [min_le_right δ 1]
  have hpos4 : 0 < 4 * Real.pi * r := by positivity
  have hge : (2 : ℝ) ≤ newtonKernel y := by
    rw [hyval]
    have hh := inv_anti₀ hpos4 h4
    have h2 : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
    rw [h2] at hh
    exact hh
  have hb1 : newtonKernel y < 1 := (abs_lt.mp hb).2
  linarith

/-- The gradient of the Newtonian kernel `newtonKernel z = (4π‖z‖)⁻¹`
(`Work.FTS.PressureOn.newtonKernel`, `Submission/Work/FTS/PressureOn/Defs.lean`) is the
explicitly defined `newtonGrad z = -((4π)⁻¹‖z‖⁻³) • z` (`Work.FTS.PressureOn.newtonGrad`),
pointwise on all of `ℝ³` (both sides are `0` at `z = 0`). -/
theorem gradient_newtonKernel (z : Work.FTS.PressureOn.R3) :
    gradient Work.FTS.PressureOn.newtonKernel z = Work.FTS.PressureOn.newtonGrad z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [gradient_eq_zero_of_not_differentiableAt (f := newtonKernel)]
    · rw [newtonGrad_apply]; simp
    · exact not_differentiableAt_newtonKernel_zero
  · -- `z ≠ 0`: the chain rule, the inverse rule and the scaling `(4π‖z‖)⁻¹ = (4π)⁻¹‖z‖⁻¹`
    have hbase := hasFDerivAt_inv_norm_R3 z hz
    have hc : HasFDerivAt (fun x : R3 => (4 * Real.pi)⁻¹ * ‖x‖⁻¹)
        ((4 * Real.pi)⁻¹ • innerSL ℝ (( -(‖z‖ ^ 2)⁻¹ * ‖z‖⁻¹) • z)) z :=
      hbase.const_mul ((4 * Real.pi)⁻¹)
    have hnewt : HasFDerivAt newtonKernel
        ((4 * Real.pi)⁻¹ • innerSL ℝ (( -(‖z‖ ^ 2)⁻¹ * ‖z‖⁻¹) • z)) z := by
      have hfun : newtonKernel = fun x : R3 => (4 * Real.pi)⁻¹ * ‖x‖⁻¹ := by
        funext x; rw [newtonKernel]; ring
      rw [hfun]
      exact hc
    -- the Riesz representative of this derivative is exactly `newtonGrad z`
    have hmap : ((4 * Real.pi)⁻¹ • innerSL ℝ (( -(‖z‖ ^ 2)⁻¹ * ‖z‖⁻¹) • z))
        = InnerProductSpace.toDual ℝ R3 (newtonGrad z) := by
      ext v
      rw [newtonGrad_apply]
      simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
        real_inner_smul_left, InnerProductSpace.toDual_apply_apply]
      have hz' : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hz
      field_simp
    have h := hnewt.hasGradientAt.gradient
    rw [hmap] at h
    rw [h, LinearIsometryEquiv.symm_apply_apply]

end Work.FTS.PressureOn.PoissonAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.Weyl.exists_smooth_compactSupport_integral_ne_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PressureOn.Weyl

/-- There is a smooth, compactly supported test function on `ℝ³` with non-zero integral.

We use Mathlib's normalised bump function `ContDiffBump.normed`: it is `C^∞`, compactly
supported and its integral is exactly `1`.  (This is the "test function" needed to make the
weak formulation of the Poisson equation for the pressure non-trivial.) -/
theorem exists_smooth_compactSupport_integral_ne_zero :
    ∃ φ : Work.FTS.PressureOn.R3 → ℝ,
      (∀ n : ℕ, ContDiff ℝ n φ) ∧ HasCompactSupport φ ∧ (∫ x, φ x) ≠ 0 := by
  let b : ContDiffBump (0 : Work.FTS.PressureOn.R3) := ⟨1, 2, by norm_num, by norm_num⟩
  refine ⟨b.normed volume, fun n => ?_, b.hasCompactSupport_normed, ?_⟩
  · exact b.contDiff_normed
  · rw [b.integral_normed]
    norm_num

end Work.FTS.PressureOn.Weyl
end
-- ===== merged: Submission.Work.FTS.PressureOn.Weyl.hasFDerivAt_of_fTC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set

namespace Work.FTS.PressureOn.Weyl

/-- **From the coordinatewise fundamental theorem of calculus to a Fréchet derivative.**

If the difference quotients of `q` along the three coordinate directions are the integrals
of the corresponding components of a *continuous* field `Φ`, then `q` is differentiable
everywhere with derivative `w ↦ ⟪Φ x, w⟫` (i.e. the linear functional `innerSL ℝ (Φ x)`).

The proof is the standard one: telescoping along the three coordinate directions expresses
`q (x + v) - q x` as a sum of three one-dimensional integrals, and continuity of `Φ` at `x`
makes each of them differ from the corresponding linear term by `o(‖v‖)`. -/
theorem hasFDerivAt_of_fTC
    (q : Work.FTS.PressureOn.R3 → ℝ)
    (Φ : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3) (hΦ : Continuous Φ)
    (hFTC : ∀ x : Work.FTS.PressureOn.R3, ∀ t : ℝ, ∀ i : Fin 3,
      q (x + t • FiniteTimeSingularity.e i) - q x
        = ∫ s in (0 : ℝ)..t, Φ (x + s • FiniteTimeSingularity.e i) i) :
    ∀ x, HasFDerivAt q (innerSL ℝ (Φ x)) x := by
  intro x
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  -- a modulus of continuity of `Φ` at `x`
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ z, ‖z - x‖ < δ → ‖Φ z - Φ x‖ < c / 3 := by
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hΦ.continuousAt (c / 3) (by linarith)
    exact ⟨δ, hδpos, fun z hz => by simpa [dist_eq_norm] using hδ hz⟩
  filter_upwards [Metric.ball_mem_nhds (0 : R3) (by linarith : (0 : ℝ) < δ / 3)] with v hv
  rw [Metric.mem_ball, dist_zero_right] at hv
  -- expansion of `v` in the standard orthonormal basis
  have hsum : (∑ i : Fin 3, v i • FiniteTimeSingularity.e i) = v := by
    trans (∑ i, ((EuclideanSpace.basisFun (Fin 3) ℝ).repr v).ofLp i
        • (EuclideanSpace.basisFun (Fin 3) ℝ) i : R3)
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]; rfl
    · exact OrthonormalBasis.sum_repr _ v
  have hv3 : v = v 0 • FiniteTimeSingularity.e 0 + v 1 • FiniteTimeSingularity.e 1
      + v 2 • FiniteTimeSingularity.e 2 := by
    conv_lhs => rw [← hsum]
    rw [Fin.sum_univ_three]
  have hin : ∀ a b : ℝ, inner ℝ a b = b * a := by intro a b; simp
  have hL : (innerSL ℝ (Φ x)) v = (Φ x) 2 * v 2 + (Φ x) 1 * v 1 + (Φ x) 0 * v 0 := by
    rw [innerSL_apply_apply, PiLp.inner_apply, Fin.sum_univ_three]
    simp only [hin]
    ring
  have hnormsq_le : ∀ i : Fin 3, |v i| ≤ ‖v‖ := fun i => by
    have h := PiLp.norm_apply_le (β := fun _ : Fin 3 => ℝ) v i
    simpa using h
  have henorm : ∀ i : Fin 3, ‖FiniteTimeSingularity.e i‖ = 1 := fun i => by
    rw [FiniteTimeSingularity.e, PiLp.toLp_single, PiLp.norm_single]; simp
  -- telescoping along the three coordinate directions
  have hQ : q (x + v) - q x
      = (∫ s in (0 : ℝ)..(v 2), Φ (x + v 0 • FiniteTimeSingularity.e 0
            + v 1 • FiniteTimeSingularity.e 1 + s • FiniteTimeSingularity.e 2) 2)
      + (∫ s in (0 : ℝ)..(v 1), Φ (x + v 0 • FiniteTimeSingularity.e 0
            + s • FiniteTimeSingularity.e 1) 1)
      + (∫ s in (0 : ℝ)..(v 0), Φ (x + s • FiniteTimeSingularity.e 0) 0) := by
    conv_lhs => rw [hv3]
    rw [show x + (v 0 • FiniteTimeSingularity.e 0 + v 1 • FiniteTimeSingularity.e 1
          + v 2 • FiniteTimeSingularity.e 2)
        = x + v 0 • FiniteTimeSingularity.e 0 + v 1 • FiniteTimeSingularity.e 1
          + v 2 • FiniteTimeSingularity.e 2 from by abel]
    have H0 := hFTC x (v 0) (0 : Fin 3)
    have H1 := hFTC (x + v 0 • FiniteTimeSingularity.e 0) (v 1) (1 : Fin 3)
    have H2 := hFTC (x + v 0 • FiniteTimeSingularity.e 0 + v 1 • FiniteTimeSingularity.e 1)
      (v 2) (2 : Fin 3)
    linarith [H0, H1, H2]
  -- the individual one-dimensional estimates
  have hterm : ∀ (y : R3) (k : Fin 3), ‖y - x‖ ≤ 2 * ‖v‖ →
      ‖(∫ s in (0 : ℝ)..(v k), Φ (y + s • FiniteTimeSingularity.e k) k)
          - (Φ x) k * v k‖ ≤ (c / 3) * |v k| := by
    intro y k hy
    have hcont : Continuous fun s : ℝ => Φ (y + s • FiniteTimeSingularity.e k) k :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).comp
        (hΦ.comp (continuous_const.add (continuous_id.smul continuous_const)))
    have hsub : (∫ s in (0 : ℝ)..(v k), Φ (y + s • FiniteTimeSingularity.e k) k)
          - (Φ x) k * v k
        = ∫ s in (0 : ℝ)..(v k), (Φ (y + s • FiniteTimeSingularity.e k) k - (Φ x) k) := by
      rw [intervalIntegral.integral_sub (hcont.intervalIntegrable 0 (v k))
          (continuous_const.intervalIntegrable 0 (v k)),
        intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      ring
    rw [hsub]
    have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) (v k),
        ‖Φ (y + s • FiniteTimeSingularity.e k) k - (Φ x) k‖ ≤ c / 3 := by
      intro s hs
      have hk := hnormsq_le k
      have hs1 : |s| ≤ |v k| := by
        have hmem : s ∈ Set.uIcc (0 : ℝ) (v k) := Set.uIoc_subset_uIcc hs
        rw [Set.mem_uIcc] at hmem
        rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_nonneg h1, abs_of_nonneg (le_trans h1 h2)]
          exact h2
        · rw [abs_of_nonpos h2, abs_of_nonpos (le_trans h1 h2)]
          linarith
      have hs2 : ‖y + s • FiniteTimeSingularity.e k - x‖ < δ := by
        rw [show y + s • FiniteTimeSingularity.e k - x
            = (y - x) + s • FiniteTimeSingularity.e k from by abel]
        have hsk : ‖s • FiniteTimeSingularity.e k‖ = |s| := by
          rw [norm_smul, Real.norm_eq_abs, henorm k, mul_one]
        calc ‖(y - x) + s • FiniteTimeSingularity.e k‖
            ≤ ‖y - x‖ + ‖s • FiniteTimeSingularity.e k‖ := norm_add_le _ _
          _ ≤ 3 * ‖v‖ := by rw [hsk]; linarith
          _ < δ := by linarith
      have hΦz := hδ _ hs2
      calc ‖Φ (y + s • FiniteTimeSingularity.e k) k - (Φ x) k‖
          = ‖(Φ (y + s • FiniteTimeSingularity.e k) - Φ x) k‖ := by simp
        _ ≤ ‖Φ (y + s • FiniteTimeSingularity.e k) - Φ x‖ := by
              simpa using PiLp.norm_apply_le (Φ (y + s • FiniteTimeSingularity.e k) - Φ x) k
        _ ≤ c / 3 := le_of_lt hΦz
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := v k)
      (C := c / 3) hbound
    simpa using hb
  have e0 := hnormsq_le 0
  have e1 := hnormsq_le 1
  have e2 := hnormsq_le 2
  have ht2 := hterm (x + v 0 • FiniteTimeSingularity.e 0 + v 1 • FiniteTimeSingularity.e 1) 2 (by
      rw [show x + v 0 • FiniteTimeSingularity.e 0 + v 1 • FiniteTimeSingularity.e 1 - x
          = v 0 • FiniteTimeSingularity.e 0 + v 1 • FiniteTimeSingularity.e 1 from by abel]
      calc ‖v 0 • FiniteTimeSingularity.e 0 + v 1 • FiniteTimeSingularity.e 1‖
          ≤ ‖v 0 • FiniteTimeSingularity.e 0‖ + ‖v 1 • FiniteTimeSingularity.e 1‖ :=
            norm_add_le _ _
        _ = |v 0| + |v 1| := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, henorm 0, henorm 1]
            ring
        _ ≤ 2 * ‖v‖ := by linarith)
  have ht1 := hterm (x + v 0 • FiniteTimeSingularity.e 0) 1 (by
      rw [show x + v 0 • FiniteTimeSingularity.e 0 - x = v 0 • FiniteTimeSingularity.e 0 from
          by abel,
        norm_smul, Real.norm_eq_abs, henorm 0, mul_one]
      linarith [norm_nonneg v])
  have ht0 := hterm x 0 (by
      rw [sub_self, norm_zero]; linarith [norm_nonneg v])
  have hres : q (x + v) - q x - (innerSL ℝ (Φ x)) v
      = ((∫ s in (0 : ℝ)..(v 2), Φ (x + v 0 • FiniteTimeSingularity.e 0
            + v 1 • FiniteTimeSingularity.e 1 + s • FiniteTimeSingularity.e 2) 2)
          - (Φ x) 2 * v 2)
        + ((∫ s in (0 : ℝ)..(v 1), Φ (x + v 0 • FiniteTimeSingularity.e 0
            + s • FiniteTimeSingularity.e 1) 1) - (Φ x) 1 * v 1)
        + ((∫ s in (0 : ℝ)..(v 0), Φ (x + s • FiniteTimeSingularity.e 0) 0)
          - (Φ x) 0 * v 0) := by
    rw [hQ, hL]; ring
  set A2 : ℝ := (∫ s in (0 : ℝ)..(v 2), Φ (x + v 0 • FiniteTimeSingularity.e 0
            + v 1 • FiniteTimeSingularity.e 1 + s • FiniteTimeSingularity.e 2) 2)
          - (Φ x) 2 * v 2 with hA2
  set A1 : ℝ := (∫ s in (0 : ℝ)..(v 1), Φ (x + v 0 • FiniteTimeSingularity.e 0
            + s • FiniteTimeSingularity.e 1) 1) - (Φ x) 1 * v 1 with hA1
  set A0 : ℝ := (∫ s in (0 : ℝ)..(v 0), Φ (x + s • FiniteTimeSingularity.e 0) 0)
        - (Φ x) 0 * v 0 with hA0
  calc ‖q (x + v) - q x - (innerSL ℝ (Φ x)) v‖
      = ‖A2 + A1 + A0‖ := by rw [hres]
    _ ≤ ‖A2‖ + ‖A1‖ + ‖A0‖ := by
        linarith [norm_add_le (A2 + A1) A0, norm_add_le A2 A1]
    _ ≤ (c / 3) * |v 2| + (c / 3) * |v 1| + (c / 3) * |v 0| := by linarith [ht2, ht1, ht0]
    _ ≤ (c / 3) * (3 * ‖v‖) := by nlinarith [hc, e0, e1, e2, norm_nonneg v]
    _ = c * ‖v‖ := by ring

end Work.FTS.PressureOn.Weyl
end
-- ===== merged: Submission.Work.FTS.PressureOn.Weyl.tendsto_integral_mul_shift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Weyl

open MeasureTheory Filter

theorem tendsto_integral_mul_shift
    (f g : Work.FTS.PressureOn.R3 → ℝ) (hf : Continuous f)
    (hf0 : Filter.Tendsto f (Filter.cocompact Work.FTS.PressureOn.R3) (nhds 0))
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Filter.Tendsto (fun t : Work.FTS.PressureOn.R3 => ∫ x, f x * g (x - t))
      (Filter.cocompact Work.FTS.PressureOn.R3) (nhds 0) := by
  have hgint : Integrable g := hg.integrable_of_hasCompactSupport hgc
  -- bound for the support of `g`
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ tsupport g, ‖x‖ ≤ M := hgc.isBounded.exists_norm_le
  -- the total mass of `|g|`
  set Cg : ℝ := ∫ x, |g x| with hCg
  have hCgnn : 0 ≤ Cg := by rw [hCg]; exact integral_nonneg fun x => abs_nonneg (g x)
  have hCg1 : 0 < Cg + 1 := by linarith
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε' : ℝ := ε / (Cg + 1) with hε'def
  have hε'pos : 0 < ε' := by rw [hε'def]; exact div_pos hε hCg1
  -- threshold beyond which `|f| ≤ ε'`
  have hmem : {x : Work.FTS.PressureOn.R3 | f x ∈ Metric.ball (0 : ℝ) ε'}
      ∈ Filter.cocompact _ := hf0 (Metric.ball_mem_nhds 0 hε'pos)
  obtain ⟨K, hKc, hKsub⟩ := Filter.mem_cocompact.1 hmem
  obtain ⟨C, hC⟩ := hKc.isBounded.exists_norm_le
  set R : ℝ := C + 1 with hRdef
  have hRfd : ∀ x, R ≤ ‖x‖ → |f x| ≤ ε' := by
    intro x hx
    have hxK : x ∉ K := by
      intro hxK
      have h1 : ‖x‖ ≤ C := hC x hxK
      have h2 : C < R := by rw [hRdef]; linarith
      linarith
    have h : f x ∈ Metric.ball (0 : ℝ) ε' := hKsub (by simpa using hxK)
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at h
    exact le_of_lt h
  -- eventually `‖t‖ ≥ R + M`
  have hfinal : ∀ᶠ t in Filter.cocompact (Work.FTS.PressureOn.R3), R + M ≤ ‖t‖ :=
    tendsto_norm_cocompact_atTop.eventually (Filter.eventually_ge_atTop (R + M))
  refine hfinal.mono ?_
  intro t ht
  have hbound : ‖∫ x, f x * g (x - t)‖ ≤ ε' * Cg := by
    calc ‖∫ x, f x * g (x - t)‖
        ≤ ∫ x, ‖f x * g (x - t)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ε' * |g (x - t)| := by
            apply integral_mono_of_nonneg
            · filter_upwards with x
              simp only [Pi.zero_apply]
              positivity
            · exact (hgint.abs.comp_sub_right t).const_mul ε'
            · filter_upwards with x
              rw [Real.norm_eq_abs, abs_mul]
              by_cases hg0 : g (x - t) = 0
              · rw [hg0, abs_zero, mul_zero, mul_zero]
              · have hsupp : x - t ∈ tsupport g :=
                  subset_tsupport g (by simpa [Function.mem_support] using hg0)
                have hxt : ‖x - t‖ ≤ M := hM _ hsupp
                have hx : R ≤ ‖x‖ := by
                  have htx : x - (x - t) = t := by abel
                  have h : ‖t‖ ≤ ‖x‖ + ‖x - t‖ := by
                    calc ‖t‖ = ‖x - (x - t)‖ := by rw [htx]
                      _ ≤ ‖x‖ + ‖x - t‖ := norm_sub_le x (x - t)
                  linarith
                exact mul_le_mul_of_nonneg_right (hRfd x hx) (abs_nonneg _)
      _ = ε' * Cg := by
            rw [integral_const_mul]
            congr 1
            rw [hCg]
            exact integral_sub_right_eq_self (fun x => |g x|) t
  rw [Real.dist_eq, sub_zero]
  have hlt : ε' * Cg < ε := by
    have h1 : ε' * Cg < ε' * (Cg + 1) := mul_lt_mul_of_pos_left (by linarith) hε'pos
    have h2 : ε' * (Cg + 1) = ε := by rw [hε'def]; field_simp
    linarith
  rw [Real.norm_eq_abs] at hbound
  linarith

end Work.FTS.PressureOn.Weyl
end
-- ===== merged: Submission.Work.FTS.PressureOn.aeStronglyMeasurableAndBoundAtZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.PressureOn

/-- **The time-zero slices inherit the `(0,S]` bound and measurability** (piece of
`tendsto_timeDeriv_physVel`).

If the slices `ω · s`, `s ∈ (0,S]`, are uniformly bounded by `M ≥ 0` and a.e. strongly
measurable, and every curve `s ↦ ω x s` is continuous on `[0,S]`, then the same bound and
measurability hold at `s = 0`.

Recipe: for the bound, `ContinuousOn (fun s => ω x s) (Icc 0 S)` restricts to
`ContinuousWithinAt … (Ioc 0 S) 0`, so `Tendsto (fun s => ω x s) (𝓝[Ioc 0 S] 0) (𝓝 (ω x 0))`
(`ContinuousWithinAt.mono`) and `le_of_tendsto` against the constant bound (which holds on
`Ioc 0 S`) gives `‖ω x 0‖ ≤ M`; the filter is nontrivial because `hS : 0 < S`.  For the
measurability, use the null sequence `s n = S/(n+2) ∈ (0,S]` and
`aestronglyMeasurable_of_tendsto_ae Filter.atTop` with the pointwise convergence
`ω z (s n) → ω z 0` from `hcontω`. -/
theorem aeStronglyMeasurableAndBoundAtZero {ω : R3 → ℝ → R3} {S M : ℝ}
    (hS : 0 < S) (hM : 0 ≤ M)
    (hbdd : ∀ s ∈ Set.Ioc 0 S, ∀ x, ‖ω x s‖ ≤ M)
    (hmeas : ∀ s ∈ Set.Ioc 0 S,
      MeasureTheory.AEStronglyMeasurable (fun z => ω z s) MeasureTheory.volume)
    (hcontω : ∀ x, ContinuousOn (fun s => ω x s) (Set.Icc 0 S)) :
    (∀ x, ‖ω x 0‖ ≤ M) ∧
      MeasureTheory.AEStronglyMeasurable (fun z => ω z 0) MeasureTheory.volume := by
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 S := ⟨le_refl 0, hS.le⟩
  -- the null sequence `s n = S/(n+2)` sits in `(0,S]`, tends to `0` and stays in `[0,S]`
  have hsn_mem : ∀ n : ℕ, S / ((n : ℝ) + 2) ∈ Set.Ioc 0 S := by
    intro n
    refine ⟨div_pos hS (by positivity), ?_⟩
    refine div_le_self hS.le ?_
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hg : Tendsto (fun n : ℕ => (n : ℝ) + 2) Filter.atTop Filter.atTop := by
    simpa [add_comm] using
      (Tendsto.add_atTop (tendsto_const_nhds (x := (2 : ℝ))) tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (2 : ℝ) + (n : ℝ)) Filter.atTop Filter.atTop)
  have hsn_tend : Tendsto (fun n : ℕ => S / ((n : ℝ) + 2)) Filter.atTop
      (𝓝[Set.Icc 0 S] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop hg, ?_⟩
    exact Eventually.of_forall fun n => Set.Ioc_subset_Icc_self (hsn_mem n)
  constructor
  · -- the bound: pass to the limit along `s n → 0` in `‖ω x ·‖ ≤ M`
    intro x
    have hseq : Tendsto (fun n : ℕ => ‖ω x (S / ((n : ℝ) + 2))‖) Filter.atTop
        (𝓝 ‖ω x 0‖) := by
      have h := (((hcontω x) 0 h0mem).tendsto.comp hsn_tend).norm
      simpa only [Function.comp_def] using h
    exact le_of_tendsto_of_tendsto' hseq
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => M) Filter.atTop (𝓝 M))
      (fun n => hbdd _ (hsn_mem n) x)
  · -- the measurability: an a.e. pointwise limit of a.e. strongly measurable maps
    refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun n => hmeas _ (hsn_mem n)) ?_
    refine Eventually.of_forall fun z => ?_
    have h := ((hcontω z) 0 h0mem).tendsto.comp hsn_tend
    simpa only [Function.comp_def] using h

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.ae_coord_ne_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

open MeasureTheory

/-- The coordinate hyperplane `{y : R3 | y i = 0}` is Lebesgue-null: it is the kernel of the
(continuous, surjective) `i`-th coordinate functional `EuclideanSpace.projₗ i`, a strict
submodule of `R3`, and a strict vector subspace of a finite-dimensional real normed space is
null for every additive Haar measure (`MeasureTheory.Measure.addHaar_submodule`). -/
theorem volume_coordHyperplane_eq_zero (i : Fin 3) :
    volume {y : R3 | y i = 0} = 0 := by
  -- the set is the kernel of the `i`-th coordinate functional
  have hset : {y : R3 | y i = 0} =
      (Submodule.comap (EuclideanSpace.projₗ (𝕜 := ℝ) i) (⊥ : Submodule ℝ ℝ) :
        Set R3) := by
    ext y; simp
  rw [hset]
  refine Measure.addHaar_submodule volume _ ?_
  -- the submodule is strict: the `i`-th basis vector is not in it
  intro h
  have hmem : (EuclideanSpace.single i (1 : ℝ) : R3) ∈
      Submodule.comap (EuclideanSpace.projₗ (𝕜 := ℝ) i) (⊥ : Submodule ℝ ℝ) := by
    rw [h]; exact Submodule.mem_top
  simp at hmem

theorem ae_coord_ne_zero : ∀ᵐ y : Work.FTS.PressureOn.R3, y 0 ≠ 0 ∧ y 2 ≠ 0 := by
  have h0 : ∀ᵐ y : R3, y 0 ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using volume_coordHyperplane_eq_zero 0
  have h2 : ∀ᵐ y : R3, y 2 ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using volume_coordHyperplane_eq_zero 2
  filter_upwards [h0, h2] with y hy0 hy2
  exact ⟨hy0, hy2⟩

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.continuousOn_time_omega_of_strips =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter
open scoped Topology NNReal Matrix

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-! ## The curl of a spatial derivative -/

/-- The curl (vorticity) of a continuous linear map `ℝ³ →L[ℝ] ℝ³`, in exactly the form in which
it appears in `FiniteTimeSingularity.vorticity`: `∇×L = ∑ᵢ eᵢ ×₃ (L eᵢ)`. -/
noncomputable def curlOf (L : R3 →L[ℝ] R3) : R3 :=
  WithLp.toLp 2 (∑ i, FiniteTimeSingularity.e i ⨯₃ (L (FiniteTimeSingularity.e i)))

/-- `curlOf` is continuous: it is a finite sum of compositions of the evaluation `L ↦ L eᵢ`
(with `eᵢ` fixed) and of the cross product with the fixed vector `eᵢ`. -/
theorem continuous_curlOf : Continuous curlOf := by
  unfold curlOf
  fun_prop

/-- `FiniteTimeSingularity.vorticity` is `curlOf` applied to the derivative; definitional. -/
theorem vorticity_eq_curlOf (u : R3 → R3) (x : R3) :
    FiniteTimeSingularity.vorticity u x = curlOf (fderiv ℝ u x) := rfl

/-! ## The derivative of a time slice, from a derivative within a set -/

/-- **The derivative of a time slice, from the derivative of the uncurried field within a set.**

If `u.uncurry` has derivative `f'` within `s` at `(x, s₀)`, and the points `(y, s₀)` for `y` near
`x` all lie in `s`, then the slice `y ↦ u y s₀` is differentiable at `x` with derivative the
spatial block `f' ∘SL inl` of `f'`.

This is what makes `ContDiffOn` on a *closed* strip (whose time-boundary `s₀ = 0` is not an
interior point) usable for the spatial derivatives of the boundary slice. -/
theorem hasFDerivAt_slice_of_hasFDerivWithinAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → ℝ → F} {s : Set (E × ℝ)} {x : E} {s₀ : ℝ}
    (hs : ∀ᶠ y in 𝓝 x, (y, s₀) ∈ s) {f' : (E × ℝ) →L[ℝ] F}
    (h : HasFDerivWithinAt (Function.uncurry u) f' s (x, s₀)) :
    HasFDerivAt (fun y => u y s₀) (f' ∘SL ContinuousLinearMap.inl ℝ E ℝ) x := by
  rw [hasFDerivWithinAt_iff_tendsto] at h
  rw [hasFDerivAt_iff_tendsto]
  have hmk0 : Tendsto (fun y : E => (y, s₀)) (𝓝 x) (𝓝 (x, s₀)) := by
    rw [nhds_prod_eq]
    exact tendsto_id.prodMk tendsto_const_nhds
  have hmk : Tendsto (fun y : E => (y, s₀)) (𝓝 x) (𝓝[s] (x, s₀)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hmk0 (by simpa using hs)
  refine (h.comp hmk).congr fun y => ?_
  have hsub : ((y, s₀) : E × ℝ) - (x, s₀) = ((y - x, (0 : ℝ)) : E × ℝ) := by simp
  have hnorm : ‖((y - x, (0 : ℝ)) : E × ℝ)‖ = ‖y - x‖ := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  simp only [Function.comp_apply, Function.uncurry_apply_pair, hsub, hnorm]
  rfl

/-- The product-set form of `hasFDerivAt_slice_of_hasFDerivWithinAt`, for the strips
`univ ×ˢ I` that occur in the workspace. -/
theorem hasFDerivAt_slice_of_hasFDerivWithinAt_prod
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → ℝ → F} {I : Set ℝ} {s₀ : ℝ} (hs₀ : s₀ ∈ I) {x : E}
    {f' : (E × ℝ) →L[ℝ] F}
    (h : HasFDerivWithinAt (Function.uncurry u) f' (Set.univ ×ˢ I) (x, s₀)) :
    HasFDerivAt (fun y => u y s₀) (f' ∘SL ContinuousLinearMap.inl ℝ E ℝ) x :=
  hasFDerivAt_slice_of_hasFDerivWithinAt (s := Set.univ ×ˢ I)
    (Filter.Eventually.of_forall fun _ => Set.mem_prod.mpr ⟨Set.mem_univ _, hs₀⟩) h

/-- **The spatial derivative of a slice, through the derivative within a product set.**  If
`u.uncurry` is `C¹` within `univ ×ˢ I` at `(x, s₀)` and `s₀ ∈ I`, then the spatial derivative of
the slice `y ↦ u y s₀` at `x` is the composition of the derivative within `univ ×ˢ I` with the
inclusion `ℝ³ ↪ ℝ³ × ℝ`. -/
theorem fderiv_slice_eq_fderivWithin_prod {u : R3 → ℝ → R3} {I : Set ℝ} {s₀ : ℝ}
    (hs₀ : s₀ ∈ I) {x : R3}
    (h : ContDiffWithinAt ℝ 1 (Function.uncurry u) (Set.univ ×ˢ I) (x, s₀)) :
    fderiv ℝ (fun y => u y s₀) x
      = fderivWithin ℝ (Function.uncurry u) (Set.univ ×ˢ I) (x, s₀)
          ∘SL ContinuousLinearMap.inl ℝ R3 ℝ := by
  have hd : DifferentiableWithinAt ℝ (Function.uncurry u) (Set.univ ×ˢ I) (x, s₀) :=
    h.differentiableWithinAt one_ne_zero
  exact (hasFDerivAt_slice_of_hasFDerivWithinAt_prod hs₀ hd.hasFDerivWithinAt).fderiv

/-! ## The main statement -/

/-- **Continuity in time of the physical vorticity on the strips.**

If `u = physVel ω` is jointly `C^{1,α}` on `ℝ³ × [0,S']` for every `S' ∈ (0,T)` and the vorticity
of each time slice of `u` is `ω(·,s)`, then for every `x` the function `s ↦ ω x s` is continuous
on `[0,S]` for every `S ∈ (0,T)`. -/
theorem continuousOn_time_omega_of_strips {α : NNReal} {ω : R3 → ℝ → R3} {T S : ℝ}
    (hS : S ∈ Set.Ioo 0 T)
    (hstrips : ∀ S' ∈ Set.Ioo 0 T,
      IsContDiffHolderOn ℝ α (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z s) x = ω x s) :
    ∀ x, ContinuousOn (fun s => ω x s) (Set.Icc 0 S) := by
  intro x
  obtain ⟨hcd, -, -⟩ := hstrips S hS
  -- the strip is a set with nonempty interior in the time direction
  have hU : UniqueDiffOn ℝ ((Set.univ ×ˢ Set.Icc (0 : ℝ) S : Set (R3 × ℝ))) :=
    UniqueDiffOn.prod uniqueDiffOn_univ (uniqueDiffOn_Icc hS.1)
  -- the derivative within the strip is continuous on the strip
  have hcont : ContinuousOn
      (fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
        (Set.univ ×ˢ Set.Icc (0 : ℝ) S)) (Set.univ ×ˢ Set.Icc (0 : ℝ) S) :=
    hcd.continuousOn_fderivWithin hU le_rfl
  -- hence so is its spatial block at the fixed point `x`
  have hslice : ContinuousOn (fun s : ℝ =>
      fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
        (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, s)) (Set.Icc 0 S) :=
    hcont.comp' (by fun_prop : ContinuousOn (fun s : ℝ => (x, s)) (Set.Icc 0 S))
      (fun s hs => ⟨trivial, hs⟩)
  have hclm : ContinuousOn (fun s : ℝ =>
      fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
        (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, s) ∘SL ContinuousLinearMap.inl ℝ R3 ℝ)
      (Set.Icc 0 S) :=
    hslice.clm_comp continuousOn_const
  -- and the curl of the spatial block is `ω`
  refine (continuous_curlOf.comp_continuousOn hclm).congr fun s hs => ?_
  show ω x s = curlOf (fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
        (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, s) ∘SL ContinuousLinearMap.inl ℝ R3 ℝ)
  have hsT : s ∈ Set.Ico 0 T := ⟨hs.1, lt_of_le_of_lt hs.2 hS.2⟩
  have hwit : ContDiffWithinAt ℝ 1 (Function.uncurry (Work.FTS.Physical.physVel ω))
      (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, s) :=
    hcd.contDiffWithinAt ⟨trivial, hs⟩
  rw [← hcurl s hsT x, vorticity_eq_curlOf,
    fderiv_slice_eq_fderivWithin_prod (u := Work.FTS.Physical.physVel ω)
      (I := Set.Icc (0 : ℝ) S) hs hwit]

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.div_smul_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

/-- The product rule for the trace of the Jacobian:
`div (ψ • ω) y = ψ y * div ω y + (fderiv ℝ ψ y) (ω y)`.  This is the trace computation that
underlies `div_smul_eq`; it is stated separately because the identification
`fderiv ℝ ψ y (ω y) = ⟪∇ψ y, ω y⟫` is a second, independent step. -/
lemma div_smul_eq_fderiv {ψ : Work.FTS.PressureOn.R3 → ℝ}
    {ω : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3} {y : Work.FTS.PressureOn.R3}
    (hψ : DifferentiableAt ℝ ψ y) (hω : DifferentiableAt ℝ ω y) :
    FiniteTimeSingularity.div (ψ • ω) y
      = ψ y * FiniteTimeSingularity.div ω y + fderiv ℝ ψ y (ω y) := by
  have hsmul := fderiv_smul (𝕜 := ℝ) hψ hω
  rw [FiniteTimeSingularity.div, FiniteTimeSingularity.div, hsmul]
  rw [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.coe_smulRight]
  rw [map_add, map_smul, LinearMap.trace_smulRight, ContinuousLinearMap.coe_coe]
  ring

theorem div_smul_eq {ψ : Work.FTS.PressureOn.R3 → ℝ} {ω : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3}
    {y : Work.FTS.PressureOn.R3}
    (hψ : DifferentiableAt ℝ ψ y) (hω : DifferentiableAt ℝ ω y) :
    FiniteTimeSingularity.div (ψ • ω) y
      = ψ y * FiniteTimeSingularity.div ω y + inner ℝ (gradient ψ y) (ω y) := by
  rw [div_smul_eq_fderiv hψ hω, inner_gradient_left]

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.exists_bound_strip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

theorem exists_bound_strip {g : R3 → ℝ → R3}
    (hg : Continuous fun p : R3 × ℝ => g p.1 p.2) (R t : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ y ∈ Metric.closedBall (0 : R3) R,
      ∀ s ∈ Set.Icc (t - 1 / 2) (t + 1 / 2), ‖g y s‖ ≤ M := by
  have hcomp : IsCompact (Metric.closedBall (0 : R3) R ×ˢ Set.Icc (t - 1 / 2) (t + 1 / 2)) :=
    (isCompact_closedBall (0 : R3) R).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro y hy s hs
  exact le_trans (hC (y, s) ⟨hy, hs⟩) (le_max_left _ _)

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.hasDerivAt_pressurePotential_time_of_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Metric Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-! ## The kernel `∇Nfund` -/

/-- The pointwise size of the kernel: `‖∇Nfund z‖ = (4π)⁻¹‖z‖⁻²`. -/
theorem norm_nablaNfund (z : R3) : ‖nablaNfund z‖ = (4 * Real.pi)⁻¹ * ‖z‖ ^ (-2 : ℝ) := by
  rw [nablaNfund_eq_neg_newtonGrad, norm_neg, norm_newtonGrad]
  rcases eq_or_lt_of_le (norm_nonneg z) with h | h
  · simp [← h]
  · rw [Real.rpow_neg (norm_nonneg z) (2 : ℝ), Real.rpow_two]
    field_simp

/-- **`‖x - ·‖ ^ (-2)` is integrable on every ball of `ℝ³`** (the kernel is locally integrable in
dimension three; we shift so that the singularity sits at the centre of a ball, and use
`integrableOn_ball_of_norm_le_rpow`). -/
theorem integrableOn_norm_sub_sq_inv_ball (x : R3) (R : ℝ) :
    IntegrableOn (fun y : R3 => ‖x - y‖ ^ (-2 : ℝ)) (ball 0 R) := by
  have hdim : Module.finrank ℝ R3 = 3 := by simp [R3]
  have h1 : IntegrableOn (fun z : R3 => ‖z‖ ^ (-2 : ℝ)) (ball 0 (‖x‖ + R)) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (F := ℝ) (C := 1) (α := 2)
      (r := ‖x‖ + R) (by rw [hdim]; norm_num) (by rw [hdim]; norm_num) ?_ ?_
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _), one_mul]
    · have hfun : (fun z : R3 => ‖z‖ ^ (-2 : ℝ)) = fun z => (‖z‖ ^ (2 : ℕ))⁻¹ := by
        funext z
        rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (norm_nonneg z), Real.rpow_two]
      rw [hfun]
      exact ((continuous_norm.pow 2).measurable.inv).aemeasurable.aestronglyMeasurable
  have h2 : IntegrableOn (fun z : R3 => ‖z‖ ^ (-2 : ℝ)) (ball (-x) R) := by
    refine h1.mono_set (fun z hz => ?_)
    have hz' : ‖z + x‖ < R := by
      rw [mem_ball, dist_eq_norm, sub_neg_eq_add] at hz
      exact hz
    have hlt : ‖z‖ < ‖x‖ + R :=
      calc ‖z‖ = ‖z + x - x‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖z + x‖ + ‖x‖ := norm_sub_le _ _
        _ < R + ‖x‖ := by linarith
        _ = ‖x‖ + R := by ring
    simpa only [mem_ball, dist_zero_right, sub_zero] using hlt
  have hmp : MeasurePreserving (fun z : R3 => z + (-x)) volume volume :=
    measurePreserving_add_right volume (-x)
  have hmb : MeasurableEmbedding (fun z : R3 => z + (-x)) :=
    (Homeomorph.addRight (-x)).measurableEmbedding
  have hpre : (fun z : R3 => z + (-x)) ⁻¹' ball (-x) R = ball 0 R := by
    ext z
    rw [mem_preimage, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm,
      show z + -x - -x = z by abel, sub_zero]
  have hcomp : ((fun z : R3 => ‖z‖ ^ (-2 : ℝ)) ∘ fun z => z + (-x))
      = fun y : R3 => ‖x - y‖ ^ (-2 : ℝ) := by
    funext y
    have h : y + (-x) = -(x - y) := by abel
    rw [Function.comp_apply, h, norm_neg]
  have := (hmp.integrableOn_comp_preimage hmb (f := fun z : R3 => ‖z‖ ^ (-2 : ℝ))
    (s := ball (-x) R)).mpr h2
  rwa [hpre, hcomp] at this

/-- The dominating weight of the differentiation under the integral sign:
`C ‖∇Nfund (x - y)‖` on the closed ball of radius `R`, zero outside.  It is integrable because
`‖∇Nfund (x - ·)‖ ≲ ‖x - ·‖⁻²` is locally integrable in dimension three and the support is
bounded. -/
theorem integrable_indicator_kernelWeight (x : R3) {R C : ℝ} :
    Integrable ((closedBall (0 : R3) R).indicator (fun y => C * ‖nablaNfund (x - y)‖)) := by
  rw [integrable_indicator_iff measurableSet_closedBall]
  have hker : IntegrableOn (fun y : R3 => C * ‖nablaNfund (x - y)‖) (ball 0 (R + 1)) := by
    have h : IntegrableOn (fun y : R3 => (C * (4 * Real.pi)⁻¹) * ‖x - y‖ ^ (-2 : ℝ))
        (ball 0 (R + 1)) := (integrableOn_norm_sub_sq_inv_ball x (R + 1)).const_mul _
    refine IntegrableOn.congr_fun h (fun y _ => ?_) measurableSet_ball
    rw [norm_nablaNfund]
    ring
  refine hker.mono_set (fun y hy => ?_)
  have hy' : ‖y‖ ≤ R := by
    rw [mem_closedBall, dist_eq_norm, sub_zero] at hy
    exact hy
  simpa only [mem_ball, dist_zero_right, sub_zero] using (by linarith : ‖y‖ < R + 1)

/-! ## The corrected differentiation under the integral sign -/

theorem hasDerivAt_pressurePotential_time_of_integrable {f : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (hsupp : ∃ R, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ y, f y s ≠ 0 → ‖y‖ ≤ R)
    (hlip : ∃ C, ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖f y s - f y t‖ ≤ C * |s - t|)
    (hderiv : ∀ y, HasDerivAt (f y) (FiniteTimeSingularity.timeDeriv f y t) t)
    (hInt : ∀ s ∈ Set.Ioo (t - 1) (t + 1),
      Integrable (fun y => inner ℝ (nablaNfund (x - y)) (f y s))) :
    HasDerivAt (fun s => pressurePotential (f · s) x)
      (-∫ y, inner ℝ (nablaNfund (x - y)) (FiniteTimeSingularity.timeDeriv f y t)) t := by
  obtain ⟨R, hR⟩ := hsupp
  obtain ⟨C, hC⟩ := hlip
  -- the neighbourhood of `t` on which all the hypotheses are available
  have htS : t ∈ Set.Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hSnhds : Set.Ioo (t - 1) (t + 1) ∈ 𝓝 t := isOpen_Ioo.mem_nhds htS
  -- the Lipschitz constant is non-negative (test it at `s = t + 1/2`)
  have hCnn : 0 ≤ C := by
    have hhalf : t + 1 / 2 ∈ Set.Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
    have h := hC (0 : R3) (t + 1 / 2) hhalf
    have h2 : |t + 1 / 2 - t| = 1 / 2 := by rw [add_sub_cancel_left, abs_of_pos]; norm_num
    rw [h2] at h
    linarith [norm_nonneg (f 0 (t + 1 / 2) - f 0 t)]
  -- the intermediate objects
  set F : ℝ → R3 → ℝ := fun s y => inner ℝ (nablaNfund (x - y)) (f y s) with hF
  set F' : R3 → ℝ := fun y => inner ℝ (nablaNfund (x - y)) (timeDeriv f y t) with hF'
  set G : ℝ → R3 → ℝ := fun s y => (s - t)⁻¹ • (F s y - F t y) with hG
  set bound : R3 → ℝ :=
    (closedBall (0 : R3) R).indicator (fun y => C * ‖nablaNfund (x - y)‖) with hbound
  have hbound_int : Integrable bound volume := integrable_indicator_kernelWeight x
  -- ## measurability of the difference quotients
  have hG_meas : ∀ᶠ s in 𝓝[≠] t, AEStronglyMeasurable (G s) volume := by
    filter_upwards [nhdsWithin_le_nhds hSnhds] with s hsS
    have h1 : Integrable (F s) volume := hInt s hsS
    have h2 : Integrable (F t) volume := hInt t htS
    exact ((h1.aestronglyMeasurable.sub h2.aestronglyMeasurable).const_smul (s - t)⁻¹)
  -- ## the dominating bound
  have hG_bound : ∀ᶠ s in 𝓝[≠] t, ∀ᵐ y ∂volume, ‖G s y‖ ≤ bound y := by
    filter_upwards [nhdsWithin_le_nhds hSnhds] with s hsS
    refine ae_of_all _ (fun y => ?_)
    by_cases hy : ‖y‖ ≤ R
    · have hyc : y ∈ closedBall (0 : R3) R := by
        rw [mem_closedBall, dist_eq_norm, sub_zero]
        exact hy
      have hby : bound y = C * ‖nablaNfund (x - y)‖ := by
        simp only [hbound, Set.indicator_of_mem hyc]
      rw [hby]
      by_cases hst : s = t
      · subst hst
        simp only [hG, sub_self, inv_zero, zero_smul, norm_zero]
        exact mul_nonneg hCnn (norm_nonneg _)
      · have hpos : 0 < |s - t| := abs_pos.mpr (sub_ne_zero.mpr hst)
        have hle := hC y s hsS
        have hinner : F s y - F t y = inner ℝ (nablaNfund (x - y)) (f y s - f y t) := by
          simp only [hF, inner_sub_right]
        have hGy : G s y = (s - t)⁻¹ • (F s y - F t y) := by simp only [hG]
        have hb : ‖inner ℝ (nablaNfund (x - y)) (f y s - f y t)‖
            ≤ ‖nablaNfund (x - y)‖ * (C * |s - t|) :=
          calc ‖inner ℝ (nablaNfund (x - y)) (f y s - f y t)‖
              ≤ ‖nablaNfund (x - y)‖ * ‖f y s - f y t‖ := norm_inner_le_norm _ _
            _ ≤ ‖nablaNfund (x - y)‖ * (C * |s - t|) :=
                mul_le_mul_of_nonneg_left hle (norm_nonneg _)
        rw [hGy, hinner, norm_smul, Real.norm_eq_abs, abs_inv]
        calc |s - t|⁻¹ * ‖inner ℝ (nablaNfund (x - y)) (f y s - f y t)‖
            ≤ |s - t|⁻¹ * (‖nablaNfund (x - y)‖ * (C * |s - t|)) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ = C * ‖nablaNfund (x - y)‖ := by
              have hsne' : |s - t| ≠ 0 := ne_of_gt hpos
              field_simp
    · have hynot : y ∉ closedBall (0 : R3) R := by
        rw [mem_closedBall, dist_eq_norm, sub_zero]
        exact hy
      have hby : bound y = 0 := by simp only [hbound, Set.indicator_of_notMem hynot]
      have hfs : f y s = 0 := by
        by_contra hne
        exact hy (hR s hsS y hne)
      have hft : f y t = 0 := by
        by_contra hne
        exact hy (hR t htS y hne)
      rw [hby]
      simp only [hG, hF, hfs, hft, inner_zero_right, sub_zero, smul_zero, norm_zero, le_refl]
  -- ## the pointwise limit of the difference quotients
  have hG_lim : ∀ᵐ y ∂volume, Tendsto (fun s => G s y) (𝓝[≠] t) (𝓝 (F' y)) := by
    refine ae_of_all _ (fun y => ?_)
    have hraw : Tendsto (fun s : ℝ => (s - t)⁻¹ • (f y s - f y t)) (𝓝[≠] t)
        (𝓝 (timeDeriv f y t)) := by
      simpa only [slope_def_module] using (show Tendsto (fun s : ℝ => slope (f y) t s) (𝓝[≠] t)
        (𝓝 (timeDeriv f y t)) from (hderiv y).tendsto_slope)
    have hcomp : Tendsto (fun s : ℝ =>
        inner ℝ (nablaNfund (x - y)) ((s - t)⁻¹ • (f y s - f y t))) (𝓝[≠] t)
        (𝓝 (inner ℝ (nablaNfund (x - y)) (timeDeriv f y t))) :=
      (tendsto_const_nhds (x := nablaNfund (x - y)) (f := 𝓝[≠] t)).inner hraw
    refine hcomp.congr' ?_
    filter_upwards with s
    simp only [hG, hF, inner_sub_right, real_inner_smul_right, smul_eq_mul]
  -- ## differentiation under the integral sign
  have hDCT := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[≠] t)
    (F := G) (f := F') bound hG_meas hG_bound hbound_int hG_lim
  -- ## identify the integrals of the difference quotients with the slopes
  have hslope : (fun s => ∫ y, G s y) =ᶠ[𝓝[≠] t] slope (fun s => ∫ y, F s y) t := by
    have hA : Set.Ioo (t - 1) (t + 1) ∈ 𝓝[≠] t := nhdsWithin_le_nhds hSnhds
    filter_upwards [self_mem_nhdsWithin, hA] with s hsne hsS
    have hIs : Integrable (F s) volume := hInt s hsS
    have hIt : Integrable (F t) volume := hInt t htS
    have h1 : (∫ y, G s y) = (s - t)⁻¹ • ∫ y, (F s y - F t y) := by
      simp only [hG, integral_smul]
    have h2 : (∫ y, (F s y - F t y)) = (∫ y, F s y) - ∫ y, F t y := integral_sub hIs hIt
    rw [h1, h2, slope_def_module]
  have hmain : Tendsto (slope (fun s => ∫ y, F s y) t) (𝓝[≠] t) (𝓝 (∫ y, F' y)) :=
    hDCT.congr' hslope
  have hderivF : HasDerivAt (fun s => ∫ y, F s y) (∫ y, F' y) t :=
    hasDerivAt_iff_tendsto_slope.mpr hmain
  have hneg := hderivF.neg
  have hfun : (fun s => pressurePotential (f · s) x) = -fun s => ∫ y, F s y := by
    funext s
    simp only [pressurePotential, hF, Pi.neg_apply]
  rw [hfun]
  simpa only [hF'] using hneg

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.integrable_inner_gradient =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

/-- **Integrability of a continuous field paired with a compactly supported gradient.**

If `ω` is continuous and `ψ` is `C¹` with compact support, then `y ↦ ⟪ω y, ∇ψ y⟫` is integrable:
`∇ψ = 0` off the (compact) support of `ψ`, and on it `ω` is bounded because it is continuous
there.  Concretely, the function is continuous and compactly supported: continuity via
`⟪ω y, ∇ψ y⟫ = fderiv ℝ ψ y (ω y)` (`inner_gradient_right`) and the joint continuity of the
Fréchet derivative of a `C¹` map, compact support via `HasCompactSupport.mono'` and
`gradient_eq` for eventually-equal functions. -/
theorem integrable_inner_gradient {ω : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3}
    {ψ : Work.FTS.PressureOn.R3 → ℝ}
    (hωcont : Continuous ω) (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun y => inner ℝ (ω y) (gradient ψ y)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · -- continuity: rewrite the inner product as the Fréchet derivative applied to `ω`
    have hfderiv : Continuous fun p : R3 × R3 => (fderiv ℝ ψ p.1) p.2 :=
      hψ.continuous_fderiv_apply (by norm_num)
    have hpair : Continuous fun y : R3 => (y, ω y) := continuous_id.prodMk hωcont
    have hcont : Continuous fun y : R3 => (fderiv ℝ ψ y) (ω y) := hfderiv.comp hpair
    refine hcont.congr ?_
    intro y
    rw [inner_gradient_right, starRingEnd_apply, star_trivial]
  · -- compact support: off `tsupport ψ` the gradient vanishes
    refine hψcs.mono' ?_
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hcon
    have h0 : ψ =ᶠ[nhds y] 0 := notMem_tsupport_iff_eventuallyEq.mp hcon
    have hgrad : gradient ψ y = 0 := by
      rw [h0.gradient_eq]
      change gradient (fun _ : R3 => (0 : ℝ)) y = 0
      exact gradient_fun_const y 0
    exact hy (by rw [hgrad, inner_zero_right])

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.integrable_inv_normSq_indicator_closedBall =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Metric
open scoped Topology ENNReal

namespace Work.FTS.PressureOn

/-- In `ℝ³` the function `z ↦ ‖z‖⁻²` is integrable on any ball centred at the origin: the
angular average supplies the factor `r²` that makes `r⁻²` integrable against `dr` in dimension
`3`.  Formally this is the polar-coordinate identity
`MeasureTheory.integrable_fun_norm_addHaar`, which reduces integrability of `f ‖·‖` on `ℝ³` to
integrability of `y ↦ y² * f y` on `(0, ∞)`; for `f y = y⁻² 𝟙_{y ≤ S}` the latter is the
indicator of the finite interval `(0, S]`.  The value `S ≤ 0` is covered as well, the ball then
being null. -/
theorem integrable_inv_normSq_indicator_closedBall (S : ℝ) :
    MeasureTheory.Integrable (fun z : Work.FTS.PressureOn.R3 => (‖z‖ ^ 2)⁻¹ *
      (Metric.closedBall (0 : Work.FTS.PressureOn.R3) S).indicator (fun _ => (1 : ℝ)) z)
      MeasureTheory.volume := by
  -- Step 1: write the integrand as a function of the norm.
  have hEq : (fun z : Work.FTS.PressureOn.R3 => (‖z‖ ^ 2)⁻¹ *
        (Metric.closedBall (0 : Work.FTS.PressureOn.R3) S).indicator (fun _ => (1 : ℝ)) z)
      = fun z : Work.FTS.PressureOn.R3 =>
          (fun y : ℝ => (y ^ 2)⁻¹ * (Set.Iic S).indicator (fun _ => (1 : ℝ)) y) ‖z‖ := by
    funext z
    by_cases h : ‖z‖ ≤ S
    · have hz : z ∈ Metric.closedBall (0 : Work.FTS.PressureOn.R3) S := by
        simpa using h
      simp [hz, h]
    · have hz : z ∉ Metric.closedBall (0 : Work.FTS.PressureOn.R3) S := by
        simpa using h
      simp [hz, h]
  rw [hEq]
  -- Step 2: polar coordinates.
  refine (MeasureTheory.integrable_fun_norm_addHaar (μ := MeasureTheory.volume)
    (f := fun y : ℝ => (y ^ 2)⁻¹ * (Set.Iic S).indicator (fun _ => (1 : ℝ)) y)).mpr ?_
  have hdim : Module.finrank ℝ Work.FTS.PressureOn.R3 = 3 := by simp [Work.FTS.PressureOn.R3]
  -- On `(0, ∞)` the radial weight `y ^ (finrank - 1) = y²` cancels the `y⁻²`.
  have h1 : ∀ y ∈ Set.Ioi (0:ℝ),
      y ^ (Module.finrank ℝ Work.FTS.PressureOn.R3 - 1) •
        ((y ^ 2)⁻¹ * (Set.Iic S).indicator (fun _ => (1 : ℝ)) y)
      = (Set.Iic S).indicator (fun _ => (1 : ℝ)) y := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt hy
    rw [hdim]
    norm_num
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hy0), one_mul]
  rw [MeasureTheory.integrableOn_congr_fun h1 measurableSet_Ioi]
  -- Step 3: `𝟙_{(0,S]}` is integrable, the interval having finite measure.
  have h2 : (Set.Ioi (0:ℝ)).indicator ((Set.Iic S).indicator (fun _ => (1:ℝ)))
      = (Set.Ioc (0:ℝ) S).indicator (fun _ => (1:ℝ)) := by
    ext y
    by_cases hy : y ∈ Set.Ioi (0:ℝ) <;> by_cases hS : y ∈ Set.Iic S <;>
      simp_all [Set.mem_Ioc, Set.mem_Ioi, Set.mem_Iic]
  rw [← MeasureTheory.integrable_indicator_iff measurableSet_Ioi, h2,
      MeasureTheory.integrable_indicator_iff measurableSet_Ioc]
  exact MeasureTheory.integrableOn_const (by simp)

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.joint.majorant_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.joint

/-- **The singular majorant of the Newtonian kernel is integrable.**

The function `z ↦ (4π)⁻¹ ‖z‖⁻²` restricted to the closed ball of radius `S` about the origin is
integrable: in `ℝ³` the singularity `‖z‖⁻²` is exactly at the integrability threshold
(`∫_{‖z‖≤S} ‖z‖⁻² dz = 4π S`), the extra `‖z‖²` in the volume element cancelling the `‖z‖⁻²`.

Proof.  The function is `(closedBall 0 S).indicator (fun z ↦ (4π)⁻¹‖z‖⁻²)`, so it suffices to
integrate the radial function over the closed ball.  Since `closedBall 0 S ⊆ ball 0 (S+1)`, it
suffices to integrate it over the *open* ball, where the polar-coordinate formula
`MeasureTheory.integrableOn_fun_norm_addHaar` applies: it converts integrability of
`x ↦ f ‖x‖` on `ball 0 r` into integrability of `y ↦ y ^ (finrank ℝ ℝ³ - 1) • f y` on
`Ioo 0 r`.  Here `finrank ℝ ℝ³ - 1 = 2`, and `y ^ 2 • ((4π)⁻¹ * (y^2)⁻¹) = (4π)⁻¹` for `y ≠ 0`,
i.e. the reduced integrand is (a.e.) the constant `(4π)⁻¹` on the bounded interval
`Ioo 0 (S+1)`. -/
theorem majorant_integrable (S : ℝ) :
    MeasureTheory.Integrable (fun z : R3 => (4 * Real.pi)⁻¹ * ((‖z‖ ^ 2)⁻¹ *
      (Metric.closedBall (0 : R3) S).indicator (fun _ => (1 : ℝ)) z)) MeasureTheory.volume := by
  -- The integrand is the indicator of the closed ball times the radial kernel.
  have hfun : (fun z : R3 => (4 * Real.pi)⁻¹ * ((‖z‖ ^ 2)⁻¹ *
        (Metric.closedBall (0 : R3) S).indicator (fun _ => (1 : ℝ)) z))
      = (Metric.closedBall (0 : R3) S).indicator
          (fun z : R3 => (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) := by
    funext z
    by_cases hz : z ∈ Metric.closedBall (0 : R3) S
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, mul_one]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero, mul_zero]
  rw [hfun, MeasureTheory.integrable_indicator_iff (Metric.isClosed_closedBall.measurableSet)]
  -- Integrability of the radial kernel on the open ball, via polar coordinates.
  have hball : MeasureTheory.IntegrableOn
      (fun z : R3 => (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) (Metric.ball 0 (S + 1))
      MeasureTheory.volume := by
    have hiff := MeasureTheory.integrableOn_fun_norm_addHaar
      (μ := (MeasureTheory.volume : MeasureTheory.Measure R3))
      (f := fun t : ℝ => (4 * Real.pi)⁻¹ * (t ^ 2)⁻¹) (r := S + 1)
    rw [hiff]
    -- The reduced integrand on `Ioo 0 (S+1)` is the constant `(4π)⁻¹`.
    have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (4 * Real.pi)⁻¹)
        (Set.Ioo 0 (S + 1)) MeasureTheory.volume :=
      MeasureTheory.integrableOn_const (hs := by simp [Real.volume_Ioo])
    refine hconst.congr_fun ?_ measurableSet_Ioo
    intro y hy
    simp only [smul_eq_mul]
    rw [show Module.finrank ℝ R3 - 1 = 2 from by simp [finrank_euclideanSpace]]
    field_simp
    rw [div_self hy.1.ne']
  exact hball.mono_set (fun z hz => by
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    linarith [dist_nonneg (x := z) (y := (0 : R3))])

end Work.FTS.PressureOn.joint
end
-- ===== merged: Submission.Work.FTS.PressureOn.lipschitz_time_of_hasDerivWithinAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

/-- **The one-sided mean value bound on a subinterval.**  If `ω y` is continuous on
`[0,T]` and has right derivative `timeDeriv ω y x` at every `x ∈ [0,T)`, with
`‖timeDeriv ω y x‖ ≤ C` there, then on any subinterval `[a,b] ⊆ [0,T]` (`a ≤ b`) one has
`‖ω y b - ω y a‖ ≤ C (b - a)`.  This is the mean value inequality
`norm_image_sub_le_of_norm_deriv_right_le_segment` applied to the slice `ω y`, the point
being that the derivative hypothesis (available on `Ici x` at each `x ∈ [0,T)`) restricts
to the right-derivative form the MVT needs. -/
theorem norm_time_sub_le_of_mem_Icc {ω : R3 → ℝ → R3} {T C : ℝ}
    (hcont : ∀ y, ContinuousOn (ω y) (Set.Icc 0 T))
    (hderiv : ∀ y, ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω y) (FiniteTimeSingularity.timeDeriv ω y s) (Set.Ici s) s)
    (hbd : ∀ y, ∀ s ∈ Set.Ico 0 T, ‖FiniteTimeSingularity.timeDeriv ω y s‖ ≤ C) :
    ∀ y, ∀ a ∈ Set.Icc 0 T, ∀ b ∈ Set.Icc 0 T,
      a ≤ b → ‖ω y b - ω y a‖ ≤ C * (b - a) := by
  intro y a ha b hb hab
  obtain ⟨ha0, haT⟩ := ha
  obtain ⟨hb0, hbT⟩ := hb
  have hkey : ∀ x ∈ Set.Icc a b, ‖ω y x - ω y a‖ ≤ C * (x - a) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment (f := ω y)
      (f' := FiniteTimeSingularity.timeDeriv ω y) (C := C) (a := a) (b := b)
      ((hcont y).mono (fun x hx => ⟨le_trans ha0 hx.1, le_trans hx.2 hbT⟩))
      (fun x hx => hderiv y x ⟨le_trans ha0 hx.1, lt_of_lt_of_le hx.2 hbT⟩)
      (fun x hx => hbd y x ⟨le_trans ha0 hx.1, lt_of_lt_of_le hx.2 hbT⟩)
  exact hkey b ⟨hab, le_rfl⟩

theorem lipschitz_time_of_hasDerivWithinAt {ω : R3 → ℝ → R3} {T C : ℝ}
    (hcont : ∀ y, ContinuousOn (ω y) (Set.Icc 0 T))
    (hderiv : ∀ y, ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω y) (FiniteTimeSingularity.timeDeriv ω y s) (Set.Ici s) s)
    (hbd : ∀ y, ∀ s ∈ Set.Ico 0 T, ‖FiniteTimeSingularity.timeDeriv ω y s‖ ≤ C) :
    ∀ y, ∀ s ∈ Set.Icc 0 T, ∀ s' ∈ Set.Icc 0 T, ‖ω y s - ω y s'‖ ≤ C * |s - s'| := by
  intro y s hs s' hs'
  rcases le_total s s' with h | h
  · have hkey : ‖ω y s' - ω y s‖ ≤ C * (s' - s) :=
      norm_time_sub_le_of_mem_Icc hcont hderiv hbd y s hs s' hs' h
    rw [show ‖ω y s - ω y s'‖ = ‖ω y s' - ω y s‖ from norm_sub_rev (ω y s) (ω y s'),
      show |s - s'| = s' - s from by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]]
    exact hkey
  · have hkey : ‖ω y s - ω y s'‖ ≤ C * (s - s') :=
      norm_time_sub_le_of_mem_Icc hcont hderiv hbd y s' hs' s hs h
    rw [show |s - s'| = s - s' from abs_of_nonneg (sub_nonneg.mpr h)]
    exact hkey

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.materialDeriv_eq_gradient_sub_cross =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity
open scoped Matrix

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-- **The curl of a linear field as a continuous linear map of its derivative**:
`curlVec D = ∑ᵢ eᵢ × (D eᵢ)`, i.e. `FiniteTimeSingularity.vorticity (fun x => D x)` evaluated
anywhere. -/
noncomputable def curlVec (D : R3 →L[ℝ] R3) : R3 :=
  WithLp.toLp 2 (∑ i : Fin 3, e i ⨯₃ (D (e i)))

/-- The derivative `D : ℝ³ →L[ℝ] ℝ³`, transported to the coordinate space `Fin 3 → ℝ` along the
canonical linear equivalence `WithLp.ofLp`.  By construction
`conjLin D f = (D (WithLp.toLp 2 f)).ofLp`. -/
noncomputable def conjLin (D : R3 →L[ℝ] R3) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap.comp
    (D.toLinearMap.comp (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap)


/-- **The inner product of `R3`-vectors is their coordinatewise sum of products.** -/
theorem inner_eq_sum (x y : R3) : inner ℝ x y = ∑ i : Fin 3, x.ofLp i * y.ofLp i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [RCLike.inner_apply', starRingEnd_apply, star_trivial]

/-- The same, with the first vector written as `WithLp.toLp 2 F`. -/
theorem inner_toLp_left (F : Fin 3 → ℝ) (y : R3) :
    inner ℝ ((WithLp.toLp 2 F : R3)) y = ∑ i, F i * y.ofLp i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [RCLike.inner_apply', starRingEnd_apply, star_trivial]

/-- **The coordinate core of the identity.**  For an abstract linear map `B` on `Fin 3 → ℝ`,
written `M r s := B (Pi.single s 1) r` for its matrix in the standard basis,

`∑ᵣ (p × (∑ᵢ eᵢ × (B eᵢ)))ᵣ qᵣ = ∑ᵣ (B q)ᵣ pᵣ − ∑ᵣ (B p)ᵣ qᵣ`,

the coordinates of `⟪a × curl D, w⟫ = ⟪D w, a⟫ − ⟪D a, w⟫`.  The proof expands `B f r` as the
matrix–vector product `∑ₛ M r s * f s` (from `f = ∑ₛ f s • eₛ` and linearity), computes the curl
`∑ᵢ eᵢ × (B eᵢ) = (M 2 1 − M 1 2, M 0 2 − M 2 0, M 1 0 − M 0 1)`, and closes the resulting
polynomial identity by `ring`. -/
theorem curl_inner_core (B : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (p q : Fin 3 → ℝ) :
    (∑ r : Fin 3,
        crossProduct p (∑ i : Fin 3, crossProduct (Pi.single i (1:ℝ)) (B (Pi.single i (1:ℝ)))) r
          * q r)
      = (∑ r : Fin 3, B q r * p r) - (∑ r : Fin 3, B p r * q r) := by
  set M : Fin 3 → Fin 3 → ℝ := fun r s => B (Pi.single s (1:ℝ)) r with hM
  have hBsing : ∀ s : Fin 3, B (Pi.single s (1:ℝ)) = fun r => M r s := by
    intro s; funext r; rw [hM]
  have hB : ∀ (f : Fin 3 → ℝ) (r : Fin 3), B f r = ∑ s, M r s * f s := by
    intro f r
    have hbasis : f = ∑ s, f s • Pi.single s (1:ℝ) := by
      ext t; simp [Pi.single_apply, Finset.sum_ite_eq]
    conv_lhs => rw [hbasis]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hM]
    ring
  have hc : (∑ i : Fin 3, crossProduct (Pi.single i (1:ℝ)) (B (Pi.single i (1:ℝ))))
      = ![M 2 1 - M 1 2, M 0 2 - M 2 0, M 1 0 - M 0 1] := by
    ext r
    fin_cases r <;> simp [hBsing, Fin.sum_univ_three, cross_apply]
  rw [hc]
  simp only [hB, Fin.sum_univ_three, cross_apply]
  norm_num
  ring

/-- **The derivative of `‖u·‖²/2`.**  If `u` has derivative `D` at `x`, then the derivative of
`y ↦ ‖u y‖²/2` at `x`, evaluated at `w`, is `⟪D w, u x⟫`. -/
theorem fderiv_norm_sq_half_apply {u : R3 → R3} {x : R3} {D : R3 →L[ℝ] R3}
    (hu : HasFDerivAt u D x) (w : R3) :
    fderiv ℝ (fun y => ‖u y‖ ^ 2 / 2) x w = inner ℝ (D w) (u x) := by
  have h1 : HasFDerivAt (fun y => ‖u y‖ ^ 2) (2 • ((innerSL ℝ) (u x) ∘SL D)) x := hu.norm_sq
  have h2 : HasFDerivAt (fun y => ‖u y‖ ^ 2 / 2)
      ((2:ℝ)⁻¹ • (2 • ((innerSL ℝ) (u x) ∘SL D))) x := by
    have := h1.const_mul ((2:ℝ)⁻¹)
    simpa [div_eq_inv_mul] using this
  rw [h2.fderiv]
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, innerSL_apply_apply]
  rw [real_inner_comm (u x) (D w)]
  ring

/-- **The coordinate form of `⟪a × (∇×u), w⟫ = ⟪(Du) w, a⟫ − ⟪(Du) a, w⟫`** for a linear field
with derivative `D`:  `⟪crossVec a (curlVec D), w⟫ = ⟪D w, a⟫ − ⟪D a, w⟫`.

This is `curl_inner_core` transported along `WithLp.ofLp` (the two sides are even definitionally
equal after that transport, which is why the first three steps are `rfl`). -/
theorem inner_crossVec_curlVec (D : R3 →L[ℝ] R3) (a w : R3) :
    inner ℝ (crossVec a (curlVec D)) w = inner ℝ (D w) a - inner ℝ (D a) w := by
  have hcross : crossVec a (curlVec D) = WithLp.toLp 2 (crossProduct a.ofLp
      (∑ i : Fin 3, crossProduct (Pi.single i (1:ℝ)) (conjLin D (Pi.single i (1:ℝ))))) := rfl
  have hDw : D w = WithLp.toLp 2 (conjLin D (w.ofLp)) := rfl
  have hDa : D a = WithLp.toLp 2 (conjLin D (a.ofLp)) := rfl
  rw [hcross, hDw, hDa, inner_toLp_left, inner_toLp_left, inner_toLp_left]
  exact curl_inner_core (conjLin D) a.ofLp w.ofLp

/-- **The material derivative is the gradient of the kinetic energy minus the cross product with
the vorticity**:  `(u·∇)u = ∇(‖u‖²/2) − u × (∇×u)`, i.e.
`fderiv ℝ u x (u x) = gradient (fun y => ‖u y‖²/2) x − crossVec (u x) (vorticity u x)`.

Proved by testing against an arbitrary `w` with `ext_inner_right`: the left side is
`⟪(Du) (u x), w⟫`, the gradient term is `⟪(Du) w, u x⟫` (`inner_gradient_left` +
`fderiv_norm_sq_half_apply`), and the cross-product term is handled by
`inner_crossVec_curlVec`. -/
theorem materialDeriv_eq_gradient_sub_cross {u : R3 → R3} {x : R3}
    (hu : HasFDerivAt u (fderiv ℝ u x) x) :
    fderiv ℝ u x (u x)
      = gradient (fun y => ‖u y‖ ^ 2 / 2) x - crossVec (u x) (FiniteTimeSingularity.vorticity u x) := by
  refine ext_inner_right ℝ fun w => ?_
  rw [inner_sub_left, inner_gradient_left, fderiv_norm_sq_half_apply hu w]
  have hv : FiniteTimeSingularity.vorticity u x = curlVec (fderiv ℝ u x) := rfl
  rw [hv, inner_crossVec_curlVec]
  ring

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.pressurePotential_basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Bornology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-! ## Pointwise bounds for the kernel -/

private lemma inv_pow_three_mul_le (a : ℝ) (ha : 0 ≤ a) : (a ^ 3)⁻¹ * a ≤ (a ^ 2)⁻¹ := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h]; norm_num
  · refine le_of_eq ?_
    field_simp

/-- The pointwise size of the gradient of the fundamental solution:
`‖nablaNfund z‖ ≤ (4π)⁻¹ ‖z‖⁻²` (with the junk value `0` at `z = 0`, where the
inequality is also true). -/
private lemma norm_nablaNfund_le (z : R3) : ‖nablaNfund z‖ ≤ (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := by
  have h : ‖nablaNfund z‖ = ‖newtonGrad z‖ := by
    rw [nablaNfund_eq_neg_newtonGrad, norm_neg]
  rw [h, norm_newtonGrad]
  have h2 : (‖z‖ ^ 3)⁻¹ * ‖z‖ ≤ (‖z‖ ^ 2)⁻¹ := inv_pow_three_mul_le ‖z‖ (norm_nonneg z)
  calc (4 * Real.pi)⁻¹ * (‖z‖ ^ 3)⁻¹ * ‖z‖
      = (4 * Real.pi)⁻¹ * ((‖z‖ ^ 3)⁻¹ * ‖z‖) := by ring
    _ ≤ (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- The kernel is Borel measurable (its only discontinuity is at the origin,
where it is declared to be `0`). -/
private lemma meas_nablaNfund : Measurable (fun z : R3 => nablaNfund z) := by
  unfold nablaNfund
  have h1 : Measurable (fun z : R3 => (4 * Real.pi)⁻¹ * (‖z‖ ^ 3)⁻¹) := by fun_prop
  have h2 : Measurable (fun z : R3 => z) := measurable_id
  exact h1.smul h2

/-- A.e. strong measurability of the integrand of the potential in the shifted
form `z ↦ ⟪∇N z, f (x - z)⟫`. -/
private lemma aeStronglyMeasurable_shifted (f : R3 → R3) (hf : Continuous f) (x : R3) :
    AEStronglyMeasurable (fun z : R3 => inner ℝ (nablaNfund z) (f (x - z))) volume := by
  have hm1 : Measurable (fun z : R3 => nablaNfund z) := meas_nablaNfund
  have hm2 : Measurable (fun z : R3 => f (x - z)) :=
    hf.measurable.comp (continuous_const.sub continuous_id).measurable
  exact (Measurable.inner hm1 hm2).aestronglyMeasurable

/-- A.e. strong measurability of the integrand of the potential in its defining
(unshifted) form `y ↦ ⟪∇N (x - y), f y⟫`. -/
private lemma aeStronglyMeasurable_unshifted (f : R3 → R3) (hf : Continuous f) (x : R3) :
    AEStronglyMeasurable (fun y : R3 => inner ℝ (nablaNfund (x - y)) (f y)) volume := by
  have hm1 : Measurable (fun y : R3 => nablaNfund (x - y)) :=
    meas_nablaNfund.comp (continuous_const.sub continuous_id).measurable
  have hm2 : Measurable (fun y : R3 => f y) := hf.measurable
  exact (Measurable.inner hm1 hm2).aestronglyMeasurable

/-! ## Bounded data: a sup bound and a supporting ball -/

private lemma exists_bound_support {f : R3 → R3} (hf : Continuous f) (hcs : HasCompactSupport f) :
    ∃ M R : ℝ, 0 ≤ M ∧ 0 < R ∧ (∀ y, ‖f y‖ ≤ M) ∧ (∀ y, R ≤ ‖y‖ → f y = 0) := by
  obtain ⟨M₀, hM₀⟩ := hf.bounded_above_of_compact_support hcs
  obtain ⟨R₀, hR₀pos, hR₀⟩ := hcs.isBounded.exists_pos_norm_le
  refine ⟨max M₀ 0, R₀ + 1, le_max_right _ _, by linarith, fun y => ?_, fun y hy => ?_⟩
  · exact le_trans (hM₀ y) (le_max_left _ _)
  · by_contra h
    have hy1 : y ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr h)
    have hy2 := hR₀ y hy1
    linarith

/-- Pointwise domination of the integrand of the potential by the model function
`(4π)⁻¹ M (‖x - y‖²)⁻¹ 1_{ball 0 R} y`, where `M` bounds `‖f‖` and `f` vanishes
outside the ball of radius `R`. -/
private lemma integrand_le {f : R3 → R3} {M R : ℝ} (hbd : ∀ y, ‖f y‖ ≤ M)
    (hsupp : ∀ y, R ≤ ‖y‖ → f y = 0) (x y : R3) :
    ‖inner ℝ (nablaNfund (x - y)) (f y)‖
      ≤ (4 * Real.pi)⁻¹ * M *
          ((‖x - y‖ ^ 2)⁻¹ * (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y) := by
  by_cases hy : y ∈ Metric.ball (0 : R3) R
  · rw [Set.indicator_of_mem hy, mul_one]
    calc ‖inner ℝ (nablaNfund (x - y)) (f y)‖
        ≤ ‖nablaNfund (x - y)‖ * ‖f y‖ := norm_inner_le_norm _ _
      _ ≤ ((4 * Real.pi)⁻¹ * (‖x - y‖ ^ 2)⁻¹) * M :=
          mul_le_mul (norm_nablaNfund_le _) (hbd y) (norm_nonneg _) (by positivity)
      _ = (4 * Real.pi)⁻¹ * M * (‖x - y‖ ^ 2)⁻¹ := by ring
  · rw [Set.indicator_of_notMem hy, mul_zero, mul_zero]
    have hy2 : R ≤ ‖y‖ := by
      rw [Metric.mem_ball, not_lt, dist_eq_norm, sub_zero] at hy; exact hy
    rw [hsupp y hy2]
    simp

/-! ## The shifted form of the potential -/

/-- The change of variables `z = x - y` in the defining integral: the potential
is the convolution of the kernel with `f`, read at `x`. -/
private lemma pressurePotential_eq_shifted (f : R3 → R3) (x : R3) :
    pressurePotential f x = -∫ z, inner ℝ (nablaNfund z) (f (x - z)) := by
  set H : R3 → ℝ := fun z => inner ℝ (nablaNfund z) (f (x - z)) with hH
  have h1 : (fun y => inner ℝ (nablaNfund (x - y)) (f y)) = fun y => H (-(y - x)) := by
    funext y; simp [hH, neg_sub]
  rw [pressurePotential_apply, h1, MeasureTheory.integral_sub_right_eq_self (fun w => H (-w)) x,
    MeasureTheory.integral_neg_eq_self H volume]

/-! ## Continuity -/

/-- Integrability of the singular majorant `‖z‖⁻²` on a ball centred at the
origin (the `L²`-marginal kernel is absolutely integrable at the origin in
dimension `3`). -/
private lemma integrable_kernel_ball_closed (S : ℝ) :
    Integrable (fun z : R3 =>
      (‖z‖ ^ 2)⁻¹ * (Metric.closedBall (0 : R3) S).indicator (fun _ => (1 : ℝ)) z) volume := by
  have h0 : ∀ T : ℝ, IntegrableOn (fun z : R3 => (‖z‖ ^ 2)⁻¹) (Metric.ball (0 : R3) T) := by
    intro T
    refine (MeasureTheory.integrableOn_fun_norm_addHaar (μ := volume)
      (f := fun y : ℝ => (y ^ 2)⁻¹) (r := T)).mpr ?_
    have h3 : Module.finrank ℝ R3 = 3 := by rw [finrank_euclideanSpace_fin]
    rw [h3]
    refine IntegrableOn.congr_fun (f := fun _ : ℝ => (1 : ℝ))
      (integrableOn_const (C := (1 : ℝ)) (measure_Ioo_lt_top.ne)) ?_ measurableSet_Ioo
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt hy.1
    simp only [smul_eq_mul]
    rw [show (3 : ℕ) - 1 = 2 from rfl]
    exact (mul_inv_cancel₀ (pow_ne_zero 2 hy0)).symm
  have hclosed : IntegrableOn (fun z : R3 => (‖z‖ ^ 2)⁻¹) (Metric.closedBall (0 : R3) S) := by
    refine (h0 (max S 0 + 1)).mono_set (fun z hz => ?_)
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    linarith [le_max_left S 0]
  have hInd : Integrable ((Metric.closedBall (0 : R3) S).indicator
      (fun z : R3 => (‖z‖ ^ 2)⁻¹)) volume :=
    (integrable_indicator_iff measurableSet_closedBall).mpr hclosed
  refine hInd.congr ?_
  filter_upwards with z
  by_cases hz : z ∈ Metric.closedBall (0 : R3) S
  · simp [Set.indicator_of_mem hz]
  · simp [Set.indicator_of_notMem hz]

/-- At every point `x₀`, the shifted singular integral is continuous: dominated
convergence for `x` near `x₀`, dominated by the integrable function
`(4π)⁻¹ M ‖z‖⁻² 1_{closedBall 0 (R + ‖x₀‖ + 1)}`. -/
private lemma continuousAt_shifted (f : R3 → R3) (hf : Continuous f)
    (hcs : HasCompactSupport f) (x₀ : R3) :
    ContinuousAt (fun x : R3 => ∫ z, inner ℝ (nablaNfund z) (f (x - z))) x₀ := by
  obtain ⟨M, R, hM, hR, hbd, hsupp⟩ := exists_bound_support hf hcs
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝 x₀)
    (fun z : R3 => (4 * Real.pi)⁻¹ * M * ((‖z‖ ^ 2)⁻¹ *
      (Metric.closedBall (0 : R3) (R + ‖x₀‖ + 1)).indicator (fun _ => (1 : ℝ)) z)) ?_ ?_
    ((integrable_kernel_ball_closed (R + ‖x₀‖ + 1)).const_mul ((4 * Real.pi)⁻¹ * M)) ?_
  · filter_upwards with x
    exact aeStronglyMeasurable_shifted f hf x
  · filter_upwards [Metric.ball_mem_nhds x₀ zero_lt_one] with x hx
    refine Eventually.of_forall fun z => ?_
    by_cases hz : f (x - z) = 0
    · rw [hz, inner_zero_right, norm_zero]
      have hind : 0 ≤ (Metric.closedBall (0 : R3) (R + ‖x₀‖ + 1)).indicator
          (fun _ => (1 : ℝ)) z := Set.indicator_nonneg (fun _ _ => zero_le_one) z
      exact mul_nonneg (mul_nonneg (by positivity) hM) (mul_nonneg (by positivity) hind)
    · have hzR : ‖x - z‖ < R := by
        by_contra h
        exact hz (hsupp (x - z) (not_lt.mp h))
      have hx1 : ‖x‖ ≤ ‖x₀‖ + 1 := by
        rw [Metric.mem_ball, dist_eq_norm] at hx
        have h2 : ‖x‖ = ‖(x - x₀) + x₀‖ := by rw [sub_add_cancel]
        rw [h2]
        linarith [norm_add_le (x - x₀) x₀]
      have hzx : ‖z‖ ≤ R + ‖x₀‖ + 1 := by
        have h2 : ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
        rw [h2]
        have h3 : ‖z - x‖ = ‖x - z‖ := norm_sub_rev z x
        linarith [norm_add_le (z - x) x]
      have hzball : z ∈ Metric.closedBall (0 : R3) (R + ‖x₀‖ + 1) := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hzx
      rw [Set.indicator_of_mem hzball, mul_one]
      calc ‖inner ℝ (nablaNfund z) (f (x - z))‖
          ≤ ‖nablaNfund z‖ * ‖f (x - z)‖ := norm_inner_le_norm _ _
        _ ≤ ((4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) * M :=
            mul_le_mul (norm_nablaNfund_le z) (hbd _) (norm_nonneg _) (by positivity)
        _ = (4 * Real.pi)⁻¹ * M * (‖z‖ ^ 2)⁻¹ := by ring
  · filter_upwards with z
    exact (continuous_const.inner (hf.comp (continuous_id.sub continuous_const))).continuousAt

/-- **The potential is continuous**. -/
private lemma pressurePotential_continuous {f : R3 → R3} (hf : Continuous f)
    (hcs : HasCompactSupport f) : Continuous (pressurePotential f) := by
  have hfun : pressurePotential f = fun x => -∫ z, inner ℝ (nablaNfund z) (f (x - z)) := by
    funext x; exact pressurePotential_eq_shifted f x
  rw [hfun, continuous_iff_continuousAt]
  intro x₀
  exact (continuousAt_shifted f hf hcs x₀).neg

/-! ## The model decay estimate for the kernel -/

/-- **The `L²`-marginal kernel bound.**  For `‖x‖ > 2R` and `y ∈ ball 0 R`,
`‖x - y‖ ≥ ‖x‖ - ‖y‖ ≥ ‖x‖/2`, so `(‖x - y‖²)⁻¹ ≤ 4‖x‖⁻²`; integrating over the
ball gives `∫ (‖x - y‖²)⁻¹ 1_{ball 0 R}(y) ≤ 4‖x‖⁻² vol (ball 0 R)`. -/
private lemma modelDecayBound_aux (R : ℝ) (hR : 0 ≤ R) (x : R3) (hx : 2 * R < ‖x‖) :
    Integrable (fun y : R3 => (‖x - y‖ ^ 2)⁻¹ *
        (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y) volume
      ∧ (∫ y, (‖x - y‖ ^ 2)⁻¹ * (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y)
          ≤ 4 * (‖x‖ ^ 2)⁻¹ * (volume (Metric.ball (0 : R3) R)).toReal := by
  have hxpos : 0 < ‖x‖ := by linarith
  have hxhalf : 0 < ‖x‖ / 2 := by linarith
  have hmeasBall : MeasurableSet (Metric.ball (0 : R3) R) := measurableSet_ball
  have hvolne : volume (Metric.ball (0 : R3) R) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall (0 : R3) R).measure_lt_top.ne
      (measure_mono Metric.ball_subset_closedBall)
  -- on the closed ball the kernel is bounded below by `‖x‖/2`
  have hge : ∀ y ∈ Metric.closedBall (0 : R3) R, ‖x‖ / 2 ≤ ‖x - y‖ := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy
    have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      have h2 : ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      rw [h2]; exact norm_add_le _ _
    linarith
  -- the kernel is continuous on the closed ball, where it never vanishes
  have hcont : ContinuousOn (fun y : R3 => (‖x - y‖ ^ 2)⁻¹) (Metric.closedBall (0 : R3) R) := by
    refine ContinuousOn.inv₀ ((continuous_const.sub continuous_id).norm.pow 2).continuousOn ?_
    intro y hy
    refine pow_ne_zero 2 (ne_of_gt ?_)
    exact lt_of_lt_of_le hxhalf (hge y hy)
  have hIntCB : IntegrableOn (fun y : R3 => (‖x - y‖ ^ 2)⁻¹) (Metric.closedBall (0 : R3) R) :=
    hcont.integrableOn_compact (isCompact_closedBall (0 : R3) R)
  have hIntA : IntegrableOn (fun y : R3 => (‖x - y‖ ^ 2)⁻¹) (Metric.ball (0 : R3) R) :=
    hIntCB.mono_set Metric.ball_subset_closedBall
  have hIndA : Integrable ((Metric.ball (0 : R3) R).indicator
      (fun y : R3 => (‖x - y‖ ^ 2)⁻¹)) volume :=
    (integrable_indicator_iff hmeasBall).mpr hIntA
  have heq : ∀ y : R3, (‖x - y‖ ^ 2)⁻¹ *
        (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y
      = (Metric.ball (0 : R3) R).indicator (fun y : R3 => (‖x - y‖ ^ 2)⁻¹) y := by
    intro y
    by_cases hy : y ∈ Metric.ball (0 : R3) R
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  have hIntModel : Integrable (fun y : R3 => (‖x - y‖ ^ 2)⁻¹ *
      (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y) volume := by
    refine hIndA.congr ?_
    filter_upwards with y
    exact (heq y).symm
  constructor
  · exact hIntModel
  · -- the pointwise bound on the ball
    have hpt : ∀ y : R3, (‖x - y‖ ^ 2)⁻¹ * (Metric.ball (0 : R3) R).indicator
          (fun _ => (1 : ℝ)) y
        ≤ 4 * (‖x‖ ^ 2)⁻¹ * (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y := by
      intro y
      by_cases hy : y ∈ Metric.ball (0 : R3) R
      · rw [Set.indicator_of_mem hy, mul_one, mul_one]
        have h1 : ‖x‖ / 2 ≤ ‖x - y‖ := hge y (Metric.ball_subset_closedBall hy)
        have h2 : (‖x‖ / 2) ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        have hpos : 0 < ‖x - y‖ := lt_of_lt_of_le hxhalf h1
        have h3 : (‖x - y‖ ^ 2)⁻¹ ≤ ((‖x‖ / 2) ^ 2)⁻¹ :=
          (inv_le_inv₀ (pow_pos hpos 2) (pow_pos hxhalf 2)).mpr h2
        have h4 : ((‖x‖ / 2) ^ 2)⁻¹ = 4 * (‖x‖ ^ 2)⁻¹ := by
          field_simp
          ring
        linarith [h3, h4]
      · rw [Set.indicator_of_notMem hy, mul_zero, mul_zero]
    have hConstInt : Integrable (fun y : R3 => 4 * (‖x‖ ^ 2)⁻¹ *
        (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y) volume := by
      have heqc : (fun y : R3 => 4 * (‖x‖ ^ 2)⁻¹ *
            (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y)
          = (Metric.ball (0 : R3) R).indicator (fun _ => 4 * (‖x‖ ^ 2)⁻¹) := by
        funext y
        by_cases hy : y ∈ Metric.ball (0 : R3) R
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy]
      rw [heqc]
      exact (integrable_indicator_iff hmeasBall).mpr
        (integrableOn_const (C := 4 * (‖x‖ ^ 2)⁻¹) hvolne)
    calc ∫ y, (‖x - y‖ ^ 2)⁻¹ * (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y
        ≤ ∫ y, 4 * (‖x‖ ^ 2)⁻¹ *
            (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y :=
          integral_mono hIntModel hConstInt hpt
      _ = 4 * (‖x‖ ^ 2)⁻¹ *
            ∫ y, (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y :=
          integral_const_mul _ _
      _ = 4 * (‖x‖ ^ 2)⁻¹ * (volume (Metric.ball (0 : R3) R)).toReal := by
          rw [integral_indicator hmeasBall, setIntegral_const, Measure.real_def]
          simp only [smul_eq_mul, mul_one]

/-! ## Decay at infinity -/

/-- For `‖x‖ > 2R` the kernel factor is `≤ 4‖x‖⁻²` on the support of `f`, which
gives the quantitative decay of the potential. -/
private lemma pressurePotential_decay {f : R3 → R3} (hf : Continuous f) {M R : ℝ} (hM : 0 ≤ M)
    (hR : 0 ≤ R) (hbd : ∀ y, ‖f y‖ ≤ M) (hsupp : ∀ y, R ≤ ‖y‖ → f y = 0) {x : R3}
    (hx : 2 * R < ‖x‖) :
    |pressurePotential f x| ≤ (4 * Real.pi)⁻¹ * M *
      (4 * (‖x‖ ^ 2)⁻¹ * (volume (Metric.ball (0 : R3) R)).toReal) := by
  obtain ⟨hInt, hBnd⟩ := modelDecayBound_aux R hR x hx
  have hIntL : Integrable (fun y : R3 => ‖inner ℝ (nablaNfund (x - y)) (f y)‖) volume := by
    refine Integrable.mono' (g := fun y : R3 => (4 * Real.pi)⁻¹ * M *
      ((‖x - y‖ ^ 2)⁻¹ * (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y)) ?_ ?_ ?_
    · exact hInt.const_mul _
    · exact (aeStronglyMeasurable_unshifted f hf x).norm
    · filter_upwards with y
      simpa only [Real.norm_eq_abs, abs_abs] using integrand_le hbd hsupp x y
  calc |pressurePotential f x| = |∫ y, inner ℝ (nablaNfund (x - y)) (f y)| := by
        rw [pressurePotential_apply, abs_neg]
    _ ≤ ∫ y, ‖inner ℝ (nablaNfund (x - y)) (f y)‖ := abs_integral_le_integral_abs
    _ ≤ ∫ y, (4 * Real.pi)⁻¹ * M *
          ((‖x - y‖ ^ 2)⁻¹ * (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y) :=
        integral_mono hIntL (hInt.const_mul _) (fun y => integrand_le hbd hsupp x y)
    _ = (4 * Real.pi)⁻¹ * M * ∫ y,
          ((‖x - y‖ ^ 2)⁻¹ * (Metric.ball (0 : R3) R).indicator (fun _ => (1 : ℝ)) y) :=
        integral_const_mul _ _
    _ ≤ (4 * Real.pi)⁻¹ * M *
          (4 * (‖x‖ ^ 2)⁻¹ * (volume (Metric.ball (0 : R3) R)).toReal) :=
        mul_le_mul_of_nonneg_left hBnd (by positivity)

/-- `‖x‖⁻² → 0` along the cocompact filter of `ℝ³`. -/
private lemma tendsto_normSq_inv_cocompact :
    Filter.Tendsto (fun x : R3 => (‖x‖ ^ 2)⁻¹) (Filter.cocompact R3) (nhds 0) := by
  have h1 : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) := Filter.Tendsto.inv_tendsto_atTop tendsto_id
  have h2 : Tendsto (fun t : ℝ => (t⁻¹) ^ 2) atTop (nhds 0) := by
    simpa using h1.pow 2
  have h3 : Tendsto (fun t : ℝ => (t ^ 2)⁻¹) atTop (nhds 0) := by
    simpa only [inv_pow] using h2
  exact h3.comp tendsto_norm_cocompact_atTop

/-- **The potential vanishes at infinity**, at the rate `‖x‖⁻²`. -/
private lemma pressurePotential_tendsto_zero {f : R3 → R3} (hf : Continuous f)
    (hcs : HasCompactSupport f) :
    Filter.Tendsto (pressurePotential f) (Filter.cocompact R3) (nhds 0) := by
  obtain ⟨M, R, hM, hR, hbd, hsupp⟩ := exists_bound_support hf hcs
  have hR0 : 0 ≤ R := le_of_lt hR
  have hev : ∀ᶠ x in Filter.cocompact R3, 2 * R < ‖x‖ :=
    (tendsto_norm_cocompact_atTop (E := R3)).eventually (eventually_gt_atTop (2 * R))
  have hbound : ∀ᶠ x in Filter.cocompact R3,
      |pressurePotential f x|
        ≤ ((4 * Real.pi)⁻¹ * M * (4 * (volume (Metric.ball (0 : R3) R)).toReal))
            * (‖x‖ ^ 2)⁻¹ := by
    filter_upwards [hev] with x hx
    have h := pressurePotential_decay hf hM hR0 hbd hsupp hx
    calc |pressurePotential f x| ≤ (4 * Real.pi)⁻¹ * M *
          (4 * (‖x‖ ^ 2)⁻¹ * (volume (Metric.ball (0 : R3) R)).toReal) := h
      _ = ((4 * Real.pi)⁻¹ * M * (4 * (volume (Metric.ball (0 : R3) R)).toReal))
            * (‖x‖ ^ 2)⁻¹ := by ring
  refine (tendsto_zero_iff_abs_tendsto_zero _).mpr ?_
  refine squeeze_zero' ?_ hbound ?_
  · filter_upwards with x; exact abs_nonneg _
  · simpa using tendsto_normSq_inv_cocompact.const_mul _

/-- **The potential is bounded**: by continuity on the compact ball
`closedBall 0 (2R)`, and by the decay estimate outside it. -/
private lemma pressurePotential_bounded {f : R3 → R3} (hf : Continuous f)
    (hcs : HasCompactSupport f) : ∃ C, ∀ x, |pressurePotential f x| ≤ C := by
  obtain ⟨M, R, hM, hR, hbd, hsupp⟩ := exists_bound_support hf hcs
  have hR0 : 0 ≤ R := le_of_lt hR
  have hcont : Continuous (pressurePotential f) := pressurePotential_continuous hf hcs
  obtain ⟨C₁, hC₁⟩ :=
    (isCompact_closedBall (0 : R3) (2 * R)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C₁ ((4 * Real.pi)⁻¹ * M *
      (4 * (2 * R)⁻¹ ^ 2 * (volume (Metric.ball (0 : R3) R)).toReal)), fun x => ?_⟩
  by_cases hx : x ∈ Metric.closedBall (0 : R3) (2 * R)
  · have h := hC₁ x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · have hx' : 2 * R < ‖x‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
      exact not_le.mp hx
    have h := pressurePotential_decay hf hM hR0 hbd hsupp hx'
    have h2 : (‖x‖ ^ 2)⁻¹ ≤ (2 * R)⁻¹ ^ 2 := by
      have h4 : 0 < 2 * R := by linarith
      have h5 : 2 * R ≤ ‖x‖ := le_of_lt hx'
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by positivity) (inv_anti₀ h4 h5) 2
    calc |pressurePotential f x| ≤ (4 * Real.pi)⁻¹ * M *
          (4 * (‖x‖ ^ 2)⁻¹ * (volume (Metric.ball (0 : R3) R)).toReal) := h
      _ ≤ (4 * Real.pi)⁻¹ * M *
          (4 * ((2 * R)⁻¹ ^ 2) * (volume (Metric.ball (0 : R3) R)).toReal) := by
          gcongr
      _ ≤ max C₁ ((4 * Real.pi)⁻¹ * M *
          (4 * (2 * R)⁻¹ ^ 2 * (volume (Metric.ball (0 : R3) R)).toReal)) := le_max_right _ _

/-! ## The statement -/

theorem pressurePotential_basic {f : R3 → R3} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Continuous (pressurePotential f) ∧ (∃ C, ∀ x, |pressurePotential f x| ≤ C) ∧
      Filter.Tendsto (pressurePotential f) (Filter.cocompact R3) (nhds 0) :=
  ⟨pressurePotential_continuous hf hcs, pressurePotential_bounded hf hcs,
    pressurePotential_tendsto_zero hf hcs⟩

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.timeDeriv_support =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.PressureOn


end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.vorticity_cross_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity
open scoped Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.PressureOn

/-! ## The norm bound and bilinearity of the cross product -/

/-- On `ℝ³ = EuclideanSpace ℝ (Fin 3)` the inner product is the (Euclidean) dot product of the
underlying coordinate functions. -/
private lemma inner_eq_dotProduct (a b : R3) : inner ℝ a b = WithLp.ofLp a ⬝ᵥ WithLp.ofLp b := by
  rw [PiLp.inner_apply, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [RCLike.inner_apply]
  simp [mul_comm]


/-- **The norm bound for the cross product**: `‖a ⨯ b‖ ≤ ‖a‖ ‖b‖`.  It follows from the Binet–Cauchy
identity `(a ⨯ b) ⬝ (a ⨯ b) = (a ⬝ a)(b ⬝ b) - (a ⬝ b)²`. -/
lemma vorticityCross_norm_crossVec_le (a b : R3) : ‖crossVec a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h1 : ‖crossVec a b‖ ^ 2
      = (WithLp.ofLp a ⨯₃ WithLp.ofLp b) ⬝ᵥ (WithLp.ofLp a ⨯₃ WithLp.ofLp b) := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_dotProduct]
    rfl
  have h2 : (WithLp.ofLp a ⨯₃ WithLp.ofLp b) ⬝ᵥ (WithLp.ofLp a ⨯₃ WithLp.ofLp b)
      = (WithLp.ofLp a ⬝ᵥ WithLp.ofLp a) * (WithLp.ofLp b ⬝ᵥ WithLp.ofLp b)
        - (WithLp.ofLp a ⬝ᵥ WithLp.ofLp b) * (WithLp.ofLp b ⬝ᵥ WithLp.ofLp a) :=
    cross_dot_cross _ _ _ _
  have h3 : WithLp.ofLp a ⬝ᵥ WithLp.ofLp a = ‖a‖ ^ 2 := by
    rw [← inner_eq_dotProduct, real_inner_self_eq_norm_sq]
  have h4 : WithLp.ofLp b ⬝ᵥ WithLp.ofLp b = ‖b‖ ^ 2 := by
    rw [← inner_eq_dotProduct, real_inner_self_eq_norm_sq]
  have h5 : (WithLp.ofLp a ⬝ᵥ WithLp.ofLp b) * (WithLp.ofLp b ⬝ᵥ WithLp.ofLp a) =
      (inner ℝ a b) ^ 2 := by
    rw [dotProduct_comm (WithLp.ofLp b), ← inner_eq_dotProduct a b]
    ring
  have h6 : ‖crossVec a b‖ ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by
    rw [h1, h2, h3, h4, h5]
    nlinarith [sq_nonneg (inner ℝ a b)]
  have h7 : ‖crossVec a b‖ ≤ Real.sqrt ((‖a‖ * ‖b‖) ^ 2) :=
    (Real.le_sqrt (by positivity) (by positivity)).2 h6
  rwa [Real.sqrt_sq (by positivity)] at h7

/-- **The cross product is a bounded bilinear map** on `ℝ³`.  (The only non-formal ingredient is the
norm bound `vorticityCross_norm_crossVec_le`; the algebraic laws are those of `crossProduct`.) -/
lemma vorticityCross_isBoundedBilinearMap :
    IsBoundedBilinearMap ℝ (fun p : R3 × R3 => crossVec p.1 p.2) where
  add_left x₁ x₂ y := by
    change WithLp.toLp 2 (WithLp.ofLp (x₁ + x₂) ⨯₃ WithLp.ofLp y)
      = WithLp.toLp 2 (WithLp.ofLp x₁ ⨯₃ WithLp.ofLp y)
        + WithLp.toLp 2 (WithLp.ofLp x₂ ⨯₃ WithLp.ofLp y)
    rw [WithLp.ofLp_add, map_add, LinearMap.add_apply, WithLp.toLp_add]
  smul_left c x y := by
    change WithLp.toLp 2 ((c • WithLp.ofLp x) ⨯₃ WithLp.ofLp y)
      = c • WithLp.toLp 2 (WithLp.ofLp x ⨯₃ WithLp.ofLp y)
    rw [map_smul, LinearMap.smul_apply, WithLp.toLp_smul]
  add_right x y₁ y₂ := by
    change WithLp.toLp 2 (WithLp.ofLp x ⨯₃ WithLp.ofLp (y₁ + y₂))
      = WithLp.toLp 2 (WithLp.ofLp x ⨯₃ WithLp.ofLp y₁)
        + WithLp.toLp 2 (WithLp.ofLp x ⨯₃ WithLp.ofLp y₂)
    rw [WithLp.ofLp_add, map_add, WithLp.toLp_add]
  smul_right c x y := by
    change WithLp.toLp 2 (WithLp.ofLp x ⨯₃ (c • WithLp.ofLp y))
      = c • WithLp.toLp 2 (WithLp.ofLp x ⨯₃ WithLp.ofLp y)
    rw [map_smul, WithLp.toLp_smul]
  bound := ⟨1, one_pos, fun x y => by rw [one_mul]; exact vorticityCross_norm_crossVec_le x y⟩

/-! ## The derivative of a pointwise cross product -/

/-- **Product rule for the cross product**: at a point where `u` and `ω` are differentiable, the
derivative of `y ↦ u y ⨯ ω y` in the direction `e i` is
`(fderiv u x (e i)) ⨯ ω x + u x ⨯ (fderiv ω x (e i))`. -/
lemma vorticityCross_fderiv_crossVec_apply {u ω : R3 → R3} {x : R3} (i : Fin 3)
    (hu : HasFDerivAt u (fderiv ℝ u x) x) (hω : HasFDerivAt ω (fderiv ℝ ω x) x) :
    fderiv ℝ (fun y => crossVec (u y) (ω y)) x (e i)
      = crossVec (fderiv ℝ u x (e i)) (ω x) + crossVec (u x) (fderiv ℝ ω x (e i)) := by
  have hB := vorticityCross_isBoundedBilinearMap
  have hpair : HasFDerivAt (fun y => (u y, ω y))
      ((fderiv ℝ u x).prod (fderiv ℝ ω x)) x := hu.prodMk hω
  have hcomp := (hB.hasFDerivAt (u x, ω x)).comp x hpair
  have hf : fderiv ℝ (fun y => crossVec (u y) (ω y)) x
      = (hB.deriv (u x, ω x)).comp ((fderiv ℝ u x).prod (fderiv ℝ ω x)) := by
    show fderiv ℝ ((fun p : R3 × R3 => crossVec p.1 p.2) ∘ fun y => (u y, ω y)) x = _
    rw [hcomp.fderiv]
  rw [hf, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    IsBoundedBilinearMap.deriv_apply]
  rw [add_comm]

/-! ## The standard basis `e` of `ℝ³` -/

/-- The vector `e i` is the `i`-th basis vector: dotting with it is taking the `i`-th coordinate. -/
private lemma dot_e_left (i : Fin 3) (w : Fin 3 → ℝ) : WithLp.ofLp (e i) ⬝ᵥ w = w i := by
  rw [FiniteTimeSingularity.e, WithLp.ofLp_toLp, dotProduct]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The right version of `dot_e_left`. -/
private lemma dot_e_right (i : Fin 3) (v : Fin 3 → ℝ) : v ⬝ᵥ WithLp.ofLp (e i) = v i := by
  rw [dotProduct_comm, dot_e_left]

/-- The basis expansion `v = ∑ i, (v i) • e i` in `ℝ³`. -/
lemma vorticityCross_sum_smul_e (v : R3) : ∑ i : Fin 3, (v i) • e i = v := by
  rw [WithLp.ext_iff]
  have h := Module.Basis.sum_repr (Pi.basisFun ℝ (Fin 3)) (WithLp.ofLp v)
  simp only [Pi.basisFun_apply, Pi.basisFun_repr] at h
  simpa only [WithLp.ofLp_sum, WithLp.ofLp_smul, FiniteTimeSingularity.e,
    WithLp.ofLp_toLp] using h

/-- A linear map is the sum of its diagonal matrix entries in the basis `e`. -/
lemma vorticityCross_fderiv_apply_sum_smul (L : R3 →L[ℝ] R3) (v : R3) :
    L v = ∑ i : Fin 3, (v i) • L (e i) := by
  conv_lhs => rw [← vorticityCross_sum_smul_e v]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])

/-! ## Divergence as the sum of the diagonal entries -/

/-- The basis `e 0, e 1, e 2` of `ℝ³` (whose coordinates are the coordinate functions). -/
noncomputable def vorticityCross_eBasis : Module.Basis (Fin 3) ℝ R3 :=
  Module.Basis.ofEquivFun (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ))

/-- `vorticityCross_eBasis` is the standard basis `e`. -/
lemma vorticityCross_eBasis_apply (i : Fin 3) : vorticityCross_eBasis i = e i := by
  simp only [vorticityCross_eBasis, Module.Basis.coe_ofEquivFun, FiniteTimeSingularity.e]
  rfl

/-- The coordinates of a vector in `vorticityCross_eBasis` are its coordinates. -/
lemma vorticityCross_eBasis_repr (v : R3) (i : Fin 3) : vorticityCross_eBasis.repr v i = v i := by
  rw [vorticityCross_eBasis, Module.Basis.ofEquivFun_repr_apply]
  rfl

/-- **The divergence is the sum of the diagonal entries of the derivative**: for the standard basis
`e` of `ℝ³`, `div g x = ∑ i, (fderiv ℝ g x (e i)) i`. -/
lemma vorticityCross_div_eq_sum_diag (g : R3 → R3) (x : R3) :
    div g x = ∑ i : Fin 3, (fderiv ℝ g x (e i)) i := by
  rw [div, LinearMap.trace_eq_matrix_trace ℝ vorticityCross_eBasis, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, vorticityCross_eBasis_apply,
    vorticityCross_eBasis_repr]
  rfl

/-! ## The identity `curl (u ⨯ ω) = (div ω) u - (div u) ω + (ω · ∇)u - (u · ∇)ω` -/

theorem vorticity_cross_eq {u ω : R3 → R3} {x : R3}
    (hu : HasFDerivAt u (fderiv ℝ u x) x) (hω : HasFDerivAt ω (fderiv ℝ ω x) x) :
    FiniteTimeSingularity.vorticity (fun y => crossVec (u y) (ω y)) x
      = FiniteTimeSingularity.div ω x • u x - FiniteTimeSingularity.div u x • ω x
        + fderiv ℝ u x (ω x) - fderiv ℝ ω x (u x) := by
  have hd : ∀ i : Fin 3, fderiv ℝ (fun y => crossVec (u y) (ω y)) x (e i)
      = crossVec (fderiv ℝ u x (e i)) (ω x) + crossVec (u x) (fderiv ℝ ω x (e i)) :=
    fun i => vorticityCross_fderiv_crossVec_apply i hu hω
  have hL : WithLp.ofLp (vorticity (fun y => crossVec (u y) (ω y)) x)
      = ∑ i : Fin 3, WithLp.ofLp (e i) ⨯₃
          WithLp.ofLp (fderiv ℝ (fun y => crossVec (u y) (ω y)) x (e i)) := by
    rw [FiniteTimeSingularity.vorticity]
  have hstep : (∑ i : Fin 3, WithLp.ofLp (e i) ⨯₃
          WithLp.ofLp (fderiv ℝ (fun y => crossVec (u y) (ω y)) x (e i)))
      = ∑ i : Fin 3, ( (WithLp.ofLp (ω x) i) • WithLp.ofLp (fderiv ℝ u x (e i))
        - (WithLp.ofLp (fderiv ℝ u x (e i)) i) • WithLp.ofLp (ω x)
        + (WithLp.ofLp (fderiv ℝ ω x (e i)) i) • WithLp.ofLp (u x)
        - (WithLp.ofLp (u x) i) • WithLp.ofLp (fderiv ℝ ω x (e i)) ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hd i]
    change WithLp.ofLp (e i) ⨯₃
        (WithLp.ofLp (fderiv ℝ u x (e i)) ⨯₃ WithLp.ofLp (ω x)
          + WithLp.ofLp (u x) ⨯₃ WithLp.ofLp (fderiv ℝ ω x (e i)))
      = _
    rw [map_add, cross_cross_eq_smul_sub_smul', cross_cross_eq_smul_sub_smul',
      dot_e_left, dot_e_right, dot_e_right, dot_e_left]
    abel
  have hs1 : (∑ i : Fin 3, (WithLp.ofLp (ω x) i) • WithLp.ofLp (fderiv ℝ u x (e i)))
      = WithLp.ofLp (fderiv ℝ u x (ω x)) := by
    rw [show (∑ i : Fin 3, (WithLp.ofLp (ω x) i) • WithLp.ofLp (fderiv ℝ u x (e i)))
          = WithLp.ofLp (∑ i : Fin 3, (WithLp.ofLp (ω x) i) • fderiv ℝ u x (e i)) from by
        rw [WithLp.ofLp_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [WithLp.ofLp_smul])]
    rw [vorticityCross_fderiv_apply_sum_smul (fderiv ℝ u x) (ω x)]
  have hs2 : (∑ i : Fin 3, (WithLp.ofLp (fderiv ℝ u x (e i)) i) • WithLp.ofLp (ω x))
      = WithLp.ofLp (div u x • ω x) := by
    rw [← Finset.sum_smul, ← vorticityCross_div_eq_sum_diag u x, ← WithLp.ofLp_smul]
  have hs3 : (∑ i : Fin 3, (WithLp.ofLp (fderiv ℝ ω x (e i)) i) • WithLp.ofLp (u x))
      = WithLp.ofLp (div ω x • u x) := by
    rw [← Finset.sum_smul, ← vorticityCross_div_eq_sum_diag ω x, ← WithLp.ofLp_smul]
  have hs4 : (∑ i : Fin 3, (WithLp.ofLp (u x) i) • WithLp.ofLp (fderiv ℝ ω x (e i)))
      = WithLp.ofLp (fderiv ℝ ω x (u x)) := by
    rw [show (∑ i : Fin 3, (WithLp.ofLp (u x) i) • WithLp.ofLp (fderiv ℝ ω x (e i)))
          = WithLp.ofLp (∑ i : Fin 3, (WithLp.ofLp (u x) i) • fderiv ℝ ω x (e i)) from by
        rw [WithLp.ofLp_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [WithLp.ofLp_smul])]
    rw [vorticityCross_fderiv_apply_sum_smul (fderiv ℝ ω x) (u x)]
  have key : WithLp.ofLp (vorticity (fun y => crossVec (u y) (ω y)) x)
      = WithLp.ofLp ((fderiv ℝ u x (ω x) - div u x • ω x) + div ω x • u x
          - fderiv ℝ ω x (u x)) := by
    rw [hL, hstep, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      hs1, hs2, hs3, hs4]
    rw [WithLp.ofLp_sub, WithLp.ofLp_add, WithLp.ofLp_sub]
  have hkey := congrArg (WithLp.toLp 2) key
  simp only [WithLp.toLp_ofLp] at hkey
  rw [hkey]
  abel

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.weakCurl.int2_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the second weak-curl pairing

This file proves `Work.FTS.PressureOn.weakCurl.int2_integrable`, the measure-theoretic input of the
weak-curl identity `weakCurl_pair`:

> `x ↦ ⟪∂u(·,t)|ₓ (ω x t) − ∂ω(·,t)|ₓ (u x t), A x⟫` is integrable,

for `A` of class `C^∞` with compact support, `u(·,s)` of class `C¹` and `ω(·,t)` continuous, and
the Jacobian `Dω(·,t)` locally integrable.

## Route

The whole integrand `F` is supported in `tsupport A` (it is `⟪…, A x⟫`, so it vanishes where `A`
does), a compact set, so it suffices to dominate it there by a locally integrable function — the
task of the helper `integrable_of_support_subset_compact_of_bound` below.

* The first summand `∂u(·,t)|ₓ (ω x t)` is bounded on the compact `tsupport A`, because `D(u(·,t))`
  is *continuous* (`u(·,t) ∈ C¹`) and `ω(·,t)` is continuous.
* The second summand `∂ω(·,t)|ₓ (u x t)` is not bounded, but on the compact `tsupport A` it is
  dominated by `‖∂ω(·,t)|ₓ‖ · sup ‖u(·,t)‖`, and `‖∂ω(·,t)‖` is locally integrable (hypothesis
  `hωint`), hence integrable over the compact `tsupport A`.
* Almost-everywhere strong measurability of `F` is obtained from
  `LocallyIntegrable.aestronglyMeasurable` for `Dω(·,t)`, continuity of `u(·,t)`, `ω(·,t)`, `A`, and
  continuity of the application map `(L, v) ↦ L v` and of the inner product.

No use is made of `hR` (the uniform support of `ω(·,s)` in `s`) or of `hωdiff` (the differentiability
of `ω(·,t)` off the axis and the plane): the statement only needs `Dω(·,t)` to be locally integrable.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace Work.FTS.PressureOn.weakCurl

/-- **A function supported in a compact set and dominated by a locally integrable function is
integrable.**  If `f : ℝ³ → ℝ` vanishes off the compact `K`, is a.e. strongly measurable, and is
bounded on `K` by `C * (‖g‖ + 1)` for some locally integrable `g` and some constant `C`, then `f` is
integrable.  (No sign condition on `C` is needed: the bound is only used on `K`.) -/
lemma integrable_of_support_subset_compact_of_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : R3 → ℝ} {g : R3 → E} {K : Set R3} (hK : IsCompact K)
    (hf : ∀ x, x ∉ K → f x = 0) (hfm : AEStronglyMeasurable f)
    (hgl : MeasureTheory.LocallyIntegrable g) {C : ℝ}
    (hbd : ∀ x ∈ K, ‖f x‖ ≤ C * (‖g x‖ + 1)) : MeasureTheory.Integrable f := by
  have hbase : IntegrableOn (fun x => C * (‖g x‖ + 1)) K :=
    ((hgl.integrableOn_isCompact hK).norm.add
      (integrableOn_const (μ := volume) (s := K) hK.measure_ne_top)).const_mul C
  have hgi : Integrable (K.indicator (fun x => C * (‖g x‖ + 1))) :=
    (integrable_indicator_iff hK.measurableSet).mpr hbase
  refine hgi.mono' hfm ?_
  filter_upwards with x
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]; exact hbd x hx
  · rw [hf x hx, norm_zero, Set.indicator_of_notMem hx]

-- `hR` and `hωdiff` are part of the requested statement but not needed by the proof (see the
-- module docstring); silence the "unused variable" linter rather than touch the statement.
set_option linter.unusedVariables false in
theorem int2_integrable {u ω : R3 → ℝ → R3} {t : ℝ} {A : R3 → R3}
    (hA : ∀ n : ℕ, ContDiff ℝ n A) (hAcs : HasCompactSupport A)
    (hR : ∃ R : ℝ, 0 ≤ R ∧ ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R)
    (hsnbhd : ∀ s ∈ Set.Ioo (t - 1) (t + 1), ContDiff ℝ 1 (u · s))
    (hωcont : Continuous (fun x => ω x t))
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt (fun x => ω x t) (fderiv ℝ (ω · t) x) x)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ (ω · t) x)) :
    MeasureTheory.Integrable (fun x => inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
      - fderiv ℝ (fun y => ω y t) x (u x t)) (A x)) := by
  have ht : t ∈ Set.Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hu : ContDiff ℝ 1 (fun y => u y t) := hsnbhd t ht
  have hu_cont : Continuous (fun x => u x t) := hu.continuous
  have hu_fd : Continuous (fun x => fderiv ℝ (fun y => u y t) x) :=
    hu.continuous_fderiv (by norm_num)
  have hA_cont : Continuous A := contDiff_zero.mp (hA 0)
  have hK : IsCompact (tsupport A) := hAcs
  -- a.e. strong measurability: the application map and the inner product are continuous
  have hae : AEStronglyMeasurable (fun x => inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
      - fderiv ℝ (fun y => ω y t) x (u x t)) (A x)) := by
    have happ : Continuous (fun p : (R3 →L[ℝ] R3) × R3 => p.1 p.2) :=
      continuous_fst.clm_apply continuous_snd
    have hT1 : AEStronglyMeasurable (fun x => fderiv ℝ (fun y => u y t) x (ω x t)) :=
      happ.comp_aestronglyMeasurable
        (hu_fd.aestronglyMeasurable.prodMk hωcont.aestronglyMeasurable)
    have hDω : AEStronglyMeasurable (fun x => fderiv ℝ (fun y => ω y t) x) :=
      hωint.aestronglyMeasurable
    have hT2 : AEStronglyMeasurable (fun x => fderiv ℝ (fun y => ω y t) x (u x t)) :=
      happ.comp_aestronglyMeasurable (hDω.prodMk hu_cont.aestronglyMeasurable)
    have hT : AEStronglyMeasurable (fun x => fderiv ℝ (fun y => u y t) x (ω x t)
        - fderiv ℝ (fun y => ω y t) x (u x t)) := hT1.sub hT2
    have hpair : AEStronglyMeasurable (fun x => (fderiv ℝ (fun y => u y t) x (ω x t)
        - fderiv ℝ (fun y => ω y t) x (u x t), A x)) :=
      hT.prodMk hA_cont.aestronglyMeasurable
    exact (continuous_inner (𝕜 := ℝ)).comp_aestronglyMeasurable hpair
  -- the integrand vanishes off the (compact) support of `A`
  have hsupp : ∀ x, x ∉ tsupport A → inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
      - fderiv ℝ (fun y => ω y t) x (u x t)) (A x) = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := A) hx, inner_zero_right]
  -- the bounds on the compact support of `A`
  obtain ⟨Cd, hCd0⟩ := IsCompact.exists_bound_of_continuousOn hK hu_fd.continuousOn
  obtain ⟨Cw, hCw0⟩ := IsCompact.exists_bound_of_continuousOn hK hωcont.continuousOn
  obtain ⟨Cu, hCu0⟩ := IsCompact.exists_bound_of_continuousOn hK hu_cont.continuousOn
  obtain ⟨Ca, hCa0⟩ := IsCompact.exists_bound_of_continuousOn hK hA_cont.continuousOn
  have hbd : ∀ x ∈ tsupport A, ‖inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
      - fderiv ℝ (fun y => ω y t) x (u x t)) (A x)‖
      ≤ (max 0 Cd * max 0 Cw * max 0 Ca + max 0 Cu * max 0 Ca)
        * (‖fderiv ℝ (fun y => ω y t) x‖ + 1) := by
    intro x hx
    have hd : ‖fderiv ℝ (fun y => u y t) x‖ ≤ max 0 Cd :=
      le_trans (hCd0 x hx) (le_max_right _ _)
    have hw : ‖ω x t‖ ≤ max 0 Cw := le_trans (hCw0 x hx) (le_max_right _ _)
    have hU : ‖u x t‖ ≤ max 0 Cu := le_trans (hCu0 x hx) (le_max_right _ _)
    have ha : ‖A x‖ ≤ max 0 Ca := le_trans (hCa0 x hx) (le_max_right _ _)
    have h1 : 0 ≤ max 0 Cd := le_max_left _ _
    have h2 : 0 ≤ max 0 Cw := le_max_left _ _
    have h3 : 0 ≤ max 0 Cu := le_max_left _ _
    have h4 : 0 ≤ max 0 Ca := le_max_left _ _
    have hD0 : 0 ≤ ‖fderiv ℝ (fun y => ω y t) x‖ := norm_nonneg _
    have hA0 : 0 ≤ ‖A x‖ := norm_nonneg _
    have step1 : ‖inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
          - fderiv ℝ (fun y => ω y t) x (u x t)) (A x)‖
        ≤ (‖fderiv ℝ (fun y => u y t) x (ω x t)‖
            + ‖fderiv ℝ (fun y => ω y t) x (u x t)‖) * ‖A x‖ := by
      refine le_trans (norm_inner_le_norm _ _) ?_
      exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) hA0
    have step2 : (‖fderiv ℝ (fun y => u y t) x (ω x t)‖
            + ‖fderiv ℝ (fun y => ω y t) x (u x t)‖) * ‖A x‖
        ≤ (max 0 Cd * max 0 Cw + max 0 Cu * ‖fderiv ℝ (fun y => ω y t) x‖)
          * max 0 Ca := by
      apply mul_le_mul
      · refine add_le_add ?_ ?_
        · calc ‖(fderiv ℝ (fun y => u y t) x) (ω x t)‖
              ≤ ‖fderiv ℝ (fun y => u y t) x‖ * ‖ω x t‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ max 0 Cd * max 0 Cw := mul_le_mul hd hw (norm_nonneg _) h1
        · calc ‖fderiv ℝ (fun y => ω y t) x (u x t)‖
              ≤ ‖fderiv ℝ (fun y => ω y t) x‖ * ‖u x t‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ ‖fderiv ℝ (fun y => ω y t) x‖ * max 0 Cu := mul_le_mul_of_nonneg_left hU hD0
            _ = max 0 Cu * ‖fderiv ℝ (fun y => ω y t) x‖ := by ring
      · exact ha
      · exact hA0
      · exact add_nonneg (mul_nonneg h1 h2) (mul_nonneg h3 hD0)
    have step3 : (max 0 Cd * max 0 Cw + max 0 Cu * ‖fderiv ℝ (fun y => ω y t) x‖)
          * max 0 Ca
        ≤ (max 0 Cd * max 0 Cw * max 0 Ca + max 0 Cu * max 0 Ca)
          * (‖fderiv ℝ (fun y => ω y t) x‖ + 1) := by
      have hX : max 0 Cd * max 0 Cw * max 0 Ca
          ≤ max 0 Cd * max 0 Cw * max 0 Ca + max 0 Cu * max 0 Ca :=
        le_add_of_nonneg_right (mul_nonneg h3 h4)
      have hY : max 0 Cu * max 0 Ca
          ≤ max 0 Cd * max 0 Cw * max 0 Ca + max 0 Cu * max 0 Ca :=
        le_add_of_nonneg_left (mul_nonneg (mul_nonneg h1 h2) h4)
      have hYD : ‖fderiv ℝ (fun y => ω y t) x‖ * (max 0 Cu * max 0 Ca)
          ≤ ‖fderiv ℝ (fun y => ω y t) x‖
            * (max 0 Cd * max 0 Cw * max 0 Ca + max 0 Cu * max 0 Ca) :=
        mul_le_mul_of_nonneg_left hY hD0
      have hsum : (max 0 Cd * max 0 Cw + max 0 Cu * ‖fderiv ℝ (fun y => ω y t) x‖)
            * max 0 Ca
          = max 0 Cd * max 0 Cw * max 0 Ca
            + ‖fderiv ℝ (fun y => ω y t) x‖ * (max 0 Cu * max 0 Ca) := by ring
      rw [hsum]
      nlinarith [hX, hYD, hD0]
    linarith
  exact integrable_of_support_subset_compact_of_bound hK hsupp hae hωint hbd

end Work.FTS.PressureOn.weakCurl
end

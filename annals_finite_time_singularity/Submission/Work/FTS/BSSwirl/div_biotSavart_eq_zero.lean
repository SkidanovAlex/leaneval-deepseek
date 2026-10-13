/-
# `div (BS ω) = 0` — the divergence half of the Biot–Savart law

This module proves the second half of item 7a of the lead's design (`FTS_PHYS_BRIDGE.md` §1):

  `div (biotSavart ω) = 0`  everywhere on `ℝ³`,

for a vorticity `ω` that is bounded, supported in `closedBall 0 R`, ae-strongly-measurable and
Hölder of some positive exponent `α` (the classical compactly supported `L^∞ ∩ C^{0,α}` setting of
the Calderón–Zygmund chapter).

## The idea

The Biot–Savart field of such a vorticity is `C¹` (`Work.CoreResiduals.BiotSavart`), so
`div (biotSavart ω) x` is the trace of an explicit continuous linear map: at every `x` and for
every `ρ > R + ‖x‖`,

  `fderiv ℝ (biotSavart ω) x = (4π)⁻¹ • bsDerivCLM ω ρ x`

(`hasFDerivAt_biotSavart_slice`), and the trace of `bsDerivCLM ω ρ x` **vanishes identically**, by
pure algebra of the integrand.  Indeed

  `bsDerivCLM ω ρ x = ∫_{B(0,ρ)} (crossL (ω a - ω x)).comp (kDerivCLM (x - a)) + (4π/3) • crossL (ω x)`,

and each of the two kernels is *trace-free as a linear map*:

* `crossL u` is the cross product `v ↦ u × v`, whose matrix is antisymmetric, so
  `trace (crossL u) = 0` (each diagonal entry `⟪eᵢ, u × eᵢ⟫` vanishes by `dot_cross_self`);
* `kDerivCLM b = ‖b‖⁻³ • id - 3‖b‖⁻⁵ • rankOne ℝ b b`, so
  `(crossL u).comp (kDerivCLM b) = ‖b‖⁻³ • crossL u - 3‖b‖⁻⁵ • rankOne ℝ (u × b) b`
  (`InnerProductSpace.comp_rankOne`), and
  `trace (rankOne ℝ (u × b) b) = ⟪b, u × b⟫ = 0` (`InnerProductSpace.trace_rankOne`);
* the trace is a continuous linear functional (`traceCLM`, with the bound `‖trace f‖ ≤ 3‖f‖`
  obtained from an orthonormal basis), so it commutes with the Bochner integral
  (`trace_setIntegral`).

No integration by parts, no boundary terms and no second derivative of the Newtonian potential are
needed: the divergence-free character of the Biot–Savart kernel is visible pointwise in its trace.

## Contents

* `inner_crossL_self`, `trace_crossL`, `trace_crossL_rankOne`, `trace_crossL_kDerivCLM`,
  `trace_bsIntegrand` — the algebraic trace-freeness of the kernels;
* `trace_sub_clm`, `trace_smul_clm`, `trace_add_clm`, `trace_bound`, `traceLin`, `traceCLM`,
  `trace_setIntegral` — the trace as a continuous linear functional on `ℝ³ →L[ℝ] ℝ³` and its
  compatibility with the Bochner integral;
* `integrableOn_bsIntegrand_ball` — the integrability of the (Hölder-regularised) derivative
  integrand on `B(0,ρ)`, from `integrableOn_bsIntegrand_inter`;
* `trace_bsDerivCLM` — `trace (bsDerivCLM ω ρ x) = 0`;
* `div_biotSavart_eq_zero` — the target.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_contDiff_one
import Submission.Work.CoreResiduals.BiotSavart.DerivDefs
import Submission.Work.CoreResiduals.BiotSavart.hasFDerivAt_biotSavart_slice
import Submission.Work.CoreResiduals.BiotSavart.continuous_bsDerivCLM
import Submission.Work.StabilityFar.Decay.KernelDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Set
open scoped Topology Matrix InnerProductSpace

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Work.FTS.BSSwirl

/-! ## Linearity of the trace on continuous linear maps -/

/-- The trace is additive on continuous linear maps. -/
theorem trace_add_clm (A B : R3 →L[ℝ] R3) :
    (A + B).trace ℝ R3 = A.trace ℝ R3 + B.trace ℝ R3 := by
  rw [show ((A + B).trace ℝ R3) = LinearMap.trace ℝ R3 ((A : R3 →ₗ[ℝ] R3) + B) from rfl, map_add]

/-- The trace is homogeneous on continuous linear maps. -/
theorem trace_smul_clm (c : ℝ) (A : R3 →L[ℝ] R3) :
    (c • A).trace ℝ R3 = c • A.trace ℝ R3 := by
  rw [show ((c • A).trace ℝ R3) = LinearMap.trace ℝ R3 (c • (A : R3 →ₗ[ℝ] R3)) from rfl, map_smul]

/-- The trace of a difference of continuous linear maps. -/
theorem trace_sub_clm (A B : R3 →L[ℝ] R3) :
    (A - B).trace ℝ R3 = A.trace ℝ R3 - B.trace ℝ R3 := by
  rw [show ((A - B).trace ℝ R3) = LinearMap.trace ℝ R3 ((A : R3 →ₗ[ℝ] R3) - B) from rfl, map_sub]

/-! ## Trace-freeness of the Biot–Savart kernels -/

/-- **The cross-product operator is orthogonal to its argument**: `⟪w, u × w⟫ = 0`.  This is the
componentwise form of `dot_cross_self`, transported to the Euclidean space `ℝ³`. -/
theorem inner_crossL_self (u w : R3) : ⟪w, Work.StabilityFar.Decay.crossL u w⟫_ℝ = 0 := by
  have h := dot_cross_self u.ofLp w.ofLp
  simp only [dotProduct] at h
  rw [Work.StabilityFar.Decay.crossL_apply, PiLp.inner_apply]
  have h2 : (∑ x, ⟪w.ofLp x, (crossProduct u.ofLp) w.ofLp x⟫_ℝ)
      = ∑ x, w.ofLp x * (crossProduct u.ofLp) w.ofLp x :=
    Finset.sum_congr rfl (fun x _ => by simp [mul_comm])
  rw [h2, h]

/-- **The cross-product operator is trace-free.**  In an orthonormal basis the trace of
`v ↦ u × v` is the sum of the diagonal entries `⟪eᵢ, u × eᵢ⟫`, all of which vanish
(`inner_crossL_self`). -/
theorem trace_crossL (u : R3) : (Work.StabilityFar.Decay.crossL u).trace ℝ R3 = 0 := by
  rw [show (Work.StabilityFar.Decay.crossL u).trace ℝ R3
      = LinearMap.trace ℝ R3 (Work.StabilityFar.Decay.crossL u).toLinearMap from rfl]
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  exact Finset.sum_eq_zero (fun i _ => inner_crossL_self u _)

/-- **The composite of the cross-product operator with a rank-one operator is trace-free.**
`(v ↦ u × v) ∘ (w ↦ ⟪z,w⟫ • z) = (w ↦ ⟪z,w⟫ • (u × z))` is the rank-one operator with symbol
`(u × z, z)`, whose trace is `⟪z, u × z⟫ = 0`. -/
theorem trace_crossL_rankOne (u z : R3) :
    ((Work.StabilityFar.Decay.crossL u).comp (InnerProductSpace.rankOne ℝ z z)).trace ℝ R3 = 0 := by
  rw [show ((Work.StabilityFar.Decay.crossL u).comp (InnerProductSpace.rankOne ℝ z z)).trace ℝ R3
      = LinearMap.trace ℝ R3
          (((Work.StabilityFar.Decay.crossL u).comp (InnerProductSpace.rankOne ℝ z z)).toLinearMap)
      from rfl]
  rw [InnerProductSpace.comp_rankOne]
  rw [show (InnerProductSpace.rankOne ℝ ((Work.StabilityFar.Decay.crossL u) z) z).trace ℝ R3
      = LinearMap.trace ℝ R3
          ((InnerProductSpace.rankOne ℝ ((Work.StabilityFar.Decay.crossL u) z) z).toLinearMap)
      from rfl]
  rw [InnerProductSpace.trace_rankOne]
  exact inner_crossL_self u z

/-- **The Jacobian of the Biot–Savart kernel composed with a cross product is trace-free.**  Since
`kDerivCLM z = ‖z‖⁻³ • id - 3‖z‖⁻⁵ • (w ↦ ⟪z,w⟫ • z)`, this reduces to the two previous lemmas
plus linearity of the trace. -/
theorem trace_crossL_kDerivCLM (u z : R3) :
    ((Work.StabilityFar.Decay.crossL u).comp (Work.StabilityFar.Decay.kDerivCLM z)).trace ℝ R3
      = 0 := by
  have hA : (Work.StabilityFar.Decay.crossL u).comp
        ((‖z‖ ^ (3:ℕ))⁻¹ • (ContinuousLinearMap.id ℝ R3)
          - (3 * (‖z‖ ^ (5:ℕ))⁻¹) • ((innerSL ℝ) z).smulRight z)
      = (‖z‖ ^ (3:ℕ))⁻¹ • Work.StabilityFar.Decay.crossL u
          - (3 * (‖z‖ ^ (5:ℕ))⁻¹) •
            ((Work.StabilityFar.Decay.crossL u).comp (InnerProductSpace.rankOne ℝ z z)) := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_id]
    rw [show ((innerSL ℝ) z).smulRight z = InnerProductSpace.rankOne ℝ z z from by
      rw [InnerProductSpace.rankOne_def]]
  rw [Work.StabilityFar.Decay.kDerivCLM, hA, trace_sub_clm, trace_smul_clm, trace_smul_clm,
    trace_crossL, trace_crossL_rankOne]
  simp

/-- **The integrand of the derivative of the Biot–Savart field is trace-free at every point.**
This is the pointwise algebraic heart of the divergence-free character of the Biot–Savart law. -/
theorem trace_bsIntegrand (ω : R3 → R3) (x a : R3) :
    (Work.CoreResiduals.BiotSavart.bsIntegrand ω x a).trace ℝ R3 = 0 := by
  rw [Work.CoreResiduals.BiotSavart.bsIntegrand]
  exact trace_crossL_kDerivCLM (ω a - ω x) (x - a)

/-! ## The trace as a continuous linear functional -/

/-- **The trace is bounded by three times the operator norm** — the dimension of `ℝ³`.  Obtained
by expanding the trace in the standard orthonormal basis. -/
theorem trace_bound (f : R3 →L[ℝ] R3) : ‖f.trace ℝ R3‖ ≤ 3 * ‖f‖ := by
  rw [show f.trace ℝ R3 = LinearMap.trace ℝ R3 f.toLinearMap from rfl]
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  have honb : ∀ i : Fin 3, ‖(EuclideanSpace.basisFun (Fin 3) ℝ) i‖ = 1 :=
    fun i => OrthonormalBasis.norm_eq_one _ i
  calc ‖∑ i, ⟪(EuclideanSpace.basisFun (Fin 3) ℝ) i,
        f ((EuclideanSpace.basisFun (Fin 3) ℝ) i)⟫_ℝ‖
      ≤ ∑ i, ‖⟪(EuclideanSpace.basisFun (Fin 3) ℝ) i,
          f ((EuclideanSpace.basisFun (Fin 3) ℝ) i)⟫_ℝ‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖f ((EuclideanSpace.basisFun (Fin 3) ℝ) i)‖ := by
        apply Finset.sum_le_sum
        intro i _
        have h2 := norm_inner_le_norm (𝕜 := ℝ) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
          (f ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
        rwa [honb i, one_mul] at h2
    _ ≤ ∑ i, ‖f‖ := by
        apply Finset.sum_le_sum
        intro i _
        have h1 := f.le_opNorm ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
        rwa [honb i, mul_one] at h1
    _ = 3 * ‖f‖ := by simp

/-- The trace, as a linear functional on the (finite-dimensional) space of continuous linear
endomorphisms of `ℝ³`. -/
noncomputable def traceLin : (R3 →L[ℝ] R3) →ₗ[ℝ] ℝ where
  toFun f := f.trace ℝ R3
  map_add' f g := trace_add_clm f g
  map_smul' c f := trace_smul_clm c f

/-- The trace, as a **continuous** linear functional on `ℝ³ →L[ℝ] ℝ³`. -/
noncomputable def traceCLM : (R3 →L[ℝ] R3) →L[ℝ] ℝ :=
  LinearMap.mkContinuous traceLin 3 (fun f => trace_bound f)

/-- The defining value of `traceCLM`. -/
theorem traceCLM_apply (f : R3 →L[ℝ] R3) : traceCLM f = f.trace ℝ R3 := rfl

/-- **The trace commutes with the Bochner integral of continuous linear maps.**  This is
`ContinuousLinearMap.integral_comp_comm` applied to the continuous linear functional `traceCLM`,
and needs the integrability of the `ℝ³ →L[ℝ] ℝ³`-valued integrand. -/
theorem trace_setIntegral {s : Set R3} {F : R3 → (R3 →L[ℝ] R3)}
    (hF : IntegrableOn F s volume) :
    ((∫ a in s, F a)).trace ℝ R3 = ∫ a in s, (F a).trace ℝ R3 := by
  have h := ContinuousLinearMap.integral_comp_comm traceCLM (φ := F) hF
  simpa only [traceCLM_apply] using h.symm

/-! ## Integrability of the derivative integrand and the trace of `bsDerivCLM` -/

/-- **The derivative integrand is integrable on any ball `B(0,ρ)`.**  The Hölder condition
`‖ω a - ω x‖ ≤ C‖a - x‖^α` with `α > 0` makes the singular kernel
`a ↦ ‖x - a‖^{α - 3}` integrable near `a = x`; the statement is
`integrableOn_bsIntegrand_inter` with the centre `x₀ := x` and a radius `Δ` so large that
`B(0,ρ) ⊆ B(x,Δ)`. -/
theorem integrableOn_bsIntegrand_ball (ω : R3 → R3) {C α : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ α) (ρ : ℝ) (x : R3) :
    IntegrableOn (Work.CoreResiduals.BiotSavart.bsIntegrand ω x) (Metric.ball 0 ρ) volume := by
  have hΔpos : 0 < max (2 * ρ) 0 + 2 * ‖x‖ + 1 := by
    have := norm_nonneg x; linarith [le_max_right (2 * ρ) 0]
  have hsub : Metric.ball (0 : R3) ρ ⊆ Metric.ball x (max (2 * ρ) 0 + 2 * ‖x‖ + 1) := by
    intro a ha
    rw [Metric.mem_ball, dist_zero_right] at ha
    rw [Metric.mem_ball, dist_eq_norm]
    have hxnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
    have hmax : ρ ≤ max (2 * ρ) 0 := by
      by_cases h : ρ ≤ 0
      · exact le_trans h (le_max_right _ _)
      · exact le_trans (by linarith [not_le.mp h]) (le_max_left _ _)
    calc ‖a - x‖ ≤ ‖a‖ + ‖x‖ := norm_sub_le a x
      _ < ρ + ‖x‖ := by linarith
      _ ≤ max (2 * ρ) 0 + 2 * ‖x‖ + 1 := by linarith
  have hx : ‖x - x‖ ≤ (max (2 * ρ) 0 + 2 * ‖x‖ + 1) / 2 := by
    rw [sub_self, norm_zero]
    linarith [le_max_right (2 * ρ) 0, norm_nonneg x]
  have h1 := Work.CoreResiduals.BiotSavart.integrableOn_bsIntegrand_inter (ω := ω) hα hC hhold x
    (Δ := max (2 * ρ) 0 + 2 * ‖x‖ + 1) (ρ := ρ) hΔpos hx
  rwa [Set.inter_eq_left.mpr hsub] at h1

/-- **The candidate derivative of the Biot–Savart field is trace-free.**  This is the
divergence-free character of the Biot–Savart law in infinitesimal form: the trace of
`bsDerivCLM ω ρ x` — which is `4π • fderiv (biotSavart ω) x` — vanishes. -/
theorem trace_bsDerivCLM (ω : R3 → R3) {C α : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ α) (ρ : ℝ) (x : R3) :
    (Work.CoreResiduals.BiotSavart.bsDerivCLM ω ρ x).trace ℝ R3 = 0 := by
  have hint : IntegrableOn (Work.CoreResiduals.BiotSavart.bsIntegrand ω x)
      (Metric.ball 0 ρ) volume := integrableOn_bsIntegrand_ball ω hα hC hhold ρ x
  have hint' : IntegrableOn (fun a : R3 => Work.StabilityFar.Decay.crossL (ω a - ω x)
      ∘SL Work.StabilityFar.Decay.kDerivCLM (x - a)) (Metric.ball 0 ρ) volume := hint
  have hb : ∀ a : R3, (Work.StabilityFar.Decay.crossL (ω a - ω x)
      ∘SL Work.StabilityFar.Decay.kDerivCLM (x - a)).trace ℝ R3 = 0 :=
    fun a => trace_bsIntegrand ω x a
  rw [Work.CoreResiduals.BiotSavart.bsDerivCLM.eq_def, trace_add_clm, trace_smul_clm,
    trace_crossL, trace_setIntegral hint']
  simp only [hb, integral_zero, zero_add, smul_zero]

/-! ## The divergence of the Biot–Savart field -/

theorem div_biotSavart_eq_zero {ω : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    {R M α C : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hα : 0 < α) (hC : 0 ≤ C)
    (hbdd : ∀ y, ‖ω y‖ ≤ M) (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hholder : ∀ a b : Work.FTS.BSSwirl.R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ α) :
    ∀ x, FiniteTimeSingularity.div (Work.LWP.biotSavart ω) x = 0 := by
  intro x
  -- `biotSavart ω` is differentiable at `x`, with derivative `(4π)⁻¹ • bsDerivCLM ω ρ x` for any
  -- radius `ρ > R + ‖x‖`.
  have hρ : R + ‖x‖ < R + ‖x‖ + 1 := by linarith
  have hfd := Work.CoreResiduals.BiotSavart.hasFDerivAt_biotSavart_slice
    (ω := ω) (R := R) (M := M) (C := C) (c := α) (ρ := R + ‖x‖ + 1)
    hR hM hα hbdd hsupp hmeas hholder hρ
  -- The divergence is the trace of the derivative, which is therefore the trace of a multiple of
  -- the trace-free map `bsDerivCLM ω ρ x`.
  rw [FiniteTimeSingularity.div, hfd.fderiv, trace_smul_clm,
    trace_bsDerivCLM ω hα hC hholder (R + ‖x‖ + 1) x]
  simp

end Work.FTS.BSSwirl

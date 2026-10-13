import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.Defs
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
import Submission.Work.CoreResiduals.BiotSavart.integral_kDerivCLM_annulus_eq_zero
import Submission.Work.CoreResiduals.BiotSavart.hasFDerivAt_biotSavart_slice
import Submission.Work.CoreResiduals.BiotSavart.norm_bsDerivCLM_le_of_bdd_holder
import Submission.Work.CoreResiduals.BiotSavart.IntegrandDefs
import Submission.Work.CoreResiduals.BiotSavart.continuous_bsDerivCLM
import Submission.Work.CoreResiduals.BiotSavart.lintegral_exterior_norm_rpow
import Submission.Work.CoreResiduals.BiotSavart.norm_setIntegral_crossL_kf_inter_le
import Submission.Work.CoreResiduals.BiotSavart.integral_ball_sub_norm_rpow
import Submission.Work.CoreResiduals.BiotSavart.norm_bsField_diff_bound
import Submission.Work.StabilityFar.Decay.decay_aux
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_le
import Submission.Work.CoreResiduals.BiotSavart.Bundle.norm_kDerivCLM_sub_le_of_two_mul_le
import Submission.Work.CoreResiduals.BiotSavart.Bundle.integrableOn_and_norm_setIntegral_kDerivCLM_diff_ball
import Submission.Work.CoreResiduals.BiotSavart.Bundle.norm_setIntegral_bsIntegrand_diff_inter_ball_le
import Submission.Work.CoreResiduals.BiotSavart.Bundle.norm_setIntegral_crossL_kDerivCLM_sub_le
import Submission.Work.CoreResiduals.BiotSavart.Bundle.norm_setIntegral_kDerivCLM_ball_diff_ball_le
import Submission.Work.CoreResiduals.BiotSavart.Bundle.sliceFderiv_holder_arith

import Submission.Work.CoreResiduals.BiotSavart.windowExt_holder_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 2000000

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric Set Filter Topology
open scoped Topology
open Work.StabilityFar.Decay (kDerivCLM kf crossL)

/-! ## 1. The pointwise splitting of the peeled integrand -/

/-- **Pointwise algebra of the two peeled integrands.**  The difference of the two derivative
integrands is the sum of the "constant vector times kernel" term and the
"kernel difference times Hölder difference" term:
`Λ(ω a - ω x)∘K(x-a) - Λ(ω a - ω y)∘K(y-a)
   = Λ(ω y - ω x)∘K(x-a) + Λ(ω a - ω y)∘(K(x-a) - K(y-a))`. -/
theorem bsIntegrand_sub_eq (g : R3 → R3) (x y a : R3) :
    bsIntegrand g x a - bsIntegrand g y a
      = (crossL (g y - g x)).comp (kDerivCLM (x - a))
        + (crossL (g a - g y)).comp (kDerivCLM (x - a) - kDerivCLM (y - a)) := by
  have hcomp : ∀ (A B K K' : R3 →L[ℝ] R3),
      A.comp K - B.comp K' = (A - B).comp K + B.comp (K - K') := by
    intro A B K K'
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  have hAB : crossL (g a - g x) - crossL (g a - g y) = crossL (g y - g x) := by
    rw [← Work.StabilityFar.Decay.crossL_sub]
    congr 1
    abel
  simp only [bsIntegrand]
  rw [hcomp, hAB]

/-! ## 2. Integrability of the shifted kernel on a ball-minus-ball region -/

/-- The kernel `a ↦ kDerivCLM (x - a)` is Bochner integrable on
`B(0,ρ) \ B(y,2δ)` whenever `0 < δ` and `‖x - y‖ ≤ δ`: the region stays at distance at least
`δ` from `x`, so the integrand is bounded by `4/δ³` there, and the region has finite volume. -/
theorem integrableOn_kDerivCLM_sub_diff_ball {x y : R3} {ρ δ : ℝ} (hδ : 0 < δ)
    (hxy : ‖x - y‖ ≤ δ) :
    IntegrableOn (fun a : R3 => kDerivCLM (x - a))
      ((Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ))) volume := by
  have hmeas : MeasurableSet ((Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ))) :=
    measurableSet_ball.diff measurableSet_ball
  refine MeasureTheory.IntegrableOn.of_bound (f := fun a : R3 => kDerivCLM (x - a)) ?hfin ?hmeas
    (4 / δ ^ 3) ?hbd
  · refine lt_of_le_of_lt (measure_mono ?_) ((isCompact_closedBall (0 : R3) ρ).measure_lt_top)
    intro a ha
    have h1 : a ∈ Metric.ball (0 : R3) ρ := (Set.mem_sdiff a).mp ha |>.1
    rw [Metric.mem_ball, dist_zero_right] at h1
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt h1
  · exact ((Work.StabilityFar.Decay.measurable_kDerivCLM_sub x).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  · rw [MeasureTheory.ae_restrict_iff' hmeas]
    refine Filter.Eventually.of_forall fun a ha => ?_
    have h1 : 2 * δ ≤ ‖a - y‖ := by
      have h2 : a ∉ Metric.ball y (2 * δ) := (Set.mem_sdiff a).mp ha |>.2
      rw [Metric.mem_ball] at h2
      have h3 := not_lt.mp h2
      rwa [dist_eq_norm] at h3
    have h3 : ‖a - y‖ ≤ ‖a - x‖ + ‖x - y‖ := by
      have heq : a - y = (a - x) + (x - y) := by abel
      rw [heq]
      exact norm_add_le _ _
    have h2 : δ ≤ ‖x - a‖ := by
      rw [norm_sub_rev a x] at h3
      linarith
    exact Work.StabilityFar.Decay.norm_kDerivCLM_le (x - a) δ hδ h2

/-! ## 3. The uniform-in-the-field Calderón–Zygmund difference estimate -/

/-- **The Schauder difference estimate for `bsDerivCLM`, uniform in the field.**

For `0 < α < 1`, `R > 0`, `M, C ≥ 0` and fixed `R'`, there is `K ≥ 0` — depending only on
`R, M, C, α, R'` and *not* on the field — such that for every `α`-Hölder field `g` bounded by `M`,

`‖bsDerivCLM g (R+R'+1) x - bsDerivCLM g (R+R'+1) y‖ ≤ K ‖x-y‖^α` for `‖x‖, ‖y‖ ≤ R'`.

The proof is the Calderón–Zygmund argument: for `δ := ‖x-y‖ ≤ 1/4` split the peeled integral
over `B(0,ρ)` at the ball `B(y,2δ)`; the near part is bounded by
`4C(4π/α)((3δ)^α + (2δ)^α)`, the far part splits into the constant-vector term
`Λ(g y - g x)∘∫K(x-a)` (bounded uniformly by the mean-zero property of the kernel over centred
annuli) and the kernel-difference term (bounded by `1024 C δ (4π (2δ)^{α-1}/(1-α))`); the shape
term contributes `(4π/3) C δ^α`.  For `δ ≥ 1/4` both derivatives are bounded by the interpolation
bound `norm_bsDerivCLM_le_of_bdd_holder`. -/
theorem bsDerivCLM_sub_holder_uniform {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {R M C R' : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : R3 → R3),
      (∀ a, ‖g a‖ ≤ M) →
      (∀ a b : R3, ‖g a - g b‖ ≤ C * ‖a - b‖ ^ (α : ℝ)) →
      ∀ x y : R3, ‖x‖ ≤ R' → ‖y‖ ≤ R' →
        ‖bsDerivCLM g (R + R' + 1) x - bsDerivCLM g (R + R' + 1) y‖
          ≤ K * ‖x - y‖ ^ (α : ℝ) := by
  classical
  by_cases hR'neg : R' < 0
  · refine ⟨0, le_refl 0, fun g hbdd hhold x y hx hy => ?_⟩
    rw [zero_mul]
    exact absurd hx (not_le.mpr (by linarith [norm_nonneg x, hR'neg]))
  set ρ : ℝ := R + R' + 1 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hexp : 0 < (α : ℝ) * (1 - (α : ℝ)) := by nlinarith
  -- the uniform interpolation bound on each derivative
  set B : ℝ := 4 * (2 * M) ^ (α : ℝ) * (2 * C) ^ (1 - (α : ℝ)) *
      (4 * Real.pi * (ρ + R') ^ ((α : ℝ) * (1 - (α : ℝ))) / ((α : ℝ) * (1 - (α : ℝ))))
      + (4 * Real.pi / 3) * M with hBdef
  -- the constants of the near-field bound
  set Kv : ℝ := (16 * Real.pi / 3) * ((ρ + R') ^ 3 / (ρ - R') ^ 3)
      + (16 * Real.pi / 3) * 27 with hKvdef
  set smallK : ℝ := 4 * C * (4 * Real.pi / (α : ℝ)) * ((3 : ℝ) ^ (α : ℝ) + (2 : ℝ) ^ (α : ℝ))
      + 1024 * C * (4 * Real.pi * (2 : ℝ) ^ ((α : ℝ) - 1) / (1 - (α : ℝ)))
      + (C * Kv + (4 * Real.pi / 3) * C) with hsmallKdef
  refine ⟨max 0 (max smallK (2 * B * (4 : ℝ) ^ (α : ℝ))), le_max_left _ _, ?_⟩
  intro g hbdd hhold x y hx hy
  -- the uniform bound on `bsDerivCLM g ρ ·` on the ball `‖·‖ ≤ R'`
  have hBnd : ∀ z : R3, ‖z‖ ≤ R' → ‖bsDerivCLM g ρ z‖ ≤ B := by
    intro z hz
    have h1 := norm_bsDerivCLM_le_of_bdd_holder (α := (α : ℝ)) (A := M) (H := C) (ρ := ρ)
      hα hα1 hM hC hρpos.le hbdd (fun a b => by
        have h := hhold a b
        have h2 : 0 ≤ ‖a - b‖ ^ (α : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
        nlinarith [h, hC, h2]) z
    rw [hBdef]
    refine le_trans h1 (add_le_add ?_ le_rfl)
    have hnum : (ρ + ‖z‖) ^ ((α : ℝ) * (1 - (α : ℝ)))
        ≤ (ρ + R') ^ ((α : ℝ) * (1 - (α : ℝ))) :=
      Real.rpow_le_rpow (by linarith [norm_nonneg z]) (by linarith) hexp.le
    have hfrac : 4 * Real.pi * (ρ + ‖z‖) ^ ((α : ℝ) * (1 - (α : ℝ)))
          / ((α : ℝ) * (1 - (α : ℝ)))
        ≤ 4 * Real.pi * (ρ + R') ^ ((α : ℝ) * (1 - (α : ℝ)))
          / ((α : ℝ) * (1 - (α : ℝ))) := by
      calc 4 * Real.pi * (ρ + ‖z‖) ^ ((α : ℝ) * (1 - (α : ℝ)))
            / ((α : ℝ) * (1 - (α : ℝ)))
          = (4 * Real.pi / ((α : ℝ) * (1 - (α : ℝ))))
              * (ρ + ‖z‖) ^ ((α : ℝ) * (1 - (α : ℝ))) := by ring
        _ ≤ (4 * Real.pi / ((α : ℝ) * (1 - (α : ℝ))))
              * (ρ + R') ^ ((α : ℝ) * (1 - (α : ℝ))) :=
            mul_le_mul_of_nonneg_left hnum (by positivity)
        _ = 4 * Real.pi * (ρ + R') ^ ((α : ℝ) * (1 - (α : ℝ)))
            / ((α : ℝ) * (1 - (α : ℝ))) := by ring
    have hcoef : 0 ≤ 4 * (2 * M) ^ (α : ℝ) * (2 * C) ^ (1 - (α : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_left hfrac hcoef
  rcases eq_or_ne x y with hxyEq | hxyNe
  · subst hxyEq
    have h1 : ‖bsDerivCLM g ρ x - bsDerivCLM g ρ x‖ = 0 := by simp
    have h2 : ‖x - x‖ ^ (α : ℝ) = 0 := by simp [Real.zero_rpow, hα.ne']
    rw [h1, h2, mul_zero]
  have hδpos0 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxyNe)
  set δ : ℝ := ‖x - y‖ with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact hδpos0
  have hxyδ : ‖x - y‖ ≤ δ := le_of_eq hδdef.symm
  by_cases hδq : δ ≤ 1 / 4
  · -- near field: `δ ≤ 1/4`
    have hρδ : R' + 2 * δ < ρ := by rw [hρdef]; linarith
    have hIntx : IntegrableOn (bsIntegrand g x) (Metric.ball (0 : R3) ρ) volume :=
      integrableOn_bsIntegrand_ball hα hC hhold x ρ
    have hInty : IntegrableOn (bsIntegrand g y) (Metric.ball (0 : R3) ρ) volume :=
      integrableOn_bsIntegrand_ball hα hC hhold y ρ
    have hInt : IntegrableOn (fun a : R3 => bsIntegrand g x a - bsIntegrand g y a)
        (Metric.ball (0 : R3) ρ) volume := hIntx.sub hInty
    -- the peeled difference
    have hsm : (4 * Real.pi / 3) • (crossL (g x) - crossL (g y))
        = (4 * Real.pi / 3) • crossL (g x) - (4 * Real.pi / 3) • crossL (g y) := by
      have h := map_sub ((4 * Real.pi / 3) • ContinuousLinearMap.id ℝ (R3 →L[ℝ] R3))
        (crossL (g x)) (crossL (g y))
      simpa using h
    have hpeel : bsDerivCLM g ρ x - bsDerivCLM g ρ y
        = (∫ a in Metric.ball (0 : R3) ρ, (bsIntegrand g x a - bsIntegrand g y a))
          + (4 * Real.pi / 3) • crossL (g x - g y) := by
      have hx' : bsDerivCLM g ρ x
          = (∫ a in Metric.ball (0 : R3) ρ, bsIntegrand g x a)
            + (4 * Real.pi / 3) • crossL (g x) := rfl
      have hy' : bsDerivCLM g ρ y
          = (∫ a in Metric.ball (0 : R3) ρ, bsIntegrand g y a)
            + (4 * Real.pi / 3) • crossL (g y) := rfl
      rw [hx', hy', integral_sub hIntx hInty,
        Work.StabilityFar.Decay.crossL_sub (g x) (g y), hsm]
      abel
    -- split at the ball `B(y,2δ)`
    have hsplit : (∫ a in Metric.ball (0 : R3) ρ, (bsIntegrand g x a - bsIntegrand g y a))
        = (∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball y (2 * δ)),
              (bsIntegrand g x a - bsIntegrand g y a))
          + (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
              (bsIntegrand g x a - bsIntegrand g y a)) :=
      (MeasureTheory.integral_inter_add_sdiff measurableSet_ball hInt).symm
    have hInner : ‖∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball y (2 * δ)),
          (bsIntegrand g x a - bsIntegrand g y a)‖
        ≤ 4 * C * (4 * Real.pi / (α : ℝ)) * ((3 * δ) ^ (α : ℝ) + (2 * δ) ^ (α : ℝ)) :=
      Bundle.norm_setIntegral_bsIntegrand_diff_inter_ball_le hα hC hhold hδpos hxyδ
    -- the far-field split of the integrand
    have hKint : IntegrableOn (fun a : R3 => kDerivCLM (x - a))
        ((Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ))) volume :=
      integrableOn_kDerivCLM_sub_diff_ball (ρ := ρ) hδpos hxyδ
    have hAint : IntegrableOn
        (fun a : R3 => (crossL (g y - g x)).comp (kDerivCLM (x - a)))
        ((Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ))) volume := by
      have hmeasure : MeasurableSet
          ((Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ))) :=
        measurableSet_ball.diff measurableSet_ball
      have hmA : Measurable
          (fun a : R3 => (crossL (g y - g x)).comp (kDerivCLM (x - a))) :=
        Work.StabilityFar.Decay.continuous_compL.measurable.comp
          (measurable_const.prodMk (Work.StabilityFar.Decay.measurable_kDerivCLM_sub x))
      refine MeasureTheory.IntegrableOn.of_bound (f := fun a : R3 =>
        (crossL (g y - g x)).comp (kDerivCLM (x - a))) ?hfin ?hmeas
        (‖crossL (g y - g x)‖ * (4 / δ ^ 3)) ?hbd
      · refine lt_of_le_of_lt (measure_mono ?_) ((isCompact_closedBall (0 : R3) ρ).measure_lt_top)
        intro a ha
        have h1 : a ∈ Metric.ball (0 : R3) ρ := (Set.mem_sdiff a).mp ha |>.1
        rw [Metric.mem_ball, dist_zero_right] at h1
        rw [Metric.mem_closedBall, dist_zero_right]
        exact le_of_lt h1
      · exact hmA.aestronglyMeasurable.mono_measure Measure.restrict_le_self
      · rw [MeasureTheory.ae_restrict_iff' hmeasure]
        refine Filter.Eventually.of_forall fun a ha => ?_
        have h1 : 2 * δ ≤ ‖a - y‖ := by
          have h2 : a ∉ Metric.ball y (2 * δ) := (Set.mem_sdiff a).mp ha |>.2
          rw [Metric.mem_ball] at h2
          have h3 := not_lt.mp h2
          rwa [dist_eq_norm] at h3
        have h3 : ‖a - y‖ ≤ ‖a - x‖ + ‖x - y‖ := by
          have heq : a - y = (a - x) + (x - y) := by abel
          rw [heq]
          exact norm_add_le _ _
        have h2 : δ ≤ ‖x - a‖ := by
          rw [norm_sub_rev a x] at h3
          linarith
        calc ‖(crossL (g y - g x)).comp (kDerivCLM (x - a))‖
            ≤ ‖crossL (g y - g x)‖ * ‖kDerivCLM (x - a)‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖crossL (g y - g x)‖ * (4 / δ ^ 3) :=
              mul_le_mul_of_nonneg_left
                (Work.StabilityFar.Decay.norm_kDerivCLM_le (x - a) δ hδpos h2) (norm_nonneg _)
    have hpt : ∀ a : R3, bsIntegrand g x a - bsIntegrand g y a
        = (crossL (g y - g x)).comp (kDerivCLM (x - a))
          + (crossL (g a - g y)).comp (kDerivCLM (x - a) - kDerivCLM (y - a)) :=
      fun a => bsIntegrand_sub_eq g x y a
    have hBint : IntegrableOn (fun a : R3 =>
        (crossL (g a - g y)).comp (kDerivCLM (x - a) - kDerivCLM (y - a)))
        ((Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ))) volume := by
      have h : IntegrableOn (fun a : R3 => (bsIntegrand g x a - bsIntegrand g y a)
          - (crossL (g y - g x)).comp (kDerivCLM (x - a)))
          ((Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ))) volume :=
        (hInt.mono_set Set.sdiff_subset).sub hAint
      refine h.congr_fun_ae ?_
      filter_upwards with a
      rw [hpt a]
      abel
    have hadd : (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
            (bsIntegrand g x a - bsIntegrand g y a))
        = (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
              (crossL (g y - g x)).comp (kDerivCLM (x - a)))
          + (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
              (crossL (g a - g y)).comp (kDerivCLM (x - a) - kDerivCLM (y - a))) := by
      simp only [hpt]
      rw [MeasureTheory.integral_add hAint hBint]
    -- the constant-vector term
    have hAF : ‖∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
          (crossL (g y - g x)).comp (kDerivCLM (x - a))‖ ≤ C * Kv * δ ^ (α : ℝ) := by
      haveI : CompleteSpace (R3 →L[ℝ] R3) :=
        FiniteDimensional.complete ℝ (R3 →L[ℝ] R3)
      have hpull : (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
            (crossL (g y - g x)).comp (kDerivCLM (x - a)))
          = (crossL (g y - g x)).comp
              (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
                kDerivCLM (x - a)) := by
        have h := ContinuousLinearMap.integral_comp_comm
          (ContinuousLinearMap.compL ℝ R3 R3 R3 (crossL (g y - g x))) hKint
        simpa only [ContinuousLinearMap.compL_apply, Function.comp_apply] using h
      rw [hpull]
      have hD5 := Bundle.norm_setIntegral_kDerivCLM_ball_diff_ball_le (ρ := ρ) (R' := R') (δ := δ)
        hδpos hρδ hx hy hxyδ
      rw [← hKvdef] at hD5
      have hL : ‖crossL (g y - g x)‖ ≤ C * δ ^ (α : ℝ) := by
        have h1 : ‖g y - g x‖ ≤ C * ‖y - x‖ ^ (α : ℝ) := hhold y x
        have h2 : ‖y - x‖ = δ := by rw [norm_sub_rev y x, ← hδdef]
        rw [h2] at h1
        exact le_trans (Work.StabilityFar.Decay.norm_crossL_le _) h1
      calc ‖(crossL (g y - g x)).comp
              (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
                kDerivCLM (x - a))‖
          ≤ ‖crossL (g y - g x)‖ *
              ‖∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
                kDerivCLM (x - a)‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (C * δ ^ (α : ℝ)) * Kv :=
            mul_le_mul hL hD5 (norm_nonneg _) (by positivity)
        _ = C * Kv * δ ^ (α : ℝ) := by ring
    -- the kernel-difference term
    have hBF : ‖∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
          (crossL (g a - g y)).comp (kDerivCLM (x - a) - kDerivCLM (y - a))‖
        ≤ 1024 * C * δ * (4 * Real.pi * (2 * δ) ^ ((α : ℝ) - 1) / (1 - (α : ℝ))) :=
      Bundle.norm_setIntegral_crossL_kDerivCLM_sub_le (ρ := ρ) hα hα1 hC hhold hδpos hxyδ
    have hOuter : ‖∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
          (bsIntegrand g x a - bsIntegrand g y a)‖
        ≤ C * Kv * δ ^ (α : ℝ)
          + 1024 * C * δ * (4 * Real.pi * (2 * δ) ^ ((α : ℝ) - 1) / (1 - (α : ℝ))) := by
      rw [hadd]
      exact le_trans (norm_add_le _ _) (add_le_add hAF hBF)
    -- the shape term
    have hShape : ‖(4 * Real.pi / 3) • crossL (g x - g y)‖
        ≤ (4 * Real.pi / 3) * C * δ ^ (α : ℝ) := by
      have h1 : ‖g x - g y‖ ≤ C * δ ^ (α : ℝ) := by
        have h := hhold x y
        rwa [← hδdef] at h
      have h2 : ‖(4 * Real.pi / 3) • crossL (g x - g y)‖
          ≤ (4 * Real.pi / 3) * ‖crossL (g x - g y)‖ := by
        refine le_trans (norm_smul_le (4 * Real.pi / 3) (crossL (g x - g y))) ?_
        rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi / 3)]
      calc ‖(4 * Real.pi / 3) • crossL (g x - g y)‖
          ≤ (4 * Real.pi / 3) * ‖crossL (g x - g y)‖ := h2
        _ ≤ (4 * Real.pi / 3) * ‖g x - g y‖ :=
            mul_le_mul_of_nonneg_left (Work.StabilityFar.Decay.norm_crossL_le _) (by positivity)
        _ ≤ (4 * Real.pi / 3) * (C * δ ^ (α : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (4 * Real.pi / 3) * C * δ ^ (α : ℝ) := by ring
    have htotal : ‖bsDerivCLM g ρ x - bsDerivCLM g ρ y‖
        ≤ 4 * C * (4 * Real.pi / (α : ℝ)) * ((3 * δ) ^ (α : ℝ) + (2 * δ) ^ (α : ℝ))
          + 1024 * C * δ * (4 * Real.pi * (2 * δ) ^ ((α : ℝ) - 1) / (1 - (α : ℝ)))
          + (C * Kv + (4 * Real.pi / 3) * C) * δ ^ (α : ℝ) := by
      rw [hpeel, hsplit]
      have hstep : ‖(∫ a in (Metric.ball (0 : R3) ρ) ∩ (Metric.ball y (2 * δ)),
              (bsIntegrand g x a - bsIntegrand g y a))
            + (∫ a in (Metric.ball (0 : R3) ρ) \ (Metric.ball y (2 * δ)),
              (bsIntegrand g x a - bsIntegrand g y a))
            + (4 * Real.pi / 3) • crossL (g x - g y)‖
          ≤ (4 * C * (4 * Real.pi / (α : ℝ)) * ((3 * δ) ^ (α : ℝ) + (2 * δ) ^ (α : ℝ)))
            + (C * Kv * δ ^ (α : ℝ)
              + 1024 * C * δ * (4 * Real.pi * (2 * δ) ^ ((α : ℝ) - 1) / (1 - (α : ℝ))))
            + (4 * Real.pi / 3) * C * δ ^ (α : ℝ) := by
        refine le_trans (norm_add_le _ _) (add_le_add ?_ hShape)
        exact le_trans (norm_add_le _ _) (add_le_add hInner hOuter)
      refine le_trans hstep (le_of_eq ?_)
      ring
    have harith := Bundle.sliceFderiv_holder_arith (α := (α : ℝ)) (C := C) (δ := δ) (Kv := Kv)
      hα hα1 hC hδpos.le
    rw [← hsmallKdef] at harith
    refine le_trans htotal (le_trans harith ?_)
    have hδpow : 0 ≤ δ ^ (α : ℝ) := Real.rpow_nonneg hδpos.le _
    have hle : smallK ≤ max 0 (max smallK (2 * B * (4 : ℝ) ^ (α : ℝ))) :=
      le_trans (le_max_left smallK (2 * B * (4 : ℝ) ^ (α : ℝ)))
        (le_max_right 0 (max smallK (2 * B * (4 : ℝ) ^ (α : ℝ))))
    exact mul_le_mul_of_nonneg_right hle hδpow
  · -- far field: `1/4 < δ`
    have hδq' : 1 / 4 < δ := not_le.mp hδq
    have h4δ : 1 ≤ 4 * δ := by linarith
    have hrpow : 1 ≤ (4 : ℝ) ^ (α : ℝ) * δ ^ (α : ℝ) := by
      have h := Real.one_le_rpow h4δ hα.le
      rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hδpos.le] at h
    have h2B : 0 ≤ 2 * B := by
      have h1 := hBnd x hx
      linarith [norm_nonneg (bsDerivCLM g ρ x)]
    calc ‖bsDerivCLM g ρ x - bsDerivCLM g ρ y‖
        ≤ ‖bsDerivCLM g ρ x‖ + ‖bsDerivCLM g ρ y‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hBnd x hx) (hBnd y hy)
      _ = 2 * B := by ring
      _ ≤ 2 * B * ((4 : ℝ) ^ (α : ℝ) * δ ^ (α : ℝ)) := by
          simpa using mul_le_mul_of_nonneg_left hrpow h2B
      _ = (2 * B * (4 : ℝ) ^ (α : ℝ)) * δ ^ (α : ℝ) := by ring
      _ ≤ (max 0 (max smallK (2 * B * (4 : ℝ) ^ (α : ℝ)))) * δ ^ (α : ℝ) := by
          have hδpow : 0 ≤ δ ^ (α : ℝ) := Real.rpow_nonneg hδpos.le _
          have hle : 2 * B * (4 : ℝ) ^ (α : ℝ)
              ≤ max 0 (max smallK (2 * B * (4 : ℝ) ^ (α : ℝ))) :=
            le_trans (le_max_right smallK (2 * B * (4 : ℝ) ^ (α : ℝ)))
              (le_max_right 0 (max smallK (2 * B * (4 : ℝ) ^ (α : ℝ))))
          exact mul_le_mul_of_nonneg_right hle hδpow

/-! ## 4. The uniform single-slice Schauder estimate -/

/-- **The uniform-in-the-slice Schauder estimate for one vorticity slice.**

For `0 < α < 1`, `R > 0`, `M, C ≥ 0` and fixed `R'` there is `K ≥ 0`, depending only on
`R, M, C, α, R'`, such that for every field `g` bounded by `M`, supported in `closedBall 0 R`,
ae-strongly-measurable and `α`-Hölder with constant `C`, the derivative
`x ↦ fderiv ℝ (biotSavart g) x` is `α`-Hölder on `‖x‖ ≤ R'` with constant `K`. -/
theorem sliceFderiv_holder_uniform {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {R M C R' : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : R3 → R3),
      (∀ a, ‖g a‖ ≤ M) →
      (∀ a, g a ≠ 0 → a ∈ Metric.closedBall 0 R) →
      MeasureTheory.AEStronglyMeasurable g volume →
      (∀ a b : R3, ‖g a - g b‖ ≤ C * ‖a - b‖ ^ (α : ℝ)) →
      ∀ x y : R3, ‖x‖ ≤ R' → ‖y‖ ≤ R' →
        ‖fderiv ℝ (Work.LWP.biotSavart g) x - fderiv ℝ (Work.LWP.biotSavart g) y‖
          ≤ K * ‖x - y‖ ^ (α : ℝ) := by
  obtain ⟨K₀, hK₀0, hK₀⟩ := bsDerivCLM_sub_holder_uniform (α := α) hα hα1 hR hM hC
  refine ⟨(4 * Real.pi)⁻¹ * K₀, by positivity, ?_⟩
  intro g hbdd hs hm hhold x y hx hy
  by_cases hR'neg : R' < 0
  · exact absurd hx (not_le.mpr (by linarith [norm_nonneg x, hR'neg]))
  have hxρ : R + ‖x‖ < R + R' + 1 := by linarith
  have hyρ : R + ‖y‖ < R + R' + 1 := by linarith
  have hfx : fderiv ℝ (Work.LWP.biotSavart g) x
      = (4 * Real.pi)⁻¹ • bsDerivCLM g (R + R' + 1) x :=
    (hasFDerivAt_biotSavart_slice (R := R) (M := M) (C := C) (c := (α : ℝ)) (ρ := R + R' + 1)
      hR hM hα hbdd hs hm hhold hxρ).fderiv
  have hfy : fderiv ℝ (Work.LWP.biotSavart g) y
      = (4 * Real.pi)⁻¹ • bsDerivCLM g (R + R' + 1) y :=
    (hasFDerivAt_biotSavart_slice (R := R) (M := M) (C := C) (c := (α : ℝ)) (ρ := R + R' + 1)
      hR hM hα hbdd hs hm hhold hyρ).fderiv
  have hsm : (4 * Real.pi)⁻¹ • bsDerivCLM g (R + R' + 1) x
        - (4 * Real.pi)⁻¹ • bsDerivCLM g (R + R' + 1) y
      = (4 * Real.pi)⁻¹ • (bsDerivCLM g (R + R' + 1) x - bsDerivCLM g (R + R' + 1) y) := by
    have h := map_sub ((4 * Real.pi)⁻¹ • ContinuousLinearMap.id ℝ (R3 →L[ℝ] R3))
      (bsDerivCLM g (R + R' + 1) x) (bsDerivCLM g (R + R' + 1) y)
    simpa using h.symm
  rw [hfx, hfy, hsm, norm_smul,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (4 * Real.pi)⁻¹)]
  have hmain := hK₀ g hbdd hhold x y hx hy
  calc (4 * Real.pi)⁻¹
        * ‖bsDerivCLM g (R + R' + 1) x - bsDerivCLM g (R + R' + 1) y‖
      ≤ (4 * Real.pi)⁻¹ * (K₀ * ‖x - y‖ ^ (α : ℝ)) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = (4 * Real.pi)⁻¹ * K₀ * ‖x - y‖ ^ (α : ℝ) := by ring

/-! ## 5. The bundle lemma -/

/-- **The uniform-in-`t` single-slice Schauder estimate for a strip-bundle vorticity.**

For `0 < α < 1`, let `ω` satisfy the full strip bundle `BSAdmissibleStripFull α ω R S`: supported in
`closedBall 0 R`, uniformly bounded by `M`, uniformly `α`-Hölder in `x` with constant `H`, uniformly
Hölder in `t`, with ae-strongly-measurable slices. Then the spatial Calderón–Zygmund derivative of
each slice, `x ↦ fderiv ℝ (BS (ω·t)) x`, is `α`-Hölder on the ball `‖x‖ ≤ R'`, with a constant `K`
*uniform in `t ∈ Icc 0 S`*.

This is the `x`-direction half of the space-time Schauder estimate: the bundle is exactly the
statement that all the constants of the classical Schauder estimate (`R`, the sup bound `M`, the
`x`-Hölder constant `H`) are uniform in `t`, which is what makes the resulting constant uniform.
The proof is `sliceFderiv_holder_uniform`, applied to each slice: the constants `R, max M 0, (H:ℝ)`
do not depend on `t`. -/
theorem bundleSliceFderiv_holder {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S R' : ℝ}
    (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc (0:ℝ) S, ∀ x y : Work.LWP.R3,
      ‖x‖ ≤ R' → ‖y‖ ≤ R' →
      ‖fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t)) x
        - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t)) y‖
      ≤ K * ‖x - y‖ ^ (α : ℝ) := by
  obtain ⟨⟨hR, hsupp, ⟨M, hM⟩, ⟨H, hH⟩, htime, hmeas⟩, -, -⟩ := hbun
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hH0 : 0 ≤ (H : ℝ) := H.coe_nonneg
  obtain ⟨K, hK0, hK⟩ := sliceFderiv_holder_uniform (α := α) hα hα1 (R := R) (M := max M 0)
    (C := (H : ℝ)) (R' := R') hR hM0 hH0
  refine ⟨K, hK0, ?_⟩
  intro t ht x y hx hy
  have hbdd : ∀ a : Work.LWP.R3, ‖ω a t‖ ≤ max M 0 :=
    fun a => le_trans (hM t ht a) (le_max_left _ _)
  have hhold : ∀ a b : Work.LWP.R3, ‖ω a t - ω b t‖ ≤ (H : ℝ) * ‖a - b‖ ^ (α : ℝ) :=
    fun a b => holderWith_norm_sub_le (hH t ht) a b
  exact hK (fun a => ω a t) hbdd (fun a ha => hsupp t ht a ha) (hmeas t ht) hhold x y hx hy

end Work.CoreResiduals.BiotSavart

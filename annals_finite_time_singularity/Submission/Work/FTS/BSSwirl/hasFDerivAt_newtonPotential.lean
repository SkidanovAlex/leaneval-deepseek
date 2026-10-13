/-
# `Work.FTS.BSSwirl.hasFDerivAt_newtonPotential`

For a vorticity `ω` that is ae-strongly-measurable, bounded by `M ≥ 0` and supported in the
closed ball `B(0,R)`, the vector Newtonian potential

  `newtonPotential ω x = (4π)⁻¹ • ∫ y, ‖x - y‖⁻¹ • ω y`

is differentiable at every point `x : ℝ³`, with derivative
`potDeriv ω x = (4π)⁻¹ • ∫ y, ‖x - y‖⁻³ • (⟪y - x, ·⟫ ⊗ ω y)`.

Write `P x = ∫ y, ‖x-y‖⁻¹ • ω y` and `A = ∫ y, ‖x-y‖⁻³ • (⟪y-x,·⟫ ⊗ ω y)`.  By linearity of the
Bochner integral, `ContinuousLinearMap.integral_apply` and `inner_sub_left`,

  `P(x+h) - P x - A h = ∫ y, K(h,y) • ω y`,

and `residual_integral_bound` bounds the right-hand side by `C ‖h‖^{3/2}`, which is `o(‖h‖)`.
Then `HasFDerivAt P A x` (`hasFDerivAt_iff_isLittleO_nhds_zero`), and the statement follows by
multiplying by `(4π)⁻¹`.
-/
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSSwirl.residualIntegralBound
import Submission.Work.FTS.BSSwirl.integrable_inv_norm_smul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter Set
open scoped Topology ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-! ## The main theorem -/

theorem hasFDerivAt_newtonPotential {ω : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3} {R M : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hbdd : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (x : Work.FTS.BSSwirl.R3) :
    HasFDerivAt (Work.FTS.BSSwirl.newtonPotential ω) (Work.FTS.BSSwirl.potDeriv ω x) x := by
  classical
  -- the candidate derivative, as a Bochner integral of operators
  set A : R3 →L[ℝ] R3 := ∫ y, (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ •
    (innerSL ℝ (y - x)).smulRight (ω y) with hA
  have hintK : Integrable (fun y => (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ •
      (innerSL ℝ (y - x)).smulRight (ω y)) volume :=
    integrable_potDeriv_kernel' hM hbdd hsupp hmeas x
  have hint1 : ∀ u : R3, Integrable (fun y => (‖u - y‖)⁻¹ • ω y) volume :=
    fun u => integrable_inv_norm_smul hM hbdd hsupp hmeas u
  have hint3 : ∀ h : R3, Integrable
      (fun y => ((‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y) volume :=
    fun h => integrable_inv_cube_inner_smul' hM hbdd hsupp hmeas x h
  -- the derivative, tested on a vector
  have hAapply : ∀ h : R3, A h = -∫ y, ((‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y := by
    intro h
    rw [hA, ContinuousLinearMap.integral_apply hintK h]
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hsub : inner ℝ (y - x) h = -inner ℝ (x - y) h := by
      rw [inner_sub_left, inner_sub_left]
      ring
    show (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ • ((innerSL ℝ (y - x)).smulRight (ω y)) h
      = -(((‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y)
    rw [ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, hsub, neg_smul, smul_neg, smul_smul]
  -- the residual identity
  have hkey : ∀ h : R3, (∫ y, (‖(x + h) - y‖)⁻¹ • ω y)
      - (∫ y, (‖x - y‖)⁻¹ • ω y) - A h
      = ∫ y, ((‖(x + h) - y‖)⁻¹ - (‖x - y‖)⁻¹
          + (‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y := by
    intro h
    have h1 := hint1 (x + h)
    have h2 := hint1 x
    have h3 := hint3 h
    have e1 : (∫ y, (‖(x + h) - y‖)⁻¹ • ω y) - (∫ y, (‖x - y‖)⁻¹ • ω y)
        = ∫ y, ((‖(x + h) - y‖)⁻¹ • ω y - (‖x - y‖)⁻¹ • ω y) :=
      (integral_sub h1 h2).symm
    have e2 : (∫ y, ((‖(x + h) - y‖)⁻¹ • ω y - (‖x - y‖)⁻¹ • ω y))
        + (∫ y, ((‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y)
        = ∫ y, (((‖(x + h) - y‖)⁻¹ • ω y - (‖x - y‖)⁻¹ • ω y)
            + ((‖x - y‖ ^ (3 : ℕ) : ℝ)⁻¹ * inner ℝ (x - y) h) • ω y) :=
      (integral_add (h1.sub h2) h3).symm
    rw [hAapply h, sub_neg_eq_add, e1, e2]
    congr 1
    funext y
    rw [add_smul, sub_smul]
  -- the little-o estimate
  set D : ℝ := |R| + ‖x‖ + 1 with hDD
  have hDnn : 0 ≤ D := by rw [hDD]; positivity
  have hbd : ∀ h : R3, ‖(∫ y, (‖(x + h) - y‖)⁻¹ • ω y)
      - (∫ y, (‖x - y‖)⁻¹ • ω y) - A h‖
      ≤ M * (34 * Real.pi * ‖h‖ ^ 2
          + 80000 * Real.pi * Real.sqrt D * ‖h‖ ^ ((3 : ℝ) / 2)) := by
    intro h
    rw [hkey h]
    exact residual_integral_bound hM hbdd hsupp hmeas x h
  have hbigO : (fun h : R3 => (∫ y, (‖(x + h) - y‖)⁻¹ • ω y)
      - (∫ y, (‖x - y‖)⁻¹ • ω y) - A h)
      =O[𝓝 0] (fun h : R3 => ‖h‖ ^ ((3 : ℝ) / 2)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨M * (34 * Real.pi + 80000 * Real.pi * Real.sqrt D), ?_⟩
    filter_upwards [Metric.ball_mem_nhds (0 : R3) one_pos] with h hh
    have hnorm : ‖h‖ < 1 := by simpa [dist_eq_norm] using hh
    have hr0 : 0 ≤ ‖h‖ := norm_nonneg h
    have h2 : ‖h‖ ^ 2 ≤ ‖h‖ ^ ((3 : ℝ) / 2) := by
      rcases eq_or_lt_of_le hr0 with h0 | hpos
      · rw [← h0]
        norm_num
      · have h3h : ‖h‖ ^ ((3 : ℝ) / 2) = ‖h‖ * Real.sqrt ‖h‖ := by
          rw [Real.sqrt_eq_rpow, show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num,
            Real.rpow_add hpos, Real.rpow_one]
        have hsq : ‖h‖ ^ 2 = ‖h‖ * ‖h‖ := by ring
        rw [h3h, hsq]
        refine mul_le_mul_of_nonneg_left ?_ hr0
        rw [Real.le_sqrt hr0 hr0]
        calc ‖h‖ ^ 2 = ‖h‖ * ‖h‖ := by ring
          _ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right hnorm.le hr0
          _ = ‖h‖ := by rw [one_mul]
    have hrow : (‖h‖ ^ ((3 : ℝ) / 2)) = ‖‖h‖ ^ ((3 : ℝ) / 2)‖ :=
      (Real.norm_of_nonneg (Real.rpow_nonneg hr0 _)).symm
    rw [← hrow]
    calc ‖(∫ y, (‖(x + h) - y‖)⁻¹ • ω y) - (∫ y, (‖x - y‖)⁻¹ • ω y) - A h‖
        ≤ M * (34 * Real.pi * ‖h‖ ^ 2
            + 80000 * Real.pi * Real.sqrt D * ‖h‖ ^ ((3 : ℝ) / 2)) := hbd h
      _ ≤ M * ((34 * Real.pi + 80000 * Real.pi * Real.sqrt D) * ‖h‖ ^ ((3 : ℝ) / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hM
          calc 34 * Real.pi * ‖h‖ ^ 2 + 80000 * Real.pi * Real.sqrt D * ‖h‖ ^ ((3 : ℝ) / 2)
              ≤ 34 * Real.pi * ‖h‖ ^ ((3 : ℝ) / 2)
                + 80000 * Real.pi * Real.sqrt D * ‖h‖ ^ ((3 : ℝ) / 2) := by
                linarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 34 * Real.pi)]
            _ = (34 * Real.pi + 80000 * Real.pi * Real.sqrt D) * ‖h‖ ^ ((3 : ℝ) / 2) := by ring
      _ = M * (34 * Real.pi + 80000 * Real.pi * Real.sqrt D) * ‖h‖ ^ ((3 : ℝ) / 2) := by ring
  have hstep : HasFDerivAt (fun z : R3 => ∫ y, (‖z - y‖)⁻¹ • ω y) A x := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    exact hbigO.trans_isLittleO littleO_norm_rpow_three_halves
  -- multiply by the normalisation constant and identify the potential and the derivative
  have hstep2 : HasFDerivAt ((4 * Real.pi)⁻¹ • fun z : R3 => ∫ y, (‖z - y‖)⁻¹ • ω y)
      ((4 * Real.pi)⁻¹ • A) x := hstep.const_smul _
  have hfun : ((4 * Real.pi)⁻¹ • fun z : R3 => ∫ y, (‖z - y‖)⁻¹ • ω y) = newtonPotential ω := by
    funext z
    rfl
  rw [hfun] at hstep2
  have hderiv : (4 * Real.pi)⁻¹ • A = potDeriv ω x := by
    rw [hA, potDeriv]
  rw [hderiv] at hstep2
  exact hstep2

end

end Work.FTS.BSSwirl

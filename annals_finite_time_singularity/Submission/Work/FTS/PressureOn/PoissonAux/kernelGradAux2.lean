/-
# Auxiliary lemmas for the gradient form of the fundamental-solution identity (part 2)

The smooth approximation `regN c z = (4π)⁻¹(‖z‖²+c)^{-1/2}` of the Newtonian kernel, the two
dominated-convergence limits of the integration-by-parts identity as `c → 0⁺`, and the centred
scalar identity `∫ ΔΨ ∂ᵢN = ∂ᵢΨ(0)`.
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.PressureOn.PoissonAux.kernelGradAux
import Submission.Work.FTS.PressureOn.PoissonAux.kernelIntegral
import Submission.Work.FTS.PressureOn.integrable_inv_normSq_indicator_closedBall
import Submission.Work.FTS.PressureOn.Green.integrableOn_newtonKernel_ball

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

namespace kgiAux

/-! ## General smoothness of partial derivatives -/

theorem contDiff_fderiv_apply_e_of {u : R3 → ℝ} {m : ℕ} (hu : ContDiff ℝ (m + 1) u) (i : Fin 3) :
    ContDiff ℝ m (fun x : R3 => fderiv ℝ u x (FiniteTimeSingularity.e i)) := by
  have h : ContDiff ℝ m (fun p : R3 × R3 => fderiv ℝ u p.1 p.2) :=
    ContDiff.contDiff_fderiv_apply hu (by simp)
  have h2 : ContDiff ℝ m (fun x : R3 => (x, FiniteTimeSingularity.e i)) := by
    have h3 : ContDiff ℝ m (fun x : R3 => ((x, (0 : R3)) : R3 × R3)) :=
      (ContinuousLinearMap.inl ℝ R3 R3).contDiff
    simpa using h3.add (contDiff_const (c := ((0 : R3), FiniteTimeSingularity.e i)))
  exact h.comp h2

theorem contDiff_fderiv_apply_e_all {u : R3 → ℝ} (hu : ∀ n : ℕ, ContDiff ℝ n u) (i : Fin 3) :
    ∀ n : ℕ, ContDiff ℝ n (fun x : R3 => fderiv ℝ u x (FiniteTimeSingularity.e i)) :=
  fun n => contDiff_fderiv_apply_e_of (hu (n + 1)) i

/-- `laplaceTrace Ψ` is `C²` when `Ψ` is smooth. -/
theorem contDiff_two_laplaceTrace {Ψ : R3 → ℝ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) :
    ContDiff ℝ 2 (laplaceTrace Ψ) := by
  change ContDiff ℝ 2 (fun x : R3 => ∑ i : Fin 3, fderiv ℝ
    (fun w : R3 => fderiv ℝ Ψ w (FiniteTimeSingularity.e i)) x (FiniteTimeSingularity.e i))
  exact ContDiff.sum fun i _ =>
    contDiff_fderiv_apply_e_of (contDiff_fderiv_apply_e_of (hΨ 4) i) i

/-- The coordinate form of `gradient newtonKernel = newtonGrad`. -/
theorem inner_e_newtonGrad_tmp (z : R3) (i : Fin 3) :
    inner ℝ (FiniteTimeSingularity.e i) (newtonGrad z)
      = fderiv ℝ newtonKernel z (FiniteTimeSingularity.e i) := by
  rw [← gradient_newtonKernel z, real_inner_comm]
  exact inner_gradient_left

/-! ## A smooth approximation of the Newtonian kernel -/

/-- The regularised Newtonian kernel `regN c z = (4π)⁻¹ (‖z‖² + c)^{-1/2}`: for `c > 0` it is a
`C^∞` function on all of `ℝ³` (there is no singularity at the origin), it converges to the
Newtonian kernel `newtonKernel z = (4π‖z‖)⁻¹` as `c → 0⁺`, and its gradient is dominated uniformly
in `c` by `(4π)⁻¹‖z‖⁻²` — which is integrable on balls of `ℝ³`.  This is what makes the limit
`c → 0⁺` of the integration-by-parts identity an instance of dominated convergence. -/
noncomputable abbrev regN (c : ℝ) : R3 → ℝ :=
  fun z => (4 * Real.pi)⁻¹ * (Real.sqrt (‖z‖ ^ 2 + c))⁻¹

theorem regN_apply (c : ℝ) (z : R3) :
    regN c z = (4 * Real.pi)⁻¹ * (Real.sqrt (‖z‖ ^ 2 + c))⁻¹ := rfl

theorem contDiff_one_regN (c : ℝ) (hc : 0 < c) : ContDiff ℝ 1 (regN c) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have hpos : (0 : ℝ) < ‖z‖ ^ 2 + c := by positivity
  have h1 : ContDiffAt ℝ 1 (fun w : R3 => ‖w‖ ^ 2 + c) z :=
    ((contDiff_norm_sq (𝕜 := ℝ) (n := 1)).add contDiff_const).contDiffAt
  have h2 : ContDiffAt ℝ 1 Real.sqrt (‖z‖ ^ 2 + c) :=
    Real.contDiffAt_sqrt (x := ‖z‖ ^ 2 + c) (n := 1) (ne_of_gt hpos)
  have h3 : ContDiffAt ℝ 1 (fun w : R3 => Real.sqrt (‖w‖ ^ 2 + c)) z := h2.comp z h1
  have h4 : ContDiffAt ℝ 1 (fun w : R3 => (Real.sqrt (‖w‖ ^ 2 + c))⁻¹) z :=
    h3.inv (by positivity)
  exact (contDiffAt_const (c := (4 * Real.pi)⁻¹)).mul h4

theorem fderiv_real_apply (f : ℝ → ℝ) (t s : ℝ) :
    (fderiv ℝ f t) s = deriv f t * s := by
  have h : (s : ℝ) • (1 : ℝ) = s := by simp
  calc (fderiv ℝ f t) s = (fderiv ℝ f t) (s • (1 : ℝ)) := by rw [h]
    _ = s • ((fderiv ℝ f t) 1) := map_smul _ _ _
    _ = deriv f t * s := by
        rw [show (fderiv ℝ f t) 1 = deriv f t from rfl, smul_eq_mul]
        ring

theorem fderiv_regN_apply (c : ℝ) (hc : 0 < c) (z : R3) (i : Fin 3) :
    fderiv ℝ (regN c) z (FiniteTimeSingularity.e i)
      = -((4 * Real.pi)⁻¹ * ((Real.sqrt (‖z‖ ^ 2 + c))⁻¹) ^ 3) * z i := by
  have hpos : (0 : ℝ) < ‖z‖ ^ 2 + c := by positivity
  have hr : DifferentiableAt ℝ (fun s : ℝ => (4 * Real.pi)⁻¹ * (Real.sqrt s)⁻¹)
      (‖z‖ ^ 2 + c) :=
    (((Real.hasDerivAt_sqrt (ne_of_gt hpos)).inv (by positivity)).const_mul
      ((4 * Real.pi)⁻¹)).differentiableAt
  have hg : DifferentiableAt ℝ (fun z : R3 => ‖z‖ ^ 2 + c) z :=
    (((contDiff_norm_sq (𝕜 := ℝ) (n := 1)).add (contDiff_const (c := c))).differentiable
      (by norm_num)).differentiableAt
  have hderiv : deriv (fun s : ℝ => (4 * Real.pi)⁻¹ * (Real.sqrt s)⁻¹) (‖z‖ ^ 2 + c)
      = (4 * Real.pi)⁻¹ * (-(1 / (2 * Real.sqrt (‖z‖ ^ 2 + c)))
          / (Real.sqrt (‖z‖ ^ 2 + c)) ^ 2) := by
    have h1 : HasDerivAt (fun s : ℝ => Real.sqrt s)
        (1 / (2 * Real.sqrt (‖z‖ ^ 2 + c))) (‖z‖ ^ 2 + c) :=
      Real.hasDerivAt_sqrt (ne_of_gt hpos)
    have h2 : HasDerivAt (fun s : ℝ => (Real.sqrt s)⁻¹)
        (-(1 / (2 * Real.sqrt (‖z‖ ^ 2 + c))) / (Real.sqrt (‖z‖ ^ 2 + c)) ^ 2)
        (‖z‖ ^ 2 + c) :=
      h1.inv (by positivity)
    have h3 := h2.const_mul ((4 * Real.pi)⁻¹)
    rw [h3.deriv]
  have hinner : (fderiv ℝ (fun z : R3 => ‖z‖ ^ 2 + c) z) (FiniteTimeSingularity.e i)
      = 2 * z i := by
    have h := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt).add_const c
    rw [h.fderiv]
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul,
      Work.FTS.PressureOn.Green.inner_e_eq]
    ring
  rw [show regN c = (fun s : ℝ => (4 * Real.pi)⁻¹ * (Real.sqrt s)⁻¹) ∘
      (fun z : R3 => ‖z‖ ^ 2 + c) from rfl,
    fderiv_comp (x := z) hr hg, ContinuousLinearMap.comp_apply, fderiv_real_apply, hderiv,
    hinner]
  field_simp

theorem norm_fderiv_regN_apply_le (c : ℝ) (hc : 0 < c) (z : R3) (i : Fin 3) :
    ‖fderiv ℝ (regN c) z (FiniteTimeSingularity.e i)‖ ≤ (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [fderiv_regN_apply c hc 0 i]
    simp
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hG : ‖z‖ ≤ Real.sqrt (‖z‖ ^ 2 + c) := by
      calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
        _ ≤ Real.sqrt (‖z‖ ^ 2 + c) := Real.sqrt_le_sqrt (by linarith)
    have hGpos : 0 < Real.sqrt (‖z‖ ^ 2 + c) := lt_of_lt_of_le hzpos hG
    have hinv : ((Real.sqrt (‖z‖ ^ 2 + c))⁻¹) ^ 3 ≤ (‖z‖⁻¹) ^ 3 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 3
      exact (inv_le_inv₀ hGpos hzpos).mpr hG
    rw [fderiv_regN_apply c hc z i, Real.norm_eq_abs, abs_mul, abs_neg, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 * Real.pi)⁻¹),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((Real.sqrt (‖z‖ ^ 2 + c))⁻¹) ^ 3)]
    have hzi : |z i| ≤ ‖z‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
    have hstep : ((Real.sqrt (‖z‖ ^ 2 + c))⁻¹) ^ 3 * |z i| ≤ (‖z‖⁻¹) ^ 3 * ‖z‖ :=
      mul_le_mul hinv hzi (abs_nonneg _) (by positivity)
    calc (4 * Real.pi)⁻¹ * ((Real.sqrt (‖z‖ ^ 2 + c))⁻¹) ^ 3 * |z i|
        = (4 * Real.pi)⁻¹ * (((Real.sqrt (‖z‖ ^ 2 + c))⁻¹) ^ 3 * |z i|) := by ring
      _ ≤ (4 * Real.pi)⁻¹ * ((‖z‖⁻¹) ^ 3 * ‖z‖) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := by
          rw [mul_inv]
          field_simp

theorem tendsto_regN (z : R3) (hz : z ≠ 0) :
    Filter.Tendsto (fun c : ℝ => regN c z) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (newtonKernel z)) := by
  have hcont : ContinuousAt (fun c : ℝ => (4 * Real.pi)⁻¹ * (Real.sqrt (‖z‖ ^ 2 + c))⁻¹) 0 := by
    refine ContinuousAt.mul continuousAt_const ?_
    refine ContinuousAt.inv₀ ?_ ?_
    · exact Real.continuous_sqrt.continuousAt.comp (continuousAt_const.add continuousAt_id)
    · rw [add_zero, Real.sqrt_sq (norm_nonneg z)]
      exact norm_ne_zero_iff.mpr hz
  have hval : (fun c : ℝ => (4 * Real.pi)⁻¹ * (Real.sqrt (‖z‖ ^ 2 + c))⁻¹) 0
      = newtonKernel z := by
    rw [newtonKernel, mul_inv]
    simp only [add_zero, Real.sqrt_sq (norm_nonneg z)]
    ring
  rw [← hval]
  exact hcont.tendsto.mono_left nhdsWithin_le_nhds

theorem tendsto_fderiv_regN (z : R3) (hz : z ≠ 0) (i : Fin 3) :
    Filter.Tendsto (fun c : ℝ => fderiv ℝ (regN c) z (FiniteTimeSingularity.e i))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (fderiv ℝ newtonKernel z (FiniteTimeSingularity.e i))) := by
  have hcont : ContinuousAt (fun c : ℝ => ((Real.sqrt (‖z‖ ^ 2 + c))⁻¹) ^ 3) 0 := by
    have h1 : ContinuousAt (fun c : ℝ => Real.sqrt (‖z‖ ^ 2 + c)) 0 :=
      Real.continuous_sqrt.continuousAt.comp (continuousAt_const.add continuousAt_id)
    have h2 : (fun c : ℝ => Real.sqrt (‖z‖ ^ 2 + c)) 0 ≠ 0 := by
      show Real.sqrt (‖z‖ ^ 2 + 0) ≠ 0
      rw [add_zero, Real.sqrt_sq (norm_nonneg z)]
      exact norm_ne_zero_iff.mpr hz
    exact (h1.inv₀ h2).pow 3
  have hfun : Filter.Tendsto (fun c : ℝ => fderiv ℝ (regN c) z (FiniteTimeSingularity.e i))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (-((4 * Real.pi)⁻¹ * ((Real.sqrt (‖z‖ ^ 2 + 0))⁻¹) ^ 3) * z i)) := by
    refine ((continuousAt_const.mul hcont).neg.mul continuousAt_const).tendsto.mono_left
      nhdsWithin_le_nhds |>.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact (fderiv_regN_apply c hc z i).symm
  have hval : -((4 * Real.pi)⁻¹ * ((Real.sqrt (‖z‖ ^ 2 + 0))⁻¹) ^ 3) * z i
      = fderiv ℝ newtonKernel z (FiniteTimeSingularity.e i) := by
    rw [add_zero, Real.sqrt_sq (norm_nonneg z), ← inner_e_newtonGrad_tmp z i, real_inner_comm,
      Work.FTS.PressureOn.Green.inner_e_eq, newtonGrad_apply, inv_pow, mul_inv]
    simp only [smul_eq_mul, WithLp.ofLp_smul, Pi.smul_apply]
  rwa [hval] at hfun

/-! ## The two limits of the regularised identity -/

/-- A uniform bound for `∂ᵢ(laplaceTrace Ψ)` with the ball indicator. -/
theorem exists_bound_fderiv_laplaceTrace {Ψ : R3 → ℝ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ)
    (hcs : HasCompactSupport Ψ) (i : Fin 3) :
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ z : R3,
      ‖fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i)‖
        ≤ C * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) z := by
  have hcont : Continuous (fun z : R3 => fderiv ℝ (laplaceTrace Ψ) z
      (FiniteTimeSingularity.e i)) :=
    (contDiff_fderiv_apply_e_of (contDiff_two_laplaceTrace hΨ) i).continuous
  obtain ⟨R, hR⟩ := exists_ball_tsupport_subset (hasCompactSupport_fderiv_apply_e
    (hasCompactSupport_laplaceTrace hcs) i)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : R3) R).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, R, le_max_right _ _, fun z => ?_⟩
  by_cases hzc : z ∈ Metric.closedBall (0 : R3) R
  · rw [Set.indicator_of_mem hzc, mul_one]
    exact le_trans (hC z hzc) (le_max_left _ _)
  · rw [Set.indicator_of_notMem hzc, mul_zero]
    have hzts : z ∉ tsupport (fun x : R3 => fderiv ℝ (laplaceTrace Ψ) x
        (FiniteTimeSingularity.e i)) :=
      fun hm => hzc (Metric.ball_subset_closedBall (hR hm))
    have h0 : fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun x : R3 =>
        fderiv ℝ (laplaceTrace Ψ) x (FiniteTimeSingularity.e i)) hzts
    rw [h0, norm_zero]

theorem integrable_newtonKernel_mul_fderiv_laplaceTrace {Ψ : R3 → ℝ}
    (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (hcs : HasCompactSupport Ψ) (i : Fin 3) :
    MeasureTheory.Integrable (fun z : R3 => newtonKernel z *
      fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i)) := by
  obtain ⟨C, R, hC0, hC⟩ := exists_bound_fderiv_laplaceTrace hΨ hcs i
  have hcont : Continuous (fun z : R3 => fderiv ℝ (laplaceTrace Ψ) z
      (FiniteTimeSingularity.e i)) :=
    (contDiff_fderiv_apply_e_of (contDiff_two_laplaceTrace hΨ) i).continuous
  have hdom : MeasureTheory.Integrable (fun z : R3 =>
      C * (Metric.closedBall (0 : R3) R).indicator newtonKernel z) volume :=
    (((Work.FTS.PressureOn.Green.integrableOn_newtonKernel_ball (R + 1)).mono_set
      (fun z hz => by
        rw [Metric.mem_closedBall, dist_zero_right] at hz
        rw [Metric.mem_ball, dist_zero_right]
        linarith)).integrable_indicator measurableSet_closedBall).const_mul C
  refine hdom.mono' ?_ ?_
  · exact (Work.FTS.PressureOn.Green.measurable_newtonKernel.mul
      hcont.measurable).aestronglyMeasurable
  · filter_upwards with z
    by_cases hzc : z ∈ Metric.closedBall (0 : R3) R
    · rw [Set.indicator_of_mem hzc]
      have hnk : 0 ≤ newtonKernel z := by rw [newtonKernel]; positivity
      have h1 := hC z
      rw [Set.indicator_of_mem hzc, mul_one] at h1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnk, ← Real.norm_eq_abs]
      calc newtonKernel z * ‖fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i)‖
          ≤ newtonKernel z * C := mul_le_mul_of_nonneg_left h1 hnk
        _ = C * newtonKernel z := by ring
    · have hz0 : ‖fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i)‖ ≤ 0 := by
        have h := hC z
        rwa [Set.indicator_of_notMem hzc, mul_zero] at h
      rw [norm_le_zero_iff.mp hz0, Set.indicator_of_notMem hzc, mul_zero, mul_zero, norm_zero]

theorem tendsto_integral_regN_mul_fderiv_laplaceTrace (Ψ : R3 → ℝ)
    (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (hcs : HasCompactSupport Ψ) (i : Fin 3) :
    Filter.Tendsto (fun c : ℝ => ∫ z : R3,
        regN c z * fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ z : R3, newtonKernel z *
        fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i))) := by
  obtain ⟨C, R, hC0, hC⟩ := exists_bound_fderiv_laplaceTrace hΨ hcs i
  have hcont : Continuous (fun z : R3 => fderiv ℝ (laplaceTrace Ψ) z
      (FiniteTimeSingularity.e i)) :=
    (contDiff_fderiv_apply_e_of (contDiff_two_laplaceTrace hΨ) i).continuous
  have hdom : MeasureTheory.Integrable (fun z : R3 =>
      C * (Metric.closedBall (0 : R3) R).indicator newtonKernel z) volume :=
    (((Work.FTS.PressureOn.Green.integrableOn_newtonKernel_ball (R + 1)).mono_set
      (fun z hz => by
        rw [Metric.mem_closedBall, dist_zero_right] at hz
        rw [Metric.mem_ball, dist_zero_right]
        linarith)).integrable_indicator measurableSet_closedBall).const_mul C
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun z : R3 => C * (Metric.closedBall (0 : R3) R).indicator newtonKernel z) ?_ ?_
    hdom ?_
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact ((contDiff_one_regN c hc).continuous.mul hcont).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with c hc
    filter_upwards [ae_ne_zero_volume] with z hz
    have hregnn : 0 ≤ regN c z := by rw [regN_apply]; positivity
    have hnknn : 0 ≤ newtonKernel z := by rw [newtonKernel]; positivity
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have h1 : ‖z‖ ≤ Real.sqrt (‖z‖ ^ 2 + c) := by
      calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
        _ ≤ Real.sqrt (‖z‖ ^ 2 + c) := Real.sqrt_le_sqrt (le_add_of_nonneg_right (le_of_lt hc))
    have h2 : (Real.sqrt (‖z‖ ^ 2 + c))⁻¹ ≤ ‖z‖⁻¹ :=
      (inv_le_inv₀ (lt_of_lt_of_le hzpos h1) hzpos).mpr h1
    have hle : regN c z ≤ ‖newtonKernel z‖ := by
      calc regN c z = (4 * Real.pi)⁻¹ * (Real.sqrt (‖z‖ ^ 2 + c))⁻¹ := rfl
        _ ≤ (4 * Real.pi)⁻¹ * ‖z‖⁻¹ := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = ‖newtonKernel z‖ := by
            rw [newtonKernel, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            field_simp
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hregnn]
    calc regN c z * ‖fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i)‖
        ≤ ‖newtonKernel z‖ * (C * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) z) :=
          mul_le_mul hle (hC z) (norm_nonneg _) (norm_nonneg _)
      _ = C * (Metric.closedBall (0 : R3) R).indicator newtonKernel z := by
          by_cases hzc : z ∈ Metric.closedBall (0 : R3) R
          · rw [Set.indicator_of_mem hzc, Set.indicator_of_mem hzc, mul_one]
            rw [Real.norm_eq_abs, abs_of_nonneg hnknn]
            ring
          · rw [Set.indicator_of_notMem hzc, Set.indicator_of_notMem hzc, mul_zero, mul_zero]
  · filter_upwards [ae_ne_zero_volume] with z hz
    exact (tendsto_regN z hz).mul tendsto_const_nhds

theorem tendsto_integral_laplaceTrace_mul_fderiv_regN (Ψ : R3 → ℝ)
    (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (hcs : HasCompactSupport Ψ) (i : Fin 3) :
    Filter.Tendsto (fun c : ℝ => ∫ z : R3,
        laplaceTrace Ψ z * fderiv ℝ (regN c) z (FiniteTimeSingularity.e i))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ z : R3, laplaceTrace Ψ z *
        fderiv ℝ newtonKernel z (FiniteTimeSingularity.e i))) := by
  obtain ⟨R, hR⟩ := exists_ball_tsupport_subset (hasCompactSupport_laplaceTrace hcs)
  obtain ⟨C, hC⟩ := (hasCompactSupport_laplaceTrace hcs).exists_bound_of_continuous
    (Work.FTS.PressureOn.Green.continuous_laplaceTrace Ψ (hΨ 2))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hdom : MeasureTheory.Integrable (fun z : R3 => C * ((4 * Real.pi)⁻¹ *
      ((‖z‖ ^ 2)⁻¹ * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) z)))
      volume := by
    refine (((Work.FTS.PressureOn.integrable_inv_normSq_indicator_closedBall R).const_mul
      C).const_mul ((4 * Real.pi)⁻¹)).congr ?_
    filter_upwards with z
    ring
  have hΔ : ∀ z : R3, ‖laplaceTrace Ψ z‖
      ≤ C * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hzc : z ∈ Metric.closedBall (0 : R3) R
    · rw [Set.indicator_of_mem hzc, mul_one]
      exact hC z
    · rw [Set.indicator_of_notMem hzc, mul_zero]
      have hzts : z ∉ tsupport (laplaceTrace Ψ) :=
        fun hm => hzc (Metric.ball_subset_closedBall (hR hm))
      rw [image_eq_zero_of_notMem_tsupport hzts, norm_zero]
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun z : R3 => C * ((4 * Real.pi)⁻¹ *
      ((‖z‖ ^ 2)⁻¹ * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) z))) ?_ ?_
    hdom ?_
  · filter_upwards [self_mem_nhdsWithin] with c hc
    have hker : Continuous (fun z : R3 => fderiv ℝ (regN c) z (FiniteTimeSingularity.e i)) :=
      ((contDiff_one_regN c hc).continuous_fderiv_apply (by norm_num)).comp
        (continuous_id.prodMk continuous_const)
    exact ((Work.FTS.PressureOn.Green.continuous_laplaceTrace Ψ (hΨ 2)).mul hker).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with c hc
    filter_upwards with z
    rw [norm_mul]
    have hker : ‖fderiv ℝ (regN c) z (FiniteTimeSingularity.e i)‖
        ≤ (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := norm_fderiv_regN_apply_le c hc z i
    calc ‖laplaceTrace Ψ z‖ * ‖fderiv ℝ (regN c) z (FiniteTimeSingularity.e i)‖
        ≤ (C * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) z)
            * ((4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) := by
          refine mul_le_mul (hΔ z) hker (norm_nonneg _) ?_
          exact mul_nonneg hC0 (Set.indicator_nonneg (fun _ _ => zero_le_one) z)
      _ = C * ((4 * Real.pi)⁻¹ *
            ((‖z‖ ^ 2)⁻¹ * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) z)) := by
          ring
  · filter_upwards [ae_ne_zero_volume] with z hz
    exact tendsto_const_nhds.mul (tendsto_fderiv_regN z hz i)

theorem regN_ibp {Ψ : R3 → ℝ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (hcs : HasCompactSupport Ψ)
    {c : ℝ} (hc : 0 < c) (i : Fin 3) :
    ∫ z, laplaceTrace Ψ z * fderiv ℝ (regN c) z (FiniteTimeSingularity.e i)
      = -∫ z, regN c z * fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i) := by
  have h := integral_fderiv_mul_eq_neg (g := regN c) (h := laplaceTrace Ψ)
    (contDiff_one_regN c hc) (contDiff_one_laplaceTrace hΨ)
    (hasCompactSupport_laplaceTrace hcs) i
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  ring

/-! ## The centred scalar identity -/

/-- **The centred scalar identity**: `∫ ΔΨ · ∂ᵢN = ∂ᵢΨ(0)`. -/
theorem kernelGrad_coord {Ψ : R3 → ℝ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (hcs : HasCompactSupport Ψ)
    (i : Fin 3) :
    ∫ z, laplaceTrace Ψ z * fderiv ℝ newtonKernel z (FiniteTimeSingularity.e i)
      = fderiv ℝ Ψ 0 (FiniteTimeSingularity.e i) := by
  have hL := tendsto_integral_laplaceTrace_mul_fderiv_regN Ψ hΨ hcs i
  have hR := tendsto_integral_regN_mul_fderiv_laplaceTrace Ψ hΨ hcs i
  have hRlim : (∫ z : R3, newtonKernel z * fderiv ℝ (laplaceTrace Ψ) z
      (FiniteTimeSingularity.e i)) = -fderiv ℝ Ψ 0 (FiniteTimeSingularity.e i) := by
    have hone : (∫ z : R3, newtonKernel z * fderiv ℝ (laplaceTrace Ψ) z
          (FiniteTimeSingularity.e i))
        = ∫ z : R3, newtonKernel z * laplaceTrace
            (fun z' : R3 => fderiv ℝ Ψ z' (FiniteTimeSingularity.e i)) z := by
      refine integral_congr_ae ?_
      filter_upwards with z
      rw [show fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i)
          = laplaceTrace (fun z' : R3 => fderiv ℝ Ψ z' (FiniteTimeSingularity.e i)) z from
        congrFun (laplaceTrace_fderiv_comm (hΨ 3) i).symm z]
    rw [hone]
    have h := kernelIntegral (contDiff_fderiv_apply_e_all hΨ i)
      (hasCompactSupport_fderiv_apply_e hcs i) 0
    simpa using h
  have hR' : Filter.Tendsto (fun c : ℝ => ∫ z : R3,
        regN c z * fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (-(fderiv ℝ Ψ 0 (FiniteTimeSingularity.e i)))) := by
    rw [hRlim] at hR
    exact hR
  have hneg : Filter.Tendsto (fun c : ℝ => -(∫ z : R3,
        regN c z * fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (fderiv ℝ Ψ 0 (FiniteTimeSingularity.e i))) := by
    simpa using hR'.neg
  have hId : (fun c : ℝ => ∫ z : R3, laplaceTrace Ψ z *
        fderiv ℝ (regN c) z (FiniteTimeSingularity.e i))
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun c : ℝ => -(∫ z : R3,
        regN c z * fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i))) := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact regN_ibp hΨ hcs hc i
  exact tendsto_nhds_unique hL (hneg.congr' hId.symm)

end kgiAux

end Work.FTS.PressureOn.PoissonAux

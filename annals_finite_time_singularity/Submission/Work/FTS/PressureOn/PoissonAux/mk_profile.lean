/-
# Auxiliary profile facts for the mass kernel

This module collects the one-dimensional facts about the profile
`rhoProfile ε r = 1 - χ(r²/ε²)` (with `χ = radialCut`) that the proof of
`Work.FTS.PressureOn.PoissonAux.tendsto_integral_massKernel_mul` needs:

* smoothness of `rhoProfile ε`;
* local constancy off the transition annulus `[ε, √2 ε]` (`mk_rhoProfile_eventuallyEq_zero`,
  `mk_rhoProfile_eventuallyEq_one`) and hence the vanishing of `ρ_ε''` there
  (`mk_deriv_deriv_rhoProfile_eq_zero`);
* the scaling identity `ρ_ε''(r) = ρ_1''(r/ε)/ε²`
  (`mk_deriv_deriv_rhoProfile_div`) and the resulting uniform bound
  `|ρ_ε''(r)| ≤ B/ε²` (`mk_exists_bound_deriv_deriv_rhoProfile`);
* the total-mass identity `∫_0^∞ r ρ_ε''(r) dr = -1`
  (`mk_integral_mul_deriv_deriv_rhoProfile`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PressureOn.PoissonAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology Metric
open scoped Topology ENNReal NNReal

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

/-! ## Smoothness -/

theorem mk_contDiff_rhoProfile (ε : ℝ) (n : ℕ∞) : ContDiff ℝ n (rhoProfile ε) := by
  have h : ContDiff ℝ n (fun r : ℝ => radialCut (r ^ 2 / ε ^ 2)) :=
    (contDiff_radialCut n).comp ((contDiff_id.pow 2).div_const (ε ^ 2))
  exact contDiff_const.sub h

theorem mk_continuous_deriv_deriv_rhoProfile (ε : ℝ) :
    Continuous (deriv (deriv (rhoProfile ε))) := by
  have h : ContDiff ℝ 2 (rhoProfile ε) := mk_contDiff_rhoProfile ε 2
  have h2 : ContDiff ℝ 0 (deriv (deriv (rhoProfile ε))) := (h.deriv').deriv'
  exact h2.continuous

/-! ## Local constancy off the transition annulus -/

theorem mk_rhoProfile_eventuallyEq_zero {ε r : ℝ} (hε : 0 < ε) (hr : |r| < ε) :
    rhoProfile ε =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
  have hpos : 0 < ε - |r| := by linarith
  filter_upwards [Metric.ball_mem_nhds r hpos] with s hs
  rw [Metric.mem_ball, Real.dist_eq] at hs
  have hs' : |s| < ε := by
    have h1 : |s - r| < ε - |r| := hs
    have h2 : |s| ≤ |s - r| + |r| := by
      calc |s| = |s - r + r| := by ring_nf
        _ ≤ |s - r| + |r| := abs_add_le (s - r) r
    linarith
  have hs2 : s ^ 2 ≤ ε ^ 2 := by
    have h3 : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
    have h4 : ε ^ 2 = |ε| ^ 2 := (sq_abs ε).symm
    rw [h3, h4, abs_of_pos hε]
    nlinarith [abs_nonneg s, abs_lt.mp hs']
  rw [rhoProfile_apply, radialCut_eq_one (by rw [div_le_one (by positivity)]; exact hs2), sub_self]

theorem mk_rhoProfile_eventuallyEq_one {ε r : ℝ} (hε : 0 < ε)
    (hr : Real.sqrt 2 * ε < |r|) : rhoProfile ε =ᶠ[𝓝 r] fun _ => (1 : ℝ) := by
  have hpos : 0 < |r| - Real.sqrt 2 * ε := by linarith
  filter_upwards [Metric.ball_mem_nhds r hpos] with s hs
  rw [Metric.mem_ball, Real.dist_eq] at hs
  have hs' : Real.sqrt 2 * ε < |s| := by
    have h1 : |s - r| < |r| - Real.sqrt 2 * ε := hs
    have h2 : |r| - |s| ≤ |s - r| := by
      rw [abs_sub_comm s r]
      exact abs_sub_abs_le_abs_sub r s
    linarith
  have h2 : 2 * ε ^ 2 ≤ s ^ 2 := by
    have h3 : 0 ≤ Real.sqrt 2 * ε := by positivity
    have h4 : (Real.sqrt 2 * ε) ^ 2 < |s| ^ 2 := by nlinarith [abs_nonneg s]
    have h5 : (Real.sqrt 2 * ε) ^ 2 = 2 * ε ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have h6 : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
    rw [h6]
    linarith
  rw [rhoProfile_apply, radialCut_eq_zero (by rw [le_div_iff₀ (by positivity)]; exact h2), sub_zero]

/-- The second derivative of the profile vanishes off the transition annulus. -/
theorem mk_deriv_deriv_rhoProfile_eq_zero {ε r : ℝ} (hε : 0 < ε)
    (hr : |r| < ε ∨ Real.sqrt 2 * ε < |r|) :
    deriv (deriv (rhoProfile ε)) r = 0 := by
  rcases hr with hr | hr
  · have h1 : deriv (rhoProfile ε) =ᶠ[𝓝 r] fun _ : ℝ => (0 : ℝ) := by
      have h := (mk_rhoProfile_eventuallyEq_zero hε hr).deriv
      rwa [deriv_const'] at h
    rw [h1.deriv_eq]
    exact deriv_const r 0
  · have h1 : deriv (rhoProfile ε) =ᶠ[𝓝 r] fun _ : ℝ => (0 : ℝ) := by
      have h := (mk_rhoProfile_eventuallyEq_one hε hr).deriv
      rwa [deriv_const'] at h
    rw [h1.deriv_eq]
    exact deriv_const r 0

/-! ## The scaling identity `ρ_ε''(r) = ρ_1''(r/ε)/ε²` -/

theorem mk_deriv_rhoProfile_eq {ε : ℝ} (_hε : 0 < ε) :
    deriv (rhoProfile ε)
      = (deriv (rhoProfile 1)) ∘ (fun s : ℝ => s / ε) * fun _ : ℝ => ε⁻¹ := by
  have hfun : rhoProfile ε = (rhoProfile 1) ∘ (fun s : ℝ => s / ε) := by
    funext s
    simp only [Function.comp_apply, rhoProfile_apply, one_pow, div_one, div_pow]
  funext r
  rw [hfun]
  have hA : HasDerivAt (fun t : ℝ => t / ε) (ε⁻¹) r := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id r).div_const ε
  have hB : HasDerivAt (rhoProfile 1) (deriv (rhoProfile 1) (r / ε)) (r / ε) :=
    (((mk_contDiff_rhoProfile 1 1).differentiable (by norm_num)).differentiableAt).hasDerivAt
  have h3 := hB.comp r hA
  rw [h3.deriv]
  simp only [Pi.mul_apply, Function.comp_apply]

theorem mk_deriv_deriv_rhoProfile_div (ε : ℝ) (hε : 0 < ε) (r : ℝ) :
    deriv (deriv (rhoProfile ε)) r = deriv (deriv (rhoProfile 1)) (r / ε) / ε ^ 2 := by
  rw [mk_deriv_rhoProfile_eq hε]
  have hA : HasDerivAt (fun t : ℝ => t / ε) (ε⁻¹) r := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id r).div_const ε
  have hB : HasDerivAt (deriv (rhoProfile 1)) (deriv (deriv (rhoProfile 1)) (r / ε)) (r / ε) :=
    (((mk_contDiff_rhoProfile 1 2).differentiable_deriv_two).differentiableAt).hasDerivAt
  have hC := hB.comp r hA
  have hD : HasDerivAt ((deriv (rhoProfile 1)) ∘ (fun t : ℝ => t / ε) * fun _ : ℝ => ε⁻¹)
      ((deriv (deriv (rhoProfile 1)) (r / ε) * ε⁻¹) * ε⁻¹
        + deriv (rhoProfile 1) (r / ε) * 0) r :=
    hC.mul (hasDerivAt_const r ε⁻¹)
  rw [hD.deriv]
  have hε2 : (ε : ℝ)⁻¹ * ε⁻¹ = (ε ^ 2)⁻¹ := by rw [← inv_pow, pow_two]
  have hval : (deriv (deriv (rhoProfile 1)) (r / ε) * ε⁻¹) * ε⁻¹
        + deriv (rhoProfile 1) (r / ε) * 0
      = deriv (deriv (rhoProfile 1)) (r / ε) * (ε ^ 2)⁻¹ := by
    rw [← hε2]
    ring
  rw [hval]
  exact (div_eq_mul_inv _ _).symm

/-! ## The uniform bound on the second derivative -/

theorem mk_sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

theorem mk_exists_bound_rhoProfile_one :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, |deriv (deriv (rhoProfile (1 : ℝ))) r| ≤ B := by
  have hcont : Continuous (fun r : ℝ => deriv (deriv (rhoProfile (1 : ℝ))) r) :=
    mk_continuous_deriv_deriv_rhoProfile 1
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (f := fun r : ℝ => deriv (deriv (rhoProfile (1 : ℝ))) r) hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun r => ?_⟩
  by_cases hr : |r| ≤ 2
  · exact le_trans (hC r (by rw [Set.mem_Icc]; exact abs_le.mp hr)) (le_max_left _ _)
  · have hrs : Real.sqrt 2 < |r| := by
      have h2 : 2 < |r| := lt_of_not_ge hr
      linarith [mk_sqrt_two_lt_two]
    rw [mk_deriv_deriv_rhoProfile_eq_zero one_pos (Or.inr (by simpa using hrs)), abs_zero]
    exact le_max_right _ _

theorem mk_exists_bound_deriv_deriv_rhoProfile :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ε : ℝ), 0 < ε → ∀ r : ℝ,
      |deriv (deriv (rhoProfile ε)) r| ≤ B / ε ^ 2 := by
  obtain ⟨B, hB0, hB⟩ := mk_exists_bound_rhoProfile_one
  refine ⟨B, hB0, fun ε hε r => ?_⟩
  rw [mk_deriv_deriv_rhoProfile_div ε hε r, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ε ^ 2)]
  exact div_le_div_of_nonneg_right (hB (r / ε)) (by positivity)

/-! ## The total mass `∫_0^∞ r ρ_ε''(r) dr = -1` -/

theorem mk_integral_mul_deriv_deriv_rhoProfile (ε : ℝ) (hε : 0 < ε) :
    ∫ r in Set.Ioi (0 : ℝ), r * deriv (deriv (rhoProfile ε)) r = -1 := by
  have hRpos : 0 < Real.sqrt 2 * ε + 1 := by
    have h1 : 0 ≤ Real.sqrt 2 * ε := mul_nonneg (Real.sqrt_nonneg 2) hε.le
    linarith
  have hRgt : Real.sqrt 2 * ε < Real.sqrt 2 * ε + 1 := by linarith
  have hzero : ∀ r ∈ Set.Ioi (0 : ℝ) \ Set.Ioc 0 (Real.sqrt 2 * ε + 1),
      r * deriv (deriv (rhoProfile ε)) r = 0 := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    have hrR : Real.sqrt 2 * ε + 1 < r := by
      by_contra h
      exact hr2 ⟨hr1, not_lt.mp h⟩
    rw [mk_deriv_deriv_rhoProfile_eq_zero hε
      (Or.inr (by rw [abs_of_pos hr1]; linarith)), mul_zero]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume)
    (s := Set.Ioc 0 (Real.sqrt 2 * ε + 1)) (t := Set.Ioi (0 : ℝ))
    measurableSet_Ioi (fun r hr => hr.1) hzero]
  rw [← intervalIntegral.integral_of_le hRpos.le]
  have hderiv : ∀ r ∈ Set.uIcc (0 : ℝ) (Real.sqrt 2 * ε + 1),
      HasDerivAt (fun s : ℝ => s * deriv (rhoProfile ε) s - rhoProfile ε s)
        (r * deriv (deriv (rhoProfile ε)) r) r := by
    intro r _
    have hρ : HasDerivAt (rhoProfile ε) (deriv (rhoProfile ε) r) r :=
      (((mk_contDiff_rhoProfile ε 1).differentiable (by norm_num)).differentiableAt).hasDerivAt
    have hρ' : HasDerivAt (deriv (rhoProfile ε)) (deriv (deriv (rhoProfile ε)) r) r :=
      (((mk_contDiff_rhoProfile ε 2).differentiable_deriv_two).differentiableAt).hasDerivAt
    have h1 : HasDerivAt (fun s : ℝ => s * deriv (rhoProfile ε) s)
        (1 * deriv (rhoProfile ε) r + r * deriv (deriv (rhoProfile ε)) r) r :=
      (hasDerivAt_id r).mul hρ'
    have h2 := h1.sub hρ
    convert h2 using 1; ring
  have hint : IntervalIntegrable (fun r : ℝ => r * deriv (deriv (rhoProfile ε)) r)
      volume 0 (Real.sqrt 2 * ε + 1) :=
    (continuous_id.mul (mk_continuous_deriv_deriv_rhoProfile ε)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hFR : deriv (rhoProfile ε) (Real.sqrt 2 * ε + 1) = 0 := by
    have h : rhoProfile ε =ᶠ[𝓝 (Real.sqrt 2 * ε + 1)] fun _ => (1 : ℝ) :=
      mk_rhoProfile_eventuallyEq_one hε (by rw [abs_of_pos hRpos]; exact hRgt)
    rw [h.deriv_eq, deriv_const']
  have hρR : rhoProfile ε (Real.sqrt 2 * ε + 1) = 1 := by
    refine rhoProfile_eq_one hε ?_
    have h2 : (Real.sqrt 2 * ε) ^ 2 < (Real.sqrt 2 * ε + 1) ^ 2 := by
      nlinarith [Real.sqrt_nonneg 2, hε]
    have h3 : (Real.sqrt 2 * ε) ^ 2 = 2 * ε ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hρ0 : rhoProfile ε 0 = 0 := rhoProfile_eq_zero hε (by simpa using sq_nonneg ε)
  rw [hFR, hρR, hρ0]
  ring

end Work.FTS.PressureOn.PoissonAux

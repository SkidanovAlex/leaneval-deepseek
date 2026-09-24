import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Submission.Commons.Analysis.Fresnel.cexp_neg_mul_sq_interval_bound
import Submission.Commons.Analysis.Fresnel.cpow_pi_div_mul_I
import Submission.Commons.Analysis.Fresnel.tendsto_intervalIntegral_cexp_gauss

namespace Commons.Analysis.Fresnel

open Complex MeasureTheory intervalIntegral Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 0

/-- **Fresnel integral on `[0,U]`.**  For `l > 0` and `U > 0`,
`∫_0^U exp(-i l u²) du = (√(π/l)/2)·exp(-iπ/4) + O(1/(lU))`, with explicit constant `3`.

This is the boundary case `Re b = 0` of the complex Gaussian integral: Mathlib's
`integral_gaussian_complex` gives `∫_ℝ exp(-b u²) = (π/b)^(1/2)` for `Re b > 0`, and the
value above follows by letting `b → i l` through `Re b > 0`, using the uniform
integration-by-parts tail bound `‖∫_t^∞ exp(-i l u²) du‖ ≤ 1/(l t)`. -/
theorem fresnel_interval (l U : ℝ) (hl : 0 < l) (hU : 0 < U) :
    ‖(∫ u in (0:ℝ)..U, Complex.exp (-((l : ℂ) * Complex.I) * (u : ℂ)^2))
      - (((Real.sqrt (Real.pi / l) / 2 : ℝ)) : ℂ) * Complex.exp (-(Real.pi / 4) * Complex.I)‖
    ≤ 3 / (l * U) := by
  -- Regularised Fresnel integral `I ε` and the corresponding Gaussian value `W ε`.
  set I : ℝ → ℂ :=
    fun ε => ∫ u in (0:ℝ)..U, Complex.exp (-(((ε : ℂ) + (l : ℂ) * Complex.I)) * (u : ℂ)^2)
    with hI
  set W : ℝ → ℂ :=
    fun ε => ((Real.pi : ℂ) / ((ε : ℂ) + (l : ℂ) * Complex.I)) ^ (1 / 2 : ℂ) / 2 with hW
  -- The key estimate: for `ε > 0` the difference of the two sides is a Gaussian tail.
  have hkey : ∀ ε : ℝ, 0 < ε → ‖I ε - W ε‖ ≤ 1 / (l * U) := by
    intro ε hε
    set c : ℂ := (ε : ℂ) + (l : ℂ) * Complex.I with hc
    have hcre : 0 < c.re := by
      rw [hc]
      simpa [Complex.add_re] using hε
    -- exact value of the half-line Gaussian integral, `Re c > 0`
    have hval : ∫ x in Set.Ioi (0:ℝ), Complex.exp (-c * (x : ℂ)^2) = (Real.pi / c) ^ (1/2 : ℂ) / 2 :=
      integral_gaussian_complex_Ioi hcre
    have hint : IntegrableOn (fun x : ℝ => Complex.exp (-c * (x : ℂ)^2)) (Set.Ioi (0:ℝ)) volume :=
      (integrable_cexp_neg_mul_sq hcre).integrableOn
    have hsplit : (∫ x in Set.Ioi (0:ℝ), Complex.exp (-c * (x : ℂ)^2))
        - (∫ x in Set.Ioi U, Complex.exp (-c * (x : ℂ)^2))
        = ∫ x in (0:ℝ)..U, Complex.exp (-c * (x : ℂ)^2) :=
      integral_Ioi_sub_Ioi hint hU.le
    -- uniform tail bound, obtained from the integration-by-parts bound on `[U,T]`
    have hintU : IntegrableOn (fun x : ℝ => Complex.exp (-c * (x : ℂ)^2)) (Set.Ioi U) volume :=
      (integrable_cexp_neg_mul_sq hcre).integrableOn
    have hlim : Tendsto (fun T : ℝ => ∫ u in U..T, Complex.exp (-c * (u : ℂ)^2)) atTop
        (𝓝 (∫ x in Set.Ioi U, Complex.exp (-c * (x : ℂ)^2))) :=
      intervalIntegral_tendsto_integral_Ioi U hintU tendsto_id
    have hcnorm : l ≤ ‖c‖ := by
      have h := Complex.abs_im_le_norm c
      have him : c.im = l := by
        rw [hc]; simp [Complex.add_im]
      rwa [him, abs_of_pos hl] at h
    have hconst : 1 / (‖c‖ * U) ≤ 1 / (l * U) := by
      have h1 : 0 < l * U := mul_pos hl hU
      have h2 : l * U ≤ ‖c‖ * U := mul_le_mul_of_nonneg_right hcnorm hU.le
      exact one_div_le_one_div_of_le h1 h2
    have htail : ‖∫ x in Set.Ioi U, Complex.exp (-c * (x : ℂ)^2)‖ ≤ 1 / (l * U) :=
      le_of_tendsto hlim.norm ((eventually_ge_atTop U).mono (fun T hT =>
        le_trans (cexp_neg_mul_sq_interval_bound c hcre hU hT) hconst))
    -- conclude for this `ε`
    have hIε : I ε = ∫ x in (0:ℝ)..U, Complex.exp (-c * (x : ℂ)^2) := by
      simp only [hI, hc]
    have hWε : W ε = (Real.pi / c) ^ (1/2 : ℂ) / 2 := by
      simp only [hW, hc]
    have hC : (∫ x in (0:ℝ)..U, Complex.exp (-c * (x : ℂ)^2))
        = (Real.pi / c) ^ (1/2 : ℂ) / 2 - ∫ x in Set.Ioi U, Complex.exp (-c * (x : ℂ)^2) := by
      rw [← hsplit, hval]
    rw [hIε, hWε, hC,
      show ((Real.pi / c) ^ (1 / 2 : ℂ) / 2 - (∫ x in Set.Ioi U, Complex.exp (-c * (x : ℂ)^2)))
          - (Real.pi / c) ^ (1 / 2 : ℂ) / 2
          = -(∫ x in Set.Ioi U, Complex.exp (-c * (x : ℂ)^2)) by ring,
      norm_neg]
    exact htail
  -- Continuity of both sides at `ε = 0⁺`.
  have hcontI : Tendsto I (𝓝[>] (0:ℝ))
      (𝓝 (∫ u in (0:ℝ)..U, Complex.exp (-(((l : ℂ) * Complex.I)) * (u : ℂ)^2))) := by
    simpa only [hI] using tendsto_intervalIntegral_cexp_gauss l U hl hU
  have hcontW : Tendsto W (𝓝[>] (0:ℝ))
      (𝓝 (((Real.pi : ℂ) / ((l : ℂ) * Complex.I)) ^ (1 / 2 : ℂ) / 2)) := by
    have hmem : ((Real.pi : ℂ) / ((l : ℂ) * Complex.I)) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      right
      rw [show (((Real.pi : ℂ) / ((l : ℂ) * Complex.I))).im = -(Real.pi / l) from by
        rw [Complex.div_im]
        simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
        field_simp]
      exact neg_ne_zero.mpr (div_ne_zero Real.pi_ne_zero hl.ne')
    have hcont : ContinuousAt (fun ε : ℝ => (Real.pi : ℂ) / ((ε : ℂ) + (l : ℂ) * Complex.I)) 0 := by
      apply ContinuousAt.div continuousAt_const ?_ ?_
      · fun_prop
      · simp [hl.ne']
    have h1 : Tendsto (fun ε : ℝ => (Real.pi : ℂ) / ((ε : ℂ) + (l : ℂ) * Complex.I)) (𝓝[>] (0:ℝ))
        (𝓝 ((Real.pi : ℂ) / ((l : ℂ) * Complex.I))) := by
      have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using h
    have h2 : Tendsto (fun z : ℂ => z ^ (1 / 2 : ℂ)) (𝓝 ((Real.pi : ℂ) / ((l : ℂ) * Complex.I)))
        (𝓝 (((Real.pi : ℂ) / ((l : ℂ) * Complex.I)) ^ (1 / 2 : ℂ))) :=
      (continuousAt_cpow_const hmem).tendsto
    simpa only [hW, Function.comp_apply] using (h2.comp h1).div_const 2
  -- Pass the estimate to the limit `ε → 0⁺`.
  have hlim : Tendsto (fun ε : ℝ => ‖I ε - W ε‖) (𝓝[>] (0:ℝ))
      (𝓝 ‖(∫ u in (0:ℝ)..U, Complex.exp (-(((l : ℂ) * Complex.I)) * (u : ℂ)^2))
        - ((Real.pi : ℂ) / ((l : ℂ) * Complex.I)) ^ (1 / 2 : ℂ) / 2‖) :=
    (hcontI.sub hcontW).norm
  have hbound : ‖(∫ u in (0:ℝ)..U, Complex.exp (-(((l : ℂ) * Complex.I)) * (u : ℂ)^2))
      - ((Real.pi : ℂ) / ((l : ℂ) * Complex.I)) ^ (1 / 2 : ℂ) / 2‖ ≤ 1 / (l * U) :=
    le_of_tendsto hlim (Filter.eventually_of_mem self_mem_nhdsWithin (fun ε hε => hkey ε hε))
  -- Identify the limiting value and weaken `1/(lU) ≤ 3/(lU)`.
  rw [cpow_pi_div_mul_I l hl] at hbound
  refine le_trans hbound ?_
  have h : 0 < l * U := mul_pos hl hU
  rw [div_le_div_iff_of_pos_right h]
  norm_num

end Commons.Analysis.Fresnel
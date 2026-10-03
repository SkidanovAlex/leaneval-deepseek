import Mathlib

namespace Commons.Analysis.Integral

open MeasureTheory intervalIntegral

/-- Pointwise lower bound: `√(1+y) ≥ 1 + y/2 - y²/8 + y³/32` for `y ∈ [0,1]`. -/
lemma sqrt_one_add_ge (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    1 + y / 2 - y ^ 2 / 8 + y ^ 3 / 32 ≤ Real.sqrt (1 + y) := by
  have hy2 : y ^ 2 ≤ 1 := by
    have : 0 ≤ (1 - y) * (1 + y) := mul_nonneg (by linarith) (by linarith)
    nlinarith [this]
  have hy3 : y ^ 3 ≤ 1 := by
    have : y ^ 2 * y ≤ 1 := by nlinarith [hy0, hy1, hy2]
    nlinarith [this]
  have hp : 0 ≤ 1 + y / 2 - y ^ 2 / 8 + y ^ 3 / 32 := by
    nlinarith [hy0, hy2, pow_nonneg hy0 3]
  have hq : 0 ≤ 64 - 48 * y + 8 * y ^ 2 - y ^ 3 := by
    nlinarith [hy1, hy3]
  have hfac : 1 + y - (1 + y / 2 - y ^ 2 / 8 + y ^ 3 / 32) ^ 2
      = y ^ 3 * (64 - 48 * y + 8 * y ^ 2 - y ^ 3) / 1024 := by ring
  have hnn : 0 ≤ y ^ 3 * (64 - 48 * y + 8 * y ^ 2 - y ^ 3) / 1024 :=
    div_nonneg (mul_nonneg (pow_nonneg hy0 3) hq) (by norm_num)
  have hsq : (1 + y / 2 - y ^ 2 / 8 + y ^ 3 / 32) ^ 2 ≤ 1 + y := by linarith
  exact Real.le_sqrt_of_sq_le hsq

/-- Pointwise bound for the integrand. -/
lemma sqrt_one_sub_pow_four_ge_pointwise (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sqrt (1 - x ^ 2) * (1 + x ^ 2 / 2 - x ^ 4 / 8 + x ^ 6 / 32) ≤ Real.sqrt (1 - x ^ 4) := by
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hx2le : x ^ 2 ≤ 1 := by nlinarith [hx0, hx1]
  have h1x2 : 0 ≤ 1 - x ^ 2 := by linarith
  have hfac : 1 - x ^ 4 = (1 - x ^ 2) * (1 + x ^ 2) := by ring
  rw [hfac, Real.sqrt_mul h1x2]
  have hmain := sqrt_one_add_ge (x ^ 2) hx2 hx2le
  have hmain' : 1 + x ^ 2 / 2 - x ^ 4 / 8 + x ^ 6 / 32 ≤ Real.sqrt (1 + x ^ 2) := by
    convert hmain using 1
    ring
  have hs : 0 ≤ Real.sqrt (1 - x ^ 2) := Real.sqrt_nonneg _
  exact mul_le_mul_of_nonneg_left hmain' hs

/-- `∫₀^{π/2} 1 = π/2`. -/
private lemma J0c : ∫ _ in (0:ℝ)..(Real.pi/2), (1:ℝ) = Real.pi / 2 := by simp

private lemma J2 : ∫ θ in (0:ℝ)..(Real.pi/2), Real.sin θ ^ 2 = Real.pi / 4 := by
  rw [integral_sin_sq]
  rw [Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

private lemma J4 : ∫ θ in (0:ℝ)..(Real.pi/2), Real.sin θ ^ 4 = 3 * Real.pi / 16 := by
  have h := integral_sin_pow (a := (0:ℝ)) (b := Real.pi/2) (n := 2)
  rw [h, Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two]
  rw [J2]
  ring

private lemma J6 : ∫ θ in (0:ℝ)..(Real.pi/2), Real.sin θ ^ 6 = 5 * Real.pi / 32 := by
  have h := integral_sin_pow (a := (0:ℝ)) (b := Real.pi/2) (n := 4)
  rw [h, Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two]
  rw [J4]
  ring

private lemma J8 : ∫ θ in (0:ℝ)..(Real.pi/2), Real.sin θ ^ 8 = 35 * Real.pi / 256 := by
  have h := integral_sin_pow (a := (0:ℝ)) (b := Real.pi/2) (n := 6)
  rw [h, Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two]
  rw [J6]
  ring

/-- Value of the trigonometric integral. -/
lemma integral_theta_main :
    (∫ θ in (0:ℝ)..(Real.pi/2),
        (1 - (Real.sin θ)^2/2 - 5*(Real.sin θ)^4/8 + 5*(Real.sin θ)^6/32 - (Real.sin θ)^8/32))
      = 2277 * Real.pi / 8192 := by
  have h0 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume (0:ℝ) (Real.pi/2) :=
    continuous_const.intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun θ : ℝ => (Real.sin θ)^2/2) volume (0:ℝ) (Real.pi/2) :=
    (show Continuous (fun θ : ℝ => (Real.sin θ)^2/2) by continuity).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ : ℝ => 5*(Real.sin θ)^4/8) volume (0:ℝ) (Real.pi/2) :=
    (show Continuous (fun θ : ℝ => 5*(Real.sin θ)^4/8) by continuity).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun θ : ℝ => 5*(Real.sin θ)^6/32) volume (0:ℝ) (Real.pi/2) :=
    (show Continuous (fun θ : ℝ => 5*(Real.sin θ)^6/32) by continuity).intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun θ : ℝ => (Real.sin θ)^8/32) volume (0:ℝ) (Real.pi/2) :=
    (show Continuous (fun θ : ℝ => (Real.sin θ)^8/32) by continuity).intervalIntegrable _ _
  have hA : IntervalIntegrable
      (fun x : ℝ => ((((1:ℝ) - x.sin^2/2) - 5*x.sin^4/8) + 5*x.sin^6/32))
      volume (0:ℝ) (Real.pi/2) := ((h0.sub h1).sub h2).add h3
  have hB : IntervalIntegrable (fun x : ℝ => (((1:ℝ) - x.sin^2/2) - 5*x.sin^4/8))
      volume (0:ℝ) (Real.pi/2) := (h0.sub h1).sub h2
  have hC : IntervalIntegrable (fun x : ℝ => ((1:ℝ) - x.sin^2/2)) volume (0:ℝ) (Real.pi/2) :=
    h0.sub h1
  rw [intervalIntegral.integral_sub hA h4, intervalIntegral.integral_add hB h3,
      intervalIntegral.integral_sub hC h2, intervalIntegral.integral_sub h0 h1]
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
  rw [J0c, J2, J4, J6, J8]
  ring

theorem integral_sqrt_one_sub_pow_four_ge :
    (87215 : ℝ) / 100000 ≤ ∫ u in (0)..1, Real.sqrt (1 - u ^ 4) := by
  have hg_cont : Continuous (fun u : ℝ => Real.sqrt (1 - u^2) * (1 + u^2/2 - u^4/8 + u^6/32)) := by
    continuity
  have hu_cont : Continuous (fun u : ℝ => Real.sqrt (1 - u^4)) := by continuity
  have hint_g : IntervalIntegrable
      (fun u : ℝ => Real.sqrt (1 - u^2) * (1 + u^2/2 - u^4/8 + u^6/32)) volume (0:ℝ) 1 :=
    hg_cont.intervalIntegrable (0:ℝ) 1
  have hint_u : IntervalIntegrable (fun u : ℝ => Real.sqrt (1 - u^4)) volume (0:ℝ) 1 :=
    hu_cont.intervalIntegrable (0:ℝ) 1
  have hmono : (∫ u in (0:ℝ)..1, Real.sqrt (1 - u^2) * (1 + u^2/2 - u^4/8 + u^6/32))
      ≤ ∫ u in (0:ℝ)..1, Real.sqrt (1 - u^4) :=
    intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hint_g hint_u
      (fun x hx => sqrt_one_sub_pow_four_ge_pointwise x hx.1 hx.2)
  have hval : (∫ u in (0:ℝ)..1, Real.sqrt (1 - u^2) * (1 + u^2/2 - u^4/8 + u^6/32))
      = 2277 * Real.pi / 8192 := by
    have hsub := integral_comp_mul_deriv (a := (0:ℝ)) (b := Real.pi/2)
      (f := Real.sin) (f' := Real.cos)
      (g := fun u => Real.sqrt (1 - u^2) * (1 + u^2/2 - u^4/8 + u^6/32))
      (fun x _ => Real.hasDerivAt_sin x) Real.continuousOn_cos (by fun_prop)
    rw [Real.sin_zero, Real.sin_pi_div_two] at hsub
    simp only [Function.comp_apply] at hsub
    rw [← hsub]
    have hcongr : (∫ x in (0:ℝ)..(Real.pi/2),
          Real.sqrt (1 - (Real.sin x)^2) *
            (1 + (Real.sin x)^2/2 - (Real.sin x)^4/8 + (Real.sin x)^6/32) * Real.cos x)
        = ∫ x in (0:ℝ)..(Real.pi/2),
            (1 - (Real.sin x)^2/2 - 5*(Real.sin x)^4/8 + 5*(Real.sin x)^6/32 - (Real.sin x)^8/32) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi/2)] at hx
      show Real.sqrt (1 - (Real.sin x)^2) *
            (1 + (Real.sin x)^2/2 - (Real.sin x)^4/8 + (Real.sin x)^6/32) * Real.cos x
          = 1 - (Real.sin x)^2/2 - 5*(Real.sin x)^4/8 + 5*(Real.sin x)^6/32 - (Real.sin x)^8/32
      have hcnn : 0 ≤ Real.cos x :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
      have hcos : Real.cos x = Real.sqrt (1 - (Real.sin x)^2) := by
        rw [← Real.abs_cos_eq_sqrt_one_sub_sin_sq]
        exact (abs_of_nonneg hcnn).symm
      rw [← hcos]
      have hkey : Real.cos x * (1 + Real.sin x^2/2 - Real.sin x^4/8 + Real.sin x^6/32) * Real.cos x
          = (1 - Real.sin x^2) * (1 + Real.sin x^2/2 - Real.sin x^4/8 + Real.sin x^6/32) := by
        rw [← Real.cos_sq' x]; ring
      rw [hkey]
      ring
    rw [hcongr, integral_theta_main]
  have hnum : (87215 : ℝ) / 100000 ≤ 2277 * Real.pi / 8192 := by
    nlinarith [Real.pi_gt_d6]
  calc (87215 : ℝ) / 100000 ≤ 2277 * Real.pi / 8192 := hnum
    _ = ∫ u in (0:ℝ)..1, Real.sqrt (1 - u^2) * (1 + u^2/2 - u^4/8 + u^6/32) := hval.symm
    _ ≤ ∫ u in (0:ℝ)..1, Real.sqrt (1 - u^4) := hmono

end Commons.Analysis.Integral

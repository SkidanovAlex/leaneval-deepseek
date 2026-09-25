import Mathlib
import Submission.Commons.Analysis.Laplace.laplace_kernel_power_gt_one
import Submission.Commons.Analysis.Complex.vertical_contour_shift
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
open MeasureTheory Set Complex Filter
open scoped Topology Interval BigOperators
noncomputable section
namespace PsiKernelBound

def K2 (a c : ℝ) : ℂ :=
  ∫ t : ℝ, Complex.exp ((c : ℂ) * ((a : ℂ) + (t : ℂ) * Complex.I)) *
    ((((a : ℂ) + (t : ℂ) * Complex.I))^2)⁻¹

def gK (a lam u : ℝ) : ℂ :=
  (Complex.exp (-(((a:ℂ)+(u:ℂ)*Complex.I)*(lam:ℂ))) - 1) * ((((a:ℂ)+(u:ℂ)*Complex.I))^2)⁻¹

def ghat (a lam r : ℝ) : ℂ := ∫ u : ℝ, gK a lam u * Complex.exp ((r:ℂ)*((u:ℂ)*Complex.I))





lemma norm_K2_line (s c t : ℝ) :
    ‖Complex.exp ((c:ℂ)*((s:ℂ)+(t:ℂ)*Complex.I)) * ((((s:ℂ)+(t:ℂ)*Complex.I))^2)⁻¹‖
      = Real.exp (c*s) * (s^2+t^2)⁻¹ := by
  rw [norm_mul, Complex.norm_exp, norm_inv, norm_pow]
  have hre : ((c:ℂ)*((s:ℂ)+(t:ℂ)*Complex.I)).re = c*s := by
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
  rw [hre]
  have hns : ‖((s:ℂ)+(t:ℂ)*Complex.I)‖^2 = s^2+t^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [hns]

lemma cpow_neg_two (w : ℂ) (hw : w ≠ 0) : w ^ (-((2:ℝ):ℂ)) = (w^2)⁻¹ := by
  rw [show (-((2:ℝ):ℂ)) = ((-2:ℤ):ℂ) by norm_num, Complex.cpow_intCast, zpow_neg, zpow_two]
  rw [sq]

theorem K2_pos (a c : ℝ) (ha : 0 < a) (hc : 0 < c) : K2 a c = 2 * Real.pi * c := by
  have h := Commons.Analysis.Laplace.laplace_kernel_power_gt_one a c 2 ha hc (by norm_num : (1:ℝ) < 2)
  have h2 : ((c ^ ((2:ℝ) - 1) / Real.Gamma (2:ℝ) : ℝ) : ℂ) = (c : ℂ) := by
    rw [show (2:ℝ)-1 = 1 by norm_num, Real.rpow_one, Real.Gamma_two]; norm_num
  have harg : (∫ t : ℝ, Complex.exp (((a : ℂ) + (t : ℂ) * Complex.I) * (c : ℂ)) * (((a : ℂ) + (t : ℂ) * Complex.I) ^ (-((2:ℝ):ℂ)))) = K2 a c := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    have hne : (a:ℂ)+(t:ℂ)*Complex.I ≠ 0 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith
    rw [cpow_neg_two _ hne]
    rw [mul_comm ((a:ℂ)+(t:ℂ)*Complex.I) (c:ℂ)]
  have hh : 1 / (2 * (Real.pi : ℂ)) * K2 a c = (c : ℂ) := by
    rw [← harg]; exact h.trans h2
  rw [div_eq_mul_inv] at hh
  have h' : K2 a c = (c:ℂ) * ((2:ℂ) * (Real.pi:ℂ)) := by
    rw [← hh]; field_simp
  rw [h']
  ring

lemma integrable_K2 (s c : ℝ) (hs : 0 < s) (hc : c ≤ 0) :
    Integrable (fun t : ℝ => Complex.exp ((c:ℂ)*((s:ℂ)+(t:ℂ)*Complex.I)) * ((((s:ℂ)+(t:ℂ)*Complex.I))^2)⁻¹) := by
  have hbase : Integrable (fun t : ℝ => (1+t^2)⁻¹) := integrable_inv_one_add_sq
  refine Integrable.mono' (hbase.const_mul ((1:ℝ) + 1/s^2)) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact Complex.continuous_exp.comp (by fun_prop)
    · apply Continuous.inv₀ (by fun_prop)
      intro t
      intro h
      have h0 : (s:ℂ)+(t:ℂ)*Complex.I = 0 := by
        have hm : ((s:ℂ)+(t:ℂ)*Complex.I)*((s:ℂ)+(t:ℂ)*Complex.I) = 0 := by rwa [sq] at h
        exact mul_self_eq_zero.mp hm
      have := congrArg Complex.re h0
      simp at this; linarith
  · filter_upwards with t
    rw [norm_K2_line]
    have hexp : Real.exp (c*s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    calc Real.exp (c*s) * (s^2+t^2)⁻¹ ≤ 1 * (s^2+t^2)⁻¹ :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
      _ ≤ (1+1/s^2) * (1+t^2)⁻¹ := by
          rw [one_mul]
          have hkey : (1+t^2)/(1+1/s^2) ≤ s^2+t^2 := by
            rw [div_le_iff₀ (by positivity)]
            have hs2 : s^2 ≠ 0 := by positivity
            field_simp
            nlinarith [sq_nonneg s, sq_nonneg t, sq_nonneg (s^2)]
          calc (s^2+t^2)⁻¹ ≤ ((1+t^2)/(1+1/s^2))⁻¹ := inv_anti₀ (by positivity) hkey
            _ = (1+1/s^2)*(1+t^2)⁻¹ := by rw [inv_div, div_eq_mul_inv]

theorem K2_nonpos (a c : ℝ) (ha : 0 < a) (hc : c ≤ 0) : K2 a c = 0 := by
  set F : ℂ → ℂ := fun w => Complex.exp ((c:ℂ)*w) * (w^2)⁻¹
  have hFval : ∀ Q : ℝ, (∫ t : ℝ, F ((Q:ℂ)+(t:ℂ)*Complex.I)) = K2 Q c := by
    intro Q; rfl
  have hFcont : ∀ R : ℝ, 0 < R → Continuous (fun x : ℝ => F ((x:ℂ)+(R:ℂ)*Complex.I)) := by
    intro R hR
    apply Continuous.mul
    · exact Complex.continuous_exp.comp (by fun_prop)
    · apply Continuous.inv₀ (by fun_prop)
      intro x
      intro h
      have h0 : (x:ℂ)+(R:ℂ)*Complex.I = 0 := by
        have hm : ((x:ℂ)+(R:ℂ)*Complex.I)*((x:ℂ)+(R:ℂ)*Complex.I) = 0 := by rwa [sq] at h
        exact mul_self_eq_zero.mp hm
      have := congrArg Complex.im h0
      simp at this; linarith
  have hquad : ∀ Q : ℝ, 0 < Q → (∫ t : ℝ, (Q^2+t^2)⁻¹) = Real.pi * Q⁻¹ := by
    intro Q hQ
    have hsub : (∫ t : ℝ, (1+(t/Q)^2)⁻¹) = Q * Real.pi := by
      have h := MeasureTheory.Measure.integral_comp_div (fun u : ℝ => (1+u^2)⁻¹) Q
      rw [integral_univ_inv_one_add_sq, smul_eq_mul, abs_of_pos hQ] at h
      exact h
    have hstep : (∫ t : ℝ, (Q^2+t^2)⁻¹) = (Q^2)⁻¹ * ∫ t : ℝ, (1+(t/Q)^2)⁻¹ := by
      rw [← integral_const_mul]
      apply integral_congr_ae; filter_upwards with t
      have : (0:ℝ) < Q := hQ
      field_simp
    rw [hstep, hsub]
    field_simp
  have hshift : ∀ Q : ℝ, a ≤ Q → (∫ t : ℝ, F ((Q:ℂ)+(t:ℂ)*Complex.I)) = (∫ t : ℝ, F ((a:ℂ)+(t:ℂ)*Complex.I)) := by
    intro Q hQ
    have hQ0 : 0 < Q := lt_of_lt_of_le ha hQ
    apply Commons.Analysis.Complex.vertical_contour_shift F a Q hQ
    · intro R
      have hne : ∀ w ∈ uIcc a Q ×ℂ uIcc (-R) R, w^2 ≠ 0 := by
        intro w hw
        rw [Complex.mem_reProdIm, uIcc_of_le hQ] at hw
        have h1 : 0 < w.re := lt_of_lt_of_le ha hw.1.1
        intro h
        have hw0 : w = 0 := by
          have : w*w = 0 := by rwa [sq] at h
          exact mul_self_eq_zero.mp this
        rw [hw0] at h1; simp at h1
      refine DifferentiableOn.mul ?_ ?_
      · exact Complex.differentiable_exp.comp_differentiableOn (differentiableOn_id.const_mul _)
      · have h2 : DifferentiableOn ℂ (fun w : ℂ => w^2) (uIcc a Q ×ℂ uIcc (-R) R) := by
          fun_prop
        exact h2.inv hne
    · exact integrable_K2 a c ha hc
    · exact integrable_K2 Q c hQ0 hc
    · have hbd : ∀ R : ℝ, 0 < R → ‖∫ x in a..Q, F ((x:ℂ)+(R:ℂ)*Complex.I)‖ ≤ (Q-a)*((R^2)⁻¹) := by
        intro R hR
        calc ‖∫ x in a..Q, F ((x:ℂ)+(R:ℂ)*Complex.I)‖
            ≤ ∫ x in a..Q, ‖F ((x:ℂ)+(R:ℂ)*Complex.I)‖ :=
              intervalIntegral.norm_integral_le_integral_norm hQ
          _ ≤ ∫ x in a..Q, (R^2)⁻¹ := by
              refine intervalIntegral.integral_mono_on hQ
                ((hFcont R hR).norm.continuousOn.intervalIntegrable)
                intervalIntegrable_const ?_
              intro x hx
              rw [norm_K2_line]
              have hexp : Real.exp (c*x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hx.1])
              calc Real.exp (c*x) * (x^2+R^2)⁻¹ ≤ 1 * (x^2+R^2)⁻¹ :=
                    mul_le_mul_of_nonneg_right hexp (by positivity)
                _ ≤ (R^2)⁻¹ := by
                    rw [one_mul]
                    apply inv_anti₀ (by positivity)
                    nlinarith [sq_nonneg x]
          _ = (Q-a)*((R^2)⁻¹) := by rw [intervalIntegral.integral_const, smul_eq_mul]
      refine squeeze_zero_norm' (a := fun R : ℝ => (Q-a)*(R^2)⁻¹) ?_ ?_
      · filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
        exact hbd R hR
      · have h2 : Tendsto (fun R : ℝ => (R^2)⁻¹) atTop (nhds 0) := by
          have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 2
          simpa [inv_pow] using h
        have h3 := h2.const_mul (Q-a)
        simpa [mul_comm, mul_left_comm, mul_assoc] using h3
    · have hbd : ∀ R : ℝ, 0 < R → ‖∫ x in a..Q, F ((x:ℂ)-(R:ℂ)*Complex.I)‖ ≤ (Q-a)*((R^2)⁻¹) := by
        intro R hR
        have hcR : Continuous (fun x : ℝ => F ((x:ℂ)-(R:ℂ)*Complex.I)) := by
          apply Continuous.mul
          · exact Complex.continuous_exp.comp (by fun_prop)
          · apply Continuous.inv₀ (by fun_prop)
            intro x
            intro h
            have h0 : (x:ℂ)-(R:ℂ)*Complex.I = 0 := by
              have hm : ((x:ℂ)-(R:ℂ)*Complex.I)*((x:ℂ)-(R:ℂ)*Complex.I) = 0 := by rwa [sq] at h
              exact mul_self_eq_zero.mp hm
            have := congrArg Complex.im h0
            simp at this; linarith
        calc ‖∫ x in a..Q, F ((x:ℂ)-(R:ℂ)*Complex.I)‖
            ≤ ∫ x in a..Q, ‖F ((x:ℂ)-(R:ℂ)*Complex.I)‖ :=
              intervalIntegral.norm_integral_le_integral_norm hQ
          _ ≤ ∫ x in a..Q, (R^2)⁻¹ := by
              refine intervalIntegral.integral_mono_on hQ
                (hcR.norm.continuousOn.intervalIntegrable)
                intervalIntegrable_const ?_
              intro x hx
              rw [show (x:ℂ)-(R:ℂ)*Complex.I = (x:ℂ)+((-R:ℝ):ℂ)*Complex.I from by push_cast; ring]
              rw [norm_K2_line]
              have hexp : Real.exp (c*x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hx.1])
              calc Real.exp (c*x) * (x^2+(-R)^2)⁻¹ ≤ 1 * (x^2+(-R)^2)⁻¹ :=
                    mul_le_mul_of_nonneg_right hexp (by positivity)
                _ ≤ (R^2)⁻¹ := by
                    rw [one_mul]
                    apply inv_anti₀ (by positivity)
                    nlinarith [sq_nonneg x]
          _ = (Q-a)*((R^2)⁻¹) := by rw [intervalIntegral.integral_const, smul_eq_mul]
      refine squeeze_zero_norm' (a := fun R : ℝ => (Q-a)*(R^2)⁻¹) ?_ ?_
      · filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
        exact hbd R hR
      · have h2 : Tendsto (fun R : ℝ => (R^2)⁻¹) atTop (nhds 0) := by
          have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 2
          simpa [inv_pow] using h
        have h3 := h2.const_mul (Q-a)
        simpa [mul_comm, mul_left_comm, mul_assoc] using h3
  have hev : (fun Q : ℝ => (∫ t : ℝ, F ((Q:ℂ)+(t:ℂ)*Complex.I))) =ᶠ[atTop] (fun _ => (∫ t : ℝ, F ((a:ℂ)+(t:ℂ)*Complex.I))) :=
    (Filter.eventually_atTop).2 ⟨a, fun Q hQ => hshift Q hQ⟩
  have hbound : ∀ Q : ℝ, 0 < Q → ‖∫ t : ℝ, F ((Q:ℂ)+(t:ℂ)*Complex.I)‖ ≤ Real.pi * Q⁻¹ := by
    intro Q hQ
    calc ‖∫ t : ℝ, F ((Q:ℂ)+(t:ℂ)*Complex.I)‖ ≤ ∫ t : ℝ, ‖F ((Q:ℂ)+(t:ℂ)*Complex.I)‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ t : ℝ, Real.exp (c*Q) * (Q^2+t^2)⁻¹ := by
          apply integral_congr_ae; filter_upwards with t; rw [norm_K2_line]
      _ = Real.exp (c*Q) * (∫ t : ℝ, (Q^2+t^2)⁻¹) := integral_const_mul _ _
      _ = Real.exp (c*Q) * (Real.pi * Q⁻¹) := by rw [hquad Q hQ]
      _ ≤ 1 * (Real.pi * Q⁻¹) := mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (by nlinarith)) (by positivity)
      _ = Real.pi * Q⁻¹ := one_mul _
  have hlim : Tendsto (fun Q : ℝ => (∫ t : ℝ, F ((Q:ℂ)+(t:ℂ)*Complex.I))) atTop (nhds 0) := by
    refine squeeze_zero_norm' (a := fun Q : ℝ => Real.pi * Q⁻¹) ?_ ?_
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with Q hQ
      exact hbound Q hQ
    · have h2 : Tendsto (fun Q : ℝ => Real.pi * Q⁻¹) atTop (nhds (Real.pi * 0)) :=
        tendsto_const_nhds.mul tendsto_inv_atTop_zero
      simpa using h2
  have hconst : Tendsto (fun Q : ℝ => (∫ t : ℝ, F ((Q:ℂ)+(t:ℂ)*Complex.I))) atTop (nhds (∫ t : ℝ, F ((a:ℂ)+(t:ℂ)*Complex.I))) :=
    tendsto_const_nhds.congr' hev.symm
  have hone : (∫ t : ℝ, F ((a:ℂ)+(t:ℂ)*Complex.I)) = 0 := tendsto_nhds_unique hconst hlim
  rw [← hFval a]; exact hone




lemma integrable_exp_mul_K2 (a c : ℝ) (ha : 0 < a) :
    Integrable (fun u : ℝ => Complex.exp ((c:ℂ)*((u:ℂ)*Complex.I)) * ((((a:ℂ)+(u:ℂ)*Complex.I))^2)⁻¹) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (1+1/a^2)) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact Complex.continuous_exp.comp (by fun_prop)
    · apply Continuous.inv₀ (by fun_prop)
      intro u; intro h
      have h0 : (a:ℂ)+(u:ℂ)*Complex.I = 0 := by
        have hm : ((a:ℂ)+(u:ℂ)*Complex.I)*((a:ℂ)+(u:ℂ)*Complex.I) = 0 := by rwa [sq] at h
        exact mul_self_eq_zero.mp hm
      have := congrArg Complex.re h0; simp at this; linarith
  · filter_upwards with u
    rw [Complex.norm_mul, Complex.norm_exp, norm_inv, norm_pow]
    have hre : ((c:ℂ)*((u:ℂ)*Complex.I)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero, one_mul]
    have hns : ‖((a:ℂ)+(u:ℂ)*Complex.I)‖^2 = a^2+u^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    rw [hns]
    have hkey : (1+u^2)/(1+1/a^2) ≤ a^2+u^2 := by
      rw [div_le_iff₀ (by positivity)]
      have ha2 : a^2 ≠ 0 := by positivity
      field_simp
      nlinarith [sq_nonneg a, sq_nonneg u]
    calc (a^2+u^2)⁻¹ ≤ ((1+u^2)/(1+1/a^2))⁻¹ := inv_anti₀ (by positivity) hkey
      _ = (1+1/a^2)*(1+u^2)⁻¹ := by rw [inv_div, div_eq_mul_inv]

lemma integral_exp_mul_K2 (a c : ℝ) :
    (∫ u : ℝ, Complex.exp ((c:ℂ)*((u:ℂ)*Complex.I)) * ((((a:ℂ)+(u:ℂ)*Complex.I))^2)⁻¹)
      = Complex.exp (-((c:ℂ)*a)) * K2 a c := by
  have h1 : K2 a c = Complex.exp ((c:ℂ)*a) * (∫ u : ℝ, Complex.exp ((c:ℂ)*((u:ℂ)*Complex.I)) * ((((a:ℂ)+(u:ℂ)*Complex.I))^2)⁻¹) := by
    rw [K2, ← integral_const_mul]
    apply integral_congr_ae; filter_upwards with u
    rw [show (c:ℂ)*((a:ℂ)+(u:ℂ)*Complex.I) = (c:ℂ)*a + (c:ℂ)*((u:ℂ)*Complex.I) by ring, Complex.exp_add]
    ring
  rw [h1, ← mul_assoc, mul_comm (Complex.exp (-((c:ℂ)*a))) (Complex.exp ((c:ℂ)*a)), ← Complex.exp_add]
  simp

lemma key_pointwise (a lam r : ℝ) (u : ℝ) :
    Complex.exp (-(((a:ℂ)+(u:ℂ)*Complex.I)*(lam:ℂ))) * Complex.exp ((r:ℂ)*((u:ℂ)*Complex.I))
      = Complex.exp (-((lam:ℂ)*a)) * Complex.exp ((((r-lam:ℝ):ℂ))*((u:ℂ)*Complex.I)) := by
  rw [← Complex.exp_add]
  rw [show -(((a:ℂ)+(u:ℂ)*Complex.I)*(lam:ℂ)) + (r:ℂ)*((u:ℂ)*Complex.I)
      = -((lam:ℂ)*a) + (((r-lam:ℝ):ℂ))*((u:ℂ)*Complex.I) by
    push_cast; ring, Complex.exp_add]

lemma ghat_eq (a lam r : ℝ) (ha : 0 < a) :
    (∫ u : ℝ, (Complex.exp (-(((a:ℂ)+(u:ℂ)*Complex.I)*(lam:ℂ))) - 1) * ((((a:ℂ)+(u:ℂ)*Complex.I))^2)⁻¹ * Complex.exp ((r:ℂ)*((u:ℂ)*Complex.I)))
      = Complex.exp (-(r*a)) * (K2 a (r-lam) - K2 a r) := by
  have hAint : Integrable (fun u : ℝ => Complex.exp (-(((a:ℂ)+(u:ℂ)*Complex.I)*(lam:ℂ))) * Complex.exp ((r:ℂ)*((u:ℂ)*Complex.I)) * ((((a:ℂ)+(u:ℂ)*Complex.I))^2)⁻¹) := by
    refine (integrable_exp_mul_K2 a (r-lam) ha).const_mul (Complex.exp (-((lam:ℂ)*a))) |>.congr ?_
    filter_upwards with u
    rw [key_pointwise]; ring
  have h1 : (∫ u : ℝ, Complex.exp (-(((a:ℂ)+(u:ℂ)*Complex.I)*(lam:ℂ))) * Complex.exp ((r:ℂ)*((u:ℂ)*Complex.I)) * ((((a:ℂ)+(u:ℂ)*Complex.I))^2)⁻¹)
      = Complex.exp (-(r*a)) * K2 a (r-lam) := by
    have hB : (∫ u : ℝ, Complex.exp ((((r-lam:ℝ):ℂ))*((u:ℂ)*Complex.I)) * ((((a:ℂ)+(u:ℂ)*Complex.I))^2)⁻¹)
        = Complex.exp (-(((r-lam:ℝ):ℂ)*a)) * K2 a (r-lam) := integral_exp_mul_K2 a (r-lam)
    have hA : (∫ u : ℝ, Complex.exp (-(((a:ℂ)+(u:ℂ)*Complex.I)*(lam:ℂ))) * Complex.exp ((r:ℂ)*((u:ℂ)*Complex.I)) * ((((a:ℂ)+(u:ℂ)*Complex.I))^2)⁻¹)
        = Complex.exp (-((lam:ℂ)*a)) * (∫ u : ℝ, Complex.exp ((((r-lam:ℝ):ℂ))*((u:ℂ)*Complex.I)) * ((((a:ℂ)+(u:ℂ)*Complex.I))^2)⁻¹) := by
      rw [← integral_const_mul]
      apply integral_congr_ae; filter_upwards with u
      rw [key_pointwise]; ring
    rw [hA, hB, ← mul_assoc, ← Complex.exp_add]
    rw [show -((lam:ℂ)*a) + -(((r-lam:ℝ):ℂ)*a) = -((r:ℂ)*a) by push_cast; ring]
  have h2 : (∫ u : ℝ, Complex.exp ((r:ℂ)*((u:ℂ)*Complex.I)) * ((((a:ℂ)+(u:ℂ)*Complex.I))^2)⁻¹)
      = Complex.exp (-(r*a)) * K2 a r := integral_exp_mul_K2 a r
  have hid : (∫ u : ℝ, (Complex.exp (-(((a:ℂ)+(u:ℂ)*Complex.I)*(lam:ℂ))) - 1) * ((((a:ℂ)+(u:ℂ)*Complex.I))^2)⁻¹ * Complex.exp ((r:ℂ)*((u:ℂ)*Complex.I)))
      = (∫ u : ℝ, Complex.exp (-(((a:ℂ)+(u:ℂ)*Complex.I)*(lam:ℂ))) * Complex.exp ((r:ℂ)*((u:ℂ)*Complex.I)) * ((((a:ℂ)+(u:ℂ)*Complex.I))^2)⁻¹)
        - (∫ u : ℝ, Complex.exp ((r:ℂ)*((u:ℂ)*Complex.I)) * ((((a:ℂ)+(u:ℂ)*Complex.I))^2)⁻¹) := by
    rw [← integral_sub]
    · apply integral_congr_ae; filter_upwards with u; ring
    · exact hAint
    · exact integrable_exp_mul_K2 a r ha
  rw [hid, h1, h2]
  ring



lemma integrable_gK (a lam : ℝ) (ha : 0 < a) :
    Integrable (fun u : ℝ => gK a lam u) (volume : Measure ℝ) := by
  have hbase : Integrable (fun u : ℝ => (1+u^2)⁻¹) := integrable_inv_one_add_sq
  refine Integrable.mono' (hbase.const_mul ((Real.exp (-lam*a)+1)*(1+1/a^2))) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (Complex.continuous_exp.comp (by fun_prop)).sub continuous_const
    · apply Continuous.inv₀ (by fun_prop)
      intro u h
      have h0 : (a:ℂ)+(u:ℂ)*Complex.I = 0 := by
        have hm : ((a:ℂ)+(u:ℂ)*Complex.I)*((a:ℂ)+(u:ℂ)*Complex.I) = 0 := by rwa [sq] at h
        exact mul_self_eq_zero.mp hm
      have := congrArg Complex.re h0; simp at this; linarith
  · filter_upwards with u
    unfold gK
    rw [norm_mul]
    have h2 : ‖(((a:ℂ)+(u:ℂ)*Complex.I)^2)⁻¹‖ = (a^2+u^2)⁻¹ := by
      rw [norm_inv, norm_pow, Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero]
      ring_nf
    rw [h2]
    have h1 : ‖Complex.exp (-(((a:ℂ) + (u:ℂ) * Complex.I) * (lam:ℂ))) - 1‖ ≤ Real.exp (-lam*a) + 1 := by
      calc ‖Complex.exp (-(((a:ℂ) + (u:ℂ) * Complex.I) * (lam:ℂ))) - 1‖
          ≤ ‖Complex.exp (-(((a:ℂ) + (u:ℂ) * Complex.I) * (lam:ℂ)))‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = Real.exp (-lam*a) + 1 := by
            rw [Complex.norm_exp, norm_one]
            congr 1
            simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
              Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero]
            ring
    have h3 : (a^2+u^2)⁻¹ ≤ (1+1/a^2)*(1+u^2)⁻¹ := by
      have hkey : (1+u^2)/(1+1/a^2) ≤ a^2+u^2 := by
        rw [div_le_iff₀ (by positivity)]
        have ha2 : a^2 ≠ 0 := by positivity
        field_simp
        nlinarith [sq_nonneg a, sq_nonneg u]
      calc (a^2+u^2)⁻¹ ≤ ((1+u^2)/(1+1/a^2))⁻¹ := inv_anti₀ (by positivity) hkey
        _ = (1+1/a^2)*(1+u^2)⁻¹ := by rw [inv_div, div_eq_mul_inv]
    calc ‖Complex.exp (-(((a:ℂ) + (u:ℂ) * Complex.I) * (lam:ℂ))) - 1‖ * (a^2+u^2)⁻¹
        ≤ (Real.exp (-lam*a)+1) * (a^2+u^2)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (Real.exp (-lam*a)+1) * ((1+1/a^2)*(1+u^2)⁻¹) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = ((Real.exp (-lam*a)+1)*(1+1/a^2)) * (1+u^2)⁻¹ := by ring

lemma integrable_gK_norm (a lam : ℝ) (ha : 0 < a) :
    Integrable (fun u : ℝ => ‖gK a lam u‖) (volume : Measure ℝ) :=
  (integrable_gK a lam ha).norm

lemma ghat_eq' (a lam r : ℝ) (ha : 0 < a) :
    ghat a lam r = Complex.exp (-(r*a)) * (K2 a (r-lam) - K2 a r) := ghat_eq a lam r ha

lemma integrable_exp_restrict (P : ℂ) (hP : 0 < P.re) :
    IntegrableOn (fun r : ℝ => Real.exp (-P.re * r)) (Ioi (0:ℝ)) volume := by
  have h := integrableOn_exp_mul_Ioi (a := -P.re) (by linarith) (c := 0)
  simpa only [neg_mul] using h

lemma integrable_fubini (a lam : ℝ) (ha : 0 < a) (P : ℂ) (hP : 0 < P.re) :
    Integrable (fun p : ℝ × ℝ => gK a lam p.1 * (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P - (p.1:ℂ)*Complex.I)*(r:ℂ)))) p.2)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  have hprod : Integrable (fun z : ℝ × ℝ => ‖gK a lam z.1‖ * (Ioi (0:ℝ)).indicator (fun r : ℝ => Real.exp (-P.re * r)) z.2)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    MeasureTheory.Integrable.mul_prod
      (f := fun u : ℝ => ‖gK a lam u‖)
      (g := fun r : ℝ => (Ioi (0:ℝ)).indicator (fun r : ℝ => Real.exp (-P.re * r)) r)
      (integrable_gK_norm a lam ha) ((integrable_indicator_iff measurableSet_Ioi).mpr (integrable_exp_restrict P hP))
  refine hprod.mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · have hcont : Continuous (fun u : ℝ => gK a lam u) := by
        unfold gK
        apply Continuous.mul
        · exact (Complex.continuous_exp.comp (by fun_prop)).sub continuous_const
        · apply Continuous.inv₀ (by fun_prop)
          intro u h
          have h0 : (a:ℂ)+(u:ℂ)*Complex.I = 0 := by
            have hm : ((a:ℂ)+(u:ℂ)*Complex.I)*((a:ℂ)+(u:ℂ)*Complex.I) = 0 := by rwa [sq] at h
            exact mul_self_eq_zero.mp hm
          have := congrArg Complex.re h0; simp at this; linarith
      exact hcont.measurable.comp measurable_fst
    · exact Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
        (Complex.continuous_exp.measurable.comp (by fun_prop)) measurable_const
  · filter_upwards with p
    rw [norm_mul]
    have h2 : ‖(Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P - (p.1:ℂ)*Complex.I)*(r:ℂ)))) p.2‖
        ≤ (Ioi (0:ℝ)).indicator (fun r : ℝ => Real.exp (-P.re * r)) p.2 := by
      by_cases hp : p.2 ∈ Ioi (0:ℝ)
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Complex.norm_exp]
        apply le_of_eq
        congr 1
        simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, neg_zero]
        ring
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, norm_zero]
    exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)


lemma integral_indicator_Ioi (F : ℝ → ℂ) :
    (∫ r : ℝ, (Ioi (0:ℝ)).indicator F r) = ∫ r : ℝ in Ioi (0:ℝ), F r :=
  MeasureTheory.integral_indicator measurableSet_Ioi

lemma J_fubini (a lam : ℝ) (ha : 0 < a) (P : ℂ) (hP : 0 < P.re) :
    (∫ u : ℝ, gK a lam u / (P - (u:ℂ)*Complex.I))
      = ∫ r in Ioi (0:ℝ), Complex.exp (-(P*(r:ℂ))) * ghat a lam r := by
  have hf := integrable_fubini a lam ha P hP
  have hswap := integral_integral_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (f := fun u r => gK a lam u * (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P - (u:ℂ)*Complex.I)*(r:ℂ)))) r) hf
  have hleft : (∫ u : ℝ, gK a lam u / (P - (u:ℂ)*Complex.I))
      = ∫ u : ℝ, ∫ r : ℝ, gK a lam u * (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P - (u:ℂ)*Complex.I)*(r:ℂ)))) r ∂volume ∂volume := by
    apply integral_congr_ae; filter_upwards with u
    have hint : (∫ r : ℝ, (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P - (u:ℂ)*Complex.I)*(r:ℂ)))) r)
        = ∫ r : ℝ in Ioi (0:ℝ), Complex.exp (-((P - (u:ℂ)*Complex.I)*(r:ℂ))) := integral_indicator_Ioi _
    have hP' : (-(P - (u:ℂ)*Complex.I)).re < 0 := by
      simp only [Complex.neg_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, Complex.neg_im, Complex.sub_im, neg_zero]
      linarith
    have h := integral_exp_mul_complex_Ioi (a := -(P - (u:ℂ)*Complex.I)) hP' 0
    have hexp : (∫ r : ℝ in Ioi (0:ℝ), Complex.exp (-((P - (u:ℂ)*Complex.I)*(r:ℂ))))
        = (P - (u:ℂ)*Complex.I)⁻¹ := by
      rw [show (∫ r : ℝ in Ioi (0:ℝ), Complex.exp (-((P - (u:ℂ)*Complex.I)*(r:ℂ))))
          = ∫ r : ℝ in Ioi (0:ℝ), Complex.exp ((-(P - (u:ℂ)*Complex.I))*(r:ℂ)) from by
          apply integral_congr_ae; filter_upwards with r; congr 1; ring]
      rw [h, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      rw [show (-1 / -(P - (u:ℂ) * Complex.I)) = (P - (u:ℂ) * Complex.I)⁻¹ by field_simp]
    have hfac : (∫ r : ℝ, gK a lam u * (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P - (u:ℂ)*Complex.I)*(r:ℂ)))) r)
        = gK a lam u * (∫ r : ℝ, (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P - (u:ℂ)*Complex.I)*(r:ℂ)))) r) := by
      rw [← integral_const_mul]
    rw [hfac, hint, hexp, div_eq_mul_inv]
  have hright : (∫ r in Ioi (0:ℝ), Complex.exp (-(P*(r:ℂ))) * ghat a lam r)
      = ∫ r : ℝ, ∫ u : ℝ, gK a lam u * (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P - (u:ℂ)*Complex.I)*(r:ℂ)))) r ∂volume ∂volume := by
    rw [← integral_indicator_Ioi (fun r : ℝ => Complex.exp (-(P*(r:ℂ))) * ghat a lam r)]
    apply integral_congr_ae; filter_upwards with r
    by_cases hr : r ∈ Ioi (0:ℝ)
    · have hinner : (∫ u : ℝ, gK a lam u * (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P - (u:ℂ)*Complex.I)*(r:ℂ)))) r)
          = ∫ u : ℝ, gK a lam u * Complex.exp (-((P - (u:ℂ)*Complex.I)*(r:ℂ))) := by
        apply integral_congr_ae; filter_upwards with u; rw [Set.indicator_of_mem hr]
      have hswap2 : (∫ u : ℝ, gK a lam u * Complex.exp (-((P - (u:ℂ)*Complex.I)*(r:ℂ))))
          = Complex.exp (-(P*(r:ℂ))) * (∫ u : ℝ, gK a lam u * Complex.exp ((r:ℂ)*((u:ℂ)*Complex.I))) := by
        rw [← integral_const_mul]
        apply integral_congr_ae; filter_upwards with u
        rw [show Complex.exp (-((P - (u:ℂ)*Complex.I)*(r:ℂ))) = Complex.exp (-(P*(r:ℂ))) * Complex.exp ((r:ℂ)*((u:ℂ)*Complex.I)) from by
          rw [← Complex.exp_add]; congr 1; ring]
        ring
      have hghat : (∫ u : ℝ, gK a lam u * Complex.exp ((r:ℂ)*((u:ℂ)*Complex.I))) = ghat a lam r := rfl
      rw [Set.indicator_of_mem hr, hinner, hswap2, hghat]
    · have hzero : (∫ u : ℝ, gK a lam u * (Ioi (0:ℝ)).indicator (fun r : ℝ => Complex.exp (-((P - (u:ℂ)*Complex.I)*(r:ℂ)))) r) = 0 := by
        apply integral_eq_zero_of_ae; filter_upwards with u
        simp only [Set.indicator_of_notMem hr, mul_zero, Pi.zero_apply]
      rw [Set.indicator_of_notMem hr, hzero]
  rw [hleft, hright, hswap]

-- The values of K2 at positive / negative arguments
lemma hasDerivAt_antideriv (c : ℂ) (hc : c ≠ 0) (r : ℝ) :
    HasDerivAt (fun s : ℝ => -((1 + c*(s:ℂ))*Complex.exp (-(c*(s:ℂ)))/(c^2)))
      ((r:ℂ)*Complex.exp (-(c*(r:ℂ)))) r := by
  have hz : HasDerivAt (fun s : ℝ => (s:ℂ)) 1 r := (hasDerivAt_id r).ofReal_comp
  have h1 : HasDerivAt (fun s : ℝ => (1:ℂ) + c*(s:ℂ)) (c*1) r := (hz.const_mul c).const_add 1
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (-(c*(s:ℂ)))) (Complex.exp (-(c*(r:ℂ))) * (-(c*1))) r := (hz.const_mul c).neg.cexp
  have h2 := ((h1.mul hexp).div_const (c^2)).neg
  have hderiv : -((c * 1 * Complex.exp (-(c*(r:ℂ)))
        + (1 + c*(r:ℂ)) * (Complex.exp (-(c*(r:ℂ))) * -(c * 1))) / c^2)
      = (r:ℂ)*Complex.exp (-(c*(r:ℂ))) := by
    field_simp
    ring
  simp only [Pi.mul_apply, Pi.neg_apply] at h2
  rw [hderiv] at h2
  exact h2

lemma integral_Ioc_mul_exp (c : ℂ) (hc : c ≠ 0) (lam : ℝ) :
    (∫ r in (0:ℝ)..lam, (r:ℂ)*Complex.exp (-(c*(r:ℂ))))
      = -(1 + c*(lam:ℂ))*Complex.exp (-(c*(lam:ℂ)))/(c^2) + 1/c^2 := by
  have hint : IntervalIntegrable (fun r : ℝ => (r:ℂ)*Complex.exp (-(c*(r:ℂ)))) volume 0 lam := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hasDerivAt_antideriv c hc r) hint]
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one, one_mul, div_one, sub_zero]
  ring

lemma integral_Ioi_exp (c : ℂ) (hc : 0 < c.re) (lam : ℝ) :
    (∫ r in Ioi lam, Complex.exp (-(c*(r:ℂ)))) = Complex.exp (-(c*(lam:ℂ)))/c := by
  have h := integral_exp_mul_complex_Ioi (a := -c) (by simpa using hc) lam
  simp only [neg_mul] at h
  rw [h]
  rw [neg_div]
  ring



theorem J_eq (a lam x b j : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hxj : 0 < x + j) :
    (∫ u : ℝ, gK a lam u / ((x+j:ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I))
      = 4 * Real.pi * (Complex.exp (-((a + 2*(x+j) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / ((a:ℂ) + 2*(x+j) + (b:ℂ)*Complex.I)^2 := by
  set P : ℂ := 2*((x+j):ℂ) + (b:ℂ)*Complex.I with hPdef
  set c : ℂ := (a:ℂ) + P with hcdef
  have hPre_eq : P.re = 2*(x+j) := by
    rw [hPdef]
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hPre : 0 < P.re := by rw [hPre_eq]; linarith
  have hcre : 0 < c.re := by
    have h1 : c.re = a + P.re := by rw [hcdef]; simp
    rw [h1]; linarith [ha, hPre]
  have hcne : c ≠ 0 := by intro h; rw [h] at hcre; simp at hcre
  have hstep1 : (∫ u : ℝ, gK a lam u / ((x+j:ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I))
      = 2 * (∫ u : ℝ, gK a lam u / (P - (u:ℂ)*Complex.I)) := by
    rw [← integral_const_mul]; apply integral_congr_ae; filter_upwards with u
    have hz : P - (u:ℂ)*Complex.I = 2*((x+j:ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) := by
      rw [hPdef]; push_cast; ring
    rw [hz]
    have hne : 2*((x+j:ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [hxj]
    field_simp
  rw [hstep1, J_fubini a lam ha P hPre]
  have hpoint : ∀ r : ℝ, Complex.exp (-(P*(r:ℂ))) * ghat a lam r
      = Complex.exp (-(c*(r:ℂ))) * (K2 a (r-lam) - K2 a r) := by
    intro r
    rw [ghat_eq' a lam r ha]
    have heq : Complex.exp (-(P*(r:ℂ))) * (Complex.exp (-(r*a)) * (K2 a (r-lam) - K2 a r))
        = Complex.exp (-(c*(r:ℂ))) * (K2 a (r-lam) - K2 a r) := by
      rw [← mul_assoc, ← Complex.exp_add]
      congr 1
      rw [hcdef]; ring
    exact heq
  have hstep2 : (∫ r in Ioi (0:ℝ), Complex.exp (-(P*(r:ℂ))) * ghat a lam r)
      = ∫ r in Ioi (0:ℝ), Complex.exp (-(c*(r:ℂ))) * (K2 a (r-lam) - K2 a r) := by
    apply integral_congr_ae; filter_upwards with r; rw [hpoint]
  rw [hstep2]
  have hdisj : Disjoint (Ioc (0:ℝ) lam) (Ioi lam) := by
    rw [Set.disjoint_left]; intro r hr hr2
    rw [mem_Ioc] at hr; rw [mem_Ioi] at hr2; linarith
  have hunion : Ioc (0:ℝ) lam ∪ Ioi lam = Ioi (0:ℝ) := by
    ext r; simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨h1,h2⟩ | h2) <;> linarith
    · intro h
      rcases le_or_gt r lam with h2 | h2
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr h2
  have hvalIoc : ∀ r ∈ Ioc (0:ℝ) lam, (K2 a (r-lam) - K2 a r) = -(2*Real.pi*r) := by
    intro r hr
    rw [mem_Ioc] at hr
    rw [K2_nonpos a (r-lam) ha (by linarith), K2_pos a r ha hr.1]
    push_cast; ring
  have hvalIoi : ∀ r ∈ Ioi lam, (K2 a (r-lam) - K2 a r) = -(2*Real.pi*lam) := by
    intro r hr
    rw [mem_Ioi] at hr
    rw [K2_pos a (r-lam) ha (by linarith), K2_pos a r ha (by linarith)]
    push_cast; ring
  have hcongrIoc : (∫ r in Ioc (0:ℝ) lam, Complex.exp (-(c*(r:ℂ))) * (K2 a (r-lam) - K2 a r))
      = ∫ r in Ioc (0:ℝ) lam, (-(2*Real.pi*r)) * Complex.exp (-(c*(r:ℂ))) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    show Complex.exp (-(c*(r:ℂ))) * (K2 a (r-lam) - K2 a r) = (-(2*Real.pi*r)) * Complex.exp (-(c*(r:ℂ)))
    rw [hvalIoc r hr]; ring
  have hcongrIoi : (∫ r in Ioi lam, Complex.exp (-(c*(r:ℂ))) * (K2 a (r-lam) - K2 a r))
      = ∫ r in Ioi lam, (-(2*Real.pi*lam)) * Complex.exp (-(c*(r:ℂ))) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    show Complex.exp (-(c*(r:ℂ))) * (K2 a (r-lam) - K2 a r) = (-(2*Real.pi*lam)) * Complex.exp (-(c*(r:ℂ)))
    rw [hvalIoi r hr]; ring
  have hcontIoc : IntegrableOn (fun r : ℝ => (-(2*Real.pi*r)) * Complex.exp (-(c*(r:ℂ)))) (Ioc (0:ℝ) lam) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc
      ((continuous_const.mul continuous_ofReal).neg.continuousOn.mul
        (Complex.continuous_exp.comp (by fun_prop)).continuousOn)).mono_set Ioc_subset_Icc_self
  have hint2 : IntegrableOn (fun r : ℝ => (-(2*Real.pi*lam)) * Complex.exp (-(c*(r:ℂ)))) (Ioi lam) := by
    have hbase : IntegrableOn (fun r : ℝ => Real.exp (-c.re * r)) (Ioi lam) :=
      integrableOn_exp_mul_Ioi (a := -c.re) (by linarith) lam
    refine MeasureTheory.Integrable.mono' (hbase.const_mul ‖(-(2*Real.pi*lam) : ℂ)‖) ?_ ?_
    · apply Measurable.aestronglyMeasurable
      exact Measurable.mul measurable_const
        (Complex.continuous_exp.measurable.comp (by fun_prop))
    · filter_upwards with r
      rw [norm_mul, Complex.norm_exp]
      have hre : (-(c*(r:ℂ))).re = -c.re * r := by simp [Complex.mul_re, Complex.neg_re]
      rw [hre]
  have hint1 : IntegrableOn (fun r : ℝ => Complex.exp (-(c*(r:ℂ))) * (K2 a (r-lam) - K2 a r)) (Ioc (0:ℝ) lam) := by
    refine MeasureTheory.IntegrableOn.congr_fun hcontIoc ?_ measurableSet_Ioc
    intro r hr
    show (-(2*Real.pi*r)) * Complex.exp (-(c*(r:ℂ))) = Complex.exp (-(c*(r:ℂ))) * (K2 a (r-lam) - K2 a r)
    rw [hvalIoc r hr]; ring
  have hint2' : IntegrableOn (fun r : ℝ => Complex.exp (-(c*(r:ℂ))) * (K2 a (r-lam) - K2 a r)) (Ioi lam) := by
    refine MeasureTheory.IntegrableOn.congr_fun hint2 ?_ measurableSet_Ioi
    intro r hr
    show (-(2*Real.pi*lam)) * Complex.exp (-(c*(r:ℂ))) = Complex.exp (-(c*(r:ℂ))) * (K2 a (r-lam) - K2 a r)
    rw [hvalIoi r hr]; ring
  have hsplit : (∫ r in Ioi (0:ℝ), Complex.exp (-(c*(r:ℂ))) * (K2 a (r-lam) - K2 a r))
      = (∫ r in Ioc (0:ℝ) lam, Complex.exp (-(c*(r:ℂ))) * (K2 a (r-lam) - K2 a r))
        + (∫ r in Ioi lam, Complex.exp (-(c*(r:ℂ))) * (K2 a (r-lam) - K2 a r)) := by
    rw [← hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hint1 hint2']
  rw [hsplit, hcongrIoc, hcongrIoi]
  have hIocval : (∫ r in Ioc (0:ℝ) lam, (-(2*Real.pi*r)) * Complex.exp (-(c*(r:ℂ))))
      = -(2*Real.pi) * (∫ r in (0:ℝ)..lam, (r:ℂ) * Complex.exp (-(c*(r:ℂ)))) := by
    rw [intervalIntegral.integral_of_le hlam.le]
    rw [show (∫ r in Ioc (0:ℝ) lam, (-(2*Real.pi*r)) * Complex.exp (-(c*(r:ℂ))))
        = ∫ r in Ioc (0:ℝ) lam, (-(2*Real.pi)) * ((r:ℂ) * Complex.exp (-(c*(r:ℂ)))) from by
        apply integral_congr_ae; filter_upwards with r; ring]
    rw [integral_const_mul]
  have hIoival : (∫ r in Ioi lam, (-(2*Real.pi*lam)) * Complex.exp (-(c*(r:ℂ))))
      = (-(2*Real.pi*lam)) * (∫ r in Ioi lam, Complex.exp (-(c*(r:ℂ)))) := by
    rw [← integral_const_mul]
  rw [hIocval, hIoival, integral_Ioc_mul_exp c hcne lam, integral_Ioi_exp c hcre lam]
  have hc_form : c = (a:ℂ) + 2*((x+j):ℂ) + (b:ℂ)*Complex.I := by rw [hcdef, hPdef]; ring
  rw [hc_form] at *
  field_simp
  ring

lemma integrable_log_one_add_sq :
    Integrable (fun u : ℝ => Real.log (1+u^2) / (1+u^2)) (volume : Measure ℝ) := by
  have hdom : Integrable (fun u : ℝ => 4 * (1+u^2)^(-(3/4:ℝ))) (volume : Measure ℝ) := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := (volume : Measure ℝ)) (r := 3/2) (by norm_num)
    have h2 : ((-(3/2)/2 : ℝ)) = -(3/4 : ℝ) := by norm_num
    rw [h2] at h
    have h' : Integrable (fun u : ℝ => (1+u^2)^(-(3/4:ℝ))) (volume : Measure ℝ) := by
      simpa [Real.norm_eq_abs, sq_abs] using h
    exact h'.const_mul 4
  refine hdom.mono' ?_ ?_
  · exact ((by fun_prop : Measurable (fun u : ℝ => Real.log (1+u^2)/(1+u^2)))).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (by apply div_nonneg _ (by positivity); apply Real.log_nonneg; nlinarith [sq_nonneg u])]
    rw [div_le_iff₀ (by positivity)]
    have hpos : (0:ℝ) < 1+u^2 := by nlinarith [sq_nonneg u]
    have hlog := Real.log_le_rpow_div (x := 1+u^2) (ε := (1/4:ℝ)) (le_of_lt hpos) (by norm_num)
    have hrw : (1+u^2)^(1/4:ℝ) / (1/4:ℝ) = 4*(1+u^2)^(1/4:ℝ) := by
      rw [div_eq_mul_inv, show ((1:ℝ)/4)⁻¹ = 4 by norm_num]; ring
    rw [hrw] at hlog
    have hval : 4 * (1+u^2)^(-(3/4:ℝ)) * (1+u^2) = 4*(1+u^2)^(1/4:ℝ) := by
      rw [show (-(3/4:ℝ)) = (1/4:ℝ) - 1 by norm_num, Real.rpow_sub hpos, Real.rpow_one]
      field_simp
    rw [hval]
    exact hlog

lemma norm_gK_bound (a lam u : ℝ) (ha : 0 < a) :
    ‖gK a lam u‖ ≤ ((Real.exp (-lam*a)+1)*(1+1/a^2))/(1+u^2) := by
  unfold gK
  rw [norm_mul]
  have h2 : ‖(((a:ℂ)+(u:ℂ)*Complex.I)^2)⁻¹‖ = (a^2+u^2)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero]
    ring_nf
  rw [h2]
  have h1 : ‖Complex.exp (-(((a:ℂ) + (u:ℂ) * Complex.I) * (lam:ℂ))) - 1‖ ≤ Real.exp (-lam*a) + 1 := by
    calc ‖Complex.exp (-(((a:ℂ) + (u:ℂ) * Complex.I) * (lam:ℂ))) - 1‖
        ≤ ‖Complex.exp (-(((a:ℂ) + (u:ℂ) * Complex.I) * (lam:ℂ)))‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = Real.exp (-lam*a) + 1 := by
          rw [Complex.norm_exp, norm_one]
          congr 1
          simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero]
          ring
  have h3 : (a^2+u^2)⁻¹ ≤ (1+1/a^2)*(1+u^2)⁻¹ := by
    have hkey : (1+u^2)/(1+1/a^2) ≤ a^2+u^2 := by
      rw [div_le_iff₀ (by positivity)]
      have ha2 : a^2 ≠ 0 := by positivity
      field_simp
      nlinarith [sq_nonneg a, sq_nonneg u]
    calc (a^2+u^2)⁻¹ ≤ ((1+u^2)/(1+1/a^2))⁻¹ := inv_anti₀ (by positivity) hkey
      _ = (1+1/a^2)*(1+u^2)⁻¹ := by rw [inv_div, div_eq_mul_inv]
  calc ‖Complex.exp (-(((a:ℂ) + (u:ℂ) * Complex.I) * (lam:ℂ))) - 1‖ * (a^2+u^2)⁻¹
      ≤ (Real.exp (-lam*a)+1) * (a^2+u^2)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ (Real.exp (-lam*a)+1) * ((1+1/a^2)*(1+u^2)⁻¹) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = ((Real.exp (-lam*a)+1)*(1+1/a^2))/(1+u^2) := by rw [div_eq_mul_inv]; ring


lemma integrable_log_gK (a lam b : ℝ) (ha : 0 < a) :
    Integrable (fun u : ℝ => (Real.log (2 + |b - u|/2) + 7) * ‖gK a lam u‖) (volume : Measure ℝ) := by
  set C : ℝ := (Real.exp (-lam*a)+1)*(1+1/a^2) with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  have hdom : Integrable (fun u : ℝ => C * (((Real.log (4+|b|)+7+Real.log 3) * (1+u^2)⁻¹) + Real.log (1+u^2)/(1+u^2))) (volume : Measure ℝ) := by
    refine (Integrable.add ?_ ?_).const_mul C
    · exact integrable_inv_one_add_sq.const_mul _
    · exact integrable_log_one_add_sq
  refine hdom.mono' ?_ ?_
  · exact (((Real.measurable_log.comp (by fun_prop)).add measurable_const).aestronglyMeasurable).mul
      ((integrable_gK a lam ha).norm.aestronglyMeasurable)
  · filter_upwards with u
    have hnn : (0:ℝ) ≤ (Real.log (2 + |b - u|/2) + 7) * ‖gK a lam u‖ := by
      apply mul_nonneg _ (norm_nonneg _)
      have hx : (0:ℝ) ≤ Real.log (2 + |b - u|/2) := Real.log_nonneg (by nlinarith [abs_nonneg (b-u)])
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hbk := norm_gK_bound a lam u ha
    have hsub : |b - u| ≤ |b| + |u| := abs_sub_le_iff.mpr
      ⟨by linarith [le_abs_self b, neg_le_abs u], by linarith [le_abs_self u, neg_le_abs b]⟩
    have hbabs : |b - u|/2 ≤ (|b| + |u|)/2 := div_le_div_of_nonneg_right hsub (by norm_num)
    have hlogb : Real.log (2 + |b - u|/2) ≤ Real.log (4+|b|) + Real.log (2+|u|) := by
      have h1 : 2 + |b - u|/2 ≤ (4+|b|)*(2+|u|) := by
        nlinarith [hbabs, abs_nonneg b, abs_nonneg u]
      have h2 : (0:ℝ) < 2 + |b-u|/2 := by nlinarith [abs_nonneg (b-u)]
      have h3 : (0:ℝ) < (4+|b|)*(2+|u|) := by
        have hb : (0:ℝ) ≤ |b| := abs_nonneg b
        have hu : (0:ℝ) ≤ |u| := abs_nonneg u
        nlinarith
      calc Real.log (2 + |b - u|/2) ≤ Real.log ((4+|b|)*(2+|u|)) := Real.log_le_log h2 h1
        _ = Real.log (4+|b|) + Real.log (2+|u|) := Real.log_mul (by positivity) (by positivity)
    have hlogu : Real.log (2+|u|) ≤ Real.log 3 + Real.log (1+u^2) := by
      have h1 : 2 + |u| ≤ 3*(1+u^2) := by nlinarith [abs_nonneg u, sq_abs u, sq_nonneg u]
      have h2 : (0:ℝ) < 2+|u| := by nlinarith [abs_nonneg u]
      have h3 : (0:ℝ) < 3*(1+u^2) := by nlinarith [sq_nonneg u]
      calc Real.log (2+|u|) ≤ Real.log (3*(1+u^2)) := Real.log_le_log h2 h1
        _ = Real.log 3 + Real.log (1+u^2) := Real.log_mul (by norm_num) (by positivity)
    have hABE : Real.log (2 + |b - u|/2) + 7 ≤ Real.log (4+|b|) + 7 + Real.log 3 + Real.log (1+u^2) := by
      have h1 := hlogb
      have h2 := hlogu
      linarith
    calc (Real.log (2 + |b - u|/2) + 7) * ‖gK a lam u‖
        ≤ (Real.log (2 + |b - u|/2) + 7) * (C/(1+u^2)) :=
          mul_le_mul_of_nonneg_left hbk (by
            have : (1:ℝ) ≤ 2 + |b-u|/2 := by nlinarith [abs_nonneg (b-u)]
            linarith [Real.log_nonneg this])
      _ ≤ (Real.log (4+|b|) + 7 + Real.log 3 + Real.log (1+u^2)) * (C/(1+u^2)) :=
          mul_le_mul_of_nonneg_right hABE (div_nonneg (le_of_lt hCpos) (by positivity))
      _ = C * (((Real.log (4+|b|)+7+Real.log 3) * (1+u^2)⁻¹) + Real.log (1+u^2)/(1+u^2)) := by
          rw [div_eq_mul_inv]; ring

lemma integral_gK_zero (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam) :
    (∫ u : ℝ, gK a lam u) = 0 := by
  have h := ghat_eq' a lam 0 ha
  have h2 : ghat a lam 0 = ∫ u : ℝ, gK a lam u := by
    unfold ghat
    apply integral_congr_ae; filter_upwards with u
    rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [h2] at h
  rw [h, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul,
    show (0:ℝ) - lam = -lam by ring, K2_nonpos a (-lam) ha (by linarith), K2_nonpos a 0 ha (le_refl 0)]
  ring

lemma re_wfun (x' b u : ℝ) : (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)).re = x' := by
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]

lemma wfun_cont (x' b : ℝ) : Continuous (fun u : ℝ => (x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) := by
  apply Continuous.add continuous_const
  apply Continuous.mul
  · exact Complex.continuous_ofReal.comp (by fun_prop)
  · exact continuous_const

lemma dgTermC_cont (x' b : ℝ) (hx1 : (1:ℝ)/4 ≤ x') (n : ℕ) :
    Continuous (fun u : ℝ => Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) := by
  have hne : ∀ u : ℝ, ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (n:ℂ) ≠ 0 := by
    intro u h
    have h2 := congrArg Complex.re h
    simp at h2
    have hn : (0:ℝ) ≤ (n : ℝ) := by positivity
    linarith [hx1]
  have h1 : Continuous (fun u : ℝ => (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (n:ℂ))⁻¹) := by
    apply Continuous.inv₀ _ hne
    exact (wfun_cont x' b).add continuous_const
  have h2 : Continuous (fun _ : ℝ => (((n:ℂ)+1)⁻¹)) := continuous_const
  have hdef : Commons.Analysis.SpecialFunctions.Gamma.dgTermC = fun (s : ℂ) (n : ℕ) => ((n:ℂ)+1)⁻¹ - (s + (n:ℂ))⁻¹ := rfl
  rw [hdef]
  exact h2.sub h1

lemma continuous_gK (a lam : ℝ) (ha : 0 < a) : Continuous (fun u : ℝ => gK a lam u) := by
  unfold gK
  apply Continuous.mul
  · exact (Complex.continuous_exp.comp (by fun_prop)).sub continuous_const
  · apply Continuous.inv₀ (by fun_prop)
    intro u h
    have h0 : (a:ℂ)+(u:ℂ)*Complex.I = 0 := by
      have hm : ((a:ℂ)+(u:ℂ)*Complex.I)*((a:ℂ)+(u:ℂ)*Complex.I) = 0 := by rwa [sq] at h
      exact mul_self_eq_zero.mp hm
    have := congrArg Complex.re h0; simp at this; linarith

lemma integrable_bound_gK (a lam b : ℝ) (ha : 0 < a) :
    Integrable (fun u : ℝ => (Real.log (2 + |b - u|/2) + 7 + ‖(Real.eulerMascheroniConstant : ℂ)‖) * ‖gK a lam u‖) (volume : Measure ℝ) := by
  have h1 : (fun u : ℝ => (Real.log (2 + |b - u|/2) + 7 + ‖(Real.eulerMascheroniConstant : ℂ)‖) * ‖gK a lam u‖)
      = (fun u : ℝ => (Real.log (2 + |b - u|/2) + 7) * ‖gK a lam u‖ + ‖(Real.eulerMascheroniConstant : ℂ)‖ * ‖gK a lam u‖) := by
    funext u; ring
  rw [h1]
  exact (integrable_log_gK a lam b ha).add ((integrable_gK_norm a lam ha).const_mul _)

lemma psi_integrable_inv_gK (a lam x' b j : ℝ) (ha : 0 < a) (hj : 0 < x' + j) :
    Integrable (fun u : ℝ => ((((x'+j:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹) * gK a lam u) (volume : Measure ℝ) := by
  refine ((integrable_gK_norm a lam ha).const_mul ((x'+j)⁻¹)).mono' ?_ ?_
  · have hc : Continuous (fun u : ℝ => ((((x'+j:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹)) := by
      apply Continuous.inv₀ (wfun_cont (x'+j) b) (fun u h => ?_)
      have h2 := congrArg Complex.re h
      rw [re_wfun] at h2
      simp at h2
      linarith
    exact (hc.mul (continuous_gK a lam ha)).aestronglyMeasurable
  · filter_upwards with u
    rw [norm_mul]
    have hnorm : x' + j ≤ ‖((x'+j:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I‖ := by
      have h := Complex.re_le_norm (((x'+j:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)
      rwa [re_wfun] at h
    have h1 : ‖(((x'+j:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹‖ ≤ (x'+j)⁻¹ := by
      rw [norm_inv]; exact inv_anti₀ hj hnorm
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

lemma psi_J_eq (a lam x b j : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hxj : 0 < x + j) :
    (∫ u : ℝ, gK a lam u / (((x+j:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I))
      = 4 * Real.pi * ((Complex.exp (-(((a:ℂ) + 2*((x+j:ℝ):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x+j:ℝ):ℂ) + (b:ℂ)*Complex.I)^2)) := by
  have h := J_eq a lam x b j ha hlam hxj
  have e1 : (∫ u : ℝ, gK a lam u / (((x+j:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I))
      = ∫ u : ℝ, gK a lam u / (((x:ℂ) + (j:ℂ)) + (((b-u)/2:ℝ):ℂ)*Complex.I) := by
    apply integral_congr_ae; filter_upwards with u
    push_cast
    ring
  have e2 : (4 * Real.pi * ((Complex.exp (-(((a:ℂ) + 2*((x:ℂ) + (j:ℂ)) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1)) / (((a:ℂ) + 2*((x:ℂ) + (j:ℂ)) + (b:ℂ)*Complex.I)^2))
      = 4 * Real.pi * ((Complex.exp (-(((a:ℂ) + 2*((x+j:ℝ):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x+j:ℝ):ℂ) + (b:ℂ)*Complex.I)^2)) := by
    rw [mul_div_assoc]
    congr 1
    push_cast; ring
  rw [e1, h, e2]

lemma interchange_aux (a lam x' b : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hx1 : (1:ℝ)/4 ≤ x') (hx2 : x' ≤ 8) :
    (∫ u : ℝ, Complex.digamma ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) * gK a lam u)
      = -4 * Real.pi * ∑' n : ℕ, (Complex.exp (-(((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)^2) := by
  have hFmeas : ∀ N : ℕ, AEStronglyMeasurable
      (fun u : ℝ => (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u) volume := by
    intro N
    have hc : Continuous (fun u : ℝ => (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n)) := by
      apply Continuous.add continuous_const
      exact continuous_finset_sum _ (fun n _ => dgTermC_cont x' b hx1 n)
    exact (hc.mul (continuous_gK a lam ha)).aestronglyMeasurable
  have hbnd : ∀ (N : ℕ) (u : ℝ), ‖(-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u‖
      ≤ (Real.log (2 + |b - u|/2) + 7 + ‖(Real.eulerMascheroniConstant : ℂ)‖) * ‖gK a lam u‖ := by
    intro N u
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hsum : Summable (fun n : ℕ => ‖Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n‖) :=
      Commons.Analysis.SpecialFunctions.Gamma.summable_dgTerm_norm _ (by rw [re_wfun]; exact hx1)
    have hb1 : (∑' n : ℕ, ‖Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n‖) ≤ Real.log (2 + |b-u|/2) + 7 := by
      have h := Commons.Analysis.SpecialFunctions.Gamma.digamma_series_norm_bound x' ((b-u)/2) hx1 hx2
      rw [show |((b-u)/2 : ℝ)| = |b-u|/2 by rw [abs_div]; norm_num] at h
      exact h
    have h2 : ‖∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n‖ ≤ Real.log (2 + |b-u|/2) + 7 :=
      le_trans (norm_sum_le _ _) (le_trans (hsum.sum_le_tsum _ (fun n _ => norm_nonneg _)) hb1)
    calc ‖(-(Real.eulerMascheroniConstant:ℂ)) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n‖
        ≤ ‖(-(Real.eulerMascheroniConstant:ℂ))‖ + ‖∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n‖ := norm_add_le _ _
      _ ≤ ‖(Real.eulerMascheroniConstant:ℂ)‖ + (Real.log (2 + |b-u|/2) + 7) := by rw [norm_neg]; linarith
      _ = Real.log (2 + |b-u|/2) + 7 + ‖(Real.eulerMascheroniConstant : ℂ)‖ := by ring
  have hlim : ∀ᵐ u : ℝ ∂volume, Tendsto (fun N : ℕ => (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u) atTop
      (nhds (Complex.digamma ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) * gK a lam u)) := by
    filter_upwards with u
    have hsum : Summable (fun n : ℕ => Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) := by
      refine Summable.of_norm ?_
      simpa using Commons.Analysis.SpecialFunctions.Gamma.summable_dgTerm_norm ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) (by rw [re_wfun]; exact hx1)
    have hs : HasSum (fun n : ℕ => Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n)
        (Complex.digamma ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (Real.eulerMascheroniConstant:ℂ)) := by
      rw [hsum.hasSum_iff_tendsto_nat]
      have hthis := Commons.Analysis.SpecialFunctions.Gamma.digamma_eq_euler_sub_tsum ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) (by rw [re_wfun]; exact hx1)
      rw [hthis]
      rw [show (-(Real.eulerMascheroniConstant:ℂ) + ∑' n : ℕ, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) + (Real.eulerMascheroniConstant:ℂ) = ∑' n : ℕ, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n by ring]
      exact hsum.hasSum.tendsto_sum_nat
    have ht' := hs.tendsto_sum_nat.const_add (-(Real.eulerMascheroniConstant:ℂ))
    have ht'' : Tendsto (fun N : ℕ => -(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) atTop (nhds (Complex.digamma ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I))) := by
      rw [add_comm (Complex.digamma _)] at ht'
      simpa using ht'
    exact ht''.mul_const _
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure ℝ))
    (F := fun (N : ℕ) (u : ℝ) => (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u)
    (f := fun u : ℝ => Complex.digamma ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) * gK a lam u)
    (fun u : ℝ => (Real.log (2 + |b - u|/2) + 7 + ‖(Real.eulerMascheroniConstant : ℂ)‖) * ‖gK a lam u‖)
    hFmeas (integrable_bound_gK a lam b ha) (fun N => Filter.Eventually.of_forall (fun u => hbnd N u)) hlim
  -- compute ∫ F N
  have hFN : ∀ N : ℕ, (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u)
      = - ∑ n ∈ Finset.range N, 4 * Real.pi * ((Complex.exp (-(((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)^2)) := by
    have hI1 : ∀ n : ℕ, Integrable (fun u : ℝ => (((n:ℂ)+1)⁻¹) * gK a lam u) (volume : Measure ℝ) :=
      fun n => (integrable_gK a lam ha).const_mul _
    have hI2 : ∀ n : ℕ, Integrable (fun u : ℝ => ((((x'+n:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹) * gK a lam u) (volume : Measure ℝ) :=
      fun n => psi_integrable_inv_gK a lam x' b (n:ℝ) ha (by positivity)
    have hpiece_int : ∀ n : ℕ, Integrable (fun u : ℝ => Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n * gK a lam u) (volume : Measure ℝ) := by
      intro n
      refine ((integrable_gK_norm a lam ha).const_mul ((((n:ℝ)+1)⁻¹ + (x'+n)⁻¹))).mono' ?_ ?_
      · exact ((dgTermC_cont x' b hx1 n).mul (continuous_gK a lam ha)).aestronglyMeasurable
      · filter_upwards with u
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        have hdef : ∀ (s : ℂ) (k : ℕ), Commons.Analysis.SpecialFunctions.Gamma.dgTermC s k = ((k:ℂ)+1)⁻¹ - (s + (k:ℂ))⁻¹ := fun s k => rfl
        have hw : ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (n:ℂ) = ((x'+n:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I := by push_cast; ring
        rw [hdef, hw]
        have h1 : ‖(((n:ℂ)+1)⁻¹)‖ ≤ ((n:ℝ)+1)⁻¹ := by
          rw [norm_inv]
          apply inv_anti₀
          · show (0:ℝ) < (n:ℝ)+1
            positivity
          · have h := Complex.re_le_norm (((n:ℂ)+1))
            simpa using h
        have h2 : ‖((((x'+n:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹)‖ ≤ (x'+n)⁻¹ := by
          rw [norm_inv]
          apply inv_anti₀
          · show (0:ℝ) < x'+n
            have hn : (0:ℝ) ≤ (n:ℝ) := by positivity
            linarith [hx1, hn]
          · show x'+n ≤ ‖((x'+n:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I‖
            have h := Complex.re_le_norm (((x'+n:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)
            rwa [re_wfun] at h
        calc ‖((n:ℂ)+1)⁻¹ - (((x'+n:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹‖
            ≤ ‖((n:ℂ)+1)⁻¹‖ + ‖((((x'+n:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹)‖ := norm_sub_le _ _
          _ ≤ ((n:ℝ)+1)⁻¹ + (x'+n)⁻¹ := add_le_add h1 h2
    have hpieceint : ∀ n : ℕ, (∫ u : ℝ, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n * gK a lam u)
        = -(4 * Real.pi * ((Complex.exp (-(((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)^2))) := by
      intro n
      have hJfun : (fun u : ℝ => ((((x'+n:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹) * gK a lam u)
          = fun u : ℝ => gK a lam u / (((x'+n:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) := by
        funext u
        rw [div_eq_mul_inv]
        exact mul_comm _ _
      have hJ : (∫ u : ℝ, ((((x'+n:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹) * gK a lam u)
          = 4 * Real.pi * ((Complex.exp (-(((a:ℂ) + 2*((x'+n:ℝ):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n:ℝ):ℂ) + (b:ℂ)*Complex.I)^2)) := by
        rw [hJfun]
        exact psi_J_eq a lam x' b (n:ℝ) ha hlam (by positivity)
      have hcong : (∫ u : ℝ, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n * gK a lam u)
          = ∫ u : ℝ, ((((n:ℂ)+1)⁻¹) * gK a lam u - ((((x'+n:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹) * gK a lam u) := by
        apply integral_congr_ae; filter_upwards with u
        have hdef : ∀ (s : ℂ) (k : ℕ), Commons.Analysis.SpecialFunctions.Gamma.dgTermC s k = ((k:ℂ)+1)⁻¹ - (s + (k:ℂ))⁻¹ := fun s k => rfl
        have hw : ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (n:ℂ) = ((x'+n:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I := by push_cast; ring
        rw [hdef, hw, sub_mul]
      rw [hcong, MeasureTheory.integral_sub (hI1 n) (hI2 n), MeasureTheory.integral_const_mul,
        integral_gK_zero a lam ha hlam, mul_zero, zero_sub, hJ]
      rw [show ((x'+n:ℝ):ℂ) = (x':ℂ) + (n:ℂ) from by push_cast; ring]
    have hFint : ∀ N : ℕ, Integrable (fun u : ℝ => (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u) (volume : Measure ℝ) :=
      fun N => (integrable_bound_gK a lam b ha).mono' (hFmeas N) (Filter.Eventually.of_forall (fun u => hbnd N u))
    intro N
    induction N with
    | zero =>
      simp only [Finset.sum_range_zero, add_zero, neg_zero]
      rw [show (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ)) * gK a lam u) = (-(Real.eulerMascheroniConstant:ℂ)) * (∫ u : ℝ, gK a lam u) from integral_const_mul _ _]
      rw [integral_gK_zero a lam ha hlam, mul_zero]
    | succ N ih =>
      simp only [Finset.sum_range_succ]
      rw [show (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ) + (∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n + Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) N)) * gK a lam u)
          = ∫ u : ℝ, ((-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u + Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) N * gK a lam u) from by
          apply integral_congr_ae; filter_upwards with u
          ring]
      rw [MeasureTheory.integral_add (hFint N) (hpiece_int N), ih, hpieceint N]
      ring

  have hTbound : ∀ n : ℕ, ‖(Complex.exp (-(((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)^2)‖ ≤ 8/((n:ℝ)+1)^2 := by
    intro n
    set c : ℂ := (a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I with hc
    have hcre : c.re = a + 2*(x'+n) := by
      have h1 : c = (((a + 2*(x'+n)) : ℝ) : ℂ) + (b:ℂ)*Complex.I := by rw [hc]; push_cast; ring
      rw [h1]
      simp
    have hcpos : 0 < c.re := by
      rw [hcre]
      have hn : (0:ℝ) ≤ (n:ℝ) := by positivity
      push_cast
      linarith [ha, hx1, hn]
    have hnum : ‖Complex.exp (-(c*(lam:ℂ))) - 1‖ ≤ 2 := by
      calc ‖Complex.exp (-(c*(lam:ℂ))) - 1‖ ≤ ‖Complex.exp (-(c*(lam:ℂ)))‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = Real.exp ((-(c*(lam:ℂ))).re) + 1 := by rw [Complex.norm_exp, norm_one]
        _ ≤ 2 := by
          have hre : (-(c*(lam:ℂ))).re = -(c.re * lam) := by
            simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_one,
              mul_zero, sub_zero]
          rw [hre]
          have h1 : Real.exp (-(c.re * lam)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hcpos, hlam])
          linarith
    have hden : c.re^2 ≤ ‖c^2‖ := by
      rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]
      have hx := sq_nonneg c.im
      nlinarith [hx]
    have hkey : ((n:ℝ)+1)/2 ≤ c.re := by
      rw [hcre]
      have hn : (0:ℝ) ≤ (n:ℝ) := by positivity
      push_cast
      linarith [ha, hx1, hn]
    have hkey2 : ((n:ℝ)+1)^2/4 ≤ c.re^2 := by
      have h1 : (0:ℝ) ≤ ((n:ℝ)+1)/2 := by positivity
      have h2 := mul_self_le_mul_self h1 hkey
      nlinarith [h2]
    calc ‖(Complex.exp (-(c*(lam:ℂ))) - 1) / c^2‖
        = ‖Complex.exp (-(c*(lam:ℂ))) - 1‖ / ‖c^2‖ := norm_div _ _
      _ ≤ 2 / (c.re^2) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul hnum (inv_anti₀ (pow_pos hcpos 2) hden) (by positivity) (by norm_num : (0:ℝ) ≤ 2)
      _ ≤ 2 / (((n:ℝ)+1)^2/4) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hkey2) (by norm_num : (0:ℝ) ≤ 2)
      _ = 8/((n:ℝ)+1)^2 := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          have hn1 : ((n:ℝ)+1) ≠ 0 := by positivity
          field_simp
          ring
  have hTsummable : Summable (fun n : ℕ => 8/((n:ℝ)+1)^2) := by
    have h := hasSum_zeta_two.summable
    have h' : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^2) := by
      have h2 := (summable_nat_add_iff (f := fun n : ℕ => (1:ℝ)/(n:ℝ)^2) 1).mpr h
      simpa using h2
    simpa [div_eq_mul_inv, one_mul] using h'.mul_left 8
  have hT : Summable (fun n : ℕ => (Complex.exp (-(((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)^2)) :=
    Summable.of_norm_bounded hTsummable hTbound
  have hTlim := hT.hasSum.tendsto_sum_nat
  have hmul : (fun N : ℕ => - ∑ n ∈ Finset.range N, ((4 * Real.pi * ((Complex.exp (-(((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)^2))) : ℂ))
      = fun N : ℕ => (-4 * Real.pi : ℂ) * ∑ n ∈ Finset.range N, ((Complex.exp (-(((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)^2)) := by
    funext N
    rw [← Finset.mul_sum]
    ring
  have h4 : Tendsto (fun N : ℕ => - ∑ n ∈ Finset.range N, ((4 * Real.pi * ((Complex.exp (-(((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)^2))) : ℂ)) atTop
      (nhds (- (4 * Real.pi * ∑' n : ℕ, (Complex.exp (-(((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)^2)))) := by
    rw [hmul]
    have h6 : (- (4 * Real.pi * ∑' n : ℕ, (Complex.exp (-(((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)^2)))
        = (-4 * Real.pi : ℂ) * ∑' n : ℕ, ((Complex.exp (-(((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)^2)) := by ring
    rw [h6]
    exact hTlim.const_mul ((-4 : ℂ) * Real.pi)
  have h1' : Tendsto (fun N : ℕ => - ∑ n ∈ Finset.range N, ((4 * Real.pi * ((Complex.exp (-(((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)^2))) : ℂ)) atTop
      (nhds (∫ u : ℝ, Complex.digamma ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) * gK a lam u)) := by
    have h1 := hDCT
    rw [show (fun N : ℕ => ∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u)
        = fun N : ℕ => - ∑ n ∈ Finset.range N, ((4 * Real.pi * ((Complex.exp (-(((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)^2))) : ℂ) from by
      funext N; exact hFN N] at h1
    exact h1
  have key : (∫ u : ℝ, Complex.digamma ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) * gK a lam u)
      = - (4 * Real.pi * ∑' n : ℕ, (Complex.exp (-(((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)^2)) :=
    tendsto_nhds_unique h1' h4
  rw [key]
  ring


lemma psi_digamma_add_nat (m : ℕ) (w : ℂ) (hw : ∀ j : ℕ, j < m → ∀ n : ℕ, w + (j:ℂ) ≠ -(n:ℂ)) :
    Complex.digamma (w + m) = Complex.digamma w + ∑ j ∈ Finset.range m, (w + (j:ℂ))⁻¹ := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hk : ∀ j : ℕ, j < k → ∀ n : ℕ, w + (j:ℂ) ≠ -(n:ℂ) := fun j hj => hw j (Nat.lt_succ_of_lt hj)
    rw [Finset.sum_range_succ, show w + ((k+1:ℕ):ℂ) = (w + (k:ℂ)) + 1 by push_cast; ring,
        Complex.digamma_apply_add_one (w + (k:ℂ)) (fun n => hw k (Nat.lt_succ_self k) n), ih hk]
    ring

lemma psi_summable_eight : Summable (fun n : ℕ => (8:ℝ)/((n:ℝ)+1)^2) := by
  have h := hasSum_zeta_two.summable
  have h' : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^2) := by
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => (1:ℝ)/(n:ℝ)^2) 1).mpr h
    simpa using h2
  simpa [div_eq_mul_inv, one_mul] using h'.mul_left 8

lemma psi_T_bound (a lam x' b : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hx1 : (1:ℝ)/4 ≤ x') (n : ℕ) :
    ‖(Complex.exp (-(((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)^2)‖ ≤ 8/((n:ℝ)+1)^2 := by
  set c : ℂ := (a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I with hc
  have hcre : c.re = a + 2*(x'+n) := by
    have h1 : c = (((a + 2*(x'+n)) : ℝ) : ℂ) + (b:ℂ)*Complex.I := by rw [hc]; push_cast; ring
    rw [h1]
    simp
  have hcpos : 0 < c.re := by
    rw [hcre]
    have hn : (0:ℝ) ≤ (n:ℝ) := by positivity
    push_cast
    linarith [ha, hx1, hn]
  have hnum : ‖Complex.exp (-(c*(lam:ℂ))) - 1‖ ≤ 2 := by
    calc ‖Complex.exp (-(c*(lam:ℂ))) - 1‖ ≤ ‖Complex.exp (-(c*(lam:ℂ)))‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = Real.exp ((-(c*(lam:ℂ))).re) + 1 := by rw [Complex.norm_exp, norm_one]
      _ ≤ 2 := by
        have hre : (-(c*(lam:ℂ))).re = -(c.re * lam) := by
          simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_one,
            mul_zero, sub_zero]
        rw [hre]
        have h1 : Real.exp (-(c.re * lam)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hcpos, hlam])
        linarith
  have hden : c.re^2 ≤ ‖c^2‖ := by
    rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]
    have hx := sq_nonneg c.im
    nlinarith [hx]
  have hkey : ((n:ℝ)+1)/2 ≤ c.re := by
    rw [hcre]
    have hn : (0:ℝ) ≤ (n:ℝ) := by positivity
    push_cast
    linarith [ha, hx1, hn]
  have hkey2 : ((n:ℝ)+1)^2/4 ≤ c.re^2 := by
    have h1 : (0:ℝ) ≤ ((n:ℝ)+1)/2 := by positivity
    have h2 := mul_self_le_mul_self h1 hkey
    nlinarith [h2]
  calc ‖(Complex.exp (-(c*(lam:ℂ))) - 1) / c^2‖
      = ‖Complex.exp (-(c*(lam:ℂ))) - 1‖ / ‖c^2‖ := norm_div _ _
    _ ≤ 2 / (c.re^2) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul hnum (inv_anti₀ (pow_pos hcpos 2) hden) (by positivity) (by norm_num : (0:ℝ) ≤ 2)
    _ ≤ 2 / (((n:ℝ)+1)^2/4) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hkey2) (by norm_num : (0:ℝ) ≤ 2)
    _ = 8/((n:ℝ)+1)^2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have hn1 : ((n:ℝ)+1) ≠ 0 := by positivity
        field_simp
        ring

lemma psi_T_summable (a lam x' b : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hx1 : (1:ℝ)/4 ≤ x') :
    Summable (fun n : ℕ => (Complex.exp (-(((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)^2)) :=
  Summable.of_norm_bounded psi_summable_eight (fun n => psi_T_bound a lam x' b ha hlam hx1 n)
lemma psi_hFN (a lam x' b : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hx1 : (1:ℝ)/4 ≤ x') (hx2 : x' ≤ 8) (N : ℕ) :
    (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u)
      = - ∑ n ∈ Finset.range N, 4 * Real.pi * ((Complex.exp (-(((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+n):ℂ) + (b:ℂ)*Complex.I)^2)) := by
  have hcont1 : ∀ M : ℕ, Continuous (fun u : ℝ => (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n)) := by
    intro M
    apply Continuous.add continuous_const
    exact continuous_finset_sum _ (fun n _ => dgTermC_cont x' b hx1 n)
  have hbnd : ∀ (M : ℕ) (u : ℝ), ‖(-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u‖
      ≤ (Real.log (2 + |b - u|/2) + 7 + ‖(Real.eulerMascheroniConstant : ℂ)‖) * ‖gK a lam u‖ := by
    intro M u
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hsum : Summable (fun n : ℕ => ‖Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n‖) :=
      Commons.Analysis.SpecialFunctions.Gamma.summable_dgTerm_norm _ (by rw [re_wfun]; exact hx1)
    have hb1 : (∑' n : ℕ, ‖Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n‖) ≤ Real.log (2 + |b-u|/2) + 7 := by
      have h := Commons.Analysis.SpecialFunctions.Gamma.digamma_series_norm_bound x' ((b-u)/2) hx1 hx2
      rw [show |((b-u)/2 : ℝ)| = |b-u|/2 by rw [abs_div]; norm_num] at h
      exact h
    have h2 : ‖∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n‖ ≤ Real.log (2 + |b-u|/2) + 7 :=
      le_trans (norm_sum_le _ _) (le_trans (hsum.sum_le_tsum _ (fun n _ => norm_nonneg _)) hb1)
    calc ‖(-(Real.eulerMascheroniConstant:ℂ)) + ∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n‖
        ≤ ‖(-(Real.eulerMascheroniConstant:ℂ))‖ + ‖∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n‖ := norm_add_le _ _
      _ ≤ ‖(Real.eulerMascheroniConstant:ℂ)‖ + (Real.log (2 + |b-u|/2) + 7) := by rw [norm_neg]; linarith
      _ = Real.log (2 + |b-u|/2) + 7 + ‖(Real.eulerMascheroniConstant : ℂ)‖ := by ring
  have hFint : ∀ M : ℕ, Integrable (fun u : ℝ => (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u) (volume : Measure ℝ) :=
    fun M => (integrable_bound_gK a lam b ha).mono' (((hcont1 M).mul (continuous_gK a lam ha)).aestronglyMeasurable) (Filter.Eventually.of_forall (hbnd M))
  have hI1 : ∀ n : ℕ, Integrable (fun u : ℝ => (((n:ℂ)+1)⁻¹) * gK a lam u) (volume : Measure ℝ) :=
    fun n => (integrable_gK a lam ha).const_mul _
  have hI2 : ∀ n : ℕ, Integrable (fun u : ℝ => ((((x'+n:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹) * gK a lam u) (volume : Measure ℝ) :=
    fun n => psi_integrable_inv_gK a lam x' b (n:ℝ) ha (by positivity)
  have hpiece_int : ∀ k : ℕ, Integrable (fun u : ℝ => Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) k * gK a lam u) (volume : Measure ℝ) := by
    intro k
    refine ((integrable_gK_norm a lam ha).const_mul ((((k:ℝ)+1)⁻¹ + (x'+k)⁻¹))).mono' ?_ ?_
    · exact ((dgTermC_cont x' b hx1 k).mul (continuous_gK a lam ha)).aestronglyMeasurable
    · filter_upwards with u
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hdef : ∀ (s : ℂ) (m : ℕ), Commons.Analysis.SpecialFunctions.Gamma.dgTermC s m = ((m:ℂ)+1)⁻¹ - (s + (m:ℂ))⁻¹ := fun s m => rfl
      have hw : ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (k:ℂ) = ((x'+k:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I := by push_cast; ring
      rw [hdef, hw]
      have h1 : ‖(((k:ℂ)+1)⁻¹)‖ ≤ ((k:ℝ)+1)⁻¹ := by
        rw [norm_inv]
        apply inv_anti₀
        · show (0:ℝ) < (k:ℝ)+1
          positivity
        · have h := Complex.re_le_norm (((k:ℂ)+1))
          simpa using h
      have h2 : ‖((((x'+k:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹)‖ ≤ (x'+k)⁻¹ := by
        rw [norm_inv]
        apply inv_anti₀
        · show (0:ℝ) < x'+k
          have hn : (0:ℝ) ≤ (k:ℝ) := by positivity
          linarith [hx1, hn]
        · show x'+k ≤ ‖((x'+k:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I‖
          have h := Complex.re_le_norm (((x'+k:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)
          rwa [re_wfun] at h
      calc ‖((k:ℂ)+1)⁻¹ - (((x'+k:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹‖
          ≤ ‖((k:ℂ)+1)⁻¹‖ + ‖((((x'+k:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹)‖ := norm_sub_le _ _
        _ ≤ ((k:ℝ)+1)⁻¹ + (x'+k)⁻¹ := add_le_add h1 h2
  have hpieceval : ∀ k : ℕ, (∫ u : ℝ, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) k * gK a lam u)
      = -(4 * Real.pi * ((Complex.exp (-(((a:ℂ) + 2*((x'+k):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+k):ℂ) + (b:ℂ)*Complex.I)^2))) := by
    intro k
    have hJfun : (fun u : ℝ => ((((x'+k:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹) * gK a lam u)
        = fun u : ℝ => gK a lam u / (((x'+k:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) := by
      funext u
      rw [div_eq_mul_inv]
      exact mul_comm _ _
    have hJ : (∫ u : ℝ, ((((x'+k:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹) * gK a lam u)
        = 4 * Real.pi * ((Complex.exp (-(((a:ℂ) + 2*((x'+k:ℝ):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x'+k:ℝ):ℂ) + (b:ℂ)*Complex.I)^2)) := by
      rw [hJfun]
      exact psi_J_eq a lam x' b (k:ℝ) ha hlam (by positivity)
    have hcong : (∫ u : ℝ, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) k * gK a lam u)
        = ∫ u : ℝ, ((((k:ℂ)+1)⁻¹) * gK a lam u - ((((x'+k:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹) * gK a lam u) := by
      apply integral_congr_ae; filter_upwards with u
      have hdef : ∀ (s : ℂ) (m : ℕ), Commons.Analysis.SpecialFunctions.Gamma.dgTermC s m = ((m:ℂ)+1)⁻¹ - (s + (m:ℂ))⁻¹ := fun s m => rfl
      have hw : ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (k:ℂ) = ((x'+k:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I := by push_cast; ring
      rw [hdef, hw, sub_mul]
    rw [hcong, MeasureTheory.integral_sub (hI1 k) (hI2 k), MeasureTheory.integral_const_mul,
      integral_gK_zero a lam ha hlam, mul_zero, zero_sub, hJ]
    rw [show ((x'+k:ℝ):ℂ) = (x':ℂ) + (k:ℂ) from by push_cast; ring]
  induction N with
  | zero =>
    simp only [Finset.sum_range_zero, add_zero, neg_zero]
    rw [show (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ)) * gK a lam u) = (-(Real.eulerMascheroniConstant:ℂ)) * (∫ u : ℝ, gK a lam u) from integral_const_mul _ _]
    rw [integral_gK_zero a lam ha hlam, mul_zero]
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    rw [show (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ) + (∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n + Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) N)) * gK a lam u)
        = ∫ u : ℝ, ((-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u + Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) N * gK a lam u) from by
        apply integral_congr_ae; filter_upwards with u
        ring]
    rw [MeasureTheory.integral_add (hFint N) (hpiece_int N), ih, hpieceval N]
    ring
def psiT (a lam x b : ℝ) (n : ℕ) : ℂ :=
  (Complex.exp (-(((a:ℂ) + 2*((x+n):ℂ) + (b:ℂ)*Complex.I)*(lam:ℂ))) - 1) / (((a:ℂ) + 2*((x+n):ℂ) + (b:ℂ)*Complex.I)^2)

lemma psiT_bound (a lam x' b : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hx1 : (1:ℝ)/4 ≤ x') (n : ℕ) :
    ‖psiT a lam x' b n‖ ≤ 8/((n:ℝ)+1)^2 :=
  psi_T_bound a lam x' b ha hlam hx1 n

lemma psiT_summable (a lam x' b : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hx1 : (1:ℝ)/4 ≤ x') :
    Summable (fun n : ℕ => psiT a lam x' b n) :=
  psi_T_summable a lam x' b ha hlam hx1

lemma psiT_index (a lam b x x' : ℝ) (m : ℕ) (h : x = x' + m) (i : ℕ) :
    psiT a lam x' b (i + m) = psiT a lam x b i := by
  have hz : ((x':ℂ) + ((i+m:ℕ):ℂ)) = ((x:ℂ) + (i:ℂ)) := by
    rw [h]; push_cast; ring
  simp only [psiT]
  rw [hz]

lemma psi_inv_shift_val (a lam x' b : ℝ) (ha : 0 < a) (hlam : 0 < lam) (j : ℕ) (hj : 0 < x' + (j:ℝ)) :
    (∫ u : ℝ, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹ * gK a lam u)
      = 4 * Real.pi * psiT a lam x' b j := by
  have h1 : (fun u : ℝ => (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹ * gK a lam u)
      = fun u : ℝ => gK a lam u / (((x'+j:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) := by
    funext u
    have hz : ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ) = ((x'+j:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I := by push_cast; ring
    rw [hz, div_eq_mul_inv]
    exact mul_comm _ _
  rw [h1]
  rw [psi_J_eq a lam x' b (j:ℝ) ha hlam hj]
  unfold psiT
  rw [show ((x'+j:ℝ):ℂ) = (x':ℂ) + (j:ℂ) from by push_cast; ring]

lemma psi_inv_shift_int (a lam x' b : ℝ) (ha : 0 < a) (j : ℕ) (hj : 0 < x' + (j:ℝ)) :
    Integrable (fun u : ℝ => (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹ * gK a lam u) (volume : Measure ℝ) := by
  have hfun : (fun u : ℝ => ((((x'+j:ℝ):ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)⁻¹) * gK a lam u)
      = fun u : ℝ => (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹ * gK a lam u := by
    funext u
    have hz : ((x'+j:ℝ):ℂ) = (x':ℂ) + (j:ℂ) := by push_cast; ring
    rw [hz]
    ring
  rw [← hfun]
  exact psi_integrable_inv_gK a lam x' b (j:ℝ) ha hj

theorem interchange_gen (a lam x b : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hx : (1:ℝ)/4 ≤ x) :
    (∫ u : ℝ, Complex.digamma ((x:ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) * gK a lam u)
      = -4 * Real.pi * ∑' n : ℕ, psiT a lam x b n := by
  set m : ℕ := Nat.floor (x - (1:ℝ)/4) with hm
  set x' : ℝ := x - m with hx'def
  have hxm : x = x' + m := by rw [hx'def]; ring
  have hx'1 : (1:ℝ)/4 ≤ x' := by
    rw [hx'def]
    have := Nat.floor_le (show (0:ℝ) ≤ x - (1:ℝ)/4 by linarith)
    linarith
  have hx'8 : x' ≤ 8 := by
    rw [hx'def]
    have := Nat.lt_floor_add_one (x - (1:ℝ)/4)
    linarith
  have hjm : ∀ j : ℕ, (0:ℝ) < x' + (j:ℝ) := by
    intro j
    have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    linarith [hx'1]
  have hpw : ∀ u : ℝ, Complex.digamma ((x:ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)
      = Complex.digamma ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + ∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹ := by
    intro u
    have hzw : ((x:ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) = (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (m:ℂ)) := by
      rw [hxm]; push_cast; ring
    have hsh := psi_digamma_add_nat m (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I)) ?_
    · rw [hzw, hsh]
    · intro j hj n hflag
      exfalso
      have h3 : (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ)).re = x' + (j:ℝ) := by
        rw [Complex.add_re, re_wfun]; simp
      have h5 := congrArg Complex.re hflag
      rw [h3] at h5
      simp at h5
      have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith [hx'1]
  have hcont1 : ∀ M : ℕ, Continuous (fun u : ℝ => (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n)) := by
    intro M
    apply Continuous.add continuous_const
    exact continuous_finset_sum _ (fun n _ => dgTermC_cont x' b hx'1 n)
  have hcontj : ∀ j : ℕ, Continuous (fun u : ℝ => (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹) := by
    intro j
    apply Continuous.inv₀ ((wfun_cont x' b).add continuous_const)
    intro u hflag
    have hfl : ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ) = 0 := by
      simpa using hflag
    have h3 : (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ)).re = x' + (j:ℝ) := by
      rw [Complex.add_re, re_wfun]; simp
    have h5 := congrArg Complex.re hfl
    rw [h3] at h5
    simp at h5
    have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    linarith [hx'1]
  have hCnn : ∀ u : ℝ, ‖∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹‖ ≤ ∑ j ∈ Finset.range m, (x' + (j:ℝ))⁻¹ := by
    intro u
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun j hj => ?_))
    rw [norm_inv]
    refine inv_anti₀ (hjm j) ?_
    have h3 : (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ)).re = x' + (j:ℝ) := by
      rw [Complex.add_re, re_wfun]; simp
    have h := Complex.re_le_norm (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))
    rwa [h3] at h
  have hb2 : ∀ (M : ℕ) (u : ℝ), ‖(-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n)‖ ≤ ‖(Real.eulerMascheroniConstant:ℂ)‖ + (Real.log (2 + |b-u|/2) + 7) := by
    intro M u
    have hsum : Summable (fun n : ℕ => ‖Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n‖) :=
      Commons.Analysis.SpecialFunctions.Gamma.summable_dgTerm_norm _ (by rw [re_wfun]; exact hx'1)
    have hb1 : (∑' n : ℕ, ‖Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n‖) ≤ Real.log (2 + |b-u|/2) + 7 := by
      have h := Commons.Analysis.SpecialFunctions.Gamma.digamma_series_norm_bound x' ((b-u)/2) hx'1 hx'8
      rw [show |((b-u)/2 : ℝ)| = |b-u|/2 by rw [abs_div]; norm_num] at h
      exact h
    have h2 : ‖∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n‖ ≤ Real.log (2 + |b-u|/2) + 7 :=
      le_trans (norm_sum_le _ _) (le_trans (hsum.sum_le_tsum _ (fun n _ => norm_nonneg _)) hb1)
    calc ‖(-(Real.eulerMascheroniConstant:ℂ)) + ∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n‖
        ≤ ‖(-(Real.eulerMascheroniConstant:ℂ))‖ + ‖∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n‖ := norm_add_le _ _
      _ ≤ ‖(Real.eulerMascheroniConstant:ℂ)‖ + (Real.log (2 + |b-u|/2) + 7) := by rw [norm_neg]; linarith
  have hDint : Integrable (fun u : ℝ => (Real.log (2 + |b - u|/2) + 7 + ‖(Real.eulerMascheroniConstant : ℂ)‖ + ∑ j ∈ Finset.range m, (x' + (j:ℝ))⁻¹) * ‖gK a lam u‖) (volume : Measure ℝ) := by
    have h1 : (fun u : ℝ => (Real.log (2 + |b - u|/2) + 7 + ‖(Real.eulerMascheroniConstant : ℂ)‖ + ∑ j ∈ Finset.range m, (x' + (j:ℝ))⁻¹) * ‖gK a lam u‖)
        = fun u : ℝ => (Real.log (2 + |b - u|/2) + 7) * ‖gK a lam u‖ + (‖(Real.eulerMascheroniConstant : ℂ)‖ + ∑ j ∈ Finset.range m, (x' + (j:ℝ))⁻¹) * ‖gK a lam u‖ := by
      funext u; ring
    rw [h1]
    exact (integrable_log_gK a lam b ha).add ((integrable_gK_norm a lam ha).const_mul _)
  have hFmeas : ∀ N : ℕ, AEStronglyMeasurable (fun u : ℝ => (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n + ∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹) * gK a lam u) (volume : Measure ℝ) := by
    intro N
    exact (((hcont1 N).add (continuous_finset_sum _ (fun j _ => hcontj j))).mul (continuous_gK a lam ha)).aestronglyMeasurable
  have hbndF : ∀ (N : ℕ) (u : ℝ), ‖(-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n + ∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹) * gK a lam u‖
      ≤ (Real.log (2 + |b - u|/2) + 7 + ‖(Real.eulerMascheroniConstant : ℂ)‖ + ∑ j ∈ Finset.range m, (x' + (j:ℝ))⁻¹) * ‖gK a lam u‖ := by
    intro N u
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc ‖(-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) + ∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹‖
        ≤ ‖(-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n)‖ + ‖∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹‖ := norm_add_le _ _
      _ ≤ (‖(Real.eulerMascheroniConstant:ℂ)‖ + (Real.log (2 + |b-u|/2) + 7)) + ∑ j ∈ Finset.range m, (x' + (j:ℝ))⁻¹ := add_le_add (hb2 N u) (hCnn u)
      _ = Real.log (2 + |b-u|/2) + 7 + ‖(Real.eulerMascheroniConstant:ℂ)‖ + ∑ j ∈ Finset.range m, (x' + (j:ℝ))⁻¹ := by ring
  have hlimF : ∀ᵐ u : ℝ ∂volume, Tendsto (fun N : ℕ => (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n + ∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹) * gK a lam u) atTop
      (nhds (Complex.digamma ((x:ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) * gK a lam u)) := by
    filter_upwards with u
    have hsum : Summable (fun n : ℕ => Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) := by
      refine Summable.of_norm ?_
      simpa using Commons.Analysis.SpecialFunctions.Gamma.summable_dgTerm_norm ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) (by rw [re_wfun]; exact hx'1)
    have hs : HasSum (fun n : ℕ => Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n)
        (Complex.digamma ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (Real.eulerMascheroniConstant:ℂ)) := by
      rw [hsum.hasSum_iff_tendsto_nat]
      have hthis := Commons.Analysis.SpecialFunctions.Gamma.digamma_eq_euler_sub_tsum ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) (by rw [re_wfun]; exact hx'1)
      rw [hthis]
      rw [show (-(Real.eulerMascheroniConstant:ℂ) + ∑' n : ℕ, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) + (Real.eulerMascheroniConstant:ℂ) = ∑' n : ℕ, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n by ring]
      exact hsum.hasSum.tendsto_sum_nat
    have ht' := hs.tendsto_sum_nat.const_add (-(Real.eulerMascheroniConstant:ℂ))
    have ht'' : Tendsto (fun N : ℕ => -(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) atTop (nhds (Complex.digamma ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I))) := by
      rw [add_comm (Complex.digamma _)] at ht'
      simpa using ht'
    have ht2 := (ht''.add_const (∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹)).mul_const (gK a lam u)
    have hlim2 : (Complex.digamma ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + ∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹) = Complex.digamma ((x:ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) := (hpw u).symm
    rwa [hlim2] at ht2
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure ℝ))
    (F := fun (N : ℕ) (u : ℝ) => (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n + ∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹) * gK a lam u)
    (f := fun u : ℝ => Complex.digamma ((x:ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) * gK a lam u)
    (fun u : ℝ => (Real.log (2 + |b - u|/2) + 7 + ‖(Real.eulerMascheroniConstant : ℂ)‖ + ∑ j ∈ Finset.range m, (x' + (j:ℝ))⁻¹) * ‖gK a lam u‖)
    hFmeas hDint (fun N => Filter.Eventually.of_forall (fun u => hbndF N u)) hlimF
  have hbndA : ∀ (M : ℕ) (u : ℝ), ‖(-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u‖ ≤ (Real.log (2 + |b - u|/2) + 7 + ‖(Real.eulerMascheroniConstant : ℂ)‖) * ‖gK a lam u‖ := by
    intro M u
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have h := hb2 M u
    linarith [h]
  have hAFint : ∀ M : ℕ, Integrable (fun u : ℝ => (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range M, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u) (volume : Measure ℝ) :=
    fun M => (integrable_bound_gK a lam b ha).mono' (((hcont1 M).mul (continuous_gK a lam ha)).aestronglyMeasurable) (Filter.Eventually.of_forall (hbndA M))
  have hBint : Integrable (fun u : ℝ => (∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹) * gK a lam u) (volume : Measure ℝ) := by
    refine ((integrable_gK_norm a lam ha).const_mul (∑ j ∈ Finset.range m, (x' + (j:ℝ))⁻¹)).mono' ?_ ?_
    · exact ((continuous_finset_sum _ (fun j _ => hcontj j)).mul (continuous_gK a lam ha)).aestronglyMeasurable
    · filter_upwards with u
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hCnn u) (norm_nonneg _)
  have hsplit : ∀ N : ℕ, (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n + ∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹) * gK a lam u)
      = (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u) + (∫ u : ℝ, (∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹) * gK a lam u) := by
    intro N
    rw [show (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n + ∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹) * gK a lam u)
        = ∫ u : ℝ, ((-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u + (∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹) * gK a lam u) from by
        apply integral_congr_ae; filter_upwards with u; ring]
    exact MeasureTheory.integral_add (hAFint N) hBint
  have hBval : (∫ u : ℝ, (∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹) * gK a lam u)
      = ∑ j ∈ Finset.range m, 4 * Real.pi * psiT a lam x' b j := by
    have hcong : (∫ u : ℝ, (∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹) * gK a lam u)
        = ∫ u : ℝ, ∑ j ∈ Finset.range m, ((((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹ * gK a lam u) := by
      apply integral_congr_ae; filter_upwards with u
      rw [Finset.sum_mul]
    rw [hcong]
    rw [MeasureTheory.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      exact psi_inv_shift_val a lam x' b ha hlam j (hjm j)
    · intro j hj
      exact psi_inv_shift_int a lam x' b ha j (hjm j)
  have hconvB : Tendsto (fun N : ℕ => -∑ n ∈ Finset.range N, 4 * Real.pi * psiT a lam x' b n + ∑ j ∈ Finset.range m, 4 * Real.pi * psiT a lam x' b j) atTop
      (nhds (-4 * Real.pi * ∑' n : ℕ, psiT a lam x' b n + ∑ j ∈ Finset.range m, 4 * Real.pi * psiT a lam x' b j)) := by
    have hsumT := psiT_summable a lam x' b ha hlam hx'1
    have h1 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, psiT a lam x' b n) atTop (nhds (∑' n : ℕ, psiT a lam x' b n)) := hsumT.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun N : ℕ => -∑ n ∈ Finset.range N, 4 * Real.pi * psiT a lam x' b n) atTop (nhds (-4 * Real.pi * ∑' n : ℕ, psiT a lam x' b n)) := by
      have hm : (fun N : ℕ => -∑ n ∈ Finset.range N, 4 * Real.pi * psiT a lam x' b n) = fun N : ℕ => -((4 * Real.pi) * ∑ n ∈ Finset.range N, psiT a lam x' b n) := by
        funext N; rw [Finset.mul_sum]
      rw [hm]
      have h3 := (h1.const_mul ((4:ℂ) * Real.pi)).neg
      have h4 : (-((4 * Real.pi) * ∑' n : ℕ, psiT a lam x' b n)) = -4 * Real.pi * ∑' n : ℕ, psiT a lam x' b n := by ring
      rw [h4] at h3
      exact h3
    exact h2.add_const _
  have hconvA : Tendsto (fun N : ℕ => -∑ n ∈ Finset.range N, 4 * Real.pi * psiT a lam x' b n + ∑ j ∈ Finset.range m, 4 * Real.pi * psiT a lam x' b j) atTop
      (nhds (∫ u : ℝ, Complex.digamma ((x:ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) * gK a lam u)) := by
    have hmain : Tendsto (fun N : ℕ => (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u) + (∫ u : ℝ, (∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹) * gK a lam u)) atTop
        (nhds (∫ u : ℝ, Complex.digamma ((x:ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) * gK a lam u)) :=
      hDCT.congr' (Filter.Eventually.of_forall (fun N => (hsplit N)))
    have hgoal : (fun N : ℕ => (∫ u : ℝ, (-(Real.eulerMascheroniConstant:ℂ) + ∑ n ∈ Finset.range N, Commons.Analysis.SpecialFunctions.Gamma.dgTermC ((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) n) * gK a lam u) + (∫ u : ℝ, (∑ j ∈ Finset.range m, (((x':ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) + (j:ℂ))⁻¹) * gK a lam u))
        = fun N : ℕ => -∑ n ∈ Finset.range N, 4 * Real.pi * psiT a lam x' b n + ∑ j ∈ Finset.range m, 4 * Real.pi * psiT a lam x' b j := by
      funext N
      rw [psi_hFN a lam x' b ha hlam hx'1 hx'8 N, hBval]
      simp only [psiT]
    rwa [hgoal] at hmain
  have key1 : (∫ u : ℝ, Complex.digamma ((x:ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) * gK a lam u)
      = -4 * Real.pi * ∑' n : ℕ, psiT a lam x' b n + ∑ j ∈ Finset.range m, 4 * Real.pi * psiT a lam x' b j :=
    tendsto_nhds_unique hconvA hconvB
  have hS : (∑ j ∈ Finset.range m, 4 * Real.pi * psiT a lam x' b j) = 4 * Real.pi * ∑ j ∈ Finset.range m, psiT a lam x' b j := by
    rw [Finset.mul_sum]
  have hidx := Summable.sum_add_tsum_nat_add m (psiT_summable a lam x' b ha hlam hx'1)
  have hshift : (∑' i : ℕ, psiT a lam x' b (i + m)) = ∑' i : ℕ, psiT a lam x b i :=
    tsum_congr (fun i => psiT_index a lam b x x' m hxm i)
  calc (∫ u : ℝ, Complex.digamma ((x:ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) * gK a lam u)
      = -4 * Real.pi * ∑' i : ℕ, psiT a lam x' b (i + m) := by
        rw [key1, ← hidx, hS]
        ring
    _ = -4 * Real.pi * ∑' i : ℕ, psiT a lam x b i := by rw [hshift]


end PsiKernelBound

namespace Commons.Analysis.SpecialFunctions.Gamma

open MeasureTheory Set Complex Filter
open scoped Topology Interval BigOperators
open PsiKernelBound

theorem psi_kernel_bound (a lam x b : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hx : (1:ℝ)/4 ≤ x) :
    ‖∫ u : ℝ, Complex.digamma ((x : ℂ) + (((b - u)/2 : ℝ) : ℂ) * Complex.I) *
      ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
        (((a : ℂ) + (u : ℂ) * Complex.I)^2))‖ ≤ 200 := by
  have hz : (∫ u : ℝ, Complex.digamma ((x : ℂ) + (((b - u)/2 : ℝ) : ℂ) * Complex.I) *
      ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * (lam : ℂ))) - 1) /
        (((a : ℂ) + (u : ℂ) * Complex.I)^2)))
      = ∫ u : ℝ, Complex.digamma ((x:ℂ) + (((b-u)/2:ℝ):ℂ)*Complex.I) * gK a lam u := by
    apply integral_congr_ae
    filter_upwards with u
    unfold gK
    ring
  rw [hz, interchange_gen a lam x b ha hlam hx]
  have hsumm : Summable (fun n : ℕ => psiT a lam x b n) := psiT_summable a lam x b ha hlam hx
  have hnorm1 : ‖∑' n : ℕ, psiT a lam x b n‖ ≤ ∑' n : ℕ, ‖psiT a lam x b n‖ :=
    norm_tsum_le_tsum_norm hsumm.norm
  have hnorm2 : (∑' n : ℕ, ‖psiT a lam x b n‖) ≤ ∑' n : ℕ, (8:ℝ)/((n:ℝ)+1)^2 :=
    hsumm.norm.tsum_le_tsum (fun n => psiT_bound a lam x b ha hlam hx n) psi_summable_eight
  have h8 : (∑' n : ℕ, (8:ℝ)/((n:ℝ)+1)^2) = 8 * (Real.pi^2/6) := by
    have hs : HasSum (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^2) (Real.pi^2/6) := by
      have h0 : (∑ i ∈ Finset.range 1, (1:ℝ)/(i:ℝ)^2) = 0 := by simp
      have h := (hasSum_nat_add_iff (f := fun n : ℕ => (1:ℝ)/(n:ℝ)^2) 1).mpr (by simpa [h0] using hasSum_zeta_two)
      simpa using h
    have h1 : (∑' n : ℕ, (8:ℝ)/((n:ℝ)+1)^2) = 8 * ∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^2 := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n; ring
    rw [h1, hs.tsum_eq]
  have hfinal : ‖∑' n : ℕ, psiT a lam x b n‖ ≤ 8 * (Real.pi^2/6) := by
    rw [h8] at hnorm2
    linarith
  have hpi3 : Real.pi^3 < 37.5 := by
    have h1 : Real.pi^2 < 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    nlinarith [h1, Real.pi_pos, Real.pi_lt_d2]
  have hc1 : ‖((-4:ℂ))‖ = 4 := by
    have h2 : ‖((-4:ℂ))‖^2 = 16 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; norm_num
    nlinarith [h2, norm_nonneg ((-4:ℂ))]
  have hc2 : ‖((Real.pi:ℝ):ℂ)‖ = Real.pi := by
    have h2 : ‖((Real.pi:ℝ):ℂ)‖^2 = Real.pi^2 := by
      rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
    nlinarith [h2, norm_nonneg ((Real.pi:ℝ):ℂ), Real.pi_pos]
  calc ‖-4 * Real.pi * ∑' n : ℕ, psiT a lam x b n‖
      = 4 * Real.pi * ‖∑' n : ℕ, psiT a lam x b n‖ := by
        rw [norm_mul, norm_mul, hc1, hc2]
    _ ≤ 4 * Real.pi * (8 * (Real.pi^2/6)) := by
        apply mul_le_mul_of_nonneg_left hfinal
        positivity
    _ = 16/3 * Real.pi^3 := by ring
    _ ≤ 200 := by nlinarith [hpi3]

end Commons.Analysis.SpecialFunctions.Gamma

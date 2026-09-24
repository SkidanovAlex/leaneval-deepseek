import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.conv_l2_contraction
import Submission.Work.GM.Affine.norm_Fhat_conv_le

/-!
# Elementary properties of the smoothing `f̃ = T ψ(T·) * f` (GM §9)

The smoothing kernel `φ(x) = T ψ(T x)` (where `ψ ≥ 0`, `∫ ψ = 1`, `ψ` supported in `[-1,1]`) is a
nonnegative approximate identity of total mass `1`.  Consequently `smoothed ψ T f = φ * f` has all
the properties recorded below: it is continuous, nonnegative, compactly supported, supported in
`[1/(2C₀), 2C₀]` whenever `f` is supported in `[1/C₀,C₀]` and `2C₀ ≤ T`, it preserves the integral,
contracts the `L²` norm and the Fourier transform, and is bounded by `supf f`.

The `L²` contraction and the Fourier bound are proved in the companion files
`conv_l2_contraction.lean` and `norm_Fhat_conv_le.lean`; everything else is proved here.
-/

open MeasureTheory

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

theorem smoothed_properties {ψ f : ℝ → ℝ} {C₀ T : ℝ} (hψc : Continuous ψ)
    (hψnn : ∀ x, 0 ≤ ψ x) (hψcs : HasCompactSupport ψ) (hψ1 : ∫ x, ψ x = 1)
    (hψs : ∀ x, 1 ≤ |x| → ψ x = 0) (hC₀ : 1 ≤ C₀) (hf : Continuous f)
    (hfn : ∀ u, 0 ≤ f u) (hfs : SuppHyp C₀ f) (hT : 2 * C₀ ≤ T) :
    Continuous (smoothed ψ T f) ∧ (∀ u, 0 ≤ smoothed ψ T f u) ∧
    HasCompactSupport (smoothed ψ T f) ∧ SuppHyp (2 * C₀) (smoothed ψ T f) ∧
    (∫ u, smoothed ψ T f u = ∫ u, f u) ∧
    (∫ u, (smoothed ψ T f u) ^ 2 ≤ ∫ u, (f u) ^ 2) ∧
    (∀ u, smoothed ψ T f u ≤ supf f) ∧
    (∀ ξ : ℝ, ‖Fhat (smoothed ψ T f) ξ‖ ≤ ‖Fhat f ξ‖) := by
  set φ : ℝ → ℝ := fun x => T * ψ (T * x) with hφdef
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have h2C₀pos : 0 < 2 * C₀ := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le h2C₀pos hT
  have hpos2 : (0:ℝ) < 1/(2*C₀) := one_div_pos.mpr h2C₀pos
  have hposT : (0:ℝ) < 1/T := one_div_pos.mpr hTpos
  have hφnn : ∀ x, 0 ≤ φ x := fun x => mul_nonneg hTpos.le (hψnn _)
  have hφc : Continuous φ := by rw [hφdef]; fun_prop
  have hφsup : Function.support φ ⊆ Set.Icc (-(1/T)) (1/T) := by
    intro x hx
    have hx' : ψ (T * x) ≠ 0 := by
      intro h; apply hx; rw [hφdef]; simp [h]
    have h2 : ¬ (1 ≤ |T * x|) := fun hle => hx' (hψs _ hle)
    have h3 : |T * x| < 1 := not_le.mp h2
    rw [abs_mul, abs_of_pos hTpos] at h3
    have h4 : |x| < 1 / T := by
      rw [lt_div_iff₀ hTpos, mul_comm]; exact h3
    exact abs_le.mp h4.le
  have hφcs : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(1/T)) (1/T)) isCompact_Icc hφsup
  have hφ1 : ∫ x, φ x = 1 := by
    rw [hφdef]
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.Measure.integral_comp_mul_left]
    simp only [hψ1, smul_eq_mul, mul_one, abs_of_pos (inv_pos.mpr hTpos),
      mul_inv_cancel₀ hTpos.ne']
  have hφint : Integrable φ := hφc.integrable_of_hasCompactSupport hφcs
  have hf_cs : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1/C₀) C₀) isCompact_Icc
      (fun u hu => hfs u hu)
  have hf_int : Integrable f := hf.integrable_of_hasCompactSupport hf_cs
  have hf2_cs : HasCompactSupport (fun u => (f u)^2) :=
    HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1/C₀) C₀) isCompact_Icc
      (fun u hu => hfs u (by intro h; exact hu (by simp [h])))
  have hfi2 : Integrable (fun u => (f u)^2) := (hf.pow 2).integrable_of_hasCompactSupport hf2_cs
  have hφeq : ∀ u, smoothed ψ T f u
      = MeasureTheory.convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume u := by
    intro u
    rw [smoothed, MeasureTheory.convolution_lsmul_swap]
    simp only [smul_eq_mul, hφdef]
    rw [show (∫ t, (T * ψ (T * (u - t))) * f t) = T * ∫ t, ψ (T * (u - t)) * f t by
          rw [← MeasureTheory.integral_const_mul]
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t; ring]
  have hkey1 : (1:ℝ)/T ≤ 1/(2*C₀) := one_div_le_one_div_of_le h2C₀pos hT
  have hSupp : SuppHyp (2 * C₀) (smoothed ψ T f) := by
    intro u hu
    by_contra hmem
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
    rcases hmem with h1 | h2
    · apply hu
      rw [smoothed]
      have hptw : ∀ u', ψ (T * (u - u')) * f u' = 0 := by
        intro u'
        by_cases hfu : f u' = 0
        · rw [hfu, mul_zero]
        · obtain ⟨ha, hb⟩ := hfs u' hfu
          have heq : (1:ℝ)/C₀ - 1/(2*C₀) = 1/(2*C₀) := by field_simp; ring
          have hnum : (1:ℝ)/(2*C₀) ≤ u' - u := by linarith
          have hge : (1:ℝ)/T ≤ u' - u := le_trans hkey1 hnum
          have hbig : (1:ℝ) ≤ |T * (u - u')| := by
            have hneg : u - u' < 0 := by linarith
            rw [abs_mul, abs_of_pos hTpos, abs_of_neg hneg, neg_sub]
            have hmul : T * (1/T) ≤ T * (u' - u) := mul_le_mul_of_nonneg_left hge hTpos.le
            rwa [mul_one_div, div_self hTpos.ne'] at hmul
          rw [hψs _ hbig, zero_mul]
      have hzero : ∫ u', ψ (T * (u - u')) * f u' = 0 := by
        simp only [hptw, MeasureTheory.integral_zero]
      rw [hzero, mul_zero]
    · apply hu
      rw [smoothed]
      have hptw : ∀ u', ψ (T * (u - u')) * f u' = 0 := by
        intro u'
        by_cases hfu : f u' = 0
        · rw [hfu, mul_zero]
        · obtain ⟨ha, hb⟩ := hfs u' hfu
          have hTge1 : (1:ℝ) ≤ T := by linarith
          have hge1 : (1:ℝ)/T ≤ 1 := by
            simpa using one_div_le_one_div_of_le (zero_lt_one) hTge1
          have hnum : (1:ℝ) ≤ u - u' := by linarith
          have hge : (1:ℝ)/T ≤ u - u' := le_trans hge1 hnum
          have hbig : (1:ℝ) ≤ |T * (u - u')| := by
            have hpos : 0 < u - u' := by linarith
            rw [abs_mul, abs_of_pos hTpos, abs_of_pos hpos]
            have hmul : T * (1/T) ≤ T * (u - u') := mul_le_mul_of_nonneg_left hge hTpos.le
            rwa [mul_one_div, div_self hTpos.ne'] at hmul
          rw [hψs _ hbig, zero_mul]
      have hzero : ∫ u', ψ (T * (u - u')) * f u' = 0 := by
        simp only [hptw, MeasureTheory.integral_zero]
      rw [hzero, mul_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcont : Continuous (MeasureTheory.convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) :=
      hf_cs.continuous_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hφc.locallyIntegrable hf
    exact hcont.congr (fun u => (hφeq u).symm)
  · intro u
    rw [hφeq u, MeasureTheory.convolution_lsmul_swap]
    simp only [smul_eq_mul]
    exact MeasureTheory.integral_nonneg (fun t => mul_nonneg (hφnn _) (hfn _))
  · exact HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1/(2*C₀)) (2*C₀)) isCompact_Icc
      (fun u hu => hSupp u hu)
  · exact hSupp
  · have hconvint := MeasureTheory.integral_convolution (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
        (ContinuousLinearMap.lsmul ℝ ℝ) (f := φ) (g := f) hφint hf_int
    rw [show (∫ u, smoothed ψ T f u)
          = ∫ u, MeasureTheory.convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume u by
          apply MeasureTheory.integral_congr_ae; filter_upwards with u; exact hφeq u]
    rw [hconvint]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, hφ1, one_mul]
  · simpa only [hφeq] using conv_l2_contraction hφnn hφc hφcs hφ1 hfn hf_int hfi2
  · intro u
    rw [hφeq u]
    have hex : ConvolutionExistsAt φ (fun _ : ℝ => supf f) u (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume := by
      simpa only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
        hφint.mul_const (supf f)
    calc MeasureTheory.convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume u
        ≤ MeasureTheory.convolution φ (fun _ : ℝ => supf f) (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume u :=
          MeasureTheory.convolution_mono_right_of_nonneg hex hφnn (fun x => le_supf hf hf_cs x)
            (fun _ => supf_nonneg hf hf_cs hfn)
      _ = supf f := by
          rw [MeasureTheory.convolution_lsmul]
          simp only [smul_eq_mul]
          rw [MeasureTheory.integral_mul_const, hφ1, one_mul]
  · intro ξ
    have hfun : smoothed ψ T f
        = MeasureTheory.convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume := funext hφeq
    rw [hfun]
    exact norm_Fhat_conv_le hφnn hφc hφcs hφ1 hf hf_int ξ

end

end Work.GM.Affine

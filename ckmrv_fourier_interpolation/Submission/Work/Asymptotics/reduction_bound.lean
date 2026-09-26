import Mathlib
import Submission.Work.Asymptotics.PropagateBounds.Defs

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups
open Work.Kernels

set_option maxHeartbeats 4000000

/-- The Frobenius norm is invariant under inversion in `SL(2,ℤ)`. -/
private lemma Frob_inv' (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Frob γ⁻¹ = Frob γ := by
  unfold Frob
  rw [Matrix.SpecialLinearGroup.coe_inv]
  have hadj : (Matrix.adjugate (γ : Matrix (Fin 2) (Fin 2) ℤ)) =
      !![γ 1 1, -(γ 0 1); -(γ 1 0), γ 0 0] := by
    rw [Matrix.adjugate_fin_two]
  rw [hadj]
  congr 1
  simp
  ring

/-- **The quantitative core of the reduction.**  Any `g ∈ SL(2,ℤ)` that moves `τ` into the
closed fundamental domain `𝒟` has Frobenius norm and produces a point of polynomially bounded
scale, both controlled by `(1 + scale τ)⁴`. -/
private lemma reduction_core (τ : ℍ) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hg : g • τ ∈ ModularGroup.fd) :
    Frob g ≤ 12 * (1 + Work.Kernels.scale τ)^4 ∧
    Work.Kernels.scale (g • τ) ≤ 12 * (1 + Work.Kernels.scale τ)^4 := by
  set M : ℝ := 1 + Work.Kernels.scale τ with hMdef
  have hM1 : 1 ≤ M := by rw [hMdef]; linarith [Work.Kernels.one_le_scale τ]
  have hy0 : 0 < τ.im := τ.im_pos
  have hy_le : τ.im ≤ M := by
    have h1 : τ.im ≤ ‖(τ:ℂ)‖ := Work.Kernels.im_le_coe_norm τ
    have h2 : ‖(τ:ℂ)‖ ≤ M := by rw [hMdef]; linarith [Work.Kernels.coe_norm_le_scale τ]
    linarith
  have hinvy_le : (τ.im)⁻¹ ≤ M := by
    rw [hMdef]; linarith [Work.Kernels.inv_im_le_scale τ]
  have hMy : 1 ≤ M * τ.im := by
    have := mul_le_mul_of_nonneg_right hinvy_le hy0.le
    rwa [inv_mul_cancel₀ hy0.ne'] at this
  have hx_le : |τ.re| ≤ M := by
    have h1 : |τ.re| ≤ ‖(τ:ℂ)‖ := by
      simpa [UpperHalfPlane.coe_re] using Complex.abs_re_le_norm (τ:ℂ)
    have h2 : ‖(τ:ℂ)‖ ≤ M := by rw [hMdef]; linarith [Work.Kernels.coe_norm_le_scale τ]
    linarith
  set z : ℍ := g • τ with hzdef
  have hg' : z ∈ ModularGroup.fd := by rw [hzdef]; exact hg
  have hzre : |z.re| ≤ 1/2 := hg'.2
  set q : ℝ := Complex.normSq (UpperHalfPlane.denom (g : GL (Fin 2) ℝ) (τ : ℂ)) with hqdef
  have hqpos : 0 < q := by
    rw [hqdef]
    exact UpperHalfPlane.normSq_denom_pos _ (by simpa [UpperHalfPlane.coe_im] using τ.im_ne_zero)
  have him : z.im = τ.im / q := by rw [hzdef, hqdef, ModularGroup.im_smul_eq_div_normSq]
  have hzim_half : (1:ℝ)/2 ≤ z.im := by
    have h3 : 3 ≤ 4 * z.im^2 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg'
    nlinarith [z.im_pos]
  have hq_eq : q = τ.im / z.im := by
    rw [eq_div_iff z.im_ne_zero, him]
    field_simp
  have hq_le : q ≤ 2 * τ.im := by
    rw [hq_eq, div_le_iff₀ z.im_pos]
    nlinarith [hzim_half, hy0]
  have hzim_le : z.im ≤ M := by
    rcases eq_or_ne (g 1 0) 0 with hc0 | hc0
    · have hd : g 1 1 = 1 ∨ g 1 1 = -1 := by
        have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
          have h := g.property; rwa [Matrix.det_fin_two] at h
        rw [hc0, mul_zero, sub_zero] at hdet
        exact Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact hdet)
      have hq1 : q = 1 := by
        have hden : UpperHalfPlane.denom (g : GL (Fin 2) ℝ) (τ:ℂ)
            = ((g 1 1 : ℤ) : ℂ) := by
          rw [ModularGroup.denom_apply, hc0]; simp
        rw [hqdef, hden]
        rcases hd with h | h <;> simp [h]
      rw [him, hq1, div_one]
      exact hy_le
    · have hc2 : (1:ℝ) ≤ ((g 1 0 : ℤ):ℝ)^2 := by
        have h : (1:ℤ) ≤ (g 1 0)^2 := by nlinarith [sq_pos_of_ne_zero hc0]
        exact_mod_cast h
      have hcy : ((g 1 0 : ℤ):ℝ)^2 * τ.im^2 ≤ q := by
        rw [hqdef]
        have h := UpperHalfPlane.c_mul_im_sq_le_normSq_denom (g : GL (Fin 2) ℝ) τ
        rw [show ((g : GL (Fin 2) ℝ) 1 0) = ((g 1 0 : ℤ) : ℝ) from rfl] at h
        calc ((g 1 0 : ℤ) : ℝ)^2 * τ.im^2 = (((g 1 0 : ℤ) : ℝ) * τ.im)^2 := by ring
          _ ≤ _ := h
      have hy2 : τ.im^2 ≤ q := by nlinarith [hcy, hc2, hy0]
      rw [him, div_le_iff₀ hqpos]
      nlinarith [hy2, hMy, hy0]
  -- the numerator and denominator of the Möbius transformation
  have hden_eq : UpperHalfPlane.denom (g : GL (Fin 2) ℝ) (τ : ℂ)
      = ((g 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((g 1 1 : ℤ) : ℂ) := by
    rw [ModularGroup.denom_apply]
  have hnum_eq : UpperHalfPlane.num (g : GL (Fin 2) ℝ) (τ : ℂ)
      = ((g 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((g 0 1 : ℤ) : ℂ) := by
    unfold UpperHalfPlane.num
    rw [show ((g : GL (Fin 2) ℝ) 0 0) = ((g 0 0 : ℤ) : ℝ) from rfl,
        show ((g : GL (Fin 2) ℝ) 0 1) = ((g 0 1 : ℤ) : ℝ) from rfl]
    push_cast; ring
  have hmul : UpperHalfPlane.num (g : GL (Fin 2) ℝ) (τ : ℂ)
      = (z : ℂ) * UpperHalfPlane.denom (g : GL (Fin 2) ℝ) (τ : ℂ) := by
    have hw : (z : ℂ) = UpperHalfPlane.num (g : GL (Fin 2) ℝ) (τ : ℂ) /
        UpperHalfPlane.denom (g : GL (Fin 2) ℝ) (τ : ℂ) := by
      rw [hzdef, ModularGroup.sl_moeb]
      rw [UpperHalfPlane.coe_smul_of_det_pos
        (show (0:ℝ) < (g : GL (Fin 2) ℝ).det.val from by simp)]
    have hdenne : UpperHalfPlane.denom (g : GL (Fin 2) ℝ) (τ : ℂ) ≠ 0 :=
      UpperHalfPlane.denom_ne_zero _ τ
    rw [eq_div_iff hdenne] at hw
    exact hw.symm
  have hznormSq_le : Complex.normSq (z:ℂ) ≤ 1/4 + M^2 := by
    rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    have h1 : z.re * z.re ≤ (1/2)^2 := by nlinarith [abs_le.mp hzre]
    have h2 : z.im * z.im ≤ M^2 := by nlinarith [hzim_le, z.im_pos]
    linarith
  have hnum_normSq : Complex.normSq (UpperHalfPlane.num (g : GL (Fin 2) ℝ) (τ : ℂ))
      = Complex.normSq (z:ℂ) * q := by
    rw [hmul, Complex.normSq_mul, hqdef]
  have hnum_le : Complex.normSq (UpperHalfPlane.num (g : GL (Fin 2) ℝ) (τ : ℂ)) ≤ 3*M^3 := by
    rw [hnum_normSq]
    nlinarith [hznormSq_le, hq_le, hM1, hy_le, hy0]
  -- bound on the (0,0) entry
  have him_num : (UpperHalfPlane.num (g : GL (Fin 2) ℝ) (τ : ℂ)).im
      = ((g 0 0 : ℤ):ℝ) * τ.im := by
    rw [hnum_eq]
    simp [Complex.add_im, Complex.mul_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  have ha2y2 : (((g 0 0 : ℤ):ℝ) * τ.im)^2
      ≤ Complex.normSq (UpperHalfPlane.num (g : GL (Fin 2) ℝ) (τ : ℂ)) := by
    rw [← him_num, Complex.normSq_apply]
    nlinarith [sq_nonneg (UpperHalfPlane.num (g : GL (Fin 2) ℝ) (τ : ℂ)).re]
  have ha2 : ((g 0 0 : ℤ):ℝ)^2 ≤ 3*M^5 := by
    have hMy2 : 1 ≤ (M*τ.im)^2 := by nlinarith [hMy]
    calc ((g 0 0 : ℤ):ℝ)^2 = ((g 0 0 : ℤ):ℝ)^2 * 1 := by ring
      _ ≤ ((g 0 0 : ℤ):ℝ)^2 * (M*τ.im)^2 := by
          apply mul_le_mul_of_nonneg_left hMy2 (by positivity)
      _ = (((g 0 0 : ℤ):ℝ) * τ.im)^2 * M^2 := by ring
      _ ≤ (3*M^3) * M^2 := by
          apply mul_le_mul_of_nonneg_right (le_trans ha2y2 hnum_le) (by positivity)
      _ = 3*M^5 := by ring
  -- bound on the (0,1) entry
  have hre_num : (UpperHalfPlane.num (g : GL (Fin 2) ℝ) (τ : ℂ)).re
      = ((g 0 0 : ℤ):ℝ) * τ.re + ((g 0 1 : ℤ):ℝ) := by
    rw [hnum_eq]
    simp [Complex.add_re, Complex.mul_re, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  have hb2 : ((g 0 1 : ℤ):ℝ)^2 ≤ 12*M^7 := by
    have hb_eq : ((g 0 1 : ℤ):ℝ)
        = (UpperHalfPlane.num (g : GL (Fin 2) ℝ) (τ : ℂ)).re - ((g 0 0 : ℤ):ℝ) * τ.re := by
      rw [hre_num]; ring
    have hrn : ((UpperHalfPlane.num (g : GL (Fin 2) ℝ) (τ : ℂ)).re)^2
        ≤ Complex.normSq (UpperHalfPlane.num (g : GL (Fin 2) ℝ) (τ : ℂ)) := by
      rw [Complex.normSq_apply]
      nlinarith [sq_nonneg (UpperHalfPlane.num (g : GL (Fin 2) ℝ) (τ : ℂ)).im]
    have hx2 : τ.re^2 ≤ M^2 := by nlinarith [abs_le.mp hx_le]
    have h1 : ((g 0 0 : ℤ):ℝ)^2 * τ.re^2 ≤ 3*M^5 * M^2 :=
      mul_le_mul ha2 hx2 (sq_nonneg _) (by positivity)
    have hM3 : M^3 ≤ M^7 := pow_le_pow_right₀ hM1 (by norm_num)
    rw [hb_eq]
    nlinarith [sq_nonneg ((UpperHalfPlane.num (g : GL (Fin 2) ℝ) (τ : ℂ)).re
        + ((g 0 0 : ℤ):ℝ) * τ.re),
      sq_nonneg (UpperHalfPlane.num (g : GL (Fin 2) ℝ) (τ : ℂ)).re, hrn, hnum_le, h1, hM3]
  -- bound on the (1,0) entry
  have hc2n : ((g 1 0 : ℤ):ℝ)^2 ≤ 2*M := by
    have hcy : ((g 1 0 : ℤ):ℝ)^2 * τ.im^2 ≤ q := by
      rw [hqdef]
      have h := UpperHalfPlane.c_mul_im_sq_le_normSq_denom (g : GL (Fin 2) ℝ) τ
      rw [show ((g : GL (Fin 2) ℝ) 1 0) = ((g 1 0 : ℤ) : ℝ) from rfl] at h
      calc ((g 1 0 : ℤ) : ℝ)^2 * τ.im^2 = (((g 1 0 : ℤ) : ℝ) * τ.im)^2 := by ring
        _ ≤ _ := h
    have h1 : ((g 1 0 : ℤ):ℝ)^2 * τ.im ≤ 2 := by
      have h' : (((g 1 0 : ℤ):ℝ)^2 * τ.im) * τ.im ≤ 2 * τ.im := by
        nlinarith [hcy, hq_le]
      exact (mul_le_mul_iff_of_pos_right hy0).mp h'
    have h2 : ((g 1 0 : ℤ):ℝ)^2 * τ.im * τ.im⁻¹ ≤ 2 * τ.im⁻¹ :=
      mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hy0.le)
    rw [mul_assoc, mul_inv_cancel₀ hy0.ne', mul_one] at h2
    nlinarith [h2, hinvy_le, hM1]
  -- bound on the (1,1) entry
  have hre_den : (UpperHalfPlane.denom (g : GL (Fin 2) ℝ) (τ : ℂ)).re
      = ((g 1 0 : ℤ):ℝ) * τ.re + ((g 1 1 : ℤ):ℝ) := by
    rw [hden_eq]
    simp [Complex.add_re, Complex.mul_re, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  have hd2 : ((g 1 1 : ℤ):ℝ)^2 ≤ 8*M^3 := by
    have hd_eq : ((g 1 1 : ℤ):ℝ)
        = (UpperHalfPlane.denom (g : GL (Fin 2) ℝ) (τ : ℂ)).re - ((g 1 0 : ℤ):ℝ) * τ.re := by
      rw [hre_den]; ring
    have hrd : ((UpperHalfPlane.denom (g : GL (Fin 2) ℝ) (τ : ℂ)).re)^2 ≤ q := by
      rw [hqdef, Complex.normSq_apply]
      nlinarith [sq_nonneg (UpperHalfPlane.denom (g : GL (Fin 2) ℝ) (τ : ℂ)).im]
    have hx2 : τ.re^2 ≤ M^2 := by nlinarith [abs_le.mp hx_le]
    have h1 : ((g 1 0 : ℤ):ℝ)^2 * τ.re^2 ≤ 2*M * M^2 :=
      mul_le_mul hc2n hx2 (sq_nonneg _) (by positivity)
    rw [hd_eq]
    nlinarith [sq_nonneg ((UpperHalfPlane.denom (g : GL (Fin 2) ℝ) (τ : ℂ)).re
        + ((g 1 0 : ℤ):ℝ) * τ.re),
      sq_nonneg (UpperHalfPlane.denom (g : GL (Fin 2) ℝ) (τ : ℂ)).re, hrd, hq_le, h1, hM1]
  refine ⟨?_, ?_⟩
  · change Real.sqrt (((g 0 0 : ℤ) : ℝ) ^ 2 + ((g 0 1 : ℤ) : ℝ) ^ 2 +
      ((g 1 0 : ℤ) : ℝ) ^ 2 + ((g 1 1 : ℤ) : ℝ) ^ 2) ≤ 12 * M^4
    have hsum : ((g 0 0 : ℤ) : ℝ) ^ 2 + ((g 0 1 : ℤ) : ℝ) ^ 2 +
        ((g 1 0 : ℤ) : ℝ) ^ 2 + ((g 1 1 : ℤ) : ℝ) ^ 2 ≤ 25 * M^7 := by
      have h3 : M^3 ≤ M^7 := pow_le_pow_right₀ hM1 (by norm_num)
      have h5 : M^5 ≤ M^7 := pow_le_pow_right₀ hM1 (by norm_num)
      have h1 : M ≤ M^7 := le_self_pow₀ hM1 (by norm_num)
      nlinarith [ha2, hb2, hc2n, hd2, h3, h5, h1]
    have hfin : Real.sqrt (25 * M^7) ≤ 12 * M^4 := by
      have h2 : 25 * M^7 ≤ (12 * M^4)^2 := by
        have h8 : M^7 ≤ M^8 := pow_le_pow_right₀ hM1 (by norm_num)
        nlinarith [h8, hM1, pow_nonneg (by linarith : (0:ℝ) ≤ M) 7]
      calc Real.sqrt (25 * M^7) ≤ Real.sqrt ((12 * M^4)^2) := Real.sqrt_le_sqrt h2
        _ = 12 * M^4 := Real.sqrt_sq (by positivity)
    calc Real.sqrt (((g 0 0 : ℤ) : ℝ) ^ 2 + ((g 0 1 : ℤ) : ℝ) ^ 2 +
          ((g 1 0 : ℤ) : ℝ) ^ 2 + ((g 1 1 : ℤ) : ℝ) ^ 2)
        ≤ Real.sqrt (25 * M^7) := Real.sqrt_le_sqrt hsum
      _ ≤ 12 * M^4 := hfin
  · rw [Work.Kernels.scale]
    have h1 : (z.im)⁻¹ ≤ 2 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/2) hzim_half
      rw [one_div] at h
      norm_num at h
      exact h
    have h2 : ‖(z:ℂ)‖ ≤ 2 * M := by
      have h : Complex.normSq (z:ℂ) ≤ (2*M)^2 := by
        rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        nlinarith [abs_le.mp hzre, hzim_le, hM1, z.im_pos]
      have h' := Real.sqrt_le_sqrt h
      rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg (z:ℂ)),
        Real.sqrt_sq (by positivity)] at h'
      exact h'
    have h3 : 3 + 2*M ≤ 12*M^4 := by
      have h4 : M ≤ M^4 := le_self_pow₀ hM1 (by norm_num)
      nlinarith [h4, hM1]
    nlinarith [h1, h2, h3]

/-- **Reduction to the standard fundamental domain with polynomial bounds.**  Every
`τ : UpperHalfPlane` is carried into the closed standard fundamental domain `ModularGroup.fd`
(`{z : 1 ≤ ‖z‖² ∧ |z.re| ≤ 1/2}`) by the *inverse* of a matrix `γ ∈ SL(2,ℤ)` whose Frobenius
norm, and the scale of the resulting point, are polynomially bounded in the scale of `τ`.
This is the reduction-theoretic input of CKMRV Proposition 3.2(2): Mathlib's
`ModularGroup.exists_smul_mem_fd` provides the element, and the paper's inequality
`‖g_z‖_Frob ≤ ‖δ g_z‖_Frob` (for `z` in the keyhole fundamental domain, `δ ∈ SL(2,ℤ)`)
upgrades it to `Frob γ ≤ C (1 + scale τ)^N`. -/
theorem reduction_bound :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      Work.Asymptotics.slSmul γ⁻¹ τ ∈ ModularGroup.fd ∧
      Work.Asymptotics.Frob γ ≤ C * (1 + Work.Kernels.scale τ) ^ N ∧
      Work.Kernels.scale (Work.Asymptotics.slSmul γ⁻¹ τ)
        ≤ C * (1 + Work.Kernels.scale τ) ^ N := by
  refine ⟨12, 4, by norm_num, by norm_num, fun τ => ?_⟩
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  refine ⟨g⁻¹, ?_, ?_, ?_⟩
  · simpa [slSmul] using hg
  · have h := (reduction_core τ g hg).1
    rw [Frob_inv']
    simpa using h
  · have h := (reduction_core τ g hg).2
    simpa [slSmul] using h

end Work.Asymptotics

import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.slash_qtau_twentyfour
import Submission.Work.Asymptotics.divisor_qdiff_lower
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.CKFinal.LineDecay.qParamFun_line_norm_sub

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

noncomputable section

/-! ## Auxiliary geometry -/

/-- `imagAxis` depends only on its value argument. -/
private lemma imagAxis_congr {a b : ℝ} (h : a = b) (ha : 0 < a) (hb : 0 < b) :
    Work.Kernels.imagAxis a ha = Work.Kernels.imagAxis b hb := by
  apply UpperHalfPlane.ext
  simp only [Work.Kernels.imagAxis, UpperHalfPlane.coe_mk]
  rw [h]

/-- `S` acts on the imaginary axis by `i s ↦ i/s`. -/
private lemma S_smul_imagAxis (s : ℝ) (hs : 0 < s) :
    ModularGroup.S • Work.Kernels.imagAxis s hs = Work.Kernels.imagAxis s⁻¹ (by positivity) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul]
  simp only [Work.Kernels.imagAxis, UpperHalfPlane.coe_mk]
  rw [show (-(↑s * Complex.I)) = -(((s : ℝ) : ℂ) * Complex.I) by ring, inv_neg, mul_inv,
    Complex.inv_I]
  push_cast
  field_simp

theorem P1_axis_bound_twentyfour (K : UpperHalfPlane → UpperHalfPlane → ℂ) (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hscal : ∀ y t : ℝ, 1 ≤ y → 0 < t → t ≤ 1 →
      t ^ 10 * Real.exp (-(Real.pi * (1 / t)) - 2 * Real.pi * y)
        / (Real.exp (-(2 * Real.pi * y)) + Real.exp (-(2 * Real.pi * (1 / t))))
        ≤ Real.exp (-(Real.pi * y)))
    (hslash : ∀ (τ z : UpperHalfPlane), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
      (1 : ℝ) / 3 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      ‖(z : ℂ) ^ ((24 : ℤ) / 2 - 2) * K τ (ModularGroup.S • z)‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * ‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) :
    ∃ C' N' Y₀' : ℝ, 0 ≤ C' ∧ 0 ≤ N' ∧ 2 ≤ Y₀' ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), (τ.re = 1 / 2 ∨ τ.re = - 1 / 2) → Y₀' ≤ τ.im → t ≤ 1 →
        ‖K τ (Work.Kernels.imagAxis t ht)‖ ≤ C' * τ.im ^ N' * Real.exp (-(3 * Real.pi * τ.im)) := by
  obtain ⟨CD, hCD, hΔup⟩ := Work.Asymptotics.delta_upper_third
  obtain ⟨cc, T₀, hcc, hT₀, hdiv⟩ := Work.Asymptotics.divisor_qdiff_lower
  have hCpos : (0 : ℝ) ≤ C * CD / cc * 3 ^ A := by
    have h1 : (0 : ℝ) ≤ C * CD / cc := by positivity
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ A := by positivity
    nlinarith [h1, h2]
  refine ⟨C * CD / cc * 3 ^ A + 1, A, max 3 (max T₀ 2), by linarith, hA, ?_, ?_⟩
  · exact le_trans (le_max_right T₀ 2) (le_max_right 3 (max T₀ 2))
  intro τ t ht hre hy ht1
  have hy3 : (3 : ℝ) ≤ τ.im := le_trans (le_max_left 3 (max T₀ 2)) hy
  have hy1 : (1 : ℝ) ≤ τ.im := by linarith
  have hyT0 : T₀ ≤ τ.im :=
    le_trans (le_trans (le_max_left T₀ 2) (le_max_right 3 (max T₀ 2))) hy
  have hτ2 : (2 : ℝ) ≤ τ.im := by linarith
  have hτ13 : (1 : ℝ) / 3 ≤ τ.im := by linarith
  have hpos : (0 : ℝ) < t⁻¹ := inv_pos.mpr ht
  set z : UpperHalfPlane := Work.Kernels.imagAxis t⁻¹ hpos with hzdef
  have hzim : z.im = t⁻¹ := by rw [hzdef]; simp [Work.Kernels.imagAxis]
  have hs1 : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
  have hz3 : (1 : ℝ) / 3 ≤ z.im := by rw [hzim]; linarith
  have hSz : ModularGroup.S • z = Work.Kernels.imagAxis t ht := by
    rw [hzdef, S_smul_imagAxis t⁻¹ hpos]
    exact imagAxis_congr (by rw [inv_inv]) _ _
  have hnormz : ‖(z : ℂ)‖ = t⁻¹ := by
    rw [hzdef]
    simp only [Work.Kernels.imagAxis, UpperHalfPlane.coe_mk]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  -- membership in the CKMRV domain `𝒟`
  have hDmem : τ ∈ Work.Asymptotics.DomainD := by
    rw [Work.Asymptotics.mem_DomainD]
    have hb1 : (1 : ℝ) / 2 < ‖(τ : ℂ) - (1 / 2 : ℂ)‖ := by
      have h := Complex.abs_im_le_norm ((τ : ℂ) - (1 / 2 : ℂ))
      rw [Complex.sub_im, UpperHalfPlane.coe_im,
        show ((1 / 2 : ℂ)).im = 0 by norm_num, sub_zero, abs_of_pos τ.im_pos] at h
      linarith [h, hτ2]
    have hb2 : (1 : ℝ) / 2 < ‖(τ : ℂ) + (1 / 2 : ℂ)‖ := by
      have h := Complex.abs_im_le_norm ((τ : ℂ) + (1 / 2 : ℂ))
      rw [Complex.add_im, UpperHalfPlane.coe_im,
        show ((1 / 2 : ℂ)).im = 0 by norm_num, add_zero, abs_of_pos τ.im_pos] at h
      linarith [h, hτ2]
    rcases hre with h | h
    · exact ⟨by rw [h]; norm_num, by rw [h]; norm_num, hb1, hb2⟩
    · exact ⟨by rw [h]; norm_num, by rw [h]; norm_num, hb1, hb2⟩
  -- the `q`-difference on the two lines
  have hq : ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖
      = Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹)) := by
    rw [hzdef]; exact qParamFun_line_norm_sub τ hre t⁻¹ hpos
  have hden_low : cc * (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹)))
      ≤ ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
    have h := hdiv τ z hyT0 hz3
    rwa [hq] at h
  have hDpos : (0 : ℝ) < ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
    lt_of_lt_of_le (mul_pos hcc (by positivity)) hden_low
  have hne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    intro hc
    have h0 : Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) = 0 := by
      rw [hc, sub_self, mul_zero]
    rw [h0, norm_zero] at hDpos
    exact absurd hDpos (lt_irrefl 0)
  have hsla := hslash τ z hDmem hτ2 hz3 hne
  have hΔτle : ‖Work.Kernels.DeltaFun τ‖ ≤ CD * Real.exp (-(2 * Real.pi * τ.im)) := by
    calc ‖Work.Kernels.DeltaFun τ‖ ≤ CD * ‖Work.Kernels.qParamFun τ‖ := hΔup τ hτ13
      _ = CD * Real.exp (-(2 * Real.pi * τ.im)) := by rw [Work.Asymptotics.norm_qParamFun]
  have hsplit : ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
      = ‖Work.Kernels.DeltaFun τ‖
        * ‖Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
    rw [show Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
        = Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) by ring]
    rw [norm_mul]
  have hWle : cc * (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹)))
        / (CD * Real.exp (-(2 * Real.pi * τ.im)))
      ≤ ‖Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < CD * Real.exp (-(2 * Real.pi * τ.im)))]
    rw [hsplit] at hden_low
    calc cc * (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹)))
        ≤ ‖Work.Kernels.DeltaFun τ‖
            * ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := hden_low
      _ ≤ (CD * Real.exp (-(2 * Real.pi * τ.im)))
            * ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
          mul_le_mul_of_nonneg_right hΔτle (norm_nonneg _)
      _ = ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
            * (CD * Real.exp (-(2 * Real.pi * τ.im))) := by ring
  have hinv : 1 / ‖Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
      ≤ (CD * Real.exp (-(2 * Real.pi * τ.im)))
          / (cc * (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹)))) := by
    calc 1 / ‖Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
        ≤ 1 / (cc * (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹)))
              / (CD * Real.exp (-(2 * Real.pi * τ.im)))) :=
          one_div_le_one_div_of_le (by positivity) hWle
      _ = (CD * Real.exp (-(2 * Real.pi * τ.im)))
            / (cc * (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹)))) :=
          one_div_div _ _
  have hA1nn : (0 : ℝ) ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * ‖Work.Kernels.qParamFun τ‖
      * Real.exp (-(Real.pi * z.im)) := by positivity
  have hk2 : ‖(z : ℂ) ^ ((24 : ℤ) / 2 - 2) * K τ (ModularGroup.S • z)‖
      ≤ (C * (1 + ‖(τ : ℂ)‖) ^ A * ‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im)))
          * ((CD * Real.exp (-(2 * Real.pi * τ.im)))
              / (cc * (Real.exp (-(2 * Real.pi * τ.im))
                  + Real.exp (-(2 * Real.pi * t⁻¹))))) := by
    have h1 : ‖(z : ℂ) ^ ((24 : ℤ) / 2 - 2) * K τ (ModularGroup.S • z)‖
        ≤ (C * (1 + ‖(τ : ℂ)‖) ^ A * ‖Work.Kernels.qParamFun τ‖
            * Real.exp (-(Real.pi * z.im)))
          * (‖Work.Kernels.DeltaFun z
              * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)⁻¹ := by
      rw [div_eq_mul_inv] at hsla
      exact hsla
    have h2 : (‖Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)⁻¹
        ≤ (CD * Real.exp (-(2 * Real.pi * τ.im)))
            / (cc * (Real.exp (-(2 * Real.pi * τ.im))
                + Real.exp (-(2 * Real.pi * t⁻¹)))) := by
      rw [← one_div]; exact hinv
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hA1nn)
  have hnorm_eq : ‖K τ (Work.Kernels.imagAxis t ht)‖
      = t ^ 10 * ‖(z : ℂ) ^ ((24 : ℤ) / 2 - 2) * K τ (ModularGroup.S • z)‖ := by
    have hzpow : ((24 : ℤ) / 2 - 2) = ((10 : ℕ) : ℤ) := by norm_num
    rw [← hSz, hzpow, zpow_natCast, norm_mul, norm_pow, hnormz]
    rw [show (t⁻¹ : ℝ) ^ 10 = (t ^ 10)⁻¹ by rw [inv_pow]]
    field_simp
  have hze : Real.exp (-(Real.pi * z.im)) = Real.exp (-(Real.pi * t⁻¹)) := by rw [hzim]
  have halg : t ^ 10 * ((C * (1 + ‖(τ : ℂ)‖) ^ A * ‖Work.Kernels.qParamFun τ‖
          * Real.exp (-(Real.pi * z.im)))
        * ((CD * Real.exp (-(2 * Real.pi * τ.im)))
            / (cc * (Real.exp (-(2 * Real.pi * τ.im))
                + Real.exp (-(2 * Real.pi * t⁻¹))))))
      = (C * CD / cc) * (1 + ‖(τ : ℂ)‖) ^ A
          * (‖Work.Kernels.qParamFun τ‖ * (t ^ 10
              * Real.exp (-(Real.pi * t⁻¹) - 2 * Real.pi * τ.im)
              / (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹))))) := by
    rw [hze]
    rw [show Real.exp (-(Real.pi * t⁻¹) - 2 * Real.pi * τ.im)
        = Real.exp (-(Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * τ.im)) by
      rw [← Real.exp_add]; congr 1]
    field_simp
  have hchain : ‖K τ (Work.Kernels.imagAxis t ht)‖
      ≤ (C * CD / cc) * (1 + ‖(τ : ℂ)‖) ^ A
          * (‖Work.Kernels.qParamFun τ‖ * (t ^ 10
              * Real.exp (-(Real.pi * t⁻¹) - 2 * Real.pi * τ.im)
              / (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹))))) := by
    rw [hnorm_eq]
    exact le_trans (mul_le_mul_of_nonneg_left hk2 (by positivity)) (le_of_eq halg)
  have hsc' : t ^ 10 * Real.exp (-(Real.pi * t⁻¹) - 2 * Real.pi * τ.im)
      / (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹)))
      ≤ Real.exp (-(Real.pi * τ.im)) := by
    simpa only [one_div] using hscal τ.im t hy1 ht ht1
  have hexp : Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(Real.pi * τ.im))
      = Real.exp (-(3 * Real.pi * τ.im)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hτnorm : 1 + ‖(τ : ℂ)‖ ≤ 3 * τ.im := by
    have h := Complex.norm_le_abs_re_add_abs_im (τ : ℂ)
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, abs_of_pos τ.im_pos] at h
    have hre' : |τ.re| ≤ 1 / 2 := by rcases hre with hh | hh <;> rw [hh] <;> norm_num
    linarith [h, hre', hy1]
  have hp1 : (1 + ‖(τ : ℂ)‖) ^ A ≤ (3 * τ.im) ^ A :=
    Real.rpow_le_rpow (by positivity) hτnorm hA
  have hp2 : (3 * τ.im) ^ A = (3 : ℝ) ^ A * τ.im ^ A :=
    Real.mul_rpow (by norm_num) (by positivity)
  have hfinal : ‖K τ (Work.Kernels.imagAxis t ht)‖
      ≤ (C * CD / cc * 3 ^ A + 1) * τ.im ^ A * Real.exp (-(3 * Real.pi * τ.im)) := by
    refine le_trans hchain ?_
    have hstep : (C * CD / cc) * (1 + ‖(τ : ℂ)‖) ^ A
          * (‖Work.Kernels.qParamFun τ‖ * (t ^ 10
              * Real.exp (-(Real.pi * t⁻¹) - 2 * Real.pi * τ.im)
              / (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹)))))
        ≤ (C * CD / cc) * (1 + ‖(τ : ℂ)‖) ^ A
          * (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * τ.im))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hsc' (norm_nonneg _)
    refine le_trans hstep ?_
    rw [Work.Asymptotics.norm_qParamFun τ, hexp]
    have hkey : (C * CD / cc) * (1 + ‖(τ : ℂ)‖) ^ A
        ≤ ((C * CD / cc) * (3 : ℝ) ^ A + 1) * τ.im ^ A := by
      calc (C * CD / cc) * (1 + ‖(τ : ℂ)‖) ^ A
          ≤ (C * CD / cc) * (3 * τ.im) ^ A := mul_le_mul_of_nonneg_left hp1 (by positivity)
        _ = (C * CD / cc) * ((3 : ℝ) ^ A * τ.im ^ A) := by rw [hp2]
        _ = ((C * CD / cc) * (3 : ℝ) ^ A) * τ.im ^ A := by ring
        _ ≤ ((C * CD / cc) * (3 : ℝ) ^ A + 1) * τ.im ^ A := by
            apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num))
            exact Real.rpow_nonneg τ.im_pos.le A
    exact mul_le_mul_of_nonneg_right hkey (Real.exp_nonneg _)
  exact hfinal

end

end Work.CKFinal.LineDecay

import Submission.Work.Fatou.DevH.deriv_setup

/-!
# The derivative of `devH`

`devH x₀ F ζ = (x₀ : ℂ) + ζ + χ(Re ζ)·ε(x₀ + ζ - 1)` is differentiable on all of `ℂ` (although `F`
is only known on `Qreg`) and

`D devH ζ = id + χ(Re ζ)·(F'(x₀+ζ-1) - 1)·id + ε(x₀+ζ-1)·χ'(Re ζ)·(Re ·) = devHDeriv x₀ F ζ`.

The point is that the factor `χ(Re ζ)` vanishes outside the transition strip `[1/8, 15/8]`, on which
the argument `x₀ + ζ - 1` lies in `Qreg`; so the only points where `F` is evaluated are points where
it is holomorphic.
-/

namespace Work.Fatou.DevH

open MandelDim Filter Set
open scoped Topology

noncomputable section

theorem devHCorr_eq_zero {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ} (h : ζ.re ≤ 1 / 8 ∨ 15 / 8 ≤ ζ.re) :
    devHCorr x₀ F ζ = 0 := by
  ext v
  rcases h with h | h
  · simp [devHCorr, smul_apply, smoothstep_eq_zero_of_le h, deriv_smoothstep_eq_zero_of_le h]
  · simp [devHCorr, smul_apply, smoothstep_eq_zero_of_ge h, deriv_smoothstep_eq_zero_of_ge h]

theorem devHDeriv_eq_id_of_le {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ} (h : ζ.re ≤ 1 / 8) :
    devHDeriv x₀ F ζ = ContinuousLinearMap.id ℝ ℂ := by
  rw [devHDeriv, devHCorr_eq_zero (Or.inl h), zero_add]

theorem devHDeriv_eq_id_of_ge {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ} (h : 15 / 8 ≤ ζ.re) :
    devHDeriv x₀ F ζ = ContinuousLinearMap.id ℝ ℂ := by
  rw [devHDeriv, devHCorr_eq_zero (Or.inr h), zero_add]

/-- To the left of the transition strip, `devH` is the translation `ζ ↦ x₀ + ζ`. -/
theorem devH_eventuallyEq_affine_of_lt {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ} (h : ζ.re < 1 / 8) :
    devH x₀ F =ᶠ[𝓝 ζ] fun ζ' => (x₀ : ℂ) + ζ' := by
  filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds h] with ζ' hζ'
  exact devH_of_le_one_eighth hζ'.le

/-- To the right of the transition strip, `devH` is again the translation `ζ ↦ x₀ + ζ`. -/
theorem devH_eventuallyEq_affine_of_gt {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ} (h : 15 / 8 < ζ.re) :
    devH x₀ F =ᶠ[𝓝 ζ] fun ζ' => (x₀ : ℂ) + ζ' := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h] with ζ' hζ'
  exact devH_of_ge_fifteen hζ'.le

/-- The derivative of the shift `ζ ↦ x₀ + ζ`. -/
theorem hasFDerivAt_affine (x₀ : ℝ) (ζ : ℂ) :
    HasFDerivAt (fun ζ' : ℂ => (x₀ : ℂ) + ζ') (ContinuousLinearMap.id ℝ ℂ) ζ := by
  have h1 : HasFDerivAt (fun ζ' : ℂ => ζ' + (x₀ : ℂ)) (ContinuousLinearMap.id ℝ ℂ) ζ :=
    (hasFDerivAt_id (𝕜 := ℝ) ζ).add_const (x₀ : ℂ)
  have hfun : (fun ζ' : ℂ => ζ' + (x₀ : ℂ)) = fun ζ' : ℂ => (x₀ : ℂ) + ζ' := by
    ext w
    ring
  rwa [hfun] at h1

/-- The main derivative formula: `D devH = devHDeriv`. -/
theorem hasFDerivAt_devH {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) (ζ : ℂ) :
    HasFDerivAt (devH (xOf b₁ b₂) F) (devHDeriv (xOf b₁ b₂) F ζ) ζ := by
  rcases lt_or_ge ζ.re (1 / 8) with hlt | hge
  · rw [devHDeriv_eq_id_of_le hlt.le]
    exact (hasFDerivAt_affine (xOf b₁ b₂) ζ).congr_of_eventuallyEq
      (devH_eventuallyEq_affine_of_lt hlt)
  · rcases le_or_gt ζ.re (15 / 8) with hle | hgt
    · have hmem : shiftArg (xOf b₁ b₂) ζ ∈ Qreg b₁ b₂ := shiftArg_mem_Qreg hadm hge hle
      have hdF : DifferentiableAt ℂ F (shiftArg (xOf b₁ b₂) ζ) :=
        differentiableAt_of_mem_Qreg hF hmem
      have hprod := HasFDerivAt.mul (hasFDerivAt_smoothstep_re ζ)
        (hasFDerivAt_eps_shift (x₀ := xOf b₁ b₂) hdF)
      have hmain : HasFDerivAt
          (fun ζ' : ℂ => ((smoothstep ζ'.re : ℝ) : ℂ) * eps F (shiftArg (xOf b₁ b₂) ζ')
            + ((xOf b₁ b₂ : ℂ) + ζ'))
          (devHDeriv (xOf b₁ b₂) F ζ) ζ := hprod.add (hasFDerivAt_affine (xOf b₁ b₂) ζ)
      refine hmain.congr_of_eventuallyEq (EventuallyEq.of_eq ?_)
      ext ζ'
      rw [devH_apply]
      simp only [shiftArg_eq]
      ring
    · rw [devHDeriv_eq_id_of_ge hgt.le]
      exact (hasFDerivAt_affine (xOf b₁ b₂) ζ).congr_of_eventuallyEq
        (devH_eventuallyEq_affine_of_gt hgt)


/-- `I·(I + c·I) = -1 - c`. -/
theorem I_mul_I_add (c : ℂ) : Complex.I * (Complex.I + c * Complex.I) = -1 - c := by
  calc Complex.I * (Complex.I + c * Complex.I) = Complex.I * Complex.I * (1 + c) := by ring
    _ = -1 * (1 + c) := by rw [Complex.I_mul_I]
    _ = -1 - c := by ring

/-- Once the real derivative is known, the Wirtinger `dz` derivative of `devH` is
`1 + c1/2 + c2`. -/
theorem dz_eq {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ}
    (h : fderiv ℝ (devH x₀ F) ζ = devHDeriv x₀ F ζ) :
    MandelDim.dz (devH x₀ F) ζ = 1 + c1 x₀ F ζ / 2 + c2 x₀ F ζ := by
  have h1 := devHDeriv_one x₀ F ζ
  have hI := devHDeriv_I x₀ F ζ
  simp only [MandelDim.dz, h, h1, hI, I_mul_I_add]
  ring

/-- Once the real derivative is known, the Wirtinger `dzbar` derivative of `devH` is `c1/2`. -/
theorem dzbar_eq {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ}
    (h : fderiv ℝ (devH x₀ F) ζ = devHDeriv x₀ F ζ) :
    MandelDim.dzbar (devH x₀ F) ζ = c1 x₀ F ζ / 2 := by
  have h1 := devHDeriv_one x₀ F ζ
  have hI := devHDeriv_I x₀ F ζ
  simp only [MandelDim.dzbar, h, h1, hI, I_mul_I_add]
  ring

/-- Once the real derivative is known, the correction term is `devHCorr`. -/
theorem fderiv_sub_id_eq {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ}
    (h : fderiv ℝ (devH x₀ F) ζ = devHDeriv x₀ F ζ) :
    fderiv ℝ (devH x₀ F) ζ - ContinuousLinearMap.id ℝ ℂ = devHCorr x₀ F ζ := by
  rw [h, devHDeriv, add_sub_cancel_right]


/-- The Wirtinger bound for `dz`, from the two coefficient bounds. -/
theorem norm_dz_sub_one_le {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ}
    (hc1 : ‖c1 x₀ F ζ‖ ≤ 1 / 16) (hc2 : ‖c2 x₀ F ζ‖ ≤ 1 / 32)
    (h : fderiv ℝ (devH x₀ F) ζ = devHDeriv x₀ F ζ) :
    ‖MandelDim.dz (devH x₀ F) ζ - 1‖ ≤ 1 / 16 := by
  have hval : 1 + c1 x₀ F ζ / 2 + c2 x₀ F ζ - 1 = c1 x₀ F ζ / 2 + c2 x₀ F ζ := by ring
  rw [dz_eq h, hval]
  calc ‖c1 x₀ F ζ / 2 + c2 x₀ F ζ‖ ≤ ‖c1 x₀ F ζ / 2‖ + ‖c2 x₀ F ζ‖ := norm_add_le _ _
    _ = ‖c1 x₀ F ζ‖ / 2 + ‖c2 x₀ F ζ‖ := by rw [norm_div]; norm_num
    _ ≤ 1 / 16 := by linarith

/-- The Wirtinger bound for `dzbar`, from the coefficient bound for `c1`. -/
theorem norm_dzbar_le {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ} (hc1 : ‖c1 x₀ F ζ‖ ≤ 1 / 16)
    (h : fderiv ℝ (devH x₀ F) ζ = devHDeriv x₀ F ζ) :
    ‖MandelDim.dzbar (devH x₀ F) ζ‖ ≤ 1 / 32 := by
  rw [dzbar_eq h]
  calc ‖c1 x₀ F ζ / 2‖ = ‖c1 x₀ F ζ‖ / 2 := by rw [norm_div]; norm_num
    _ ≤ 1 / 32 := by linarith

end

end Work.Fatou.DevH

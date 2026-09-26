import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.LogLambda.LogGrowth.Lfun_sub_pi_I_bound
import Submission.Work.Kernels.LogLambda.LogLaws
import Submission.Work.Kernels.LogLambda.LambdaLaws

namespace Work.Residues

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups Manifold Modular ModularForm

/-! ## Two functions with the same exponential differ by a constant

`ℍ` is (path)connected, so a continuous function `ℍ → ℂ` whose exponential is identically
one is constant: it takes values in the discrete set `2πiℤ = {w | exp w = 1}`. -/

private theorem holo_const_of_exp_eq {f g : ℍ → ℂ}
    (hf : ContinuousOn f Set.univ) (hg : ContinuousOn g Set.univ)
    (h : ∀ τ, Complex.exp (f τ) = Complex.exp (g τ)) :
    ∃ c : ℂ, ∀ τ, f τ = g τ + c := by
  have hcont : ContinuousOn (fun τ : ℍ => f τ - g τ) Set.univ := hf.sub hg
  have hmaps : Set.MapsTo (fun τ : ℍ => f τ - g τ) Set.univ {w : ℂ | Complex.exp w = 1} := by
    intro τ _
    show Complex.exp (f τ - g τ) = 1
    rw [Complex.exp_sub, h τ, div_self (Complex.exp_ne_zero _)]
  refine ⟨f ⟨Complex.I, by norm_num⟩ - g ⟨Complex.I, by norm_num⟩, fun τ => ?_⟩
  have hcon := isPreconnected_univ.constant_of_mapsTo
    (Work.Analysis.BranchLog.isDiscrete_exp_eq_one) hcont hmaps
    (Set.mem_univ (⟨Complex.I, by norm_num⟩ : ℍ)) (Set.mem_univ τ)
  have hcs : f τ - g τ = f ⟨Complex.I, by norm_num⟩ - g ⟨Complex.I, by norm_num⟩ := hcon.symm
  linear_combination hcs

/-! ## Exponential decay of the explicit branch `Λ_S = 4 log θ₀₁ - 4 log θ₀₀`

For `im z ≥ 1` both `θ₀₀(z)` and `θ₀₁(z) = θ₀₀(z+1)` stay within distance `1/2` of `1`, so
the principal logarithms are bounded by `(3/2)‖θ - 1‖`, and `‖θ - 1‖` decays like
`2 e^{-π im z}/(1 - e^{-π im z}) ≤ (16/7) e^{-π im z}`. -/

private lemma norm_thetaC00_sub_one_le_exp {z : ℂ} (hz : 1 ≤ z.im) :
    ‖Work.Kernels.LogLambda.thetaC00 z - 1‖ ≤ (16 / 7) * Real.exp (-(Real.pi * z.im)) := by
  have hy : 0 < z.im := lt_of_lt_of_le zero_lt_one hz
  have hb := norm_jacobiTheta_sub_one_le (τ := z) hy
  have hb' : ‖Work.Kernels.LogLambda.thetaC00 z - 1‖
      ≤ 2 / (1 - Real.exp (-(Real.pi * z.im))) * Real.exp (-(Real.pi * z.im)) := by
    have h := hb
    rw [show (-Real.pi) * z.im = -(Real.pi * z.im) by ring] at h
    exact h
  have he : Real.exp (-(Real.pi * z.im)) ≤ 1 / 8 :=
    Work.Kernels.LogLambda.LogGrowth.exp_le_inv_eight_of_le_neg_pi
      (by nlinarith [Real.pi_pos, hz])
  have hep : 0 < Real.exp (-(Real.pi * z.im)) := Real.exp_pos _
  have hden : 0 < 1 - Real.exp (-(Real.pi * z.im)) := by linarith
  have hfrac : 2 / (1 - Real.exp (-(Real.pi * z.im))) ≤ 16 / 7 := by
    rw [div_le_div_iff₀ hden (by norm_num)]
    nlinarith [he]
  calc ‖Work.Kernels.LogLambda.thetaC00 z - 1‖
      ≤ 2 / (1 - Real.exp (-(Real.pi * z.im))) * Real.exp (-(Real.pi * z.im)) := hb'
    _ ≤ (16 / 7) * Real.exp (-(Real.pi * z.im)) :=
        mul_le_mul_of_nonneg_right hfrac hep.le

private lemma norm_log_thetaC00_le_exp {z : ℂ} (hz : 1 ≤ z.im) :
    ‖Complex.log (Work.Kernels.LogLambda.thetaC00 z)‖
      ≤ (24 / 7) * Real.exp (-(Real.pi * z.im)) := by
  have hb := norm_thetaC00_sub_one_le_exp hz
  have he : Real.exp (-(Real.pi * z.im)) ≤ 1 / 8 :=
    Work.Kernels.LogLambda.LogGrowth.exp_le_inv_eight_of_le_neg_pi
      (by nlinarith [Real.pi_pos, hz])
  have hsmall : ‖Work.Kernels.LogLambda.thetaC00 z - 1‖ ≤ 1 / 2 := by
    calc ‖Work.Kernels.LogLambda.thetaC00 z - 1‖
        ≤ (16 / 7) * Real.exp (-(Real.pi * z.im)) := hb
      _ ≤ (16 / 7) * (1 / 8) := by gcongr
      _ = 2 / 7 := by norm_num
      _ ≤ 1 / 2 := by norm_num
  have h := Complex.norm_log_one_add_half_le_self (z := Work.Kernels.LogLambda.thetaC00 z - 1)
    hsmall
  rw [show (1 : ℂ) + (Work.Kernels.LogLambda.thetaC00 z - 1) = Work.Kernels.LogLambda.thetaC00 z
    by ring] at h
  calc ‖Complex.log (Work.Kernels.LogLambda.thetaC00 z)‖
      ≤ (3 / 2) * ‖Work.Kernels.LogLambda.thetaC00 z - 1‖ := h
    _ ≤ (3 / 2) * ((16 / 7) * Real.exp (-(Real.pi * z.im))) := by linarith
    _ = (24 / 7) * Real.exp (-(Real.pi * z.im)) := by ring

/-- `‖Λ_S z‖ ≤ (192/7) e^{-π im z}` for `1 ≤ im z`. -/
private lemma LamS_bound_exp {z : ℂ} (hz : 1 ≤ z.im) :
    ‖Work.Kernels.LogLambda.LamS z‖ ≤ (192 / 7) * Real.exp (-(Real.pi * z.im)) := by
  have h1 := norm_log_thetaC00_le_exp (z := z) hz
  have h2 := norm_log_thetaC00_le_exp (z := z + 1) (by simpa using hz)
  have him : (z + 1).im = z.im := by simp
  rw [him] at h2
  have h01 : Work.Kernels.LogLambda.thetaC01 z = Work.Kernels.LogLambda.thetaC00 (z + 1) :=
    Work.Kernels.LogLambda.thetaC01_eq_thetaC00_add_one z
  rw [Work.Kernels.LogLambda.LamS, h01]
  have h3 : ‖(4 : ℂ) * Complex.log (Work.Kernels.LogLambda.thetaC00 (z + 1))
        - 4 * Complex.log (Work.Kernels.LogLambda.thetaC00 z)‖
      ≤ 4 * ‖Complex.log (Work.Kernels.LogLambda.thetaC00 (z + 1))‖
        + 4 * ‖Complex.log (Work.Kernels.LogLambda.thetaC00 z)‖ := by
    have h := norm_sub_le ((4 : ℂ) * Complex.log (Work.Kernels.LogLambda.thetaC00 (z + 1)))
      (4 * Complex.log (Work.Kernels.LogLambda.thetaC00 z))
    simpa [norm_mul] using h
  calc ‖(4 : ℂ) * Complex.log (Work.Kernels.LogLambda.thetaC00 (z + 1))
        - 4 * Complex.log (Work.Kernels.LogLambda.thetaC00 z)‖
      ≤ 4 * ‖Complex.log (Work.Kernels.LogLambda.thetaC00 (z + 1))‖
        + 4 * ‖Complex.log (Work.Kernels.LogLambda.thetaC00 z)‖ := h3
    _ ≤ 4 * ((24 / 7) * Real.exp (-(Real.pi * z.im)))
          + 4 * ((24 / 7) * Real.exp (-(Real.pi * z.im))) := by linarith
    _ = (192 / 7) * Real.exp (-(Real.pi * z.im)) := by ring

/-- For any data `(𝓛, 𝓛_S)` of CKMRV (Section 2.1.5) and `Im τ ≥ 1`: `𝓛(τ) - πiτ` is bounded
and `𝓛_S(τ) = O(e^{-π Im τ})` as `Im τ → ∞`.

`𝓛 - Lfun` is a constant multiple of `2πi` (ℍ is connected and both functions are holomorphic
logarithms of `λ`), while `𝓛_S` is *determined* by the transformation law
`𝓛_S(τ+1) = -𝓛_S(τ)`, and `1 - e^{𝓛_S} = λ = O(e^{-π Im τ})`. -/
theorem LogLambdaBound (ℓ : Work.Kernels.LogLambdaData) :
    (∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
        ‖ℓ.L τ - (Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ ≤ C) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
        ‖ℓ.L_S τ‖ ≤ C * Real.exp (-(Real.pi * τ.im))) := by
  -- Continuity of the two comparison functions.
  have hLin : ContinuousOn (fun τ : ℍ => Work.Kernels.LogLambda.Lfun (τ : ℂ)) Set.univ :=
    (Work.Kernels.LogLambda.Lfun_spec.1.continuousOn).comp continuous_coe.continuousOn
      (fun τ _ => τ.im_pos)
  have hLinv : ContinuousOn (fun τ : ℍ => Work.Kernels.LogLambda.Lfun (-(τ : ℂ)⁻¹)) Set.univ :=
    (Work.Kernels.LogLambda.Lfun_spec.1.continuousOn).comp
      ((continuous_coe.inv₀ (fun τ => by
        intro h0
        have h2 : (τ : ℂ).im = 0 := by rw [h0]; simp
        rw [UpperHalfPlane.coe_im] at h2
        linarith [τ.im_pos])).neg.continuousOn)
      (fun τ _ => Work.Kernels.LogLambda.im_neg_inv_pos τ.im_pos)
  -- Both `𝓛` and `Lfun` are logarithms of `λ`; both `𝓛_S` and `τ ↦ Lfun(-1/τ)` log `λ_S`.
  have hexpA : ∀ τ : ℍ, Complex.exp (ℓ.L τ)
      = Complex.exp (Work.Kernels.LogLambda.Lfun (τ : ℂ)) := by
    intro τ
    rw [ℓ.exp_L τ, Work.Kernels.LogLambda.Lfun_spec.2.1 (τ : ℂ) τ.2]
    exact (Work.Kernels.LogLambda.lamC_of_mem τ.2).symm
  have hexpB : ∀ τ : ℍ, Complex.exp (ℓ.L_S τ)
      = Complex.exp (Work.Kernels.LogLambda.Lfun (-(τ : ℂ)⁻¹)) := by
    intro τ
    rw [ℓ.exp_L_S τ, Work.Kernels.LogLambda.Lfun_spec.2.1 _
      (Work.Kernels.LogLambda.im_neg_inv_pos τ.im_pos)]
    exact (Work.Kernels.LogLambda.lamSC_of_mem τ.2).symm.trans
      (Work.Kernels.LogLambda.lamSC_eq_lamC_inv τ.im_pos)
  obtain ⟨c, hc⟩ := holo_const_of_exp_eq ℓ.holo.continuous.continuousOn hLin hexpA
  obtain ⟨cS, hcS⟩ := holo_const_of_exp_eq ℓ.holo_S.continuous.continuousOn hLinv hexpB
  -- The `T`-laws for `ℓ.L_S` and for `τ ↦ Lfun(-1/τ)` are opposite.
  have hT_LS : ∀ τ : ℍ, ℓ.L_S (ModularGroup.T • τ) = - ℓ.L_S τ := by
    intro τ
    have h := ℓ.slash_T_S τ
    rw [Work.Kernels.slash_apply'] at h
    simpa using h
  have hT_Lfun : ∀ τ : ℍ, Work.Kernels.LogLambda.Lfun (-(((ModularGroup.T • τ : ℍ)) : ℂ)⁻¹)
      = - Work.Kernels.LogLambda.Lfun (-(τ : ℂ)⁻¹) := by
    intro τ
    rw [Work.Kernels.coe_T_smul]
    exact Work.Kernels.LogLambda.lfun_inv_add_one (τ : ℂ) τ.2
  -- Hence the constant `cS` vanishes, so `𝓛_S = Lfun(-1/·)` exactly.
  have hcS0 : cS = 0 := by
    set τ₀ : ℍ := ⟨Complex.I, by norm_num⟩ with hτ₀
    have h1 := hcS (ModularGroup.T • τ₀)
    have h2 := hcS τ₀
    rw [hT_LS τ₀, hT_Lfun τ₀] at h1
    have h1' : cS = - ℓ.L_S τ₀ + Work.Kernels.LogLambda.Lfun (-(τ₀ : ℂ)⁻¹) := by
      rw [h1]; ring
    have h2' : cS = ℓ.L_S τ₀ - Work.Kernels.LogLambda.Lfun (-(τ₀ : ℂ)⁻¹) := by
      rw [h2]; ring
    have hcs : cS = -cS := by
      calc cS = - ℓ.L_S τ₀ + Work.Kernels.LogLambda.Lfun (-(τ₀ : ℂ)⁻¹) := h1'
        _ = - (ℓ.L_S τ₀ - Work.Kernels.LogLambda.Lfun (-(τ₀ : ℂ)⁻¹)) := by ring
        _ = - cS := by rw [h2']
    have h2c : cS + cS = 0 := by nth_rewrite 1 [hcs]; rw [neg_add_cancel]
    exact add_self_eq_zero.mp h2c
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.Kernels.LogLambda.LogGrowth.Lfun_sub_pi_I_bound
  constructor
  · -- `𝓛 - πiτ` is bounded on `{im ≥ 1}` since `𝓛 = Lfun + c` there.
    refine ⟨C₀ + ‖c‖ + 1, by linarith [hC₀pos, norm_nonneg c], fun τ hτ => ?_⟩
    have hzW : (τ : ℂ) ∈ Work.Kernels.LogLambda.W := by
      show (1 / 2 : ℝ) < (τ : ℂ).im
      rw [UpperHalfPlane.coe_im]; linarith
    have hzim : 1 ≤ (τ : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact hτ
    have hb := hC₀ (τ : ℂ) hzW hzim
    have he : ℓ.L τ - (Real.pi : ℂ) * Complex.I * (τ : ℂ)
        = (Work.Kernels.LogLambda.Lfun (τ : ℂ)
            - (Real.pi : ℂ) * Complex.I * (τ : ℂ)) + c := by
      rw [hc τ]; ring
    rw [he]
    calc ‖(Work.Kernels.LogLambda.Lfun (τ : ℂ) - (Real.pi : ℂ) * Complex.I * (τ : ℂ)) + c‖
        ≤ ‖Work.Kernels.LogLambda.Lfun (τ : ℂ) - (Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ + ‖c‖ :=
          norm_add_le _ _
      _ ≤ C₀ + ‖c‖ := by linarith
      _ ≤ C₀ + ‖c‖ + 1 := by linarith
  · -- `𝓛_S = τ ↦ Lfun(-1/τ) = Λ_S`, which decays like `e^{-π im τ}`.
    refine ⟨192 / 7, by norm_num, fun τ hτ => ?_⟩
    have hzW : (τ : ℂ) ∈ Work.Kernels.LogLambda.W := by
      show (1 / 2 : ℝ) < (τ : ℂ).im
      rw [UpperHalfPlane.coe_im]; linarith
    have hzim : 1 ≤ (τ : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact hτ
    have h1 : ℓ.L_S τ = Work.Kernels.LogLambda.Lfun (-(τ : ℂ)⁻¹) := by
      rw [hcS τ, hcS0, add_zero]
    rw [h1, Work.Kernels.LogLambda.Lfun_inv_eq_LamS (τ : ℂ) hzW]
    have hb := LamS_bound_exp (z := (τ : ℂ)) hzim
    simpa [UpperHalfPlane.coe_im] using hb

end Work.Residues

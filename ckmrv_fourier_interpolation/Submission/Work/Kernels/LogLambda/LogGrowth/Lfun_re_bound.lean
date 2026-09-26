import Mathlib
import Submission.Work.Kernels.LogLambda.LogNormalisation
import Submission.Work.Kernels.LogLambda.LogExtension
import Submission.Work.Kernels.LogLambda.LogConstruct
import Submission.Work.Kernels.LogLambda.ThetaLower.theta_lower_bound
import Submission.Work.Kernels.ClassicalFacts.theta00Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.theta10Fun_mem_InP
import Submission.Work.Kernels.ModerateGrowth

noncomputable section

open UpperHalfPlane ModularGroup Matrix Complex Set Filter Topology
open scoped Modular MatrixGroups
open Work.Kernels

namespace Work.Kernels.LogLambda.LogGrowth

/-! ## Numeric bounds on the fundamental domain -/

lemma exp_neg_pi_le_fifth {y : ℝ} (hy : Real.sqrt 3 / 2 ≤ y) :
    Real.exp (-(Real.pi * y)) ≤ 1 / 5 := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hs3 : (5 : ℝ) / 3 < Real.sqrt 3 := by
    have h3 : (0 : ℝ) ≤ 3 := by norm_num
    have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt h3
    nlinarith [Real.sqrt_nonneg 3]
  have hprod : (5 : ℝ) < Real.pi * Real.sqrt 3 := by nlinarith [Real.pi_pos]
  have h2 : (5 : ℝ) / 2 ≤ Real.pi * y := by nlinarith [Real.pi_pos]
  have hmono : Real.exp (-(Real.pi * y)) ≤ Real.exp (-(5 / 2)) := by
    apply Real.exp_le_exp.mpr; linarith
  have h5 : (5 : ℝ) ≤ Real.exp (5 / 2) := by
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 5 / 2 by norm_num)
    nlinarith
  have he : Real.exp (-(5 / 2)) ≤ 1 / 5 := by
    rw [Real.exp_neg, show (1 : ℝ) / 5 = (5 : ℝ)⁻¹ by norm_num,
      inv_le_inv₀ (Real.exp_pos _) (by norm_num)]
    exact h5
  linarith

/-- On `{im z ≥ √3/2}` the theta function `θ₀₀` is within `1/2` of `1`. -/
lemma jacobiTheta_fd_bound {z : ℂ} (hz : Real.sqrt 3 / 2 ≤ z.im) :
    ‖jacobiTheta z - 1‖ ≤ 1 / 2 := by
  have hzpos : 0 < z.im := lt_of_lt_of_le (by positivity) hz
  have h := norm_jacobiTheta_sub_one_le (τ := z) hzpos
  set r := Real.exp (-Real.pi * z.im) with hr
  have hrle : r ≤ 1 / 5 := by
    rw [hr]
    have : -Real.pi * z.im = -(Real.pi * z.im) := by ring
    rw [this]
    exact exp_neg_pi_le_fifth hz
  have hrpos : 0 < r := by rw [hr]; positivity
  have hden : 0 < 1 - r := by linarith
  have htarget : 2 / (1 - r) * r ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]; linarith
  exact le_trans h htarget

lemma sqrt3_div_two_le_im_of_mem_fd {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) :
    Real.sqrt 3 / 2 ≤ τ.im := by
  have h := three_le_four_mul_im_sq_of_mem_fd hτ
  have hpos : 0 < τ.im := τ.im_pos
  have h2 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  nlinarith [Real.sqrt_nonneg 3, sq_nonneg (τ.im - Real.sqrt 3 / 2),
    sq_nonneg (τ.im + Real.sqrt 3 / 2)]

/-! ## The three theta functions on the fundamental domain -/

lemma theta00Fun_fd_lower (τ : ℍ) (hτ : τ ∈ ModularGroup.fd) :
    1 / 2 ≤ ‖theta00Fun τ‖ := by
  have h := jacobiTheta_fd_bound (z := (τ : ℂ)) (by simpa using sqrt3_div_two_le_im_of_mem_fd hτ)
  have h1 : theta00Fun τ = jacobiTheta (τ : ℂ) := rfl
  rw [h1]
  have htri : (1 : ℝ) ≤ ‖jacobiTheta (τ : ℂ)‖ + ‖jacobiTheta (τ : ℂ) - 1‖ := by
    have := norm_sub_le (jacobiTheta (τ : ℂ)) (jacobiTheta (τ : ℂ) - 1)
    simpa using this
  linarith

lemma theta00Fun_fd_upper (τ : ℍ) (hτ : τ ∈ ModularGroup.fd) :
    ‖theta00Fun τ‖ ≤ 3 := by
  have h := jacobiTheta_fd_bound (z := (τ : ℂ)) (by simpa using sqrt3_div_two_le_im_of_mem_fd hτ)
  have h1 : theta00Fun τ = jacobiTheta (τ : ℂ) := rfl
  rw [h1]
  have htri : ‖jacobiTheta (τ : ℂ)‖ ≤ ‖jacobiTheta (τ : ℂ) - 1‖ + 1 := by
    have := norm_add_le (jacobiTheta (τ : ℂ) - 1) (1 : ℂ)
    simpa using this
  linarith

lemma theta01Fun_fd_lower (τ : ℍ) (hτ : τ ∈ ModularGroup.fd) :
    1 / 2 ≤ ‖theta01Fun τ‖ := by
  have hy := sqrt3_div_two_le_im_of_mem_fd hτ
  have h1 : theta01Fun τ = jacobiTheta ((τ : ℂ) + 1) :=
    Work.Kernels.ClassicalFacts.jacobiTheta₂_half_eq_jacobiTheta_add_one (τ : ℂ)
  have him : (((τ : ℂ) + 1)).im = τ.im := by simp
  have h := jacobiTheta_fd_bound (z := (τ : ℂ) + 1) (by rw [him]; exact hy)
  rw [h1]
  have htri : (1 : ℝ) ≤ ‖jacobiTheta ((τ : ℂ) + 1)‖ + ‖jacobiTheta ((τ : ℂ) + 1) - 1‖ := by
    have := norm_sub_le (jacobiTheta ((τ : ℂ) + 1)) (jacobiTheta ((τ : ℂ) + 1) - 1)
    simpa using this
  linarith

lemma theta01Fun_fd_upper (τ : ℍ) (hτ : τ ∈ ModularGroup.fd) :
    ‖theta01Fun τ‖ ≤ 3 := by
  have hy := sqrt3_div_two_le_im_of_mem_fd hτ
  have h1 : theta01Fun τ = jacobiTheta ((τ : ℂ) + 1) :=
    Work.Kernels.ClassicalFacts.jacobiTheta₂_half_eq_jacobiTheta_add_one (τ : ℂ)
  have him : (((τ : ℂ) + 1)).im = τ.im := by simp
  have h := jacobiTheta_fd_bound (z := (τ : ℂ) + 1) (by rw [him]; exact hy)
  rw [h1]
  have htri : ‖jacobiTheta ((τ : ℂ) + 1)‖ ≤ ‖jacobiTheta ((τ : ℂ) + 1) - 1‖ + 1 := by
    have := norm_add_le (jacobiTheta ((τ : ℂ) + 1) - 1) (1 : ℂ)
    simpa using this
  linarith

/-- The estimate `‖θ(z/2,z)/2‖ ∈ [1,3]` on the fundamental domain. -/
lemma ratio_norm_bounds_fd (τ : ℍ) (hτ : τ ∈ ModularGroup.fd) :
    (1 : ℝ) ≤ ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)‖ ∧
      ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)‖ ≤ 3 := by
  have hy := sqrt3_div_two_le_im_of_mem_fd hτ
  have hzpos : 0 < τ.im := τ.im_pos
  have hr := ThetaLower.ratio_estimate (τ : ℂ) hzpos
  set r := Real.exp (-(2 * Real.pi * (τ : ℂ).im)) with hrdef
  have h2pi : (5 : ℝ) ≤ 2 * Real.pi * τ.im := by
    have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hs3 : (5 : ℝ) / 3 < Real.sqrt 3 := by
      have h3 : (0 : ℝ) ≤ 3 := by norm_num
      have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt h3
      nlinarith [Real.sqrt_nonneg 3]
    have : (5 : ℝ) < Real.pi * Real.sqrt 3 := by nlinarith [Real.pi_pos]
    nlinarith [Real.pi_pos, Real.sqrt_nonneg 3, hy]
  have hrle : r ≤ 1 / 3 := by
    rw [hrdef]
    have him : (τ : ℂ).im = τ.im := rfl
    have h5 : -(2 * Real.pi * (τ : ℂ).im) ≤ -(5 : ℝ) := by rw [him]; linarith
    have h3 : Real.exp (-(5 : ℝ)) ≤ 1 / 3 := by
      rw [Real.exp_neg, show (1 : ℝ) / 3 = (3 : ℝ)⁻¹ by norm_num,
        inv_le_inv₀ (Real.exp_pos _) (by norm_num)]
      have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 5 by norm_num); nlinarith
    exact le_trans (Real.exp_le_exp.mpr h5) h3
  have hrpos : 0 < r := by rw [hrdef]; positivity
  have hden : 0 < 1 - r := by linarith
  have hbound : r / (1 - r) ≤ 1 / 2 := by
    rw [div_le_iff₀ hden]; linarith
  have hJ : ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) / 2 - 1‖ ≤ 1 / 2 :=
    hr.trans hbound
  have hnorm : ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) / 2‖
      = ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)‖ / 2 := by rw [norm_div]; norm_num
  constructor
  · have htri : (1 : ℝ) ≤ ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) / 2‖
        + ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) / 2 - 1‖ := by
      have := norm_sub_le (jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) / 2)
        (jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) / 2 - 1)
      simpa using this
    rw [hnorm] at htri; linarith
  · have htri : ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) / 2‖
        ≤ ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) / 2 - 1‖ + 1 := by
      have := norm_add_le (jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) / 2 - 1) (1 : ℂ)
      simpa using this
    rw [hnorm] at htri; linarith

lemma norm_exp_pi_I_div_four (τ : ℍ) :
    ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4)‖
      = Real.exp (-(Real.pi * τ.im / 4)) := by
  have hre : (Real.pi * Complex.I * (τ : ℂ) / 4).re = -(Real.pi * τ.im / 4) := by
    have h : Real.pi * Complex.I * (τ : ℂ) / 4
        = ((Real.pi / 4 : ℝ) : ℂ) * (Complex.I * (τ : ℂ)) := by push_cast; ring
    rw [h, Complex.re_ofReal_mul, Complex.I_mul_re]
    simp
    ring
  rw [Complex.norm_exp, hre]

lemma theta10Fun_fd_lower (τ : ℍ) (hτ : τ ∈ ModularGroup.fd) :
    (1 / 2) * Real.exp (-(Real.pi * τ.im / 4)) ≤ ‖theta10Fun τ‖ := by
  obtain ⟨hlo, -⟩ := ratio_norm_bounds_fd τ hτ
  have htheta : ‖theta10Fun τ‖
      = Real.exp (-(Real.pi * τ.im / 4)) * ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)‖ := by
    simp only [theta10Fun]
    rw [norm_mul, norm_exp_pi_I_div_four]
  rw [htheta]
  have he : 0 < Real.exp (-(Real.pi * τ.im / 4)) := Real.exp_pos _
  nlinarith

lemma theta10Fun_fd_upper (τ : ℍ) (hτ : τ ∈ ModularGroup.fd) :
    ‖theta10Fun τ‖ ≤ 3 := by
  obtain ⟨-, hup⟩ := ratio_norm_bounds_fd τ hτ
  have htheta : ‖theta10Fun τ‖
      = Real.exp (-(Real.pi * τ.im / 4)) * ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)‖ := by
    simp only [theta10Fun]
    rw [norm_mul, norm_exp_pi_I_div_four]
  rw [htheta]
  have he1 : Real.exp (-(Real.pi * τ.im / 4)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, τ.im_pos]
  have hnn : 0 ≤ ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)‖ := norm_nonneg _
  nlinarith

lemma thetaVec_ne_zero (j : Fin 3) (τ : ℍ) : thetaVec j τ ≠ 0 := by
  fin_cases j
  · simp only [thetaVec]
    exact theta00Fun_ne_zero τ
  · simp only [thetaVec]
    exact theta01Fun_ne_zero τ
  · simp only [thetaVec]
    exact theta10Fun_ne_zero τ

lemma thetaVec_fd_bounds (τ : ℍ) (hτ : τ ∈ ModularGroup.fd) (j : Fin 3) :
    (1 / 2) * Real.exp (-(Real.pi * τ.im / 4)) ≤ ‖thetaVec j τ‖ ∧
      ‖thetaVec j τ‖ ≤ 3 := by
  have he1 : Real.exp (-(Real.pi * τ.im / 4)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, τ.im_pos]
  have hfl : (1 / 2) * Real.exp (-(Real.pi * τ.im / 4)) ≤ 1 / 2 := by nlinarith [he1]
  fin_cases j
  · change (1 / 2) * Real.exp (-(Real.pi * τ.im / 4)) ≤ ‖theta00Fun τ‖ ∧
      ‖theta00Fun τ‖ ≤ 3
    exact ⟨le_trans hfl (theta00Fun_fd_lower τ hτ), theta00Fun_fd_upper τ hτ⟩
  · change (1 / 2) * Real.exp (-(Real.pi * τ.im / 4)) ≤ ‖theta01Fun τ‖ ∧
      ‖theta01Fun τ‖ ≤ 3
    exact ⟨le_trans hfl (theta01Fun_fd_lower τ hτ), theta01Fun_fd_upper τ hτ⟩
  · change (1 / 2) * Real.exp (-(Real.pi * τ.im / 4)) ≤ ‖theta10Fun τ‖ ∧
      ‖theta10Fun τ‖ ≤ 3
    exact ⟨theta10Fun_fd_lower τ hτ, theta10Fun_fd_upper τ hτ⟩

/-- Logarithmic bound for a single theta coordinate on the fundamental domain. -/
lemma thetaVec_log_bound (τ : ℍ) (hτ : τ ∈ ModularGroup.fd) (j : Fin 3) :
    |Real.log ‖thetaVec j τ‖| ≤ Real.pi * τ.im / 4 + Real.log 3 := by
  obtain ⟨hlo, hup⟩ := thetaVec_fd_bounds τ hτ j
  have hpos : 0 < ‖thetaVec j τ‖ := lt_of_lt_of_le (by positivity) hlo
  rw [abs_le]
  constructor
  · have h1 : Real.log ((1 / 2) * Real.exp (-(Real.pi * τ.im / 4)))
        ≤ Real.log ‖thetaVec j τ‖ :=
      Real.log_le_log (by positivity) hlo
    have h2 : Real.log ((1 / 2) * Real.exp (-(Real.pi * τ.im / 4)))
        = -(Real.pi * τ.im / 4) - Real.log 2 := by
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp,
        Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
      ring
    have h3 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
    linarith
  · have h1 : Real.log ‖thetaVec j τ‖ ≤ Real.log 3 := Real.log_le_log hpos hup
    have h2 : 0 ≤ Real.pi * τ.im / 4 := by positivity
    linarith

/-! ## The imaginary part of a reduction to the fundamental domain -/

lemma im_smul_le_max_of_mem_fd (γ : SL(2,ℤ)) (τ : ℍ) :
    (γ • τ).im ≤ max τ.im ((τ.im)⁻¹) := by
  rw [ModularGroup.im_smul_eq_div_normSq, denom_apply]
  by_cases hc : γ 1 0 = 0
  · have hd : γ 1 1 ≠ 0 := fun hd => by
      have hdet : (↑γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.det_coe
      rw [Matrix.det_fin_two] at hdet
      rw [hc, hd] at hdet
      norm_num at hdet
    have hN : Complex.normSq (↑(γ 1 0) * ↑τ + ↑(γ 1 1)) = ((γ 1 1 : ℤ) : ℝ)^2 := by
      have h1 : (↑(γ 1 0) : ℂ) = 0 := by rw [hc]; simp
      rw [h1, zero_mul, zero_add]
      have h2 : (↑(γ 1 1) : ℂ) = (((γ 1 1 : ℤ) : ℝ) : ℂ) := by push_cast; ring
      rw [h2, Complex.normSq_ofReal, sq]
    rw [hN]
    have h1 : (1 : ℝ) ≤ ((γ 1 1 : ℤ) : ℝ)^2 := by
      have h1i : (1 : ℤ) ≤ |γ 1 1| := Int.one_le_abs hd
      have h1r : (1 : ℝ) ≤ |((γ 1 1 : ℤ) : ℝ)| := by exact_mod_cast h1i
      rw [← sq_abs]; nlinarith [h1r]
    calc τ.im / ((γ 1 1 : ℤ) : ℝ)^2 ≤ τ.im / 1 :=
          div_le_div_of_nonneg_left (le_of_lt τ.im_pos) (by norm_num) h1
      _ = τ.im := by ring
      _ ≤ max τ.im ((τ.im)⁻¹) := le_max_left _ _
  · have hcsq : (1 : ℝ) ≤ (((γ 1 0 : ℤ) : ℝ))^2 := by
      have h1i : (1 : ℤ) ≤ |γ 1 0| := Int.one_le_abs hc
      have h1r : (1 : ℝ) ≤ |((γ 1 0 : ℤ) : ℝ)| := by exact_mod_cast h1i
      rw [← sq_abs]; nlinarith [h1r]
    have hcm' : (((γ 1 0 : ℤ) : ℝ) * τ.im)^2
        ≤ Complex.normSq (↑(γ 1 0) * ↑τ + ↑(γ 1 1)) := by
      have hcm := UpperHalfPlane.c_mul_im_sq_le_normSq_denom
        (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ)) τ
      simpa [denom_apply] using hcm
    have hN : τ.im^2 ≤ Complex.normSq (↑(γ 1 0) * ↑τ + ↑(γ 1 1)) := by
      nlinarith [hcm', hcsq, τ.im_pos, sq_nonneg τ.im]
    have hNpos : 0 < Complex.normSq (↑(γ 1 0) * ↑τ + ↑(γ 1 1)) := by nlinarith [τ.im_pos]
    have hinv : (Complex.normSq (↑(γ 1 0) * ↑τ + ↑(γ 1 1)))⁻¹ ≤ (τ.im^2)⁻¹ :=
      (inv_le_inv₀ hNpos (by positivity)).mpr hN
    have hle : τ.im / Complex.normSq (↑(γ 1 0) * ↑τ + ↑(γ 1 1)) ≤ (τ.im)⁻¹ := by
      calc τ.im / Complex.normSq (↑(γ 1 0) * ↑τ + ↑(γ 1 1))
          = τ.im * (Complex.normSq (↑(γ 1 0) * ↑τ + ↑(γ 1 1)))⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ τ.im * (τ.im^2)⁻¹ := mul_le_mul_of_nonneg_left hinv (le_of_lt τ.im_pos)
        _ = (τ.im)⁻¹ := by field_simp
    exact le_trans hle (le_max_right _ _)

/-! ## The logarithmic growth of `λ` -/

lemma log_lambdaFun_bound (γ : SL(2,ℤ)) (τ : ℍ) (σ : Fin 3 ≃ Fin 3)
    (hσ : ∀ (τ : ℍ) (k : Fin 3), ‖thetaVec (σ k) (γ • τ)‖
      = ‖jFun γ (τ : ℂ)‖ ^ (1 / 2 : ℝ) * ‖thetaVec k τ‖)
    (hfd : γ • τ ∈ ModularGroup.fd) :
    |Real.log ‖lambdaFun τ‖| ≤ 2 * Real.pi * (γ • τ).im + 8 * Real.log 3 := by
  set τ₀ : ℍ := γ • τ with hτ₀def
  have hσ' : ∀ k : Fin 3, ‖thetaVec (σ k) τ₀‖
      = ‖jFun γ (τ : ℂ)‖ ^ (1 / 2 : ℝ) * ‖thetaVec k τ‖ := by
    intro k; rw [hτ₀def]; exact hσ τ k
  have hB2 : ‖thetaVec (σ 2) τ₀‖ ≠ 0 := (norm_pos_iff.mpr (thetaVec_ne_zero _ τ₀)).ne'
  have hB0 : ‖thetaVec (σ 0) τ₀‖ ≠ 0 := (norm_pos_iff.mpr (thetaVec_ne_zero _ τ₀)).ne'
  have hA0 : ‖thetaVec 0 τ‖ ≠ 0 := (norm_pos_iff.mpr (thetaVec_ne_zero _ τ)).ne'
  have hAB : ‖thetaVec (σ 2) τ₀‖ * ‖thetaVec 0 τ‖
      = ‖thetaVec 2 τ‖ * ‖thetaVec (σ 0) τ₀‖ := by
    rw [hσ' 2, hσ' 0]; ring
  have hratio : ‖thetaVec (σ 2) τ₀‖ / ‖thetaVec (σ 0) τ₀‖
      = ‖thetaVec 2 τ‖ / ‖thetaVec 0 τ‖ := by
    rw [div_eq_div_iff hB0 hA0]; exact hAB
  have hnorm1 : ‖lambdaFun τ‖ = (‖thetaVec 2 τ‖ / ‖thetaVec 0 τ‖)^4 := by
    rw [lambdaFun, VFun, UFun, thetaVec_zero, thetaVec_two, norm_div, norm_pow, norm_pow,
      div_pow]
  have hnorm : ‖lambdaFun τ‖ = (‖thetaVec (σ 2) τ₀‖ / ‖thetaVec (σ 0) τ₀‖)^4 := by
    rw [hnorm1, hratio]
  have hlog : Real.log ‖lambdaFun τ‖
      = 4 * (Real.log ‖thetaVec (σ 2) τ₀‖ - Real.log ‖thetaVec (σ 0) τ₀‖) := by
    rw [hnorm, Real.log_pow, Real.log_div hB2 hB0]
    ring
  have hbA := thetaVec_log_bound τ₀ (by rw [hτ₀def]; exact hfd) (σ 2)
  have hbB := thetaVec_log_bound τ₀ (by rw [hτ₀def]; exact hfd) (σ 0)
  have hyim : τ₀.im = (γ • τ).im := by rw [hτ₀def]
  calc |Real.log ‖lambdaFun τ‖|
      = |4 * (Real.log ‖thetaVec (σ 2) τ₀‖ - Real.log ‖thetaVec (σ 0) τ₀‖)| := by rw [hlog]
    _ = 4 * |Real.log ‖thetaVec (σ 2) τ₀‖ - Real.log ‖thetaVec (σ 0) τ₀‖| := by
        rw [abs_mul]; norm_num
    _ ≤ 4 * (|Real.log ‖thetaVec (σ 2) τ₀‖| + |Real.log ‖thetaVec (σ 0) τ₀‖|) := by
        have h' : |Real.log ‖thetaVec (σ 2) τ₀‖ - Real.log ‖thetaVec (σ 0) τ₀‖|
            ≤ |Real.log ‖thetaVec (σ 2) τ₀‖| + |Real.log ‖thetaVec (σ 0) τ₀‖| := by
          have h := abs_sub_le (Real.log ‖thetaVec (σ 2) τ₀‖) 0
            (Real.log ‖thetaVec (σ 0) τ₀‖)
          simpa using h
        exact mul_le_mul_of_nonneg_left h' (by norm_num)
    _ ≤ 4 * ((Real.pi * τ₀.im / 4 + Real.log 3) + (Real.pi * τ₀.im / 4 + Real.log 3)) := by
        apply mul_le_mul_of_nonneg_left (add_le_add hbA hbB) (by norm_num)
    _ = 2 * Real.pi * τ₀.im + 8 * Real.log 3 := by ring
    _ = 2 * Real.pi * (γ • τ).im + 8 * Real.log 3 := by rw [hyim]


/-! ## The main bound -/

theorem Lfun_re_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z ∈ Work.Kernels.LogLambda.U →
    |(Work.Kernels.LogLambda.Lfun z).re| ≤ C * (1 + (z.im)⁻¹ + ‖z‖) := by
  refine ⟨2 * Real.pi + 8 * Real.log 3 + 1, by positivity, ?_⟩
  intro z hz
  have hexp : Complex.exp (Work.Kernels.LogLambda.Lfun z) = Work.Kernels.LogLambda.lamC z :=
    Lfun_spec.2.1 z hz
  have hre : (Work.Kernels.LogLambda.Lfun z).re
      = Real.log ‖Work.Kernels.LogLambda.lamC z‖ := by
    have h1 : Real.exp (Work.Kernels.LogLambda.Lfun z).re
        = ‖Work.Kernels.LogLambda.lamC z‖ := by
      rw [← Complex.norm_exp, hexp]
    rw [← h1, Real.log_exp]
  rw [hre]
  set τ : ℍ := ⟨z, hz⟩ with hτdef
  have hlam : Work.Kernels.LogLambda.lamC z = lambdaFun τ := rfl
  rw [hlam]
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  obtain ⟨σ, hσ⟩ := ThetaLower.theta_smul_SL2 γ
  have hb := log_lambdaFun_bound γ τ σ hσ hγ
  have hy0le : (γ • τ).im ≤ max τ.im ((τ.im)⁻¹) := im_smul_le_max_of_mem_fd γ τ
  have hmax : (γ • τ).im ≤ τ.im + (τ.im)⁻¹ :=
    le_trans hy0le (max_le (le_add_of_nonneg_right (inv_nonneg.mpr τ.im_pos.le))
      (le_add_of_nonneg_left τ.im_pos.le))
  have himnorm : τ.im ≤ ‖(τ : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (τ : ℂ)
    rw [UpperHalfPlane.coe_im, abs_of_pos τ.im_pos] at h
    exact h
  have hinvnn : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr τ.im_pos.le
  have hM1 : 1 ≤ 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := by
    have h1 : 0 ≤ (τ.im)⁻¹ := hinvnn
    have h2 : 0 ≤ ‖(τ : ℂ)‖ := norm_nonneg _
    linarith
  have hbc : τ.im + (τ.im)⁻¹ ≤ 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := by
    linarith [himnorm, hinvnn]
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hprod : 0 ≤ 8 * Real.log 3 * ((1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖) - 1) :=
    mul_nonneg (by linarith : (0 : ℝ) ≤ 8 * Real.log 3)
      (by linarith : (0 : ℝ) ≤ (1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖) - 1)
  calc |Real.log ‖lambdaFun τ‖| ≤ 2 * Real.pi * (γ • τ).im + 8 * Real.log 3 := hb
    _ ≤ 2 * Real.pi * (τ.im + (τ.im)⁻¹) + 8 * Real.log 3 := by
        have h := mul_le_mul_of_nonneg_left hmax (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
        linarith
    _ ≤ 2 * Real.pi * (1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖) + 8 * Real.log 3 := by
        have h := mul_le_mul_of_nonneg_left hbc (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
        linarith
    _ ≤ (2 * Real.pi + 8 * Real.log 3 + 1) * (1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖) := by
        nlinarith [hM1, hlog3, hprod, Real.pi_pos]

end Work.Kernels.LogLambda.LogGrowth

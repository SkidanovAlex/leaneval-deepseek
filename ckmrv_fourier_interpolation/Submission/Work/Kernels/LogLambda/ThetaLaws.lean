/-
# Transformation laws of Jacobi's theta functions `θ₀₀`, `θ₀₁`, `θ₁₀`

This file records the classical transformation laws of the three theta functions

* `θ₀₀ τ = ∑_n exp (π i n² τ)` (`Work.Kernels.theta00Fun`),
* `θ₀₁ τ = ∑_n (-1)^n exp (π i n² τ)` (`Work.Kernels.theta01Fun`),
* `θ₁₀ τ = ∑_n exp (π i (n + 1/2)² τ)` (`Work.Kernels.theta10Fun`),

under the two generators `S : τ ↦ -1/τ` and `T : τ ↦ τ + 1` of `SL(2,ℤ)`:

* `θ₀₀(T τ) = θ₀₁(τ)`, `θ₀₁(T τ) = θ₀₀(τ)`, `θ₁₀(T τ) = exp (π i/4) θ₁₀(τ)`;
* `θ₀₀(S τ) = (-iτ)^{1/2} θ₀₀(τ)`, `θ₀₁(S τ) = (-iτ)^{1/2} θ₁₀(τ)`,
  `θ₁₀(S τ) = (-iτ)^{1/2} θ₀₁(τ)`.

The `S`-laws are proved from Mathlib's functional equation `jacobiTheta₂_functional_equation`
for the two-variable theta function, the `T`-laws directly from the defining series.
-/
import Mathlib
import Submission.Work.Kernels.Classical

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Complex Set Filter Topology
open scoped Modular

namespace Work.Kernels

/-! ## Elementary facts about `exp (π i m)` for integers `m` -/

/-- `exp (π i m) = 1` when `m` is even. -/
lemma cexp_pi_I_int_eq_one {m : ℤ} (hm : Even m) : Complex.exp (Real.pi * Complex.I * m) = 1 := by
  obtain ⟨k, rfl⟩ := hm
  have : (Real.pi : ℂ) * Complex.I * ↑(k + k) = ↑k * (2 * ↑Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma even_int_sq_sub (n : ℤ) : Even (n^2 - n) := by
  rw [show n^2 - n = n * (n-1) by ring]; exact Int.even_mul_pred_self n

lemma even_int_sq_add (n : ℤ) : Even (n^2 + n) := by
  rw [show n^2 + n = n * (n+1) by ring]; exact Int.even_mul_succ_self n

/-- The vector `(θ₀₀, θ₀₁, θ₁₀)` of the three Jacobi theta functions. -/
def thetaVec : Fin 3 → ℍ → ℂ := ![theta00Fun, theta01Fun, theta10Fun]

@[simp] lemma thetaVec_zero : thetaVec 0 = theta00Fun := rfl
@[simp] lemma thetaVec_one : thetaVec 1 = theta01Fun := rfl
@[simp] lemma thetaVec_two : thetaVec 2 = theta10Fun := rfl

lemma thetaVec_apply (j : Fin 3) (τ : ℍ) :
    thetaVec j τ = ![theta00Fun, theta01Fun, theta10Fun] j τ := rfl

/-! ## The images of `τ` under `T` and `S` -/

lemma coe_T_smul (τ : ℍ) : ((ModularGroup.T • τ : ℍ) : ℂ) = (τ:ℂ) + 1 := by
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]; norm_num; ring

lemma coe_S_smul (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = (-(τ:ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul]

/-! ## The `T`-laws -/

/-- `θ₀₀(τ+1) = θ₀₁(τ)`. -/
lemma theta00Fun_T (τ : ℍ) : theta00Fun (ModularGroup.T • τ) = theta01Fun τ := by
  show jacobiTheta (((T • τ : ℍ)) : ℂ) = jacobiTheta₂ (1/2) (τ:ℂ)
  rw [coe_T_smul, jacobiTheta_eq_jacobiTheta₂]
  rw [← (hasSum_jacobiTheta₂_term (1/2 : ℂ) τ.im_pos).tsum_eq]
  apply tsum_congr
  intro n
  simp only [jacobiTheta₂_term]
  have he : (2 * ↑Real.pi * Complex.I * ↑n * (0:ℂ) + ↑Real.pi * Complex.I * ↑n ^ 2 * ((τ:ℂ)+1))
      = (2 * ↑Real.pi * Complex.I * ↑n * (1/2:ℂ) + ↑Real.pi * Complex.I * ↑n ^ 2 * (τ:ℂ))
        + (↑Real.pi * Complex.I * ((n^2 - n : ℤ) : ℂ)) := by
    push_cast; ring
  rw [he, Complex.exp_add, cexp_pi_I_int_eq_one (even_int_sq_sub n), mul_one]

/-- `θ₀₁(τ+1) = θ₀₀(τ)`. -/
lemma theta01Fun_T (τ : ℍ) : theta01Fun (ModularGroup.T • τ) = theta00Fun τ := by
  show jacobiTheta₂ (1/2) (((T • τ : ℍ)) : ℂ) = jacobiTheta (τ:ℂ)
  rw [coe_T_smul, jacobiTheta_eq_jacobiTheta₂]
  rw [← (hasSum_jacobiTheta₂_term (0:ℂ) τ.im_pos).tsum_eq]
  apply tsum_congr
  intro n
  simp only [jacobiTheta₂_term]
  have he : (2 * ↑Real.pi * Complex.I * ↑n * (1/2:ℂ) + ↑Real.pi * Complex.I * ↑n ^ 2 * ((τ:ℂ)+1))
      = (2 * ↑Real.pi * Complex.I * ↑n * (0:ℂ) + ↑Real.pi * Complex.I * ↑n ^ 2 * (τ:ℂ))
        + (↑Real.pi * Complex.I * ((n^2 + n : ℤ) : ℂ)) := by
    push_cast; ring
  rw [he, Complex.exp_add, cexp_pi_I_int_eq_one (even_int_sq_add n), mul_one]

/-- `θ₂(z, τ + 1) = θ₂(z + 1/2, τ)`. -/
lemma jacobiTheta₂_add_one_snd (z τ : ℂ) :
    jacobiTheta₂ z (τ+1) = jacobiTheta₂ (z + 1/2) τ := by
  rw [jacobiTheta₂, jacobiTheta₂]
  apply tsum_congr
  intro n
  simp only [jacobiTheta₂_term]
  have he : (2 * ↑Real.pi * Complex.I * ↑n * z + ↑Real.pi * Complex.I * ↑n ^ 2 * (τ+1))
      = (2 * ↑Real.pi * Complex.I * ↑n * (z + 1/2) + ↑Real.pi * Complex.I * ↑n ^ 2 * τ)
        + (↑Real.pi * Complex.I * ((n^2 - n : ℤ) : ℂ)) := by
    push_cast; ring
  rw [he, Complex.exp_add, cexp_pi_I_int_eq_one (even_int_sq_sub n), mul_one]

/-- `θ₁₀(τ+1) = exp (π i / 4) θ₁₀(τ)`. -/
lemma theta10Fun_T (τ : ℍ) :
    theta10Fun (ModularGroup.T • τ) = Complex.exp (Real.pi * Complex.I / 4) * theta10Fun τ := by
  show Complex.exp (Real.pi * Complex.I * (((T • τ : ℍ)) : ℂ) / 4) * jacobiTheta₂ ((((T • τ : ℍ)) : ℂ)/2) (((T • τ : ℍ)) : ℂ)
      = Complex.exp (Real.pi * Complex.I / 4)
        * (Complex.exp (Real.pi * Complex.I * (τ:ℂ)/4) * jacobiTheta₂ ((τ:ℂ)/2) (τ:ℂ))
  rw [coe_T_smul, jacobiTheta₂_add_one_snd]
  rw [show ((τ:ℂ)+1)/2 + 1/2 = (τ:ℂ)/2 + 1 by ring, jacobiTheta₂_add_left]
  rw [show (Real.pi : ℂ) * Complex.I * ((τ:ℂ)+1) / 4 = Real.pi * Complex.I * (τ:ℂ)/4 + Real.pi * Complex.I/4 by ring]
  rw [Complex.exp_add]; ring

/-! ## The `S`-laws -/

lemma arg_ne_pi_of_re_pos {z : ℂ} (h : 0 < z.re) : z.arg ≠ Real.pi := by
  intro harg
  rw [Complex.arg_eq_pi_iff] at harg
  linarith [harg.1]

lemma I_div_tau_re_pos (τ : ℍ) : 0 < (Complex.I / (τ:ℂ)).re := by
  rw [Complex.div_re]
  simp only [Complex.I_re, Complex.I_im, Complex.normSq_apply]
  rw [zero_mul, zero_div, zero_add, one_mul]
  have h1 : 0 < (τ:ℂ).im := τ.im_pos
  exact div_pos h1 (by nlinarith [h1])

lemma coe_tau_ne_zero (τ : ℍ) : (τ:ℂ) ≠ 0 := by
  intro h; have := congr_arg Complex.im h; simp at this
  exact absurd this (ne_of_gt τ.im_pos)

/-- `θ₀₀(-1/τ) = (-iτ)^{1/2} θ₀₀(τ)`. -/
lemma theta00Fun_S (τ : ℍ) :
    theta00Fun (ModularGroup.S • τ) = (-Complex.I * (τ:ℂ))^(1/2:ℂ) * theta00Fun τ :=
  jacobiTheta_S_smul τ

/-- If `A = X * B` and `X ≠ 0` then `B = X⁻¹ * A`. -/
lemma eq_inv_mul_of_eq_mul {A X B : ℂ} (hX : X ≠ 0) (h : A = X * B) : B = X⁻¹ * A := by
  rw [h, ← mul_assoc, inv_mul_cancel₀ hX, one_mul]

/-- `θ₀₁(-1/τ) = (-iτ)^{1/2} θ₁₀(τ)`. -/
lemma theta01Fun_S (τ : ℍ) :
    theta01Fun (ModularGroup.S • τ) = (-Complex.I * (τ:ℂ))^(1/2:ℂ) * theta10Fun τ := by
  have hτ0 : (↑τ : ℂ) ≠ 0 := coe_tau_ne_zero τ
  have hu : (-Complex.I * (↑τ : ℂ)) ^ (1/2:ℂ) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)]
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ0
  set u := (-Complex.I * (↑τ : ℂ)) ^ (1/2:ℂ) with hud
  set e := Complex.exp (-(↑Real.pi * Complex.I * ↑τ / 4)) with hed
  have hu' : u ≠ 0 := hu
  have he' : e ≠ 0 := Complex.exp_ne_zero _
  have hFE := jacobiTheta₂_functional_equation ((τ:ℂ)/2) (τ:ℂ)
  have hFE' : jacobiTheta₂ ((τ:ℂ)/2) (τ:ℂ)
      = u⁻¹ * e * jacobiTheta₂ (1/2) ((-(τ:ℂ))⁻¹) := by
    rw [hFE, show ((τ:ℂ)/2)/(τ:ℂ) = 1/2 by field_simp,
      show (-1/↑τ : ℂ) = (-(τ:ℂ))⁻¹ by rw [neg_div, one_div, inv_neg],
      show -↑Real.pi*Complex.I*((τ:ℂ)/2)^2/(τ:ℂ) = -(↑Real.pi*Complex.I*↑τ/4) by
        field_simp; ring]
    rw [one_div]
  have hB : jacobiTheta₂ (1/2) ((-(τ:ℂ))⁻¹)
      = (u⁻¹ * e)⁻¹ * jacobiTheta₂ ((τ:ℂ)/2) (τ:ℂ) :=
    eq_inv_mul_of_eq_mul (mul_ne_zero (inv_ne_zero hu') he') hFE'
  have hXinv : (u⁻¹ * e)⁻¹ = u * Complex.exp (↑Real.pi*Complex.I*↑τ/4) := by
    rw [mul_inv_rev, inv_inv, hed, ← Complex.exp_neg]
    ring_nf
  show jacobiTheta₂ (1/2) (((S • τ : ℍ)) : ℂ)
      = (-Complex.I * (↑τ : ℂ)) ^ (1/2:ℂ)
        * (Complex.exp (↑Real.pi * Complex.I * ↑τ / 4) * jacobiTheta₂ (↑τ / 2) ↑τ)
  rw [coe_S_smul, hB, hXinv, hud]
  ring

/-- `θ₁₀(-1/τ) = (-iτ)^{1/2} θ₀₁(τ)`. -/
lemma theta10Fun_S (τ : ℍ) :
    theta10Fun (ModularGroup.S • τ) = (-Complex.I * (τ:ℂ))^(1/2:ℂ) * theta01Fun τ := by
  have hτ0 : (↑τ : ℂ) ≠ 0 := coe_tau_ne_zero τ
  have harg : (Complex.I / (τ:ℂ)).arg ≠ Real.pi := arg_ne_pi_of_re_pos (I_div_tau_re_pos τ)
  have hinvτ : (Complex.I / (τ:ℂ))⁻¹ = -Complex.I * (↑τ : ℂ) := by
    field_simp; rw [Complex.I_sq]; ring
  set σ := (-(↑τ : ℂ))⁻¹ with hσd
  have hσ0 : σ ≠ 0 := by rw [hσd]; exact inv_ne_zero (neg_ne_zero.mpr hτ0)
  have hSz : ((ModularGroup.S • τ : ℍ) : ℂ) = σ := coe_S_smul τ
  have hστ : -Complex.I * σ = Complex.I / (τ:ℂ) := by rw [hσd]; field_simp
  set B := jacobiTheta₂ (1/2) (↑τ) with hBd
  have hFE := jacobiTheta₂_functional_equation (σ/2) σ
  have hFE' : jacobiTheta₂ (σ/2) σ
      = ((-Complex.I*σ)^(1/2:ℂ))⁻¹ * Complex.exp (-(↑Real.pi*Complex.I*σ/4)) * B := by
    rw [hFE, show (σ/2)/σ = 1/2 by field_simp,
      show -1/σ = ↑τ by rw [hσd]; field_simp,
      show -↑Real.pi*Complex.I*(σ/2)^2/σ = -(↑Real.pi*Complex.I*σ/4) by field_simp; ring,
      one_div]
  have hcancel : Complex.exp (↑Real.pi*Complex.I*σ/4) * Complex.exp (-(↑Real.pi*Complex.I*σ/4)) = 1 := by
    rw [← Complex.exp_add]; ring_nf; simp
  have hfin : ((-Complex.I*σ)^(1/2:ℂ))⁻¹ = (-Complex.I * (↑τ:ℂ))^(1/2:ℂ) := by
    rw [hστ, ← Complex.inv_cpow _ _ harg, hinvτ]
  show Complex.exp (↑Real.pi*Complex.I*(((S•τ:ℍ)):ℂ)/4) * jacobiTheta₂ ((((S•τ:ℍ)):ℂ)/2) (((S•τ:ℍ)):ℂ)
      = (-Complex.I * (↑τ:ℂ))^(1/2:ℂ) * jacobiTheta₂ (1/2) ↑τ
  rw [hSz]
  calc Complex.exp (↑Real.pi*Complex.I*σ/4) * jacobiTheta₂ (σ/2) σ
      = Complex.exp (↑Real.pi*Complex.I*σ/4)
        * (((-Complex.I*σ)^(1/2:ℂ))⁻¹ * Complex.exp (-(↑Real.pi*Complex.I*σ/4)) * B) := by rw [hFE']
    _ = ((-Complex.I*σ)^(1/2:ℂ))⁻¹
        * (Complex.exp (↑Real.pi*Complex.I*σ/4) * Complex.exp (-(↑Real.pi*Complex.I*σ/4))) * B := by ring
    _ = ((-Complex.I*σ)^(1/2:ℂ))⁻¹ * B := by rw [hcancel, mul_one]
    _ = (-Complex.I * (↑τ:ℂ))^(1/2:ℂ) * jacobiTheta₂ (1/2) ↑τ := by rw [hfin, hBd]

end Work.Kernels

import Mathlib
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.Funnel_Kfun_diag_bound
import Submission.Work.Kernels.Kernels
import Submission.Work.Modular.E2_S_smul

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics

noncomputable section

open Work.Kernels

set_option maxHeartbeats 4000000

/-! ## The `S`-transformation laws in the direction used below -/

/-- `S • (S • τ) = τ`. -/
lemma S_smul_S_smul (τ : ℍ) : ModularGroup.S • (ModularGroup.S • τ) = τ := by
  apply UpperHalfPlane.ext
  rw [S_smul_coe, S_smul_coe]
  simp

/-- `E₄(τ) = w⁴ E₄(w)` for `w = S • τ`. -/
lemma E4Fun_S_smul' (τ : ℍ) :
    E4Fun τ = (((ModularGroup.S • τ : ℍ)) : ℂ) ^ 4 * E4Fun (ModularGroup.S • τ) := by
  have h := KernelFacts.smul_of_slash_inv KernelFacts.E4Fun_S_slash (ModularGroup.S • τ)
  rw [S_smul_S_smul] at h
  exact h

/-- `E₆(τ) = w⁶ E₆(w)` for `w = S • τ`. -/
lemma E6Fun_S_smul' (τ : ℍ) :
    E6Fun τ = (((ModularGroup.S • τ : ℍ)) : ℂ) ^ 6 * E6Fun (ModularGroup.S • τ) := by
  have h := KernelFacts.smul_of_slash_inv KernelFacts.E6Fun_S_slash (ModularGroup.S • τ)
  rw [S_smul_S_smul] at h
  exact h

/-- `Δ(τ) = w¹² Δ(w)` for `w = S • τ`. -/
lemma DeltaFun_S_smul' (τ : ℍ) :
    DeltaFun τ = (((ModularGroup.S • τ : ℍ)) : ℂ) ^ 12 * DeltaFun (ModularGroup.S • τ) := by
  have h := KernelFacts.smul_of_slash_inv KernelFacts.DeltaFun_S_slash (ModularGroup.S • τ)
  rw [S_smul_S_smul] at h
  exact h

/-- `E₂(τ) = w² E₂(w) - 6 i w / π` for `w = S • τ`. -/
lemma E2Fun_S_smul' (τ : ℍ) :
    E2Fun τ = (((ModularGroup.S • τ : ℍ)) : ℂ) ^ 2 * E2Fun (ModularGroup.S • τ)
      - 6 * Complex.I * (((ModularGroup.S • τ : ℍ)) : ℂ) / Real.pi := by
  have h := Work.Modular.E2_S_smul (ModularGroup.S • τ)
  rw [S_smul_S_smul] at h
  exact h

/-- `j(τ) = j(w)` for `w = S • τ`. -/
lemma jInvariantFun_S_smul' (τ : ℍ) :
    jInvariantFun τ = jInvariantFun (ModularGroup.S • τ) :=
  (KernelFacts.jInvariantFun_S_smul τ).symm

/-- `(τ : ℂ) = -1/w` for `w = S • τ`. -/
lemma coe_eq_neg_inv_S_smul (τ : ℍ) :
    (τ : ℂ) = -(((ModularGroup.S • τ : ℍ)) : ℂ)⁻¹ := by
  have h := S_smul_coe (ModularGroup.S • τ)
  rw [S_smul_S_smul] at h
  exact h

/-- `‖w‖ ≤ scale τ` for `w = S • τ`. -/
lemma norm_coe_S_smul_le_scale (τ : ℍ) :
    ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ≤ scale τ := by
  rw [S_smul_coe, norm_neg, norm_inv]
  have him : τ.im ≤ ‖(τ : ℂ)‖ := im_le_coe_norm τ
  have h2 : (‖(τ : ℂ)‖)⁻¹ ≤ (τ.im)⁻¹ := inv_anti₀ τ.im_pos him
  exact le_trans h2 (inv_im_le_scale τ)

/-! ## The two cusp-atoms `Ξ₈` is built from -/

/-- `N₁(τ) = E₄E₆ - 2E₂E₄² + E₂²E₆`, the numerator of the large-`j` coefficient. -/
def XiN1 (τ : ℍ) : ℂ :=
  E4Fun τ * E6Fun τ - 2 * E2Fun τ * (E4Fun τ) ^ 2 + (E2Fun τ) ^ 2 * E6Fun τ

/-- `N₂(τ) = E₂E₆ - E₄²`. -/
def XiN2 (τ : ℍ) : ℂ := E2Fun τ * E6Fun τ - (E4Fun τ) ^ 2

lemma XiN2_isBigOq : IsBigOq XiN2 1 := by
  refine IsBigOq.congr (eps_isBigOq.neg) (fun τ => ?_)
  simp only [XiN2]
  ring

lemma XiN1_isBigOq : IsBigOq XiN1 1 := by
  have h2 := E2_minus_one
  have h4 := E4_minus_one
  have h6 := E6_minus_one
  have hA : IsBigOq (fun τ : ℍ => -3 * (E4Fun τ - 1)) 1 := h4.const_mul (-3)
  have hB : IsBigOq (fun τ : ℍ => 2 * (E6Fun τ - 1)) 1 := h6.const_mul (2)
  have hC : IsBigOq (fun τ : ℍ => (E2Fun τ - 1) ^ 2) 2 := by
    have h := h2.mul h2
    refine IsBigOq.congr h (fun τ => ?_); ring
  have hD : IsBigOq (fun τ : ℍ => (E4Fun τ - 1) * (E6Fun τ - 1)) 2 := h4.mul h6
  have hE : IsBigOq (fun τ : ℍ => -4 * ((E2Fun τ - 1) * (E4Fun τ - 1))) 2 :=
    (h2.mul h4).const_mul (-4)
  have hF : IsBigOq (fun τ : ℍ => -2 * ((E4Fun τ - 1) ^ 2)) 2 := by
    have h := (h4.mul h4).const_mul (-2)
    refine IsBigOq.congr h (fun τ => ?_); ring
  have hG : IsBigOq (fun τ : ℍ => -2 * ((E2Fun τ - 1) * (E4Fun τ - 1) ^ 2)) 3 := by
    have h := (h2.mul (h4.mul h4)).const_mul (-2)
    refine IsBigOq.congr h (fun τ => ?_); ring
  have hH : IsBigOq (fun τ : ℍ => 2 * ((E2Fun τ - 1) * (E6Fun τ - 1))) 2 :=
    (h2.mul h6).const_mul 2
  have hI : IsBigOq (fun τ : ℍ => (E2Fun τ - 1) ^ 2 * (E6Fun τ - 1)) 3 := by
    have h := (h2.mul h2).mul h6
    refine IsBigOq.congr h (fun τ => ?_); ring
  have h := ((((((hA.add hB).add hC).add hD).add hE).add hF).add hG).add (hH.add hI)
  refine IsBigOq.congr h (fun τ => ?_)
  simp only [XiN1]
  ring


/-! ## Expansion of `Ξ₈` in the coordinates `τ`, `z` -/

lemma Xi8_expand (τ z : ℍ) :
    Xi8 τ z
      = (τ : ℂ) * E6Fun τ * DeltaFun z * (jInvariantFun τ - jInvariantFun z)
        - 2 * phi0 τ * E4Fun τ * DeltaFun z * (jInvariantFun τ - jInvariantFun z)
        + (τ : ℂ) * E6Fun τ * (E4Fun z) ^ 2 * (E2Fun z) ^ 2
        - 2 * phi0 τ * E4Fun τ * E4Fun z * E6Fun z * E2Fun z
        + phi2 τ * (E14Fun τ / DeltaFun τ) * DeltaFun z := by
  have hΔ : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hΔτ : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hfk12 : fk (12 : ℤ) z = DeltaFun z := by simp [Work.Kernels.fk]
  have hfk10 : fk (10 : ℤ) z = E10Fun z := by simp [Work.Kernels.fk]
  have hfk8 : fk (8 : ℤ) z = E8Fun z := by simp [Work.Kernels.fk]
  have hfk6 : fk (6 : ℤ) τ = E6Fun τ := by simp [Work.Kernels.fk]
  have hfk4 : fk (4 : ℤ) τ = E4Fun τ := by simp [Work.Kernels.fk]
  have hfk2 : fk (2 : ℤ) τ = E14Fun τ / DeltaFun τ := by simp [Work.Kernels.fk]
  have hE8 : E8Fun z = E4Fun z ^ 2 := rfl
  have hE10 : E10Fun z = E4Fun z * E6Fun z := rfl
  simp only [Xi8, Fin.sum_univ_three, phiVec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply, Fin.val_zero,
    Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one]
  rw [hfk12, hfk10, hfk8, hfk6, hfk4, hfk2, hE8, hE10]
  simp only [phi0, phi2, phiNeg2, E14Fun, jInvariantFun]
  field_simp
  ring_nf

/-! ## The decomposition of `Ξ₈` in terms of the `S`-image of `τ` -/

lemma Xi8_S_decomposition (τ z : ℍ) :
    Xi8 τ z
      = (DeltaFun z * (E4Fun (ModularGroup.S • τ)) ^ 2 / DeltaFun (ModularGroup.S • τ)) *
          (- (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 5 * XiN1 (ModularGroup.S • τ)
            + (6 * Complex.I / (Real.pi : ℂ)) * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 4 *
              XiN2 (ModularGroup.S • τ))
        + (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 5 * E6Fun (ModularGroup.S • τ) *
            (E4Fun z) ^ 2 * (E4Fun z - (E2Fun z) ^ 2)
        - ((E4Fun z) ^ 2 - E6Fun z * E2Fun z) *
            (2 * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 5 * E2Fun (ModularGroup.S • τ) *
                E4Fun (ModularGroup.S • τ) * E4Fun z
              - 6 * Complex.I * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 4 *
                E4Fun (ModularGroup.S • τ) * E4Fun z / (Real.pi : ℂ)) := by
  have hΔz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hΔw : DeltaFun (ModularGroup.S • τ) ≠ 0 := ClassicalFacts.DeltaFun_ne_zero _
  have hu : (((ModularGroup.S • τ : ℍ)) : ℂ) ≠ 0 := KernelFacts.kpc_tau_ne_zero _
  have hE2 : E2Fun τ = (((ModularGroup.S • τ : ℍ)) : ℂ) ^ 2 * E2Fun (ModularGroup.S • τ)
      - 6 * Complex.I * (((ModularGroup.S • τ : ℍ)) : ℂ) / Real.pi := E2Fun_S_smul' τ
  have hE4 : E4Fun τ = (((ModularGroup.S • τ : ℍ)) : ℂ) ^ 4 * E4Fun (ModularGroup.S • τ) :=
    E4Fun_S_smul' τ
  have hE6 : E6Fun τ = (((ModularGroup.S • τ : ℍ)) : ℂ) ^ 6 * E6Fun (ModularGroup.S • τ) :=
    E6Fun_S_smul' τ
  have hD : DeltaFun τ = (((ModularGroup.S • τ : ℍ)) : ℂ) ^ 12 *
      DeltaFun (ModularGroup.S • τ) := DeltaFun_S_smul' τ
  have hJτ : jInvariantFun τ = E4Fun τ ^ 3 / DeltaFun τ := rfl
  have hJz : jInvariantFun z = E4Fun z ^ 3 / DeltaFun z := rfl
  rw [Xi8_expand, hJτ, hJz]
  simp only [phi0, phi2, E14Fun, XiN1, XiN2]
  rw [hE2, hE4, hE6, hD, coe_eq_neg_inv_S_smul]
  field_simp
  ring_nf


/-- The bound of the problem, on the cusp-`0` tile `E = {τ : 3/2 ≤ im (S•τ)}`. -/
theorem Xi8_bound_E :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : UpperHalfPlane),
      (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im → 1 ≤ z.im →
        ‖Work.Asymptotics.Xi8 τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun z‖ := by
  obtain ⟨C1, hC1, hN1⟩ := XiN1_isBigOq
  obtain ⟨C2, hC2, hN2⟩ := XiN2_isBigOq
  obtain ⟨c0, hc0, hΔlow⟩ := DeltaFun_lower
  obtain ⟨Cq, hCq, hΔz_bd⟩ := DeltaFun_isBigOq_one
  obtain ⟨Cs, hCs, hσ⟩ := delta1_isBigOq
  obtain ⟨Ce, hCe, hε⟩ := eps_isBigOq
  obtain ⟨CE2, hCE2, hE2b⟩ := E2Fun_bound
  obtain ⟨CE4, hCE4, hE4b⟩ := E4Fun_bound
  obtain ⟨CE6, hCE6, hE6b⟩ := E6Fun_bound
  refine ⟨Cq * CE4 ^ 2 / c0 * (C1 + 6 * C2 / Real.pi)
      + (Cs * CE6 * CE4 ^ 2 + Ce * (2 * CE2 * CE4 ^ 2 + 6 * CE4 ^ 2 / Real.pi)) + 1,
    5, by positivity, by norm_num, fun τ z hτ hz => ?_⟩
  have hw1 : (1 : ℝ) ≤ (ModularGroup.S • τ).im := le_trans (by norm_num) hτ
  have hs1 : (1 : ℝ) ≤ scale τ := Work.Kernels.one_le_scale τ
  have hsc0 : (0 : ℝ) ≤ scale τ := (Work.Kernels.scale_pos τ).le
  have hu : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ≤ scale τ := norm_coe_S_smul_le_scale τ
  have hu0 : (0 : ℝ) ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ := norm_nonneg _
  have hqz0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hqw0 : (0 : ℝ) < ‖qParamFun (ModularGroup.S • τ)‖ :=
    norm_pos_iff.mpr (qParamFun_ne_zero' _)
  have hΔzb : ‖DeltaFun z‖ ≤ Cq * ‖qParamFun z‖ := by simpa using hΔz_bd z hz
  have hσb : ‖E4Fun z - (E2Fun z) ^ 2‖ ≤ Cs * ‖qParamFun z‖ := by simpa using hσ z hz
  have hεb : ‖(E4Fun z) ^ 2 - E6Fun z * E2Fun z‖ ≤ Ce * ‖qParamFun z‖ := by
    simpa using hε z hz
  have hN1b : ‖XiN1 (ModularGroup.S • τ)‖ ≤ C1 * ‖qParamFun (ModularGroup.S • τ)‖ := by
    simpa using hN1 _ hw1
  have hN2b : ‖XiN2 (ModularGroup.S • τ)‖ ≤ C2 * ‖qParamFun (ModularGroup.S • τ)‖ := by
    simpa using hN2 _ hw1
  have hδb : c0 * ‖qParamFun (ModularGroup.S • τ)‖ ≤ ‖DeltaFun (ModularGroup.S • τ)‖ :=
    hΔlow _ hw1
  have hE2wb : ‖E2Fun (ModularGroup.S • τ)‖ ≤ CE2 := hE2b _ hw1
  have hE4wb : ‖E4Fun (ModularGroup.S • τ)‖ ≤ CE4 := hE4b _ hw1
  have hE6wb : ‖E6Fun (ModularGroup.S • τ)‖ ≤ CE6 := hE6b _ hw1
  have hE2zb : ‖E2Fun z‖ ≤ CE2 := hE2b z hz
  have hE4zb : ‖E4Fun z‖ ≤ CE4 := hE4b z hz
  have hE6zb : ‖E6Fun z‖ ≤ CE6 := hE6b z hz
  have hu4 : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 4 ≤ (scale τ) ^ 5 :=
    le_trans (pow_le_pow_left₀ hu0 hu 4) (pow_le_pow_right₀ hs1 (by norm_num))
  have hu5 : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 5 ≤ (scale τ) ^ 5 :=
    pow_le_pow_left₀ hu0 hu 5
  have h6pi : ‖(6 * Complex.I / (Real.pi : ℂ))‖ = 6 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_of_nonneg Real.pi_pos.le]
  -- the three pieces of the decomposition
  let T1 : ℂ := (DeltaFun z * (E4Fun (ModularGroup.S • τ)) ^ 2 / DeltaFun (ModularGroup.S • τ)) *
      (- (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 5 * XiN1 (ModularGroup.S • τ)
        + (6 * Complex.I / (Real.pi : ℂ)) * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 4 *
          XiN2 (ModularGroup.S • τ))
  let T2 : ℂ := (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 5 * E6Fun (ModularGroup.S • τ) *
      (E4Fun z) ^ 2 * (E4Fun z - (E2Fun z) ^ 2)
  let T3 : ℂ := ((E4Fun z) ^ 2 - E6Fun z * E2Fun z) *
      (2 * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 5 * E2Fun (ModularGroup.S • τ) *
          E4Fun (ModularGroup.S • τ) * E4Fun z
        - 6 * Complex.I * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 4 *
          E4Fun (ModularGroup.S • τ) * E4Fun z / (Real.pi : ℂ))
  have hT1 : ‖T1‖ ≤ (Cq * CE4 ^ 2 / c0 * (C1 + 6 * C2 / Real.pi)) * (scale τ) ^ 5 *
      ‖qParamFun z‖ := by
    dsimp only [T1]
    have hΔδ : ‖DeltaFun z * (E4Fun (ModularGroup.S • τ)) ^ 2 / DeltaFun (ModularGroup.S • τ)‖
        ≤ Cq * ‖qParamFun z‖ * CE4 ^ 2 / (c0 * ‖qParamFun (ModularGroup.S • τ)‖) := by
      rw [norm_div, norm_mul, norm_pow]
      have hnum : ‖DeltaFun z‖ * ‖E4Fun (ModularGroup.S • τ)‖ ^ 2
          ≤ Cq * ‖qParamFun z‖ * CE4 ^ 2 :=
        mul_le_mul hΔzb (pow_le_pow_left₀ (norm_nonneg _) hE4wb 2) (by positivity) (by positivity)
      have hinv : (‖DeltaFun (ModularGroup.S • τ)‖)⁻¹
          ≤ (c0 * ‖qParamFun (ModularGroup.S • τ)‖)⁻¹ :=
        inv_anti₀ (mul_pos hc0 hqw0) hδb
      calc ‖DeltaFun z‖ * ‖E4Fun (ModularGroup.S • τ)‖ ^ 2 /
            ‖DeltaFun (ModularGroup.S • τ)‖
          = ‖DeltaFun z‖ * ‖E4Fun (ModularGroup.S • τ)‖ ^ 2 *
              (‖DeltaFun (ModularGroup.S • τ)‖)⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ (Cq * ‖qParamFun z‖ * CE4 ^ 2) *
              (c0 * ‖qParamFun (ModularGroup.S • τ)‖)⁻¹ :=
            mul_le_mul hnum hinv (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
        _ = Cq * ‖qParamFun z‖ * CE4 ^ 2 / (c0 * ‖qParamFun (ModularGroup.S • τ)‖) := by
            rw [div_eq_mul_inv]
    have hbr : ‖- (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 5 * XiN1 (ModularGroup.S • τ)
          + (6 * Complex.I / (Real.pi : ℂ)) * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 4 *
            XiN2 (ModularGroup.S • τ)‖
        ≤ (C1 + 6 * C2 / Real.pi) * (scale τ) ^ 5 * ‖qParamFun (ModularGroup.S • τ)‖ := by
      have h1 : ‖- (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 5 * XiN1 (ModularGroup.S • τ)‖
          ≤ (scale τ) ^ 5 * (C1 * ‖qParamFun (ModularGroup.S • τ)‖) := by
        rw [norm_mul, norm_neg, norm_pow]
        exact mul_le_mul hu5 hN1b (norm_nonneg _) (pow_nonneg hsc0 5)
      have h2 : ‖(6 * Complex.I / (Real.pi : ℂ)) * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 4 *
            XiN2 (ModularGroup.S • τ)‖
          ≤ (6 / Real.pi) * (scale τ) ^ 5 * (C2 * ‖qParamFun (ModularGroup.S • τ)‖) := by
        rw [norm_mul, norm_mul, norm_pow, h6pi]
        exact mul_le_mul (mul_le_mul (le_refl _) hu4 (pow_nonneg (norm_nonneg _) 4)
          (by positivity)) hN2b (norm_nonneg _) (by positivity)
      calc ‖- (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 5 * XiN1 (ModularGroup.S • τ)
            + (6 * Complex.I / (Real.pi : ℂ)) * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 4 *
              XiN2 (ModularGroup.S • τ)‖
          ≤ ‖- (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 5 * XiN1 (ModularGroup.S • τ)‖
            + ‖(6 * Complex.I / (Real.pi : ℂ)) * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 4 *
              XiN2 (ModularGroup.S • τ)‖ := norm_add_le _ _
        _ ≤ (scale τ) ^ 5 * (C1 * ‖qParamFun (ModularGroup.S • τ)‖)
            + (6 / Real.pi) * (scale τ) ^ 5 * (C2 * ‖qParamFun (ModularGroup.S • τ)‖) :=
            add_le_add h1 h2
        _ = (C1 + 6 * C2 / Real.pi) * (scale τ) ^ 5 * ‖qParamFun (ModularGroup.S • τ)‖ := by
            ring
    rw [norm_mul]
    calc ‖DeltaFun z * (E4Fun (ModularGroup.S • τ)) ^ 2 / DeltaFun (ModularGroup.S • τ)‖
          * ‖- (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 5 * XiN1 (ModularGroup.S • τ)
            + (6 * Complex.I / (Real.pi : ℂ)) * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 4 *
              XiN2 (ModularGroup.S • τ)‖
        ≤ (Cq * ‖qParamFun z‖ * CE4 ^ 2 / (c0 * ‖qParamFun (ModularGroup.S • τ)‖))
          * ((C1 + 6 * C2 / Real.pi) * (scale τ) ^ 5
            * ‖qParamFun (ModularGroup.S • τ)‖) :=
          mul_le_mul hΔδ hbr (norm_nonneg _) (by positivity)
      _ = (Cq * CE4 ^ 2 / c0 * (C1 + 6 * C2 / Real.pi)) * (scale τ) ^ 5 * ‖qParamFun z‖ := by
          rw [div_eq_mul_inv]
          field_simp
  have hT2 : ‖T2‖ ≤ (Cs * CE6 * CE4 ^ 2) * (scale τ) ^ 5 * ‖qParamFun z‖ := by
    dsimp only [T2]
    simp only [norm_mul, norm_pow]
    calc ‖(((ModularGroup.S • τ : ℍ) : ℂ))‖ ^ 5 * ‖E6Fun (ModularGroup.S • τ)‖ *
          ‖E4Fun z‖ ^ 2 * ‖E4Fun z - (E2Fun z) ^ 2‖
        ≤ (scale τ) ^ 5 * CE6 * CE4 ^ 2 * (Cs * ‖qParamFun z‖) := by
          have h1 : ‖(((ModularGroup.S • τ : ℍ) : ℂ))‖ ^ 5 * ‖E6Fun (ModularGroup.S • τ)‖
              ≤ (scale τ) ^ 5 * CE6 :=
            mul_le_mul hu5 hE6wb (norm_nonneg _) (pow_nonneg hsc0 5)
          have h2 : (‖(((ModularGroup.S • τ : ℍ) : ℂ))‖ ^ 5 * ‖E6Fun (ModularGroup.S • τ)‖)
              * ‖E4Fun z‖ ^ 2 ≤ ((scale τ) ^ 5 * CE6) * CE4 ^ 2 :=
            mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) hE4zb 2) (by positivity)
              (by positivity)
          exact mul_le_mul h2 hσb (norm_nonneg _) (by positivity)
      _ = (Cs * CE6 * CE4 ^ 2) * (scale τ) ^ 5 * ‖qParamFun z‖ := by ring
  have hT3 : ‖T3‖
      ≤ (Ce * (2 * CE2 * CE4 ^ 2 + 6 * CE4 ^ 2 / Real.pi)) * (scale τ) ^ 5 *
          ‖qParamFun z‖ := by
    dsimp only [T3]
    have hinner : ‖2 * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 5 * E2Fun (ModularGroup.S • τ) *
            E4Fun (ModularGroup.S • τ) * E4Fun z
          - 6 * Complex.I * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 4 *
            E4Fun (ModularGroup.S • τ) * E4Fun z / (Real.pi : ℂ)‖
        ≤ (2 * CE2 * CE4 ^ 2 + 6 * CE4 ^ 2 / Real.pi) * (scale τ) ^ 5 := by
      have h1 : ‖2 * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 5 * E2Fun (ModularGroup.S • τ) *
            E4Fun (ModularGroup.S • τ) * E4Fun z‖
          ≤ 2 * CE2 * CE4 ^ 2 * (scale τ) ^ 5 := by
        simp only [norm_mul, norm_pow, Complex.norm_ofNat]
        calc 2 * ‖(((ModularGroup.S • τ : ℍ) : ℂ))‖ ^ 5 * ‖E2Fun (ModularGroup.S • τ)‖ *
              ‖E4Fun (ModularGroup.S • τ)‖ * ‖E4Fun z‖
            ≤ 2 * (scale τ) ^ 5 * CE2 * CE4 * CE4 := by
              have h1' : 2 * ‖(((ModularGroup.S • τ : ℍ) : ℂ))‖ ^ 5 ≤ 2 * (scale τ) ^ 5 :=
                mul_le_mul_of_nonneg_left hu5 (by norm_num)
              exact mul_le_mul (mul_le_mul (mul_le_mul h1' hE2wb (norm_nonneg _)
                (by positivity)) hE4wb (by positivity) (by positivity)) hE4zb (by positivity)
                (by positivity)
          _ = 2 * CE2 * CE4 ^ 2 * (scale τ) ^ 5 := by ring
      have h2 : ‖6 * Complex.I * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 4 *
            E4Fun (ModularGroup.S • τ) * E4Fun z / (Real.pi : ℂ)‖
          ≤ 6 * CE4 ^ 2 * (scale τ) ^ 5 / Real.pi := by
        simp only [norm_div, norm_mul, norm_pow, Complex.norm_I, mul_one, Complex.norm_ofNat,
          Complex.norm_of_nonneg Real.pi_pos.le]
        have hnum2 : 6 * ‖(((ModularGroup.S • τ : ℍ) : ℂ))‖ ^ 4 *
            ‖E4Fun (ModularGroup.S • τ)‖ * ‖E4Fun z‖ ≤ 6 * CE4 ^ 2 * (scale τ) ^ 5 := by
          have h1' : 6 * ‖(((ModularGroup.S • τ : ℍ) : ℂ))‖ ^ 4 ≤ 6 * (scale τ) ^ 5 :=
            mul_le_mul_of_nonneg_left hu4 (by norm_num)
          have hs : 6 * ‖(((ModularGroup.S • τ : ℍ) : ℂ))‖ ^ 4 *
              ‖E4Fun (ModularGroup.S • τ)‖ ≤ 6 * (scale τ) ^ 5 * CE4 :=
            mul_le_mul h1' hE4wb (norm_nonneg _) (by positivity)
          calc 6 * ‖(((ModularGroup.S • τ : ℍ) : ℂ))‖ ^ 4 * ‖E4Fun (ModularGroup.S • τ)‖ *
                ‖E4Fun z‖ ≤ 6 * (scale τ) ^ 5 * CE4 * CE4 :=
                mul_le_mul hs hE4zb (norm_nonneg _) (by positivity)
            _ = 6 * CE4 ^ 2 * (scale τ) ^ 5 := by ring
        exact div_le_div_of_nonneg_right hnum2 Real.pi_pos.le
      calc ‖2 * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 5 * E2Fun (ModularGroup.S • τ) *
            E4Fun (ModularGroup.S • τ) * E4Fun z
          - 6 * Complex.I * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 4 *
            E4Fun (ModularGroup.S • τ) * E4Fun z / (Real.pi : ℂ)‖
          ≤ ‖2 * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 5 * E2Fun (ModularGroup.S • τ) *
              E4Fun (ModularGroup.S • τ) * E4Fun z‖
            + ‖6 * Complex.I * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 4 *
              E4Fun (ModularGroup.S • τ) * E4Fun z / (Real.pi : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 * CE2 * CE4 ^ 2 * (scale τ) ^ 5 + 6 * CE4 ^ 2 * (scale τ) ^ 5 / Real.pi :=
            add_le_add h1 h2
        _ = (2 * CE2 * CE4 ^ 2 + 6 * CE4 ^ 2 / Real.pi) * (scale τ) ^ 5 := by ring
    rw [norm_mul]
    calc ‖(E4Fun z) ^ 2 - E6Fun z * E2Fun z‖
          * ‖2 * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 5 * E2Fun (ModularGroup.S • τ) *
              E4Fun (ModularGroup.S • τ) * E4Fun z
            - 6 * Complex.I * (((ModularGroup.S • τ : ℍ) : ℂ)) ^ 4 *
              E4Fun (ModularGroup.S • τ) * E4Fun z / (Real.pi : ℂ)‖
        ≤ (Ce * ‖qParamFun z‖) *
            ((2 * CE2 * CE4 ^ 2 + 6 * CE4 ^ 2 / Real.pi) * (scale τ) ^ 5) :=
          mul_le_mul hεb hinner (norm_nonneg _) (by positivity)
      _ = (Ce * (2 * CE2 * CE4 ^ 2 + 6 * CE4 ^ 2 / Real.pi)) * (scale τ) ^ 5 *
            ‖qParamFun z‖ := by ring
  rw [Xi8_S_decomposition τ z]
  change ‖T1 + T2 - T3‖ ≤ (Cq * CE4 ^ 2 / c0 * (C1 + 6 * C2 / Real.pi)
      + (Cs * CE6 * CE4 ^ 2 + Ce * (2 * CE2 * CE4 ^ 2 + 6 * CE4 ^ 2 / Real.pi)) + 1)
      * (scale τ) ^ (5:ℝ) * ‖qParamFun z‖
  have htri : ‖T1 + T2 - T3‖ ≤ ‖T1‖ + ‖T2‖ + ‖T3‖ := by
    calc ‖T1 + T2 - T3‖ ≤ ‖T1 + T2‖ + ‖T3‖ := norm_sub_le _ _
      _ ≤ (‖T1‖ + ‖T2‖) + ‖T3‖ := add_le_add (norm_add_le T1 T2) le_rfl
      _ = ‖T1‖ + ‖T2‖ + ‖T3‖ := by ring
  have h5 : (0:ℝ) ≤ (scale τ) ^ 5 * ‖qParamFun z‖ := by positivity
  calc ‖T1 + T2 - T3‖ ≤ ‖T1‖ + ‖T2‖ + ‖T3‖ := htri
    _ ≤ (Cq * CE4 ^ 2 / c0 * (C1 + 6 * C2 / Real.pi)) * (scale τ) ^ 5 * ‖qParamFun z‖
        + (Cs * CE6 * CE4 ^ 2) * (scale τ) ^ 5 * ‖qParamFun z‖
        + (Ce * (2 * CE2 * CE4 ^ 2 + 6 * CE4 ^ 2 / Real.pi)) * (scale τ) ^ 5
            * ‖qParamFun z‖ := by linarith [hT1, hT2, hT3]
    _ = (Cq * CE4 ^ 2 / c0 * (C1 + 6 * C2 / Real.pi)
        + (Cs * CE6 * CE4 ^ 2 + Ce * (2 * CE2 * CE4 ^ 2 + 6 * CE4 ^ 2 / Real.pi)))
        * (scale τ) ^ 5 * ‖qParamFun z‖ := by ring
    _ ≤ (Cq * CE4 ^ 2 / c0 * (C1 + 6 * C2 / Real.pi)
        + (Cs * CE6 * CE4 ^ 2 + Ce * (2 * CE2 * CE4 ^ 2 + 6 * CE4 ^ 2 / Real.pi)) + 1)
        * (scale τ) ^ 5 * ‖qParamFun z‖ := by nlinarith [h5]
    _ = (Cq * CE4 ^ 2 / c0 * (C1 + 6 * C2 / Real.pi)
        + (Cs * CE6 * CE4 ^ 2 + Ce * (2 * CE2 * CE4 ^ 2 + 6 * CE4 ^ 2 / Real.pi)) + 1)
        * (scale τ) ^ (5:ℝ) * ‖qParamFun z‖ := by
        rw [show (5:ℝ) = ((5:ℕ):ℝ) from by norm_num, Real.rpow_natCast]

end

end Work.Asymptotics

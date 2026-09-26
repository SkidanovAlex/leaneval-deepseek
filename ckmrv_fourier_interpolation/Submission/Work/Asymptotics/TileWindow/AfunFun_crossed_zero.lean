/-
# The cleared kernel vanishes at the "crossed" point `(τ, (T·S)·τ)`

The cleared kernel `AfunFun ℓ d τ z = (K_+^{clear} d τ z + K_-^{clear} ℓ d τ z)/(2Δ(τ)Δ(z)^e)`
vanishes when the *second* argument is the crossed translate `(T·S)·τ = 1 - 1/τ` of the
first:

  `AfunFun ℓ d τ ((T*S)•τ) = 0`  for `d = 8` and `d = 24`.

The two halves cancel separately: writing `(T*S)•τ = 1 +ᵥ (S•τ)` and letting
`κ = τ^{10}ΔE₄²E₆` (for `d = 8`), `κ = τ^{14}Δ²E₄²E₆` (for `d = 24`) with all modular forms
evaluated at `τ`, one has

  `K_+^{clear} d τ ((T*S)•τ) =   I · κ`  and  `K_-^{clear} ℓ d τ ((T*S)•τ) = - I · κ`,

so the sum vanishes.  The `K_+` computation is a direct evaluation of the explicit matrix of
CKMRV §4.4 at `j(τ) = j((T*S)•τ)`; the `K_-` computation uses in addition the theta identities
`θ₀₀⁴ = θ₀₁⁴ + θ₁₀⁴`, `E₄ = (θ₀₀⁸ + θ₁₀⁸ + θ₀₁⁸)/2`, `E₆ = (θ₀₁⁴-θ₁₀⁴)(θ₁₀⁸+θ₀₁⁸+5/2θ₁₀⁴θ₀₁⁴)`
and `1728Δ = E₄³ - E₆²` to reduce the `𝓛`-dependence of the crossed point to the two
coefficient identities proved in `key_a_gen`/`key_c_gen`.
-/
import Mathlib
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Kernels.Kernels
import Submission.Work.Residues.All
import Submission.Work.Asymptotics.KfunClear_vanish_of_phiPair

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups Matrix

namespace Work.Asymptotics.TileWindow

open Work.Kernels Work.Residues

/-! ## Auxiliary facts about the coefficient functions `fk` -/

private lemma fk_six (x : UpperHalfPlane) : fk (6:ℤ) x = E6Fun x := by simp only [fk]; norm_num
private lemma fk_four (x : UpperHalfPlane) : fk (4:ℤ) x = E4Fun x := by simp only [fk]; norm_num
private lemma fk_two (x : UpperHalfPlane) : fk (2:ℤ) x = E14Fun x / DeltaFun x := by
  simp only [fk]; norm_num
private lemma fk_eight (x : UpperHalfPlane) : fk (8:ℤ) x = E8Fun x := by simp only [fk]; norm_num
private lemma fk_ten (x : UpperHalfPlane) : fk (10:ℤ) x = E10Fun x := by simp only [fk]; norm_num
private lemma fk_twelve (x : UpperHalfPlane) : fk (12:ℤ) x = DeltaFun x := by
  simp only [fk]; norm_num
private lemma fk_fourteen (x : UpperHalfPlane) : fk (14:ℤ) x = E14Fun x := by
  simp only [fk]; norm_num
private lemma fk_neg_two (x : UpperHalfPlane) : fk (-2:ℤ) x = E10Fun x / DeltaFun x := by
  simp only [fk]; norm_num
private lemma fk_zero (x : UpperHalfPlane) : fk (0:ℤ) x = 1 := by simp only [fk]; norm_num

/-- `Δ(z)·f₂(z) = E₁₄(z)`. -/
private lemma delta_mul_fk_two (z : UpperHalfPlane) : DeltaFun z * fk (2:ℤ) z = E14Fun z := by
  rw [fk_two]
  exact mul_div_cancel₀ _ (ClassicalFacts.DeltaFun_ne_zero z)

/-- `Δ(z)·f₀(z) = Δ(z)`. -/
private lemma delta_mul_fk_zero (z : UpperHalfPlane) : DeltaFun z * fk (0:ℤ) z = DeltaFun z := by
  rw [fk_zero, mul_one]

/-- `Δ(z)·f₋₂(z) = E₁₀(z)`. -/
private lemma delta_mul_fk_neg_two (z : UpperHalfPlane) : DeltaFun z * fk (-2:ℤ) z = E10Fun z := by
  rw [fk_neg_two]
  exact mul_div_cancel₀ _ (ClassicalFacts.DeltaFun_ne_zero z)

private lemma jInv_eq (z : UpperHalfPlane) : jInvariantFun z = E4Fun z^3/DeltaFun z := rfl
private lemma E14_eq (z : UpperHalfPlane) : E14Fun z = E4Fun z^2 * E6Fun z := rfl
private lemma E8_eq (z : UpperHalfPlane) : E8Fun z = E4Fun z^2 := rfl
private lemma E10_eq (z : UpperHalfPlane) : E10Fun z = E4Fun z * E6Fun z := rfl

/-! ## The two coefficient identities

With `U = W + V`, `E₄ = (U²+V²+W²)/2`, `E₆ = (W-V)(V²+W²+5/2VW)` and the abbreviations
`A = -E₄²U - E₆(V²-W²)`, `B = E₆U + E₄(V²-W²)`, the `a`- and `c`-coefficients of
`ψ₁A + ψ₂B` are `∓2(E₄³-E₆²)`. -/

private lemma key_a_gen (U V W E4 E6 : ℂ)
    (hUV : U = W + V) (h4 : E4 = (U^2+V^2+W^2)/2)
    (h6 : E6 = (W-V)*(V^2+W^2+5/2*V*W)) :
    (U+W) * (-E4^2*U - E6*(V^2-W^2)) + (U^2+W^2-2*V^2) * (E6*U + E4*(V^2-W^2))
      = -2*(E4^3-E6^2) := by
  subst hUV
  rw [h4, h6]
  ring

private lemma key_c_gen (U V W E4 E6 : ℂ)
    (hUV : U = W + V) (h4 : E4 = (U^2+V^2+W^2)/2)
    (h6 : E6 = (W-V)*(V^2+W^2+5/2*V*W)) :
    -((U+V) * (-E4^2*U - E6*(V^2-W^2))) + (U^2+V^2-2*W^2) * (E6*U + E4*(V^2-W^2))
      = 2*(E4^3-E6^2) := by
  subst hUV
  rw [h4, h6]
  ring

/-! ## Expansion of the cleared `K_-` at a point where `j(τ) = j(z)` -/

private lemma KMinusClear_expand_eight (ℓ : LogLambdaData) (τ z : UpperHalfPlane)
    (hJ : jInvariantFun τ = jInvariantFun z) :
    KMinusClear ℓ 8 τ z =
      (2 * 1728 * (Real.pi : ℂ))⁻¹ *
        ( psiVec ℓ τ 0 * (DeltaFun τ * fk (4:ℤ) τ) * (-2 * (1728:ℂ)) * fk (10:ℤ) z * psitVec ℓ z 0
        + psiVec ℓ τ 1 * (DeltaFun τ * fk (2:ℤ) τ) * 1 * fk (8:ℤ) z * psitVec ℓ z 1
        + psiVec ℓ τ 1 * (DeltaFun τ * fk (2:ℤ) τ) * (-1) * fk (6:ℤ) z * psitVec ℓ z 2
        + psiVec ℓ τ 2 * (DeltaFun τ * fk (0:ℤ) τ) * (1728 - jInvariantFun τ) * fk (8:ℤ) z
            * psitVec ℓ z 1
        + psiVec ℓ τ 2 * (DeltaFun τ * fk (0:ℤ) τ) * jInvariantFun τ * fk (6:ℤ) z
            * psitVec ℓ z 2) := by
  have hU : ∀ i j : Fin 3, UpsilonMinusClear 8 τ z i j =
      ((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹ *
        ((DeltaFun τ * fk (![4, 2, 0] i) τ) *
          (!![-2 * c1728, 0, 0; 0, 1, -1; 0, c1728 - jInvariantFun τ, jInvariantFun τ] :
            Matrix (Fin 3) (Fin 3) ℂ) i j * fk (![10, 8, 6] j) z) := by
    intro i j
    rw [show UpsilonMinusClear 8 τ z =
        ((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹ •
          (PiMatDelta ![4, 2, 0] τ * !![-2 * c1728, 0, 0; 0, 1, -1;
              0, c1728 - jInvariantFun τ, jInvariantFun τ] * PiMat ![10, 8, 6] z) from rfl]
    rw [Matrix.smul_apply, smul_eq_mul, PiMatDelta_mul_PiMat_apply]
  simp only [KMinusClear, Fin.sum_univ_three, psiVec, psitVec, hU, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.of_apply, c1728]
  rw [hJ]
  ring

private lemma KMinusClear_expand_twentyfour (ℓ : LogLambdaData) (τ z : UpperHalfPlane)
    (hJ : jInvariantFun τ = jInvariantFun z) :
    KMinusClear ℓ 24 τ z =
      (2 * 1728 * (Real.pi : ℂ))⁻¹ *
        ( psiVec ℓ τ 0 * (DeltaFun τ * fk (12:ℤ) τ) * (-2 * (1728:ℂ)) * (DeltaFun z * fk (2:ℤ) z)
            * psitVec ℓ z 0
        + psiVec ℓ τ 1 * (DeltaFun τ * fk (10:ℤ) τ) * jInvariantFun τ * (DeltaFun z * fk (0:ℤ) z)
            * psitVec ℓ z 1
        + psiVec ℓ τ 1 * (DeltaFun τ * fk (10:ℤ) τ) * (-1) * (DeltaFun z * fk (-2:ℤ) z)
            * psitVec ℓ z 2
        + psiVec ℓ τ 2 * (DeltaFun τ * fk (8:ℤ) τ) * (1728 - jInvariantFun τ)
            * (DeltaFun z * fk (0:ℤ) z) * psitVec ℓ z 1
        + psiVec ℓ τ 2 * (DeltaFun τ * fk (8:ℤ) τ) * 1 * (DeltaFun z * fk (-2:ℤ) z)
            * psitVec ℓ z 2) := by
  have hU : ∀ i j : Fin 3, UpsilonMinusClear 24 τ z i j =
      ((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹ *
        ((DeltaFun τ * fk (![12, 10, 8] i) τ) *
          (!![-2 * c1728, 0, 0; 0, jInvariantFun τ, -1; 0, c1728 - jInvariantFun τ, 1] :
            Matrix (Fin 3) (Fin 3) ℂ) i j * (DeltaFun z * fk (![2, 0, -2] j) z)) := by
    intro i j
    have hJz : jInvariantFun τ - jInvariantFun z = 0 := sub_eq_zero.mpr hJ
    rw [show UpsilonMinusClear 24 τ z =
        ((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹ •
          (PiMatDelta ![12, 10, 8] τ *
            !![-2 * c1728, -2 * c1728 * (jInvariantFun τ - jInvariantFun z), 0;
                0, jInvariantFun τ + 2 * (jInvariantFun τ - jInvariantFun z), -1;
                0, c1728 - 2 * (jInvariantFun τ - jInvariantFun z) - jInvariantFun τ, 1] *
            (DeltaFun z • PiMat ![2, 0, -2] z)) from rfl]
    rw [hJz, Matrix.smul_apply, smul_eq_mul, PiMatDelta_mul_smul_PiMat_apply]
    ring_nf
  simp only [KMinusClear, Fin.sum_univ_three, psiVec, psitVec, hU, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.of_apply, c1728]
  rw [hJ]
  ring

/-! ## The `K_+` value at the crossed point -/

private lemma KPlusClear_crossed_eight (τ : UpperHalfPlane) :
    KPlusClear 8 τ ((ModularGroup.T * ModularGroup.S) • τ)
      = Complex.I * ((τ:ℂ)^10 * DeltaFun τ * E4Fun τ^2 * E6Fun τ) := by
  have hJ : jInvariantFun τ = jInvariantFun ((ModularGroup.T * ModularGroup.S) • τ) := by
    rw [Work.Residues.T_mul_S_smul, Work.Residues.KMinusClearTS.jInvariantFun_TS]
  rw [Work.Residues.KPlusClear_expand_eight τ ((ModularGroup.T * ModularGroup.S) • τ) hJ]
  rw [Work.Residues.T_mul_S_smul τ]
  rw [fk_six, fk_four, fk_two, fk_eight, fk_ten, fk_twelve]
  simp only [phiNeg2, phi0, phi2, E8Fun, E10Fun, E14Fun]
  rw [Work.Residues.KMinusClearTS.E4Fun_TS, Work.Residues.KMinusClearTS.E6Fun_TS,
    Work.Residues.KMinusClearTS.DeltaFun_TS]
  rw [Work.Kernels.TildeFacts.E2S_eq, Work.Kernels.E2Fun_vadd_one, Work.Kernels.E2Fun_S_smul,
    UpperHalfPlane.coe_vadd, Work.Kernels.S_smul_coe]
  push_cast
  have hτ : (τ:ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hD : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hz : 1 - ((τ:ℂ))⁻¹ ≠ 0 := by
    have h := UpperHalfPlane.ne_zero ((ModularGroup.T * ModularGroup.S) • τ)
    rwa [Work.Residues.T_mul_S_smul, UpperHalfPlane.coe_vadd, Work.Kernels.S_smul_coe] at h
  have h1' : (τ:ℂ) - 1 ≠ 0 := by
    have : (τ:ℂ) ≠ 1 := by
      intro h
      have h3 := congrArg Complex.im h
      simp at h3
      exact (ne_of_gt τ.im_pos) h3
    simpa using sub_ne_zero.mpr this
  field_simp [hz]
  ring_nf
  rw [show -1 + (τ:ℂ) = (τ:ℂ) - 1 by ring]
  field_simp
  ring

private lemma KPlusClear_crossed_twentyfour (τ : UpperHalfPlane) :
    KPlusClear 24 τ ((ModularGroup.T * ModularGroup.S) • τ)
      = Complex.I * ((τ:ℂ)^14 * DeltaFun τ^2 * E4Fun τ^2 * E6Fun τ) := by
  have hJ : jInvariantFun τ = jInvariantFun ((ModularGroup.T * ModularGroup.S) • τ) := by
    rw [Work.Residues.T_mul_S_smul, Work.Residues.KMinusClearTS.jInvariantFun_TS]
  rw [Work.Residues.KPlusClear_expand_twentyfour τ ((ModularGroup.T * ModularGroup.S) • τ) hJ]
  rw [Work.Residues.T_mul_S_smul τ]
  rw [fk_fourteen, fk_twelve, fk_ten, fk_zero, fk_two, fk_four]
  simp only [phiNeg2, phi0, phi2, E10Fun, E14Fun, c1728]
  rw [Work.Residues.KMinusClearTS.E4Fun_TS, Work.Residues.KMinusClearTS.E6Fun_TS,
    Work.Residues.KMinusClearTS.DeltaFun_TS]
  rw [Work.Kernels.TildeFacts.E2S_eq, Work.Kernels.E2Fun_vadd_one, Work.Kernels.E2Fun_S_smul,
    UpperHalfPlane.coe_vadd, Work.Kernels.S_smul_coe]
  push_cast
  have hτ : (τ:ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hD : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hz : 1 - ((τ:ℂ))⁻¹ ≠ 0 := by
    have h := UpperHalfPlane.ne_zero ((ModularGroup.T * ModularGroup.S) • τ)
    rwa [Work.Residues.T_mul_S_smul, UpperHalfPlane.coe_vadd, Work.Kernels.S_smul_coe] at h
  have h1' : (τ:ℂ) - 1 ≠ 0 := by
    have : (τ:ℂ) ≠ 1 := by
      intro h
      have h3 := congrArg Complex.im h
      simp at h3
      exact (ne_of_gt τ.im_pos) h3
    simpa using sub_ne_zero.mpr this
  field_simp [hz]
  ring_nf
  rw [show -1 + (τ:ℂ) = (τ:ℂ) - 1 by ring]
  field_simp
  ring

/-! ## The `K_-` value at the crossed point, `d = 8` -/

private lemma KMinusClear_crossed_eight (ℓ : LogLambdaData) (τ : UpperHalfPlane) :
    KMinusClear ℓ 8 τ ((ModularGroup.T * ModularGroup.S) • τ)
      = -(Complex.I * ((τ:ℂ)^10 * DeltaFun τ * E4Fun τ^2 * E6Fun τ)) := by
  have hJ : jInvariantFun τ = jInvariantFun ((ModularGroup.T * ModularGroup.S) • τ) := by
    rw [Work.Residues.T_mul_S_smul, Work.Residues.KMinusClearTS.jInvariantFun_TS]
  rw [KMinusClear_expand_eight ℓ τ _ hJ]
  rw [Work.Residues.T_mul_S_smul τ]
  rw [fk_four, fk_two, fk_zero, fk_ten, fk_eight, fk_six]
  simp only [psiVec, psitVec, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp only [psi2, psi4, xi2Fun, xi4Fun]
  rw [Work.Residues.KMinusClearTS.xi2S_eq, Work.Residues.KMinusClearTS.xi4S_eq]
  rw [Work.Residues.KMinusClearTS.L_TS ℓ τ, Work.Residues.KMinusClearTS.WFun_TS,
    Work.Residues.KMinusClearTS.UFun_TS, Work.Residues.KMinusClearTS.VFun_TS]
  rw [Work.Residues.KMinusClearTS.E6Fun_TS, Work.Residues.KMinusClearTS.E8Fun_TS,
    Work.Residues.KMinusClearTS.E10Fun_TS]
  rw [jInv_eq τ, E14_eq τ]
  simp only [E8Fun, E10Fun]
  have hDm : 1728 * DeltaFun τ = E4Fun τ^3 - E6Fun τ^2 := Work.Residues.KMinusClearTS.disc_eq τ
  have hDnz : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hA := key_a_gen (UFun τ) (VFun τ) (WFun τ) (E4Fun τ) (E6Fun τ)
      (Work.Kernels.TildeFacts.theta_quartic τ) (Work.Residues.KMinusClearTS.E4Fun_eq_theta τ)
      (Work.Kernels.TildeFacts.E6Fun_eq_theta τ)
  have hC := key_c_gen (UFun τ) (VFun τ) (WFun τ) (E4Fun τ) (E6Fun τ)
      (Work.Kernels.TildeFacts.theta_quartic τ) (Work.Residues.KMinusClearTS.E4Fun_eq_theta τ)
      (Work.Kernels.TildeFacts.E6Fun_eq_theta τ)
  have hcombine : ((UFun τ + WFun τ) * ℓ.L τ + -(UFun τ + VFun τ) * ℓ.L_S τ)
        * (-(E4Fun τ)^2 * UFun τ - E6Fun τ * (VFun τ^2 - WFun τ^2))
      + ((UFun τ^2 + WFun τ^2 - 2*VFun τ^2) * ℓ.L τ + (UFun τ^2 + VFun τ^2 - 2*WFun τ^2) * ℓ.L_S τ)
        * (E6Fun τ * UFun τ + E4Fun τ * (VFun τ^2 - WFun τ^2))
      = 2 * (E4Fun τ^3 - E6Fun τ^2) * (ℓ.L_S τ - ℓ.L τ) := by
    linear_combination (ℓ.L τ) * hA + (ℓ.L_S τ) * hC
  have h4a : (DeltaFun τ * 1) * (1728 - E4Fun τ ^ 3 / DeltaFun τ) = -(E6Fun τ ^ 2) := by
    rw [mul_one, mul_sub, mul_div_cancel₀ _ hDnz, mul_comm (DeltaFun τ) (1728:ℂ), hDm]
    ring
  have h5a : (DeltaFun τ * 1) * (E4Fun τ ^ 3 / DeltaFun τ) = E4Fun τ ^ 3 := by
    rw [mul_one, mul_div_cancel₀ _ hDnz]
  have e1 : 1 * (DeltaFun τ * E4Fun τ) * (-2 * 1728) * (↑τ ^ 10 * (E4Fun τ * E6Fun τ)) *
        (ℓ.L_S τ - ℓ.L τ + ↑Real.pi * Complex.I)
      = E4Fun τ^2 * E6Fun τ * (↑τ)^10 * (-2*(E4Fun τ^3 - E6Fun τ^2)) *
        (ℓ.L_S τ - ℓ.L τ + ↑Real.pi * Complex.I) := by
    rw [← hDm]; ring
  have e2 : ((UFun τ + WFun τ) * ℓ.L τ + -(UFun τ + VFun τ) * ℓ.L_S τ) *
          (DeltaFun τ * (E4Fun τ ^ 2 * E6Fun τ / DeltaFun τ)) * 1 * (↑τ ^ 8 * E4Fun τ ^ 2) *
        (-↑τ ^ 2 * UFun τ)
      = ((UFun τ + WFun τ) * ℓ.L τ + -(UFun τ + VFun τ) * ℓ.L_S τ) * (E4Fun τ^2 * E6Fun τ) *
        (↑τ)^10 * (-(E4Fun τ ^ 2 * UFun τ)) := by
    rw [mul_div_cancel₀ _ hDnz]; ring
  have e3 : ((UFun τ + WFun τ) * ℓ.L τ + -(UFun τ + VFun τ) * ℓ.L_S τ) *
          (DeltaFun τ * (E4Fun τ ^ 2 * E6Fun τ / DeltaFun τ)) * -1 * (↑τ ^ 6 * E6Fun τ) *
        ((-↑τ ^ 2 * VFun τ) ^ 2 - (↑τ ^ 2 * WFun τ) ^ 2)
      = ((UFun τ + WFun τ) * ℓ.L τ + -(UFun τ + VFun τ) * ℓ.L_S τ) * (E4Fun τ^2 * E6Fun τ) *
        (↑τ)^10 * (-(E6Fun τ * (VFun τ^2 - WFun τ^2))) := by
    rw [mul_div_cancel₀ _ hDnz]; ring
  have e4 : ((UFun τ ^ 2 + WFun τ ^ 2 - 2 * VFun τ ^ 2) * ℓ.L τ +
          (UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2) * ℓ.L_S τ) * (DeltaFun τ * 1) *
        (1728 - E4Fun τ ^ 3 / DeltaFun τ) * (↑τ ^ 8 * E4Fun τ ^ 2) * (-↑τ ^ 2 * UFun τ)
      = ((UFun τ ^ 2 + WFun τ ^ 2 - 2 * VFun τ ^ 2) * ℓ.L τ +
          (UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2) * ℓ.L_S τ) * (E4Fun τ^2 * E6Fun τ) *
        (↑τ)^10 * (E6Fun τ * UFun τ) := by
    calc _ = ((UFun τ ^ 2 + WFun τ ^ 2 - 2 * VFun τ ^ 2) * ℓ.L τ +
          (UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2) * ℓ.L_S τ) *
            ((DeltaFun τ * 1) * (1728 - E4Fun τ ^ 3 / DeltaFun τ)) *
          (↑τ ^ 8 * E4Fun τ ^ 2) * (-↑τ ^ 2 * UFun τ) := by ring
      _ = _ := by rw [h4a]; ring
  have e5 : ((UFun τ ^ 2 + WFun τ ^ 2 - 2 * VFun τ ^ 2) * ℓ.L τ +
          (UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2) * ℓ.L_S τ) * (DeltaFun τ * 1) *
        (E4Fun τ ^ 3 / DeltaFun τ) * (↑τ ^ 6 * E6Fun τ) *
        ((-↑τ ^ 2 * VFun τ) ^ 2 - (↑τ ^ 2 * WFun τ) ^ 2)
      = ((UFun τ ^ 2 + WFun τ ^ 2 - 2 * VFun τ ^ 2) * ℓ.L τ +
          (UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2) * ℓ.L_S τ) * (E4Fun τ^2 * E6Fun τ) *
        (↑τ)^10 * (E4Fun τ * (VFun τ^2 - WFun τ^2)) := by
    calc _ = ((UFun τ ^ 2 + WFun τ ^ 2 - 2 * VFun τ ^ 2) * ℓ.L τ +
          (UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2) * ℓ.L_S τ) *
            ((DeltaFun τ * 1) * (E4Fun τ ^ 3 / DeltaFun τ)) *
          (↑τ ^ 6 * E6Fun τ) * ((-↑τ ^ 2 * VFun τ) ^ 2 - (↑τ ^ 2 * WFun τ) ^ 2) := by ring
      _ = _ := by rw [h5a]; ring
  rw [e1, e2, e3, e4, e5]
  have hfac : (2 * 1728 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num)) hpi
  rw [inv_mul_eq_iff_eq_mul₀ hfac]
  linear_combination (E4Fun τ ^ 2 * E6Fun τ * ↑τ ^ 10) * hcombine
    + (2 * (E4Fun τ ^ 2 * E6Fun τ * ↑τ ^ 10) * ↑Real.pi * Complex.I) * hDm

/-! ## The `K_-` value at the crossed point, `d = 24` -/

private lemma KMinusClear_crossed_twentyfour (ℓ : LogLambdaData) (τ : UpperHalfPlane) :
    KMinusClear ℓ 24 τ ((ModularGroup.T * ModularGroup.S) • τ)
      = -(Complex.I * ((τ:ℂ)^14 * DeltaFun τ^2 * E4Fun τ^2 * E6Fun τ)) := by
  have hJ : jInvariantFun τ = jInvariantFun ((ModularGroup.T * ModularGroup.S) • τ) := by
    rw [Work.Residues.T_mul_S_smul, Work.Residues.KMinusClearTS.jInvariantFun_TS]
  rw [KMinusClear_expand_twentyfour ℓ τ _ hJ]
  rw [Work.Residues.T_mul_S_smul τ]
  rw [fk_twelve, fk_ten, fk_eight, delta_mul_fk_two, delta_mul_fk_zero, delta_mul_fk_neg_two]
  simp only [psiVec, psitVec, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp only [psi2, psi4, xi2Fun, xi4Fun]
  rw [Work.Residues.KMinusClearTS.xi2S_eq, Work.Residues.KMinusClearTS.xi4S_eq]
  rw [Work.Residues.KMinusClearTS.L_TS ℓ τ, Work.Residues.KMinusClearTS.WFun_TS,
    Work.Residues.KMinusClearTS.UFun_TS, Work.Residues.KMinusClearTS.VFun_TS]
  rw [Work.Residues.KMinusClearTS.DeltaFun_TS, Work.Residues.KMinusClearTS.E14Fun_TS,
    Work.Residues.KMinusClearTS.E10Fun_TS]
  rw [jInv_eq τ, E14_eq τ]
  simp only [E8Fun, E10Fun]
  have hDm : 1728 * DeltaFun τ = E4Fun τ^3 - E6Fun τ^2 := Work.Residues.KMinusClearTS.disc_eq τ
  have hDnz : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hA := key_a_gen (UFun τ) (VFun τ) (WFun τ) (E4Fun τ) (E6Fun τ)
      (Work.Kernels.TildeFacts.theta_quartic τ) (Work.Residues.KMinusClearTS.E4Fun_eq_theta τ)
      (Work.Kernels.TildeFacts.E6Fun_eq_theta τ)
  have hC := key_c_gen (UFun τ) (VFun τ) (WFun τ) (E4Fun τ) (E6Fun τ)
      (Work.Kernels.TildeFacts.theta_quartic τ) (Work.Residues.KMinusClearTS.E4Fun_eq_theta τ)
      (Work.Kernels.TildeFacts.E6Fun_eq_theta τ)
  have hcombine : ((UFun τ + WFun τ) * ℓ.L τ + -(UFun τ + VFun τ) * ℓ.L_S τ)
        * (-(E4Fun τ)^2 * UFun τ - E6Fun τ * (VFun τ^2 - WFun τ^2))
      + ((UFun τ^2 + WFun τ^2 - 2*VFun τ^2) * ℓ.L τ + (UFun τ^2 + VFun τ^2 - 2*WFun τ^2) * ℓ.L_S τ)
        * (E6Fun τ * UFun τ + E4Fun τ * (VFun τ^2 - WFun τ^2))
      = 2 * (E4Fun τ^3 - E6Fun τ^2) * (ℓ.L_S τ - ℓ.L τ) := by
    linear_combination (ℓ.L τ) * hA + (ℓ.L_S τ) * hC
  have h2 : (DeltaFun τ * (E4Fun τ * E6Fun τ)) * (E4Fun τ ^ 3 / DeltaFun τ)
      = (E4Fun τ * E6Fun τ) * E4Fun τ ^ 3 := by
    rw [mul_comm (DeltaFun τ) (E4Fun τ * E6Fun τ), mul_assoc, mul_div_cancel₀ _ hDnz]
  have h4a : (DeltaFun τ * E4Fun τ ^ 2) * (1728 - E4Fun τ ^ 3 / DeltaFun τ)
      = -(E4Fun τ ^ 2 * E6Fun τ ^ 2) := by
    rw [show (DeltaFun τ * E4Fun τ ^ 2) * (1728 - E4Fun τ ^ 3 / DeltaFun τ)
        = E4Fun τ ^ 2 * (1728 * DeltaFun τ - DeltaFun τ * (E4Fun τ ^ 3 / DeltaFun τ)) by ring]
    rw [mul_div_cancel₀ _ hDnz, hDm]
    ring
  have e1 : 1 * (DeltaFun τ * DeltaFun τ) * (-2 * 1728) * (↑τ ^ 14 * (E4Fun τ ^ 2 * E6Fun τ)) *
        (ℓ.L_S τ - ℓ.L τ + ↑Real.pi * Complex.I)
      = ↑τ ^ 4 * DeltaFun τ * (E4Fun τ ^ 2 * E6Fun τ * ↑τ ^ 10 *
          (-2 * (E4Fun τ ^ 3 - E6Fun τ ^ 2)) * (ℓ.L_S τ - ℓ.L τ + ↑Real.pi * Complex.I)) := by
    rw [← hDm]; ring
  have e2 : ((UFun τ + WFun τ) * ℓ.L τ + -(UFun τ + VFun τ) * ℓ.L_S τ) *
          (DeltaFun τ * (E4Fun τ * E6Fun τ)) * (E4Fun τ ^ 3 / DeltaFun τ) *
        (↑τ ^ 12 * DeltaFun τ) * (-↑τ ^ 2 * UFun τ)
      = ↑τ ^ 4 * DeltaFun τ * (E4Fun τ ^ 2 * E6Fun τ * ↑τ ^ 10) *
        (((UFun τ + WFun τ) * ℓ.L τ + -(UFun τ + VFun τ) * ℓ.L_S τ) *
          (-(E4Fun τ ^ 2 * UFun τ))) := by
    calc _ = ((UFun τ + WFun τ) * ℓ.L τ + -(UFun τ + VFun τ) * ℓ.L_S τ) *
            ((DeltaFun τ * (E4Fun τ * E6Fun τ)) * (E4Fun τ ^ 3 / DeltaFun τ)) *
          (↑τ ^ 12 * DeltaFun τ) * (-↑τ ^ 2 * UFun τ) := by ring
      _ = _ := by rw [h2]; ring
  have e3 : ((UFun τ + WFun τ) * ℓ.L τ + -(UFun τ + VFun τ) * ℓ.L_S τ) *
          (DeltaFun τ * (E4Fun τ * E6Fun τ)) * -1 * (↑τ ^ 10 * (E4Fun τ * E6Fun τ)) *
        ((-↑τ ^ 2 * VFun τ) ^ 2 - (↑τ ^ 2 * WFun τ) ^ 2)
      = ↑τ ^ 4 * DeltaFun τ * (E4Fun τ ^ 2 * E6Fun τ * ↑τ ^ 10) *
        (((UFun τ + WFun τ) * ℓ.L τ + -(UFun τ + VFun τ) * ℓ.L_S τ) *
          (-(E6Fun τ * (VFun τ ^ 2 - WFun τ ^ 2)))) := by
    ring
  have e4 : ((UFun τ ^ 2 + WFun τ ^ 2 - 2 * VFun τ ^ 2) * ℓ.L τ +
          (UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2) * ℓ.L_S τ) * (DeltaFun τ * E4Fun τ ^ 2) *
        (1728 - E4Fun τ ^ 3 / DeltaFun τ) * (↑τ ^ 12 * DeltaFun τ) * (-↑τ ^ 2 * UFun τ)
      = ↑τ ^ 4 * DeltaFun τ * (E4Fun τ ^ 2 * E6Fun τ * ↑τ ^ 10) *
        (((UFun τ ^ 2 + WFun τ ^ 2 - 2 * VFun τ ^ 2) * ℓ.L τ +
          (UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2) * ℓ.L_S τ) * (E6Fun τ * UFun τ)) := by
    calc _ = ((UFun τ ^ 2 + WFun τ ^ 2 - 2 * VFun τ ^ 2) * ℓ.L τ +
          (UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2) * ℓ.L_S τ) *
            ((DeltaFun τ * E4Fun τ ^ 2) * (1728 - E4Fun τ ^ 3 / DeltaFun τ)) *
          (↑τ ^ 12 * DeltaFun τ) * (-↑τ ^ 2 * UFun τ) := by ring
      _ = _ := by rw [h4a]; ring
  have e5 : ((UFun τ ^ 2 + WFun τ ^ 2 - 2 * VFun τ ^ 2) * ℓ.L τ +
          (UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2) * ℓ.L_S τ) * (DeltaFun τ * E4Fun τ ^ 2) *
        1 * (↑τ ^ 10 * (E4Fun τ * E6Fun τ)) *
        ((-↑τ ^ 2 * VFun τ) ^ 2 - (↑τ ^ 2 * WFun τ) ^ 2)
      = ↑τ ^ 4 * DeltaFun τ * (E4Fun τ ^ 2 * E6Fun τ * ↑τ ^ 10) *
        (((UFun τ ^ 2 + WFun τ ^ 2 - 2 * VFun τ ^ 2) * ℓ.L τ +
          (UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2) * ℓ.L_S τ) *
            (E4Fun τ * (VFun τ ^ 2 - WFun τ ^ 2))) := by
    ring
  rw [e1, e2, e3, e4, e5]
  have hfac : (2 * 1728 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num)) hpi
  rw [inv_mul_eq_iff_eq_mul₀ hfac]
  linear_combination ((↑τ ^ 4 * DeltaFun τ) * (E4Fun τ ^ 2 * E6Fun τ * ↑τ ^ 10)) * hcombine
    + (2 * (↑τ ^ 4 * DeltaFun τ) * (E4Fun τ ^ 2 * E6Fun τ * ↑τ ^ 10) * ↑Real.pi * Complex.I) * hDm

/-! ## The main theorem -/

theorem AfunFun_crossed_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) :
    Work.Asymptotics.AfunFun ℓ d τ ((ModularGroup.T * ModularGroup.S) • τ) = 0 := by
  have hsum : KPlusClear d τ ((ModularGroup.T * ModularGroup.S) • τ)
      + KMinusClear ℓ d τ ((ModularGroup.T * ModularGroup.S) • τ) = 0 := by
    rcases hd with rfl | rfl
    · rw [KPlusClear_crossed_eight, KMinusClear_crossed_eight]; ring
    · rw [KPlusClear_crossed_twentyfour, KMinusClear_crossed_twentyfour]; ring
  have hK : KfunClear ℓ d τ ((ModularGroup.T * ModularGroup.S) • τ) = 0 := by
    simp only [KfunClear]; rw [hsum]; ring
  have h := KfunClear_eq_mul_AfunFun ℓ d τ ((ModularGroup.T * ModularGroup.S) • τ)
  rw [hK] at h
  have hDτ : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hDz : DeltaFun ((ModularGroup.T * ModularGroup.S) • τ) ≠ 0 :=
    ClassicalFacts.DeltaFun_ne_zero _
  have hmul : DeltaFun τ * DeltaFun ((ModularGroup.T * ModularGroup.S) • τ) ^ dpow d ≠ 0 :=
    mul_ne_zero hDτ (pow_ne_zero _ hDz)
  have : DeltaFun τ * DeltaFun ((ModularGroup.T * ModularGroup.S) • τ) ^ dpow d
      * AfunFun ℓ d τ ((ModularGroup.T * ModularGroup.S) • τ) = 0 := by
    rw [← h]
  exact (mul_eq_zero.mp this).resolve_left hmul

end Work.Asymptotics.TileWindow

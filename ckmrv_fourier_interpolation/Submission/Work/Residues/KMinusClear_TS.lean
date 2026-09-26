import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.LogLambda.LambdaLaws
import Submission.Work.Kernels.LogLambda.ThetaLaws
import Submission.Work.Kernels.TildeFacts.theta_quartic
import Submission.Work.Kernels.KernelFacts.KMinus_T2
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Kernels.KernelFacts.KPlusCoeff_slash_S
import Submission.Work.Modular.thetaSeries_E8_eq_E4
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic
import Submission.Work.Modular.ThetaFuncs
import Submission.Work.Kernels.TildeFacts.E6Fun_eq_theta

namespace Work.Residues

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace KMinusClearTS

open Work.Kernels
open Work.Kernels.KernelFacts

/-! ## Special values at `τ = T·(S·z) = (z-1)/z` -/

/-- `Δ(T·S·z) = z^{12}Δ(z)`. -/
lemma DeltaFun_TS (z : ℍ) :
    DeltaFun ((1 : ℝ) +ᵥ (ModularGroup.S • z)) = (z : ℂ) ^ 12 * DeltaFun z := by
  rw [DeltaFun_vadd_one, KernelFacts.kpc_smul_S_of_slash KernelFacts.kpc_Delta_slash_S z]
  norm_num

/-- `E₄(T·S·z) = z⁴E₄(z)`. -/
lemma E4Fun_TS (z : ℍ) :
    E4Fun ((1 : ℝ) +ᵥ (ModularGroup.S • z)) = (z : ℂ) ^ 4 * E4Fun z := by
  rw [E4Fun_vadd_one, KernelFacts.kpc_smul_S_of_slash KernelFacts.kpc_E4_slash_S z]
  norm_num

/-- `E₆(T·S·z) = z⁶E₆(z)`. -/
lemma E6Fun_TS (z : ℍ) :
    E6Fun ((1 : ℝ) +ᵥ (ModularGroup.S • z)) = (z : ℂ) ^ 6 * E6Fun z := by
  rw [E6Fun_vadd_one, KernelFacts.kpc_smul_S_of_slash KernelFacts.kpc_E6_slash_S z]
  norm_num

/-- `E₈(T·S·z) = z⁸E₈(z)`. -/
lemma E8Fun_TS (z : ℍ) :
    E8Fun ((1 : ℝ) +ᵥ (ModularGroup.S • z)) = (z : ℂ) ^ 8 * E8Fun z := by
  simp only [E8Fun]
  rw [E4Fun_TS z]
  ring

/-- `E₁₀(T·S·z) = z^{10}E₁₀(z)`. -/
lemma E10Fun_TS (z : ℍ) :
    E10Fun ((1 : ℝ) +ᵥ (ModularGroup.S • z)) = (z : ℂ) ^ 10 * E10Fun z := by
  simp only [E10Fun]
  rw [E4Fun_TS z, E6Fun_TS z]
  ring

/-- `E₁₄(T·S·z) = z^{14}E₁₄(z)`. -/
lemma E14Fun_TS (z : ℍ) :
    E14Fun ((1 : ℝ) +ᵥ (ModularGroup.S • z)) = (z : ℂ) ^ 14 * E14Fun z := by
  simp only [E14Fun]
  rw [E4Fun_TS z, E6Fun_TS z]
  ring

/-- `j(T·S·z) = j(z)`. -/
lemma jInvariantFun_TS (z : ℍ) :
    jInvariantFun ((1 : ℝ) +ᵥ (ModularGroup.S • z)) = jInvariantFun z := by
  rw [jInvariantFun_vadd_one, KernelFacts.kpc_jInvariant_S z]

/-- `U(T·S·z) = -z²V(z)`  (`U = θ₀₀⁴`). -/
lemma UFun_TS (z : ℍ) :
    UFun ((1 : ℝ) +ᵥ (ModularGroup.S • z)) = -(z : ℂ) ^ 2 * VFun z := by
  rw [KernelFacts.UFun_vadd_one, KernelFacts.WFun_S_smul]

/-- `W(T·S·z) = -z²U(z)`  (`W = θ₀₁⁴`). -/
lemma WFun_TS (z : ℍ) :
    WFun ((1 : ℝ) +ᵥ (ModularGroup.S • z)) = -(z : ℂ) ^ 2 * UFun z := by
  rw [KernelFacts.WFun_vadd_one, KernelFacts.UFun_S_smul]

/-- `V(T·S·z) = z²W(z)`  (`V = θ₁₀⁴`). -/
lemma VFun_TS (z : ℍ) :
    VFun ((1 : ℝ) +ᵥ (ModularGroup.S • z)) = (z : ℂ) ^ 2 * WFun z := by
  rw [KernelFacts.VFun_vadd_one, KernelFacts.VFun_S_smul_km]
  ring

/-- The `S`-slash of `ξ₂ = U + W` at weight `2` equals `-(U+V)`. -/
lemma xi2S_eq (z : ℍ) : (xi2Fun ∣[(2 : ℤ)] ModularGroup.S) z = -(UFun z + VFun z) := by
  rw [KernelFacts.kpc_slash_S_apply]
  simp only [xi2Fun, KernelFacts.UFun_S_smul, KernelFacts.WFun_S_smul]
  have hz : (z : ℂ) ≠ 0 := KernelFacts.kpc_tau_ne_zero z
  rw [show (-(2 : ℤ)) = -(2 : ℤ) from rfl, _root_.zpow_neg, zpow_ofNat]
  field_simp
  ring

/-- The `S`-slash of `ξ₄` at weight `4`. -/
lemma xi4S_eq (z : ℍ) :
    (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) z = UFun z ^ 2 + VFun z ^ 2 - 2 * WFun z ^ 2 :=
  KernelFacts.xi4S_apply_km z

/-! ## The values of `𝓛`, `𝓛_S`, `ψ_2`, `ψ_4` at `T·S·z` -/

/-- `𝓛(T·S·z) = 𝓛_S(z) - 𝓛(z) + πi`. -/
lemma L_TS (ℓ : LogLambdaData) (z : ℍ) :
    ℓ.L ((1 : ℝ) +ᵥ (ModularGroup.S • z))
      = ℓ.L_S z - ℓ.L z + (Real.pi : ℂ) * Complex.I := by
  have h1 : ℓ.L (ModularGroup.S • z) = ℓ.L_S z := by
    have h := congr_fun ℓ.slash_S z
    rw [KernelFacts.kpc_slash_S_apply] at h
    simpa using h
  have h2 : ℓ.L_S (ModularGroup.S • z) = ℓ.L z := by
    have h := congr_fun ℓ.slash_S_S z
    rw [KernelFacts.kpc_slash_S_apply] at h
    simpa using h
  have h := ℓ.slash_T (ModularGroup.S • z)
  rw [Work.Kernels.slash_T_apply, h1, h2] at h
  exact h

/-- `𝓛_S(T·S·z) = -𝓛(z)`. -/
lemma L_S_TS (ℓ : LogLambdaData) (z : ℍ) :
    ℓ.L_S ((1 : ℝ) +ᵥ (ModularGroup.S • z)) = -ℓ.L z := by
  have h2 : ℓ.L_S (ModularGroup.S • z) = ℓ.L z := by
    have h := congr_fun ℓ.slash_S_S z
    rw [KernelFacts.kpc_slash_S_apply] at h
    simpa using h
  have h := ℓ.slash_T_S (ModularGroup.S • z)
  rw [Work.Kernels.slash_T_apply, h2] at h
  exact h

/-- `ψ_2(T·S·z)` in terms of the data at `z`. -/
lemma psi2_TS (ℓ : LogLambdaData) (z : ℍ) :
    psi2 ℓ ((1 : ℝ) +ᵥ (ModularGroup.S • z))
      = (z : ℂ) ^ 2 *
          (-(UFun z + VFun z) * (ℓ.L_S z + (Real.pi : ℂ) * Complex.I)
            + (UFun z + WFun z) * ℓ.L z) := by
  have h1 : xi2Fun ((1 : ℝ) +ᵥ (ModularGroup.S • z)) = -(z : ℂ) ^ 2 * (UFun z + VFun z) := by
    rw [KernelFacts.xi2Fun_vadd_one]
    simp only [xi2Fun, KernelFacts.UFun_S_smul, KernelFacts.WFun_S_smul]
    ring
  have h2 : (xi2Fun ∣[(2 : ℤ)] ModularGroup.S) ((1 : ℝ) +ᵥ (ModularGroup.S • z))
      = (z : ℂ) ^ 2 * (VFun z - WFun z) := by
    rw [xi2S_eq, UFun_TS z, VFun_TS z]
    ring
  rw [psi2, h1, h2, L_TS ℓ z, L_S_TS ℓ z]
  ring

/-- `ψ_4(T·S·z)` in terms of the data at `z`. -/
lemma psi4_TS (ℓ : LogLambdaData) (z : ℍ) :
    psi4 ℓ ((1 : ℝ) +ᵥ (ModularGroup.S • z))
      = (z : ℂ) ^ 4 *
          ((UFun z ^ 2 + VFun z ^ 2 - 2 * WFun z ^ 2)
              * (ℓ.L_S z + (Real.pi : ℂ) * Complex.I)
            + (UFun z ^ 2 - 2 * VFun z ^ 2 + WFun z ^ 2) * ℓ.L z) := by
  have h1 : xi4Fun ((1 : ℝ) +ᵥ (ModularGroup.S • z))
      = (z : ℂ) ^ 4 * (UFun z ^ 2 + VFun z ^ 2 - 2 * WFun z ^ 2) := by
    rw [KernelFacts.xi4Fun_vadd_one_km]
    simp only [xi4Fun, KernelFacts.UFun_S_smul, KernelFacts.WFun_S_smul,
      KernelFacts.VFun_S_smul_km]
    ring
  have h2 : (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) ((1 : ℝ) +ᵥ (ModularGroup.S • z))
      = (z : ℂ) ^ 4 * (WFun z ^ 2 + VFun z ^ 2 - 2 * UFun z ^ 2) := by
    rw [xi4S_eq, UFun_TS z, VFun_TS z, WFun_TS z]
    ring
  rw [psi4, h1, h2, L_TS ℓ z, L_S_TS ℓ z]
  ring

/-! ## `E₄` in terms of theta functions -/

/-- `E₄ = (U² + V² + W²)/2` where `U = θ₀₀⁴`, `V = θ₁₀⁴`, `W = θ₀₁⁴`
(`Θ_{E₈} = E₄`). -/
lemma E4Fun_eq_theta (z : ℍ) :
    E4Fun z = (UFun z ^ 2 + VFun z ^ 2 + WFun z ^ 2) / 2 := by
  have h := congr_fun Work.Modular.thetaSeries_E8_eq_E4 z
  rw [Work.Modular.thetaSeries_E8_decomposition z] at h
  have hE4 : Work.Modular.E4 z = E4Fun z := rfl
  rw [hE4] at h
  rw [← h]
  simp only [UFun, WFun, VFun, theta00Fun, theta01Fun, theta10Fun,
    Work.Modular.theta3, Work.Modular.theta4, Work.Modular.theta2]
  ring

/-- `1728Δ = E₄³ - E₆²`. -/
lemma disc_eq (z : ℍ) : (1728 : ℂ) * DeltaFun z = E4Fun z ^ 3 - E6Fun z ^ 2 := by
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z
  have h2 : (1728 : ℂ) * ModularForm.discriminant z
      = ModularForm.E₄ z ^ 3 - ModularForm.E₆ z ^ 2 := by
    rw [h]; field_simp
  simpa [Work.Kernels.DeltaFun, Work.Kernels.E4Fun, Work.Kernels.E6Fun] using h2

/-- The weight-ten form `A₁ = E₄²W - E₆(U²-V²)`. -/
private noncomputable def A1 (z : ℍ) : ℂ :=
  E4Fun z ^ 2 * WFun z - E6Fun z * (UFun z ^ 2 - VFun z ^ 2)

/-- The weight-ten form `A₂ = E₄(U²-V²) - E₆W`. -/
private noncomputable def A2 (z : ℍ) : ℂ :=
  E4Fun z * (UFun z ^ 2 - VFun z ^ 2) - E6Fun z * WFun z

/-- The bracket whose vanishing gives `K_-^{clear}(T·S·z,z) = 0`. -/
private noncomputable def Br (ℓ : LogLambdaData) (z : ℍ) : ℂ :=
  (-(UFun z + VFun z) * A1 z + (UFun z ^ 2 + VFun z ^ 2 - 2 * WFun z ^ 2) * A2 z)
      * (ℓ.L_S z + (Real.pi : ℂ) * Complex.I)
    + (-(2 * (1728 * DeltaFun z)) + (UFun z + WFun z) * A1 z
        + (UFun z ^ 2 - 2 * VFun z ^ 2 + WFun z ^ 2) * A2 z) * ℓ.L z

/-- **The two theta identities** `(ξ₂|₂S)A₁ + (ξ₄|₄S)A₂ = 0` and `ξ₂A₁ + ξ₄A₂ = 3456Δ`
kill the bracket. -/
private lemma Br_eq_zero
    (hE4 : ∀ z, E4Fun z = (UFun z ^ 2 + VFun z ^ 2 + WFun z ^ 2) / 2)
    (hE6 : ∀ z, E6Fun z = (WFun z - VFun z) *
      (VFun z ^ 2 + WFun z ^ 2 + (5 / 2) * VFun z * WFun z))
    (hD : ∀ z, (1728 : ℂ) * DeltaFun z = E4Fun z ^ 3 - E6Fun z ^ 2)
    (ℓ : LogLambdaData) (z : ℍ) : Br ℓ z = 0 := by
  simp only [Br, A1, A2]
  rw [hD z, hE4 z, hE6 z, Work.Kernels.TildeFacts.theta_quartic z]
  ring

/-- `Δ·((1728-j)E₈W + jE₆(U²-V²)) = E₄²E₆A₂`. -/
private lemma Y2_eq (hD : ∀ z, (1728 : ℂ) * DeltaFun z = E4Fun z ^ 3 - E6Fun z ^ 2)
    (z : ℍ) :
    DeltaFun z * ((1728 - jInvariantFun z) * E8Fun z * WFun z
        + jInvariantFun z * E6Fun z * (UFun z ^ 2 - VFun z ^ 2))
      = E4Fun z ^ 2 * E6Fun z * A2 z := by
  have hΔ : DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have key : DeltaFun z * ((1728 - jInvariantFun z) * E8Fun z * WFun z
        + jInvariantFun z * E6Fun z * (UFun z ^ 2 - VFun z ^ 2))
      = ((1728 : ℂ) * DeltaFun z - E4Fun z ^ 3) * E4Fun z ^ 2 * WFun z
        + E4Fun z ^ 3 * E6Fun z * (UFun z ^ 2 - VFun z ^ 2) := by
    simp only [jInvariantFun, E8Fun]
    field_simp
  rw [key, hD z]
  simp only [A2]
  ring

/-! ## Entry formula for `Δ(τ)Π(τ) · M · Π(z)` -/

private lemma PiMatDelta_mul_PiMat_entry (a b : Fin 3 → ℤ) (M : Matrix (Fin 3) (Fin 3) ℂ)
    (τ z : ℍ) (i m : Fin 3) :
    (PiMatDelta a τ * M * PiMat b z) i m = (DeltaFun τ * fk (a i) τ) * M i m * fk (b m) z := by
  simp only [PiMatDelta, PiMat]
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

private lemma PiMatDelta_mul_smul_PiMat_entry (a b : Fin 3 → ℤ) (M : Matrix (Fin 3) (Fin 3) ℂ)
    (c : ℂ) (τ z : ℍ) (i m : Fin 3) :
    (PiMatDelta a τ * M * (c • PiMat b z)) i m
      = (DeltaFun τ * fk (a i) τ) * M i m * (c * fk (b m) z) := by
  rw [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, PiMatDelta_mul_PiMat_entry]
  ring

/-! ## The coefficient matrix `Υ_-^{clear}` at `T·S·z` -/

private lemma UC8_TS (z : ℍ) :
    UpsilonMinusClear 8 ((1 : ℝ) +ᵥ (ModularGroup.S • z)) z =
      ((2 * c1728 * (Real.pi : ℂ))⁻¹) •
        (PiMatDelta ![4, 2, 0] ((1 : ℝ) +ᵥ (ModularGroup.S • z)) *
          !![-2 * c1728, 0, 0; 0, 1, -1;
             0, c1728 - jInvariantFun z, jInvariantFun z] *
          PiMat ![10, 8, 6] z) := by
  simp only [UpsilonMinusClear, reduceIte,
    KernelFacts.jInvariantFun_vadd_one, KernelFacts.kpc_jInvariant_S]

private lemma UC24_TS (z : ℍ) :
    UpsilonMinusClear 24 ((1 : ℝ) +ᵥ (ModularGroup.S • z)) z =
      ((2 * c1728 * (Real.pi : ℂ))⁻¹) •
        (PiMatDelta ![12, 10, 8] ((1 : ℝ) +ᵥ (ModularGroup.S • z)) *
          !![-2 * c1728, 0, 0; 0, jInvariantFun z, -1;
             0, c1728 - jInvariantFun z, 1] *
          (DeltaFun z • PiMat ![2, 0, -2] z)) := by
  simp only [UpsilonMinusClear,
    show ¬((24 : ℕ) = 8) by decide, if_false, if_true,
    KernelFacts.jInvariantFun_vadd_one, KernelFacts.kpc_jInvariant_S,
    sub_self, mul_zero, add_zero, sub_zero]

/-! ## Explicit values of `fk` -/

private lemma fk4_all (τ : ℍ) : fk 4 τ = E4Fun τ := by simp only [fk]; norm_num
private lemma fk2_all (τ : ℍ) : fk 2 τ = E14Fun τ / DeltaFun τ := by simp only [fk]; norm_num
private lemma fk0_all (τ : ℍ) : fk 0 τ = 1 := by simp only [fk]; norm_num
private lemma fk10_all (τ : ℍ) : fk 10 τ = E10Fun τ := by simp only [fk]; norm_num
private lemma fk8_all (τ : ℍ) : fk 8 τ = E8Fun τ := by simp only [fk]; norm_num
private lemma fk6_all (τ : ℍ) : fk 6 τ = E6Fun τ := by simp only [fk]; norm_num
private lemma fk12_all (τ : ℍ) : fk 12 τ = DeltaFun τ := by simp only [fk]; norm_num
private lemma fkNeg2_all (τ : ℍ) : fk (-2) τ = E10Fun τ / DeltaFun τ := by simp only [fk]; norm_num

/-! ## The two main computations -/

set_option maxHeartbeats 8000000 in
private lemma KMinusClear_TS_8 (ℓ : LogLambdaData) (z : ℍ) :
    KMinusClear ℓ 8 ((1 : ℝ) +ᵥ (ModularGroup.S • z)) z
      = (z : ℂ) ^ 16 * E4Fun z ^ 2 * E6Fun z / (2 * 1728 * (Real.pi : ℂ)) * Br ℓ z := by
  have hz : (z : ℂ) ≠ 0 := KernelFacts.kpc_tau_ne_zero z
  have hDz : DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpsi2 := psi2_TS ℓ z
  have hpsi4 := psi4_TS ℓ z
  simp only [KMinusClear, Fin.sum_univ_three, psiVec, psitVec, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [hpsi2, hpsi4, UC8_TS z]
  simp only [Matrix.smul_apply, smul_eq_mul, PiMatDelta_mul_PiMat_entry,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.of_apply, mul_zero, zero_mul, zero_add, add_zero, mul_one,
    one_mul, mul_neg, neg_mul]
  rw [fk4_all, fk2_all, fk0_all, fk10_all, fk8_all, fk6_all,
      DeltaFun_TS z, E4Fun_TS z, E14Fun_TS z]
  simp only [E8Fun, E10Fun, E14Fun, Br, A1, A2, jInvariantFun, c1728]
  have hc : (1728 : ℂ) ≠ 0 := by norm_num
  field_simp
  rw [disc_eq z]
  ring

set_option maxHeartbeats 8000000 in
private lemma KMinusClear_TS_24 (ℓ : LogLambdaData) (z : ℍ) :
    KMinusClear ℓ 24 ((1 : ℝ) +ᵥ (ModularGroup.S • z)) z
      = (z : ℂ) ^ 24 * DeltaFun z * E4Fun z ^ 2 * E6Fun z / (2 * 1728 * (Real.pi : ℂ))
          * Br ℓ z := by
  have hz : (z : ℂ) ≠ 0 := KernelFacts.kpc_tau_ne_zero z
  have hDz : DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpsi2 := psi2_TS ℓ z
  have hpsi4 := psi4_TS ℓ z
  simp only [KMinusClear, Fin.sum_univ_three, psiVec, psitVec, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [hpsi2, hpsi4, UC24_TS z]
  simp only [Matrix.smul_apply, smul_eq_mul, PiMatDelta_mul_smul_PiMat_entry,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.of_apply, mul_zero, zero_mul, zero_add, add_zero, mul_one,
    one_mul, mul_neg, neg_mul]
  rw [fk12_all, fk10_all, fk8_all, fk2_all, fk0_all, fkNeg2_all,
      DeltaFun_TS z, E8Fun_TS z, E10Fun_TS z]
  simp only [E8Fun, E10Fun, E14Fun, Br, A1, A2, jInvariantFun, c1728]
  have hc : (1728 : ℂ) ≠ 0 := by norm_num
  field_simp
  rw [disc_eq z]
  ring

end KMinusClearTS

/-- **The cleared kernel `K_-` vanishes at `τ = TS·z = (z−1)/z`**, the point where the
residue of `K_-` is `−(1/2π)φ_-(TS) = 0`. -/
theorem KMinusClear_TS (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : UpperHalfPlane) :
    Work.Kernels.KMinusClear ℓ d ((1 : ℝ) +ᵥ (ModularGroup.S • z)) z = 0 := by
  have hE4 : ∀ z, Work.Kernels.E4Fun z
      = (Work.Kernels.UFun z ^ 2 + Work.Kernels.VFun z ^ 2 + Work.Kernels.WFun z ^ 2) / 2 :=
    KMinusClearTS.E4Fun_eq_theta
  have hE6 : ∀ z, Work.Kernels.E6Fun z
      = (Work.Kernels.WFun z - Work.Kernels.VFun z)
        * (Work.Kernels.VFun z ^ 2 + Work.Kernels.WFun z ^ 2
            + (5 / 2) * Work.Kernels.VFun z * Work.Kernels.WFun z) :=
    Work.Kernels.TildeFacts.E6Fun_eq_theta
  have hD : ∀ z, (1728 : ℂ) * Work.Kernels.DeltaFun z
      = Work.Kernels.E4Fun z ^ 3 - Work.Kernels.E6Fun z ^ 2 :=
    KMinusClearTS.disc_eq
  rcases hd with rfl | rfl
  · rw [KMinusClearTS.KMinusClear_TS_8 ℓ z,
      KMinusClearTS.Br_eq_zero hE4 hE6 hD ℓ z, mul_zero]
  · rw [KMinusClearTS.KMinusClear_TS_24 ℓ z,
      KMinusClearTS.Br_eq_zero hE4 hE6 hD ℓ z, mul_zero]

end Work.Residues

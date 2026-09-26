/-
# The `(T-I)²`-ladder of the cusp coefficients `Gcusp ℓ d`, branch-clean copy

This module is a *branch-clean* copy of the cusp-coefficient `T`-ladder block of
`Submission/Work/Asymptotics/cuspOneBandLadderSmall_TS.lean` (lines 1012--1411), which lives on
the `kernelTransform_seminorm_cuspHalf_TS` import branch.  Every `Gcusp ℓ d i j` (`d ∈ {8,24}`) is
annihilated by `(T-I)²`, hence satisfies the ladder
`G(τ+1) = 2 G(τ) - G(τ-1)`, and the same holds for the cusp model `Aexp (Gcusp ℓ d)`.

The only exported statements are `Gcusp_vadd_ladderTS`, `Aexp_vadd_ladderTS` (and the algebraic
helper `vadd_ladder_of_T2opTS`); everything else is `private`.

## Main results

* `Work.Asymptotics.Gcusp_vadd_ladderTS`;
* `Work.Asymptotics.Aexp_vadd_ladderTS`.
-/
import Mathlib
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Kernels.KernelFacts.psi2_T2
import Submission.Work.Kernels.KernelFacts.psi4_T2
import Submission.Work.Kernels.E2Laws
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.CuspL_eq
import Submission.Work.Asymptotics.Gcusp24_vadd_int

noncomputable section

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

namespace Work.Asymptotics

lemma vadd_ladder_of_T2opTS {F : ℍ → ℂ} (h : Work.Kernels.T2op F = 0) (u : ℍ) :
    F ((1 : ℝ) +ᵥ u) = 2 * F u - F ((-1 : ℝ) +ᵥ u) := by
  have h1 := congr_fun h ((-1 : ℝ) +ᵥ u)
  simp only [Work.Kernels.T2op, Pi.zero_apply] at h1
  have h2 : (2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ u) = (1 : ℝ) +ᵥ u := by
    rw [← add_vadd]; norm_num
  have h3 : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ u) = u := by
    rw [← add_vadd]; norm_num
  rw [h2, h3] at h1
  linear_combination h1

private lemma T2op_congr_L {F G : ℍ → ℂ} (h : F = G) (hG : Work.Kernels.T2op G = 0) :
    Work.Kernels.T2op F = 0 := by rw [h]; exact hG

private lemma T2op_periodic_L {F : ℍ → ℂ} (h : ∀ τ, F ((1 : ℝ) +ᵥ τ) = F τ) :
    Work.Kernels.T2op F = 0 := by
  ext τ
  have h2 : F ((2 : ℝ) +ᵥ τ) = F τ := by
    rw [show (2 : ℝ) +ᵥ τ = (1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ) from by rw [← add_vadd]; norm_num, h, h]
  simp only [Work.Kernels.T2op, Pi.zero_apply]
  rw [h2, h]
  ring

private lemma T2op_const_mul_L (c : ℂ) {F : ℍ → ℂ} (h : Work.Kernels.T2op F = 0) :
    Work.Kernels.T2op (fun τ => c * F τ) = 0 := by
  ext τ
  have h1 := congr_fun h τ
  simp only [Work.Kernels.T2op, Pi.zero_apply] at h1 ⊢
  linear_combination c * h1

private lemma T2op_sub_L {F G : ℍ → ℂ} (hF : Work.Kernels.T2op F = 0)
    (hG : Work.Kernels.T2op G = 0) :
    Work.Kernels.T2op (fun τ => F τ - G τ) = 0 := by
  ext τ
  have h1 := congr_fun hF τ
  have h2 := congr_fun hG τ
  simp only [Work.Kernels.T2op, Pi.zero_apply] at h1 h2 ⊢
  linear_combination h1 - h2

private lemma T2op_div_const_L (c : ℂ) {F : ℍ → ℂ} (h : Work.Kernels.T2op F = 0) :
    Work.Kernels.T2op (fun τ => F τ / c) = 0 := by
  refine T2op_congr_L (G := fun τ => c⁻¹ * F τ) ?_ (T2op_const_mul_L c⁻¹ h)
  funext τ; rw [div_eq_mul_inv, mul_comm]

private lemma per_E4_L : ∀ τ : ℍ, Work.Kernels.E4Fun ((1 : ℝ) +ᵥ τ) = Work.Kernels.E4Fun τ :=
  fun τ => Work.Kernels.KernelFacts.E4Fun_vadd_one τ

private lemma per_E6_L : ∀ τ : ℍ, Work.Kernels.E6Fun ((1 : ℝ) +ᵥ τ) = Work.Kernels.E6Fun τ :=
  fun τ => Work.Kernels.KernelFacts.E6Fun_vadd_one τ

private lemma per_Delta_L : ∀ τ : ℍ, Work.Kernels.DeltaFun ((1 : ℝ) +ᵥ τ) = Work.Kernels.DeltaFun τ :=
  fun τ => Work.Kernels.KernelFacts.DeltaFun_vadd_one τ

private lemma per_E4sq_L : ∀ τ : ℍ,
    (fun σ : ℍ => Work.Kernels.E4Fun σ ^ 2) ((1 : ℝ) +ᵥ τ)
      = (fun σ : ℍ => Work.Kernels.E4Fun σ ^ 2) τ := by
  intro τ
  show Work.Kernels.E4Fun ((1 : ℝ) +ᵥ τ) ^ 2 = Work.Kernels.E4Fun τ ^ 2
  rw [Work.Kernels.KernelFacts.E4Fun_vadd_one]

private lemma per_E4cube_L : ∀ τ : ℍ,
    (fun σ : ℍ => Work.Kernels.E4Fun σ ^ 3) ((1 : ℝ) +ᵥ τ)
      = (fun σ : ℍ => Work.Kernels.E4Fun σ ^ 3) τ := by
  intro τ
  show Work.Kernels.E4Fun ((1 : ℝ) +ᵥ τ) ^ 3 = Work.Kernels.E4Fun τ ^ 3
  rw [Work.Kernels.KernelFacts.E4Fun_vadd_one]

private lemma per_E4E6_L : ∀ τ : ℍ,
    (fun σ : ℍ => Work.Kernels.E4Fun σ * Work.Kernels.E6Fun σ) ((1 : ℝ) +ᵥ τ)
      = (fun σ : ℍ => Work.Kernels.E4Fun σ * Work.Kernels.E6Fun σ) τ := by
  intro τ
  show Work.Kernels.E4Fun ((1 : ℝ) +ᵥ τ) * Work.Kernels.E6Fun ((1 : ℝ) +ᵥ τ) = Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ
  rw [Work.Kernels.KernelFacts.E4Fun_vadd_one, Work.Kernels.KernelFacts.E6Fun_vadd_one]

private lemma per_E4sqE6_L : ∀ τ : ℍ,
    (fun σ : ℍ => Work.Kernels.E4Fun σ ^ 2 * Work.Kernels.E6Fun σ) ((1 : ℝ) +ᵥ τ)
      = (fun σ : ℍ => Work.Kernels.E4Fun σ ^ 2 * Work.Kernels.E6Fun σ) τ := by
  intro τ
  show Work.Kernels.E4Fun ((1 : ℝ) +ᵥ τ) ^ 2 * Work.Kernels.E6Fun ((1 : ℝ) +ᵥ τ)
      = Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ
  rw [Work.Kernels.KernelFacts.E4Fun_vadd_one, Work.Kernels.KernelFacts.E6Fun_vadd_one]

private lemma T2op_phiVec0_L : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.phiVec τ 0) = 0 := by
  refine T2op_congr_L (G := Work.Kernels.phiNeg2) ?_ Work.Kernels.phiNeg2_T2
  funext τ; simp [Work.Kernels.phiVec]

private lemma T2op_phiVec1_L : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.phiVec τ 1) = 0 := by
  refine T2op_congr_L (G := Work.Kernels.phi0) ?_ Work.Kernels.phi0_T2
  funext τ; simp [Work.Kernels.phiVec]

private lemma T2op_phiVec2_L : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.phiVec τ 2) = 0 := by
  refine T2op_congr_L (G := Work.Kernels.phi2) ?_ Work.Kernels.phi2_T2
  funext τ; simp [Work.Kernels.phiVec]

private lemma T2op_psi2_L (ℓ : Work.Kernels.LogLambdaData) :
    Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.psi2 ℓ τ) = 0 :=
  Work.Kernels.KernelFacts.psi2_T2 ℓ

private lemma T2op_psi4_L (ℓ : Work.Kernels.LogLambdaData) :
    Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) = 0 :=
  Work.Kernels.KernelFacts.psi4_T2 ℓ

private lemma T2op_E4_L : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.E4Fun τ) = 0 :=
  T2op_periodic_L per_E4_L

private lemma T2op_E6_L : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.E6Fun τ) = 0 :=
  T2op_periodic_L per_E6_L

private lemma T2op_Delta_L : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.DeltaFun τ) = 0 :=
  T2op_periodic_L per_Delta_L

private lemma E4Fun_vadd_neg_one_L (τ : ℍ) :
    Work.Kernels.E4Fun ((-1 : ℝ) +ᵥ τ) = Work.Kernels.E4Fun τ := by
  have h := Work.Kernels.KernelFacts.E4Fun_vadd_one ((-1 : ℝ) +ᵥ τ)
  rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ from by rw [← add_vadd]; norm_num] at h
  exact h.symm

private lemma E6Fun_vadd_neg_one_L (τ : ℍ) :
    Work.Kernels.E6Fun ((-1 : ℝ) +ᵥ τ) = Work.Kernels.E6Fun τ := by
  have h := Work.Kernels.KernelFacts.E6Fun_vadd_one ((-1 : ℝ) +ᵥ τ)
  rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ from by rw [← add_vadd]; norm_num] at h
  exact h.symm

private lemma DeltaFun_vadd_neg_one_L (τ : ℍ) :
    Work.Kernels.DeltaFun ((-1 : ℝ) +ᵥ τ) = Work.Kernels.DeltaFun τ := by
  have h := Work.Kernels.KernelFacts.DeltaFun_vadd_one ((-1 : ℝ) +ᵥ τ)
  rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ from by rw [← add_vadd]; norm_num] at h
  exact h.symm

/-- The `T`-ladder of the three components of `phiVec`. -/
private lemma phiVec_vadd_ladderTS (k : Fin 3) (τ : ℍ) :
    Work.Kernels.phiVec ((1 : ℝ) +ᵥ τ) k
      = 2 * Work.Kernels.phiVec τ k - Work.Kernels.phiVec ((-1 : ℝ) +ᵥ τ) k := by
  fin_cases k
  · exact vadd_ladder_of_T2opTS T2op_phiVec0_L τ
  · exact vadd_ladder_of_T2opTS T2op_phiVec1_L τ
  · exact vadd_ladder_of_T2opTS T2op_phiVec2_L τ

private lemma psi2_vadd_ladder_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Kernels.psi2 ℓ ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Kernels.psi2 ℓ τ - Work.Kernels.psi2 ℓ ((-1 : ℝ) +ᵥ τ) :=
  vadd_ladder_of_T2opTS (T2op_psi2_L ℓ) τ

private lemma psi4_vadd_ladder_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Kernels.psi4 ℓ ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Kernels.psi4 ℓ τ - Work.Kernels.psi4 ℓ ((-1 : ℝ) +ᵥ τ) :=
  vadd_ladder_of_T2opTS (T2op_psi4_L ℓ) τ

private lemma Gcusp8_00_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Gcusp8 ℓ 0 0 ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp8 ℓ 0 0 τ
        - Work.Asymptotics.Gcusp8 ℓ 0 0 ((-1 : ℝ) +ᵥ τ) := by
  have hbase : Work.Kernels.T2op (fun τ : ℍ => Work.Asymptotics.Gcusp8 ℓ 0 0 τ) = 0 := by
    have hA : Work.Kernels.T2op (fun τ : ℍ =>
        (Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ) * (-Complex.I)) = 0 :=
      Work.Kernels.T2op_mul_of (Work.Kernels.T2op_mul_of T2op_phiVec0_L per_E6_L)
        (fun _ => rfl)
    have hB : Work.Kernels.T2op (fun τ : ℍ =>
        Work.Kernels.E4Fun τ * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)) = 0 :=
      T2op_div_const_L _ (Work.Kernels.T2op_mul_of T2op_E4_L (fun _ => rfl))
    have hC : Work.Kernels.T2op (fun τ : ℍ =>
        Work.Kernels.psi4 ℓ τ / (2 * (Real.pi : ℂ))) = 0 :=
      T2op_div_const_L _ (T2op_psi4_L ℓ)
    have hsum : Work.Kernels.T2op (fun τ : ℍ =>
        ((Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ) * (-Complex.I)
          + Work.Kernels.E4Fun τ * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)
          - Work.Kernels.psi4 ℓ τ / (2 * (Real.pi : ℂ))) / 2) = 0 :=
      T2op_div_const_L 2 (T2op_sub_L (Work.Kernels.T2op_add hA hB) hC)
    refine T2op_congr_L (G := fun τ : ℍ =>
        ((Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ) * (-Complex.I)
          + Work.Kernels.E4Fun τ * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)
          - Work.Kernels.psi4 ℓ τ / (2 * (Real.pi : ℂ))) / 2) ?_ hsum
    funext τ
    rw [Work.Asymptotics.Gcusp8, if_neg (by decide : ¬ ((0 : Fin 2) = 1)),
      if_pos (by decide : ((0 : Fin 2) = 0))]
  exact vadd_ladder_of_T2opTS hbase τ

private lemma Gcusp8_01_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Gcusp8 ℓ 0 1 ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp8 ℓ 0 1 τ
        - Work.Asymptotics.Gcusp8 ℓ 0 1 ((-1 : ℝ) +ᵥ τ) := by
  have hbase : Work.Kernels.T2op (fun τ : ℍ => Work.Asymptotics.Gcusp8 ℓ 0 1 τ) = 0 := by
    have hA : Work.Kernels.T2op (fun τ : ℍ =>
        (Real.pi : ℂ) / 3 * (Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ
          - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ)) = 0 :=
      T2op_const_mul_L _ (T2op_sub_L
        (Work.Kernels.T2op_mul_of T2op_phiVec0_L per_E6_L)
        (Work.Kernels.T2op_mul_of T2op_phiVec1_L per_E4_L))
    have hB : Work.Kernels.T2op (fun τ : ℍ => Complex.I * Work.Kernels.E4Fun τ) = 0 :=
      T2op_const_mul_L _ T2op_E4_L
    have hsum : Work.Kernels.T2op (fun τ : ℍ =>
        ((Real.pi : ℂ) / 3 * (Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ
            - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ)
          + Complex.I * Work.Kernels.E4Fun τ) / 2) = 0 :=
      T2op_div_const_L 2 (Work.Kernels.T2op_add hA hB)
    refine T2op_congr_L (G := fun τ : ℍ =>
        ((Real.pi : ℂ) / 3 * (Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ
            - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ)
          + Complex.I * Work.Kernels.E4Fun τ) / 2) ?_ hsum
    funext τ
    rw [Work.Asymptotics.Gcusp8, if_neg (by decide : ¬ ((0 : Fin 2) = 1)),
      if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
  exact vadd_ladder_of_T2opTS hbase τ

private lemma Gcusp8_10_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Gcusp8 ℓ 1 0 ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp8 ℓ 1 0 τ
        - Work.Asymptotics.Gcusp8 ℓ 1 0 ((-1 : ℝ) +ᵥ τ) := by
  have h : ∀ σ : ℍ, Work.Asymptotics.Gcusp8 ℓ 1 0 σ = 0 := by
    intro σ
    rw [Work.Asymptotics.Gcusp8, if_pos (by decide : ((1 : Fin 2) = 1))]
  rw [h ((1 : ℝ) +ᵥ τ), h τ, h ((-1 : ℝ) +ᵥ τ)]
  ring

private lemma Gcusp8_11_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Gcusp8 ℓ 1 1 ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp8 ℓ 1 1 τ
        - Work.Asymptotics.Gcusp8 ℓ 1 1 ((-1 : ℝ) +ᵥ τ) := by
  have h : ∀ σ : ℍ, Work.Asymptotics.Gcusp8 ℓ 1 1 σ = 0 := by
    intro σ
    rw [Work.Asymptotics.Gcusp8, if_pos (by decide : ((1 : Fin 2) = 1))]
  rw [h ((1 : ℝ) +ᵥ τ), h τ, h ((-1 : ℝ) +ᵥ τ)]
  ring

private lemma Gcusp24_00_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Gcusp24 ℓ 0 0 ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp24 ℓ 0 0 τ
        - Work.Asymptotics.Gcusp24 ℓ 0 0 ((-1 : ℝ) +ᵥ τ) := by
  have hbase : Work.Kernels.T2op (fun τ : ℍ => Work.Asymptotics.Gcusp24 ℓ 0 0 τ) = 0 := by
    have h1 : Work.Kernels.T2op (fun τ : ℍ => -(13 * Complex.I / 12)
        * (Work.Kernels.phiVec τ 0
          * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ))) = 0 :=
      T2op_const_mul_L _ (Work.Kernels.T2op_mul_of T2op_phiVec0_L per_E4sqE6_L)
    have h2 : Work.Kernels.T2op (fun τ : ℍ => Complex.I / 6
        * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)) = 0 :=
      T2op_const_mul_L _ (Work.Kernels.T2op_mul_of T2op_phiVec1_L per_E4cube_L)
    have h3 : Work.Kernels.T2op (fun τ : ℍ => 168 * Complex.I
        * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)) = 0 :=
      T2op_const_mul_L _ (Work.Kernels.T2op_mul_of T2op_phiVec1_L per_Delta_L)
    have h4 : Work.Kernels.T2op (fun τ : ℍ => Complex.I / 12
        * (Work.Kernels.phiVec τ 2
          * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))) = 0 :=
      T2op_const_mul_L _ (Work.Kernels.T2op_mul_of T2op_phiVec2_L per_E4E6_L)
    have h5 : Work.Kernels.T2op (fun τ : ℍ => 720 * Work.Kernels.DeltaFun τ
        * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)) = 0 :=
      T2op_div_const_L _ (Work.Kernels.T2op_mul_of
        (T2op_const_mul_L 720 T2op_Delta_L) (fun _ => rfl))
    have h6 : Work.Kernels.T2op (fun τ : ℍ => 36 * Work.Kernels.DeltaFun τ
        / (Real.pi : ℂ)) = 0 :=
      T2op_div_const_L _ (T2op_const_mul_L 36 T2op_Delta_L)
    have h7 : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.E4Fun τ ^ 3
        * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)) = 0 :=
      T2op_div_const_L _ (Work.Kernels.T2op_mul_of
        (T2op_periodic_L per_E4cube_L) (fun _ => rfl))
    have h8 : Work.Kernels.T2op (fun τ : ℍ => 7 * (Work.Kernels.psi2 ℓ τ
        * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)) / (24 * (Real.pi : ℂ))) = 0 :=
      T2op_div_const_L _ (T2op_const_mul_L 7
        (Work.Kernels.T2op_mul_of (T2op_psi2_L ℓ) per_E4E6_L))
    have h9 : Work.Kernels.T2op (fun τ : ℍ => 5 * (Work.Kernels.psi4 ℓ τ
        * Work.Kernels.E4Fun τ ^ 2) / (24 * (Real.pi : ℂ))) = 0 :=
      T2op_div_const_L _ (T2op_const_mul_L 5
        (Work.Kernels.T2op_mul_of (T2op_psi4_L ℓ) per_E4sq_L))
    have hsum : Work.Kernels.T2op (fun τ : ℍ =>
        (-(13 * Complex.I / 12) * (Work.Kernels.phiVec τ 0
            * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ))
          + Complex.I / 6 * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)
          - 168 * Complex.I * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)
          - Complex.I / 12 * (Work.Kernels.phiVec τ 2
              * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))
          - 720 * Work.Kernels.DeltaFun τ * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)
          - 36 * Work.Kernels.DeltaFun τ / (Real.pi : ℂ)
          + Work.Kernels.E4Fun τ ^ 3 * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)
          - 7 * (Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))
              / (24 * (Real.pi : ℂ))
          - 5 * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2)
              / (24 * (Real.pi : ℂ))) / 2) = 0 :=
      T2op_div_const_L 2 (T2op_sub_L (T2op_sub_L (Work.Kernels.T2op_add
        (T2op_sub_L (T2op_sub_L (T2op_sub_L (T2op_sub_L
          (Work.Kernels.T2op_add h1 h2) h3) h4) h5) h6) h7) h8) h9)
    refine T2op_congr_L (G := fun τ : ℍ =>
        (-(13 * Complex.I / 12) * (Work.Kernels.phiVec τ 0
            * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ))
          + Complex.I / 6 * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)
          - 168 * Complex.I * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)
          - Complex.I / 12 * (Work.Kernels.phiVec τ 2
              * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))
          - 720 * Work.Kernels.DeltaFun τ * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)
          - 36 * Work.Kernels.DeltaFun τ / (Real.pi : ℂ)
          + Work.Kernels.E4Fun τ ^ 3 * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)
          - 7 * (Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))
              / (24 * (Real.pi : ℂ))
          - 5 * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2)
              / (24 * (Real.pi : ℂ))) / 2) ?_ hsum
    funext τ
    dsimp only [Work.Asymptotics.Gcusp24]
    rw [if_pos (by decide : ((0 : Fin 2) = 0 ∧ (0 : Fin 2) = 0))]
  exact vadd_ladder_of_T2opTS hbase τ

private lemma Gcusp24_01_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Gcusp24 ℓ 0 1 ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp24 ℓ 0 1 τ
        - Work.Asymptotics.Gcusp24 ℓ 0 1 ((-1 : ℝ) +ᵥ τ) := by
  have hbase : Work.Kernels.T2op (fun τ : ℍ => Work.Asymptotics.Gcusp24 ℓ 0 1 τ) = 0 := by
    have hA : Work.Kernels.T2op (fun τ : ℍ => (Real.pi : ℂ) / 3
        * (Work.Kernels.phiVec τ 0 * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)
          + 720 * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)
          - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)) = 0 :=
      T2op_const_mul_L _ (T2op_sub_L (Work.Kernels.T2op_add
        (Work.Kernels.T2op_mul_of T2op_phiVec0_L per_E4sqE6_L)
        (T2op_const_mul_L 720 (Work.Kernels.T2op_mul_of T2op_phiVec1_L per_Delta_L)))
        (Work.Kernels.T2op_mul_of T2op_phiVec1_L per_E4cube_L))
    have hB : Work.Kernels.T2op (fun τ : ℍ => Complex.I * (720 * Work.Kernels.DeltaFun τ
        - Work.Kernels.E4Fun τ ^ 3)) = 0 :=
      T2op_const_mul_L _ (T2op_sub_L (T2op_const_mul_L 720 T2op_Delta_L)
        (T2op_periodic_L per_E4cube_L))
    have hsum : Work.Kernels.T2op (fun τ : ℍ =>
        ((Real.pi : ℂ) / 3
            * (Work.Kernels.phiVec τ 0 * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)
              + 720 * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)
              - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)
          - Complex.I * (720 * Work.Kernels.DeltaFun τ
              - Work.Kernels.E4Fun τ ^ 3)) / 2) = 0 :=
      T2op_div_const_L 2 (T2op_sub_L hA hB)
    refine T2op_congr_L (G := fun τ : ℍ =>
        ((Real.pi : ℂ) / 3
            * (Work.Kernels.phiVec τ 0 * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)
              + 720 * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)
              - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)
          - Complex.I * (720 * Work.Kernels.DeltaFun τ
              - Work.Kernels.E4Fun τ ^ 3)) / 2) ?_ hsum
    funext τ
    dsimp only [Work.Asymptotics.Gcusp24]
    rw [if_neg (by decide : ¬ ((0 : Fin 2) = 0 ∧ (1 : Fin 2) = 0)),
      if_pos (by decide : ((0 : Fin 2) = 0 ∧ (1 : Fin 2) = 1))]
  exact vadd_ladder_of_T2opTS hbase τ

private lemma Gcusp24_10_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Gcusp24 ℓ 1 0 ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp24 ℓ 1 0 τ
        - Work.Asymptotics.Gcusp24 ℓ 1 0 ((-1 : ℝ) +ᵥ τ) := by
  have h := Work.Asymptotics.Gcusp10_vadd_int ℓ (-1) τ
  have h1 : Work.Asymptotics.Gcusp24 ℓ 1 0 ((-1 : ℝ) +ᵥ τ)
      = Work.Asymptotics.Gcusp24 ℓ 1 0 τ
        + (-1 : ℂ) * (Work.Asymptotics.Gcusp24 ℓ 1 0 ((1 : ℝ) +ᵥ τ)
          - Work.Asymptotics.Gcusp24 ℓ 1 0 τ) := by
    have h2 : ((↑(-1 : ℤ) : ℝ)) = (-1 : ℝ) := by norm_num
    rw [h2] at h
    simpa [Work.Asymptotics.Gcusp] using h
  rw [h1]; ring

private lemma Gcusp24_11_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Gcusp24 ℓ 1 1 ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp24 ℓ 1 1 τ
        - Work.Asymptotics.Gcusp24 ℓ 1 1 ((-1 : ℝ) +ᵥ τ) := by
  have h := Work.Asymptotics.Gcusp11_vadd_int ℓ (-1) τ
  have h1 : Work.Asymptotics.Gcusp24 ℓ 1 1 ((-1 : ℝ) +ᵥ τ)
      = Work.Asymptotics.Gcusp24 ℓ 1 1 τ
        + Complex.I / 3456 * (2 * (Real.pi : ℂ) * Complex.I) * Work.Asymptotics.A24 τ := by
    have h2 : ((↑(-1 : ℤ) : ℝ)) = (-1 : ℝ) := by norm_num
    rw [h2] at h
    simpa [Work.Asymptotics.Gcusp] using h
  have h3 : Work.Asymptotics.Gcusp24 ℓ 1 1 ((1 : ℝ) +ᵥ τ)
      = Work.Asymptotics.Gcusp24 ℓ 1 1 τ
        - Complex.I / 3456 * (2 * (Real.pi : ℂ) * Complex.I) * Work.Asymptotics.A24 τ := by
    simpa [Work.Asymptotics.Gcusp] using Work.Asymptotics.Gcusp11_vadd_int ℓ 1 τ
  rw [h1, h3]; ring

/-- **The `T`-ladder of the cusp coefficients.**  Every entry of `Gcusp ℓ d` (`d = 8` or `24`)
is annihilated by `(T-I)²`: `G(τ+1) = 2G(τ) - G(τ-1)`. -/
theorem Gcusp_vadd_ladderTS (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (i j : Fin 2) (τ : ℍ) :
    Work.Asymptotics.Gcusp ℓ d i j ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp ℓ d i j τ
        - Work.Asymptotics.Gcusp ℓ d i j ((-1 : ℝ) +ᵥ τ) := by
  rcases hd with h8 | h24
  · subst h8
    fin_cases i <;> fin_cases j
    · simpa [Work.Asymptotics.Gcusp] using Gcusp8_00_L ℓ τ
    · simpa [Work.Asymptotics.Gcusp] using Gcusp8_01_L ℓ τ
    · simpa [Work.Asymptotics.Gcusp] using Gcusp8_10_L ℓ τ
    · simpa [Work.Asymptotics.Gcusp] using Gcusp8_11_L ℓ τ
  · subst h24
    fin_cases i <;> fin_cases j
    · simpa [Work.Asymptotics.Gcusp] using Gcusp24_00_L ℓ τ
    · simpa [Work.Asymptotics.Gcusp] using Gcusp24_01_L ℓ τ
    · simpa [Work.Asymptotics.Gcusp] using Gcusp24_10_L ℓ τ
    · simpa [Work.Asymptotics.Gcusp] using Gcusp24_11_L ℓ τ

/-- **The `T`-ladder of the cusp model `Aexp`.** -/
theorem Aexp_vadd_ladderTS (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) (t : ℝ) :
    Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ τ) t
      = 2 * Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ τ) t := by
  simp only [Work.Asymptotics.Aexp]
  rw [Gcusp_vadd_ladderTS ℓ d hd 0 0 τ, Gcusp_vadd_ladderTS ℓ d hd 0 1 τ,
    Gcusp_vadd_ladderTS ℓ d hd 1 0 τ, Gcusp_vadd_ladderTS ℓ d hd 1 1 τ]
  ring



end Work.Asymptotics

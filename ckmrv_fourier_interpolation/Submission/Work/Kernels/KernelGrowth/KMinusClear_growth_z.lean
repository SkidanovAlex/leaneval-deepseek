import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.E4Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.E6Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.theta00Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.theta01Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.theta10Fun_mem_InP

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels.KernelGrowth

/-! ## Membership in `𝒫` of the classical functions used in `K_-^{(d)}` -/

private lemma E8InP : Work.Kernels.InP Work.Kernels.E8Fun :=
  Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 2

private lemma E10InP : Work.Kernels.InP Work.Kernels.E10Fun :=
  Work.Kernels.ClassicalFacts.E4Fun_mem_InP.mul Work.Kernels.ClassicalFacts.E6Fun_mem_InP

private lemma E14InP : Work.Kernels.InP Work.Kernels.E14Fun :=
  (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 2).mul
    Work.Kernels.ClassicalFacts.E6Fun_mem_InP

private lemma DeltaInP : Work.Kernels.InP Work.Kernels.DeltaFun :=
  Work.Kernels.ClassicalFacts.DeltaFun_mem_InP

private lemma WFunInP : Work.Kernels.InP Work.Kernels.WFun :=
  Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.pow 4

private lemma UFunInP : Work.Kernels.InP Work.Kernels.UFun :=
  Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.pow 4

private lemma VFunInP : Work.Kernels.InP Work.Kernels.VFun :=
  Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.pow 4

private lemma UWVInP : Work.Kernels.InP (fun z => Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2) :=
  (UFunInP.pow 2).sub (VFunInP.pow 2)

private lemma jDInP : Work.Kernels.InP (fun z => Work.Kernels.jInvariantFun z * Work.Kernels.DeltaFun z) := by
  have h : (fun z => Work.Kernels.jInvariantFun z * Work.Kernels.DeltaFun z)
      = fun z => Work.Kernels.E4Fun z ^ 3 := by
    funext z; rw [mul_comm, Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
  rw [h]; exact Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 3

private lemma fk10InP : Work.Kernels.InP (fun z => Work.Kernels.fk (10:ℤ) z) := by
  have h : (fun z => Work.Kernels.fk (10:ℤ) z) = Work.Kernels.E10Fun := by
    funext z; simp [Work.Kernels.fk]
  rw [h]; exact E10InP

private lemma fk8InP : Work.Kernels.InP (fun z => Work.Kernels.fk (8:ℤ) z) := by
  have h : (fun z => Work.Kernels.fk (8:ℤ) z) = Work.Kernels.E8Fun := by
    funext z; simp [Work.Kernels.fk]
  rw [h]; exact E8InP

private lemma fk6InP : Work.Kernels.InP (fun z => Work.Kernels.fk (6:ℤ) z) := by
  have h : (fun z => Work.Kernels.fk (6:ℤ) z) = Work.Kernels.E6Fun := by
    funext z; simp [Work.Kernels.fk]
  rw [h]; exact Work.Kernels.ClassicalFacts.E6Fun_mem_InP

private lemma Dfk2 (z : ℍ) : Work.Kernels.DeltaFun z * Work.Kernels.fk (2:ℤ) z = Work.Kernels.E14Fun z := by
  have h := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  rw [show Work.Kernels.fk (2:ℤ) z = Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z by
    simp [Work.Kernels.fk]]
  field_simp

private lemma Dfk0 (z : ℍ) : Work.Kernels.DeltaFun z * Work.Kernels.fk (0:ℤ) z = Work.Kernels.DeltaFun z := by
  rw [show Work.Kernels.fk (0:ℤ) z = 1 by simp [Work.Kernels.fk], mul_one]

private lemma Dfkm2 (z : ℍ) : Work.Kernels.DeltaFun z * Work.Kernels.fk (-2:ℤ) z = Work.Kernels.E10Fun z := by
  have h := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  rw [show Work.Kernels.fk (-2:ℤ) z = Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z by
    simp [Work.Kernels.fk]]
  field_simp

/-! ## The `B` matrices and the entry formulas for `Υ_-^{clear}` -/

private def B8 (τ : ℍ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-2 * Work.Kernels.c1728, 0, 0; 0, 1, -1;
     0, Work.Kernels.c1728 - Work.Kernels.jInvariantFun τ, Work.Kernels.jInvariantFun τ]

private def B24 (τ z : ℍ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-2 * Work.Kernels.c1728,
      -2 * Work.Kernels.c1728 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z), 0;
     0, Work.Kernels.jInvariantFun τ + 2 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z), -1;
     0, Work.Kernels.c1728 - 2 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) - Work.Kernels.jInvariantFun τ, 1]

private lemma smul_diagonal_aux {c : ℂ} {g : Fin 3 → ℂ} :
    c • Matrix.diagonal g = Matrix.diagonal (fun j => c * g j) := by
  ext i j
  rw [Matrix.smul_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

private lemma umc8_eq (τ z : ℍ) :
    Work.Kernels.UpsilonMinusClear 8 τ z =
      (((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹) •
      (Work.Kernels.PiMatDelta ![4,2,0] τ * B8 τ * Work.Kernels.PiMat ![10,8,6] z) := by
  simp only [Work.Kernels.UpsilonMinusClear]
  rw [if_pos trivial]
  rfl

private lemma umc24_eq (τ z : ℍ) :
    Work.Kernels.UpsilonMinusClear 24 τ z =
      (((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹) •
      (Work.Kernels.PiMatDelta ![12,10,8] τ * B24 τ z *
        (Work.Kernels.DeltaFun z • Work.Kernels.PiMat ![2,0,-2] z)) := by
  simp only [Work.Kernels.UpsilonMinusClear]
  rw [if_neg (by norm_num : ¬ ((24:ℕ) = 8)), if_pos trivial]
  rfl

private lemma umc8_apply (τ z : ℍ) (i j : Fin 3) :
    Work.Kernels.UpsilonMinusClear 8 τ z i j =
      (((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹) *
      ((Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4,2,0] i) τ) * B8 τ i j *
        Work.Kernels.fk (![10,8,6] j) z) := by
  rw [umc8_eq]
  simp only [Matrix.smul_apply, Work.Kernels.PiMatDelta, Work.Kernels.PiMat,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

private lemma umc24_apply (τ z : ℍ) (i j : Fin 3) :
    Work.Kernels.UpsilonMinusClear 24 τ z i j =
      (((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹) *
      ((Work.Kernels.DeltaFun τ * Work.Kernels.fk (![12,10,8] i) τ) * B24 τ z i j *
        (Work.Kernels.DeltaFun z * Work.Kernels.fk (![2,0,-2] j) z)) := by
  rw [umc24_eq]
  simp only [Matrix.smul_apply, Work.Kernels.PiMatDelta, Work.Kernels.PiMat,
    Matrix.diagonal_mul, Matrix.mul_diagonal, smul_diagonal_aux]
  ring

/-! ## Closure of `𝒫` under finite sums of functions -/

private lemma InP_sum_fun {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ}
    (h : ∀ i ∈ s, Work.Kernels.InP (F i)) :
    Work.Kernels.InP (fun z => ∑ i ∈ s, F i z) := by
  have hsum := Work.Kernels.InP.sum s h
  have heq : (∑ i ∈ s, F i) = fun z => ∑ i ∈ s, F i z := by
    funext z; rw [Finset.sum_apply]
  rwa [heq] at hsum

/-! ## The `𝒫`-membership of the entries of `Υ_-^{clear}` -/

/-- Transfer `𝒫`-membership across a pointwise equality of functions. -/
private lemma InP_congr {F G : ℍ → ℂ} (h : F = G) (hF : Work.Kernels.InP F) :
    Work.Kernels.InP G := h ▸ hF

private lemma fk_w8_InP (j : Fin 3) :
    Work.Kernels.InP (fun z => Work.Kernels.fk (![10,8,6] j) z) := by
  have h10 := fk10InP
  have h8 := fk8InP
  have h6 := fk6InP
  fin_cases j
  · simpa using h10
  · simpa using h8
  · simpa using h6

private lemma UpsilonMinusClear8_InP (τ : ℍ) (i j : Fin 3) :
    Work.Kernels.InP (fun z => Work.Kernels.UpsilonMinusClear 8 τ z i j) := by
  have heq : (fun z => Work.Kernels.UpsilonMinusClear 8 τ z i j)
      = fun z => (((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹ *
          ((Work.Kernels.DeltaFun τ * Work.Kernels.fk (![4,2,0] i) τ) * B8 τ i j)) *
          Work.Kernels.fk (![10,8,6] j) z := by
    funext z
    rw [umc8_apply]
    ring
  rw [heq]
  exact Work.Kernels.InP.const_mul _ (fk_w8_InP j)

private lemma B24_product_InP (τ : ℍ) (i j : Fin 3) :
    Work.Kernels.InP (fun z => B24 τ z i j *
      (Work.Kernels.DeltaFun z * Work.Kernels.fk (![2,0,-2] j) z)) := by
  have hj0 : j = (0:Fin 3) ∨ j = (1:Fin 3) ∨ j = (2:Fin 3) := by fin_cases j <;> simp
  obtain rfl | rfl | rfl := hj0
  · have hi0 : i = (0:Fin 3) ∨ i = (1:Fin 3) ∨ i = (2:Fin 3) := by fin_cases i <;> simp
    obtain rfl | rfl | rfl := hi0
    · exact InP_congr (by
        funext z
        rw [show Work.Kernels.fk (![2,0,-2] (0:Fin 3)) z = Work.Kernels.fk (2:ℤ) z from rfl, Dfk2,
          show B24 τ z (0:Fin 3) (0:Fin 3) = -2 * Work.Kernels.c1728 from rfl]
        try rfl)
        (Work.Kernels.InP.const_mul (-2 * Work.Kernels.c1728) E14InP)
    · exact InP_congr (by
        funext z
        rw [show Work.Kernels.fk (![2,0,-2] (0:Fin 3)) z = Work.Kernels.fk (2:ℤ) z from rfl, Dfk2,
          show B24 τ z (1:Fin 3) (0:Fin 3) = 0 from rfl]
        try ring)
        Work.Kernels.InP.zero
    · exact InP_congr (by
        funext z
        rw [show Work.Kernels.fk (![2,0,-2] (0:Fin 3)) z = Work.Kernels.fk (2:ℤ) z from rfl, Dfk2,
          show B24 τ z (2:Fin 3) (0:Fin 3) = 0 from rfl]
        try ring)
        Work.Kernels.InP.zero
  · have hi0 : i = (0:Fin 3) ∨ i = (1:Fin 3) ∨ i = (2:Fin 3) := by fin_cases i <;> simp
    obtain rfl | rfl | rfl := hi0
    · exact InP_congr (by
        funext z
        rw [show Work.Kernels.fk (![2,0,-2] (1:Fin 3)) z = Work.Kernels.fk (0:ℤ) z from rfl, Dfk0,
          show B24 τ z (0:Fin 3) (1:Fin 3) =
            -2 * Work.Kernels.c1728 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) from rfl]
        try ring)
        ((Work.Kernels.InP.const_mul (-2 * Work.Kernels.c1728 * Work.Kernels.jInvariantFun τ) DeltaInP).add
          (Work.Kernels.InP.const_mul (2 * Work.Kernels.c1728) jDInP))
    · exact InP_congr (by
        funext z
        rw [show Work.Kernels.fk (![2,0,-2] (1:Fin 3)) z = Work.Kernels.fk (0:ℤ) z from rfl, Dfk0,
          show B24 τ z (1:Fin 3) (1:Fin 3) =
            Work.Kernels.jInvariantFun τ + 2 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) from rfl]
        try ring)
        ((Work.Kernels.InP.const_mul (3 * Work.Kernels.jInvariantFun τ) DeltaInP).add
          (Work.Kernels.InP.const_mul (-2) jDInP))
    · exact InP_congr (by
        funext z
        rw [show Work.Kernels.fk (![2,0,-2] (1:Fin 3)) z = Work.Kernels.fk (0:ℤ) z from rfl, Dfk0,
          show B24 τ z (2:Fin 3) (1:Fin 3) =
            Work.Kernels.c1728 - 2 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) - Work.Kernels.jInvariantFun τ from rfl]
        try ring)
        ((Work.Kernels.InP.const_mul (Work.Kernels.c1728 - 3 * Work.Kernels.jInvariantFun τ) DeltaInP).add
          (Work.Kernels.InP.const_mul (2 : ℂ) jDInP))
  · have hi0 : i = (0:Fin 3) ∨ i = (1:Fin 3) ∨ i = (2:Fin 3) := by fin_cases i <;> simp
    obtain rfl | rfl | rfl := hi0
    · exact InP_congr (by
        funext z
        rw [show Work.Kernels.fk (![2,0,-2] (2:Fin 3)) z = Work.Kernels.fk (-2:ℤ) z from rfl, Dfkm2,
          show B24 τ z (0:Fin 3) (2:Fin 3) = 0 from rfl]
        try ring)
        Work.Kernels.InP.zero
    · exact InP_congr (by
        funext z
        rw [show Work.Kernels.fk (![2,0,-2] (2:Fin 3)) z = Work.Kernels.fk (-2:ℤ) z from rfl, Dfkm2,
          show B24 τ z (1:Fin 3) (2:Fin 3) = -1 from rfl]
        try ring)
        (Work.Kernels.InP.const_mul (-1) E10InP)
    · exact InP_congr (by
        funext z
        rw [show Work.Kernels.fk (![2,0,-2] (2:Fin 3)) z = Work.Kernels.fk (-2:ℤ) z from rfl, Dfkm2,
          show B24 τ z (2:Fin 3) (2:Fin 3) = 1 from rfl]
        try ring)
        (Work.Kernels.InP.const_mul (1 : ℂ) E10InP)

private lemma UpsilonMinusClear24_InP (τ : ℍ) (i j : Fin 3) :
    Work.Kernels.InP (fun z => Work.Kernels.UpsilonMinusClear 24 τ z i j) := by
  have hmain := B24_product_InP τ i j
  have heq : (fun z => Work.Kernels.UpsilonMinusClear 24 τ z i j)
      = fun z => ((((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹) *
          (Work.Kernels.DeltaFun τ * Work.Kernels.fk (![12,10,8] i) τ)) *
          (B24 τ z i j * (Work.Kernels.DeltaFun z * Work.Kernels.fk (![2,0,-2] j) z)) := by
    funext z
    rw [umc24_apply]
    ring
  rw [heq]
  exact Work.Kernels.InP.const_mul _ hmain

/-! ## The basis vector `ψ̃` and the main assembly -/

private lemma psitVec_InP (ℓ : Work.Kernels.LogLambdaData) (j : Fin 3) :
    Work.Kernels.InP (fun z => Work.Kernels.psitVec ℓ z j) := by
  fin_cases j
  · simpa [Work.Kernels.psitVec] using (show Work.Kernels.InP ℓ.L from ⟨ℓ.holo, ℓ.memP⟩)
  · simpa [Work.Kernels.psitVec] using WFunInP
  · simpa [Work.Kernels.psitVec] using UWVInP

private lemma main_case (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ)
    (hU : ∀ i j : Fin 3, Work.Kernels.InP (fun z => Work.Kernels.UpsilonMinusClear d τ z i j)) :
    Work.Kernels.InP (fun z => Work.Kernels.KMinusClear ℓ d τ z) := by
  have hPsi : ∀ j : Fin 3, Work.Kernels.InP (fun z => Work.Kernels.psitVec ℓ z j) := psitVec_InP ℓ
  have hsum : Work.Kernels.InP (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
      Work.Kernels.psiVec ℓ τ i * Work.Kernels.UpsilonMinusClear d τ z i j *
        Work.Kernels.psitVec ℓ z j) := by
    apply InP_sum_fun
    intro i _
    apply InP_sum_fun
    intro j _
    exact (Work.Kernels.InP.const_mul (Work.Kernels.psiVec ℓ τ i) (hU i j)).mul (hPsi j)
  have heq : (fun z => Work.Kernels.KMinusClear ℓ d τ z) = fun z => ∑ i : Fin 3, ∑ j : Fin 3,
      Work.Kernels.psiVec ℓ τ i * Work.Kernels.UpsilonMinusClear d τ z i j *
        Work.Kernels.psitVec ℓ z j := by
    funext z; rfl
  rwa [heq]

theorem KMinusClear_growth_z (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) :
    Work.Kernels.InP (fun z : UpperHalfPlane => Work.Kernels.KMinusClear ℓ d τ z) := by
  rcases hd with rfl | rfl
  · exact main_case ℓ 8 τ (fun i j => UpsilonMinusClear8_InP τ i j)
  · exact main_case ℓ 24 τ (fun i j => UpsilonMinusClear24_InP τ i j)

end Work.Kernels.KernelGrowth

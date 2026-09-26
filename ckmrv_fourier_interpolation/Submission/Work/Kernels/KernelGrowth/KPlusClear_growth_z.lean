import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.E4Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.E6Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.E2Fun_mem_InP
import Submission.Work.Kernels.Slash

set_option linter.unusedSimpArgs false

/-
# Moderate growth of the cleared kernel `K_+^{(d)}` in the second variable

Theorem 4.9(4) of CKMRV states that `Δ(τ)Δ(z)^{e}(j(τ)-j(z))K_+^{(d)}(τ,z)` lies in `𝒫`.
The cleared kernel `Work.Kernels.KPlusClear d τ z` is this product written without any
division by `j(τ)-j(z)`.  Here we show that, for fixed `τ` and `d ∈ {8, 24}`, the function
`z ↦ KPlusClear d τ z` lies in the class `𝒫 = Work.Kernels.InP` (holomorphic and of
moderate growth on `ℍ`).

The point of the *cleared* form is exactly this: `Δ(z)j(z) = E₄(z)³` for all `z`, so the
terms in which the factor `j(τ)-j(z)` is multiplied by `Δ(z)` (or by `Δ(z)E₄(z)`) are
moderate; the holomorphic factor `Δ(z)(j(τ)-j(z))` is handled through the auxiliary
function `JJ`.
-/
namespace Work.Kernels.KernelGrowth

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

noncomputable section

private lemma InP_coe : Work.Kernels.InP (fun z : ℍ => (z : ℂ)) :=
  ⟨UpperHalfPlane.mdifferentiable_coe,
   ⟨1, 0, 1, zero_le_one, le_rfl, zero_le_one, fun z _ => by
      rw [Real.rpow_zero, one_mul, Real.rpow_one]
      linarith [norm_nonneg (z : ℂ)]⟩⟩

private lemma E8Fun_mem_InP : Work.Kernels.InP Work.Kernels.E8Fun := by
  simpa [Work.Kernels.E8Fun] using (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 2)

private lemma E10Fun_mem_InP : Work.Kernels.InP Work.Kernels.E10Fun := by
  simpa [Work.Kernels.E10Fun] using
    (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.mul Work.Kernels.ClassicalFacts.E6Fun_mem_InP)

private lemma E14Fun_mem_InP : Work.Kernels.InP Work.Kernels.E14Fun := by
  simpa [Work.Kernels.E14Fun] using
    ((Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 2).mul
      Work.Kernels.ClassicalFacts.E6Fun_mem_InP)

private lemma E2S_mem_InP : Work.Kernels.InP Work.Kernels.E2S := by
  have h := Work.Kernels.InP.slash (Work.Kernels.ClassicalFacts.E2Fun_mem_InP) (2:ℤ) ModularGroup.S
  have hE : Work.Kernels.E2S = (Work.Kernels.E2Fun ∣[(2:ℤ)] ModularGroup.S) := by
    funext z; rfl
  rw [hE]; exact h

private lemma DeltaFun_mul_div_DeltaFun (F : ℍ → ℂ) (z : ℍ) :
    Work.Kernels.DeltaFun z * (F z / Work.Kernels.DeltaFun z) = F z := by
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z)]

/-- `JJ τ z = (j(τ) - j(z)) Δ(z)`, the holomorphic replacement of the factor
`(j(τ)-j(z))·Δ(z)` appearing in the cleared kernels. -/
private def JJ (τ : ℍ) : ℍ → ℂ :=
  fun z => (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) * Work.Kernels.DeltaFun z

private lemma JJ_mem_InP (τ : ℍ) : Work.Kernels.InP (JJ τ) := by
  have hfun : JJ τ = fun z => Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun z
      - Work.Kernels.E4Fun z ^ 3 := by
    funext z
    simp only [JJ]
    rw [sub_mul, mul_comm (Work.Kernels.jInvariantFun z) (Work.Kernels.DeltaFun z),
      Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun z]
  rw [hfun]
  exact (Work.Kernels.InP.const_mul (Work.Kernels.jInvariantFun τ)
      Work.Kernels.ClassicalFacts.DeltaFun_mem_InP).sub
    (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.pow 3)

private lemma phitVec_mem_InP (j : Fin 3) :
    Work.Kernels.InP (fun z => Work.Kernels.phitVec z j) := by
  fin_cases j
  · change Work.Kernels.InP (fun z => Work.Kernels.phitVec z 0)
    have h : (fun z => Work.Kernels.phitVec z 0) = fun z : ℍ => (z : ℂ) ^ 2 := by
      funext z; simp [Work.Kernels.phitVec]
    rw [h]; exact InP_coe.pow 2
  · change Work.Kernels.InP (fun z => Work.Kernels.phitVec z 1)
    have h : (fun z => Work.Kernels.phitVec z 1) =
        fun z : ℍ => (z : ℂ) ^ 2 * Work.Kernels.E2S z := by
      funext z; simp [Work.Kernels.phitVec]
    rw [h]; exact (InP_coe.pow 2).mul E2S_mem_InP
  · change Work.Kernels.InP (fun z => Work.Kernels.phitVec z 2)
    have h : (fun z => Work.Kernels.phitVec z 2) =
        fun z : ℍ => (z : ℂ) ^ 2 * Work.Kernels.E2S z ^ 2 := by
      funext z; simp [Work.Kernels.phitVec]
    rw [h]; exact (InP_coe.pow 2).mul (E2S_mem_InP.pow 2)

private def c8 : ℂ := ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹

private def c24 : ℂ :=
  ((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹

/-- Macro for the simplification that unfolds `UpsilonPlusClear` into explicit scalar
expressions. -/
private lemma entry8 (τ : ℍ) (i j : Fin 3) :
    Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 8 τ z i j) := by
  fin_cases i <;> fin_cases j
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 0 0)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 0 0) =
        fun z => (c8 * (Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ)) * JJ τ z := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul, JJ, c8]
      ring
    rw [h]; exact Work.Kernels.InP.const_mul _ (JJ_mem_InP τ)
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 0 1)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 0 1) = fun _ : ℍ => (0:ℂ) := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul]
      ring
    rw [h]; exact Work.Kernels.InP.zero
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 0 2)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 0 2) =
        fun z => (c8 * (Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ)) * Work.Kernels.E8Fun z := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul, c8]
      ring
    rw [h]; exact Work.Kernels.InP.const_mul _ E8Fun_mem_InP
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 1 0)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 1 0) =
        fun z => (c8 * (Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ) * (-2)) * JJ τ z := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul, JJ, c8]
      ring
    rw [h]; exact Work.Kernels.InP.const_mul _ (JJ_mem_InP τ)
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 1 1)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 1 1) =
        fun z => (c8 * (Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ) * (-2))
          * Work.Kernels.E10Fun z := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul, c8]
      ring
    rw [h]; exact Work.Kernels.InP.const_mul _ E10Fun_mem_InP
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 1 2)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 1 2) = fun _ : ℍ => (0:ℂ) := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul]
      ring
    rw [h]; exact Work.Kernels.InP.zero
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 2 0)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 2 0) =
        fun z => (c8 * (Work.Kernels.DeltaFun τ * (Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ)))
          * Work.Kernels.DeltaFun z := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul, c8]
      ring
    rw [h]; exact Work.Kernels.InP.const_mul _ Work.Kernels.ClassicalFacts.DeltaFun_mem_InP
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 2 1)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 2 1) = fun _ : ℍ => (0:ℂ) := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul]
      ring
    rw [h]; exact Work.Kernels.InP.zero
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 2 2)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 8 τ z 2 2) = fun _ : ℍ => (0:ℂ) := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul]
      ring
    rw [h]; exact Work.Kernels.InP.zero

private lemma entry24 (τ : ℍ) (i j : Fin 3) :
    Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 24 τ z i j) := by
  fin_cases i <;> fin_cases j
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 0 0)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 0 0) =
        fun z => (c24 * (Work.Kernels.DeltaFun τ * Work.Kernels.E14Fun τ) * 6)
          * (JJ τ z * Work.Kernels.E4Fun z) := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul, JJ, c24]
      ring
    rw [h]
    exact Work.Kernels.InP.const_mul _ ((JJ_mem_InP τ).mul
      Work.Kernels.ClassicalFacts.E4Fun_mem_InP)
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 0 1)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 0 1) = fun _ : ℍ => (0:ℂ) := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul]
      ring
    rw [h]; exact Work.Kernels.InP.zero
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 0 2)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 0 2) =
        fun z => (c24 * (Work.Kernels.DeltaFun τ * Work.Kernels.E14Fun τ))
          * (Work.Kernels.c1728 * Work.Kernels.DeltaFun z - 6 * JJ τ z) := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul, JJ, c24]
      ring
    rw [h]
    exact Work.Kernels.InP.const_mul _
      ((Work.Kernels.InP.const_mul Work.Kernels.c1728
          Work.Kernels.ClassicalFacts.DeltaFun_mem_InP).sub
        (Work.Kernels.InP.const_mul 6 (JJ_mem_InP τ)))
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 1 0)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 1 0) =
        fun z => (c24 * (Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun τ)
            * ((-12) * Work.Kernels.jInvariantFun τ + 5 * Work.Kernels.c1728))
          * (JJ τ z * Work.Kernels.E4Fun z) := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul, JJ, c24]
      ring
    rw [h]
    exact Work.Kernels.InP.const_mul _ ((JJ_mem_InP τ).mul
      Work.Kernels.ClassicalFacts.E4Fun_mem_InP)
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 1 1)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 1 1) =
        fun z => (c24 * (Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun τ)
            * (-2 * Work.Kernels.c1728)) * Work.Kernels.E14Fun z := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul, c24]
      rw [DeltaFun_mul_div_DeltaFun Work.Kernels.E14Fun z]
      ring
    rw [h]; exact Work.Kernels.InP.const_mul _ E14Fun_mem_InP
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 1 2)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 1 2) =
        fun z => (c24 * (Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun τ)
            * (12 * Work.Kernels.jInvariantFun τ - 7 * Work.Kernels.c1728)) * JJ τ z := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul, JJ, c24]
      ring
    rw [h]; exact Work.Kernels.InP.const_mul _ (JJ_mem_InP τ)
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 2 0)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 2 0) =
        fun z => (c24 * (Work.Kernels.DeltaFun τ * Work.Kernels.E10Fun τ))
          * ((Work.Kernels.c1728 * Work.Kernels.DeltaFun z + 6 * JJ τ z)
            * Work.Kernels.E4Fun z) := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul, JJ, c24]
      ring
    rw [h]
    exact Work.Kernels.InP.const_mul _
      (((Work.Kernels.InP.const_mul Work.Kernels.c1728
            Work.Kernels.ClassicalFacts.DeltaFun_mem_InP).add
          (Work.Kernels.InP.const_mul 6 (JJ_mem_InP τ))).mul
        Work.Kernels.ClassicalFacts.E4Fun_mem_InP)
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 2 1)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 2 1) = fun _ : ℍ => (0:ℂ) := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul]
      ring
    rw [h]; exact Work.Kernels.InP.zero
  · change Work.Kernels.InP (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 2 2)
    have h : (fun z => Work.Kernels.UpsilonPlusClear 24 τ z 2 2) =
        fun z => (c24 * (Work.Kernels.DeltaFun τ * Work.Kernels.E10Fun τ) * (-6))
          * JJ τ z := by
      funext z
      simp (config := { decide := true }) only [Work.Kernels.UpsilonPlusClear,
        Work.Kernels.PiMatDelta, Work.Kernels.PiMat, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.diagonal_apply, Work.Kernels.fk, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false, smul_eq_mul, JJ, c24]
      ring
    rw [h]; exact Work.Kernels.InP.const_mul _ (JJ_mem_InP τ)

/-- **Theorem 4.9(4), `d = 8`, `τ`-fixed**: for fixed `τ` the cleared kernel
`z ↦ Δ(τ)Δ(z)(j(τ)-j(z))K_+^{(8)}(τ,z)` lies in `𝒫`. -/
private theorem KPlusClear_growth_z_8 (τ : UpperHalfPlane) :
    Work.Kernels.InP (fun z : UpperHalfPlane => Work.Kernels.KPlusClear 8 τ z) := by
  have hfun : (fun z : UpperHalfPlane => Work.Kernels.KPlusClear 8 τ z) =
      ∑ i : Fin 3, ∑ j : Fin 3, (fun z : UpperHalfPlane =>
        Work.Kernels.phiVec τ i * Work.Kernels.UpsilonPlusClear 8 τ z i j
          * Work.Kernels.phitVec z j) := by
    funext z
    simp only [Work.Kernels.KPlusClear, Finset.sum_apply]
  rw [hfun]
  refine Work.Kernels.InP.sum Finset.univ (fun i _ =>
    Work.Kernels.InP.sum Finset.univ (fun j _ => ?_))
  exact Work.Kernels.InP.mul
    (Work.Kernels.InP.const_mul (Work.Kernels.phiVec τ i) (entry8 τ i j))
    (phitVec_mem_InP j)

/-- **Theorem 4.9(4), `d = 24`, `τ`-fixed**: for fixed `τ` the cleared kernel
`z ↦ Δ(τ)Δ(z)²(j(τ)-j(z))K_+^{(24)}(τ,z)` lies in `𝒫`. -/
private theorem KPlusClear_growth_z_24 (τ : UpperHalfPlane) :
    Work.Kernels.InP (fun z : UpperHalfPlane => Work.Kernels.KPlusClear 24 τ z) := by
  have hfun : (fun z : UpperHalfPlane => Work.Kernels.KPlusClear 24 τ z) =
      ∑ i : Fin 3, ∑ j : Fin 3, (fun z : UpperHalfPlane =>
        Work.Kernels.phiVec τ i * Work.Kernels.UpsilonPlusClear 24 τ z i j
          * Work.Kernels.phitVec z j) := by
    funext z
    simp only [Work.Kernels.KPlusClear, Finset.sum_apply]
  rw [hfun]
  refine Work.Kernels.InP.sum Finset.univ (fun i _ =>
    Work.Kernels.InP.sum Finset.univ (fun j _ => ?_))
  exact Work.Kernels.InP.mul
    (Work.Kernels.InP.const_mul (Work.Kernels.phiVec τ i) (entry24 τ i j))
    (phitVec_mem_InP j)

theorem KPlusClear_growth_z (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) :
    Work.Kernels.InP (fun z : UpperHalfPlane => Work.Kernels.KPlusClear d τ z) := by
  rcases hd with rfl | rfl
  · exact KPlusClear_growth_z_8 τ
  · exact KPlusClear_growth_z_24 τ

end
end Work.Kernels.KernelGrowth

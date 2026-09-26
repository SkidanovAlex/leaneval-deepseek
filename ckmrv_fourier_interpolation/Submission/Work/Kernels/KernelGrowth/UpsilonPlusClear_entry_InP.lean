/-
# Membership in `𝒫` of the entries of the cleared matrix `Υ_+^{clear}` in the variable `τ`

Theorem 4.9(4) of CKMRV states that `Δ(τ)Δ(z)^{e}(j(τ)-j(z))K_+^{(d)}(τ,z)` lies in `𝒫`.
The cleared matrix `Work.Kernels.UpsilonPlusClear d τ z` is the coefficient matrix of this
product written without any division by `j(τ)-j(z)`; the replacement identity
`Δ(τ)(j(τ)-j(z))` is realized through `Δ(τ)j(τ) = E₄(τ)³`
(`Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun`).

Here we show that, for fixed `z` and `d ∈ {8, 24}`, every entry
`τ ↦ Υ_+^{clear}(d,τ,z)_{ij}` lies in the class `𝒫 = Work.Kernels.InP`.

The individual entries are explicit monomials in `E₄, E₆, Δ` and `j`; each occurrence of
`j(τ)` in the matrix `M` of Section 4.4 is accompanied by enough powers of `Δ(τ)` to clear
the denominator of `j = E₄³/Δ`.  Concretely the entries reduce (see `entry8`, `entry24`) to
constant multiples of the functions

  `Δ E₆ (j - j_z)`, `Δ E₆`, `Δ E₄ (j - j_z)`, `Δ E₄`, `E₁₄`, `Δ E₁₄ (j - j_z)`, `Δ E₁₄`,
  `Δ² j (j - j_z)`, `Δ² (j - j_z)`, `Δ²`, `Δ E₁₀ (j - j_z)`, `Δ E₁₀`,

all of which lie in `𝒫` thanks to `Δ j = E₄³`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ClassicalFacts.E4Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.E6Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels.KernelGrowth

open Work.Kernels
open Work.Kernels.ClassicalFacts

/-! ## Basic membership in `𝒫` -/

private lemma E4InP : InP E4Fun := E4Fun_mem_InP

private lemma E6InP : InP E6Fun := E6Fun_mem_InP

private lemma DeltaInP : InP DeltaFun := DeltaFun_mem_InP

private lemma E10InP : InP E10Fun := by
  have h : E10Fun = fun τ => E4Fun τ * E6Fun τ := rfl
  rw [h]; exact E4InP.mul E6InP

private lemma E14InP : InP E14Fun := by
  have h : E14Fun = fun τ => E4Fun τ ^ 2 * E6Fun τ := rfl
  rw [h]; exact (E4InP.pow 2).mul E6InP

/-- `Δ z * (F z / Δ z) = F z`, used to clear the division in `fk 2`. -/
private lemma DeltaFun_mul_div_DeltaFun (F : ℍ → ℂ) (z : ℍ) :
    DeltaFun z * (F z / DeltaFun z) = F z := by
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ (DeltaFun_ne_zero z)]

/-! ## The individual factors appearing in the entries

Each is a monomial in `E₄, E₆, Δ` with the `j`'s cleared by `Δ j = E₄³`; `z` is fixed. -/

private lemma F1_mem (z : ℍ) :
    InP (fun τ => DeltaFun τ * E6Fun τ * (jInvariantFun τ - jInvariantFun z)) := by
  have h : (fun τ => DeltaFun τ * E6Fun τ * (jInvariantFun τ - jInvariantFun z))
      = fun τ => E6Fun τ * E4Fun τ ^ 3 - jInvariantFun z * (DeltaFun τ * E6Fun τ) := by
    funext τ
    rw [← DeltaFun_mul_jInvariantFun τ]
    ring
  rw [h]
  exact (E6InP.mul (E4InP.pow 3)).sub (InP.const_mul _ (DeltaInP.mul E6InP))

private lemma F3_mem (z : ℍ) :
    InP (fun τ => DeltaFun τ * E4Fun τ * (jInvariantFun τ - jInvariantFun z)) := by
  have h : (fun τ => DeltaFun τ * E4Fun τ * (jInvariantFun τ - jInvariantFun z))
      = fun τ => E4Fun τ * E4Fun τ ^ 3 - jInvariantFun z * (DeltaFun τ * E4Fun τ) := by
    funext τ
    rw [← DeltaFun_mul_jInvariantFun τ]
    ring
  rw [h]
  exact (E4InP.mul (E4InP.pow 3)).sub (InP.const_mul _ (DeltaInP.mul E4InP))

private lemma G1_mem (z : ℍ) :
    InP (fun τ => DeltaFun τ * E14Fun τ * (jInvariantFun τ - jInvariantFun z)) := by
  have h : (fun τ => DeltaFun τ * E14Fun τ * (jInvariantFun τ - jInvariantFun z))
      = fun τ => E14Fun τ * E4Fun τ ^ 3 - jInvariantFun z * (DeltaFun τ * E14Fun τ) := by
    funext τ
    rw [← DeltaFun_mul_jInvariantFun τ]
    ring
  rw [h]
  exact (E14InP.mul (E4InP.pow 3)).sub (InP.const_mul _ (DeltaInP.mul E14InP))

private lemma G2_mem (z : ℍ) :
    InP (fun τ => DeltaFun τ * E14Fun τ *
      (c1728 - 6 * (jInvariantFun τ - jInvariantFun z))) := by
  have h : (fun τ => DeltaFun τ * E14Fun τ *
        (c1728 - 6 * (jInvariantFun τ - jInvariantFun z)))
      = fun τ => c1728 * (DeltaFun τ * E14Fun τ)
          - 6 * (DeltaFun τ * E14Fun τ * (jInvariantFun τ - jInvariantFun z)) := by
    funext τ; ring
  rw [h]
  exact (InP.const_mul c1728 (DeltaInP.mul E14InP)).sub (InP.const_mul 6 (G1_mem z))

private lemma H1_mem (z : ℍ) :
    InP (fun τ => DeltaFun τ ^ 2 * (jInvariantFun τ * (jInvariantFun τ - jInvariantFun z))) := by
  have h : (fun τ => DeltaFun τ ^ 2 *
        (jInvariantFun τ * (jInvariantFun τ - jInvariantFun z)))
      = fun τ => E4Fun τ ^ 3 * E4Fun τ ^ 3
          - jInvariantFun z * (DeltaFun τ * E4Fun τ ^ 3) := by
    funext τ
    rw [← DeltaFun_mul_jInvariantFun τ]
    ring
  rw [h]
  exact ((E4InP.pow 3).mul (E4InP.pow 3)).sub
    (InP.const_mul _ (DeltaInP.mul (E4InP.pow 3)))

private lemma H2_mem (z : ℍ) :
    InP (fun τ => DeltaFun τ ^ 2 * (jInvariantFun τ - jInvariantFun z)) := by
  have h : (fun τ => DeltaFun τ ^ 2 * (jInvariantFun τ - jInvariantFun z))
      = fun τ => DeltaFun τ * E4Fun τ ^ 3 - jInvariantFun z * DeltaFun τ ^ 2 := by
    funext τ
    rw [← DeltaFun_mul_jInvariantFun τ]
    ring
  rw [h]
  exact (DeltaInP.mul (E4InP.pow 3)).sub (InP.const_mul _ (DeltaInP.pow 2))

private lemma G3_mem (z : ℍ) :
    InP (fun τ => DeltaFun τ ^ 2 *
      ((-12) * jInvariantFun τ * (jInvariantFun τ - jInvariantFun z)
        + 5 * c1728 * (jInvariantFun τ - jInvariantFun z))) := by
  have h : (fun τ => DeltaFun τ ^ 2 *
        ((-12) * jInvariantFun τ * (jInvariantFun τ - jInvariantFun z)
          + 5 * c1728 * (jInvariantFun τ - jInvariantFun z)))
      = fun τ => (-12) * (DeltaFun τ ^ 2 *
            (jInvariantFun τ * (jInvariantFun τ - jInvariantFun z)))
          + (5 * c1728) * (DeltaFun τ ^ 2 * (jInvariantFun τ - jInvariantFun z)) := by
    funext τ; ring
  rw [h]
  exact (InP.const_mul (-12) (H1_mem z)).add (InP.const_mul (5 * c1728) (H2_mem z))

private lemma G5_mem (z : ℍ) :
    InP (fun τ => DeltaFun τ ^ 2 *
      (12 * jInvariantFun τ * (jInvariantFun τ - jInvariantFun z)
        - 7 * c1728 * (jInvariantFun τ - jInvariantFun z))) := by
  have h : (fun τ => DeltaFun τ ^ 2 *
        (12 * jInvariantFun τ * (jInvariantFun τ - jInvariantFun z)
          - 7 * c1728 * (jInvariantFun τ - jInvariantFun z)))
      = fun τ => 12 * (DeltaFun τ ^ 2 *
            (jInvariantFun τ * (jInvariantFun τ - jInvariantFun z)))
          - (7 * c1728) * (DeltaFun τ ^ 2 * (jInvariantFun τ - jInvariantFun z)) := by
    funext τ; ring
  rw [h]
  exact (InP.const_mul 12 (H1_mem z)).sub (InP.const_mul (7 * c1728) (H2_mem z))

private lemma K1_mem (z : ℍ) :
    InP (fun τ => DeltaFun τ * E10Fun τ * (jInvariantFun τ - jInvariantFun z)) := by
  have h : (fun τ => DeltaFun τ * E10Fun τ * (jInvariantFun τ - jInvariantFun z))
      = fun τ => E10Fun τ * E4Fun τ ^ 3 - jInvariantFun z * (DeltaFun τ * E10Fun τ) := by
    funext τ
    rw [← DeltaFun_mul_jInvariantFun τ]
    ring
  rw [h]
  exact (E10InP.mul (E4InP.pow 3)).sub (InP.const_mul _ (DeltaInP.mul E10InP))

private lemma G6_mem (z : ℍ) :
    InP (fun τ => DeltaFun τ * E10Fun τ *
      (c1728 + 6 * (jInvariantFun τ - jInvariantFun z))) := by
  have h : (fun τ => DeltaFun τ * E10Fun τ *
        (c1728 + 6 * (jInvariantFun τ - jInvariantFun z)))
      = fun τ => c1728 * (DeltaFun τ * E10Fun τ)
          + 6 * (DeltaFun τ * E10Fun τ * (jInvariantFun τ - jInvariantFun z)) := by
    funext τ; ring
  rw [h]
  exact (InP.const_mul c1728 (DeltaInP.mul E10InP)).add (InP.const_mul 6 (K1_mem z))

private lemma G7_mem (z : ℍ) :
    InP (fun τ => DeltaFun τ * E10Fun τ * (-6 * (jInvariantFun τ - jInvariantFun z))) := by
  have h : (fun τ => DeltaFun τ * E10Fun τ * (-6 * (jInvariantFun τ - jInvariantFun z)))
      = fun τ => (-6) * (DeltaFun τ * E10Fun τ * (jInvariantFun τ - jInvariantFun z)) := by
    funext τ; ring
  rw [h]
  exact InP.const_mul (-6) (K1_mem z)

/-! ## The entries of `Υ_+^{clear}(8,·,z)` and `Υ_+^{clear}(24,·,z)` -/

private def c8 : ℂ := ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹

private def c24 : ℂ :=
  ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹

private lemma entry8 (z : ℍ) (i j : Fin 3) :
    InP (fun τ : ℍ => UpsilonPlusClear 8 τ z i j) := by
  fin_cases i <;> fin_cases j
  · change InP (fun τ : ℍ => UpsilonPlusClear 8 τ z 0 0)
    have h : (fun τ : ℍ => UpsilonPlusClear 8 τ z 0 0) =
        fun τ => (c8 * DeltaFun z) *
          (DeltaFun τ * E6Fun τ * (jInvariantFun τ - jInvariantFun z)) := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c8]
      ring
    rw [h]; exact InP.const_mul _ (F1_mem z)
  · change InP (fun τ : ℍ => UpsilonPlusClear 8 τ z 0 1)
    have h : (fun τ : ℍ => UpsilonPlusClear 8 τ z 0 1) = fun _ : ℍ => (0:ℂ) := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c8]
      ring
    rw [h]; exact InP.zero
  · change InP (fun τ : ℍ => UpsilonPlusClear 8 τ z 0 2)
    have h : (fun τ : ℍ => UpsilonPlusClear 8 τ z 0 2) =
        fun τ => (c8 * E8Fun z) * (DeltaFun τ * E6Fun τ) := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c8]
      ring
    rw [h]; exact InP.const_mul _ (DeltaInP.mul E6InP)
  · change InP (fun τ : ℍ => UpsilonPlusClear 8 τ z 1 0)
    have h : (fun τ : ℍ => UpsilonPlusClear 8 τ z 1 0) =
        fun τ => (c8 * DeltaFun z * (-2)) *
          (DeltaFun τ * E4Fun τ * (jInvariantFun τ - jInvariantFun z)) := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c8]
      ring
    rw [h]; exact InP.const_mul _ (F3_mem z)
  · change InP (fun τ : ℍ => UpsilonPlusClear 8 τ z 1 1)
    have h : (fun τ : ℍ => UpsilonPlusClear 8 τ z 1 1) =
        fun τ => (c8 * E10Fun z * (-2)) * (DeltaFun τ * E4Fun τ) := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c8]
      ring
    rw [h]; exact InP.const_mul _ (DeltaInP.mul E4InP)
  · change InP (fun τ : ℍ => UpsilonPlusClear 8 τ z 1 2)
    have h : (fun τ : ℍ => UpsilonPlusClear 8 τ z 1 2) = fun _ : ℍ => (0:ℂ) := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c8]
      ring
    rw [h]; exact InP.zero
  · change InP (fun τ : ℍ => UpsilonPlusClear 8 τ z 2 0)
    have h : (fun τ : ℍ => UpsilonPlusClear 8 τ z 2 0) =
        fun τ => (c8 * DeltaFun z) * (DeltaFun τ * (E14Fun τ / DeltaFun τ)) := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c8]
      ring
    rw [h]
    have h2 : (fun τ : ℍ => (c8 * DeltaFun z) * (DeltaFun τ * (E14Fun τ / DeltaFun τ)))
        = fun τ => (c8 * DeltaFun z) * E14Fun τ := by
      funext τ; rw [DeltaFun_mul_div_DeltaFun E14Fun τ]
    rw [h2]; exact InP.const_mul _ E14InP
  · change InP (fun τ : ℍ => UpsilonPlusClear 8 τ z 2 1)
    have h : (fun τ : ℍ => UpsilonPlusClear 8 τ z 2 1) = fun _ : ℍ => (0:ℂ) := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c8]
      ring
    rw [h]; exact InP.zero
  · change InP (fun τ : ℍ => UpsilonPlusClear 8 τ z 2 2)
    have h : (fun τ : ℍ => UpsilonPlusClear 8 τ z 2 2) = fun _ : ℍ => (0:ℂ) := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c8]
      ring
    rw [h]; exact InP.zero

private lemma entry24 (z : ℍ) (i j : Fin 3) :
    InP (fun τ : ℍ => UpsilonPlusClear 24 τ z i j) := by
  fin_cases i <;> fin_cases j
  · change InP (fun τ : ℍ => UpsilonPlusClear 24 τ z 0 0)
    have h : (fun τ : ℍ => UpsilonPlusClear 24 τ z 0 0) =
        fun τ => (c24 * (DeltaFun z * E4Fun z) * 6) *
          (DeltaFun τ * E14Fun τ * (jInvariantFun τ - jInvariantFun z)) := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c24]
      ring
    rw [h]; exact InP.const_mul _ (G1_mem z)
  · change InP (fun τ : ℍ => UpsilonPlusClear 24 τ z 0 1)
    have h : (fun τ : ℍ => UpsilonPlusClear 24 τ z 0 1) = fun _ : ℍ => (0:ℂ) := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c24]
      ring
    rw [h]; exact InP.zero
  · change InP (fun τ : ℍ => UpsilonPlusClear 24 τ z 0 2)
    have h : (fun τ : ℍ => UpsilonPlusClear 24 τ z 0 2) =
        fun τ => (c24 * DeltaFun z) *
          (DeltaFun τ * E14Fun τ *
            (c1728 - 6 * (jInvariantFun τ - jInvariantFun z))) := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c24]
      ring
    rw [h]; exact InP.const_mul _ (G2_mem z)
  · change InP (fun τ : ℍ => UpsilonPlusClear 24 τ z 1 0)
    have h : (fun τ : ℍ => UpsilonPlusClear 24 τ z 1 0) =
        fun τ => (c24 * (DeltaFun z * E4Fun z)) *
          (DeltaFun τ ^ 2 *
            ((-12) * jInvariantFun τ * (jInvariantFun τ - jInvariantFun z)
              + 5 * c1728 * (jInvariantFun τ - jInvariantFun z))) := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c24]
      ring
    rw [h]; exact InP.const_mul _ (G3_mem z)
  · change InP (fun τ : ℍ => UpsilonPlusClear 24 τ z 1 1)
    have h : (fun τ : ℍ => UpsilonPlusClear 24 τ z 1 1) =
        fun τ => (c24 * (DeltaFun z * (E14Fun z / DeltaFun z)) * (-2 * c1728)) *
          DeltaFun τ ^ 2 := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c24]
      ring
    rw [h]; exact InP.const_mul _ (DeltaInP.pow 2)
  · change InP (fun τ : ℍ => UpsilonPlusClear 24 τ z 1 2)
    have h : (fun τ : ℍ => UpsilonPlusClear 24 τ z 1 2) =
        fun τ => (c24 * DeltaFun z) *
          (DeltaFun τ ^ 2 *
            (12 * jInvariantFun τ * (jInvariantFun τ - jInvariantFun z)
              - 7 * c1728 * (jInvariantFun τ - jInvariantFun z))) := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c24]
      ring
    rw [h]; exact InP.const_mul _ (G5_mem z)
  · change InP (fun τ : ℍ => UpsilonPlusClear 24 τ z 2 0)
    have h : (fun τ : ℍ => UpsilonPlusClear 24 τ z 2 0) =
        fun τ => (c24 * (DeltaFun z * E4Fun z)) *
          (DeltaFun τ * E10Fun τ *
            (c1728 + 6 * (jInvariantFun τ - jInvariantFun z))) := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c24]
      ring
    rw [h]; exact InP.const_mul _ (G6_mem z)
  · change InP (fun τ : ℍ => UpsilonPlusClear 24 τ z 2 1)
    have h : (fun τ : ℍ => UpsilonPlusClear 24 τ z 2 1) = fun _ : ℍ => (0:ℂ) := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c24]
      ring
    rw [h]; exact InP.zero
  · change InP (fun τ : ℍ => UpsilonPlusClear 24 τ z 2 2)
    have h : (fun τ : ℍ => UpsilonPlusClear 24 τ z 2 2) =
        fun τ => (c24 * DeltaFun z) *
          (DeltaFun τ * E10Fun τ * (-6 * (jInvariantFun τ - jInvariantFun z))) := by
      funext τ
      simp (config := { decide := true }) only [UpsilonPlusClear, PiMatDelta, PiMat,
        Matrix.smul_apply, Matrix.mul_apply, Matrix.diagonal_apply, fk, Fin.sum_univ_three,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, if_true, ite_false,
        smul_eq_mul, c24]
      ring
    rw [h]; exact InP.const_mul _ (G7_mem z)

theorem UpsilonPlusClear_entry_InP (d : ℕ) (hd : d = 8 ∨ d = 24) (z : UpperHalfPlane)
    (i j : Fin 3) :
    Work.Kernels.InP (fun τ : UpperHalfPlane => Work.Kernels.UpsilonPlusClear d τ z i j) := by
  rcases hd with rfl | rfl
  · exact entry8 z i j
  · exact entry24 z i j

end Work.Kernels.KernelGrowth

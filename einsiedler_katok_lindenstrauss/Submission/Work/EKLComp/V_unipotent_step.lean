import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Diag
import Submission.Work.EKLContract.Lemmas.isHoro_Uij
import Submission.Work.EKLComp.uij_step_matrix
import Submission.Work.EKLComp.shear_estimate

/-!
# The unipotent step of `V`-closeness

`Work.EKLContract.V δ` is the entrywise `δ`-neighbourhood of the identity in `SL₃(ℝ)`.
This file proves that a right translation by an element of `V ε`, followed by a small
unipotent correction `(u₁₀(X) u₂₀(Y))⁻¹` with `|X|, |Y| ≤ e³ ε`, stays inside `V δ` as soon as
`2600 ε ≤ δ` (and `0 < ε ≤ 1`).

The proof is the explicit matrix computation: with `M = 1 + (-X)E₁₀ + (-Y)E₂₀`,

  `toMat ((u₁₀(X) u₂₀(Y))⁻¹ · h) = M · toMat h`   (`uij_step_matrix`),

and the rows of `M · toMat h` are `(toMat h)₀`, `(toMat h)₁ - X (toMat h)₀`,
`(toMat h)₂ - Y (toMat h)₀`.  Every entry of `h ∈ V ε` is within `ε ≤ 1` of the identity, so
`|(toMat h)₀ⱼ| ≤ 2`, and the triangle inequality gives

  `|(M · toMat h)ᵢⱼ - δᵢⱼ| ≤ ε + e³ ε · 2 = (1 + 2 e³) ε < 2600 ε ≤ δ`,   since `1 + 2 e³ < 27 < 2600`.

The last step is the delegated estimate `shear_estimate`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace Work.EKLComp

open Work.EKLContract

/-- `1 + 2 e³ < 2600` (in fact `e³ < 27`, since `e < 3`). -/
private lemma exp3bd : (1 : ℝ) + 2 * Real.exp 3 < 2600 := by
  have h3 : Real.exp (3 : ℝ) < 27 := by
    have heq : Real.exp (3 : ℝ) = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [heq]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1, sq_nonneg (Real.exp 1)]
  linarith

/-- Row `0` of `(1 + (-X)E₁₀ + (-Y)E₂₀) · A` is row `0` of `A`. -/
private lemma row0_loc (X Y : ℝ) (A : SL3) (j : Fin 3) :
    ((1 + Matrix.single (1:Fin 3) (0:Fin 3) (-X) + Matrix.single (2:Fin 3) (0:Fin 3) (-Y)) * toMat A) 0 j
      = toMat A 0 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

/-- Row `1` of `(1 + (-X)E₁₀ + (-Y)E₂₀) · A` is `(row 1 of A) - X · (row 0 of A)`. -/
private lemma row1_loc (X Y : ℝ) (A : SL3) (j : Fin 3) :
    ((1 + Matrix.single (1:Fin 3) (0:Fin 3) (-X) + Matrix.single (2:Fin 3) (0:Fin 3) (-Y)) * toMat A) 1 j
      = toMat A 1 j - X * toMat A 0 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] <;> ring

/-- Row `2` of `(1 + (-X)E₁₀ + (-Y)E₂₀) · A` is `(row 2 of A) - Y · (row 0 of A)`. -/
private lemma row2_loc (X Y : ℝ) (A : SL3) (j : Fin 3) :
    ((1 + Matrix.single (1:Fin 3) (0:Fin 3) (-X) + Matrix.single (2:Fin 3) (0:Fin 3) (-Y)) * toMat A) 2 j
      = toMat A 2 j - Y * toMat A 0 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] <;> ring

theorem V_unipotent_step (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεδ : 2600 * ε ≤ δ)
    (X Y : ℝ) (hX : |X| ≤ Real.exp 3 * ε) (hY : |Y| ≤ Real.exp 3 * ε)
    (h : Work.EKLContract.SL3) (hh : h ∈ Work.EKLContract.V ε) :
    (Work.EKLContract.uij (show (1 : Fin 3) ≠ 0 by decide) X *
      Work.EKLContract.uij (show (2 : Fin 3) ≠ 0 by decide) Y)⁻¹ * h ∈ Work.EKLContract.V δ := by
  have hεδ2 : ε < δ := by
    have h1 : (1 : ℝ) < 1 + 2 * Real.exp 3 := by nlinarith [Real.exp_pos 3]
    have h2 : (1:ℝ) * ε < (1 + 2 * Real.exp 3) * ε := mul_lt_mul_of_pos_right h1 hε
    have h3 : (1 + 2 * Real.exp 3) * ε < 2600 * ε := mul_lt_mul_of_pos_right exp3bd hε
    linarith
  have hhE : ∀ i j, |toMat h i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < ε :=
    fun i j => hh i j
  have hcol : ∀ j : Fin 3, |toMat h 0 j| ≤ 2 := by
    intro j
    have h1 : |toMat h 0 j - (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j| < ε := hhE 0 j
    have h2 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j| ≤ 1 := by
      rw [Matrix.one_apply]; split <;> norm_num
    calc |toMat h 0 j|
        = |(toMat h 0 j - (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j) + (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j| := by ring_nf
      _ ≤ |toMat h 0 j - (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j| := abs_add_le _ _
      _ ≤ ε + 1 := by linarith [le_of_lt h1, h2]
      _ ≤ 2 := by linarith [hε1]
  rw [V]
  intro i j
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl
  · change |toMat ((uij (show (1 : Fin 3) ≠ 0 by decide) X *
        uij (show (2 : Fin 3) ≠ 0 by decide) Y)⁻¹ * h) 0 j - (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 j| < δ
    rw [uij_step_matrix X Y h, row0_loc]
    exact lt_of_lt_of_le (hhE 0 j) (le_of_lt hεδ2)
  · change |toMat ((uij (show (1 : Fin 3) ≠ 0 by decide) X *
        uij (show (2 : Fin 3) ≠ 0 by decide) Y)⁻¹ * h) 1 j - (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 j| < δ
    rw [uij_step_matrix X Y h, row1_loc]
    rw [show toMat h 1 j - X * toMat h 0 j - (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 j
        = (toMat h 1 j - (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 j) - X * toMat h 0 j from by ring]
    exact shear_estimate δ ε hε hεδ hX (hhE 1 j) (hcol j)
  · change |toMat ((uij (show (1 : Fin 3) ≠ 0 by decide) X *
        uij (show (2 : Fin 3) ≠ 0 by decide) Y)⁻¹ * h) 2 j - (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 j| < δ
    rw [uij_step_matrix X Y h, row2_loc]
    rw [show toMat h 2 j - Y * toMat h 0 j - (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 j
        = (toMat h 2 j - (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 j) - Y * toMat h 0 j from by ring]
    exact shear_estimate δ ε hε hεδ hY (hhE 2 j) (hcol j)

end Work.EKLComp

import Mathlib
import Submission.Work.ZassenhausSuzuki.SL2ModelClass
import Submission.Work.Models.PSL2.Defs
import Submission.Work.ZassenhausSuzuki.SingerModelDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.Odd

open Matrix

/-!
# Every element of `SL(2,F)` is inverted by an involution (`F` of characteristic two)

The main result `sl2_conj_involution` shows that for a finite field `F` of characteristic two
every `A ∈ SL(2,F)` admits an involution `b ∈ SL(2,F)` with `b * A * b = A⁻¹`.

The argument is elementary and explicit.  Writing `A = !![p, q; r, s]` (so that, in
characteristic two, `A.adjugate = !![s, q; r, p]`), an involution inverting `A` is given by
* `!![1, 0; (p+s)/q, 1]` when `q ≠ 0`,
* `!![1, (p+s)/r; 0, 1]` when `r ≠ 0`,
* `!![0, 1; 1, 0]` when `q = r = 0`.
Each of these is an involution (its square is the identity because the field has characteristic
two) and conjugates `!![p, q; r, s]` to `!![s, q; r, p]`. -/

/-- The upper unitriangular shear is an involution in characteristic two. -/
private lemma sq_upper {F : Type*} [Field F] [CharP F 2] (x : F) :
    (!![1, 0; x, 1] : Matrix (Fin 2) (Fin 2) F) * !![1, 0; x, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    simp [CharTwo.add_self_eq_zero]

/-- The lower unitriangular shear is an involution in characteristic two. -/
private lemma sq_lower {F : Type*} [Field F] [CharP F 2] (y : F) :
    (!![1, y; 0, 1] : Matrix (Fin 2) (Fin 2) F) * !![1, y; 0, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    simp [CharTwo.add_self_eq_zero]

/-- The coordinate swap is an involution in characteristic two. -/
private lemma sq_swap {F : Type*} [Field F] [CharP F 2] :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; 1, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    simp

/-- The upper shear `!![1, 0; x, 1]` conjugates `!![p, q; r, s]` to `!![s, q; r, p]` provided
`x * q = p + s`. -/
private lemma conj_upper {F : Type*} [Field F] [CharP F 2] (p q r s x : F)
    (hx : x * q = p + s) :
    !![1, 0; x, 1] * !![p, q; r, s] * !![1, 0; x, 1] = !![s, q; r, p] := by
  have hxq : q * x = p + s := by rw [mul_comm, hx]
  have h2 : x ^ 2 * q = x * p + x * s := by rw [pow_two, mul_assoc, hx]; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    simp
  · rw [hxq]; ring_nf; simp [CharTwo.two_eq_zero]
  · ring_nf; rw [h2]; ring_nf; simp [CharTwo.two_eq_zero]
  · rw [hx]; ring_nf; simp [CharTwo.two_eq_zero]

/-- The lower shear `!![1, y; 0, 1]` conjugates `!![p, q; r, s]` to `!![s, q; r, p]` provided
`y * r = p + s`. -/
private lemma conj_lower {F : Type*} [Field F] [CharP F 2] (p q r s y : F)
    (hy : y * r = p + s) :
    !![1, y; 0, 1] * !![p, q; r, s] * !![1, y; 0, 1] = !![s, q; r, p] := by
  have hyr : r * y = p + s := by rw [mul_comm, hy]
  have h2 : y ^ 2 * r = y * p + y * s := by rw [pow_two, mul_assoc, hy]; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    simp
  · rw [hy]; ring_nf; simp [CharTwo.two_eq_zero]
  · ring_nf; rw [h2]; ring_nf; simp [CharTwo.two_eq_zero]
  · rw [hyr]; ring_nf; simp [CharTwo.two_eq_zero]

/-- The coordinate swap conjugates the diagonal matrix `!![p, 0; 0, s]` to `!![s, 0; 0, p]`. -/
private lemma conj_swap {F : Type*} [Field F] [CharP F 2] (p s : F) :
    !![0, 1; 1, 0] * !![p, 0; 0, s] * !![0, 1; 1, 0] = !![s, 0; 0, p] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    simp

theorem sl2_conj_involution {F : Type*} [Field F] [Finite F] [CharP F 2]
    (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ b : Matrix.SpecialLinearGroup (Fin 2) F, b * b = 1 ∧ b * A * b = A⁻¹ := by
  set p : F := (A : Matrix (Fin 2) (Fin 2) F) 0 0 with hp
  set q : F := (A : Matrix (Fin 2) (Fin 2) F) 0 1 with hq'
  set r : F := (A : Matrix (Fin 2) (Fin 2) F) 1 0 with hr'
  set s : F := (A : Matrix (Fin 2) (Fin 2) F) 1 1 with hs
  have hA : (A : Matrix (Fin 2) (Fin 2) F) = !![p, q; r, s] :=
    Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) F)
  by_cases hq : q = 0
  · by_cases hr : r = 0
    · -- `A` is diagonal: the coordinate swap works.
      have hA' : (A : Matrix (Fin 2) (Fin 2) F) = !![p, 0; 0, s] := by rw [hA, hq, hr]
      refine ⟨⟨!![0, 1; 1, 0], ?_⟩, ?_, ?_⟩
      · rw [Matrix.det_fin_two_of]; simp [CharTwo.neg_eq]
      · apply Subtype.ext
        show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; 1, 0] = 1
        exact sq_swap
      · apply Subtype.ext
        show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F)
          * !![0, 1; 1, 0] = Matrix.adjugate (A : Matrix (Fin 2) (Fin 2) F)
        rw [hA', Matrix.adjugate_fin_two_of]
        simp only [CharTwo.neg_eq]
        exact conj_swap p s
    · -- `q = 0`, `r ≠ 0`: a lower shear works.
      have hdetL : (!![1, (p + s) / r; 0, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
        rw [Matrix.det_fin_two_of]; simp
      refine ⟨⟨!![1, (p + s) / r; 0, 1], hdetL⟩, ?_, ?_⟩
      · apply Subtype.ext
        show (!![1, (p + s) / r; 0, 1] : Matrix (Fin 2) (Fin 2) F)
          * !![1, (p + s) / r; 0, 1] = 1
        exact sq_lower ((p + s) / r)
      · apply Subtype.ext
        show (!![1, (p + s) / r; 0, 1] : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F)
          * !![1, (p + s) / r; 0, 1] = Matrix.adjugate (A : Matrix (Fin 2) (Fin 2) F)
        rw [hA, Matrix.adjugate_fin_two_of]
        simp only [CharTwo.neg_eq]
        exact conj_lower p q r s ((p + s) / r) (div_mul_cancel₀ (p + s) hr)
  · -- `q ≠ 0`: an upper shear works.
    have hdetU : (!![1, 0; (p + s) / q, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [Matrix.det_fin_two_of]; simp
    refine ⟨⟨!![1, 0; (p + s) / q, 1], hdetU⟩, ?_, ?_⟩
    · apply Subtype.ext
      show (!![1, 0; (p + s) / q, 1] : Matrix (Fin 2) (Fin 2) F) * !![1, 0; (p + s) / q, 1] = 1
      exact sq_upper ((p + s) / q)
    · apply Subtype.ext
      show (!![1, 0; (p + s) / q, 1] : Matrix (Fin 2) (Fin 2) F)
        * (A : Matrix (Fin 2) (Fin 2) F) * !![1, 0; (p + s) / q, 1]
        = Matrix.adjugate (A : Matrix (Fin 2) (Fin 2) F)
      rw [hA, Matrix.adjugate_fin_two_of]
      simp only [CharTwo.neg_eq]
      exact conj_upper p q r s ((p + s) / q) (div_mul_cancel₀ (p + s) hq)

end Work.ZassenhausSuzuki.Odd

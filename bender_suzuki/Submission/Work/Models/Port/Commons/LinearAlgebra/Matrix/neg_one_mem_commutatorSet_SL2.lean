import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.SimpleRing.Principal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.LinearAlgebra.Matrix

open scoped MatrixGroups commutatorElement

/-- In a finite field, `-1` is a sum of two squares.  (For a general element this is false, e.g. in
`F₄` the squares are the prime field `F₂`; but `-1` lies in the prime field.) -/
lemma exists_sq_add_sq_eq_neg_one_of_finiteField {F : Type*} [Field F] [Finite F] :
    ∃ a b : F, a ^ 2 + b ^ 2 = -1 := by
  have hne : NeZero (ringChar F) := ⟨CharP.ringChar_ne_zero_of_finite F⟩
  obtain ⟨a, b, hab⟩ := @CharP.sq_add_sq F _ _ (ringChar F) hne _ (-1)
  exact ⟨a, b, by simpa using hab⟩

set_option linter.unusedVariables false in
/-- The element `-1` of `SL(2, F)` is a commutator, for `F` a finite field of cardinality `≥ 4`.
(The hypothesis on the cardinality is not needed: the argument works for every finite field.)

Explicitly, if `a ^ 2 + b ^ 2 = -1` then
`A = !![0, -1; 1, 0]` and `B = !![a, b; b, -a]` are elements of `SL(2, F)` with `A * B = -B * A`,
whence `⁅A, B⁆ = A * B * A⁻¹ * B⁻¹ = -1`. -/
theorem neg_one_mem_commutatorSet_SL2 {F : Type*} [Field F] [Fintype F] (hF : 4 ≤ Fintype.card F) :
    (-1 : Matrix.SpecialLinearGroup (Fin 2) F) ∈ commutatorSet (Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq_eq_neg_one_of_finiteField (F := F)
  have hdetB : Matrix.det (!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
    have h1 : a * -a - b * b = -(a ^ 2 + b ^ 2) := by ring
    rw [h1, hab, neg_neg]
  have hdetA : Matrix.det (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  let A : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![0, -1; 1, 0], hdetA⟩
  let B : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![a, b; b, -a], hdetB⟩
  -- `A` and `B` anticommute
  have hAB : (A * B : Matrix.SpecialLinearGroup (Fin 2) F) = -(B * A) := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, B, Matrix.mul_apply, Fin.sum_univ_two]
  refine mem_commutatorSet_iff.mpr ⟨A, B, ?_⟩
  rw [commutatorElement_def]
  calc A * B * A⁻¹ * B⁻¹ = (-(B * A)) * A⁻¹ * B⁻¹ := by rw [hAB]
    _ = -1 := by
      rw [neg_mul, neg_mul, show (B * A) * A⁻¹ * B⁻¹ = 1 by group]

end Commons.LinearAlgebra.Matrix
import Mathlib
import Submission.Work.Models.Port.Commons.LinearAlgebra.Matrix.exists_isSimilar_companion
import Submission.Work.Models.Port.Commons.LinearAlgebra.Matrix.companion_mem_commutatorSet
import Submission.Work.Models.Port.Commons.LinearAlgebra.Matrix.neg_one_mem_commutatorSet_SL2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Matrix
open scoped MatrixGroups commutatorElement

namespace Commons.LinearAlgebra.Matrix

/-- `P * P⁻¹ = 1` inside the matrix ring, for `P : GL(2,F)`. -/
lemma gl_mul_inv_val {F : Type*} [Field F] (P : Matrix.GeneralLinearGroup (Fin 2) F) :
    (P : Matrix (Fin 2) (Fin 2) F)
      * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]

/-- `P⁻¹ * P = 1` inside the matrix ring, for `P : GL(2,F)`. -/
lemma gl_inv_mul_val {F : Type*} [Field F] (P : Matrix.GeneralLinearGroup (Fin 2) F) :
    ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      * (P : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]

/-- The sandwich identity: conjugating `P M P⁻¹` back by `P⁻¹` returns `M`. -/
lemma gl_conj_sandwich {F : Type*} [Field F] (P : Matrix.GeneralLinearGroup (Fin 2) F)
    (M : Matrix (Fin 2) (Fin 2) F) :
    ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      * ((P : Matrix (Fin 2) (Fin 2) F) * M
          * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
      * (P : Matrix (Fin 2) (Fin 2) F) = M := by
  set a : Matrix (Fin 2) (Fin 2) F :=
    ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with ha
  set b : Matrix (Fin 2) (Fin 2) F := (P : Matrix (Fin 2) (Fin 2) F) with hb
  have hab : a * b = 1 := by rw [ha, hb]; exact gl_inv_mul_val P
  show a * (b * M * a) * b = M
  calc a * (b * M * a) * b = a * (b * M) * a * b := by rw [Matrix.mul_assoc a (b * M) a]
    _ = a * (b * M) * (a * b) := by rw [Matrix.mul_assoc]
    _ = a * b * M * (a * b) := by rw [← Matrix.mul_assoc a b M]
    _ = M := by rw [hab, Matrix.one_mul, Matrix.mul_one]

/-- Conjugation by an element `P` of `GL(2,F)`, as a group homomorphism of `SL(2,F)`. -/
def conjSL {F : Type*} [Field F] (P : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun Z := ⟨(P : Matrix (Fin 2) (Fin 2) F) * (Z : Matrix (Fin 2) (Fin 2) F)
      * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
    rw [Matrix.det_mul, Matrix.det_mul, Z.2, mul_one, ← Matrix.det_mul, gl_mul_inv_val,
      Matrix.det_one]⟩
  map_one' := by
    apply Subtype.ext
    show (P : Matrix (Fin 2) (Fin 2) F) * (1 : Matrix (Fin 2) (Fin 2) F)
        * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [Matrix.mul_one, gl_mul_inv_val]
  map_mul' := by
    intro Z W
    apply Subtype.ext
    show (P : Matrix (Fin 2) (Fin 2) F)
          * ((Z * W : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = ((P : Matrix (Fin 2) (Fin 2) F) * (Z : Matrix (Fin 2) (Fin 2) F)
            * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
          * ((P : Matrix (Fin 2) (Fin 2) F) * (W : Matrix (Fin 2) (Fin 2) F)
            * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) (P : Matrix (Fin 2) (Fin 2) F)
          ((W : Matrix (Fin 2) (Fin 2) F)
            * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)),
        gl_inv_mul_val, Matrix.one_mul]

end Commons.LinearAlgebra.Matrix

namespace Commons.GroupTheory.Commutator

open Matrix
open scoped MatrixGroups commutatorElement

/-- **Ore for `SL(2,F)`**: every element of `SL(2,F)` is a commutator, for a finite field `F`
with at least `4` elements. -/
theorem commutatorSet_SL2_eq_univ {F : Type*} [Field F] [Fintype F] (hF : 4 ≤ Fintype.card F) :
    commutatorSet (Matrix.SpecialLinearGroup (Fin 2) F) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro A
  by_cases hnc : ∀ c : F, (A : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)
  · obtain ⟨P, hP⟩ := Commons.LinearAlgebra.Matrix.exists_isSimilar_companion
      (A : Matrix (Fin 2) (Fin 2) F) A.2 hnc
    obtain ⟨X, Y, hXY⟩ :=
      Commons.LinearAlgebra.Matrix.companion_mem_commutatorSet hF ((A : Matrix (Fin 2) (Fin 2) F).trace)
    refine ⟨Commons.LinearAlgebra.Matrix.conjSL P⁻¹ X,
      Commons.LinearAlgebra.Matrix.conjSL P⁻¹ Y, ?_⟩
    rw [← map_commutatorElement (Commons.LinearAlgebra.Matrix.conjSL P⁻¹) X Y, hXY]
    apply Subtype.ext
    show ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          * (!![0, -1; 1, (A : Matrix (Fin 2) (Fin 2) F).trace] : Matrix (Fin 2) (Fin 2) F)
          * (((P⁻¹)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = (A : Matrix (Fin 2) (Fin 2) F)
    rw [inv_inv, ← hP]
    exact Commons.LinearAlgebra.Matrix.gl_conj_sandwich P (A : Matrix (Fin 2) (Fin 2) F)
  · simp only [not_forall, not_not] at hnc
    obtain ⟨c, hc⟩ := hnc
    have hdet : c ^ 2 = 1 := by
      have h := A.2
      rw [hc, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at h
      exact h
    rcases sq_eq_one_iff.mp hdet with hc1 | hc1
    · have hA : A = 1 := by
        apply Subtype.ext
        rw [hc, hc1]
        simp
      rw [hA]
      exact one_mem_commutatorSet _
    · have hA : A = -1 := by
        apply Subtype.ext
        rw [hc, hc1]
        simp [Matrix.SpecialLinearGroup.coe_neg]
      rw [hA]
      exact Commons.LinearAlgebra.Matrix.neg_one_mem_commutatorSet_SL2 hF

end Commons.GroupTheory.Commutator

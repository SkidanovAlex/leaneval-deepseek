import Mathlib
import Submission.Work.Models.PSL2.Defs
import Submission.Work.Models.PSL2.U_facts

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The centralizer of a transvection in `SL(2,F)`, `char F = 2`

Let `F` be a field of characteristic `2` and let `unip 1 = 1 + E₀₁ ∈ SL(2,F)` be the
standard transvection.  Its centralizer in `SL(2,F)` is the whole unipotent radical

`C_{SL(2,F)}(1 + E₀₁) = U`.

The inclusion `U ≤ C` is immediate since `U` is abelian (`unip a * unip b = unip (a+b)`).
For the converse, if `A = !![a,b;c,d] ∈ SL(2,F)` commutes with `1 + E₀₁` then a direct
entry computation of `A * (1+E₀₁) = (1+E₀₁) * A` gives `c = 0` and `d = a`; the determinant
condition `ad - bc = 1` becomes `a² = 1`, i.e. `(a+1)² = 0`, so `a = 1` (the field has no
zero divisors, and `-1 = 1` in characteristic `2`).  Hence `A = 1 + bE₀₁ = unip b ∈ U`.

This is the model statement for the `PSL(2,2ⁿ)` case of the Bender–Suzuki classification:
it identifies the centralizer of an involution of the unipotent radical with that radical,
so that `C_G(t) ≤ U ⋊ D` sits inside the standard Borel — the input to the
strongly-embedded analysis of `PSL(2,q)`.
-/

namespace Work.Models.PSL2

open Matrix

variable {F : Type*} [Field F] [CharP F 2]

/-- In a field of characteristic `2` the only solution of `a ^ 2 = 1` is `a = 1`. -/
lemma sq_eq_one_of_char_two {a : F} (h : a ^ 2 = 1) : a = 1 := by
  rcases sq_eq_one_iff.mp h with h | h
  · exact h
  · rwa [CharTwo.neg_eq] at h

/-- `unip b` lies in `U`. -/
lemma unip_mem_U (b : F) : unip b ∈ U (F := F) := ⟨b, rfl⟩

private lemma unip_one_coe_00 :
    ((unip (1 : F) : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by simp [unip_coe]

private lemma unip_one_coe_01 :
    ((unip (1 : F) : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 1 = 1 := by simp [unip_coe]

private lemma unip_one_coe_10 :
    ((unip (1 : F) : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simp [unip_coe]

private lemma unip_one_coe_11 :
    ((unip (1 : F) : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by simp [unip_coe]

/-- If `A : SL2 F` commutes with the transvection `unip 1`, then `A 1 0 = 0`. -/
lemma commute_unip_one_apply_one_zero {A : SL2 F}
    (hcomm : unip (1 : F) * A = A * unip (1 : F)) :
    (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  have hmat : ((unip (1 : F) * A : SL2 F) : Matrix (Fin 2) (Fin 2) F)
      = ((A * unip (1 : F) : SL2 F) : Matrix (Fin 2) (Fin 2) F) :=
    congrArg (fun B : SL2 F => (B : Matrix (Fin 2) (Fin 2) F)) hcomm
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hmat
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    unip_one_coe_00, unip_one_coe_01, unip_one_coe_10, one_mul, mul_one, mul_zero] at h
  simpa using h

/-- If `A : SL2 F` commutes with the transvection `unip 1`, then `A 0 0 = A 1 1`. -/
lemma commute_unip_one_apply_zero_zero {A : SL2 F}
    (hcomm : unip (1 : F) * A = A * unip (1 : F)) :
    (A : Matrix (Fin 2) (Fin 2) F) 0 0 = (A : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  have hmat : ((unip (1 : F) * A : SL2 F) : Matrix (Fin 2) (Fin 2) F)
      = ((A * unip (1 : F) : SL2 F) : Matrix (Fin 2) (Fin 2) F) :=
    congrArg (fun B : SL2 F => (B : Matrix (Fin 2) (Fin 2) F)) hcomm
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hmat
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    unip_one_coe_00, unip_one_coe_01, unip_one_coe_11, one_mul, mul_one] at h
  rw [add_comm ((A : Matrix (Fin 2) (Fin 2) F) 0 1)] at h
  exact (add_right_cancel_iff).mp h |>.symm

/-- An element of `SL(2,F)` commuting with the transvection `unip 1` lies in the
unipotent radical `U`. -/
lemma mem_U_of_commute_unip_one {A : SL2 F}
    (hcomm : unip (1 : F) * A = A * unip (1 : F)) : A ∈ U (F := F) := by
  have h10 := commute_unip_one_apply_one_zero hcomm
  have h00 := commute_unip_one_apply_zero_zero hcomm
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := Matrix.SpecialLinearGroup.det_coe A
  rw [Matrix.det_fin_two] at hdet
  rw [h10, mul_zero, sub_zero, ← h00] at hdet
  have h1 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 :=
    sq_eq_one_of_char_two (by rw [pow_two]; exact hdet)
  have h11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by rw [← h00, h1]
  rw [mem_U_iff]
  refine ⟨(A : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unip_coe, h10, h1, h11]

theorem centralizer_unip {F : Type*} [Field F] [CharP F 2] :
    Subgroup.centralizer ({Work.Models.PSL2.unip (F := F) 1} : Set (Work.Models.SL2 F))
      = Work.Models.PSL2.U (F := F) := by
  apply le_antisymm
  · intro A hA
    exact mem_U_of_commute_unip_one
      ((Subgroup.mem_centralizer_iff.mp hA) _ (Set.mem_singleton _))
  · intro A hA
    rw [mem_U_iff] at hA
    obtain ⟨b, rfl⟩ := hA
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← unip_add, ← unip_add, add_comm]

end Work.Models.PSL2

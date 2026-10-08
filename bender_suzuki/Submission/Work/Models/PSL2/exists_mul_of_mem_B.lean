import Mathlib
import Submission.Work.Models.PSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.PSL2.exists_mul_of_mem_B` — the Borel factors as `U · D`

Every upper triangular matrix `A = !![a, b; 0, c]` of determinant `1` satisfies `a * c = 1`, and
hence factors as
`A = !![1, b*a; 0, 1] * !![a, 0; 0, c]`, i.e. `A = u * d` with `u ∈ U` unipotent and `d ∈ D`
diagonal.  Thus every element of the standard Borel `B` is a product of an element of the
unipotent radical `U` and an element of the standard split torus `D`.
-/

namespace Work.Models.PSL2

open Matrix

/-- The diagonal matrix `!![a, 0; 0, c]` has determinant `1` when `a * c = 1`. -/
lemma det_diag_eq_one {F : Type*} [Field F] {a c : F} (h : a * c = 1) :
    (!![a, 0; 0, c] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [Matrix.det_fin_two_of]
  simp [h]

/-- The diagonal matrix `!![a, 0; 0, c]` built from `a * c = 1` is an element of `D`. -/
lemma mk_diag_mem_D {F : Type*} [Field F] [CharP F 2] {a c : F} (h : a * c = 1) :
    (⟨!![a, 0; 0, c], det_diag_eq_one h⟩ : Work.Models.SL2 F) ∈ D (F := F) := by
  refine ⟨?_, ?_⟩ <;> simp

/-- Matrix identity underlying the factorisation: the unipotent matrix `unip b` multiplied by
the diagonal matrix `!![a, 0; 0, d]` is `!![a, b*d; 0, d]`. -/
lemma unip_mul_diag {F : Type*} [Field F] [CharP F 2] (b a d : F) :
    (↑(unip b) : Matrix (Fin 2) (Fin 2) F) * (!![a, 0; 0, d] : Matrix (Fin 2) (Fin 2) F)
      = !![a, b * d; 0, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, unip_coe]

theorem exists_mul_of_mem_B {F : Type*} [Field F] [CharP F 2] {A : Work.Models.SL2 F}
    (hA : A ∈ Work.Models.PSL2.B (F := F)) :
    ∃ u ∈ Work.Models.PSL2.U (F := F),
      ∃ d ∈ Work.Models.PSL2.D (F := F), A = u * d := by
  -- the `(1,0)`-entry of `A` vanishes, and its determinant is `1`
  have h10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hA
  have hdet : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have h := A.2
    rw [Matrix.det_fin_two] at h
    rw [h10, mul_zero, sub_zero] at h
    exact h
  -- the unipotent factor `1 + (b*a) E₀₁` and the diagonal factor `diag(a, c)`
  let u : Work.Models.SL2 F :=
    unip ((A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 0 0)
  let d : Work.Models.SL2 F :=
    ⟨!![(A : Matrix (Fin 2) (Fin 2) F) 0 0, 0; 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1],
      det_diag_eq_one hdet⟩
  have hu : u ∈ U (F := F) := ⟨_, rfl⟩
  have hdmem : d ∈ D (F := F) := mk_diag_mem_D hdet
  refine ⟨u, hu, d, hdmem, ?_⟩
  have hcoe := Matrix.SpecialLinearGroup.coe_mul u d
  -- `A` is the upper triangular matrix with the same entries
  have hAmat : (A : Matrix (Fin 2) (Fin 2) F) =
      !![(A : Matrix (Fin 2) (Fin 2) F) 0 0, (A : Matrix (Fin 2) (Fin 2) F) 0 1;
         0, (A : Matrix (Fin 2) (Fin 2) F) 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10]
  -- the product `u * d` has the same underlying matrix
  have hprod : (A : Matrix (Fin 2) (Fin 2) F)
      = (↑u : Matrix (Fin 2) (Fin 2) F) * (↑d : Matrix (Fin 2) (Fin 2) F) := by
    rw [hAmat]
    have hstep : (↑u : Matrix (Fin 2) (Fin 2) F) * (↑d : Matrix (Fin 2) (Fin 2) F)
        = !![(A : Matrix (Fin 2) (Fin 2) F) 0 0,
              ((A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 0 0)
                * (A : Matrix (Fin 2) (Fin 2) F) 1 1; 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1] := by
      change (↑(unip ((A : Matrix (Fin 2) (Fin 2) F) 0 1
              * (A : Matrix (Fin 2) (Fin 2) F) 0 0)) : Matrix (Fin 2) (Fin 2) F)
          * (!![(A : Matrix (Fin 2) (Fin 2) F) 0 0, 0;
               0, (A : Matrix (Fin 2) (Fin 2) F) 1 1] : Matrix (Fin 2) (Fin 2) F)
        = !![(A : Matrix (Fin 2) (Fin 2) F) 0 0,
              ((A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 0 0)
                * (A : Matrix (Fin 2) (Fin 2) F) 1 1; 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1]
      exact unip_mul_diag _ _ _
    rw [hstep]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_assoc, hdet]
  -- finally recover the group equality from the matrix equality
  refine Matrix.SpecialLinearGroup.ext A (u * d) ?_
  intro i j
  exact (congrFun (congrFun hprod i) j).trans (congrFun (congrFun hcoe i) j).symm

end Work.Models.PSL2

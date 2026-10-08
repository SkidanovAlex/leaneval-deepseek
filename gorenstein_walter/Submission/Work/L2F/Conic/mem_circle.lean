import Mathlib
import Submission.Work.L2F.Defs

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Conic

/-- Membership in `circle F = C_{SL(2,F)}(z)`, `z = !![0,1;-1,0]`: exactly the matrices
`!![a, b; -b, a]` with `a² + b² = 1`.  (From `x * z = z * x` for `x = !![a,b;c,d]` one gets
`c = -b`, `d = a`; conversely such a matrix commutes with `z` and lies in `SL(2,F)` when
`a² + b² = 1`.) -/
theorem mem_circle (F : Type*) [Field F] (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    x ∈ Work.L2F.circle F ↔
      ∃ a b : F, a ^ 2 + b ^ 2 = 1 ∧
        (x : Matrix (Fin 2) (Fin 2) F) = !![a, b; -b, a] := by
  constructor
  · intro hx
    -- `x` commutes with `z`, hence with the matrix `!![0,1;-1,0]`.
    have hcomm : Work.L2F.z F * x = x * Work.L2F.z F :=
      (Subgroup.mem_centralizer_iff.mp hx) (Work.L2F.z F) rfl
    have hmat : ((Work.L2F.z F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
          ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
          ((Work.L2F.z F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hcomm]
    rw [Work.L2F.z, Work.PSL2.coe_weyl] at hmat
    -- the four entries of the matrix relation `!![0,1;-1,0] * M = M * !![0,1;-1,0]`
    have k1 : (!![0, 1; -1, 0] * ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 0 0 = ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have k2 : (((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * !![0, 1; -1, 0] :
        Matrix (Fin 2) (Fin 2) F) 0 0 = - ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have k3 : (!![0, 1; -1, 0] * ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 0 1 = ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have k4 : (((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * !![0, 1; -1, 0] :
        Matrix (Fin 2) (Fin 2) F) 0 1 = ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    -- `c = -b` and `d = a`
    have e00 : ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 =
        - ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 := by
      have h' := congrFun (congrFun hmat 0) 0
      rw [k1, k2] at h'
      exact h'
    have e01 : ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 =
        ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      have h' := congrFun (congrFun hmat 0) 1
      rw [k3, k4] at h'
      exact h'
    refine ⟨((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0,
            ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1, ?_, ?_⟩
    · -- `a² + b² = 1` is the determinant condition
      have hdet : ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).det = 1 :=
        Matrix.SpecialLinearGroup.det_coe x
      rw [Matrix.det_fin_two] at hdet
      rw [e00, e01] at hdet
      linear_combination hdet
    · -- the matrix is `!![a, b; -b, a]`
      ext i j
      fin_cases i <;> fin_cases j <;> simp [e00, e01]
  · rintro ⟨a, b, hab, hxeq⟩
    rw [Work.L2F.circle, Subgroup.mem_centralizer_iff]
    intro h hmem
    rw [Set.mem_singleton_iff] at hmem
    subst hmem
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hxeq]
    rw [show ((Work.L2F.z F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] from
      Work.PSL2.coe_weyl F]
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

end Work.L2F.Conic

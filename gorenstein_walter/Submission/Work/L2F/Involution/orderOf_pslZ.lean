import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff

namespace Work.L2F.Involution

open scoped MatrixGroups
open Matrix

/-! ## The square of the Weyl element -/

/-- `z * z = -1` : the square of the Weyl element `!![0,1;-1,0]` of `SL(2,F)` is the matrix
`-1`, i.e. the nontrivial central element `negOne F`. -/
theorem weyl_mul_weyl (F : Type*) [Field F] :
    Work.PSL2.weyl F * Work.PSL2.weyl F = Work.L2F.negOne F := by
  apply Subtype.ext
  change ((Work.PSL2.weyl F * Work.PSL2.weyl F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
    ((Work.L2F.negOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
  rw [Matrix.SpecialLinearGroup.coe_mul, Work.PSL2.coe_weyl, Matrix.mul_fin_two,
    show ((Work.L2F.negOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The image of `-1` in `PSL(2,F)` is trivial (`-1` is central). -/
theorem pslMap_negOne (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    Work.PSL2.pslMap F (Work.L2F.negOne F) = 1 :=
  (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (Work.L2F.negOne F)).mpr (Or.inr rfl)

/-- The Weyl element is not the identity (its `(0,1)` entry is `1`, that of `1` is `0`). -/
theorem weyl_ne_one (F : Type*) [Field F] : Work.PSL2.weyl F ≠ (1 : SL(2, F)) := by
  intro h
  have h' := congrArg (fun x : SL(2, F) => ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [Work.PSL2.coe_weyl] at h'

/-- The Weyl element is not `-1` (its `(0,1)` entry is `1`, that of `-1` is `0`). -/
theorem weyl_ne_negOne (F : Type*) [Field F] : Work.PSL2.weyl F ≠ Work.L2F.negOne F := by
  intro h
  have h' := congrArg (fun x : SL(2, F) => ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [Work.PSL2.coe_weyl,
    show ((Work.L2F.negOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 from rfl] at h'

/-- The image of `z` in `PSL(2,F)` is an involution (for `(2:F) ≠ 0`).
Proof: `z * z = -1`, so `pslZ F * pslZ F = 1`, and `pslZ F ≠ 1` because `z ≠ ±1`
(`pslMap_eq_one_iff`), i.e. `orderOf (pslZ F) ∣ 2` and `≠ 1`. -/
theorem orderOf_pslZ (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) : orderOf (Work.L2F.pslZ F) = 2 := by
  have hsq : Work.L2F.pslZ F ^ 2 = 1 := by
    rw [pow_two, Work.L2F.pslZ, Work.PSL2.pslWeyl, ← map_mul, weyl_mul_weyl F,
      pslMap_negOne F h2]
  have hne : Work.L2F.pslZ F ≠ 1 := by
    intro h
    have hp : Work.PSL2.pslMap F (Work.PSL2.weyl F) = 1 := by
      rw [Work.L2F.pslZ, Work.PSL2.pslWeyl] at h
      exact h
    rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (Work.PSL2.weyl F)).mp hp with hh | hh
    · exact weyl_ne_one F hh
    · exact weyl_ne_negOne F hh
  exact orderOf_eq_prime (p := 2) hsq hne

end Work.L2F.Involution

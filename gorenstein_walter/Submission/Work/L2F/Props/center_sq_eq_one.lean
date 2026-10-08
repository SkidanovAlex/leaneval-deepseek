import Mathlib
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs

namespace Work.L2F.Props

/-- A central element of `GL(2,F)` (`F` a field) with `A * A = 1` is `1` or `-1`.
Reason: the centre of `GL(2,F)` is the range of `scalar`, so `A = scalar u` (`u : Fˣ`); `A * A = 1` then gives `scalar (u * u) = scalar 1`, whose `(0,0)`-entries give `(u : F) * (u : F) = 1`, i.e. `(u - 1) * (u + 1) = 0`, so `u = 1` or `u = -1`, i.e. `A = scalar 1 = 1` or `A = scalar (-1) = negOneGL`. -/
theorem center_sq_eq_one (F : Type*) [Field F] (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : A ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F)) (h : A * A = 1) :
    A = 1 ∨ A = Work.L2F.Props.negOneGL F := by
  -- The centre of `GL(2,F)` consists of the scalar matrices.
  obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hA
  -- The `(0,0)`-entry of `A * A = 1` gives `a * a = 1`.
  have h00 : a * a = 1 := by
    have hh := congrArg (fun x : Matrix.GeneralLinearGroup (Fin 2) F =>
      (x : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one] at hh
    rw [← ha] at hh
    rw [← map_mul, Matrix.scalar_apply] at hh
    simpa using hh
  rcases mul_self_eq_one_iff.mp h00 with h1 | h1
  · -- `a = 1`, so `A = scalar 1 = 1`.
    left
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_one, ← ha, h1, map_one]
  · -- `a = -1`, so `A = scalar (-1) = -1 = negOneGL`.
    right
    apply Units.ext
    rw [Work.L2F.Props.negOneGL_apply, ← ha, h1, map_neg, map_one]

end Work.L2F.Props

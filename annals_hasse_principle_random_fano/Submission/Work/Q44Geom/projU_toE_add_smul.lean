import Mathlib
import Submission.Work.HP.BCSDefs
import Submission.Work.HP.Q44Child.SuperDefs

namespace Work.Q44Geom

/-- `projU` only sees the component of `w` orthogonal to the line spanned by `x`:
the `x`-part of `a • x + b • w` is killed, leaving the `b`-multiple of `projU x w`. -/
lemma projU_toE_add_smul (x w : Fin 5 → ℤ) (hx0 : x ≠ 0) (a b : ℤ) :
    Work.HP.projU (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE (a • x + b • w))
      = (b : ℝ) • Work.HP.projU (Work.HP.Q44Child.toE x) (Work.HP.Q44Child.toE w) := by
  -- Split the integral combination through the `ℤ`-linear inclusion `toE`,
  -- then reinterpret the `ℤ`-scalars as real scalars so that `projU` (ℝ-linear) applies.
  rw [map_add, map_smul, map_smul]
  conv_lhs =>
    rw [← Int.cast_smul_eq_zsmul ℝ a (Work.HP.Q44Child.toE x),
        ← Int.cast_smul_eq_zsmul ℝ b (Work.HP.Q44Child.toE w)]
  rw [map_add, map_smul, map_smul]
  -- `projU` kills the direction `toE x` it projects away from.
  have hself : (Work.HP.projU (Work.HP.Q44Child.toE x)) (Work.HP.Q44Child.toE x) = 0 := by
    have := Work.HP.projU_add_smul (Work.HP.Q44Child.toE x) (1 : ℝ) 0
    simpa using this
  rw [hself, smul_zero, zero_add]

end Work.Q44Geom

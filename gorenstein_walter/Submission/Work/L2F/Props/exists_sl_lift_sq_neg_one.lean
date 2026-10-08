import Mathlib
import Submission.Work.L2F.Involution.lift_sq_neg_one
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs

namespace Work.L2F.Props

/-- An involution `t` of `PGL(2,F)` whose class lies in `L₂(F) = range (PSL(2,F) → PGL(2,F))` lifts to an element `T ∈ SL(2,F)` with `T² = -1` (as matrices) and `toPGL T = t`.
Proof: `t = toPGL u` for a (unique) `u : PSL(2,F)`, and `orderOf u = 2` because `toPGL` is injective; `Work.L2F.Involution.lift_sq_neg_one` then supplies `x ∈ SL(2,F)` with `pslMap x = u` and `x * x = -1`, and `toPGL x = toPGL (pslMap x) = t`. -/
theorem exists_sl_lift_sq_neg_one (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (t : Matrix.ProjGenLinGroup (Fin 2) F) (ht : orderOf t = 2)
    (htL : t ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F →*
        Matrix.ProjGenLinGroup (Fin 2) F).range) :
    ∃ T : Matrix.SpecialLinearGroup (Fin 2) F,
      Matrix.SpecialLinearGroup.toPGL T = t ∧
      (T : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F) = -1 := by
  -- `t` lies in the range of `PSL(2,F) →* PGL(2,F)`: pick a preimage `u`.
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp htL
  -- `toPGL` is injective, so it preserves orders: `orderOf u = orderOf t = 2`.
  have hu2 : orderOf u = 2 := by
    rw [← orderOf_injective Matrix.ProjectiveSpecialLinearGroup.toPGL
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective u, hu, ht]
  -- Lift the involution `u` of `PSL(2,F)` to `x ∈ SL(2,F)` with `x² = -1`.
  obtain ⟨x, hx1, hx2⟩ := Work.L2F.Involution.lift_sq_neg_one F h2 u hu2
  refine ⟨x, ?_, hx2⟩
  -- `toPGL x = toPGL (pslMap x) = toPGL u = t`.
  rw [← hu, ← hx1]
  rfl

end Work.L2F.Props

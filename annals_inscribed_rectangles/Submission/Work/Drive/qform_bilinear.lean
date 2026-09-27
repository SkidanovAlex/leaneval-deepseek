import Mathlib
import Submission.Work.Drive.squareSystemForm

namespace Work.Drive

/-- `qform` is additive, `ℝ`-homogeneous (in each variable), antisymmetric, and isotropic
(`qform v v = 0`) — the algebraic facts about the model form of the class equality on `ℝP³`.

Both variables are read componentwise (`Fin 3`); the cross-product term is handled by
`cross_apply` and the three `Matrix.cons_val_*` simplifications, after which each of the six
claims is a polynomial identity in the coordinates closed by `ring`. -/
theorem qform_bilinear (v v' w w' : Work.Drive.Eucl 3) (c : ℝ) :
    Work.Drive.qform (v + v') w = Work.Drive.qform v w + Work.Drive.qform v' w ∧
    Work.Drive.qform v (w + w') = Work.Drive.qform v w + Work.Drive.qform v w' ∧
    Work.Drive.qform (c • v) w = c • Work.Drive.qform v w ∧
    Work.Drive.qform v (c • w) = c • Work.Drive.qform v w ∧
    Work.Drive.qform v w = - Work.Drive.qform w v ∧
    Work.Drive.qform v v = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ext k <;>
    fin_cases k <;>
    simp [Work.Drive.qform_ofLp, Work.Drive.imagPart_ofLp, cross_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;> ring

end Work.Drive

import Mathlib
import Submission.Work.TMC13.Defs

namespace Work.TMC13

/-- The `t ↔ -t` Fourier identity for the action of a real `2×2` matrix on a unit vector:
`smul A (vc t) = c1 A * vc t + c2 A * conj (vc t)`. -/
lemma fourier_amp_smul (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    Work.TMComp.RotBasics.smul A (Work.TMComp.RotBasics.vc t) =
      c1 A * Work.TMComp.RotBasics.vc t +
        c2 A * (starRingEnd ℂ (Work.TMComp.RotBasics.vc t)) := by
  apply Complex.ext <;>
    simp [Work.TMComp.RotBasics.smul, Work.TMComp.RotBasics.vc, c1, c2,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;>
    ring

/-- The amplitude identity `‖c1 A‖² − ‖c2 A‖² = det A`, written in real coordinates. -/
lemma fourier_amp_det (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (c1 A).re ^ 2 + (c1 A).im ^ 2 - ((c2 A).re ^ 2 + (c2 A).im ^ 2) = A.det := by
  simp [c1, c2, Matrix.det_fin_two]
  ring

theorem fourier_amp (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ t : ℝ, Work.TMComp.RotBasics.smul A (Work.TMComp.RotBasics.vc t) =
      Work.TMC13.c1 A * Work.TMComp.RotBasics.vc t +
        Work.TMC13.c2 A * (starRingEnd ℂ (Work.TMComp.RotBasics.vc t))) ∧
    ((Work.TMC13.c1 A).re ^ 2 + (Work.TMC13.c1 A).im ^ 2 -
      ((Work.TMC13.c2 A).re ^ 2 + (Work.TMC13.c2 A).im ^ 2) = A.det) :=
  ⟨fun t => fourier_amp_smul A t, fourier_amp_det A⟩

end Work.TMC13

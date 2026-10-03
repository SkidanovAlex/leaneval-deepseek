import Mathlib
import Submission.Work.Interfaces.Fatou

namespace Work.Fatou.Surface.Wirtinger

/-- The real Fréchet derivative of `w ↦ f (w - c)` at `z` is the derivative of `f` at `z - c`:
translation of the argument does not change the derivative. -/
theorem fderiv_comp_sub_const (f : ℂ → ℂ) (c z : ℂ) :
    fderiv ℝ (fun w => f (w - c)) z = fderiv ℝ f (z - c) :=
  fderiv_comp_sub c

/-- Translation invariance of the Wirtinger derivatives:
`∂(w ↦ f (w - c)) z = ∂f (z - c)` and likewise for `∂̄`. -/
theorem dz_dzbar_sub_const (f : ℂ → ℂ) (c z : ℂ) :
    MandelDim.dz (fun w => f (w - c)) z = MandelDim.dz f (z - c) ∧
      MandelDim.dzbar (fun w => f (w - c)) z = MandelDim.dzbar f (z - c) := by
  have h : fderiv ℝ (fun w : ℂ => f (w - c)) z = fderiv ℝ f (z - c) :=
    fderiv_comp_sub_const f c z
  constructor <;> simp only [MandelDim.dz, MandelDim.dzbar, h]

end Work.Fatou.Surface.Wirtinger

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped Real FourierTransform

namespace Work.SmallBoxBridge.Resolve

theorem kinFT_eq_fourier (g : EuclideanSpace ℝ (Fin 3) → ℂ) (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT g p
      = (FourierTransform.fourier g) ((2 * Real.pi)⁻¹ • p) := by
  rw [Real.fourier_eq']
  simp only [Submission.BoseGases.kinFT, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  rw [real_inner_smul_right, real_inner_comm p y]
  congr 1
  have h2 : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero]
  push_cast
  field_simp

end Work.SmallBoxBridge.Resolve

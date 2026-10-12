import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Calculus.ContDiff.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
open Real
namespace Work.BoseFixB1.KH

theorem fourier_pow_norm_le_aux (K : ℕ) (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hf : ContDiff ℝ (K : ℕ∞) f)
    (hint : ∀ n : ℕ, n ≤ K → MeasureTheory.Integrable (iteratedFDeriv ℝ n f))
    (w : EuclideanSpace ℝ (Fin 3)) :
    (2 * π) ^ K * ‖w‖ ^ K * ‖FourierTransform.fourier f w‖
      ≤ ∫ z : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ K f z‖ := by sorry

end Work.BoseFixB1.KH

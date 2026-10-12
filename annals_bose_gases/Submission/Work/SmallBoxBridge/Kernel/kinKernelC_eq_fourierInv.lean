import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped Real Topology BigOperators FourierTransform

namespace Work.SmallBoxBridge.Kernel

/-- The `p`-convention kernel `kinKernelC F z = (2π)⁻³∫_p F(‖p‖)e^{i⟪p,z⟫}dp` is the
Mathlib inverse Fourier transform of the symbol `ξ ↦ F(2π‖ξ‖)`, the change of variables
`p = 2πξ` (Lebesgue measure scaling by `(2π)³`). -/
theorem kinKernelC_eq_fourierInv (F : ℝ → ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinKernelC F z =
      FourierTransform.fourierInv
        (fun ξ : EuclideanSpace ℝ (Fin 3) => (F (2 * Real.pi * ‖ξ‖) : ℂ)) z := by
  rw [Real.fourierInv_eq', Submission.BoseGases.kinKernelC]
  simp only [smul_eq_mul]
  -- `G v = H ((2π) • v)` for `H p = e^{i⟪p,z⟫} F(‖p‖)`.
  have hcomp : (fun v : EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (↑(2 * Real.pi * inner ℝ v z) * Complex.I) * ↑(F (2 * Real.pi * ‖v‖)))
      = (fun v : EuclideanSpace ℝ (Fin 3) =>
        (fun p : EuclideanSpace ℝ (Fin 3) => Complex.exp (↑(inner ℝ p z) * Complex.I) * ↑(F ‖p‖))
          ((2 * Real.pi) • v)) := by
    funext v
    have h1 : inner ℝ ((2 * Real.pi) • v) z = 2 * Real.pi * inner ℝ v z := by
      rw [real_inner_smul_left]
    have h2 : ‖(2 * Real.pi) • v‖ = 2 * Real.pi * ‖v‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    simp only
    rw [h1, h2]
  rw [hcomp, Measure.integral_comp_smul_of_nonneg (μ := volume) (hR := by positivity)
        (fun p : EuclideanSpace ℝ (Fin 3) => Complex.exp (↑(inner ℝ p z) * Complex.I) * ↑(F ‖p‖))
        (2 * Real.pi), finrank_euclideanSpace, Fintype.card_fin,
      Complex.real_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  rw [mul_comm (↑(inner ℝ p z) : ℂ) Complex.I]
  exact mul_comm _ _

end Work.SmallBoxBridge.Kernel

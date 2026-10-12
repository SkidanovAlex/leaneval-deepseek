import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.KinRowQuant
import Submission.Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Plancherel for the `p`-convention kinetic Fourier transform (`L¹ ∩ L²` states)

For `u : ℝ³ → ℂ` a smooth compactly supported function,

`(2π)⁻³ ∫_p ‖kinFT u p‖² = ∫_x ‖u x‖²`,

where `kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy` is the corpus's `p`-convention Fourier transform
(`Submission.BoseGases.kinFT`).

The mathematical content is entirely delegated to the corpus lemma
`Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel` (Plancherel for `L¹ ∩ L²` functions, proved via
`kinFT_eq_fourier`, the `p ↦ (2π)⁻¹ • p` change of variables and `Lp.norm_fourier_eq`); here we
only bridge the hypotheses: a `ContDiff ℝ ⊤` function with compact support is continuous with
compact support, hence integrable and in `L²` (`Continuous.memLp_of_hasCompactSupport`), and
`(2π)³ ≠ 0`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

theorem kinFT_plancherel {u : ℝ³ → ℂ} (hu : ContDiff ℝ (⊤ : ENat) u)
    (huc : HasCompactSupport u) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ p, ‖Submission.BoseGases.kinFT u p‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  have hint : Integrable u := hu.continuous.integrable_of_hasCompactSupport huc
  have hml : MemLp u 2 := hu.continuous.memLp_of_hasCompactSupport huc
  have hplan := Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel hint hml
  have hne : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
  rw [hplan, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end Work.BoseBoxFock

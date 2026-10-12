import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.Defs
import Submission.Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.HighMassAux

/-- Plancherel in the corpus's `p`-convention for `L¹ ∩ L²` functions:
`(2π)⁻³ ∫_p ‖kinFT u p‖² = ∫_x ‖u x‖²`.

This is the normalised form of `Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel`,
which states the un-normalised identity `∫_p ‖kinFT u p‖² = (2π)³ ∫_x ‖u x‖²`
under the hypotheses `Integrable u` and `MemLp u 2`; the `L¹` hypothesis here is
converted with `MeasureTheory.memLp_one_iff_integrable`. -/
theorem plancherel_L1L2 {u : Submission.BoseGases.kcE3 → ℂ}
    (h1 : MeasureTheory.MemLp u 1 MeasureTheory.volume)
    (h2 : MeasureTheory.MemLp u 2 MeasureTheory.volume) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : Submission.BoseGases.kcE3,
        ‖Submission.BoseGases.kinFT u p‖ ^ 2
      = ∫ x : Submission.BoseGases.kcE3, ‖u x‖ ^ 2 := by
  have hint : MeasureTheory.Integrable u MeasureTheory.volume :=
    MeasureTheory.memLp_one_iff_integrable.mp h1
  have h := Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel (F := u) hint h2
  have hne : (2 * Real.pi) ^ 3 ≠ 0 := by positivity
  rw [h, inv_mul_cancel_left₀ hne]

end Work.BoseFixB3.HighMassAux

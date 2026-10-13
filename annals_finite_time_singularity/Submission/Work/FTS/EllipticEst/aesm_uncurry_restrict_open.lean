import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-- Almost everywhere strong measurability of a function which is only known to be continuous
on the open quadrant `(0,∞) × (0,π/2)`, with respect to the product of Lebesgue measure
restricted to `(a,b]` and to `Iθ = [0,π/2]`.

Since `0 ≤ a` forces `(a,b] ⊆ (0,∞)`, the domain `(a,b] × Iθ` is covered by the open quadrant
`(0,∞) × (0,π/2)` together with the null set `(a,b] × {0,π/2}`.  Hence the hypothesis of
continuity on the open quadrant already gives almost everywhere strong measurability, and the
result for the larger set `Iz = [0,∞)` (proved in `Work.Spaces.aesm_of_continuousOn_Qd`) is
transferred by monotonicity of the restricted measure. -/
theorem aesm_uncurry_restrict_open (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) {a b : ℝ} (ha : 0 ≤ a) :
    MeasureTheory.AEStronglyMeasurable g
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- `0 ≤ a` makes the half-open interval `(a,b]` a subset of `Iz = [0,∞)`.
  have hA : Set.Ioc a b ⊆ Work.Spaces.Iz :=
    fun x hx => le_of_lt (lt_of_le_of_lt ha hx.1)
  have hmain := Work.Spaces.aesm_of_continuousOn_Qd g hg
  -- Write both product measures as restrictions of the planar Lebesgue measure.
  rw [MeasureTheory.Measure.prod_restrict (Set.Ioc a b) Work.Spaces.Iθ]
  rw [MeasureTheory.Measure.prod_restrict Work.Spaces.Iz Work.Spaces.Iθ] at hmain
  exact hmain.mono_measure
    (MeasureTheory.Measure.restrict_mono (Set.prod_mono hA (subset_refl _)) le_rfl)

end Work.FTS.EllipticEst

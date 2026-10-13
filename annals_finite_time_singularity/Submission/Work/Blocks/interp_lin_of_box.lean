import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Blocks.interpol_mixed_box_proof
import Submission.Work.Blocks.interp_truncation
import Submission.Work.FTS.EllipticEst.interpol_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Blocks

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# `Work.Blocks.interp_lin_of_box`

The mixed weighted interpolation estimate of the paper's §Elliptic Estimates in the general
(non-compactly-supported) case:

`α² ∫∫ (D_z∂_θG)² w² σ ≤ C (α⁴ ∫∫ (D_z²G)² w² σ + ∫∫ (∂_θ²G)² w² σ + α² ∫∫ (D_zG)² w² σ)`

for `G` of class `C^∞` on the open strip `(0,∞) × (-1, π/2+1)`, vanishing on the two angular
boundary lines, with the four `z`-slice integrability conditions `FourInt G` (which make the
four Bochner functionals honest numbers rather than the junk value `0`).

The proof is the composition of the two halves of the reduction that already exist in the
workspace:

* `Work.Blocks.interp_box_uniform_aux` (`interpol_mixed_box_proof.lean`) — the **box** case:
  the same inequality for `G` supported in a compact `[δ,R] ⊂ (0,∞)`, with a constant `C`
  uniform in `δ`, `R` and `G` (so the `∃ C` can be pulled outside the `∀ δ R`);
* `Work.Blocks.interp_truncation` (`interp_truncation.lean`) — the **truncation** step: from
  the box case for a fixed constant `C` (the logarithmic radial cut-offs
  `χ_k ↗ 1`, with the `O(1/log k)` truncation errors controlled by Fatou and the extra
  `FourInt` hypothesis), it produces the general case for the same `C`.

The only thing to check is that the quantifier order of the box hypothesis matches: the box
case is stated as `∀ α G, … → ∀ δ R, 0 < δ → δ < R → …`, while the truncation consumes
`∀ δ R, 0 < δ → δ < R → ∀ α G, …`.  Both are universally quantified hypotheses with no
dependencies between `δ, R` on the one side and `α, G` on the other, so they are the same
statement read in a different order.
-/

theorem interp_lin_of_box : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))) →
      (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
      Work.FTS.EllipticEst.FourInt G →
      α ^ 2 * Work.FTS.EllipticEst.mixInt G
        ≤ C * (α ^ 4 * Work.FTS.EllipticEst.ddInt G
            + Work.FTS.EllipticEst.ttInt G
            + α ^ 2 * Work.FTS.EllipticEst.dInt G) := by
  -- the box case, with a constant uniform in the support interval and in `G`
  obtain ⟨C, hCpos, hbox⟩ := Work.Blocks.interp_box_uniform_aux
  refine ⟨C, hCpos, ?_⟩
  -- the truncation step: the general case follows from the box case for the same constant
  refine Work.Blocks.interp_truncation C hCpos ?_
  -- reorder the (independent) quantifiers `α, G` and `δ, R` of the box hypothesis
  intro δ R hδ hδR α G hα hα4 hS h0 hπ hsupp _
  exact hbox α hα hα4 G hS h0 hπ δ R hδ hδR hsupp

end Work.Blocks

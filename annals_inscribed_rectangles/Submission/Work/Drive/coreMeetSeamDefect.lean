import Mathlib
import Submission.Work.Drive.coreLoopClosed
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.sideCountDefs

/-!
# The seam defect of the box count `coreSideCount`

`Work.Drive.coreSideCount Q c P = #(coreMeet Q c P)` counts the parameter pairs
`(s, x) ∈ [0,1] × unitBox 2` at which the core loop `t ↦ Q (exp (i π t))` meets the clamped sweep.
Both parameter domains are quotients presented by *closed* boxes, so the box count double counts the
meets at the two seams:

* **the loop's seam.**  The chart's seam clause `Q (-z) = Q z` on `‖z‖ = 1` gives
  `coreLoop Q 0 = coreLoop Q 1` (`Work.Drive.coreLoop_zero_eq_one`), hence a meet at the loop's base
  point has *both* box representatives `(0, x)` and `(1, x)`;
* **the chain's seam.**  The chain is seam-invariant (`Work.Drive.clampedSweep_seamInv`), so a meet at
  a chain parameter `x` on the seam (`Work.Drive.onSeam x`, i.e. `x 0 ∈ {0,1}` or `x 1 ∈ {0,1}`) has
  both representatives `x` and `seamInv x = (1-x₀, 1-x₁, x₂)`.

This is the *seam* defect of `Odd (coreSideCount …)` (see
`Submission/Work/Drive/HN4_SEAM_DEFECT.md`): unlike the tangency defect of a raw cardinality count
(`Work.Drive.parity_jump_at_tangency`), it is not removable by a generic small perturbation, since the
box count agrees with the geometric (pairing) count only at the angles where no meet sits on a seam.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **The loop-seam defect.**  If the core loop meets the chain at the loop's base point, then both
box representatives `(0, x)` and `(1, x)` are points of `coreMeet`: the geometric meet is counted
twice. -/
theorem coreMeet_seam_pair {Q : ℂ → CappingSpace}
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) (c : ℝ) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (x : Work.Drive.Amb 2) (hx : x ∈ Submission.Drive.unitBox 2)
    (h : coreLoop Q 0 = clampedSweep c (fun t => 1 - t) P x) :
    ((0 : ℝ), x) ∈ coreMeet Q c P ∧ ((1 : ℝ), x) ∈ coreMeet Q c P := by
  have h01 : coreLoop Q 0 = coreLoop Q 1 := coreLoop_zero_eq_one hQseam
  refine ⟨⟨⟨le_rfl, zero_le_one⟩, hx, h⟩, ⟨⟨zero_le_one, le_rfl⟩, hx, ?_⟩⟩
  rw [← h01]
  exact h

/-- The two representatives of the loop-seam meet are *distinct* points of the box. -/
theorem coreMeet_seam_pair_ne (x : Work.Drive.Amb 2) :
    (((0 : ℝ), x) : ℝ × Work.Drive.Amb 2) ≠ ((1 : ℝ), x) := by
  intro h
  exact absurd (congrArg Prod.fst h) (by norm_num)

/-- **The chain-seam defect, parameter side.**  A chain parameter on the seam and inside the box has a
*second*, distinct box representative `seamInv x = (1-x₀, 1-x₁, x₂)`, which is again in the box. -/
theorem seamInv_mem_unitBox {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ Submission.Drive.unitBox 2)
    (hseam : onSeam x) : seamInv x ∈ Submission.Drive.unitBox 2 := by
  intro i
  rw [Submission.Drive.unitBox, Set.mem_ofPred_eq] at hx
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  fin_cases i
  · simpa [seamInv] using ⟨by linarith [h0.2], by linarith [h0.1]⟩
  · simpa [seamInv] using ⟨by linarith [h1.2], by linarith [h1.1]⟩
  · simpa [seamInv] using h2

/-- **The chain-seam defect, meet side.**  A meet whose chain parameter lies on the seam has both box
representatives as meets. -/
theorem coreMeet_chainSeam_pair (c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hP : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P y = P (seamInv2 y))
    (Q : ℂ → CappingSpace) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ Submission.Drive.unitBox 2)
    (hseam : onSeam x) (h : coreLoop Q 0 = clampedSweep c (fun t => 1 - t) P x) :
    ((0 : ℝ), seamInv x) ∈ coreMeet Q c P := by
  rw [coreMeet, Set.mem_ofPred_eq]
  refine ⟨⟨le_rfl, zero_le_one⟩, seamInv_mem_unitBox hx hseam, ?_⟩
  rw [← clampedSweep_seamInv c (fun t => 1 - t) P hP x hseam]
  exact h

end

end Work.Drive

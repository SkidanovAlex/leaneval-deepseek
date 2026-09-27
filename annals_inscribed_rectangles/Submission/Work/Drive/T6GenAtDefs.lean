import Mathlib
import Submission.Work.Drive.transportThreeLevel
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.meetBoxEngine

/-!
# The at-`t` input bundle of the transport `T6` (`NOTES_LEAD_hblock_uniformity.md` §4.3)

The transport `T6` is *not* uniform in the family parameter (`NOTES_LEAD_hblock_uniformity.md` §3,
`ADMISSIBILITY_FAMILY_STATUS.md` §6): at a non-transverse parameter the box counts can be infinite and
the diameter side function is arbitrary.  The lead's fix is to carry the T6 inputs **at one parameter**,
bundled as `T6GenAt`, and to provide the wrapper `odd_topBdryMeet_zero_iff_of_T6GenAt` which turns that
bundle into T6's conclusion.

This file contains only the two *definitions* (verbatim from the lead's note, with the fourth conjunct
of `T6GenAt` already deleted per `NOTES_LEAD_hfib.md` §4.3 — the cut-fibre conditions are not needed
thanks to `Work.Drive.colCount_zero_eq_topBdryMeet_nofib`); the lemmas about them are delegated/on disk
elsewhere.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **A `2`-chain that meets a `1`-periodic loop `L` in general position.**  Exactly the triple kept
open by `Work.Drive.eventually_good_meetBox` (`goodPair_pertChart_isOpen.lean`): the meet set of the loop
and the sweep is finite, all its parameters are strictly interior in the box, and the loop and the sweep
are transverse there. -/
def GoodLoopChain (L : ℝ → CappingSpace) (W : EuclideanSpace ℝ (Fin 3) → CappingSpace) : Prop :=
  (meetBox L W).Finite ∧
    (∀ p ∈ meetBox L W,
      p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i : Fin 3, p.2 i ∈ Set.Ioo (0 : ℝ) 1) ∧
    (∀ p ∈ meetBox L W,
      LinearMap.range (mfderiv 𝓘(ℝ, ℝ) (𝓡 4) L p.1).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) W p.2).toLinearMap = ⊤)

/-- **The at-`t` input bundle of `T6`** (the lead's `NOTES_LEAD_hblock_uniformity.md` §4.3, with the
`cutBaseBox`/`cutFibreBox` conjunct deleted per `NOTES_LEAD_hfib.md`): the core loop of the chart meets
the sweep of `P₁` in general position, at every core meet the diameter loop meets the sweep of `P₂` in
general position, and the cut of `Q` misses a neighbourhood of the plane parameter's origin. -/
def T6GenAt (Q : ℂ → CappingSpace) (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (c₁ c₂ : ℝ) : Prop :=
  GoodLoopChain (coreLoop Q) (clampedSweep c₁ (fun r => 1 - r) P₁) ∧
    (∀ q ∈ coreMeet Q c₁ P₁,
      GoodLoopChain (diamLoop Q q.1) (clampedSweep c₂ (fun r => 1 - r) P₂)) ∧
    (∃ δc : ℝ, 0 < δc ∧ ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc →
      x ∉ diskCut Q (clampedSweep c₂ (fun r => 1 - r) P₂))

end

end Work.Drive

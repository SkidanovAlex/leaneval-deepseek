import Mathlib
import Submission.Work.PinchFamily.Defs
import Submission.Work.PinchFamily.Collar

/-!
# The local moves of the collar family

`Work.PinchFamily.collarRegion` is the three-piece family of Pardon's pinch read through a collar
`Z` of the box region: the region inside the box for `t < 1/2`, the box region with the collar
removed for `1/2 ≤ t < 3/4`, and the two half-regions for `t ≥ 3/4`.  The aim of this file is the
ε-form of its local moves, in the exact shape consumed by `Work.PinchCounted.CountedPinch`:

> at every parameter `t` there is `ε > 0` such that every `r` with `|r - t| < ε` gives a
> `CountedStep` from the region at `t` to the region at `r`.

The content is the two *transitions* of the collar decomposition:

* `countedStep_box_sdiff` — the collar is removed (from the box region to `box \ Z`);
* `countedStep_sdiff_halves` — the collar is pushed into the two half-regions
  (from `box \ Z` to `halves`),

together with the trivial reflexive move `CountedStep A A` (an empty transport of the loop
content).  Only the neighbourhood of the two critical parameters `t = 1/2` and `t = 3/4` needs
care: the ε is chosen so that no parameter is reached whose value would make both critical
transitions necessary — since at `t = 1/2` only `box → box \ Z` (or the reflexive move) can occur,
and at `t = 3/4` only `box \ Z → halves` (or the reflexive move) can occur.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchFamily

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The reflexive local move**: two copies of the same region are related by a `CountedStep`
(the empty transport of the loop content). -/
theorem countedStep_self (β : Work.CoreTopology.ClosedCurve P) (A : Set R3) :
    Work.PinchCounted.CountedStep P β A A :=
  Work.PinchCounted.CountedStep.of_regionEquivalent
    (Work.SurgeryInvariance.RegionEquivalent.refl (P := P) A)

/-- **The local moves of the collar family.**  At every parameter `t` the three-piece family
`collarRegion P s c σ u Z` has an ε-neighbourhood in which every move is a
`Work.PinchCounted.CountedStep`. -/
theorem collarRegion_localMoves {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hZ : Work.PinchFamily.IsPinchCollar P s c σ u Z)
    (hspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥)
    (β : Work.CoreTopology.ClosedCurve P) (t : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, |r - t| < ε →
      Work.PinchCounted.CountedStep P β
        (Work.PinchFamily.collarRegion P s c σ u Z t)
        (Work.PinchFamily.collarRegion P s c σ u Z r) := by
  have hstep1 : Work.PinchCounted.CountedStep P β (box P s c σ) (box P s c σ \ Z) :=
    countedStep_box_sdiff hZ hspan β
  have hstep2 : Work.PinchCounted.CountedStep P β (box P s c σ \ Z) (halves P s c σ u) :=
    countedStep_sdiff_halves hZ hspan β
  by_cases ht1 : t < 1 / 2
  · -- `t < 1/2`: the whole ε-neighbourhood stays in the box region.
    refine ⟨1 / 2 - t, by linarith, fun r hr => ?_⟩
    have hr1 : r < 1 / 2 := by
      have h := (abs_lt.mp hr).2; linarith
    rw [collarRegion_of_lt (P := P) ht1, collarRegion_of_lt (P := P) hr1]
    exact countedStep_self β _
  · by_cases ht2 : t < 3 / 4
    · -- `1/2 ≤ t < 3/4`: the region at `t` is `box \ Z`; nearby regions are `box`, `box \ Z` or
      -- `halves`.
      refine ⟨1 / 4, by norm_num, fun r _hr => ?_⟩
      rw [collarRegion_of_mem (P := P) ht1 ht2]
      by_cases hr1 : r < 1 / 2
      · rw [collarRegion_of_lt (P := P) hr1]; exact hstep1.symm
      · by_cases hr2 : r < 3 / 4
        · rw [collarRegion_of_mem (P := P) hr1 hr2]; exact countedStep_self β _
        · rw [collarRegion_of_le (P := P) hr1 hr2]; exact hstep2
    · -- `3/4 ≤ t`: the region at `t` is `halves`; the ε ensures `r > 1/2`, so nearby regions are
      -- `box \ Z` or `halves`.
      refine ⟨1 / 4, by norm_num, fun r hr => ?_⟩
      have ht3 : 3 / 4 ≤ t := not_lt.mp ht2
      have hr1' : 1 / 2 ≤ r := by
        have h := (abs_lt.mp hr).1; linarith
      have hr1 : ¬ r < 1 / 2 := not_lt.mpr hr1'
      rw [collarRegion_of_le (P := P) ht1 ht2]
      by_cases hr2 : r < 3 / 4
      · rw [collarRegion_of_mem (P := P) hr1 hr2]; exact hstep2.symm
      · rw [collarRegion_of_le (P := P) hr1 hr2]; exact countedStep_self β _

end

end Work.PinchFamily

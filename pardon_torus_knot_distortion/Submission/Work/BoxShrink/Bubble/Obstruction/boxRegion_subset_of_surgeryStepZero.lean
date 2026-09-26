import Mathlib
import Submission.Work.BoxShrink.Bubble.Basic

namespace Work.BoxShrink.Bubble.Obstruction

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- **The slice cannot show up on the `Z` side of a `SurgeryStepZero`.**

Suppose the region inside the sphere is written as a disjoint union `A' ∪ Z` of two pieces open in
the surface, with both half-regions of the slicing plane contained in `A'`.  Then all of the box
region lies in `A'`: a point of `Z` that is not in one of the half-regions would be in the slice,
and `SliceLocallyTwoSided` produces, inside the open-in-the-surface set `Z`, a point of one of the
half-regions, which lies in `A'` — contradicting disjointness. -/
theorem boxRegion_subset_of_surgeryStepZero
    {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (htwo : Work.BoxShrink.Bubble.SliceLocallyTwoSided P s c σ u)
    {A' Z : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hA' : Work.SurgeryInvariance.IsOpenInCarrier P A')
    (hZ : Work.SurgeryInvariance.IsOpenInCarrier P Z)
    (hcover : Work.BoxShrink.Core.boxRegion P s c σ = A' ∪ Z) (hdisj : Disjoint A' Z)
    (hupper : Work.BoxShrink.Core.upperRegion P s c σ u ⊆ A')
    (hlower : Work.BoxShrink.Core.lowerRegion P s c σ u ⊆ A') :
    Work.BoxShrink.Core.boxRegion P s c σ ⊆ A' := by
  intro y hy
  have hyb : y ∈ Work.BoxShrink.Core.boxRegion P s c σ := hy
  rw [hcover] at hy
  rcases hy with hyA | hyZ
  · exact hyA
  · rw [Work.BoxShrink.Core.boxRegion_eq_union] at hyb
    rcases hyb with (hyu | hyl) | hys
    · exact hupper hyu
    · exact hlower hyl
    · -- `y` is in the slice: local two-sidedness of the surface at `y` spreads `Z` into a
      -- half-region, which lies in `A'`.
      exfalso
      obtain ⟨y', hy'Z, hy'half⟩ := htwo y hys Z hZ hyZ
      have hy'A : y' ∈ A' := hy'half.elim (fun h => hupper h) (fun h => hlower h)
      exact hdisj.le_bot ⟨hy'A, hy'Z⟩

end Work.BoxShrink.Bubble.Obstruction

import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Surface.isCompact_levelSet
import Submission.Work.Smooth.Morse.Surface.isCompact_closedRegion
import Submission.Work.Smooth.Morse.Regular.levelSet_isLocalArc_of_regularValue
import Submission.Work.Smooth.Morse.Critical.ae_regular_of_countable
import Submission.Work.Smooth.Morse.Critical.ae_regular_of_locallyFinite

/-!
# Almost every level of a smooth function on the torus is nice (item 2)

For a `C¹` function `g : ℝ³ → ℝ` and a regular value `t` of `g|_F`, the level set
`F ∩ {g = t}` is compact (closed in the compact surface), locally an arc
(`Submission.Work.Smooth.Morse.Regular.levelSet_isLocalArc_of_regularValue`, from the implicit
function theorem), and the closed sublevel region `F ∩ {g ≤ t}` is compact.  With the
classification of compact `1`-manifolds — carried here as the single isolated input
`CompactOneManifoldInput` because Mathlib does not contain it — the level set is a finite disjoint
union of simple closed curves of the torus, i.e. a `NiceLevel`.

Combining this with the Sard/Morse input `LocallyFiniteCriticalValues` (or merely countability of
the critical values) gives: **almost every level is nice**.

## Main results

* `Work.Smooth.Morse.niceLevel_of_regularValue` — a regular level is nice;
* `Work.Smooth.Morse.ae_niceLevel_of_countable` and
  `Work.Smooth.Morse.ae_niceLevel_of_locallyFinite` — almost every level is nice;
* `Work.Smooth.Morse.NiceLevel.isCompact_closedRegion` (the region is a compact surface with
  boundary the level set), and `Work.Smooth.Morse.niceLevel_circleUnion`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse

noncomputable section

variable {ψ : Submission.Diffeo} {g : R3 → ℝ} {t : ℝ}

/-- **A regular level is nice.**  If `t` is a regular value of `g|_F` then `F ∩ {g = t}` is a
compact finite disjoint union of simple closed curves of the torus and `F ∩ {g ≤ t}` is a compact
surface with boundary the level set. -/
theorem niceLevel_of_regularValue (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : ContDiff ℝ 1 g)
    (hclass : CompactOneManifoldInput ψ) {t : ℝ} (hreg : IsRegularValue ψ g t) :
    NiceLevel ψ g t where
  isCompact_levelSet := Work.Smooth.Morse.Surface.isCompact_levelSet ψ hg.continuous t
  circleUnion := hclass _
    (Work.Smooth.Morse.Surface.isCompact_levelSet ψ hg.continuous t)
    (Work.Smooth.Morse.Regular.levelSet_isLocalArc_of_regularValue ψ hg hreg)
  isCompact_closedRegion := Work.Smooth.Morse.Surface.isCompact_closedRegion ψ hg.continuous t

/-- **Almost every level is nice**, granted the classification of compact `1`-manifolds and that
the critical values of `g|_F` are countable. -/
theorem ae_niceLevel_of_countable (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : ContDiff ℝ 1 g)
    (hclass : CompactOneManifoldInput ψ) (h : (criticalValues ψ g).Countable) :
    ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), NiceLevel ψ g t :=
  (Work.Smooth.Morse.Critical.ae_regular_of_countable ψ g h).mono
    fun t ht => niceLevel_of_regularValue ψ hg hclass ht

/-- **Almost every level is nice**, granted the classification of compact `1`-manifolds and the
Morse/Sard input that the critical values are locally finite. -/
theorem ae_niceLevel_of_locallyFinite (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : ContDiff ℝ 1 g)
    (hclass : CompactOneManifoldInput ψ) (h : LocallyFiniteCriticalValues ψ g) :
    ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), NiceLevel ψ g t :=
  (Work.Smooth.Morse.Critical.ae_regular_of_locallyFinite ψ g h).mono
    fun t ht => niceLevel_of_regularValue ψ hg hclass ht

/-- The level set of a nice level is a finite disjoint union of simple closed curves. -/
theorem NiceLevel.circleUnion' (h : NiceLevel ψ g t) : IsCircleUnion ψ (levelSet ψ g t) :=
  h.circleUnion

/-- The closed region of a nice level is compact, and it is the region together with the level
set (`closedRegion_eq_region_union_levelSet`): this is the statement that the region `F ∩ {g < t}`
is a compact surface with boundary. -/
theorem NiceLevel.isCompact_closedRegion' (h : NiceLevel ψ g t) :
    IsCompact (closedRegion ψ g t) :=
  h.isCompact_closedRegion

end

end Work.Smooth.Morse

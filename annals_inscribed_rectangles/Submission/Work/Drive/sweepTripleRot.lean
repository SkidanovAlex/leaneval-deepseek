import Mathlib
import Submission.Work.Drive.sweepTripleGeneric
import Submission.Work.Drive.sweepTripleSource
import Submission.Work.Drive.contMDiff_rotPresentation
import Submission.Work.Drive.sweepTripleLocus

/-!
# The design's triple: three rotations of one chart

The design's triple of planes (`CHAINPARITY_REDUCTION.md` §4, `tripleMultiplicativity.lean`) is
`P k = rotPresentation Q (u k)` — three rotations of one chart.  This file instantiates the genericity
endpoint `Work.Drive.exists_meet3Hyp_sweepChartFam_of_baseSource` at that triple, discharging its two
plane hypotheses:

* `hP` (smoothness of the rotated presentation) — `Work.Drive.contMDiff_rotPresentation` applied to
  `Work.Drive.contMDiff_diskPlane` of the chart;
* `hPseam` (seam invariance) — `Work.Drive.diskPlane_seamInv2` for the rotated chart, whose seam clause
  is the chart's own seam clause composed with the fixed rotation.
-/

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **Seam invariance of a rotated plane presentation.** -/
lemma rotPresentation_seamInv (Q : ℂ → CappingSpace)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) (w : UnitAddCircle)
    (y : EuclideanSpace ℝ (Fin 2)) (hy : onSeam2 y) :
    rotPresentation Q w y = rotPresentation Q w (seamInv2 y) :=
  (diskPlane_seamInv2 (Q := fun z => rotCapping w (Q z))
    (fun z hz => congrArg (rotCapping w) (hQseam z hz)) hy).symm

/-- **The design's rotated triple satisfies `Meet3Hyp` at arbitrarily small parameters.**

The plane data are discharged from the chart's data (`IsChartData Q`), so the hypothesis list is: the
`ChartPert` instance, pairwise distinct truncation levels, the three angles `a k`, and the two design
data (`hsrcK`: the base values on `K` lie in one chart; `hbase`: the base triple locus lies in the
interior of `K`). -/
theorem exists_meet3Hyp_sweepRotFam {Q : ℂ → CappingSpace} (hQ : IsChartData Q)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (hΞ : ChartPert Q 4 Ξ)
    (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k') (a : Fin 3 → UnitAddCircle)
    (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) (p : CappingSpace)
    (hsrcK : ∀ y ∈ K, ∀ k : Fin 3,
      sweepChartFam (fun j => rotPresentation Q (a j)) Ξ c 0 k
        (Work.Drive.TParity.bPartC k y) ∈ (chr p).source)
    (hbase : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      Work.Drive.TParity.meet3 (sweepChartFam (fun j => rotPresentation Q (a j)) Ξ c 0) y →
      y ∈ interior K) :
    ∀ ε' : ℝ, 0 < ε' →
      ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
        Meet3Hyp CappingSpace (sweepChartFam (fun j => rotPresentation Q (a j)) Ξ c t) := by
  refine exists_meet3Hyp_sweepChartFam_of_baseSource
    (fun j => rotPresentation Q (a j)) Ξ c hΞ hc hcdist ?_ ?_ K hK p hsrcK hbase
  · intro k
    exact contMDiff_rotPresentation Q (a k) (contMDiff_diskPlane (Q := Q) hQ.1)
  · intro k y hy
    exact rotPresentation_seamInv Q hQ.2 (a k) y hy

/-- **The design's rotated triple, with the chart containment taken at the base triple locus only.**

This is `Work.Drive.exists_meet3Hyp_sweepChartFam_of_locus` at the design's triple
`P k = rotPresentation Q (a k)`, with the two plane hypotheses discharged from the chart's
`IsChartData`.  The only geometric datum left is `hloc`: at the base triple locus the three values lie
in the source of one chart. -/
theorem exists_meet3Hyp_sweepRotFam_of_locus {Q : ℂ → CappingSpace} (hQ : IsChartData Q)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (hΞ : ChartPert Q 4 Ξ)
    (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k') (a : Fin 3 → UnitAddCircle)
    (p : CappingSpace)
    (hloc : ∀ y ∈ Submission.Drive.unitBox 8,
      Work.Drive.TParity.meet3 (sweepChartFam (fun j => rotPresentation Q (a j)) Ξ c 0) y →
      ∀ k : Fin 3,
        sweepChartFam (fun j => rotPresentation Q (a j)) Ξ c 0 k
          (Work.Drive.TParity.bPartC k y) ∈ (chr p).source) :
    ∀ ε' : ℝ, 0 < ε' →
      ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
        Meet3Hyp CappingSpace (sweepChartFam (fun j => rotPresentation Q (a j)) Ξ c t) := by
  refine exists_meet3Hyp_sweepChartFam_of_locus
    (fun j => rotPresentation Q (a j)) Ξ c hΞ hc hcdist ?_ ?_ p hloc
  · intro k
    exact contMDiff_rotPresentation Q (a k) (contMDiff_diskPlane (Q := Q) hQ.1)
  · intro k y hy
    exact rotPresentation_seamInv Q hQ.2 (a k) y hy

end

end Work.Drive

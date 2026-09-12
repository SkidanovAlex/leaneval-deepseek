import Mathlib
import Submission.Work.Lattice.FlowDataBound
import Submission.GeometryOfNumbers.ImageLatticeCovolume
import Submission.Work.Lattice.IntrinsicIndex

/-!
# (G) along a unimodular linear flow

`Submission.FlowDataBound.rankData_le_of_unimodular` bounds the rank-`j` Grayson data of a
full-rank lattice by `(j/d)·log (2^{2d}/vol(B_d))` whenever the lattice is unimodular.  Here we
instantiate it for the lattices of the §3 route, which are images of `ℤᵈ` under a linear
automorphism of determinant `±1` (the exponential two-scale flow `a_t`, with `det a_t = 1`,
composed with the frozen shearing `s_x`).

Module `Submission.Work.Lattice.FlowDataBoundImage`, namespace `Submission.FlowDataBound`.
-/

noncomputable section

open Set Module Real MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Submission.FlowDataBound

open Submission.GraysonData
open Submission.LatticePolygon

/-- The uniform rank-data bound at the lattices `h(ℤᵈ)` of the §3 route (`|det h| = 1`). -/
theorem rankData_imageSpan_le {d j : ℕ} (hd : 1 ≤ d) (h : E d ≃ₗ[ℝ] E d)
    (hdet : |LinearMap.det (h : E d →ₗ[ℝ] E d)| = 1)
    (hj1 : 1 ≤ j) (hjd : j ≤ d) :
    rankData (Submission.ImageLattice.imageSpan h) j ≤ ((j : ℝ) / (d : ℝ)) *
      Real.log ((2 : ℝ) ^ (2 * d) / ENNReal.toReal (volume (Metric.closedBall (0 : E d) 1))) := by
  haveI : DiscreteTopology (Submission.ImageLattice.imageSpan h) := inferInstance
  haveI : IsZLattice ℝ (Submission.ImageLattice.imageSpan h) := inferInstance
  refine rankData_le_of_unimodular (d := d) hd _ ?_ ?_ hj1 hjd
  · exact Submission.IntrinsicIndex.finrank_zLattice (Λ := Submission.ImageLattice.imageSpan h)
  · rw [Submission.ImageLattice.covol_imageSpan]
    exact hdet

end Submission.FlowDataBound

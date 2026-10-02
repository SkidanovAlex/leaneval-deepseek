import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.localHomology_corner
import Submission.Work.Orient.Boundary.HalfRestrictIso
import Submission.Work.Orient.Boundary.isZero_punctured_halfBall_of_model
import Submission.Work.Cohomology.excision

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The chart transfer for the boundary-point half-ball vanishing

`Work.Orient.Boundary.isZero_halfBallInteriorUnionPoint_of_model`: if the flat model statement
(with the puncture at the image of the boundary point `y`, the centre of the coordinate half-ball)
holds, then

`H_n(W ∖ {y}, (W ∖ {y}) ∖ (K ∩ W°)) = 0`

in the space `W`, where `K = halfBallPiece (n+1) W y r`.

The proof is the chart transfer, exactly as in `Work.Orient.Boundary.isZero_punctured_halfBall_of_model`
(closed-set excision in `W`, the chart homeomorphism of pairs, closed-set excision in the
half-space), with the puncture moved from an interior point to the boundary point `y` itself; the
only difference is that the chart is centred at the puncture, so no interiority hypothesis is
needed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold Topology

namespace Work.Orient.Boundary

noncomputable section

/-- **The chart transfer.**  For a coordinate half-ball `K = halfBallPiece (n+1) W y r` at the
boundary point `y`, the vanishing of the flat model (with the puncture at the image of `y` and the
excluded set the complement of the half-ball) implies the vanishing of
`H_n(W∖{y}, (W∖{y})∖(K ∩ W°))`. -/
theorem isZero_halfBallInteriorUnionPoint_of_model (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) W y r)
    (hmodel : CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains
      (TopCat.of {v : EuclideanHalfSpace (n + 1) | v ≠ (chartAt (EuclideanHalfSpace (n + 1)) y) y})
      {v : {v : EuclideanHalfSpace (n + 1) | v ≠ (chartAt (EuclideanHalfSpace (n + 1)) y) y} |
        (v : EuclideanHalfSpace (n + 1)) ∉
          (Work.Orient.halfIncl (n + 1) ⁻¹' Metric.closedBall
              (Work.Orient.halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) y) y)) (r / 2)
            ∩ {v : EuclideanHalfSpace (n + 1) | 0 < v.1 0})}).homology n)) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains (TopCat.of {z : W | z ≠ y})
      {z : {z : W | z ≠ y} | (z : W) ∉ (Work.Orient.halfBallPiece (n + 1) W y r ∩
        {z : W | z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W})}).homology n) := by
  classical
  let e := chartAt (EuclideanHalfSpace (n + 1)) y
  have hysrc : y ∈ e.source := mem_chart_source (EuclideanHalfSpace (n + 1)) y
  have hKclosed : IsClosed (Work.Orient.halfBallPiece (n + 1) W y r) :=
    (Work.Orient.IsCoordHalfBall.isCompact (n := n + 1) ⟨y, r, hr, hgood, rfl⟩).isClosed
  have hKsrc : Work.Orient.halfBallPiece (n + 1) W y r ⊆ e.source := fun w hw => hw.2
  let K0 : Set (EuclideanHalfSpace (n + 1)) :=
    Work.Orient.halfIncl (n + 1) ⁻¹'
      Metric.closedBall (Work.Orient.halfIncl (n + 1) (e y)) (r / 2)
  let D : Set (EuclideanHalfSpace (n + 1)) :=
    K0 ∩ {v : EuclideanHalfSpace (n + 1) | 0 < v.1 0}
  have hK0target : K0 ⊆ e.target :=
    fun v hv => hgood (Metric.closedBall_subset_ball (by linarith) hv)
  have hDK0 : D ⊆ K0 := fun v hv => hv.1
  have hK0closed : IsClosed K0 :=
    (Metric.isClosed_closedBall (x := Work.Orient.halfIncl (n + 1) (e y)) (ε := r / 2)).preimage
      continuous_subtype_val
  have hcorr : ∀ w : W, w ∈ e.source →
      ((w ∈ Work.Orient.halfBallPiece (n + 1) W y r ∩
        {z : W | z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W}) ↔
      e w ∈ D) := by
    refine fun w hw => ?_
    have h1 : w ∈ Work.Orient.halfBallPiece (n + 1) W y r ↔ e w ∈ K0 :=
      ⟨fun h => h.1, fun h => ⟨h, hw⟩⟩
    have h2 : w ∈ ({z : W | z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W}) ↔
        0 < (e w).1 0 :=
      ⟨fun h => chartAt_interior_pos hw h, fun h => not_mem_boundary_of_chartAt_pos hw h⟩
    exact h1.and h2
  -- ### Step 1: excise `W∖{y}` down to the chart source
  let X : TopCat := TopCat.of {z : W | z ≠ y}
  let A : Set X := {z : X | (z : W) ∉ (Work.Orient.halfBallPiece (n + 1) W y r ∩
        {z : W | z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W})}
  let Z : Set X := {z : X | (z : W) ∉ e.source}
  have hZclosed : IsClosed Z := by
    have heq : Z = (fun z : X => (z : W)) ⁻¹' (e.source)ᶜ := by ext z; exact Iff.rfl
    rw [heq]
    exact e.open_source.isClosed_compl.preimage continuous_subtype_val
  have hsub : closure Z ⊆ interior A := by
    intro z hz
    rw [hZclosed.closure_eq] at hz
    have hzW : (z : W) ∉ e.source := hz
    have hzK : (z : W) ∉ Work.Orient.halfBallPiece (n + 1) W y r := fun h => hzW (hKsrc h)
    have hnbhd : ({z' : X | (z' : W) ∉ Work.Orient.halfBallPiece (n + 1) W y r} ∈ 𝓝 z) :=
      (hKclosed.isOpen_compl.preimage continuous_subtype_val).mem_nhds hzK
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset hnbhd (fun z' hz' h => hz' h.1))
  obtain ⟨e0⟩ := Work.Cohomology.excision X A Z hsub n
  -- ### The model side
  let XH : TopCat := TopCat.of {v : EuclideanHalfSpace (n + 1) | v ≠ e y}
  let AH : Set XH := {v : XH | (v : EuclideanHalfSpace (n + 1)) ∉ D}
  let ZH : Set XH := {v : XH | (v : EuclideanHalfSpace (n + 1)) ∉ e.target}
  have hmod : IsZero ((Work.Cohomology.relChains XH AH).homology n) := hmodel
  have hZHclosed : IsClosed ZH := by
    have heq : ZH = (fun v : XH => (v : EuclideanHalfSpace (n + 1))) ⁻¹' (e.target)ᶜ := by
      ext v; exact Iff.rfl
    rw [heq]
    exact e.open_target.isClosed_compl.preimage continuous_subtype_val
  have hsubH : closure ZH ⊆ interior AH := by
    intro v hv
    rw [hZHclosed.closure_eq] at hv
    have hvK0 : (v : EuclideanHalfSpace (n + 1)) ∉ K0 := fun h => hv (hK0target h)
    have hnbhd : ({v' : XH | (v' : EuclideanHalfSpace (n + 1)) ∉ K0} ∈ 𝓝 v) :=
      (hK0closed.preimage continuous_subtype_val).isOpen_compl.mem_nhds hvK0
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset hnbhd (fun v' hv' h => hv' (hDK0 h)))
  obtain ⟨e2⟩ := Work.Cohomology.excision XH AH ZH hsubH n
  -- ### The chart homeomorphism between the two chart sources
  let U1 : Type := {z : X | z ∉ Z}
  let A1 : Set U1 := {z : U1 | (z : X) ∈ A}
  let U2 : Type := {v : XH | v ∉ ZH}
  let A2 : Set U2 := {v : U2 | (v : XH) ∈ AH}
  have hnn : ∀ {p : Prop}, ¬¬p → p := fun h => Classical.byContradiction h
  let φ : U1 ≃ₜ U2 :=
    { toFun := fun z =>
        ⟨⟨e (((z : U1) : X) : W), fun heq =>
            ((z : U1) : X).2 (e.injOn (hnn z.2) hysrc heq)⟩,
          fun h => h (e.map_source (hnn z.2))⟩
      invFun := fun v =>
        ⟨⟨e.symm (((v : U2) : XH) : EuclideanHalfSpace (n + 1)), fun heq =>
            ((v : U2) : XH).2 (by
              have hv : (((v : U2) : XH) : EuclideanHalfSpace (n + 1)) ∈ e.target := hnn v.2
              rw [← e.right_inv hv, heq])⟩,
          fun h => h (e.map_target (hnn v.2))⟩
      left_inv := fun z => by
        apply Subtype.ext
        apply Subtype.ext
        exact e.left_inv (hnn z.2)
      right_inv := fun v => by
        apply Subtype.ext
        apply Subtype.ext
        exact e.right_inv (hnn v.2)
      continuous_toFun := Continuous.subtype_mk (Continuous.subtype_mk
        (e.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
          (fun z => hnn z.2)) _) _
      continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk
        (e.symm.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
          (fun v => hnn v.2)) _) _ }
  have hA1 : ∀ z : U1, z ∈ A1 ↔ φ z ∈ A2 := by
    intro z
    have hw : (((z : U1) : X) : W) ∈ e.source := hnn z.2
    show (((z : U1) : X) : W) ∉ (Work.Orient.halfBallPiece (n + 1) W y r ∩
        {z : W | z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W}) ↔
      e (((z : U1) : X) : W) ∈ D → False
    exact not_congr (hcorr (((z : U1) : X) : W) hw)
  obtain ⟨e1⟩ := homeoRelChainsIso φ A1 A2 hA1 n
  exact IsZero.of_iso (IsZero.of_iso (IsZero.of_iso hmod e2.symm) e1) e0

end

end Work.Orient.Boundary

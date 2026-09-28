import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.RatHurewicz.AttachPush.CellInterior
import Submission.Work.AttachPush.isClosed_cellMap_image_closedBall

/-!
# The image of a sphere of radius `< 1` in an attached cell is closed

Companion to `Work.AttachPush.isClosed_cellMap_image_closedBall`: the image under the characteristic
map `cellMap n Y ι f i` of the model sphere `{y : D^{n+2} | ‖y‖ = ρ}` with `ρ < 1` is a closed
subset of `attachCells n Y ι f`.

The argument is verbatim the one of the closed-ball case: since `ρ < 1` the model sphere lies in the
open model cell, where classes in the gluing relation are singletons, so the saturated preimage of
the image is exactly the part of the `i`-th summand over that sphere; that part is closed (the
sphere is closed in the model cell), and the quotient map is coinducing.
-/

open scoped Topology

namespace Work.Serre.DiscPair

theorem isClosed_cellMap_sphere (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) {ρ : ℝ} (hρ : ρ < 1) :
    IsClosed (Work.RatHurewicz.cellMap n Y ι f i ''
      {y : Work.RatHurewicz.cellDisk n | ‖(y : Work.RatHurewicz.CellVec n)‖ = ρ}) := by
  classical
  set U : Set (Work.RatHurewicz.cellDisk n) :=
    {y | ‖(y : Work.RatHurewicz.CellVec n)‖ = ρ} with hUdef
  have hUsub : U ⊆ Work.RatHurewicz.cellInner n := fun y hy => by
    show ‖(y : Work.RatHurewicz.CellVec n)‖ < 1
    have hy' : ‖(y : Work.RatHurewicz.CellVec n)‖ = ρ := hy
    rw [hy']
    exact hρ
  have hUcl : IsClosed U := by
    have h : U = Subtype.val ⁻¹' Metric.sphere (0 : Work.RatHurewicz.CellVec n) ρ := by
      ext y
      simp only [Set.mem_preimage, Metric.mem_sphere, dist_eq_norm, sub_zero, hUdef,
        Set.mem_ofPred_eq]
    rw [h]
    exact Metric.isClosed_sphere.preimage continuous_subtype_val
  have hpre := Work.RatHurewicz.preimage_cellMap_image (n := n) (Y := Y) (ι := ι) (f := f)
    (i := i) (U := U) hUsub
  have hScl : IsClosed (Work.RatHurewicz.sigmaOver (Y := Y) (ι := ι) i U) :=
    Work.AttachPush.isClosed_sigmaOver hUcl
  refine ((isQuotientMap_quotient_mk'
    (X := Y ⊕ (Σ _ : ι, Work.RatHurewicz.cellDisk n))
    (s := Relation.EqvGen.setoid (Work.RatHurewicz.attachRel n Y ι f))).isCoinducing.isClosed_preimage
    (s := {z : Work.RatHurewicz.attachCells n Y ι f |
      ∃ x ∈ U, Work.RatHurewicz.cellMap n Y ι f i x = z})).mp ?_
  rw [hpre]
  exact hScl

end Work.Serre.DiscPair

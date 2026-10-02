import Mathlib
import Submission.Work.Serre.serreC0KillShellHomology
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.AttachPush.CellInterior

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The image of the sphere of radius `1/4` in an attached cell is a sphere

For a space `Y` with `(n+2)`-cells attached along `f : ι → C(S^{n+1}, Y)`, the characteristic map
`cellMap i` of the `i`-th cell is a homeomorphism from the open model cell `D^{n+2}` onto the open
cell interior of the attachment (`Work.Serre.ks_cellImgHomeo`).  Consequently, the image of *any*
subset of the open model cell is homeomorphic to that subset.  The one used by the Thom cylinder
comparison `thomCylAt_sphereInCell` is the sphere of radius `1/4`: its image is homeomorphic to the
model sphere `S^{n+1} = Work.RatHurewicz.cellSphere n`.

The two pieces are

* `↥(cellImg f i (quarterSet n)) ≃ₜ ↥(quarterSet n)` — the restriction of the characteristic map
  (`ks_cellImgHomeo`);
* `↥(quarterSet n) ≃ₜ cellSphere n` — scaling by `4`, a continuous bijection from a compact space
  onto a Hausdorff space, hence a homeomorphism (`quarterEquiv` and
  `Continuous.homeoOfEquivCompactToT2`).
-/

set_option linter.style.haveILetI false

namespace Work.Serre

noncomputable section

open scoped Topology

/-- The sphere of radius `1/4` inside the model cell `D^{n+2}`. -/
abbrev quarterSet (n : ℕ) : Set (Work.RatHurewicz.cellDisk n) :=
  {y | ‖(y : Work.RatHurewicz.CellVec n)‖ = 1/4}

/-- Scaling by `4` maps the radius-`1/4` sphere inside the model cell onto the unit sphere
`S^{n+1} = cellSphere n`. -/
def quarterToSphere (n : ℕ) (x : ↥(quarterSet n)) : Work.RatHurewicz.cellSphere n :=
  ⟨(4 : ℝ) • (x : Work.RatHurewicz.CellVec n), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, x.2]
    norm_num⟩

/-- Scaling by `1/4` maps the unit sphere into the radius-`1/4` sphere inside the model cell; this
is the inverse of `quarterToSphere`. -/
def sphereToQuarter (n : ℕ) (z : Work.RatHurewicz.cellSphere n) : ↥(quarterSet n) :=
  ⟨⟨(1 / 4 : ℝ) • (z : Work.RatHurewicz.CellVec n), by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul]
      have hz : ‖(z : Work.RatHurewicz.CellVec n)‖ = 1 := by
        have h := Metric.mem_sphere.mp z.2
        rwa [dist_eq_norm, sub_zero] at h
      rw [hz]; norm_num⟩, by
    show ‖(1 / 4 : ℝ) • (z : Work.RatHurewicz.CellVec n)‖ = 1 / 4
    rw [norm_smul]
    have hz : ‖(z : Work.RatHurewicz.CellVec n)‖ = 1 := by
      have h := Metric.mem_sphere.mp z.2
      rwa [dist_eq_norm, sub_zero] at h
    rw [hz]; norm_num⟩

/-- The scaling equivalence between the radius-`1/4` sphere in the model cell and the unit
sphere. -/
def quarterEquiv (n : ℕ) : ↥(quarterSet n) ≃ Work.RatHurewicz.cellSphere n where
  toFun := quarterToSphere n
  invFun := sphereToQuarter n
  left_inv := by
    intro x
    apply Subtype.ext; apply Subtype.ext
    show (1 / 4 : ℝ) • ((4 : ℝ) • (x : Work.RatHurewicz.CellVec n)) =
      (x : Work.RatHurewicz.CellVec n)
    rw [smul_smul]; norm_num
  right_inv := by
    intro z
    apply Subtype.ext
    show (4 : ℝ) • ((1 / 4 : ℝ) • (z : Work.RatHurewicz.CellVec n)) =
      (z : Work.RatHurewicz.CellVec n)
    rw [smul_smul]; norm_num

theorem quarterToSphere_continuous (n : ℕ) : Continuous (quarterToSphere n) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_subtype_val).const_smul (4 : ℝ)

/-- **The radius-`1/4` sphere in the model cell is homeomorphic to the model sphere.** -/
theorem quarterSphereHomeo (n : ℕ) :
    Nonempty (↥(quarterSet n) ≃ₜ Work.RatHurewicz.cellSphere n) := by
  haveI : CompactSpace ↥(quarterSet n) := by
    rw [← isCompact_iff_compactSpace]
    exact (isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const).isCompact
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := quarterEquiv n) ?_⟩
  exact quarterToSphere_continuous n

theorem cellImgQuarterSphereHomeo (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    Nonempty (↥(Work.Serre.cellImg (f := f) i
        {y : Work.RatHurewicz.cellDisk n | ‖(y : Work.RatHurewicz.CellVec n)‖ = 1/4}) ≃ₜ
      Work.RatHurewicz.cellSphere n) := by
  have hS : quarterSet n ⊆ Work.RatHurewicz.cellInner n := by
    intro y hy
    rw [Work.RatHurewicz.cellInner]
    show ‖(y : Work.RatHurewicz.CellVec n)‖ < 1
    rw [hy]; norm_num
  obtain ⟨e₁⟩ := ks_cellImgHomeo f i (quarterSet n) hS
  obtain ⟨e₂⟩ := quarterSphereHomeo n
  exact ⟨e₁.symm.trans e₂⟩

end

end Work.Serre

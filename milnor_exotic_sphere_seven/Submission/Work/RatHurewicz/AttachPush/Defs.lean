import Mathlib
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.DiskPairDefs
import Submission.Work.RatHurewicz.attachIncl_isOpenMap_range
import Submission.Work.RatHurewicz.ExcisionSetup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Pushing a cube off the attached cells: vocabulary

This directory proves `Work.RatHurewicz.compressRel_attachCells_range`: attaching `(n+2)`-cells does
not change the homotopy groups in degrees `≤ n`, in compression form.

The route (Hatcher, Lemma 4.10 and Corollary 4.12) is:

1. *general position*: a map of a `d`-cube (`d ≤ n+1 < n+2`) into `attachCells n Y ι f` can be
   homotoped, relative to the boundary, into a map whose image misses the *centre* of every
   attached cell — the cell is a convex disc of dimension `n+2`, and a smooth perturbation of the
   lift of the map to the cell misses the centre by Sard (the dimension count `d < n+2`);
2. *push-off*: because the radial retraction of a punctured cell onto its boundary sphere fixes
   the sphere pointwise, it descends to `attachCells n Y ι f`, and a map missing every centre can
   be homotoped into the range of `attachIncl`.

This module fixes the vocabulary of both steps: the open model cell `cellInner`, the centre
`cellOrigin` of an attached cell, its interior `cellInterior`, the set `cellCentres` of all centres,
and the radial push `cellPush` of the punctured model cell, with its elementary properties.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphere n, Y))

/-- The **open model cell** `D^{n+2} ∖ S^{n+1}`: the points of the closed model cell of norm `< 1`. -/
def cellInner : Set (cellDisk n) := {x | ‖(x : CellVec n)‖ < 1}

/-- The **centre** of the model cell, as a point of `cellDisk n`. -/
def cellDiskCentre : cellDisk n := ⟨0, by simp [Metric.mem_closedBall]⟩

@[simp] theorem cellDiskCentre_coe : ((cellDiskCentre n : cellDisk n) : CellVec n) = 0 := rfl

/-- **The centre of the `i`-th attached cell**, `cellMap i 0`, in `attachCells n Y ι f`. -/
def cellOrigin (i : ι) : attachCells n Y ι f := cellMap n Y ι f i (cellDiskCentre n)

/-- **The interior of the `i`-th attached cell**: the image of the open model cell under the
characteristic map. -/
def cellInterior (i : ι) : Set (attachCells n Y ι f) := cellMap n Y ι f i '' cellInner n

/-- The set of all cell centres. -/
def cellCentres : Set (attachCells n Y ι f) := Set.range (cellOrigin n Y ι f)

/-- The centre lies in the interior of its cell. -/
theorem cellOrigin_mem_cellInterior (i : ι) : cellOrigin n Y ι f i ∈ cellInterior n Y ι f i :=
  ⟨cellDiskCentre n, by simp [cellInner, cellDiskCentre], rfl⟩

/-! ### The boundary sphere inside the model cell -/

theorem cellSphereToDisk_coe (n : ℕ) (z : cellSphere n) :
    ((cellSphereToDisk n z : cellDisk n) : CellVec n) = (z : CellVec n) := rfl

theorem norm_cellSphereToDisk (n : ℕ) (z : cellSphere n) :
    ‖((cellSphereToDisk n z : cellDisk n) : CellVec n)‖ = 1 := by
  rw [cellSphereToDisk_coe]
  simpa [dist_eq_norm] using Metric.mem_sphere.mp z.2

theorem cellSphereToDisk_ne_zero (n : ℕ) (z : cellSphere n) :
    ((cellSphereToDisk n z : cellDisk n) : CellVec n) ≠ 0 := by
  intro h
  have h1 := norm_cellSphereToDisk n z
  rw [h, norm_zero] at h1
  exact one_ne_zero h1.symm

/-- The boundary point of the model cell as an element of the punctured cell. -/
def cellSpherePt (n : ℕ) (z : cellSphere n) : ↥(puncturedCellDisk n) :=
  ⟨cellSphereToDisk n z, by
    show ((cellSphereToDisk n z : cellDisk n) : CellVec n) ≠ 0
    exact cellSphereToDisk_ne_zero n z⟩

@[simp] theorem cellSpherePt_coe (n : ℕ) (z : cellSphere n) :
    ((cellSpherePt n z : ↥(puncturedCellDisk n)) : cellDisk n) = cellSphereToDisk n z := rfl

/-! ### The radial push of the punctured model cell

`cellPush s x = ((1 - s) + s / ‖x‖) • x` for `x ≠ 0`: at `s = 0` it is the identity, at `s = 1`
the radial retraction onto the boundary sphere, and it fixes the boundary sphere pointwise for
every `s`. -/

/-- The **radial push** of the punctured model cell towards its boundary: the straight-line
interpolation between the identity and the radial retraction `x ↦ x / ‖x‖`,
`cellPushVec s x = ((1 - s) + s / ‖x‖) • x`. -/
def cellPushVec (n : ℕ) (s : I) (x : CellVec n) : CellVec n :=
  ((1 - (s : ℝ)) + (s : ℝ) * ‖x‖⁻¹) • x

theorem norm_cellPushVec (n : ℕ) (s : I) {x : CellVec n} (hx : x ≠ 0) :
    ‖cellPushVec n s x‖ = (1 - (s : ℝ)) * ‖x‖ + (s : ℝ) := by
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hcoef : (0 : ℝ) ≤ (1 - (s : ℝ)) + (s : ℝ) * ‖x‖⁻¹ := by
    have h1 : (0 : ℝ) ≤ 1 - (s : ℝ) := by linarith [s.2.2]
    have h2 : (0 : ℝ) ≤ (s : ℝ) * ‖x‖⁻¹ := mul_nonneg s.2.1 (inv_nonneg.mpr (norm_nonneg x))
    linarith
  rw [cellPushVec, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef]
  field_simp

theorem norm_cellPushVec_le_one (n : ℕ) (s : I) {x : CellVec n} (hx0 : x ≠ 0)
    (hx : ‖x‖ ≤ 1) : ‖cellPushVec n s x‖ ≤ 1 := by
  rw [norm_cellPushVec n s hx0]
  have hs : (0 : ℝ) ≤ (s : ℝ) := s.2.1
  nlinarith [s.2.2]

theorem cellPushVec_mem (n : ℕ) (s : I) {x : CellVec n} (hx0 : x ≠ 0) (hx : ‖x‖ ≤ 1) :
    cellPushVec n s x ∈ Metric.closedBall (0 : CellVec n) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_cellPushVec_le_one n s hx0 hx

@[simp] theorem cellPushVec_zero (n : ℕ) (x : CellVec n) : cellPushVec n 0 x = x := by
  simp [cellPushVec]

theorem cellPushVec_sphere (n : ℕ) (s : I) {x : CellVec n} (hx : ‖x‖ = 1) :
    cellPushVec n s x = x := by
  rw [cellPushVec, hx, inv_one, mul_one, show (1 - (s : ℝ)) + (s : ℝ) = 1 by ring, one_smul]

theorem norm_cellPushVec_one (n : ℕ) {x : CellVec n} (hx0 : x ≠ 0) (hx : ‖x‖ ≤ 1) :
    ‖cellPushVec n 1 x‖ = 1 := by
  rw [norm_cellPushVec n 1 hx0]
  norm_num

theorem continuous_cellPushVec (n : ℕ) :
    Continuous fun p : ↥(puncturedCellDisk n) × I =>
      cellPushVec n p.2 ((p.1 : cellDisk n) : CellVec n) := by
  have hval : Continuous fun p : ↥(puncturedCellDisk n) × I => (((p.1 : cellDisk n) : CellVec n)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
  have hcoef : Continuous fun p : ↥(puncturedCellDisk n) × I =>
      (1 - (p.2 : ℝ)) + (p.2 : ℝ) * ‖(((p.1 : cellDisk n) : CellVec n))‖⁻¹ := by
    refine Continuous.add ?_ ?_
    · exact continuous_const.sub (continuous_subtype_val.comp continuous_snd)
    · exact (continuous_subtype_val.comp continuous_snd).mul
        ((hval.norm).inv₀ (fun p => norm_ne_zero_iff.mpr p.1.2))
  exact hcoef.smul hval

/-- The **radial push** of the punctured model cell `D^{n+2} ∖ {0}` into the model cell, as a
bundled continuous map. -/
def cellPush (n : ℕ) : C(↥(puncturedCellDisk n) × I, cellDisk n) where
  toFun p := ⟨cellPushVec n p.2 ((p.1 : cellDisk n) : CellVec n),
    by
      have hx0 : ((p.1 : cellDisk n) : CellVec n) ≠ 0 := p.1.2
      have hx : ‖((p.1 : cellDisk n) : CellVec n)‖ ≤ 1 := by
        have h := Metric.mem_closedBall.mp (p.1 : cellDisk n).2
        simpa [dist_eq_norm] using h
      exact cellPushVec_mem n p.2 hx0 hx⟩
  continuous_toFun := Continuous.subtype_mk (continuous_cellPushVec n)
    (fun p => by
      have hx0 : ((p.1 : cellDisk n) : CellVec n) ≠ 0 := p.1.2
      have hx : ‖((p.1 : cellDisk n) : CellVec n)‖ ≤ 1 := by
        have h := Metric.mem_closedBall.mp (p.1 : cellDisk n).2
        simpa [dist_eq_norm] using h
      exact cellPushVec_mem n p.2 hx0 hx)

@[simp] theorem cellPush_apply (n : ℕ) (p : ↥(puncturedCellDisk n) × I) :
    ((cellPush n p : cellDisk n) : CellVec n) = cellPushVec n p.2 ((p.1 : cellDisk n) : CellVec n) :=
  rfl

theorem cellPush_zero (n : ℕ) (x : ↥(puncturedCellDisk n)) :
    cellPush n (x, 0) = (x : cellDisk n) := by
  refine Subtype.ext ?_
  rw [cellPush_apply]
  exact cellPushVec_zero n ((x : cellDisk n) : CellVec n)

/-- The radial push fixes the boundary sphere pointwise. -/
theorem cellPush_sphere (n : ℕ) (z : cellSphere n) (s : I) :
    cellPush n (cellSpherePt n z, s) = cellSphereToDisk n z := by
  refine Subtype.ext ?_
  rw [cellPush_apply]
  exact cellPushVec_sphere n s (norm_cellSphereToDisk n z)

theorem cellPush_one_mem_sphere (n : ℕ) (x : ↥(puncturedCellDisk n)) :
    ((cellPush n (x, 1) : cellDisk n) : CellVec n) ∈ Metric.sphere (0 : CellVec n) 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  have hx0 : ((x : cellDisk n) : CellVec n) ≠ 0 := x.2
  have hx : ‖((x : cellDisk n) : CellVec n)‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp (x : cellDisk n).2
    simpa [dist_eq_norm] using h
  rw [cellPush_apply]
  exact norm_cellPushVec_one n hx0 hx

end

end Work.RatHurewicz

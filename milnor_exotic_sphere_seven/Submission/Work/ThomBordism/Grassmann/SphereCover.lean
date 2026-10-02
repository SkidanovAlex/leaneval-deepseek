import Mathlib
import Submission.Work.ThomBordism.Grassmann.IncidenceVector
import Submission.Work.Thom.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# The two-hemisphere cover of the sphere bundle of the tautological bundle

The incidence fibration `(P, w) ↦ w/‖w‖` of the sphere bundle of the tautological bundle over
`G̃r_k(ℝ^{k+m})` sends it onto the unit sphere `S^{k+m-1} ⊆ Amb (k+m)`.  This module sets up the
cover of the zero complement `E = zeroComplement (tautologicalBundle k m)` induced by the two
"hemispheres" of the sphere in the direction of a fixed unit vector `baseVec k m` (the last standard
basis vector):

* `baseVec k m : Amb (k+m)` — the fixed unit vector;
* `heightVec p = ⟪evalVec p, baseVec k m⟫_ℝ` — the height of the vector of the plane at `p`;
* `upSet = {p | -1/2 < heightVec p}`, `downSet = {p | heightVec p < 1/2}` — the two halves, open and
  covering, together with their intersections with `E`.

The remaining geometric input of `sphereBundleReduction` is that each of the two halves is homotopy
equivalent to `OG (k-1) m` and that their intersection is homotopy equivalent to
`S^{k+m-2} × OG (k-1) m` — the local triviality of the incidence fibration, which is where
`Work.ThomBordism.Grassmann.evalVec` and the orthonormal frame `chartFrame` are used.
-/

open scoped Topology
open Work.TangentClasses

namespace Work.ThomBordism.Grassmann

noncomputable section

/-- The fixed unit vector of the ambient space `Amb (k+m)` used to cut the sphere bundle into two
halves: the last standard basis vector. -/
def baseVec (k m : ℕ) : Amb (k+m) :=
  if h : k + m = 0 then 0 else EuclideanSpace.single ⟨k + m - 1, by omega⟩ 1

theorem norm_baseVec {k m : ℕ} (h : k + m ≠ 0) : ‖baseVec k m‖ = 1 := by
  rw [baseVec, dif_neg h, EuclideanSpace.norm_single, norm_one]

/-- The (unnormalised) **height** of the vector of the plane at a point of the total space, in the
direction of `baseVec`. -/
def heightVec (k m : ℕ) (p : (tautologicalBundle k m).TotalSpace) : ℝ :=
  inner ℝ (evalVec p) (baseVec k m)

theorem continuous_heightVec (k m : ℕ) : Continuous (heightVec k m) :=
  continuous_evalVec.inner continuous_const

/-- The zero complement of the tautological bundle: the total space with the zero section
removed. -/
abbrev zeroComp (k m : ℕ) : Set (tautologicalBundle k m).TotalSpace :=
  Work.Thom.zeroComplement (tautologicalBundle k m)

/-- The "upper" half of the sphere bundle: the points whose *unit* plane-vector has height
`> -1/2`.  Written without division, as `0 < 2⟨w, e⟩ + ‖w‖` (for `w = evalVec p`); on the zero
section (`w = 0`, where the sphere bundle does not live) the inequality holds, so that the two
halves always cover. -/
def upSet (k m : ℕ) : Set ↥(zeroComp k m) :=
  {p | 0 < 2 * heightVec k m (p : (tautologicalBundle k m).TotalSpace) +
    ‖evalVec (p : (tautologicalBundle k m).TotalSpace)‖}

/-- The "lower" half of the sphere bundle: the points whose *unit* plane-vector has height
`< 1/2`, written as `0 < ‖w‖ - 2⟨w, e⟩`. -/
def downSet (k m : ℕ) : Set ↥(zeroComp k m) :=
  {p | 0 < ‖evalVec (p : (tautologicalBundle k m).TotalSpace)‖ -
    2 * heightVec k m (p : (tautologicalBundle k m).TotalSpace)}

theorem continuous_heightVec_subtype (k m : ℕ) : Continuous fun p : ↥(zeroComp k m) =>
    heightVec k m (p : (tautologicalBundle k m).TotalSpace) :=
  (continuous_heightVec k m).comp continuous_subtype_val

theorem continuous_upSet_cond (k m : ℕ) : Continuous fun p : ↥(zeroComp k m) =>
    2 * heightVec k m (p : (tautologicalBundle k m).TotalSpace) +
      ‖evalVec (p : (tautologicalBundle k m).TotalSpace)‖ :=
  (continuous_const.mul (continuous_heightVec_subtype k m)).add
    (continuous_evalVec.norm.comp continuous_subtype_val)

theorem continuous_downSet_cond (k m : ℕ) : Continuous fun p : ↥(zeroComp k m) =>
    ‖evalVec (p : (tautologicalBundle k m).TotalSpace)‖ -
      2 * heightVec k m (p : (tautologicalBundle k m).TotalSpace) :=
  (continuous_evalVec.norm.comp continuous_subtype_val).sub
    (continuous_const.mul (continuous_heightVec_subtype k m))

theorem isOpen_upSet (k m : ℕ) : IsOpen (upSet k m) :=
  isOpen_lt continuous_const (continuous_upSet_cond k m)

theorem isOpen_downSet (k m : ℕ) : IsOpen (downSet k m) :=
  isOpen_lt continuous_const (continuous_downSet_cond k m)

/-- The two halves always cover: at least one of `2⟨w,e⟩ + ‖w‖` and `‖w‖ - 2⟨w,e⟩` is positive,
because `|⟨w,e⟩| ≤ ‖w‖`. -/
theorem norm_baseVec_le_one (k m : ℕ) : ‖baseVec k m‖ ≤ 1 := by
  rw [baseVec]
  split
  · simp
  · rw [EuclideanSpace.norm_single, norm_one]

theorem heightVec_le_norm (k m : ℕ) (p : (tautologicalBundle k m).TotalSpace) :
    heightVec k m p ≤ ‖evalVec p‖ := by
  rw [heightVec, real_inner_comm]
  calc inner ℝ (baseVec k m) (evalVec p) ≤ ‖baseVec k m‖ * ‖evalVec p‖ := real_inner_le_norm _ _
    _ ≤ 1 * ‖evalVec p‖ := by
        exact mul_le_mul_of_nonneg_right (norm_baseVec_le_one k m) (norm_nonneg _)
    _ = ‖evalVec p‖ := one_mul _

theorem upSet_union_downSet (k m : ℕ) : upSet k m ∪ downSet k m = Set.univ := by
  ext p
  simp only [upSet, downSet, Set.mem_setOf_eq, Set.mem_union, Set.mem_univ, iff_true]
  rw [or_iff_not_imp_left]
  intro h
  by_contra hd
  push_neg at h hd
  have hw : (0 : ℝ) < ‖evalVec (p : (tautologicalBundle k m).TotalSpace)‖ :=
    norm_pos_iff.mpr (evalVec_ne_zero_of_mem_zeroComplement _ p.2)
  linarith

/-- The intersection of the two halves: the "equatorial band" of the sphere bundle. -/
def bandSet (k m : ℕ) : Set ↥(zeroComp k m) := upSet k m ∩ downSet k m

theorem bandSet_eq (k m : ℕ) :
    bandSet k m = {p : ↥(zeroComp k m) |
      0 < 2 * heightVec k m (p : (tautologicalBundle k m).TotalSpace) +
        ‖evalVec (p : (tautologicalBundle k m).TotalSpace)‖ ∧
      0 < ‖evalVec (p : (tautologicalBundle k m).TotalSpace)‖ -
        2 * heightVec k m (p : (tautologicalBundle k m).TotalSpace)} := by
  ext p
  rfl

end

end Work.ThomBordism.Grassmann

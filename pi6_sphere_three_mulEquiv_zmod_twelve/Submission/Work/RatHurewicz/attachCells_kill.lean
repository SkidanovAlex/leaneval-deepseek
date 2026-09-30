import Mathlib
import Submission.Work.RatHurewicz.AttachCells

set_option synthInstance.maxHeartbeats 400000

/-!
# The attached classes die

`attachCells n Y ι f` is obtained from `Y` by gluing `(n+2)`-cells along the attaching maps
`f i : S^{n+1} → Y`.  This module proves the complementary half of the construction of the Serre
blueprint's models: for every cell `i`, the composite **`attachIncl ∘ f i : S^{n+1} → attachCells`
is null-homotopic** — the characteristic map `cellMap i` of the cell is an explicit null-homotopy,
obtained by scaling the sphere into the disc: `H (t, z) = cellMap i ((1 - t) • z)`.

Consequently, if the cells are attached along representatives of every element of `π_{n+1}(Y)`
(the Serre blueprint's `Y_{i+1}`), then all of `π_{n+1}(Y)` dies in `π_{n+1}(Y_{i+1})`, which
together with the compression fact `attachCells_relPi_subsingleton` gives `π_{n+1}(Y_{i+1}) = 0`
and `π_j(Y_{i+1}) ≅ π_j(Y)` for `j ≤ n`.
-/

set_option linter.unusedVariables false

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- The point of the model disc `D^{n+2}` obtained from a sphere point `z` by the scaling
`z ↦ (1 - t) • z`; at `t = 0` it is `z` (as a point of the boundary), at `t = 1` it is the centre. -/
def scaleVec (n : ℕ) (t : unitInterval) (z : cellSphere n) : cellDisk n :=
  ⟨((1 : ℝ) - (t : ℝ)) • (z : EuclideanSpace ℝ (Fin (n + 2))), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
    have hz : ‖(z : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 := by
      simpa [dist_eq_norm] using Metric.mem_sphere.mp z.2
    rw [hz, mul_one, abs_of_nonneg (by linarith [t.2.2])]
    linarith [t.2.1]⟩

/-- The scaling `(t, z) ↦ (1 - t) • z` is continuous into the model disc. -/
theorem continuous_scaleVec (n : ℕ) :
    Continuous fun w : unitInterval × cellSphere n => scaleVec n w.1 w.2 := by
  have hf : Continuous fun w : unitInterval × cellSphere n =>
      ((1 : ℝ) - (w.1 : ℝ)) • (w.2 : EuclideanSpace ℝ (Fin (n + 2))) :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd))
  exact Continuous.subtype_mk
    (p := fun x => x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
    hf (fun w => (scaleVec n w.1 w.2).2)

/-- At `t = 0` the scaling is the inclusion of the sphere as the boundary of the disc. -/
theorem scaleVec_zero (n : ℕ) (z : cellSphere n) : scaleVec n 0 z = cellSphereToDisk n z :=
  Subtype.ext (by simp [scaleVec, cellSphereToDisk])

/-- At `t = 1` the scaling is the centre of the disc. -/
theorem scaleVec_one (n : ℕ) (z : cellSphere n) :
    scaleVec n 1 z = (⟨0, by simp [Metric.mem_closedBall]⟩ : cellDisk n) :=
  Subtype.ext (by simp [scaleVec])

/-- **The attaching maps die in the attached space.**  For every cell, the composite of the
attaching map `f i` with the inclusion `Y → attachCells n Y ι f` is null-homotopic: the
characteristic map of the cell, restricted along the scaling of the sphere into the disc, provides
an explicit homotopy to the centre of that cell. -/
theorem attachIncl_comp_nullhomotopic (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (i : ι) :
    ∃ y : attachCells n Y ι f,
      ((attachIncl n Y ι f).comp (f i)).Homotopic (ContinuousMap.const (cellSphere n) y) := by
  refine ⟨cellMap n Y ι f i ⟨0, by simp [Metric.mem_closedBall]⟩, ⟨?_⟩⟩
  refine ⟨⟨(fun w : unitInterval × cellSphere n => cellMap n Y ι f i (scaleVec n w.1 w.2)), ?_⟩,
    ?_, ?_⟩
  · exact (cellMap n Y ι f i).continuous.comp (continuous_scaleVec n)
  · intro z
    show cellMap n Y ι f i (scaleVec n 0 z) = (attachIncl n Y ι f) (f i z)
    rw [scaleVec_zero, attachIncl_attachRel]
  · intro z
    show cellMap n Y ι f i (scaleVec n 1 z) = cellMap n Y ι f i ⟨0, by simp [Metric.mem_closedBall]⟩
    rw [scaleVec_one]

end

end Work.RatHurewicz

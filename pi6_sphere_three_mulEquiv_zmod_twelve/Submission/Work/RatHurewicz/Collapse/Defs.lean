import Mathlib
import Submission.Work.Stems.CollapseDefs
import Submission.Work.Stems.Cubical.CubeFace

set_option synthInstance.maxHeartbeats 400000

/-!
# The corner of the boundary of the cube, as a point of the round sphere

This file collects the vocabulary needed to collapse the cube `I^d` onto the boundary of the
next cube `∂I^{d+1}` *at its corner* (rather than at a face centre).

The construction (used by `Work.RatHurewicz.Collapse.exists_sphereToBdy` and
`Work.RatHurewicz.Collapse.exists_onePointHomeo`) goes through the round sphere
`S^d ⊆ ℝ^{d+1}`:

* `cornerVec d = -(1,…,1)/√(d+1)` is the unit vector pointing from the centre of the cube
  `I^{d+1}` to the corner `(0,…,0)`;
* `cornerPt d` is that vector as a point of the unit sphere;
* `cornerBdy d` is the corner `(0,…,0) ∈ ∂I^{d+1}`, i.e. the point `0` of the cube `I^{d+1}`
  (which is a point of the boundary as soon as `d + 1 ≥ 1`).
-/

open scoped unitInterval Topology

namespace Work.RatHurewicz.Collapse

noncomputable section

open Work.Stems.Cubical

/-- The vector all of whose coordinates are `1`, in `ℝ^{d+1}`. -/
def oneVec (d : ℕ) : EuclideanSpace ℝ (Fin (d + 1)) :=
  (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm (fun _ => 1)

@[simp] theorem oneVec_apply (d : ℕ) (i : Fin (d + 1)) : oneVec d i = 1 := rfl

theorem norm_oneVec (d : ℕ) : ‖oneVec d‖ = Real.sqrt ((d : ℝ) + 1) := by
  have h2 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin (d + 1) => ℝ) (oneVec d)
  have h3 : ∀ i : Fin (d + 1), ‖oneVec d i‖ ^ 2 = (1 : ℝ) := by
    intro i; rw [oneVec_apply]; simp
  rw [Finset.sum_congr rfl (fun i _ => h3 i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h2
  rw [← Real.sqrt_sq (norm_nonneg (oneVec d)), h2]
  congr 1
  push_cast
  ring

/-- The unit vector pointing from the centre of the cube `I^{d+1}` to its corner `(0,…,0)`. -/
def cornerVec (d : ℕ) : EuclideanSpace ℝ (Fin (d + 1)) :=
  -(Real.sqrt ((d : ℝ) + 1))⁻¹ • oneVec d

theorem cornerVec_apply (d : ℕ) (i : Fin (d + 1)) :
    cornerVec d i = -(Real.sqrt ((d : ℝ) + 1))⁻¹ := by
  rw [cornerVec, PiLp.smul_apply, oneVec_apply, smul_eq_mul, mul_one]

theorem norm_cornerVec (d : ℕ) : ‖cornerVec d‖ = 1 := by
  rw [cornerVec, norm_smul, norm_oneVec, Real.norm_eq_abs, abs_neg, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg ((d : ℝ) + 1))]
  rw [inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < (d : ℝ) + 1)))]

theorem cornerVec_ne_zero (d : ℕ) : cornerVec d ≠ 0 := by
  intro h
  have h1 := norm_cornerVec d
  rw [h] at h1
  simp at h1

/-- The corner direction as a point of the unit sphere `S^d ⊆ ℝ^{d+1}`. -/
def cornerPt (d : ℕ) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 :=
  ⟨cornerVec d, mem_sphere_zero_iff_norm.mpr (norm_cornerVec d)⟩

@[simp] theorem cornerPt_coe (d : ℕ) :
    ((cornerPt d : Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) :
      EuclideanSpace ℝ (Fin (d + 1))) = cornerVec d := rfl

/-- The corner `(0,…,0)` of `I^n` lies on the boundary, for `1 ≤ n`. -/
theorem zero_mem_cubeBoundary (n : ℕ) (hn : 1 ≤ n) : (0 : IC n) ∈ Cube.boundary (Fin n) :=
  ⟨⟨0, hn⟩, Or.inl rfl⟩

/-- The corner `(0,…,0)` of the cube `I^{d+1}`, as a point of its boundary. -/
def cornerBdy (d : ℕ) : ↥(Cube.boundary (Fin (d + 1))) :=
  ⟨0, zero_mem_cubeBoundary (d + 1) (by omega)⟩

@[simp] theorem cornerBdy_coe (d : ℕ) :
    ((cornerBdy d : ↥(Cube.boundary (Fin (d + 1)))) : IC (d + 1)) = 0 := rfl

end

end Work.RatHurewicz.Collapse

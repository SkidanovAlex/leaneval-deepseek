import Submission.Work.StemsB.RadialRetraction
import Submission.Work.StemsB.isCompact_coordSup_le_one
import Submission.Work.StemsB.SerreSphereCollar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The radial normalisation of the inner cube onto the cube, and of the collar onto its boundary

For the Serre exact sequence over a sphere, the inner piece `Q = sphLoopBig n = {|v|_∞ < 3/2}` and
its relative part, the **collar** `sphLoopCollar n = {1/2 < |v|_∞ < 3/2}`, have to be compared with
the cube pair `(Iⁿ, ∂Iⁿ)`.  The comparison map is the **radial normalisation**

  `v ↦ v / max (1/2) (|v|_∞)`,

which

* maps the cube `{|v|_∞ ≤ 1}` onto itself, and the *collar* `{1/2 < |v|_∞ < 3/2}` onto the boundary
  `{|v|_∞ = 1}`;
* is homotopic to the identity on the cube and on the inner piece `Q`, through the **radial
  interpolation** `v ↦ ((1-t) + t/max(1/2,|v|_∞)) • v`;
* is *literally* the identity on the boundary.

This file contains the arithmetic and the (Euclidean) continuity of these maps, as well as the
elementary point-set facts about the sets

  `eucBig n = {|v|_∞ < 3/2}`,  `eucCube n = {|v|_∞ ≤ 1}`,  `eucBdry n = {|v|_∞ = 1}`,
  `eucCollar n = {1/2 < |v|_∞ < 3/2}`

in `EuclideanSpace ℝ (Fin n)` — the Euclidean counterparts of `sphLoopBig`, `sphLoopCube`,
`sphLoopBdry`, `sphLoopCollar`.  The transport to the sphere model `SphModel n = OnePoint ℝⁿ` is in
`Submission/Work/StemsB/CollarPair.lean`.

## Main results

* `Work.StemsB.collarNorm`, `Work.StemsB.collarInterp` — the normalisation and the interpolation;
* `Work.StemsB.collarNorm_mem_cube`, `Work.StemsB.collarNorm_mem_bdry_of_mem_collar` — the two
  mapping properties;
* `Work.StemsB.collarInterp_mem_big`, `Work.StemsB.collarInterp_mem_cube`,
  `Work.StemsB.collarInterp_mem_collar` — the homotopies stay in the pieces;
* `Work.StemsB.collarNorm_eq_self_of_mem_bdry` — the normalisation fixes the boundary;
* `Work.StemsB.continuous_collarNorm`, `Work.StemsB.continuous_collarInterp` — continuity.
-/

open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

variable {n : ℕ}

/-! ## The normalisation and the interpolation -/

/-- The **normalisation factor** `(max (1/2) (|v|_∞))⁻¹`; unlike the compression factor
`Work.StemsB.compFactor` it is bounded by `2` and hence continuous everywhere. -/
def collarScale (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (max (1 / 2 : ℝ) (coordSup n v : ℝ))⁻¹

/-- The **radial normalisation** `v ↦ v / max (1/2) (|v|_∞)` of the coordinate sup-norm. -/
def collarNorm (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  collarScale n v • v

/-- The **interpolating factor** `(1-t) + t * collarScale v`. -/
def collarInterpScale (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  (1 - t) + t * collarScale n v

/-- The **radial interpolation** from `v` (at `t = 0`) to the normalisation `collarNorm n v`
(at `t = 1`). -/
def collarInterp (n : ℕ) (p : EuclideanSpace ℝ (Fin n) × unitInterval) :
    EuclideanSpace ℝ (Fin n) :=
  collarInterpScale n p.1 (p.2 : ℝ) • p.1

@[simp] theorem collarInterp_apply (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (t : unitInterval) :
    collarInterp n (v, t) = collarInterpScale n v (t : ℝ) • v := rfl

@[simp] theorem collarInterpScale_zero (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    collarInterpScale n v 0 = 1 := by
  rw [collarInterpScale]; ring

@[simp] theorem collarInterpScale_one (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    collarInterpScale n v 1 = collarScale n v := by
  rw [collarInterpScale]; ring

@[simp] theorem collarInterp_zero (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    collarInterp n (v, 0) = v := by
  have h : (((0 : unitInterval) : ℝ)) = 0 := rfl
  rw [collarInterp_apply, h, collarInterpScale_zero, one_smul]

@[simp] theorem collarInterp_one (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    collarInterp n (v, 1) = collarNorm n v := by
  have h : (((1 : unitInterval) : ℝ)) = 1 := rfl
  rw [collarInterp_apply, h, collarInterpScale_one, collarNorm]

/-! ## Elementary arithmetic -/

theorem half_pos : (0 : ℝ) < 1 / 2 := by norm_num

theorem half_le_max_collarSup (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    (1 / 2 : ℝ) ≤ max (1 / 2 : ℝ) (coordSup n v : ℝ) := le_max_left _ _

theorem max_collarSup_pos (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    (0 : ℝ) < max (1 / 2 : ℝ) (coordSup n v : ℝ) :=
  lt_of_lt_of_le half_pos (half_le_max_collarSup n v)

theorem collarScale_pos (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) : 0 < collarScale n v :=
  inv_pos.mpr (max_collarSup_pos n v)

theorem collarScale_nonneg (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) : 0 ≤ collarScale n v :=
  le_of_lt (collarScale_pos n v)

theorem collarScale_le_two (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) : collarScale n v ≤ 2 := by
  rw [collarScale]
  have h := (inv_le_inv₀ (max_collarSup_pos n v)
    (by norm_num : (0 : ℝ) < 1 / 2)).mpr (half_le_max_collarSup n v)
  norm_num at h
  exact h

theorem collarScale_of_half_le (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (h : (1 / 2 : ℝ) ≤ (coordSup n v : ℝ)) : collarScale n v = ((coordSup n v : ℝ))⁻¹ := by
  rw [collarScale, max_eq_right h]

theorem collarScale_of_le_half (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (h : (coordSup n v : ℝ) ≤ 1 / 2) : collarScale n v = 2 := by
  rw [collarScale, max_eq_left h]
  norm_num

/-- The normalisation factor times any coordinate (in absolute value) is at most `1`. -/
theorem collarScale_mul_abs_le_one (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    collarScale n v * |v i| ≤ 1 := by
  have h1 : (nnnorm (v i) : ℝ) ≤ (coordSup n v : ℝ) := by
    exact_mod_cast coordSup_le v i
  have h2 : |v i| = (nnnorm (v i) : ℝ) := by rw [coe_nnnorm, Real.norm_eq_abs]
  rw [h2, collarScale]
  calc (max (1 / 2 : ℝ) (coordSup n v : ℝ))⁻¹ * (nnnorm (v i) : ℝ)
      ≤ (max (1 / 2 : ℝ) (coordSup n v : ℝ))⁻¹ * (coordSup n v : ℝ) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (le_of_lt (max_collarSup_pos n v)))
    _ ≤ (max (1 / 2 : ℝ) (coordSup n v : ℝ))⁻¹ * max (1 / 2 : ℝ) (coordSup n v : ℝ) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (inv_nonneg.mpr (le_of_lt (max_collarSup_pos n v)))
    _ = 1 := inv_mul_cancel₀ (ne_of_gt (max_collarSup_pos n v))

/-- The absolute value of the attaining coordinate of `v` is the coordinate sup-norm of `v`. -/
theorem abs_eq_coordSup_of_eq {n : ℕ} {v : EuclideanSpace ℝ (Fin n)} {i : Fin n}
    (hi : coordSup n v = nnnorm (v i)) : |v i| = (coordSup n v : ℝ) := by
  have : (nnnorm (v i) : ℝ) = (coordSup n v : ℝ) :=
    congrArg (fun z : NNReal => (z : ℝ)) hi.symm
  rwa [coe_nnnorm, Real.norm_eq_abs] at this

/-! ## The normalisation of the coordinates -/

theorem collarNorm_apply (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (collarNorm n v) i = collarScale n v * v i := by
  simp [collarNorm, PiLp.smul_apply, smul_eq_mul]

theorem abs_collarNorm_apply_le_one (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |(collarNorm n v) i| ≤ 1 := by
  rw [collarNorm_apply, abs_mul, abs_of_nonneg (collarScale_nonneg n v)]
  exact collarScale_mul_abs_le_one n v i

/-- If the coordinate sup-norm of `v` exceeds `1/2`, the normalisation is of sup-norm exactly `1`:
some coordinate of `collarNorm n v` has absolute value `1`. -/
theorem exists_abs_collarNorm_apply_eq_one (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (h : (1 / 2 : ℝ) < (coordSup n v : ℝ)) :
    ∃ i : Fin n, |(collarNorm n v) i| = 1 := by
  have hpos : 0 < coordSup n v := by
    have : (0 : ℝ) < (coordSup n v : ℝ) := lt_trans half_pos h
    exact_mod_cast this
  obtain ⟨j, hj⟩ := exists_coordSup_eq_of_pos v hpos
  refine ⟨j, ?_⟩
  have hcs : collarScale n v = ((coordSup n v : ℝ))⁻¹ := collarScale_of_half_le n v (le_of_lt h)
  have hne : (coordSup n v : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
  calc |(collarNorm n v) j| = collarScale n v * |v j| := by
        rw [collarNorm_apply, abs_mul, abs_of_nonneg (collarScale_nonneg n v)]
    _ = ((coordSup n v : ℝ))⁻¹ * (coordSup n v : ℝ) := by rw [hcs, abs_eq_coordSup_of_eq hj]
    _ = 1 := inv_mul_cancel₀ hne

/-- If the coordinate sup-norm of `v` equals `1`, the normalisation fixes `v`. -/
theorem collarScale_eq_one_of_coordSup_eq_one (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (h : (coordSup n v : ℝ) = 1) : collarScale n v = 1 := by
  rw [collarScale, h, max_eq_right (by norm_num : (1 / 2 : ℝ) ≤ 1), inv_one]

theorem collarNorm_eq_self_of_coordSup_eq_one (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (h : (coordSup n v : ℝ) = 1) : collarNorm n v = v := by
  rw [collarNorm, collarScale_eq_one_of_coordSup_eq_one n v h, one_smul]

/-! ## The interpolation -/

theorem collarInterpScale_nonneg (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ collarInterpScale n v t := by
  rw [collarInterpScale]
  nlinarith [collarScale_nonneg n v]

theorem abs_collarInterp_apply_le_max (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (t : unitInterval)
    (i : Fin n) : |(collarInterp n (v, t)) i| ≤ max |v i| 1 := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have h1 : (collarInterp n (v, t)) i = collarInterpScale n v (t : ℝ) * v i := by
    simp [collarInterp, PiLp.smul_apply, smul_eq_mul]
  rw [h1, abs_mul, abs_of_nonneg (collarInterpScale_nonneg n v _ ht0 ht1), collarInterpScale]
  have hsum : ((1 - (t : ℝ)) + (t : ℝ) * collarScale n v) * |v i|
      = (1 - (t : ℝ)) * |v i| + (t : ℝ) * (collarScale n v * |v i|) := by ring
  rw [hsum]
  have hM : |v i| ≤ max |v i| 1 := le_max_left _ _
  have hM1 : (1 : ℝ) ≤ max |v i| 1 := le_max_right _ _
  have hcs : collarScale n v * |v i| ≤ 1 := collarScale_mul_abs_le_one n v i
  nlinarith [ht0, ht1]

theorem abs_collarInterp_apply_lt_three_halves (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (t : unitInterval) (i : Fin n) (h : |v i| < 3 / 2) :
    |(collarInterp n (v, t)) i| < 3 / 2 :=
  lt_of_le_of_lt (abs_collarInterp_apply_le_max n v t i) (max_lt h (by norm_num))

theorem abs_collarInterp_apply_le_one (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (t : unitInterval)
    (i : Fin n) (h : |v i| ≤ 1) : |(collarInterp n (v, t)) i| ≤ 1 :=
  le_trans (abs_collarInterp_apply_le_max n v t i) (max_le h le_rfl)

/-- Along the interpolation, the attaining coordinate stays above `1/2` as long as the coordinate
sup-norm of `v` does. -/
theorem exists_abs_collarInterp_apply_gt_half (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (t : unitInterval) (h : (1 / 2 : ℝ) < (coordSup n v : ℝ)) :
    ∃ i : Fin n, (1 / 2 : ℝ) < |(collarInterp n (v, t)) i| := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hpos : 0 < coordSup n v := by
    have : (0 : ℝ) < (coordSup n v : ℝ) := lt_trans half_pos h
    exact_mod_cast this
  obtain ⟨j, hj⟩ := exists_coordSup_eq_of_pos v hpos
  refine ⟨j, ?_⟩
  have hcs : collarScale n v = ((coordSup n v : ℝ))⁻¹ := collarScale_of_half_le n v (le_of_lt h)
  have hne : (coordSup n v : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
  have h1 : (collarInterp n (v, t)) j = collarInterpScale n v (t : ℝ) * v j := by
    simp [collarInterp, PiLp.smul_apply, smul_eq_mul]
  rw [h1, abs_mul, abs_of_nonneg (collarInterpScale_nonneg n v _ ht0 ht1),
    abs_eq_coordSup_of_eq hj, collarInterpScale, hcs]
  have hsplit : ((1 - (t : ℝ)) + (t : ℝ) * ((coordSup n v : ℝ))⁻¹) * (coordSup n v : ℝ)
      = (1 - (t : ℝ)) * (coordSup n v : ℝ) + (t : ℝ) := by
    field_simp
  rw [hsplit]
  have hconv : min (coordSup n v : ℝ) 1 ≤ (1 - (t : ℝ)) * (coordSup n v : ℝ) + (t : ℝ) := by
    rcases le_total (coordSup n v : ℝ) 1 with hc | hc
    · rw [min_eq_left hc]; nlinarith [ht0, ht1]
    · rw [min_eq_right hc]; nlinarith [ht0, ht1]
  have hkey : (1 / 2 : ℝ) < min (coordSup n v : ℝ) 1 := lt_min h (by norm_num)
  linarith

/-! ## The Euclidean pieces and the mapping properties of the normalisation -/

/-- The Euclidean counterpart of `sphLoopBig n`: the open cube `{|v|_∞ < 3/2}`. -/
def eucBig (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := {v | ∀ i, |v i| < 3 / 2}

/-- The Euclidean counterpart of `sphLoopCube n`: the cube `{|v|_∞ ≤ 1}`. -/
def eucCube (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := {v | ∀ i, |v i| ≤ 1}

/-- The Euclidean counterpart of `sphLoopBdry n`: the boundary `{|v|_∞ = 1}` of the cube. -/
def eucBdry (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {v | (∀ i, |v i| ≤ 1) ∧ ∃ i, |v i| = 1}

/-- The Euclidean counterpart of `sphLoopCollar n`: the collar `{1/2 < |v|_∞ < 3/2}`. -/
def eucCollar (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {v | (∃ i, (1 / 2 : ℝ) < |v i|) ∧ ∀ i, |v i| < 3 / 2}

/-- The collar inside the product `↥(eucBig n) × Y` (for the relative chain complexes of the
collar pair). -/
def eucCollarProd (n : ℕ) (Y : Type) : Set (↥(eucBig n) × Y) :=
  {p | (p.1 : EuclideanSpace ℝ (Fin n)) ∈ eucCollar n}

/-- The boundary part inside the product `↥(eucCube n) × Y`. -/
def eucBdryProd (n : ℕ) (Y : Type) : Set (↥(eucCube n) × Y) :=
  {p | (p.1 : EuclideanSpace ℝ (Fin n)) ∈ eucBdry n}

theorem exists_abs_gt_half_of_coordSup_gt_half (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (h : (1 / 2 : ℝ) < (coordSup n v : ℝ)) : ∃ i, (1 / 2 : ℝ) < |v i| := by
  have hpos : 0 < coordSup n v := by
    have : (0 : ℝ) < (coordSup n v : ℝ) := lt_trans half_pos h
    exact_mod_cast this
  obtain ⟨j, hj⟩ := exists_coordSup_eq_of_pos v hpos
  exact ⟨j, by rw [abs_eq_coordSup_of_eq hj]; exact h⟩

theorem coordSup_gt_half_of_exists_abs_gt_half (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (h : ∃ i, (1 / 2 : ℝ) < |v i|) : (1 / 2 : ℝ) < (coordSup n v : ℝ) := by
  obtain ⟨i, hi⟩ := h
  have hle : (nnnorm (v i) : ℝ) ≤ (coordSup n v : ℝ) := by exact_mod_cast coordSup_le v i
  rw [coe_nnnorm, Real.norm_eq_abs] at hle
  exact lt_of_lt_of_le hi hle

theorem coordSup_eq_one_of_mem_eucBdry (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (h1 : ∀ i, |v i| ≤ 1) (h2 : ∃ i, |v i| = 1) : (coordSup n v : ℝ) = 1 := by
  refine le_antisymm ?_ ?_
  · have h := (coordSup_le_one_iff n v).mpr (fun i => by
      rw [Set.mem_Icc, ← abs_le]; exact h1 i)
    exact_mod_cast h
  · obtain ⟨i, hi⟩ := h2
    have hle : (nnnorm (v i) : ℝ) ≤ (coordSup n v : ℝ) := by exact_mod_cast coordSup_le v i
    rw [coe_nnnorm, Real.norm_eq_abs, hi] at hle
    exact hle

theorem collarNorm_mem_cube (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    collarNorm n v ∈ eucCube n := fun i => abs_collarNorm_apply_le_one n v i

theorem collarNorm_mem_bdry_of_mem_collar (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (h : v ∈ eucCollar n) : collarNorm n v ∈ eucBdry n :=
  ⟨fun i => abs_collarNorm_apply_le_one n v i,
    exists_abs_collarNorm_apply_eq_one n v
      (coordSup_gt_half_of_exists_abs_gt_half n v h.1)⟩

theorem collarInterp_mem_big (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (t : unitInterval)
    (h : v ∈ eucBig n) : collarInterp n (v, t) ∈ eucBig n :=
  fun i => abs_collarInterp_apply_lt_three_halves n v t i (h i)

theorem collarInterp_mem_cube (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (t : unitInterval)
    (h : v ∈ eucCube n) : collarInterp n (v, t) ∈ eucCube n :=
  fun i => abs_collarInterp_apply_le_one n v t i (h i)

theorem collarInterp_mem_collar (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (t : unitInterval)
    (h : v ∈ eucCollar n) : collarInterp n (v, t) ∈ eucCollar n :=
  ⟨exists_abs_collarInterp_apply_gt_half n v t
      (coordSup_gt_half_of_exists_abs_gt_half n v h.1),
    fun i => abs_collarInterp_apply_lt_three_halves n v t i (h.2 i)⟩

theorem collarScale_eq_one_of_mem_eucBdry (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (h : v ∈ eucBdry n) :
    collarScale n v = 1 :=
  collarScale_eq_one_of_coordSup_eq_one n v
    (coordSup_eq_one_of_mem_eucBdry n v h.1 h.2)

theorem collarNorm_eq_self_of_mem_eucBdry (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (h : v ∈ eucBdry n) : collarNorm n v = v :=
  collarNorm_eq_self_of_coordSup_eq_one n v
    (coordSup_eq_one_of_mem_eucBdry n v h.1 h.2)

theorem collarInterp_eq_self_of_mem_eucBdry (n : ℕ) (v : EuclideanSpace ℝ (Fin n))
    (t : unitInterval) (h : v ∈ eucBdry n) : collarInterp n (v, t) = v := by
  have h1 : collarInterpScale n v (t : ℝ) = 1 := by
    rw [collarInterpScale, collarScale_eq_one_of_mem_eucBdry n v h]
    ring
  rw [collarInterp_apply, h1, one_smul]

theorem eucBdry_subset_eucCollar (n : ℕ) : eucBdry n ⊆ eucCollar n := by
  rintro v ⟨h1, i, hi⟩
  refine ⟨⟨i, ?_⟩, fun j => lt_of_le_of_lt (h1 j) (by norm_num)⟩
  rw [hi]; norm_num

theorem eucCube_subset_eucBig (n : ℕ) : eucCube n ⊆ eucBig n := fun v h i =>
  lt_of_le_of_lt (h i) (by norm_num)

/-! ## Continuity -/

@[fun_prop]
theorem continuous_collarScale (n : ℕ) : Continuous (collarScale n) := by
  have h1 : Continuous fun v : EuclideanSpace ℝ (Fin n) => (coordSup n v : ℝ) :=
    continuous_subtype_val.comp (continuous_coordSup n)
  have h2 : Continuous fun v : EuclideanSpace ℝ (Fin n) =>
      max (1 / 2 : ℝ) (coordSup n v : ℝ) := continuous_const.max h1
  exact h2.inv₀ fun v => ne_of_gt (max_collarSup_pos n v)

@[fun_prop]
theorem continuous_collarNorm (n : ℕ) : Continuous (collarNorm n) :=
  (continuous_collarScale n).smul continuous_id

@[fun_prop]
theorem continuous_collarInterp (n : ℕ) :
    Continuous fun p : EuclideanSpace ℝ (Fin n) × unitInterval => collarInterp n p := by
  have hcs : Continuous fun p : EuclideanSpace ℝ (Fin n) × unitInterval =>
      collarScale n p.1 := (continuous_collarScale n).comp continuous_fst
  have ht : Continuous fun p : EuclideanSpace ℝ (Fin n) × unitInterval => (p.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have h1 : Continuous fun p : EuclideanSpace ℝ (Fin n) × unitInterval =>
      collarInterpScale n p.1 (p.2 : ℝ) := by
    simp only [collarInterpScale]
    exact (continuous_const.sub ht).add (ht.mul hcs)
  exact h1.smul continuous_fst

end

end Work.StemsB

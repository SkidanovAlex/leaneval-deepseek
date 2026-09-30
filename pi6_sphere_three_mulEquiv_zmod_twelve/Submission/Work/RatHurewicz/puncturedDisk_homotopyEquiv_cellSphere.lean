import Mathlib
import Submission.Work.RatHurewicz.DiskPairDefs

/-!
# The punctured model cell is homotopy equivalent to the model sphere

The radial retraction `y ↦ y / ‖y‖` of the punctured model cell `D^{n+2} ∖ {0}` onto the model
sphere `S^{n+1} = cellSphere n` is a deformation retraction, the straight-line homotopy
`(t, y) ↦ (1 - t + t / ‖y‖) • y` joining it to the identity.  Hence
`↥(puncturedCellDisk n) ≃ₕ cellSphere n`.

This is used, together with the connectivity of the sphere (`πᵢ(S^{n+1}) = 0` for `i ≤ n`), to see
that the homotopy groups of the punctured cell vanish in degrees `≤ n`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- A point of the punctured cell has nonzero norm. -/
theorem norm_pos_of_mem_puncturedCellDisk {n : ℕ} (y : ↥(puncturedCellDisk n)) :
    0 < ‖(y : CellVec n)‖ := by
  rw [norm_pos_iff]
  exact y.2

/-- A point of the model cell has norm at most `1`. -/
theorem norm_le_one_of_mem_cellDisk {n : ℕ} (y : cellDisk n) : ‖(y : CellVec n)‖ ≤ 1 := by
  have h := y.2
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  exact h

/-- A point of the model sphere has norm `1`. -/
theorem norm_eq_one_of_mem_cellSphere {n : ℕ} (z : cellSphere n) : ‖(z : CellVec n)‖ = 1 := by
  have h := z.2
  rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h

theorem continuous_norm_punctured (n : ℕ) :
    Continuous fun y : ↥(puncturedCellDisk n) => ‖(y : CellVec n)‖ :=
  continuous_norm.comp (by fun_prop)

/-- The scalar of the radial deformation at time `t` and point `y`: at `t = 0` it is `‖y‖⁻¹` (the
radial projection) and at `t = 1` it is `1` (the identity). -/
def radialScalar (n : ℕ) (t : I) (y : ↥(puncturedCellDisk n)) : ℝ :=
  (1 - (t : ℝ)) * (‖(y : CellVec n)‖)⁻¹ + (t : ℝ)

@[simp] theorem radialScalar_zero (n : ℕ) (y : ↥(puncturedCellDisk n)) :
    radialScalar n 0 y = (‖(y : CellVec n)‖)⁻¹ := by
  unfold radialScalar
  norm_num

@[simp] theorem radialScalar_one (n : ℕ) (y : ↥(puncturedCellDisk n)) :
    radialScalar n 1 y = 1 := by
  unfold radialScalar
  norm_num

theorem radialScalar_pos {n : ℕ} (t : I) (y : ↥(puncturedCellDisk n)) :
    0 < radialScalar n t y := by
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hinv : 0 < (‖(y : CellVec n)‖)⁻¹ := inv_pos.mpr (norm_pos_of_mem_puncturedCellDisk y)
  rcases lt_or_eq_of_le ht1 with h | h
  · have h1 : 0 < 1 - (t : ℝ) := by linarith
    have hmul := mul_pos h1 hinv
    have : radialScalar n t y = (1 - (t : ℝ)) * (‖(y : CellVec n)‖)⁻¹ + (t : ℝ) := rfl
    rw [this]
    linarith [t.2.1]
  · have : radialScalar n t y = 1 := by
      unfold radialScalar
      rw [h]
      ring
    rw [this]
    norm_num

theorem radialScalar_mul_norm_le_one {n : ℕ} (t : I) (y : ↥(puncturedCellDisk n)) :
    radialScalar n t y * ‖(y : CellVec n)‖ ≤ 1 := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hnorm : ‖(y : CellVec n)‖ ≤ 1 := norm_le_one_of_mem_cellDisk y.1
  have hne : ‖(y : CellVec n)‖ ≠ 0 := ne_of_gt (norm_pos_of_mem_puncturedCellDisk y)
  have hinv : (‖(y : CellVec n)‖)⁻¹ * ‖(y : CellVec n)‖ = 1 := inv_mul_cancel₀ hne
  have h1 : 0 ≤ 1 - (t : ℝ) := by linarith
  calc radialScalar n t y * ‖(y : CellVec n)‖
      = (1 - (t : ℝ)) * ((‖(y : CellVec n)‖)⁻¹ * ‖(y : CellVec n)‖)
          + (t : ℝ) * ‖(y : CellVec n)‖ := by
        unfold radialScalar; ring
    _ = (1 - (t : ℝ)) * 1 + (t : ℝ) * ‖(y : CellVec n)‖ := by rw [hinv]
    _ ≤ (1 - (t : ℝ)) * 1 + (t : ℝ) * 1 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hnorm ht0)
    _ = 1 := by ring

theorem continuous_radialScalar (n : ℕ) :
    Continuous fun p : I × ↥(puncturedCellDisk n) => radialScalar n p.1 p.2 := by
  unfold radialScalar
  refine Continuous.add (Continuous.mul ?_ ?_) ?_
  · exact continuous_const.sub (continuous_subtype_val.comp continuous_fst)
  · exact Continuous.inv₀ (by fun_prop)
      (fun p => ne_of_gt (norm_pos_of_mem_puncturedCellDisk p.2))
  · exact continuous_subtype_val.comp continuous_fst

theorem continuous_radialVec (n : ℕ) :
    Continuous fun p : I × ↥(puncturedCellDisk n) =>
      radialScalar n p.1 p.2 • (p.2 : CellVec n) :=
  Continuous.smul (continuous_radialScalar n) (by fun_prop)

/-- The radial deformation, as a point of the punctured cell. -/
def radialHomotopyPt (n : ℕ) (p : I × ↥(puncturedCellDisk n)) : ↥(puncturedCellDisk n) :=
  ⟨⟨radialScalar n p.1 p.2 • (p.2 : CellVec n), by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul,
        Real.norm_of_nonneg (le_of_lt (radialScalar_pos p.1 p.2))]
      exact radialScalar_mul_norm_le_one p.1 p.2⟩,
    by
      rw [mem_puncturedCellDisk]
      exact smul_ne_zero (ne_of_gt (radialScalar_pos p.1 p.2)) p.2.2⟩

theorem continuous_radialHomotopyPt (n : ℕ) : Continuous (radialHomotopyPt n) := by
  unfold radialHomotopyPt
  refine Continuous.subtype_mk ?_ _
  refine Continuous.subtype_mk ?_ _
  exact continuous_radialVec n

/-- The uncurried radial deformation, as a continuous map `I × ↥A → ↥A`. -/
def radialHomotopyMap (n : ℕ) :
    C(I × ↥(puncturedCellDisk n), ↥(puncturedCellDisk n)) :=
  ⟨radialHomotopyPt n, continuous_radialHomotopyPt n⟩

/-- **The radial retraction** `y ↦ y / ‖y‖` of the punctured cell onto the model sphere. -/
def radialMap (n : ℕ) : C(↥(puncturedCellDisk n), cellSphere n) where
  toFun y := ⟨(‖(y : CellVec n)‖)⁻¹ • (y : CellVec n), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (ne_of_gt (norm_pos_of_mem_puncturedCellDisk y))⟩
  continuous_toFun := Continuous.subtype_mk
    (Continuous.smul
      (Continuous.inv₀ (continuous_norm_punctured n)
        (fun y => ne_of_gt (norm_pos_of_mem_puncturedCellDisk y)))
      (by fun_prop)) _

/-- The inclusion of the model sphere into the model disc (`‖z‖ = 1 ≤ 1`). -/
def sphereToDisk (n : ℕ) : C(cellSphere n, cellDisk n) where
  toFun z := ⟨(z : CellVec n), by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_of_eq (norm_eq_one_of_mem_cellSphere z)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop

@[simp] theorem sphereToDisk_coe (n : ℕ) (z : cellSphere n) :
    ((sphereToDisk n z : cellDisk n) : CellVec n) = (z : CellVec n) := rfl

@[simp] theorem radialMap_coe (n : ℕ) (y : ↥(puncturedCellDisk n)) :
    ((radialMap n y : cellSphere n) : CellVec n) = (‖(y : CellVec n)‖)⁻¹ • (y : CellVec n) := rfl

/-- The inclusion of the model sphere into the punctured cell. -/
def radialIncl (n : ℕ) : C(cellSphere n, ↥(puncturedCellDisk n)) where
  toFun z := ⟨sphereToDisk n z, by
    rw [mem_puncturedCellDisk]
    intro hzero
    have hz : (z : CellVec n) = 0 := by
      have h := sphereToDisk_coe n z
      rw [hzero] at h
      exact h.symm
    have h1 := norm_eq_one_of_mem_cellSphere z
    rw [hz, norm_zero] at h1
    norm_num at h1⟩
  continuous_toFun := Continuous.subtype_mk (sphereToDisk n).continuous _

@[simp] theorem radialIncl_coe (n : ℕ) (z : cellSphere n) :
    ((radialIncl n z : ↥(puncturedCellDisk n)) : CellVec n) = (z : CellVec n) := rfl

theorem radialMap_radialIncl (n : ℕ) :
    (radialMap n).comp (radialIncl n) = ContinuousMap.id (cellSphere n) := by
  refine ContinuousMap.ext fun z => Subtype.ext ?_
  show (‖((radialIncl n z : ↥(puncturedCellDisk n)) : CellVec n)‖)⁻¹
      • ((radialIncl n z : ↥(puncturedCellDisk n)) : CellVec n) = (z : CellVec n)
  rw [radialIncl_coe, norm_eq_one_of_mem_cellSphere, inv_one, one_smul]

/-- The radial deformation is a homotopy from `radialIncl ∘ radialMap` to the identity. -/
def radialHomotopy (n : ℕ) :
    ((radialIncl n).comp (radialMap n)).Homotopy (ContinuousMap.id (↥(puncturedCellDisk n))) :=
  ContinuousMap.Homotopy.mk (radialHomotopyMap n)
    (fun y => by
      apply Subtype.ext
      apply Subtype.ext
      show radialScalar n 0 y • (y : CellVec n)
        = (‖(y : CellVec n)‖)⁻¹ • (y : CellVec n)
      rw [radialScalar_zero])
    (fun y => by
      apply Subtype.ext
      apply Subtype.ext
      show radialScalar n 1 y • (y : CellVec n) = (y : CellVec n)
      simp [radialScalar_one])

/-- **The punctured model cell is homotopy equivalent to the model sphere.** -/
theorem puncturedDisk_homotopyEquiv_cellSphere (n : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(puncturedCellDisk n) (cellSphere n)) :=
  ⟨{ toFun := radialMap n
     invFun := radialIncl n
     left_inv := ⟨radialHomotopy n⟩
     right_inv := by rw [radialMap_radialIncl] }⟩

end

end Work.RatHurewicz

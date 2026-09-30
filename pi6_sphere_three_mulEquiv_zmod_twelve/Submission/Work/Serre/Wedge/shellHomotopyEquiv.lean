import Mathlib
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.RatHurewicz.AttachPush.Defs

set_option synthInstance.maxHeartbeats 400000


/-!
# The model shell `{ρ < ‖x‖ < R}` is homotopy equivalent to the model sphere

For `0 < ρ < R ≤ 1` the model shell

  `cellShellSet n ρ R = {x : D^{n+2} | ρ < ‖x‖ < R}`

inside the model cell `D^{n+2} = cellDisk n` deformation retracts onto the sphere of radius
`r = (ρ + R)/2` contained in it, and that sphere is carried homeomorphically onto the unit
sphere `cellSphere n` by the radial projection `x ↦ x / ‖x‖`.

The deformation retraction is the radial (straight line) homotopy with scalar

  `shellScalar t x = (1 - t) * (r * ‖x‖⁻¹) + t`,

so that at `t = 0` the point moves to `(r/‖x‖) • x` (the image of the radial projection) and at
`t = 1` it is `x` itself; the crucial point is that

  `‖shellScalar t x • x‖ = (1 - t) * r + t * ‖x‖`

is a convex combination of the two radii `r` and `‖x‖`, both of which lie in `(ρ, R)`.

This is the model statement identifying the relative part of an excised piece (a shell around a
cell centre) with a sphere.
-/

open scoped Topology unitInterval

namespace Work.Serre.Wedge

noncomputable section

open Work.RatHurewicz

/-! ## The middle radius of the shell -/

/-- The middle radius `(ρ + R)/2` of the shell `{ρ < ‖x‖ < R}`. -/
def shellRadius (ρ R : ℝ) : ℝ := (ρ + R) / 2

theorem shellRadius_pos {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) : 0 < shellRadius ρ R := by
  unfold shellRadius; linarith

theorem lt_shellRadius {ρ R : ℝ} (hρR : ρ < R) : ρ < shellRadius ρ R := by
  unfold shellRadius; linarith

theorem shellRadius_lt {ρ R : ℝ} (hρR : ρ < R) : shellRadius ρ R < R := by
  unfold shellRadius; linarith

/-! ## Points of the shell have positive norm -/

theorem norm_pos_of_mem_cellShellSet {n : ℕ} {ρ R : ℝ} (hρ : 0 < ρ) {x : cellDisk n}
    (hx : x ∈ cellShellSet n ρ R) : 0 < ‖(x : CellVec n)‖ :=
  lt_trans hρ (mem_cellShellSet.mp hx).1

theorem norm_pos_shell {n : ℕ} {ρ R : ℝ} (hρ : 0 < ρ) (x : ↥(cellShellSet n ρ R)) :
    0 < ‖(x : CellVec n)‖ :=
  norm_pos_of_mem_cellShellSet hρ x.2

/-! ## The radial projection of the shell onto the sphere -/

/-- **The radial projection** of the shell onto the unit sphere, `x ↦ x / ‖x‖`. -/
def shellRadialMap (n : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) :
    C(↥(cellShellSet n ρ R), cellSphere n) where
  toFun x := ⟨(‖(x : CellVec n)‖)⁻¹ • (x : CellVec n), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (ne_of_gt (norm_pos_shell hρ x))⟩
  continuous_toFun := Continuous.subtype_mk
    (Continuous.smul
      (Continuous.inv₀ (continuous_norm.comp (by fun_prop))
        (fun x => ne_of_gt (norm_pos_shell hρ x)))
      (by fun_prop)) _

/-! ## The inclusion of the sphere as the middle sphere of the shell -/

/-- **The inclusion of the unit sphere into the shell**, `z ↦ r • z` with `r = (ρ + R)/2`. -/
def shellIncl (n : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ < R) (hR : R ≤ 1) :
    C(cellSphere n, ↥(cellShellSet n ρ R)) where
  toFun z := ⟨⟨shellRadius ρ R • (z : CellVec n), by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul,
        Real.norm_of_nonneg (le_of_lt (shellRadius_pos hρ hρR)),
        norm_eq_one_of_mem_cellSphere z, mul_one]
      exact le_of_lt (lt_of_lt_of_le (shellRadius_lt hρR) hR)⟩,
    by
      rw [mem_cellShellSet, norm_smul,
        Real.norm_of_nonneg (le_of_lt (shellRadius_pos hρ hρR)),
        norm_eq_one_of_mem_cellSphere z, mul_one]
      exact ⟨lt_shellRadius hρR, shellRadius_lt hρR⟩⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    fun_prop

/-! ## The radial homotopy -/

/-- The scalar of the radial deformation of the shell at time `t` and point `x`: at `t = 0` it is
`r * ‖x‖⁻¹` (the radial projection) and at `t = 1` it is `1` (the identity). -/
def shellScalar (n : ℕ) (ρ R : ℝ) (t : I) (x : ↥(cellShellSet n ρ R)) : ℝ :=
  (1 - (t : ℝ)) * (shellRadius ρ R * (‖(x : CellVec n)‖)⁻¹) + (t : ℝ)

@[simp] theorem shellScalar_zero (n : ℕ) (ρ R : ℝ) (x : ↥(cellShellSet n ρ R)) :
    shellScalar n ρ R 0 x = shellRadius ρ R * (‖(x : CellVec n)‖)⁻¹ := by
  unfold shellScalar
  norm_num

@[simp] theorem shellScalar_one (n : ℕ) (ρ R : ℝ) (x : ↥(cellShellSet n ρ R)) :
    shellScalar n ρ R 1 x = 1 := by
  unfold shellScalar
  norm_num

theorem shellScalar_nonneg {n : ℕ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (t : I)
    (x : ↥(cellShellSet n ρ R)) : 0 ≤ shellScalar n ρ R t x := by
  unfold shellScalar
  have h1 : 0 ≤ 1 - (t : ℝ) := by linarith [t.2.2]
  have h2 : 0 ≤ shellRadius ρ R * (‖(x : CellVec n)‖)⁻¹ :=
    mul_nonneg (le_of_lt (shellRadius_pos hρ hρR)) (inv_nonneg.mpr (norm_nonneg _))
  have h3 : 0 ≤ (t : ℝ) := t.2.1
  linarith [mul_nonneg h1 h2]

/-- **The norm of the deformed point**: `‖s t x • x‖ = (1 - t) * r + t * ‖x‖`. -/
theorem shellScalar_smul_norm {n : ℕ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (t : I)
    (x : ↥(cellShellSet n ρ R)) :
    ‖shellScalar n ρ R t x • (x : CellVec n)‖
      = (1 - (t : ℝ)) * shellRadius ρ R + (t : ℝ) * ‖(x : CellVec n)‖ := by
  rw [norm_smul, Real.norm_of_nonneg (shellScalar_nonneg hρ hρR t x)]
  have hne : ‖(x : CellVec n)‖ ≠ 0 := ne_of_gt (norm_pos_shell hρ x)
  calc shellScalar n ρ R t x * ‖(x : CellVec n)‖
      = ((1 - (t : ℝ)) * (shellRadius ρ R * (‖(x : CellVec n)‖)⁻¹) + (t : ℝ))
          * ‖(x : CellVec n)‖ := rfl
    _ = (1 - (t : ℝ)) * (shellRadius ρ R * ((‖(x : CellVec n)‖)⁻¹ * ‖(x : CellVec n)‖))
          + (t : ℝ) * ‖(x : CellVec n)‖ := by ring
    _ = (1 - (t : ℝ)) * (shellRadius ρ R * 1) + (t : ℝ) * ‖(x : CellVec n)‖ := by
          rw [inv_mul_cancel₀ hne]
    _ = (1 - (t : ℝ)) * shellRadius ρ R + (t : ℝ) * ‖(x : CellVec n)‖ := by ring

/-- The deformed point stays in the shell: its norm is a convex combination of `r` and `‖x‖`. -/
theorem shellScalar_smul_mem {n : ℕ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (t : I)
    (x : ↥(cellShellSet n ρ R)) :
    ‖shellScalar n ρ R t x • (x : CellVec n)‖ ∈ Set.Ioo ρ R := by
  rw [shellScalar_smul_norm hρ hρR t x]
  have hconv : (1 - (t : ℝ)) • shellRadius ρ R + (t : ℝ) • ‖(x : CellVec n)‖ ∈ Set.Ioo ρ R :=
    convex_Ioo ρ R ⟨lt_shellRadius hρR, shellRadius_lt hρR⟩ (mem_cellShellSet.mp x.2)
      (by linarith [t.2.2]) t.2.1 (by ring)
  simpa only [smul_eq_mul] using hconv

/-! ## The radial deformation as a map `I × shell → shell` -/

/-- The radial deformation of the shell, as a point of the shell. -/
def shellHomotopyPt (n : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ < R) (hR : R ≤ 1)
    (p : I × ↥(cellShellSet n ρ R)) : ↥(cellShellSet n ρ R) :=
  ⟨⟨shellScalar n ρ R p.1 p.2 • (p.2 : CellVec n), by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_of_lt (lt_of_lt_of_le (shellScalar_smul_mem hρ hρR p.1 p.2).2 hR)⟩,
    by
      rw [mem_cellShellSet]
      exact shellScalar_smul_mem hρ hρR p.1 p.2⟩

theorem continuous_shellScalar (n : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) :
    Continuous fun p : I × ↥(cellShellSet n ρ R) => shellScalar n ρ R p.1 p.2 := by
  unfold shellScalar
  refine Continuous.add ?_ ?_
  · refine Continuous.mul ?_ ?_
    · exact continuous_const.sub (continuous_subtype_val.comp continuous_fst)
    · exact Continuous.mul continuous_const
        (Continuous.inv₀ (continuous_norm.comp (by fun_prop))
          (fun p => ne_of_gt (norm_pos_shell hρ p.2)))
  · exact continuous_subtype_val.comp continuous_fst

theorem continuous_shellHomotopyPt (n : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ < R) (hR : R ≤ 1) :
    Continuous (shellHomotopyPt n ρ R hρ hρR hR) := by
  unfold shellHomotopyPt
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact Continuous.smul (continuous_shellScalar n ρ R hρ) (by fun_prop)

/-- The uncurried radial deformation, as a continuous map `I × shell → shell`. -/
def shellHomotopyMap (n : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ < R) (hR : R ≤ 1) :
    C(I × ↥(cellShellSet n ρ R), ↥(cellShellSet n ρ R)) :=
  ⟨shellHomotopyPt n ρ R hρ hρR hR, continuous_shellHomotopyPt n ρ R hρ hρR hR⟩

/-! ## The two homotopy identities -/

/-- The radial projection is a left inverse of the inclusion. -/
theorem shellRadialMap_comp_shellIncl (n : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ < R)
    (hR : R ≤ 1) :
    (shellRadialMap n ρ R hρ).comp (shellIncl n ρ R hρ hρR hR) = ContinuousMap.id (cellSphere n) := by
  refine ContinuousMap.ext fun z => Subtype.ext ?_
  show (‖shellRadius ρ R • (z : CellVec n)‖)⁻¹ • (shellRadius ρ R • (z : CellVec n))
    = (z : CellVec n)
  rw [norm_smul, Real.norm_of_nonneg (le_of_lt (shellRadius_pos hρ hρR)),
    norm_eq_one_of_mem_cellSphere z, mul_one, smul_smul,
    inv_mul_cancel₀ (ne_of_gt (shellRadius_pos hρ hρR)), one_smul]

/-- The radial deformation is a homotopy from `inclusion ∘ projection` to the identity. -/
def shellHomotopy (n : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ < R) (hR : R ≤ 1) :
    ((shellIncl n ρ R hρ hρR hR).comp (shellRadialMap n ρ R hρ)).Homotopy
      (ContinuousMap.id ↥(cellShellSet n ρ R)) :=
  ContinuousMap.Homotopy.mk (shellHomotopyMap n ρ R hρ hρR hR)
    (fun x => by
      apply Subtype.ext
      apply Subtype.ext
      show shellScalar n ρ R 0 x • (x : CellVec n)
        = shellRadius ρ R • ((‖(x : CellVec n)‖)⁻¹ • (x : CellVec n))
      rw [shellScalar_zero, mul_smul])
    (fun x => by
      apply Subtype.ext
      apply Subtype.ext
      show shellScalar n ρ R 1 x • (x : CellVec n) = (x : CellVec n)
      rw [shellScalar_one, one_smul])

/-! ## The homotopy equivalence -/

theorem shellHomotopyEquiv (n : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ < R) (hR : R ≤ 1) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(Work.Serre.cellShellSet n ρ R)
      (Work.RatHurewicz.cellSphere n)) :=
  ⟨{ toFun := shellRadialMap n ρ R hρ
     invFun := shellIncl n ρ R hρ hρR hR
     left_inv := ⟨shellHomotopy n ρ R hρ hρR hR⟩
     right_inv := by rw [shellRadialMap_comp_shellIncl n ρ R hρ hρR hR] }⟩

end

end Work.Serre.Wedge

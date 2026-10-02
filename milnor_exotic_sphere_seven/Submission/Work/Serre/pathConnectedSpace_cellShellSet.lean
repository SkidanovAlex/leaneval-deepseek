import Mathlib
import Submission.Work.Serre.CellStep.Geom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The model shell `{ρ < ‖x‖ < R}` of a cell is path connected

The model cell `D^{n+2}` is `cellDisk n`, the closed unit ball of `CellVec n = ℝ^{n+2}`; hence
`cellShellSet n ρ R = {x | ρ < ‖x‖ < R}` is an annulus in a real vector space of dimension
`n + 2 ≥ 2`.  It is the image of the path connected space

  `S^{n+1} × (ρ, R) = ↥(Metric.sphere 0 1) × ↥(Set.Ioo ρ R)`

under the continuous surjection `(u, t) ↦ t • u` (a point of the shell of norm `t` is `t` times the
unit vector in its own direction), hence it is path connected.

This is the input used by the Mayer–Vietoris/local-Thom machinery of the cell step, where every
piece of the cover of the attached cells has to be a path connected space (see e.g.
`Work.RatHurewicz.cupBijective_cylPre`, whose degree zero clause needs `PathConnectedSpace ↥V`).
-/

namespace Work.Serre

open Set Metric
open Work.RatHurewicz

noncomputable section

/-- The Euclidean space underlying the model cell `D^{n+2}` has dimension `n + 2 ≥ 2`. -/
theorem one_lt_rank_cellVec (n : ℕ) : 1 < Module.rank ℝ (CellVec n) := by
  rw [← Module.finrank_eq_rank ℝ, finrank_euclideanSpace_fin]
  have : (2 : Cardinal) ≤ ((n + 2 : ℕ) : Cardinal) := by
    exact_mod_cast (by omega : 2 ≤ n + 2)
  exact lt_of_lt_of_le (by norm_num : (1 : Cardinal) < 2) this

/-- A point of the unit sphere of `CellVec n` has norm one. -/
theorem norm_eq_one_of_mem_sphere_one {n : ℕ} {u : CellVec n}
    (hu : u ∈ Metric.sphere (0 : CellVec n) 1) : ‖u‖ = 1 := by
  rwa [Metric.mem_sphere, dist_zero_right] at hu

/-- **The shell parametrisation.**  Multiplication `(u, t) ↦ t • u` maps the product of the unit
sphere and the interval `(ρ, R)` into the model cell `D^{n+2}`; its values on the product have norm
`t ∈ (ρ, R)`, so its range is exactly the model shell `cellShellSet n ρ R`. -/
def cellShellMap (n : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) (hR : R ≤ 1) :
    ↥(Metric.sphere (0 : CellVec n) 1) × ↥(Set.Ioo ρ R) → cellDisk n :=
  fun p => ⟨(p.2 : ℝ) • (p.1 : CellVec n), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (le_of_lt (lt_trans hρ p.2.2.1)), norm_eq_one_of_mem_sphere_one p.1.2,
      mul_one]
    linarith [p.2.2.2, hR]⟩

/-- The norm of `cellShellMap` at `(u, t)` is `t`. -/
theorem norm_cellShellMap (n : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) (hR : R ≤ 1)
    (p : ↥(Metric.sphere (0 : CellVec n) 1) × ↥(Set.Ioo ρ R)) :
    ‖((cellShellMap n ρ R hρ hR p : cellDisk n) : CellVec n)‖ = (p.2 : ℝ) := by
  rw [cellShellMap, Subtype.coe_mk, norm_smul,
    Real.norm_of_nonneg (le_of_lt (lt_trans hρ p.2.2.1)), norm_eq_one_of_mem_sphere_one p.1.2,
    mul_one]

theorem continuous_cellShellMap (n : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) (hR : R ≤ 1) :
    Continuous (cellShellMap n ρ R hρ hR) := by
  apply Continuous.subtype_mk
  fun_prop

/-- The range of the shell parametrisation is the model shell. -/
theorem range_cellShellMap (n : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) (hR : R ≤ 1) :
    Set.range (cellShellMap n ρ R hρ hR) = cellShellSet n ρ R := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    rw [mem_cellShellSet, norm_cellShellMap]
    exact ⟨p.2.2.1, p.2.2.2⟩
  · intro hx
    rw [mem_cellShellSet] at hx
    set v : CellVec n := (x : CellVec n) with hv
    have hx0 : 0 < ‖v‖ := lt_trans hρ hx.1
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : CellVec n) 1 := by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hx0.le), inv_mul_cancel₀ hx0.ne']
    refine ⟨(⟨‖v‖⁻¹ • v, hu⟩, ⟨‖v‖, ⟨hx.1, hx.2⟩⟩), ?_⟩
    apply Subtype.ext
    show ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ hx0.ne', one_smul]

/-- **The model shell `{ρ < ‖x‖ < R}` of a cell is path connected.**  It is the continuous image of
the path connected space `S^{n+1} × (ρ, R)`, since `n + 2 ≥ 2` makes the unit sphere of
`CellVec n` path connected. -/
theorem pathConnectedSpace_cellShellSet (n : ℕ) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hR : R ≤ 1) :
    PathConnectedSpace ↥(Work.Serre.cellShellSet n ρ R) := by
  have hrank := one_lt_rank_cellVec n
  have hsphereI : PathConnectedSpace ↥(Metric.sphere (0 : CellVec n) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hrank 0 (by norm_num))
  have hIooI : PathConnectedSpace ↥(Set.Ioo ρ R) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Ioo (r := ρ) (s := R)).isPathConnected
        ⟨(ρ + R) / 2, by constructor <;> linarith⟩)
  exact isPathConnected_iff_pathConnectedSpace.mp
    ((range_cellShellMap n ρ R hρ hR) ▸ isPathConnected_range (continuous_cellShellMap n ρ R hρ hR))

end

end Work.Serre

import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `χ_{B(u)}` vanishes when the box `B(u)` is a null set

`Submission.BoseGases.chiB ℓ d u` is the localising cutoff
`χ(x/ℓ)·χ(x/(ℓd) − u)`, whose (pointwise) support is contained in the `u`-indexed
small box `dlBox ℓ d u = acube ℓ ∩ (ℓd·u + acube(ℓd))`.

The *sharp* support statement is what makes the degeneracies go away: the scaled bump
`chiScale ℓ` vanishes already on the closed complement of the open ball of radius `ℓ/2`
(the underlying `ContDiffBump` has `rOut = 1/2` and `zero_of_le_dist` applies at distance
exactly `1/2`).  Hence `chiScale ℓ x ≠ 0` forces `‖x‖ < ℓ/2` — strictly inside the box.
So if `chiB ℓ d u x ≠ 0`, both `x` and `x − (ℓd)·u` lie in the *open* balls of radii
`ℓ/2`, `ℓd/2`; a whole ball around `x` then lands in `dlBox ℓ d u`, so the box has
positive volume.  Contrapositively, volume `dlBox ℓ d u = 0` forces `chiB ℓ d u ≡ 0`.

This is the geometric degeneracy behind the "far set" analysis of round 8: when the two
cubes touch only along a lower-dimensional face the cutoff is identically zero.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real

namespace Work.UBBInputs8.A

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false

/-- The cutoff `χ` vanishes on the closed complement of the open ball of radius `1/2`
(the underlying bump has `rOut = 1/2`, and `zero_of_le_dist` applies at distance `1/2`). -/
lemma chi_eq_zero_of_half_le_norm (x : ℝ³) (hx : (1 : ℝ) / 2 ≤ ‖x‖) : chi x = 0 := by
  have hb : chiBase x = 0 := by
    apply chiBump.zero_of_le_dist
    simpa [chiBump, dist_eq_norm] using hx
  simp [chi, hb]

/-- **Sharp support of the scaled bump**: `chiScale ℓ x ≠ 0` forces `‖x‖ < ℓ/2`, i.e. `x`
lies strictly inside the open ball of radius `ℓ/2`. -/
lemma chiScale_norm_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {x : ℝ³} (hx : chiScale ℓ x ≠ 0) :
    ‖x‖ < ℓ / 2 := by
  by_contra h
  rw [not_lt] at h
  have hz : chi ((ℓ⁻¹) • x) = 0 := by
    apply chi_eq_zero_of_half_le_norm
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (inv_pos.mpr hℓ))]
    have h2 : (0 : ℝ) < ℓ⁻¹ := inv_pos.mpr hℓ
    have h3 : ℓ⁻¹ * ℓ = 1 := inv_mul_cancel₀ (ne_of_gt hℓ)
    nlinarith [h, h2, h3]
  exact hx hz

theorem chiB_eq_zero_of_volume_dlBox_eq_zero {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3))
    (h : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
          (Submission.BoseGases.dlBox ℓ d u) = 0) :
    Submission.BoseGases.chiB ℓ d u = 0 := by
  funext x
  by_contra hx
  have h1 : chiScale ℓ x ≠ 0 := by intro hz; exact hx (by simp [chiB, hz])
  have h2 : chiScale (ℓ * d) (x - (ℓ * d) • u) ≠ 0 := by
    intro hz; exact hx (by simp [chiB, hz])
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hn1 : ‖x‖ < ℓ / 2 := chiScale_norm_lt hℓ h1
  have hn2 : ‖x - (ℓ * d) • u‖ < ℓ * d / 2 := chiScale_norm_lt hld h2
  set r : ℝ := min (ℓ / 2 - ‖x‖) (ℓ * d / 2 - ‖x - (ℓ * d) • u‖) / 2 with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    have : 0 < min (ℓ / 2 - ‖x‖) (ℓ * d / 2 - ‖x - (ℓ * d) • u‖) :=
      lt_min (by linarith) (by linarith)
    positivity
  have hball : Metric.ball x r ⊆ dlBox ℓ d u := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    rw [mem_dlBox_iff]
    constructor
    · apply mem_acube_of_norm_le hℓ.le
      have hr1 : r < ℓ / 2 - ‖x‖ := by
        rw [hrdef]
        have hmin : min (ℓ / 2 - ‖x‖) (ℓ * d / 2 - ‖x - (ℓ * d) • u‖) ≤ ℓ / 2 - ‖x‖ :=
          min_le_left _ _
        linarith
      have hle : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
        have := norm_add_le (y - x) x
        simpa using this
      linarith
    · apply mem_acube_of_norm_le hld.le
      have hr2 : r < ℓ * d / 2 - ‖x - (ℓ * d) • u‖ := by
        rw [hrdef]
        have hmin : min (ℓ / 2 - ‖x‖) (ℓ * d / 2 - ‖x - (ℓ * d) • u‖)
            ≤ ℓ * d / 2 - ‖x - (ℓ * d) • u‖ := min_le_right _ _
        linarith
      have hle : ‖y - (ℓ * d) • u‖ ≤ ‖y - x‖ + ‖x - (ℓ * d) • u‖ := by
        have := norm_add_le (y - x) (x - (ℓ * d) • u)
        rw [sub_add_sub_cancel] at this
        exact this
      linarith
  have hpos : 0 < (volume : Measure ℝ³) (dlBox ℓ d u) := by
    have hb := Metric.measure_ball_pos (μ := (volume : Measure ℝ³)) x hrpos
    exact lt_of_lt_of_le hb (measure_mono hball)
  rw [h] at hpos
  exact lt_irrefl 0 hpos

end Work.UBBInputs8.A

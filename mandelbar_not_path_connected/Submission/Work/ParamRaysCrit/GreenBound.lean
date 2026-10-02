/-
# The Green function is `log ‖·‖` up to `log 2` above the escape radius

For `max 2 ‖c‖ < ‖w‖` the telescoping formula
`G_c w = log ‖w‖ + ∑'_n 2^{-(n+1)} log (‖T_c^{n+1} w‖ / ‖T_c^n w‖²)`
of `greenFun_eq_log_add_tsum` combined with the ratio bound
`|log (‖T_c^{n+1} w‖ / ‖T_c^n w‖²)| ≤ log 2` (`abs_log_orbit_ratio_le`) gives the two-sided
estimate

`|G_c w - log ‖w‖| ≤ ∑'_n 2^{-(n+1)} log 2 = log 2`

above the escape radius.  This is the quantitative form of the elementary fact that the Green
function is a perturbation of `log ‖·‖` by a bounded amount, and it is what makes the sets
`{G_c > r}` accessible: they are (for `r > 0`) unions of preimages of exteriors of balls under
the even iterates of `T_c`.

## Main results

* `Work.ParamRays.greenFun_le_log_add` : `G_c w ≤ log ‖w‖ + log 2`.
* `Work.ParamRays.log_sub_le_greenFun` : `log ‖w‖ - log 2 ≤ G_c w`.
* `Work.ParamRays.abs_greenFun_sub_log_le` : `|G_c w - log ‖w‖| ≤ log 2`.
* `Work.ParamRays.greenFun_pos_of_lt_exp` : `G_c w > r` when `‖w‖ > exp (r + log 2)` and
  `‖w‖ > escR c`.
* `Work.ParamRays.exists_norm_gt_greenFun` : for every `R` there is `z` with `R < ‖z‖` and
  `paramPotential c < G_c z`.
-/
import Mathlib
import Submission.Work.ParamRaysCrit.CritDomain
import Submission.Work.ParamRays.greenFun_eq_log_add_tsum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology

namespace Work.ParamRays

/-! ## The two-sided bound -/

/-- The `n`-th telescoping term of the Green series of an orbit above the escape radius. -/
noncomputable def orbitLogTerm (c w : ℂ) (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (n + 1))⁻¹ * Real.log (‖orbit c w (n + 1)‖ / ‖orbit c w n‖ ^ 2)

theorem log_orbit_ratio (c w : ℂ) (h : max 2 ‖c‖ < ‖w‖) (n : ℕ) :
    Real.log (‖orbit c w (n + 1)‖ / ‖orbit c w n‖ ^ 2) =
      Real.log ‖orbit c w (n + 1)‖ - 2 * Real.log ‖orbit c w n‖ := by
  rw [Real.log_div (orbit_norm_ne_zero c w h (n + 1))
    (pow_ne_zero 2 (orbit_norm_ne_zero c w h n)), Real.log_pow]
  push_cast
  ring

theorem norm_orbitLogTerm_le (c w : ℂ) (h : max 2 ‖c‖ < ‖w‖) (n : ℕ) :
    ‖orbitLogTerm c w n‖ ≤ ((2 : ℝ) ^ (n + 1))⁻¹ * Real.log 2 := by
  rw [orbitLogTerm, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ (n + 1))⁻¹),
    log_orbit_ratio c w h n]
  exact mul_le_mul_of_nonneg_left (abs_log_orbit_ratio_le c w h n) (by positivity)

theorem summable_orbitLogTerm_abs (c w : ℂ) (h : max 2 ‖c‖ < ‖w‖) :
    Summable fun n : ℕ => ‖orbitLogTerm c w n‖ := (summable_orbitLog c w h).norm

/-- The weights `2^{-(n+1)} log 2` are `(log 2 / 2)` times the geometric sequence `2^{-n}`. -/
theorem geomWeight_eq :
    (fun n : ℕ => ((2 : ℝ) ^ (n + 1))⁻¹ * Real.log 2) =
      fun n : ℕ => (Real.log 2 * (1 / 2 : ℝ)) * ((1 / 2 : ℝ) ^ n) := by
  funext n
  rw [← inv_pow, pow_succ]
  norm_num
  ring

theorem summable_geomWeight : Summable fun n : ℕ => ((2 : ℝ) ^ (n + 1))⁻¹ * Real.log 2 := by
  rw [geomWeight_eq]
  exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)).mul_left _

theorem tsum_geomWeight : (∑' n : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹ * Real.log 2) = Real.log 2 := by
  rw [geomWeight_eq, tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)]
  norm_num
  ring

/-- **The Green function above the escape radius is `log ‖w‖` up to `log 2`.** -/
theorem abs_greenFun_sub_log_le (c w : ℂ) (h : max 2 ‖c‖ < ‖w‖) :
    |greenFun c w - Real.log ‖w‖| ≤ Real.log 2 := by
  have htsum := greenFun_eq_log_add_tsum c w h
  have hsub : greenFun c w - Real.log ‖w‖ = ∑' n : ℕ, orbitLogTerm c w n := by
    rw [htsum, add_sub_cancel_left]
    rfl
  rw [hsub, ← Real.norm_eq_abs]
  calc ‖∑' n : ℕ, orbitLogTerm c w n‖
      ≤ ∑' n : ℕ, ‖orbitLogTerm c w n‖ := norm_tsum_le_tsum_norm (summable_orbitLogTerm_abs c w h)
    _ ≤ ∑' n : ℕ, ((2 : ℝ) ^ (n + 1))⁻¹ * Real.log 2 :=
        Summable.tsum_le_tsum (norm_orbitLogTerm_le c w h) (summable_orbitLogTerm_abs c w h)
          summable_geomWeight
    _ = Real.log 2 := tsum_geomWeight

/-- Above the escape radius, `G_c w ≤ log ‖w‖ + log 2`. -/
theorem greenFun_le_log_add (c w : ℂ) (h : max 2 ‖c‖ < ‖w‖) :
    greenFun c w ≤ Real.log ‖w‖ + Real.log 2 := by
  have := abs_greenFun_sub_log_le c w h
  rw [abs_le] at this
  linarith [this.2]

/-- Above the escape radius, `log ‖w‖ - log 2 ≤ G_c w`. -/
theorem log_sub_le_greenFun (c w : ℂ) (h : max 2 ‖c‖ < ‖w‖) :
    Real.log ‖w‖ - Real.log 2 ≤ greenFun c w := by
  have := abs_greenFun_sub_log_le c w h
  rw [abs_le] at this
  linarith [this.1]

/-! ## Consequences -/

/-- Above the escape radius `escR c = ‖c‖ + 3` (which dominates `max 2 ‖c‖`), a point of norm
`> exp (r + log 2)` has `G_c > r`. -/
theorem greenFun_pos_of_lt_exp (c w : ℂ) {r : ℝ} (hr : escR c < ‖w‖)
    (h : Real.exp (r + Real.log 2) < ‖w‖) : r < greenFun c w := by
  have hc : max 2 ‖c‖ < ‖w‖ := lt_of_lt_of_le (lt_max_escR c) hr.le
  have h1 := log_sub_le_greenFun c w hc
  have h2 : Real.log (Real.exp (r + Real.log 2)) < Real.log ‖w‖ :=
    Real.log_lt_log (Real.exp_pos _) h
  rw [Real.log_exp] at h2
  linarith

/-- **Every superlevel set of the Green function is unbounded with points of arbitrarily large
norm**, and (off the mandelbar) it contains the critical domain of every level.

For `r ≥ 0`: points of sufficiently large norm have `G_c > r` by the `log 2` bound. -/
theorem exists_norm_gt_greenFun (c : ℂ) {r R : ℝ} (_hr : 0 ≤ r) :
    ∃ z : ℂ, R < ‖z‖ ∧ r < greenFun c z := by
  set B : ℝ := max (max R (escR c)) (Real.exp (r + Real.log 2)) with hB
  have hB0 : 0 ≤ B := by
    have h1 : (0 : ℝ) < escR c := escR_pos c
    have h2 : escR c ≤ max R (escR c) := le_max_right _ _
    have h3 : max R (escR c) ≤ B := le_max_left _ _
    rw [hB]; linarith
  have hRB : R ≤ B := le_trans (le_max_left R (escR c)) (le_max_left _ _)
  have hEB : Real.exp (r + Real.log 2) ≤ B := le_max_right _ _
  have hNB : B < B + 1 := lt_add_one B
  refine ⟨((B + 1 : ℝ) : ℂ), ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  · refine greenFun_pos_of_lt_exp c _ ?_ ?_
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      have : escR c ≤ B := le_trans (le_max_right R (escR c)) (le_max_left _ _)
      linarith
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith

/-- The critical domain meets the exterior of every ball around the origin. -/
theorem exists_mem_critDomain_gt_norm (c : ℂ) (R : ℝ) :
    ∃ z : ℂ, R < ‖z‖ ∧ z ∈ critDomain c := by
  obtain ⟨z, hR, hz⟩ := exists_norm_gt_greenFun c (r := paramPotential c) (paramPotential_nonneg c)
  exact ⟨z, hR, hz⟩

end Work.ParamRays

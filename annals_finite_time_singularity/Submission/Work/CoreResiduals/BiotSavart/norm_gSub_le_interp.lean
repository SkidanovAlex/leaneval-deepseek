/-
# `Work.CoreResiduals.BiotSavart.norm_gSub_le_interp` — interpolation of the two bounds on `g`

If `g : ℝ³ → ℝ³` is uniformly bounded by `A ≥ 0` and `α`-Hölder with constant `2H ≥ 0`
(`0 < α < 1`), then the difference `g a - g x` obeys the intermediate bound

  `‖g a - g x‖ ≤ (2A)^α (2H)^{1-α} ‖x - a‖^{α(1-α)}`.

This is the elementary interpolation of the two available estimates
`‖g a - g x‖ ≤ 2A` (from boundedness of `g a` and `g x`) and
`‖g a - g x‖ ≤ 2H ‖x - a‖^α` (Hölder): writing `u = ‖g a - g x‖ ≥ 0` as
`u = u^α · u^{1-α}` and applying `Real.rpow_le_rpow` to each factor gives
`u ≤ (2A)^α (2H ‖x - a‖^α)^{1-α} = (2A)^α (2H)^{1-α} ‖x - a‖^{α(1-α)}`.
No case distinction is needed: all `rpow` lemmas used here are valid for the zero base.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

theorem norm_gSub_le_interp {α A H : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hA : 0 ≤ A) (hH : 0 ≤ H)
    {g : Work.LWP.R3 → Work.LWP.R3} (hbdd : ∀ a, ‖g a‖ ≤ A)
    (hhold : ∀ a b : Work.LWP.R3, ‖g a - g b‖ ≤ 2 * H * ‖a - b‖ ^ α)
    (x a : Work.LWP.R3) :
    ‖g a - g x‖ ≤ (2 * A) ^ α * (2 * H) ^ (1 - α) * ‖x - a‖ ^ (α * (1 - α)) := by
  set u : ℝ := ‖g a - g x‖ with hu_def
  set t : ℝ := ‖x - a‖ with ht_def
  have hu : 0 ≤ u := by rw [hu_def]; exact norm_nonneg _
  have ht : 0 ≤ t := by rw [ht_def]; exact norm_nonneg _
  have h2A : 0 ≤ 2 * A := by linarith
  have h2H : 0 ≤ 2 * H := by linarith
  -- the two bounds on `u = ‖g a - g x‖`
  have hbdd' : u ≤ 2 * A := by
    rw [hu_def]
    calc ‖g a - g x‖ ≤ ‖g a‖ + ‖g x‖ := norm_sub_le _ _
      _ ≤ A + A := add_le_add (hbdd a) (hbdd x)
      _ = 2 * A := by ring
  have hhold' : u ≤ 2 * H * t ^ α := by
    rw [hu_def, ht_def]
    have h := hhold a x
    rw [norm_sub_rev a x] at h
    exact h
  -- split `u` as `u^α · u^{1-α}`
  have hkey : u = u ^ α * u ^ (1 - α) := by
    have h := Real.rpow_add' hu (x := u) (y := α) (z := 1 - α) (by linarith)
    rw [show α + (1 - α) = 1 by ring, Real.rpow_one] at h
    exact h
  -- apply `rpow_le_rpow` to each factor
  have hA_le : u ^ α ≤ (2 * A) ^ α := Real.rpow_le_rpow hu hbdd' hα.le
  have hH_le : u ^ (1 - α) ≤ (2 * H * t ^ α) ^ (1 - α) :=
    Real.rpow_le_rpow hu hhold' (by linarith)
  calc u = u ^ α * u ^ (1 - α) := hkey
    _ ≤ (2 * A) ^ α * (2 * H * t ^ α) ^ (1 - α) :=
        mul_le_mul hA_le hH_le (Real.rpow_nonneg hu _) (Real.rpow_nonneg h2A _)
    _ = (2 * A) ^ α * (2 * H) ^ (1 - α) * t ^ (α * (1 - α)) := by
        rw [Real.mul_rpow h2H (Real.rpow_nonneg ht α), ← Real.rpow_mul ht]
        ring

end Work.CoreResiduals.BiotSavart

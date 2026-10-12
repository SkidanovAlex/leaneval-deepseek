import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseRowsFS.RowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS

open MeasureTheory Set

/-! ## The far-regime bound on the time-truncated heat kernel

For `‖z‖² ≥ 6` the heat kernel `s ↦ Kt s z = (4πs)^{-3/2}e^{-‖z‖²/(4s)}` is *increasing*
on `(0,1]`, with maximum at `s = 1`.  Therefore

  `∫_{0 < s ≤ 1} Kt s z ds ≤ Kt 1 z = (4π)^{-3/2} e^{-‖z‖²/4}`,

which is the lemma `ssb_Kt_Ioc_far_le`.

The monotonicity is the elementary inequality
`-(3/2)·log s ≤ ‖z‖²(1-s)/(4s)` for `0 < s ≤ 1`, `‖z‖² ≥ 6`
(equivalently `s^{-3/2}e^{-‖z‖²/(4s)} ≤ e^{-‖z‖²/4}`), which follows from
`log(1/s) ≤ 1/s - 1`. -/

/-- Elementary log inequality: for `a ≥ 6` and `0 < s ≤ 1`,
`-(3/2)·log s ≤ a (1-s)/(4s)`. -/
lemma ssb_key {a s : ℝ} (ha : 6 ≤ a) (hs : 0 < s) (hs1 : s ≤ 1) :
    -(3/2 : ℝ) * Real.log s ≤ a * (1 - s) / (4 * s) := by
  have h1 : Real.log s⁻¹ ≤ s⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_inv] at h1
  have h2 : -(3/2 : ℝ) * Real.log s ≤ (3/2 : ℝ) * (s⁻¹ - 1) := by linarith
  have h3 : (3/2 : ℝ) * (s⁻¹ - 1) = 3 * (1 - s) / (2 * s) := by field_simp
  have h34 : (3 : ℝ) / (2 * s) ≤ a / (4 * s) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [ha, hs]
  have h4 : 3 * (1 - s) / (2 * s) ≤ a * (1 - s) / (4 * s) := by
    have e1 : 3 * (1 - s) / (2 * s) = (3 / (2 * s)) * (1 - s) := by ring
    have e2 : a * (1 - s) / (4 * s) = (a / (4 * s)) * (1 - s) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right h34 (by linarith)
  linarith

/-- Monotonicity of the heat kernel at fixed far-away `z`: `Kt s z ≤ Kt 1 z` for
`0 < s ≤ 1`, `‖z‖² ≥ 6`. -/
lemma Kt_le_Kt_one {z : EuclideanSpace ℝ (Fin 3)} (hz : 6 ≤ ‖z‖ ^ 2)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) : Kt s z ≤ Kt 1 z := by
  have hA : (0 : ℝ) < 4 * Real.pi := by positivity
  have hkey : -(3/2 : ℝ) * Real.log s ≤ ‖z‖ ^ 2 * (1 - s) / (4 * s) :=
    ssb_key hz hs hs1
  rw [Kt, Kt]
  have hfac : (4 * Real.pi * s) ^ (-(3/2 : ℝ)) = (4 * Real.pi) ^ (-(3/2 : ℝ)) * s ^ (-(3/2 : ℝ)) :=
    Real.mul_rpow hA.le hs.le
  have hone : (4 * Real.pi * 1) ^ (-(3/2 : ℝ)) = (4 * Real.pi) ^ (-(3/2 : ℝ)) := by norm_num
  rw [hfac, hone, mul_one]
  rw [mul_assoc, mul_le_mul_iff_of_pos_left (Real.rpow_pos_of_pos hA _)]
  rw [Real.rpow_def_of_pos hs, ← Real.exp_add, Real.exp_le_exp]
  have h1 : Real.log s * (-(3/2)) ≤ ‖z‖ ^ 2 * (1 - s) / (4 * s) := by
    rw [mul_comm (Real.log s)]; exact hkey
  have h2 : ‖z‖ ^ 2 * (1 - s) / (4 * s) + (-(‖z‖ ^ 2) / (4 * s)) = -(‖z‖ ^ 2) / 4 := by
    field_simp
    ring
  rw [← h2]
  linarith [h1]

theorem ssb_Kt_Ioc_far_le {z : EuclideanSpace ℝ (Fin 3)} (hz : 6 ≤ ‖z‖ ^ 2) :
    (∫ s in Set.Ioc (0 : ℝ) 1, Kt s z) ≤ (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * Real.exp (-‖z‖ ^ 2 / 4) := by
  have hpt : ∀ s ∈ Set.Ioc (0 : ℝ) 1, Kt s z ≤ Kt 1 z :=
    fun s hs => Kt_le_Kt_one hz hs.1 hs.2
  have hfnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] (fun s : ℝ => Kt s z) := by
    change ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), (0 : ℝ) ≤ Kt s z
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with s hs
    exact Kt_nonneg hs.1 z
  have hle : (fun s : ℝ => Kt s z) ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (fun _ : ℝ => Kt 1 z) := by
    change ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), Kt s z ≤ Kt 1 z
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with s hs
    exact hpt s hs
  have hgint : Integrable (fun _ : ℝ => Kt 1 z) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [integrable_const_iff]
    right
    rw [isFiniteMeasure_iff, Measure.restrict_apply_univ, Real.volume_Ioc]
    norm_num
  have hmain := integral_mono_of_nonneg hfnn hgint hle
  calc (∫ s in Set.Ioc (0 : ℝ) 1, Kt s z)
      ≤ ∫ s in Set.Ioc (0 : ℝ) 1, Kt 1 z := hmain
    _ = Kt 1 z := by
        rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        rw [intervalIntegral.integral_const]
        simp
    _ = (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * Real.exp (-‖z‖ ^ 2 / 4) := by
        rw [Kt]; norm_num

end Work.BoseRowsFS

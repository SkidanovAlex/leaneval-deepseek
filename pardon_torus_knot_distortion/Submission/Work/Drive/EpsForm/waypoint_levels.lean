import Mathlib
import Submission.Work.Drive.EpsForm.WaypointDesign

namespace Work.Drive.EpsForm

open Set

/-! ## Elementary facts about the waypoint design

The design functions `bump`, `sig1`, `sig2`, `tauP`, `dlt` of `WaypointDesign`
are continuous, satisfy `bump = cos (3t/4)`, hence `bump` is negative on the
second waypoint range `(v0, u0 + 2π)`, and they take the value `1` (resp. `0`
for `dlt`) at the endpoints `u0`, `v0`. -/

/-- `bump` is the cosine `cos (3t/4)`. -/
theorem bump_eq_cos (t : ℝ) : bump t = Real.cos (3 * t / 4) := by
  have h1 : Real.pi * (t - u0) / (v0 - u0) = 3 * t / 4 + Real.pi / 2 := by
    unfold u0 v0; field_simp; ring
  unfold bump
  rw [h1, Real.sin_add_pi_div_two]

/-- `bump` is negative on `(v0, u0 + 2π)`. -/
theorem bump_neg {t : ℝ} (hv : v0 < t) (hu : t < u0 + 2 * Real.pi) : bump t < 0 := by
  rw [bump_eq_cos]
  apply Real.cos_neg_of_pi_div_two_lt_of_lt
  · simp only [v0] at hv ⊢; linarith [Real.pi_pos]
  · simp only [u0] at hu ⊢; linarith [Real.pi_pos]

theorem continuous_bump : Continuous bump := by unfold bump; fun_prop
theorem continuous_sig1 : Continuous sig1 := by unfold sig1 bump; fun_prop
theorem continuous_sig2 : Continuous sig2 := by unfold sig2 bump; fun_prop
theorem continuous_tauP : Continuous tauP := by unfold tauP sig2 bump; fun_prop
theorem continuous_dlt : Continuous dlt := by unfold dlt bump; fun_prop

theorem tauP_u0 : tauP u0 = 1 := by unfold tauP; rw [sig2_u0]; norm_num
theorem tauP_v0 : tauP v0 = 1 := by unfold tauP; rw [sig2_v0]; norm_num

theorem waypoint_levels :
    (∀ t : ℝ, u0 < t → t < v0 → (0 < sig1 t ∧ sig1 t < sig2 t ∧ sig2 t < tauP t ∧ tauP t < 1))
    ∧ (∀ t : ℝ, v0 < t → t < u0 + 2 * Real.pi → (0 < -bump t ∧ 1 < sig1 t ∧ 1 < sig2 t ∧ 1 < tauP t))
    ∧ Filter.Tendsto sig1 (nhdsWithin u0 (Set.Ioi u0)) (nhds 1)
    ∧ Filter.Tendsto sig1 (nhdsWithin v0 (Set.Iio v0)) (nhds 1)
    ∧ Filter.Tendsto sig2 (nhdsWithin u0 (Set.Ioi u0)) (nhds 1)
    ∧ Filter.Tendsto sig2 (nhdsWithin v0 (Set.Iio v0)) (nhds 1)
    ∧ Filter.Tendsto tauP (nhdsWithin u0 (Set.Ioi u0)) (nhds 1)
    ∧ Filter.Tendsto tauP (nhdsWithin v0 (Set.Iio v0)) (nhds 1)
    ∧ Filter.Tendsto dlt (nhdsWithin u0 (Set.Ioi u0)) (nhds 0)
    ∧ Filter.Tendsto dlt (nhdsWithin v0 (Set.Iio v0)) (nhds 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t hu hv
    have hb := bump_pos hu hv
    have hle : bump t ≤ 1 := Real.sin_le_one _
    refine ⟨?_, sig1_lt_sig2 hu hv, sig2_lt_tauP hu hv, tauP_lt_one hu hv⟩
    unfold sig1
    nlinarith
  · intro t hv hu
    have hb : bump t < 0 := bump_neg hv hu
    refine ⟨by linarith, ?_, ?_, ?_⟩
    · unfold sig1; linarith
    · unfold sig2; linarith
    · unfold tauP sig2; linarith
  · simpa [sig1_u0] using
      (continuous_sig1.continuousAt (x := u0)).tendsto.mono_left nhdsWithin_le_nhds
  · simpa [sig1_v0] using
      (continuous_sig1.continuousAt (x := v0)).tendsto.mono_left nhdsWithin_le_nhds
  · simpa [sig2_u0] using
      (continuous_sig2.continuousAt (x := u0)).tendsto.mono_left nhdsWithin_le_nhds
  · simpa [sig2_v0] using
      (continuous_sig2.continuousAt (x := v0)).tendsto.mono_left nhdsWithin_le_nhds
  · simpa [tauP_u0] using
      (continuous_tauP.continuousAt (x := u0)).tendsto.mono_left nhdsWithin_le_nhds
  · simpa [tauP_v0] using
      (continuous_tauP.continuousAt (x := v0)).tendsto.mono_left nhdsWithin_le_nhds
  · simpa [dlt_u0] using
      (continuous_dlt.continuousAt (x := u0)).tendsto.mono_left nhdsWithin_le_nhds
  · simpa [dlt_v0] using
      (continuous_dlt.continuousAt (x := v0)).tendsto.mono_left nhdsWithin_le_nhds

end Work.Drive.EpsForm

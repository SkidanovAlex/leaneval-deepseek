import Mathlib
import Submission.Commons.Analysis.Complex.Harmonic.harnack_inequality
import Submission.Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le
import Submission.Work.Drive.montelHarmonicBall

noncomputable section

open Set Metric

namespace Work.Drive

/-- **Oscillation estimate on concentric spheres for harmonic functions.**  If `u` is harmonic on a
neighbourhood of the closed ball of radius `R` about `c` and is bounded by `M` above and `m` below on
the sphere of radius `R`, then on the (closed) ball of radius `ρ < R` the oscillation of `u` is at
most `((R+ρ)/(R-ρ) - (R-ρ)/(R+ρ))` times `M - m`.

Proof: `v := u - m` is `≥ 0` on the closed ball (minimum principle, using `hm` and
`HarmonicOnNhd u (closedBall c R)`), harmonic there, so Harnack's inequality on the disc applies at
`c` (`Commons/Analysis/Complex/Harmonic/harnack_inequality.lean`,
`Submission.harnack_inequality`, for the unit disc; translate/scale to `c`, `R`), while
`v c ≤ M - m` by the maximum principle.  Hence for `z` with `dist z c ≤ ρ`:
`v z ≤ ((R+ρ)/(R-ρ)) (M-m)` and `v z ≥ ((R-ρ)/(R+ρ)) (M-m)`, giving the claim in the form
`((R+ρ)/(R-ρ) - (R-ρ)/(R+ρ)) (M - m)`. -/
theorem osc_sphere_le_of_harmonicOnNhd {u : ℂ → ℝ} {c : ℂ} {R ρ M m : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρR : ρ < R)
    (hu : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall c R))
    (hM : ∀ z : ℂ, dist z c = R → u z ≤ M) (hm : ∀ z : ℂ, dist z c = R → m ≤ u z) :
    ∀ x y : ℂ, dist x c ≤ ρ → dist y c ≤ ρ →
      u x - u y ≤ ((R + ρ) / (R - ρ) - (R - ρ) / (R + ρ)) * (M - m) := by
  have hRsub : 0 < R - ρ := by linarith
  have hRadd : 0 < R + ρ := by linarith
  -- The shifted function `v = u - m`, harmonic on the closed ball.
  set v : ℂ → ℝ := fun z => u z - m with hv_def
  have hv_apply : ∀ z : ℂ, v z = u z - m := by intro z; simp [hv_def]
  have hvh : InnerProductSpace.HarmonicOnNhd v (Metric.closedBall c R) := by
    have h : v = u - fun _ : ℂ => m := by funext z; simp [hv_apply]
    rw [h]
    exact hu.sub (InnerProductSpace.harmonicOnNhd_const m)
  have hv_cont : ContinuousOn v (Metric.closedBall c R) := hvh.continuousOn
  -- `v ≥ 0` on the sphere of radius `R`.
  have hvnn_sphere : ∀ z : ℂ, z ∈ Metric.sphere c R → 0 ≤ v z := by
    intro z hz
    have h := hm z (Metric.mem_sphere.mp hz)
    rw [hv_apply z]
    linarith
  -- Minimum principle: `v ≥ 0` on the open ball.
  have hvnn_ball : ∀ z : ℂ, ‖z - c‖ < R → 0 ≤ v z := by
    have hFb : ∀ z : ℂ, z ∈ Metric.sphere c R → (fun w : ℂ => -v w) z ≤ (0 : ℝ) := by
      intro z hz
      have h := hvnn_sphere z hz
      linarith
    have hAt : ∀ z : ℂ, ‖z - c‖ < R → InnerProductSpace.HarmonicAt (fun w : ℂ => -v w) z := by
      intro z hz
      have hzmem : z ∈ Metric.closedBall c R := by
        rw [Metric.mem_closedBall, dist_eq_norm]; exact le_of_lt hz
      exact (hvh z hzmem).neg
    have hcont : ContinuousOn
        (fun z : ℂ => if ‖z - c‖ < R then (fun w : ℂ => -v w) z else (fun w : ℂ => -v w) z)
        (Metric.closedBall c R) := by
      have h : (fun z : ℂ => if ‖z - c‖ < R then -v z else -v z) = fun z => -v z := by
        funext z; by_cases h : ‖z - c‖ < R <;> simp [h]
      rw [h]
      exact hv_cont.neg
    intro z hz
    have h : -v z ≤ 0 := by
      simpa using Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le
        (c := c) (R := R) (M := (0 : ℝ)) hR hFb hAt hcont z hz
    linarith
  -- `v ≥ 0` on the closed ball.
  have hvnn_closed : ∀ z ∈ Metric.closedBall c R, 0 ≤ v z := by
    intro z hz
    rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hz) with hlt | heq
    · exact hvnn_ball z (by rwa [dist_eq_norm] at hlt)
    · exact hvnn_sphere z (Metric.mem_sphere.mpr heq)
  have hvc_nn : 0 ≤ v c := hvnn_closed c (Metric.mem_closedBall_self (le_of_lt hR))
  -- Maximum principle: `u ≤ M` on the open ball, in particular `u c ≤ M`.
  have hucM : u c ≤ M := by
    have hFb : ∀ z : ℂ, z ∈ Metric.sphere c R → u z ≤ M :=
      fun z hz => hM z (Metric.mem_sphere.mp hz)
    have hAt : ∀ z : ℂ, ‖z - c‖ < R → InnerProductSpace.HarmonicAt u z := by
      intro z hz
      exact hu z (by rw [Metric.mem_closedBall, dist_eq_norm]; exact le_of_lt hz)
    have hcont : ContinuousOn (fun z : ℂ => if ‖z - c‖ < R then u z else u z)
        (Metric.closedBall c R) := by
      have h : (fun z : ℂ => if ‖z - c‖ < R then u z else u z) = u := by
        funext z; by_cases h : ‖z - c‖ < R <;> simp [h]
      rw [h]
      exact hu.continuousOn
    exact Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le
      (c := c) (R := R) (M := M) hR (F := u) hFb (u := u) hAt hcont c
      (by rw [sub_self, norm_zero]; exact hR)
  have hvc_le : v c ≤ M - m := by rw [hv_apply c]; linarith
  -- Harnack at an arbitrary point of the closed ball of radius `ρ`.
  intro x y hx hy
  have hxρ : ‖x - c‖ ≤ ρ := by rw [← dist_eq_norm]; exact hx
  have hyρ : ‖y - c‖ ≤ ρ := by rw [← dist_eq_norm]; exact hy
  have hxlt : ‖x - c‖ < R := lt_of_le_of_lt hxρ hρR
  have hylt : ‖y - c‖ < R := lt_of_le_of_lt hyρ hρR
  obtain ⟨hxlo, hxhi⟩ := harnack_inequality_center (f := v) (c := c) (ρ := R) hR hvh hvnn_closed
    (x := x) hxlt
  obtain ⟨hylo, hyhi⟩ := harnack_inequality_center (f := v) (c := c) (ρ := R) hR hvh hvnn_closed
    (x := y) hylt
  have hαle : (R + ‖x - c‖) / (R - ‖x - c‖) ≤ (R + ρ) / (R - ρ) := by
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < R - ‖x - c‖) hRsub]
    nlinarith [norm_nonneg (x - c)]
  have hβle : (R - ρ) / (R + ρ) ≤ (R - ‖y - c‖) / (R + ‖y - c‖) := by
    rw [div_le_div_iff₀ hRadd (by linarith [norm_nonneg (y - c)] : (0 : ℝ) < R + ‖y - c‖)]
    nlinarith [norm_nonneg (y - c)]
  have hx_bound : v x ≤ ((R + ρ) / (R - ρ)) * v c :=
    le_trans hxhi (mul_le_mul_of_nonneg_right hαle hvc_nn)
  have hy_bound : ((R - ρ) / (R + ρ)) * v c ≤ v y :=
    le_trans (mul_le_mul_of_nonneg_right hβle hvc_nn) hylo
  have hcoef : 0 ≤ (R + ρ) / (R - ρ) - (R - ρ) / (R + ρ) := by
    have h1 : (1 : ℝ) ≤ (R + ρ) / (R - ρ) := by
      rw [le_div_iff₀ hRsub, one_mul]; linarith
    have h2 : (R - ρ) / (R + ρ) ≤ 1 := by
      rw [div_le_one hRadd]; linarith
    linarith
  calc u x - u y = v x - v y := by rw [hv_apply x, hv_apply y]; ring
    _ ≤ ((R + ρ) / (R - ρ)) * v c - ((R - ρ) / (R + ρ)) * v c := by linarith
    _ = ((R + ρ) / (R - ρ) - (R - ρ) / (R + ρ)) * v c := by ring
    _ ≤ ((R + ρ) / (R - ρ) - (R - ρ) / (R + ρ)) * (M - m) :=
        mul_le_mul_of_nonneg_left hvc_le hcoef

end Work.Drive

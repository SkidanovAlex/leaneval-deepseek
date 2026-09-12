import Mathlib
import Submission.E2bCells
import Submission.DirSet
import Submission.StarGeom

/-!
# Star-free rays: radial integrability of the window-edge segments

The six integrability families of `Submission.E2bAssembly.circle_eq_cap_sum_x`
include the radial segments at the window-edge angles `x_j ± δ` (over
`[A, u_j]` and `[u_j, B]`).  A ray `{exp(t + θ·I) : t ∈ [A,B]}` avoids the
hedgehog iff no spike endpoint has argument congruent to `θ` modulo `2π`
(star points other than the origin have the argument of their endpoint; the
origin is never attained by `exp`).  This module records that fact
(`exp_ray_not_mem_star_of_not_dir`) and its integrability consequence
(`radial_integrable_of_angle_free`, via
`Submission.E2bCells.intervalIntegrable_pull_radial`), together with the
arc-at-radius-`B` version (`arcB_integrable_any`): the whole circle
`|X| = e^B` is star-free when `B` is above every spike tip.
-/

noncomputable section
open scoped Complex Real Interval BigOperators
open Complex
open MeasureTheory

namespace Submission.RadialFree

open Submission.DirSet
open Submission.StarGeom
open Submission.E2bCells

/-- A point `exp(t + θ·I)` is never on the hedgehog when no spike-endpoint
argument is congruent to `θ` modulo `2π`. -/
lemma exp_ray_not_mem_star_of_not_dir {S : Finset ℂ} {θ : ℝ}
    (hno : ∀ d ∈ dirSet S, d ≠ toIocMod Real.two_pi_pos (-Real.pi) θ)
    (t : ℝ) : Complex.exp (t + θ * Complex.I) ∉ Submission.XTransfer.star S := by
  intro hX
  change ∃ z ∈ S, Complex.exp (t + θ * Complex.I) ∈ segment ℝ 0 (z ^ 2) ∨
      Complex.exp (t + θ * Complex.I) ∈ segment ℝ 0 (z ^ 4) at hX
  rcases hX with ⟨z, hz, hseg⟩
  have hX0 : Complex.exp (t + θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hargX : Complex.arg (Complex.exp (t + θ * Complex.I)) =
      toIocMod Real.two_pi_pos (-Real.pi) θ := by
    rw [Complex.arg_exp]
    simp
  rcases hseg with h2 | h4
  · have harg2 : Complex.arg (z ^ 2) = toIocMod Real.two_pi_pos (-Real.pi) θ := by
      calc
        Complex.arg (z ^ 2) = Complex.arg (Complex.exp (t + θ * Complex.I)) :=
          (StarGeom.arg_eq_of_mem_segment_zero_ne_zero h2 hX0).symm
        _ = toIocMod Real.two_pi_pos (-Real.pi) θ := hargX
    exact (hno (Complex.arg (z ^ 2)) (arg_sq_mem_dirSet hz)) harg2
  · have harg4 : Complex.arg (z ^ 4) = toIocMod Real.two_pi_pos (-Real.pi) θ := by
      calc
        Complex.arg (z ^ 4) = Complex.arg (Complex.exp (t + θ * Complex.I)) :=
          (StarGeom.arg_eq_of_mem_segment_zero_ne_zero h4 hX0).symm
        _ = toIocMod Real.two_pi_pos (-Real.pi) θ := hargX
    exact (hno (Complex.arg (z ^ 4)) (arg_pow4_mem_dirSet hz)) harg4

/-- Radial segments at an angle-free direction are integrable. -/
theorem radial_integrable_of_angle_free (S : Finset ℂ)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (A B : ℝ) {θ : ℝ}
    (hno : ∀ d ∈ dirSet S, d ≠ toIocMod Real.two_pi_pos (-Real.pi) θ) :
    IntervalIntegrable (fun t : ℝ =>
      Submission.E2bCore.pull h (t + θ * Complex.I)) volume A B := by
  exact E2bCells.intervalIntegrable_pull_radial S hh (a := A) (b := B) (c := θ) (by
    intro t ht
    exact exp_ray_not_mem_star_of_not_dir hno t)

/-- A star point has norm at most its endpoint norm. -/
lemma norm_le_of_mem_star {S : Finset ℂ} {X : ℂ} (hX : X ∈ Submission.XTransfer.star S) :
    ∃ w ∈ spikeEndpoints S, ‖X‖ ≤ ‖w‖ := by
  change ∃ z ∈ S, X ∈ segment ℝ 0 (z ^ 2) ∨ X ∈ segment ℝ 0 (z ^ 4) at hX
  rcases hX with ⟨z, hz, hseg⟩
  rcases hseg with h2 | h4
  · refine ⟨z ^ 2, spikeEndpoints_mem_sq S hz, ?_⟩
    rcases (Submission.XTransfer.mem_segment_zero_iff (z ^ 2) X).mp h2 with ⟨t, ht01, htX⟩
    calc
      ‖X‖ = ‖t • (z ^ 2)‖ := by rw [htX]
      _ = t * ‖z ^ 2‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht01.1]
      _ ≤ ‖z ^ 2‖ := mul_le_of_le_one_left (norm_nonneg (z ^ 2)) ht01.2
  · refine ⟨z ^ 4, spikeEndpoints_mem_pow4 S hz, ?_⟩
    rcases (Submission.XTransfer.mem_segment_zero_iff (z ^ 4) X).mp h4 with ⟨t, ht01, htX⟩
    calc
      ‖X‖ = ‖t • (z ^ 4)‖ := by rw [htX]
      _ = t * ‖z ^ 4‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht01.1]
      _ ≤ ‖z ^ 4‖ := mul_le_of_le_one_left (norm_nonneg (z ^ 4)) ht01.2

/-- The whole circle `|X| = e^B` is star-free when `B` is above every spike
tip. -/
lemma circleB_not_mem_star {S : Finset ℂ} {B : ℝ}
    (hBigB : ∀ w ∈ spikeEndpoints S, ‖w‖ < Real.exp B) :
    ∀ X : ℂ, X ∈ Metric.sphere (0 : ℂ) (Real.exp B) → X ∉ Submission.XTransfer.star S := by
  intro X hX hXs
  have hnorm : ‖X‖ = Real.exp B := by
    have := (mem_sphere_zero_iff_norm.mp hX)
    exact this
  rcases norm_le_of_mem_star hXs with ⟨w, hw, hle⟩
  have hlt : ‖w‖ < Real.exp B := hBigB w hw
  linarith

/-- Arc at radius `e^B` over any real angular range is integrable (the whole
circle is star-free by `hBigB`). -/
theorem arcB_integrable_any (S : Finset ℂ)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (B : ℝ) {c d : ℝ}
    (hBigB : ∀ w ∈ spikeEndpoints S, ‖w‖ < Real.exp B) :
    IntervalIntegrable (fun y : ℝ =>
      Submission.E2bCore.pull h (B + y * Complex.I)) volume c d := by
  exact E2bCells.intervalIntegrable_pull_arc S hh B (by
    intro y hy
    apply circleB_not_mem_star hBigB (Complex.exp (B + y * Complex.I))
    rw [mem_sphere_zero_iff_norm, Complex.norm_exp]
    simp)

end Submission.RadialFree

end

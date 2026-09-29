import Mathlib
import Submission.Work.CPhi.cdt_defs

namespace Work.CPhi

open Complex Metric
open Submission.CDTPlan

/-- `phiC = hauptH ∘ psiC` maps the unit ball into the unit ball: `‖psiC z‖ ≤ 3/4`. -/
theorem phiC_mapsTo (hP : Submission.CDTPlan.PsiCFacts) :
    Set.MapsTo Submission.CDTPlan.psiC (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  obtain ⟨hP_cont, hP_diff, hP_zero, hP_deriv, hP_bound, hP_inj⟩ := hP
  intro z hz
  have h1 : ‖Submission.CDTPlan.psiC z‖ ≤ 3 / 4 :=
    hP_bound z (Metric.ball_subset_closedBall hz)
  simp only [mem_ball, dist_zero_right]
  linarith

/-- `phiC = hauptH ∘ psiC` is holomorphic on the unit ball. -/
theorem phiC_differentiableOn (hM : Submission.CDTPlan.HauptFacts)
    (hP : Submission.CDTPlan.PsiCFacts) :
    DifferentiableOn ℂ Submission.CDTPlan.phiC (ball (0 : ℂ) 1) := by
  obtain ⟨hM_diff, hM_deriv, hM_zero, k, hk_diff, hk_eq⟩ := hM
  obtain ⟨hP_cont, hP_diff, hP_zero, hP_deriv, hP_bound, hP_inj⟩ := hP
  show DifferentiableOn ℂ (Submission.CDTPlan.hauptH ∘ Submission.CDTPlan.psiC)
    (ball (0 : ℂ) 1)
  exact hM_diff.comp hP_diff (phiC_mapsTo ⟨hP_cont, hP_diff, hP_zero, hP_deriv, hP_bound, hP_inj⟩)

/-- The complex derivative of `phiC` at `0`. -/
theorem phiC_deriv_zero (hM : Submission.CDTPlan.HauptFacts)
    (hP : Submission.CDTPlan.PsiCFacts) :
    deriv Submission.CDTPlan.phiC 0 = -256 * (-(1287 / 2516)) := by
  obtain ⟨hM_diff, hM_deriv, hM_zero, k, hk_diff, hk_eq⟩ := hM
  obtain ⟨hP_cont, hP_diff, hP_zero, hP_deriv, hP_bound, hP_inj⟩ := hP
  have h1 : DifferentiableAt ℂ Submission.CDTPlan.psiC 0 :=
    hP_diff.differentiableAt (Metric.ball_mem_nhds _ zero_lt_one)
  have h2 : DifferentiableAt ℂ Submission.CDTPlan.hauptH (Submission.CDTPlan.psiC 0) := by
    rw [hP_zero]
    exact hM_diff.differentiableAt (Metric.ball_mem_nhds _ zero_lt_one)
  change deriv (Submission.CDTPlan.hauptH ∘ Submission.CDTPlan.psiC) 0 =
    -256 * (-(1287 / 2516))
  rw [deriv_comp (x := (0 : ℂ)) h2 h1, hP_zero, hM_deriv, hP_deriv]

theorem phiC_analytic (hM : Submission.CDTPlan.HauptFacts) (hP : Submission.CDTPlan.PsiCFacts) :
    DifferentiableOn ℂ Submission.CDTPlan.phiC (Metric.ball (0 : ℂ) 1) ∧
    Submission.CDTPlan.phiC 0 = 0 ∧
    deriv Submission.CDTPlan.phiC 0 = -256 * (-(1287 / 2516)) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, ‖Submission.CDTPlan.psiC z‖ ≤ 3 / 4) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, Submission.CDTPlan.phiC z = 0 → z = 0) ∧
    (∃ k : ℂ → ℂ, DifferentiableOn ℂ k (Metric.ball (0 : ℂ) 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1,
        Submission.CDTPlan.phiC z - 4 = k (Submission.CDTPlan.psiC z) ^ 2) ∧
      ∀ q ∈ Metric.ball (0 : ℂ) 1, Submission.CDTPlan.hauptH q - 4 = k q ^ 2) := by
  obtain ⟨hM_diff, hM_deriv, hM_zero, k, hk_diff, hk_eq⟩ := hM
  obtain ⟨hP_cont, hP_diff, hP_zero, hP_deriv, hP_bound, hP_inj⟩ := hP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `DifferentiableOn ℂ phiC (ball 0 1)`
    show DifferentiableOn ℂ (Submission.CDTPlan.hauptH ∘ Submission.CDTPlan.psiC)
      (ball (0 : ℂ) 1)
    refine hM_diff.comp hP_diff ?_
    intro z hz
    have h1 : ‖Submission.CDTPlan.psiC z‖ ≤ 3 / 4 :=
      hP_bound z (Metric.ball_subset_closedBall hz)
    simp only [mem_ball, dist_zero_right]
    linarith
  · -- `phiC 0 = 0`
    simp [Submission.CDTPlan.phiC, hP_zero, Submission.CDTPlan.hauptH]
  · -- `deriv phiC 0 = -256 * (-(1287 / 2516))`
    exact phiC_deriv_zero ⟨hM_diff, hM_deriv, hM_zero, k, hk_diff, hk_eq⟩
      ⟨hP_cont, hP_diff, hP_zero, hP_deriv, hP_bound, hP_inj⟩
  · -- `‖psiC z‖ ≤ 3/4` on the ball
    intro z hz
    exact hP_bound z (Metric.ball_subset_closedBall hz)
  · -- `phiC z = 0 → z = 0`
    intro z hz hzero
    have hb : Submission.CDTPlan.psiC z ∈ ball (0 : ℂ) 1 := by
      have h1 : ‖Submission.CDTPlan.psiC z‖ ≤ 3 / 4 :=
        hP_bound z (Metric.ball_subset_closedBall hz)
      simp only [mem_ball, dist_zero_right]
      linarith
    have h0 : Submission.CDTPlan.psiC z = 0 :=
      hM_zero (Submission.CDTPlan.psiC z) hb (by simpa [Submission.CDTPlan.phiC] using hzero)
    exact hP_inj z (Metric.ball_subset_closedBall hz) h0
  · -- the square root of `phiC - 4` and of `hauptH - 4`
    refine ⟨k, hk_diff, ?_, hk_eq⟩
    intro z hz
    have hb : Submission.CDTPlan.psiC z ∈ ball (0 : ℂ) 1 := by
      have h1 : ‖Submission.CDTPlan.psiC z‖ ≤ 3 / 4 :=
        hP_bound z (Metric.ball_subset_closedBall hz)
      simp only [mem_ball, dist_zero_right]
      linarith
    simpa [Submission.CDTPlan.phiC] using hk_eq (Submission.CDTPlan.psiC z) hb

end Work.CPhi

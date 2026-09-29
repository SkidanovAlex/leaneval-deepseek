import Mathlib
import Submission.Work.CPhi.phiC_analytic

namespace Work.CPull

open Complex Metric Filter Topology

/-- Data for the pullback analysis of `phiC = h ∘ ψ_C`: a holomorphic square root `K` of
`phiC - 4` on the unit disc (twice differentiable, as `K` is holomorphic there), nonvanishing at
`0`, together with a radius `r` on which `‖phiC‖ ≤ 3/4` and `K ≠ 0`.  All analytic inputs are
`phiC_analytic` (from `HauptFacts`/`PsiCFacts`) plus continuity of `phiC`, `K` at `0`. -/
theorem phiC_K_data (hM : Submission.CDTPlan.HauptFacts) (hP : Submission.CDTPlan.PsiCFacts) :
    ∃ (K : ℂ → ℂ) (r : ℝ), 0 < r ∧ r ≤ 1 ∧
      DifferentiableOn ℂ K (Metric.ball (0 : ℂ) 1) ∧
      DifferentiableOn ℂ (deriv K) (Metric.ball (0 : ℂ) 1) ∧
      K 0 ≠ 0 ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, Submission.CDTPlan.phiC z - 4 = K z ^ 2) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, Submission.CDTPlan.phiC z = 0 → z = 0) ∧
      Submission.CDTPlan.phiC 0 = 0 ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r, ‖Submission.CDTPlan.phiC z‖ ≤ 3 / 4) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r, K z ≠ 0) := by
  obtain ⟨hφdiff, hφ0, _hφderiv, _hψle, hφzero, _hrest⟩ := Work.CPhi.phiC_analytic hM hP
  obtain ⟨_, _, _, k, hk_diff, hk_eq⟩ := hM
  obtain ⟨_, hP_diff, _, _, hP_bound, _⟩ := hP
  -- `ψ_C` maps the unit ball into the unit ball
  have hmap : Set.MapsTo Submission.CDTPlan.psiC
      (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have h1 : ‖Submission.CDTPlan.psiC z‖ ≤ 3 / 4 :=
      hP_bound z (Metric.ball_subset_closedBall hz)
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  -- `K = k ∘ ψ_C` is holomorphic, hence so is `deriv K`
  have hKdiff : DifferentiableOn ℂ (fun z => k (Submission.CDTPlan.psiC z))
      (Metric.ball (0 : ℂ) 1) := hk_diff.comp hP_diff hmap
  have hKderivdiff : DifferentiableOn ℂ (deriv (fun z => k (Submission.CDTPlan.psiC z)))
      (Metric.ball (0 : ℂ) 1) := hKdiff.deriv Metric.isOpen_ball
  -- `K 0 ≠ 0` because `K 0 ^ 2 = phiC 0 - 4 = -4`
  have hK0 : (fun z => k (Submission.CDTPlan.psiC z)) 0 ≠ 0 := by
    intro h
    have hb : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
    have h1 : Submission.CDTPlan.phiC 0 - 4 =
        (fun z => k (Submission.CDTPlan.psiC z)) 0 ^ 2 := by
      have hh := hk_eq (Submission.CDTPlan.psiC 0) (hmap hb)
      simpa [Submission.CDTPlan.phiC] using hh
    rw [h, hφ0] at h1
    norm_num at h1
  -- `K` squares to `phiC - 4`
  have hsqrt : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Submission.CDTPlan.phiC z - 4 = (fun z => k (Submission.CDTPlan.psiC z)) z ^ 2 := by
    intro z hz
    have hh := hk_eq (Submission.CDTPlan.psiC z) (hmap hz)
    simpa [Submission.CDTPlan.phiC] using hh
  -- continuity of `phiC` and `K` at `0`
  have hφcont : ContinuousAt Submission.CDTPlan.phiC 0 :=
    (hφdiff.differentiableAt (Metric.ball_mem_nhds 0 one_pos)).continuousAt
  have hKcont : ContinuousAt (fun z => k (Submission.CDTPlan.psiC z)) 0 :=
    (hKdiff.differentiableAt (Metric.ball_mem_nhds 0 one_pos)).continuousAt
  have hmem1 : ∀ᶠ w in 𝓝 (Submission.CDTPlan.phiC 0), ‖w‖ < 3 / 4 := by
    rw [hφ0]
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 3 / 4)] with w hw
    simpa [Metric.mem_ball, dist_zero_right] using hw
  have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), ‖Submission.CDTPlan.phiC z‖ < 3 / 4 :=
    hφcont.eventually hmem1
  obtain ⟨ε1, hε1pos, hε1sub⟩ := Metric.eventually_nhds_iff.mp h1
  have hmem2 : ∀ᶠ w in 𝓝 ((fun z => k (Submission.CDTPlan.psiC z)) 0), w ≠ 0 := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hK0] with w hw
    simpa using hw
  have h2 : ∀ᶠ z in 𝓝 (0 : ℂ), (fun z => k (Submission.CDTPlan.psiC z)) z ≠ 0 :=
    hKcont.eventually hmem2
  obtain ⟨ε2, hε2pos, hε2sub⟩ := Metric.eventually_nhds_iff.mp h2
  refine ⟨fun z => k (Submission.CDTPlan.psiC z), min (min ε1 ε2) 1,
    lt_min (lt_min hε1pos hε2pos) one_pos, min_le_right _ _, hKdiff, hKderivdiff, hK0, hsqrt,
    hφzero, hφ0, ?_, ?_⟩
  · intro z hz
    rw [Metric.mem_ball] at hz
    have hz1 : dist z 0 < ε1 :=
      lt_of_lt_of_le (lt_of_lt_of_le hz (min_le_left _ _)) (min_le_left _ _)
    exact le_of_lt (hε1sub hz1)
  · intro z hz
    rw [Metric.mem_ball] at hz
    have hz2 : dist z 0 < ε2 :=
      lt_of_lt_of_le (lt_of_lt_of_le hz (min_le_left _ _)) (min_le_right _ _)
    exact hε2sub hz2

end Work.CPull

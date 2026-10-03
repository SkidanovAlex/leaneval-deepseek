import Mathlib
import Submission.Work.FatouCoord.Petal.reflected_inverse_germ
import Submission.Work.Interfaces.Parabolic
import Submission.Work.PertCrux.iterate_dslope_two_apply_zero
import Submission.Work.PertCrux.exists_ball_bounds_analytic

namespace Work.PertCrux

noncomputable section

open Metric Function
open scoped Topology

/-! ## Auxiliary fact (local) -/

/-- The difference-quotient identity: for `f` with `f 0 = 0` and `f'(0) = 1`, the twice iterated
difference quotient at the origin realises `f z - z = z^2 * hF z` for every `z` (the two
`dslope`-identities are the general `sub_smul_dslope`). -/
lemma sub_eq_sq_mul_iterate_dslope_aux {f : ℂ → ℂ} (h0 : f 0 = 0) (h1 : deriv f 0 = 1)
    (z : ℂ) :
    f z - z = z ^ 2 * ((Function.swap dslope (0 : ℂ))^[2] f) z := by
  have hiter : ((Function.swap dslope (0 : ℂ))^[2] f) = dslope (dslope f 0) 0 := rfl
  rw [hiter]
  have hA : z * dslope f 0 z = f z := by
    have h := sub_smul_dslope f 0 z
    rw [sub_zero, smul_eq_mul, h0, sub_zero] at h
    exact h
  have hB : z * dslope (dslope f 0) 0 z = dslope f 0 z - 1 := by
    have h := sub_smul_dslope (dslope f 0) 0 z
    rw [sub_zero, smul_eq_mul, dslope_same f 0, h1] at h
    exact h
  calc f z - z = z * dslope f 0 z - z := by rw [hA]
    _ = z * (dslope f 0 z - 1) := by ring
    _ = z * (z * dslope (dslope f 0) 0 z) := by rw [hB]
    _ = z ^ 2 * dslope (dslope f 0) 0 z := by ring

theorem exists_model_data {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ hF : ℂ → ℂ, ∃ ρ D : ℝ, 0 < ρ ∧ ρ ≤ 1 / 8 ∧ 0 ≤ D ∧
      Metric.closedBall (0 : ℂ) ρ ⊆ D₀ ∧ hF 0 = 1 ∧
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, f₀ z = z + z ^ 2 * hF z) ∧
      DifferentiableOn ℂ hF (Metric.ball 0 ρ) ∧
      (∀ z ∈ Metric.ball 0 ρ, ‖deriv hF z‖ ≤ D) ∧
      (∀ z ∈ Metric.ball 0 ρ, ‖hF z‖ ≤ 3 / 2) := by
  obtain ⟨hopen, h0mem, hdiff, hf0, hf1, hf2⟩ := hd
  have hAf : AnalyticAt ℂ f₀ 0 := hdiff.analyticAt (hopen.mem_nhds h0mem)
  set hF : ℂ → ℂ := (Function.swap dslope (0 : ℂ)) ^[2] f₀ with hFdef
  have hF_an : AnalyticAt ℂ hF 0 := by
    have h := HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope 2 hAf.hasFPowerSeriesAt
    rw [← hFdef] at h
    exact h.analyticAt
  have hF_second : iteratedDeriv 2 f₀ 0 = 2 := by
    rw [iteratedDeriv_eq_iterate]
    simpa using hf2
  have hF_zero : hF 0 = 1 := by
    have h := iterate_dslope_two_apply_zero hAf
    rw [← hFdef] at h
    rw [h, hF_second]
    norm_num
  have hfe : ∀ z : ℂ, f₀ z = z + z ^ 2 * hF z := by
    intro z
    have h := sub_eq_sq_mul_iterate_dslope_aux hf0 hf1 z
    rw [← hFdef] at h
    rw [← h]; ring
  obtain ⟨ρ₁, hρ₁pos, hρ₁sub⟩ : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (0 : ℂ) ρ ⊆ D₀ := by
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hopen 0 h0mem
    exact ⟨ε, hεpos, hεsub⟩
  obtain ⟨r, hrpos, hran⟩ : ∃ r : ℝ, 0 < r ∧ AnalyticOnNhd ℂ hF (Metric.ball 0 r) :=
    hF_an.exists_ball_analyticOnNhd
  obtain ⟨ρ₂, hρ₂pos, hρ₂n, hρ₂d⟩ := exists_ball_bounds_analytic hF_an hF_zero
  obtain ⟨ρ, hρpos, hρ8, hρρ₁, hρρ₂, hρr⟩ :
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 8 ∧ ρ ≤ ρ₁ / 2 ∧ ρ ≤ ρ₂ / 2 ∧ ρ ≤ r / 2 := by
    refine ⟨min (1 / 8) (min (ρ₁ / 2) (min (ρ₂ / 2) (r / 2))), ?_, ?_, ?_, ?_, ?_⟩
    · exact lt_min (by norm_num) (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨hF, ρ, ‖deriv hF 0‖ + 1, hρpos, hρ8, by positivity, ?_, hF_zero, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [Metric.mem_closedBall] at hz
    exact hρ₁sub (by rw [Metric.mem_ball]; linarith)
  · intro z _
    exact hfe z
  · refine (hran.differentiableOn).mono (fun z hz => ?_)
    rw [Metric.mem_ball] at hz ⊢
    linarith
  · intro z hz
    rw [Metric.mem_ball] at hz
    exact hρ₂d z (by rw [Metric.mem_ball]; linarith)
  · intro z hz
    rw [Metric.mem_ball] at hz
    exact hρ₂n z (by rw [Metric.mem_ball]; linarith)

end

end Work.PertCrux

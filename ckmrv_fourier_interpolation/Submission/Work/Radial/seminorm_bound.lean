import Mathlib
import Submission.Work.Core.Basic
import Submission.Work.Radial.Basic

open Filter
open LeanEval.Analysis.CKMRVInterpolation
open scoped SchwartzMap

namespace Work.Radial

/-- A continuous linear functional on the Schwartz space is bounded by finitely many
Schwartz seminorms. -/

theorem exists_seminorm_bound (n : ℕ) [NeZero n]
    (Λ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] ℂ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ F : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ‖Λ F‖ ≤ C * ((s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin n)) ℂ)) F) := by
  have hp := schwartz_withSeminorms (𝕜 := ℝ) (EuclideanSpace ℝ (Fin n)) ℂ
  have hmem : Λ ⁻¹' Metric.ball (0 : ℂ) 1 ∈ nhds (0 : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) := by
    have h := Λ.continuous.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (Λ (0 : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))) zero_lt_one)
    rwa [map_zero] at h
  obtain ⟨s, r, hr, hs⟩ := (hp.mem_nhds_iff 0 _).mp hmem
  set p := schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin n)) ℂ with hpdef
  have hkey : ∀ G : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (s.sup p) G < r → ‖Λ G‖ < 1 := by
    intro G hG
    have h1 : G ∈ (s.sup p).ball 0 r := by rw [Seminorm.mem_ball, sub_zero]; exact hG
    have h2 := hs h1
    simpa [Metric.mem_ball, dist_eq_norm] using h2
  have hsmul : ∀ (t : ℝ) (F : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
      (s.sup p) (t • F) = |t| * (s.sup p) F := by
    intro t F
    have h := Seminorm.smul' (s.sup p) t F
    rw [Real.norm_eq_abs] at h
    exact h
  have hlin : ∀ (t : ℝ) (F : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)),
      Λ (t • F) = (t : ℂ) • Λ F := by
    intro t F
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact ContinuousLinearMap.map_smul Λ (t : ℂ) F
  refine ⟨s, 2 / r, by positivity, fun F => ?_⟩
  set M : ℝ := (s.sup p) F with hM
  have hMnonneg : 0 ≤ M := apply_nonneg (s.sup p) F
  rcases eq_or_lt_of_le hMnonneg with h0 | hpos
  · have hzero : ‖Λ F‖ = 0 := by
      by_contra hne
      have hpos' : 0 < ‖Λ F‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      set t : ℝ := 1 / ‖Λ F‖ + 1 with ht
      have htpos : 0 < t := by positivity
      have hlarge : 1 < t * ‖Λ F‖ := by
        have h1 : (1 / ‖Λ F‖) * ‖Λ F‖ = 1 := by field_simp
        have h2 : 1 < (1 / ‖Λ F‖ + 1) * ‖Λ F‖ := by nlinarith [h1, hpos']
        simpa [ht] using h2
      have hball : t • F ∈ (s.sup p).ball 0 r := by
        rw [Seminorm.mem_ball, sub_zero, hsmul t F, abs_of_pos htpos, ← hM]
        rw [← h0, mul_zero]; exact hr
      have hlt := hkey _ hball
      rw [sub_zero] at hlt
      have habs : ‖(t : ℂ)‖ = |t| := by simp
      rw [hlin t F, norm_smul, habs, abs_of_pos htpos] at hlt
      linarith [hlarge]
    rw [hzero]; exact mul_nonneg (by positivity) hMnonneg
  · have hmain : ‖Λ F‖ ≤ 2 * M / r := by
      have hMpos : 0 < M := hpos
      set t : ℝ := r / (2 * M) with ht
      have htpos : 0 < t := by positivity
      have hball : t • F ∈ (s.sup p).ball 0 r := by
        rw [Seminorm.mem_ball, sub_zero, hsmul t F, abs_of_pos htpos, ← hM]
        have h2 : t * M = r / 2 := by rw [ht]; field_simp
        rw [h2]; linarith
      have hb := hkey _ hball
      rw [sub_zero] at hb
      have habs : ‖(t : ℂ)‖ = |t| := by simp
      rw [hlin t F, norm_smul, habs, abs_of_pos htpos] at hb
      rw [ht, div_mul_eq_mul_div, div_lt_one (by positivity : (0:ℝ) < 2 * M)] at hb
      apply le_of_lt
      rw [lt_div_iff₀ hr]
      linarith
    calc ‖Λ F‖ ≤ 2 * M / r := hmain
      _ = (2 / r) * ((s.sup p) F) := by rw [hM]; ring

end Work.Radial

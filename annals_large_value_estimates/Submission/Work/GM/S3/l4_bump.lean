import Mathlib
import Submission.Work.GM.S3.Base

namespace Work.GM.S3

open MeasureTheory

/-- Existence of a continuous compactly supported `ψ : ℝ → ℝ`, nonnegative, `≥ 1` on
`[0, log 2]`, whose Fourier transform is bounded everywhere by `A` and decays faster than any
power (this is the smooth bump of GM Lemma 8.3; the decay clause is the essential part).
NOTE the Mathlib trap: smooth is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`; bare `⊤` is *analytic*. -/
theorem l4_bump :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧
      (∀ x : ℝ, 0 ≤ ψ x) ∧ (∀ x ∈ Set.Icc (0 : ℝ) (Real.log 2), 1 ≤ ψ x) ∧
      (∃ A : ℝ, 0 ≤ A ∧ ∀ ξ : ℝ,
        ‖FourierTransform.fourier (fun x : ℝ => (ψ x : ℂ)) ξ‖ ≤ A) ∧
      (∀ j : ℕ, ∃ Cj : ℝ, 0 < Cj ∧ ∀ ξ : ℝ, ξ ≠ 0 →
        ‖FourierTransform.fourier (fun x : ℝ => (ψ x : ℂ)) ξ‖ ≤ Cj / |ξ| ^ j) := by
  -- The explicit smooth bump: the product of two smooth steps, which is `1` on `[0, log 2]`
  -- and vanishes off `[-1, log 2 + 1]`.
  let ψ : ℝ → ℝ :=
    fun x => Real.smoothTransition (x + 1) * Real.smoothTransition (Real.log 2 + 1 - x)
  have hψc : Continuous ψ := by
    unfold ψ
    refine Continuous.mul ?_ ?_
    · exact Real.smoothTransition.continuous.comp (continuous_id.add continuous_const)
    · exact Real.smoothTransition.continuous.comp (continuous_const.sub continuous_id)
  have hψnn : ∀ x : ℝ, 0 ≤ ψ x := by
    intro x
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hψone : ∀ x ∈ Set.Icc (0 : ℝ) (Real.log 2), 1 ≤ ψ x := by
    intro x hx
    obtain ⟨hx0, hxL⟩ := hx
    have e1 : Real.smoothTransition (x + 1) = 1 := Real.smoothTransition.one_of_one_le (by linarith)
    have e2 : Real.smoothTransition (Real.log 2 + 1 - x) = 1 :=
      Real.smoothTransition.one_of_one_le (by linarith)
    simp [ψ, e1, e2]
  have hψdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
    unfold ψ
    fun_prop
  -- The support is contained in the compact interval `[-1, log 2 + 1]`.
  have hsub : Function.support ψ ⊆ Set.Icc (-1 : ℝ) (Real.log 2 + 1) := by
    intro x hx
    rw [Function.mem_support] at hx
    dsimp only [ψ] at hx
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hx
    have hp1 : 0 < x + 1 := by
      by_contra h
      exact h1 (Real.smoothTransition.zero_of_nonpos (le_of_not_gt h))
    have hp2 : 0 < Real.log 2 + 1 - x := by
      by_contra h
      exact h2 (Real.smoothTransition.zero_of_nonpos (le_of_not_gt h))
    exact ⟨by linarith, by linarith⟩
  have hψcs : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsub
  have hsubC : Function.support (fun x : ℝ => (ψ x : ℂ)) ⊆ Set.Icc (-1 : ℝ) (Real.log 2 + 1) := by
    intro x hx
    apply hsub
    rw [Function.mem_support] at hx ⊢
    intro h
    exact hx (by simp [h])
  have hψCcs : HasCompactSupport (fun x : ℝ => (ψ x : ℂ)) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsubC
  have hψCdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => (ψ x : ℂ)) := by
    have hh := (Complex.ofRealCLM.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp hψdiff
    have hfun : (⇑Complex.ofRealCLM ∘ ψ) = fun x : ℝ => (ψ x : ℂ) := by
      funext x
      exact Complex.ofRealCLM_apply (ψ x)
    rwa [hfun] at hh
  refine ⟨ψ, hψc, hψcs, hψnn, hψone, ?_, ?_⟩
  · -- Boundedness: the Fourier transform is bounded by the `L¹` norm of `ψ`.
    refine ⟨∫ x : ℝ, ‖((ψ x : ℝ) : ℂ)‖, ?_, ?_⟩
    · exact integral_nonneg (fun x => norm_nonneg _)
    · intro ξ
      rw [Real.fourier_eq]
      have h := norm_integral_le_integral_norm (μ := volume)
        (fun v : ℝ => Real.fourierChar (-inner ℝ v ξ) • ((ψ v : ℝ) : ℂ))
      simpa only [Circle.norm_smul] using h
  · -- Decay: a smooth compactly supported function has rapidly decaying Fourier transform.
    intro j
    obtain ⟨C, hC0, hC⟩ :=
      Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay j hψCdiff hψCcs
    refine ⟨C + 1, by linarith, fun ξ hξ => ?_⟩
    have hpos : 0 < |ξ| ^ j := pow_pos (abs_pos.mpr hξ) j
    calc ‖FourierTransform.fourier (fun x : ℝ => (ψ x : ℂ)) ξ‖
        ≤ C / |ξ| ^ j := hC ξ hξ
      _ ≤ (C + 1) / |ξ| ^ j := by
          apply div_le_div_of_nonneg_right (by linarith) hpos.le

end Work.GM.S3

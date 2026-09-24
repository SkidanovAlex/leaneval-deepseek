import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.bddAbove_range_RtildeSq
import Submission.Work.GM.S3.RtildeSq_continuous

namespace Work.GM.S3

open MeasureTheory Finset Complex
open scoped BigOperators FourierTransform

/-- If `IsBumpAtOne ψ C` then `ψ` vanishes off `[1/C, C]`. -/
private theorem rtBumpAtOne_eq_zero_of_notMem {ψ : ℝ → ℝ} {C : ℝ} (h : IsBumpAtOne ψ C) {x : ℝ}
    (hx : x ∉ Set.Icc (1 / C) C) : ψ x = 0 :=
  by_contra fun hne => hx (h.2.2.1 x hne)

/-- **Trivial (`|ξ| ≤ T`) bound for `𝓕(ψ₁·RtildeSq)`.**

For non-negative bumps `ψ₁, ψ₂` (`IsBumpAtOne`) and `ψ₃` (`IsBumpAtZero`) there is `C > 0` such that
for all `W, N, B ≥ 0` and all `ξ`

  ‖𝓕 (u ↦ ψ₁ u · RtildeSq W N B ψ₃ ψ₂ u) ξ‖ ≤ C · sSup (range (u ↦ ψ₁ u · RtildeSq W N B ψ₃ ψ₂ u)).

Proof: `𝓕 f ξ = ∫ u, 𝐞(-ξu) • f u`, so `‖𝓕 f ξ‖ ≤ ∫ u, ‖f u‖ = ∫ u, f u` (the integrand is
non-negative: `ψ₁ ≥ 0`, `N B ≥ 0`, `ψ₃, ψ₂ ≥ 0`, `‖R‖² ≥ 0`), and `f` is supported in
`[1/C₀, C₀]` (support of `ψ₁`) and bounded there by `sSup (range f)` — which is a genuine upper
bound by `bddAbove_range_RtildeSq`; hence `∫ ‖f‖ ≤ (C₀ - 1/C₀)·sup ψ₁·sSup (range f)`.  This is the
`j = 0` case of `Work.GM.S3.fourier_decay_RtildeSq` (in `Submission/Work/GM/S3/lemma84.lean`)
without the hypothesis `N B ≤ M N`. -/
theorem RtildeSq_fourier_trivial (ψ₁ ψ₂ ψ₃ : ℝ → ℝ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀)
    (h₁ : Work.GM.S3.IsBumpAtOne ψ₁ C₀) (h₂ : Work.GM.S3.IsBumpAtOne ψ₂ C₀)
    (h₃ : Work.GM.S3.IsBumpAtZero ψ₃ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Finset ℝ) (N : ℕ) (B ξ : ℝ), 0 ≤ B →
      ‖FourierTransform.fourier
          (fun u => ((ψ₁ u * Work.GM.S3.RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)) ξ‖ ≤
        C * sSup (Set.range (fun u => ψ₁ u * Work.GM.S3.RtildeSq W N B ψ₃ ψ₂ u)) := by
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos hC₀
  refine ⟨C₀, hC₀pos, ?_⟩
  intro W N B ξ hB
  have hNB : 0 ≤ (N : ℝ) * B := mul_nonneg (Nat.cast_nonneg N) hB
  have hbdd : BddAbove (Set.range (fun u => ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u)) :=
    bddAbove_range_RtildeSq ψ₁ ψ₂ ψ₃ C₀ h₁ h₂ h₃ W N B hNB
  set f : ℝ → ℝ := fun u => ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u with hf
  change ‖FourierTransform.fourier (fun u => (f u : ℂ)) ξ‖ ≤ C₀ * sSup (Set.range f)
  have hfnonneg : ∀ u, 0 ≤ f u := by
    intro u
    rw [hf]
    exact mul_nonneg (h₁.2.1 u) (RtildeSq_nonneg W N B ψ₃ ψ₂ u h₃.2.1 h₂.2.1 hB)
  have hle : ∀ u, f u ≤ sSup (Set.range f) := fun u => le_csSup hbdd (Set.mem_range_self u)
  have hsupnonneg : 0 ≤ sSup (Set.range f) := le_trans (hfnonneg 0) (hle 0)
  -- the interval `[1/C₀, C₀]` is non-degenerate, and contains `1`
  have hone : (1 : ℝ) ∈ Set.Icc (1 / C₀) C₀ :=
    ⟨(div_le_one hC₀pos).mpr hC₀, hC₀⟩
  have hab : 1 / C₀ ≤ C₀ := le_trans hone.1 hone.2
  -- `f` is continuous with compact support, hence integrable
  have hcont : Continuous f := by
    rw [hf]
    exact h₁.1.continuous.mul (RtildeSq_continuous W N B C₀ ψ₃ ψ₂ h₃ h₂)
  have hcs : HasCompactSupport f := by
    refine HasCompactSupport.intro (K := Set.Icc (1 / C₀) C₀) isCompact_Icc fun x hx => ?_
    rw [hf]
    simp only
    rw [rtBumpAtOne_eq_zero_of_notMem h₁ hx, zero_mul]
  have hfint : Integrable f := hcont.integrable_of_hasCompactSupport hcs
  have hIcc : Integrable ((Set.Icc (1 / C₀) C₀).indicator (fun _ => sSup (Set.range f))) := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
    exact MeasureTheory.integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  -- pointwise domination by the indicator of `[1/C₀, C₀]` at height `sSup (range f)`
  have hpoint : ∀ u, f u ≤ (Set.Icc (1 / C₀) C₀).indicator (fun _ => sSup (Set.range f)) u := by
    intro u
    by_cases hu : u ∈ Set.Icc (1 / C₀) C₀
    · rw [Set.indicator_of_mem hu]; exact hle u
    · rw [Set.indicator_of_notMem hu, hf]
      simp only
      rw [rtBumpAtOne_eq_zero_of_notMem h₁ hu, zero_mul]
  -- the Fourier transform, as an integral against the Fourier character
  have hfour : FourierTransform.fourier (fun u => (f u : ℂ)) ξ
      = ∫ u, (Real.fourierChar (-(ξ * u))) • (f u : ℂ) := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [show inner ℝ u ξ = ξ * u from by simp]
  have hnorm_char : ∀ u : ℝ, ‖(Real.fourierChar (-(ξ * u))) • (f u : ℂ)‖ = ‖f u‖ := by
    intro u
    rw [Circle.norm_smul, Complex.norm_real]
  have hbound : ‖FourierTransform.fourier (fun u => (f u : ℂ)) ξ‖ ≤
      (C₀ - 1 / C₀) * sSup (Set.range f) := by
    calc ‖FourierTransform.fourier (fun u => (f u : ℂ)) ξ‖
        = ‖∫ u, (Real.fourierChar (-(ξ * u))) • (f u : ℂ)‖ := by rw [hfour]
      _ ≤ ∫ u, ‖(Real.fourierChar (-(ξ * u))) • (f u : ℂ)‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ u, ‖f u‖ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => hnorm_char u)
      _ = ∫ u, f u := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          dsimp only
          rw [Real.norm_eq_abs, abs_of_nonneg (hfnonneg u)]
      _ ≤ ∫ u, (Set.Icc (1 / C₀) C₀).indicator (fun _ => sSup (Set.range f)) u :=
          MeasureTheory.integral_mono hfint hIcc hpoint
      _ = (C₀ - 1 / C₀) * sSup (Set.range f) := by
          rw [MeasureTheory.integral_indicator_const (sSup (Set.range f)) measurableSet_Icc,
            Real.volume_real_Icc_of_le hab, smul_eq_mul]
  refine hbound.trans (mul_le_mul_of_nonneg_right ?_ hsupnonneg)
  have h1C : 0 ≤ 1 / C₀ := div_nonneg zero_le_one hC₀pos.le
  linarith

end Work.GM.S3

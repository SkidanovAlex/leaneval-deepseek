import Mathlib
import Submission.Work.GM.S3.Defs

namespace Work.GM.S3

open MeasureTheory Finset Complex
open scoped BigOperators
open Submission.GM (Rfun)

/-- **Boundedness of the smoothed `|R|²`.** For `N·B ≥ 0` the function
`u ↦ ψ₁ u · RtildeSq W N B ψ₃ ψ₂ u` is bounded above (its integral kernel is bounded by
`(N·B)·sup|ψ₃|·sup ψ₂·|W|²` on a bounded set of `u'`, and `ψ₁` is bounded), so that
`sSup (Set.range ·)` is a genuine upper bound.  Suggested route: bound the integrand pointwise
using `‖Rfun W u'‖ ≤ W.card` (`Rfun_norm_le_card`) and the support conditions of `ψ₂`, `ψ₃`, then
bound `ψ₁` using the `j = 0` case of its derivative bounds. -/
theorem bddAbove_range_RtildeSq (ψ₁ ψ₂ ψ₃ : ℝ → ℝ) (C₀ : ℝ) (h₁ : IsBumpAtOne ψ₁ C₀)
    (h₂ : IsBumpAtOne ψ₂ C₀) (h₃ : IsBumpAtZero ψ₃ C₀) :
    ∀ (W : Finset ℝ) (N : ℕ) (B : ℝ), 0 ≤ (N : ℝ) * B →
      BddAbove (Set.range (fun u => ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u)) := by
  intro W N B hNB
  -- derivative bounds at `j = 0`: bounds on the functions themselves
  obtain ⟨c₁, hc₁0, hc₁⟩ := h₁.2.2.2.2 0
  obtain ⟨c₂, hc₂0, hc₂⟩ := h₂.2.2.2.2 0
  obtain ⟨c₃, hc₃0, hc₃⟩ := h₃.2.2.2.2 0
  simp only [iteratedDeriv_zero] at hc₁ hc₂ hc₃
  -- `C₀ ≥ 1` (and hence `1/C₀ ≤ C₀`), from `ψ₁ 1 = 1` and the support bound of `ψ₁`
  have hmem : (1 : ℝ) ∈ Set.Icc (1 / C₀) C₀ := h₁.2.2.1 1 (by rw [h₁.2.2.2.1]; norm_num)
  have hab : 1 / C₀ ≤ C₀ := le_trans hmem.1 hmem.2
  -- the pointwise bound on the integrand, and the resulting integral bound
  set K : ℝ := (N : ℝ) * B * c₃ * c₂ * (W.card : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; exact mul_nonneg (mul_nonneg (mul_nonneg hNB hc₃0) hc₂0) (sq_nonneg _)
  set M : ℝ := (C₀ - 1 / C₀) * K with hM
  have hM0 : 0 ≤ M := by rw [hM]; exact mul_nonneg (sub_nonneg.mpr hab) hK0
  -- `∫ u', (N B) ψ₃ (N B (u-u')) ψ₂ u' ‖R u'‖² ≤ (C₀ - 1/C₀) * K`
  have hRt : ∀ u, RtildeSq W N B ψ₃ ψ₂ u ≤ M := by
    intro u
    rw [hM, RtildeSq]
    have hInt : (∫ u' : ℝ, (N : ℝ) * B * ψ₃ ((N : ℝ) * B * (u - u')) * ψ₂ u' * ‖Rfun W u'‖ ^ 2)
        ≤ ∫ u' : ℝ, (Set.Icc (1 / C₀) C₀).indicator (fun _ => K) u' := by
      refine integral_mono_of_nonneg ?_ ?_ ?_
      · exact Filter.Eventually.of_forall (fun u' =>
          mul_nonneg (mul_nonneg (mul_nonneg hNB (h₃.2.1 _)) (h₂.2.1 _)) (sq_nonneg _))
      · rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
        exact MeasureTheory.integrableOn_const
          (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      · refine Filter.Eventually.of_forall (fun u' => ?_)
        by_cases hu : u' ∈ Set.Icc (1 / C₀) C₀
        · rw [Set.indicator_of_mem hu, hK]
          have hA : ψ₃ ((N : ℝ) * B * (u - u')) ≤ c₃ := le_trans (le_abs_self _) (hc₃ _)
          have hB : ψ₂ u' ≤ c₂ := le_trans (le_abs_self _) (hc₂ _)
          have hC : ‖Rfun W u'‖ ^ 2 ≤ (W.card : ℝ) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (Rfun_norm_le_card W u') 2
          have h1 : (N : ℝ) * B * ψ₃ ((N : ℝ) * B * (u - u')) ≤ (N : ℝ) * B * c₃ :=
            mul_le_mul_of_nonneg_left hA hNB
          have h2 : ((N : ℝ) * B * ψ₃ ((N : ℝ) * B * (u - u'))) * ψ₂ u' ≤
              ((N : ℝ) * B * c₃) * c₂ :=
            mul_le_mul h1 hB (h₂.2.1 _) (mul_nonneg hNB hc₃0)
          exact mul_le_mul h2 hC (sq_nonneg _) (mul_nonneg (mul_nonneg hNB hc₃0) hc₂0)
        · rw [Set.indicator_of_notMem hu]
          have hψ₂ : ψ₂ u' = 0 := by
            by_contra hne
            exact hu (h₂.2.2.1 u' hne)
          simp [hψ₂]
    calc (∫ u' : ℝ, (N : ℝ) * B * ψ₃ ((N : ℝ) * B * (u - u')) * ψ₂ u' * ‖Rfun W u'‖ ^ 2)
        ≤ _ := hInt
      _ = (C₀ - 1 / C₀) * K := by
            rw [MeasureTheory.integral_indicator_const K measurableSet_Icc,
                Real.volume_real_Icc_of_le hab, smul_eq_mul]
  have hRt0 : ∀ u, 0 ≤ RtildeSq W N B ψ₃ ψ₂ u := by
    intro u
    rw [RtildeSq]
    exact integral_nonneg (fun u' =>
      mul_nonneg (mul_nonneg (mul_nonneg hNB (h₃.2.1 _)) (h₂.2.1 _)) (sq_nonneg _))
  rw [bddAbove_def]
  refine ⟨c₁ * M, ?_⟩
  rintro y ⟨u, rfl⟩
  have hψ₁u : ψ₁ u ≤ c₁ := le_trans (le_abs_self _) (hc₁ u)
  calc ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u ≤ c₁ * RtildeSq W N B ψ₃ ψ₂ u :=
        mul_le_mul_of_nonneg_right hψ₁u (hRt0 u)
    _ ≤ c₁ * M := mul_le_mul_of_nonneg_left (hRt u) hc₁0

end Work.GM.S3

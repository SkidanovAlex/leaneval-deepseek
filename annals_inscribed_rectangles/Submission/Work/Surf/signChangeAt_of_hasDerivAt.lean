import Mathlib
import Submission.Work.Drive.parity_tools_defs

/-!
# A zero with non-vanishing derivative is a sign change

`Work.Drive.SignChangeAt` is the non-degeneracy hypothesis under which a zero of a continuous
function on an interval counts once in the parity of the number of zeros
(`Work.Drive.odd_ncard_zeros_of_opposite_signs`).  For a differentiable function it is implied by the
non-vanishing of the derivative at the zero:

`f t = 0` and `deriv f t ≠ 0` imply `Work.Drive.SignChangeAt f t`.

This is the form in which the transversality hypotheses of the chord arguments of
`Submission/Work/Surf/chord_parity.lean` (transverse intersections) produce sign changes.
-/

namespace Work.Surf

open scoped Topology

noncomputable section

/-- **A zero with non-vanishing derivative is a sign change.** -/
theorem signChangeAt_of_hasDerivAt {f : ℝ → ℝ} {c t : ℝ} (h : HasDerivAt f c t) (hc : c ≠ 0)
    (ht : f t = 0) : Work.Drive.SignChangeAt f t := by
  have hratio : Filter.Tendsto (fun x => f x / (x - t)) (𝓝[≠] t) (𝓝 c) := by
    have h1 : Filter.Tendsto (slope f t) (𝓝[≠] t) (𝓝 c) := (hasDerivAt_iff_tendsto_slope).mp h
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [slope_def_module, ht, sub_zero, smul_eq_mul, inv_mul_eq_div]
  have key : ∀ {c' : ℝ}, c' < c → ∃ ε > 0, ∀ s : ℝ, dist s t < ε → s ≠ t →
      c' < f s / (s - t) := by
    intro c' hc'
    obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhdsWithin_iff.mp
      (hratio.eventually (Ioi_mem_nhds hc'))
    refine ⟨ε, hε, fun s hs hne => hε' ⟨?_, ?_⟩⟩
    · rwa [Metric.mem_ball]
    · simpa [Set.mem_compl_iff] using hne
  have key2 : ∀ {c' : ℝ}, c < c' → ∃ ε > 0, ∀ s : ℝ, dist s t < ε → s ≠ t →
      f s / (s - t) < c' := by
    intro c' hc'
    obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhdsWithin_iff.mp
      (hratio.eventually (Iio_mem_nhds hc'))
    refine ⟨ε, hε, fun s hs hne => hε' ⟨?_, ?_⟩⟩
    · rwa [Metric.mem_ball]
    · simpa [Set.mem_compl_iff] using hne
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · -- the derivative is negative: `f` is positive on the left and negative on the right
    right
    obtain ⟨ε, hε, hε'⟩ := key2 (show c < c / 2 by linarith)
    refine ⟨ε, hε, ?_, ?_⟩
    · intro s h1 h2
      have hs : dist s t < ε := by
        rw [Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩
      have hb := hε' s hs (by linarith)
      have hst : s - t < 0 := by linarith
      have hrr : f s / (s - t) < 0 := lt_trans hb (by linarith)
      have hsplit : (f s / (s - t)) * (s - t) = f s := div_mul_cancel₀ _ (by linarith : s - t ≠ 0)
      rw [← hsplit]
      exact mul_pos_of_neg_of_neg hrr hst
    · intro s h1 h2
      have hs : dist s t < ε := by
        rw [Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩
      have hb := hε' s hs (by linarith)
      have hst : 0 < s - t := by linarith
      have hrr : f s / (s - t) < 0 := lt_trans hb (by linarith)
      have hsplit : (f s / (s - t)) * (s - t) = f s := div_mul_cancel₀ _ (by linarith : s - t ≠ 0)
      rw [← hsplit]
      exact mul_neg_of_neg_of_pos hrr hst
  · -- the derivative is positive: `f` is negative on the left and positive on the right
    left
    obtain ⟨ε, hε, hε'⟩ := key (show c / 2 < c by linarith)
    refine ⟨ε, hε, ?_, ?_⟩
    · intro s h1 h2
      have hs : dist s t < ε := by
        rw [Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩
      have hb := hε' s hs (by linarith)
      have hst : s - t < 0 := by linarith
      have hrr : 0 < f s / (s - t) := lt_trans (by linarith) hb
      have hsplit : (f s / (s - t)) * (s - t) = f s := div_mul_cancel₀ _ (by linarith : s - t ≠ 0)
      rw [← hsplit]
      exact mul_neg_of_pos_of_neg hrr hst
    · intro s h1 h2
      have hs : dist s t < ε := by
        rw [Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩
      have hb := hε' s hs (by linarith)
      have hst : 0 < s - t := by linarith
      have hrr : 0 < f s / (s - t) := lt_trans (by linarith) hb
      have hsplit : (f s / (s - t)) * (s - t) = f s := div_mul_cancel₀ _ (by linarith : s - t ≠ 0)
      rw [← hsplit]
      exact mul_pos hrr hst

end

end Work.Surf

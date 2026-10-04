import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

open Finset Filter

/-- Log-convexity (in the exponent) of `CSq`: this is Cauchy–Schwarz applied to the
three-term identity `⟨k⟩^s = ⟨k⟩^{s-r} · ⟨k⟩^{s+r}`. -/
theorem CSq_interpolation {ι : Type*} [Fintype ι] [DecidableEq ι] (s r : ℕ)
    (hr : r ≤ s) (c : (ι → ℤ) → ℂ)
    (h : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (s + r) * ‖c k‖ ^ 2)) :
    (Work.Diff.STE.CSq s c) ^ 2
      ≤ (Work.Diff.STE.CSq (s - r) c) * (Work.Diff.STE.CSq (s + r) c) := by
  set M : (ι → ℤ) → ℝ := fun k => wt k ^ s * ‖c k‖ ^ 2 with hM
  set A : (ι → ℤ) → ℝ := fun k => wt k ^ (s - r) * ‖c k‖ ^ 2 with hA
  set B : (ι → ℤ) → ℝ := fun k => wt k ^ (s + r) * ‖c k‖ ^ 2 with hB
  have hBsum : Summable B := h
  have hAnn : ∀ k, 0 ≤ A k := fun k => by
    rw [hA]; exact mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) _) (sq_nonneg _)
  have hBnn : ∀ k, 0 ≤ B k := fun k => by
    rw [hB]; exact mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) _) (sq_nonneg _)
  have hAsum : Summable A := Summable.of_nonneg_of_le hAnn (fun k => by
    rw [hA, hB]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (wt_one_le k) (by omega)) (sq_nonneg _)) hBsum
  have hMsum : Summable M := Summable.of_nonneg_of_le (fun k => by
    rw [hM]; exact mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) _) (sq_nonneg _)) (fun k => by
    rw [hM, hB]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (wt_one_le k) (Nat.le_add_right s r)) (sq_nonneg _)) hBsum
  have hMB : ∀ k, M k ^ 2 = A k * B k := by
    intro k
    rw [hM, hA, hB]
    simp only []
    have h1 : (wt k ^ s) ^ 2 = wt k ^ (s - r) * wt k ^ (s + r) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    calc (wt k ^ s * ‖c k‖ ^ 2) ^ 2
        = (wt k ^ s) ^ 2 * (‖c k‖ ^ 2) ^ 2 := by rw [mul_pow]
      _ = (wt k ^ (s - r) * wt k ^ (s + r)) * (‖c k‖ ^ 2 * ‖c k‖ ^ 2) := by rw [h1, sq]
      _ = (wt k ^ (s - r) * ‖c k‖ ^ 2) * (wt k ^ (s + r) * ‖c k‖ ^ 2) := by ring
  have hkey : ∀ t : Finset (ι → ℤ), (∑ k ∈ t, M k) ^ 2 ≤ (∑' k, A k) * (∑' k, B k) := by
    intro t
    have h1 : (∑ k ∈ t, M k) ^ 2 ≤ (∑ k ∈ t, A k) * (∑ k ∈ t, B k) :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul t (fun k _ => hAnn k) (fun k _ => hBnn k)
        (fun k _ => (hMB k).le)
    calc (∑ k ∈ t, M k) ^ 2 ≤ (∑ k ∈ t, A k) * (∑ k ∈ t, B k) := h1
      _ ≤ (∑' k, A k) * (∑' k, B k) := by
          refine mul_le_mul (Summable.sum_le_tsum t (fun k _ => hAnn k) hAsum)
            (Summable.sum_le_tsum t (fun k _ => hBnn k) hBsum) ?_ ?_
          · exact Finset.sum_nonneg (fun k _ => hBnn k)
          · exact tsum_nonneg hAnn
  have hlim : Filter.Tendsto (fun t : Finset (ι → ℤ) => (∑ k ∈ t, M k) ^ 2) atTop
      (nhds ((∑' k, M k) ^ 2)) := by
    have hh := hMsum.hasSum
    simp only [HasSum, SummationFilter.unconditional_filter] at hh
    exact hh.pow 2
  simpa only [CSq, hM, hA, hB] using le_of_tendsto' hlim hkey

end Work.Diff.STE

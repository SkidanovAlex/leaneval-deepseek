import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.InnerProductSpace.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Regularity

open Filter Set
open scoped Topology

/-- If `f` is constant on the closed interval `[a, b]` (with `a < b`), then its derivative
vanishes at every point of `[a, b]`: at interior points `f` is locally constant, and at the
endpoints `f` is frequently equal to `f x` on the punctured neighbourhoods, so the derivative
is zero (either `f` is not differentiable there, or the derivative is forced to be `0`). -/
theorem deriv_eq_zero_of_const_on_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f x = f y) :
    ∀ x ∈ Set.Icc a b, deriv f x = 0 := by
  intro x hx
  -- It suffices that `f` frequently equals `f x` on the punctured neighbourhood of `x`.
  apply deriv_zero_of_frequently_const
  rw [Filter.frequently_iff]
  intro U hU
  -- A punctured neighbourhood contains `ball x ε \ {x}`.
  rw [Metric.mem_nhdsWithin_iff] at hU
  obtain ⟨ε, hε, hball⟩ := hU
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · -- `x < b`: step to the right into `(x, b) ⊆ [a, b]`.
    set d : ℝ := min (ε / 2) ((b - x) / 2) with hd
    have hdpos : 0 < d := by rw [hd]; exact lt_min (by linarith) (by linarith)
    refine ⟨x + d, hball ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq]
      have h1 : x + d - x = d := by ring
      rw [h1, abs_of_pos hdpos]
      have h2 : d ≤ ε / 2 := by rw [hd]; exact min_le_left _ _
      linarith
    · exact ne_of_gt (by linarith)
    · have hyb : x + d < b := by
        have h2 : d ≤ (b - x) / 2 := by rw [hd]; exact min_le_right _ _
        linarith
      exact hf _ ⟨hx.1.trans (by linarith), hyb.le⟩ x hx
  · -- `x = b`: step to the left into `(a, b) ⊆ [a, b]`.
    have hax : a < x := by rw [heq]; exact hab
    set d : ℝ := min (ε / 2) ((x - a) / 2) with hd
    have hdpos : 0 < d := by rw [hd]; exact lt_min (by linarith) (by linarith)
    refine ⟨x - d, hball ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq]
      have h1 : x - d - x = -d := by ring
      rw [h1, abs_neg, abs_of_pos hdpos]
      have h2 : d ≤ ε / 2 := by rw [hd]; exact min_le_left _ _
      linarith
    · exact ne_of_lt (by linarith)
    · have had : a < x - d := by
        have h2 : d ≤ (x - a) / 2 := by rw [hd]; exact min_le_right _ _
        linarith
      have hxb : x - d ≤ b := by rw [← heq]; linarith
      exact hf _ ⟨had.le, hxb⟩ x hx

end Work.FTS.Regularity

import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Op

theorem norm_sum_single_four {s : Finset ℤ} {f : ℤ → ℂ} {L : ℝ} (hL : 0 ≤ L) (hs : s.card ≤ 4)
    (h : ∀ i ∈ s, ‖f i‖ ≤ L) : ‖∑ i ∈ s, lp.single 2 i (f i)‖ ≤ 2 * L := by
  -- The vectors `lp.single 2 i (f i)` have pairwise disjoint supports, so the squared norm of
  -- their sum is the sum of the squared norms.
  have hnorm : ‖∑ i ∈ s, lp.single 2 i (f i)‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
    have hh := lp.norm_sum_single (E := fun _ : ℤ => ℂ) (p := 2) (by norm_num) f s
    simpa using hh
  have hsq : ‖∑ i ∈ s, lp.single 2 i (f i)‖ ^ 2 ≤ (2 * L) ^ 2 := by
    rw [hnorm]
    calc ∑ i ∈ s, ‖f i‖ ^ 2 ≤ ∑ _i ∈ s, L ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hi' := h i hi
          nlinarith [norm_nonneg (f i), hL]
      _ = (s.card : ℝ) * L ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 4 * L ^ 2 := by
          have hcard : (s.card : ℝ) ≤ 4 := by exact_mod_cast hs
          nlinarith [sq_nonneg L]
      _ = (2 * L) ^ 2 := by ring
  have h2 : |‖∑ i ∈ s, lp.single 2 i (f i)‖| ≤ |2 * L| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by linarith)] at h2

end Work.TMC16Core.Op

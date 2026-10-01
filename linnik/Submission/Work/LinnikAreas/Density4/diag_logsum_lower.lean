import Mathlib
import Submission.Work.LinnikAreas.Density4.dls_exp_floor_bounds
import Submission.Work.LinnikAreas.Density4.dls_term_bound

namespace Work.LinnikAreas.Density4

/-- Elementary quadratic bound: on the interval `[M-2, M-1]` the concave quadratic
`y ↦ (M-1)·y - y²/2` is at least its value at the left endpoint `M-2`, namely `M²/2 - M`. -/
lemma dls_log_quad_le (M y : ℝ) (hy1 : M - 2 ≤ y) (hy2 : y ≤ M - 1) :
    M ^ 2 / 2 - M ≤ (M - 1) * y - y ^ 2 / 2 := by
  nlinarith [sq_nonneg (y - (M - 1) + 1), sq_nonneg (y - (M - 1))]

theorem diag_logsum_lower (M : ℝ) (hM : 15000 ≤ M) :
    0.45 * M^2 ≤ ∑ n ∈ Finset.Icc 2 ⌊Real.exp (M-2)⌋₊, (M - 1 - Real.log n)/(n:ℝ) := by
  set N : ℕ := ⌊Real.exp (M - 2)⌋₊ with hN
  obtain ⟨h2N, hLgt, hLle⟩ := dls_exp_floor_bounds M hM N hN
  have hNle : (N : ℝ) ≤ Real.exp (M - 2) := by
    rw [hN]; exact Nat.floor_le (le_of_lt (Real.exp_pos (M - 2)))
  set G : ℕ → ℝ := fun k => (M - 1) * Real.log (k : ℝ) - (Real.log (k : ℝ)) ^ 2 / 2 with hG
  -- termwise telescoping comparison
  have hterm : ∀ n ∈ Finset.Icc 2 N, G (n + 1) - G n ≤ (M - 1 - Real.log (n : ℝ)) / (n : ℝ) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : 1 ≤ n := by omega
    have hlog : Real.log (n : ℝ) ≤ M - 2 := by
      have hcast : (n : ℝ) ≤ Real.exp (M - 2) :=
        le_trans (Nat.cast_le.mpr hn.2) hNle
      calc Real.log (n : ℝ) ≤ Real.log (Real.exp (M - 2)) :=
            Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) hcast
        _ = M - 2 := Real.log_exp _
    have := dls_term_bound M n hn1 hlog
    simpa only [hG] using this
  have htel : ∑ n ∈ Finset.Icc 2 N, (G (n + 1) - G n) = G (N + 1) - G 2 :=
    Finset.sum_Icc_sub h2N G
  have hsum : G (N + 1) - G 2 ≤ ∑ n ∈ Finset.Icc 2 N, (M - 1 - Real.log (n : ℝ)) / (n : ℝ) := by
    rw [← htel]
    exact Finset.sum_le_sum hterm
  -- evaluate the telescoped endpoint
  have hGN : G (N + 1) = (M - 1) * Real.log ((N : ℝ) + 1) - (Real.log ((N : ℝ) + 1)) ^ 2 / 2 := by
    simp only [hG]; push_cast; ring
  have hG2 : G 2 = (M - 1) * Real.log (2 : ℝ) - (Real.log (2 : ℝ)) ^ 2 / 2 := by
    simp only [hG]; push_cast; ring
  have hquad := dls_log_quad_le M (Real.log ((N : ℝ) + 1)) (le_of_lt hLgt) hLle
  have hg2le : G 2 ≤ M - 1 := by
    rw [hG2]
    have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hlog2pos : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    nlinarith [hlog2le, hlog2pos, hM, sq_nonneg (Real.log (2 : ℝ))]
  have hfin : 0.45 * M ^ 2 ≤ M ^ 2 / 2 - 2 * M + 1 := by nlinarith [sq_nonneg (M - 20)]
  have hglow : 0.45 * M ^ 2 ≤ G (N + 1) - G 2 := by
    rw [hGN]
    linarith [hquad, hg2le, hfin]
  linarith [hglow, hsum]

end Work.LinnikAreas.Density4

import Mathlib
import Submission.Work.ZeroDensity.Montgomery.zeroDetAltPerronAux

namespace Work.ZeroDensity.Montgomery

/-- The L-series of the truncated Möbius–character coefficients `n ↦ μ(n)χ(n)·[n ≤ X]`
is the truncated Möbius Dirichlet polynomial `M_X(s,χ) = Σ_{n ≤ ⌊X⌋₊} μ(n)χ(n)n^{-s}`. -/
theorem muTrunc_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ) (s : ℂ) :
    LSeries (muTrunc χ X) s = MX χ X s := by
  rw [LSeries, MX]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊X⌋₊) (fun n hn => ?_)]
  · refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mem_Icc] at hn
    obtain ⟨hn1, hnX⟩ := hn
    have hn0 : n ≠ 0 := by omega
    rw [LSeries.term, if_neg hn0, muTrunc, if_pos ?_]
    · rw [Complex.cpow_neg]; ring
    · have hX1 : (1:ℝ) ≤ X := (Nat.floor_pos).mp (by omega)
      exact le_trans (by exact_mod_cast hnX) (Nat.floor_le (by linarith))
  · rw [Finset.mem_Icc, not_and_or] at hn
    rw [LSeries.term, muTrunc]
    by_cases h0 : n = 0
    · rw [if_pos h0]
    · rw [if_neg h0]
      rcases hn with h | h
      · simp only [not_le] at h; omega
      · simp only [not_le] at h
        have : X < (n:ℝ) := by
          have h1 : (⌊X⌋₊ : ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast h
          have h2 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
          linarith
        rw [if_neg (not_le.mpr this), zero_div]

end Work.ZeroDensity.Montgomery

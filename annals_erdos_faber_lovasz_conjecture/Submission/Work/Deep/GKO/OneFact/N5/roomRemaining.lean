import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFact.N5.Basic

namespace Work.Deep.GKO.OneFact.N5

/-- Truncated subtraction of naturals, compared as reals: the real difference is always dominated
by the (monotone) cast of the truncated difference. -/
private lemma natCast_sub_le (a b : ℕ) : (a : ℝ) - (b : ℝ) ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_or_gt b a with h | h
  · rw [Nat.cast_sub h]
  · have hzero : a - b = 0 := Nat.sub_eq_zero_of_le (le_of_lt h)
    rw [hzero, Nat.cast_zero]
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast le_of_lt h
    linarith

/-- The room computation of the completion step.  The global hypothesis `hroomD` has the term
`3 * (5*n*m/L) + 14*s + m + L + 1` on the left; if the forbidden set has `f` vertices with
`f ≤ 5*n*m/L` (the "few vertices re-matched `L` times" bound), then the running degree parameter
`D₀ - (m+L) - f` still leaves room: `ε n + 2f + 14 s < D₀ - (m+L) - f`.  Note the factor `3`: two
`f` for the forbidden set itself plus one `f` for the degree loss. -/
theorem roomRemaining {n : ℕ} {ε : ℝ} {s m L D₀ f : ℕ}
    (hf : f ≤ 5 * n * m / L)
    (hroomD : ε * (n : ℝ) + ((3 * (5 * n * m / L) + 14 * s + m + L + 1 : ℕ) : ℝ) < (D₀ : ℝ)) :
    ε * (n : ℝ) + ((2 * f + 14 * s : ℕ) : ℝ) < ((D₀ - (m + L) - f : ℕ) : ℝ) := by
  -- The `3 * (5*n*m/L) + 14*s + m + L + 1` of `hroomD` in real terms.
  have hcast1 : ((3 * (5 * n * m / L) + 14 * s + m + L + 1 : ℕ) : ℝ)
      = 3 * ((5 * n * m / L : ℕ) : ℝ) + 14 * (s : ℝ) + (m : ℝ) + (L : ℝ) + 1 := by
    push_cast; ring
  rw [hcast1] at hroomD
  have hfR : (f : ℝ) ≤ ((5 * n * m / L : ℕ) : ℝ) := by exact_mod_cast hf
  have hcast2 : ((2 * f + 14 * s : ℕ) : ℝ) = 2 * (f : ℝ) + 14 * (s : ℝ) := by
    push_cast; ring
  -- Real form of the goal: `ε n + 2f + 14s + (m + L) + f < D₀`.  The hypothesis gives
  -- `ε n + 3(5nm/L) + 14s + m + L + 1 < D₀`, and `3f ≤ 3(5nm/L)` supplies the missing factor.
  have key : ε * (n : ℝ) + (2 * (f : ℝ) + 14 * (s : ℝ))
      < (D₀ : ℝ) - ((m + L : ℕ) : ℝ) - (f : ℝ) := by
    push_cast
    linarith
  rw [hcast2]
  -- Replace the truncated `ℕ`-subtraction on the right by the real one.
  refine lt_of_lt_of_le key ?_
  have hb1 := natCast_sub_le D₀ (m + L)
  have hb2 := natCast_sub_le (D₀ - (m + L)) f
  linarith

end Work.Deep.GKO.OneFact.N5

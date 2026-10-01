import Mathlib

namespace Work.LinnikAreas.Density4

/-- Telescoping the logarithmic increments of the harmonic product:
`∑_{n ∈ [a, b)} log ((n+1)/n) = log (b/a)` for `1 ≤ a ≤ b`. -/
lemma sum_Ico_log_div (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, Real.log (((n:ℝ) + 1) / (n:ℝ)) = Real.log ((b:ℝ) / (a:ℝ)) := by
  have ha0 : (a:ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp ha)
  have hb1 : 1 ≤ b := le_trans ha hab
  have hb0 : (b:ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hb1)
  -- each summand is an increment `f (n+1) - f n` of `f n = log n`
  let f : ℕ → ℝ := fun n => Real.log (n:ℝ)
  have hterm : ∀ n ∈ Finset.Ico a b, Real.log (((n:ℝ) + 1) / (n:ℝ)) = f (n+1) - f n := by
    intro n hn
    have h1 : 1 ≤ n := le_trans ha (Finset.mem_Ico.mp hn).1
    have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp h1)
    have hc : ((n:ℝ) + 1) = ((n+1 : ℕ) : ℝ) := by push_cast; ring
    simp only [f]
    rw [hc, Real.log_div (by positivity) hn0]
  have hs : ∑ n ∈ Finset.Ico a b, Real.log (((n:ℝ) + 1) / (n:ℝ))
      = ∑ n ∈ Finset.Ico a b, (f (n+1) - f n) :=
    Finset.sum_congr rfl hterm
  rw [hs, Finset.sum_Ico_sub f hab]
  simp only [f]
  rw [Real.log_div hb0 ha0]

end Work.LinnikAreas.Density4

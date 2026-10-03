import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface

namespace Work.KMTAreas.A7

/-- **The index of a lacunary scale below `X` is at most `log X / log Λ + 1`.**

Since `a` is `Λ`-lacunary with `a n ≥ 1`, it grows at least geometrically: `Λ ^ n ≤ a n`
(`Work.Analysis.EndVar.pow_le_of_lacunary`).  Hence `a n < X` forces `Λ ^ n < X`, and taking
logarithms gives `n · log Λ < log X`, i.e. `n < log X / log Λ`.  The stated `K` is the floor of
that quotient plus `2`, so that `K ≤ log X / log Λ + 2` and every admissible `n` is `< K`. -/
theorem lacunary_index_bound (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (X : ℝ) (hX : 1 ≤ X) :
    ∃ K : ℕ, (K : ℝ) ≤ Real.log X / Real.log (Λ : ℝ) + 2 ∧
      ∀ n : ℕ, (a n : ℝ) < X → n < K := by
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hlogΛpos : 0 < Real.log (Λ : ℝ) := Real.log_pos hΛR
  have hlogXnonneg : 0 ≤ Real.log X := Real.log_nonneg hX
  refine ⟨Nat.floor (Real.log X / Real.log (Λ : ℝ)) + 2, ?_, ?_⟩
  · have hfloor := Nat.floor_le (div_nonneg hlogXnonneg hlogΛpos.le)
    push_cast
    linarith
  · intro n hn
    have hpow : (Λ : ℝ) ^ n ≤ (a n : ℝ) := by
      have h := Work.Analysis.EndVar.pow_le_of_lacunary hΛ ha ha1 n
      exact_mod_cast h
    have hlt : (Λ : ℝ) ^ n < X := lt_of_le_of_lt hpow hn
    have hloglt : Real.log ((Λ : ℝ) ^ n) < Real.log X :=
      Real.log_lt_log (by positivity) hlt
    rw [Real.log_pow] at hloglt
    have hnlt : (n : ℝ) < Real.log X / Real.log (Λ : ℝ) := by
      rw [lt_div_iff₀ hlogΛpos]
      exact hloglt
    have h1 : (n : ℝ) < ((Nat.floor (Real.log X / Real.log (Λ : ℝ)) + 1 : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one (Real.log X / Real.log (Λ : ℝ))
      push_cast
      linarith
    have h2 : n < Nat.floor (Real.log X / Real.log (Λ : ℝ)) + 1 := by exact_mod_cast h1
    omega

end Work.KMTAreas.A7

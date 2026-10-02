import Mathlib
import Submission.Work.LinnikAreas.Density4.Udecay.abel_sum_by_parts
import Submission.Work.LinnikAreas.Density4.Udecay.muRecipSum_eq_sum_range

namespace Work.LinnikAreas.Density4.Udecay

open Finset

/-!
# Finite Abel summation for `Σ μ(n)/n`

This file proves the finite (partial) Abel summation identity relating the Abel-weighted partial
sums `Σ_{m ≤ M} muRecipSum m · (m^{-s} - (m+1)^{-s})` of the step weights to the partial Dirichlet
sum `Σ_{n ≤ M} μ(n)/n^{1+s}` and the boundary term `muRecipSum M · (M+1)^{-s}`.

The proof is the general summation-by-parts lemma `abel_sum_by_parts` instantiated at the
coefficient sequence `a n = μ(n)/n` and the weight `g m = m^{-s}`; the only arithmetic input is
`(μ(n)/n)·n^{-s} = μ(n)/n^{1+s}` for `n ≥ 1` (and both sides vanish at `n = 0`).
-/

/-- Finite Abel summation identity: the partial Abel sum of `muRecipSum m = Σ_{n ≤ m} μ(n)/n`
against the step weights `m^{-s} - (m+1)^{-s}` equals the partial Dirichlet sum of
`μ(n)/n^{1+s}` minus the boundary term `muRecipSum M * (M+1)^{-s}`. -/
theorem abel_finite_identity (s : ℝ) (M : ℕ) :
    (∑ m ∈ Finset.range (M + 1),
        Commons.NumberTheory.Moebius.muRecipSum m *
          ((m : ℝ) ^ (-s) - ((m : ℝ) + 1) ^ (-s)))
      = (∑ n ∈ Finset.range (M + 1),
          (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ (1 + s : ℝ))
        - Commons.NumberTheory.Moebius.muRecipSum M * ((M : ℝ) + 1) ^ (-s) := by
  -- cast bookkeeping: `(m+1 : ℕ)` coerced to `ℝ` is `(m : ℝ) + 1`
  have hcast : ∀ m : ℕ, (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by
    intro m; push_cast; ring
  -- the single arithmetic input: `(μ n / n) * n^{-s} = μ n / n^{1+s}` for `n ≥ 1`
  have hterm : ∀ n : ℕ, 1 ≤ n →
      ((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) * (n : ℝ) ^ (-s)
        = (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ (1 + s : ℝ) := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [Real.rpow_neg (le_of_lt hn0) s, Real.rpow_add hn0, Real.rpow_one]
    field_simp
  -- rewrite the Abel sum into the shape required by `abel_sum_by_parts`
  have hL : (∑ m ∈ Finset.range (M + 1),
        Commons.NumberTheory.Moebius.muRecipSum m *
          ((m : ℝ) ^ (-s) - ((m : ℝ) + 1) ^ (-s)))
      = (∑ m ∈ Finset.range (M + 1),
          (∑ n ∈ Finset.range (m + 1), (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) *
            ((m : ℝ) ^ (-s) - (((m + 1 : ℕ) : ℝ)) ^ (-s))) := by
    apply Finset.sum_congr rfl
    intro m _
    rw [muRecipSum_eq_sum_range m, hcast m]
  -- the Dirichlet side: termwise replacement of `μ n / n · n^{-s}`
  have h1 : (∑ n ∈ Finset.range (M + 1),
        (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) * (n : ℝ) ^ (-s))
      = (∑ n ∈ Finset.range (M + 1),
          (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ (1 + s : ℝ)) := by
    apply Finset.sum_congr rfl
    intro n _
    rcases n with _ | n
    · simp [ArithmeticFunction.moebius]
    · exact hterm (n + 1) (Nat.le_add_left 1 n)
  -- the boundary side
  have h2 : (∑ n ∈ Finset.range (M + 1), (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) *
        (((M + 1 : ℕ) : ℝ)) ^ (-s)
      = Commons.NumberTheory.Moebius.muRecipSum M * ((M : ℝ) + 1) ^ (-s) := by
    rw [← muRecipSum_eq_sum_range M, hcast M]
  rw [hL, abel_sum_by_parts, h1, h2]

end Work.LinnikAreas.Density4.Udecay

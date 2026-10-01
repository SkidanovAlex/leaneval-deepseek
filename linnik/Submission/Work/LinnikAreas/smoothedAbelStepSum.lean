import Mathlib
import Submission.Work.LinnikAreas.RatioDefs

namespace Work.LinnikAreas

/-- For `u ≤ x`, the summatory function `A(u) = Σ_{n ≤ ⌊u⌋} λ(n)` agrees with the partial
sum over `n ∈ [1, x]` of `λ(n)` restricted to the indices with `n ≤ u`.  This is the step
function identity `A(u) = Σ_{n ≤ x} λ(n)·1_{n ≤ u}` used to convert the Abel-type integral
`∫ (… )·A(u) du` into a finite sum over the coefficients. -/
theorem smoothedAbelStepSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℕ) :
    ∀ u : ℝ, u ≤ (x:ℝ) → Work.LinnikAreas.Asum χ u
      = ∑ n ∈ Finset.Icc 1 x, Work.LinnikAreas.lam χ n * (if (n:ℝ) ≤ u then (1:ℂ) else 0) := by
  intro u hu
  -- `⌊u⌋₊ ≤ x` because `u ≤ x`.
  have hux : ⌊u⌋₊ ≤ x := Nat.floor_le_of_le hu
  -- The indices of `[1, x]` that are `≤ u` are exactly `[1, ⌊u⌋₊]`.
  have hfilter : (Finset.Icc 1 x).filter (fun n : ℕ => (n:ℝ) ≤ u) = Finset.Icc 1 ⌊u⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, hnu⟩
      exact ⟨h1, Nat.le_floor hnu⟩
    · rintro ⟨h1, hn⟩
      refine ⟨⟨h1, le_trans hn hux⟩, ?_⟩
      -- `1 ≤ n ≤ ⌊u⌋₊` forces `1 ≤ u`, hence `⌊u⌋₊ ≤ u`.
      have h1floor : 1 ≤ ⌊u⌋₊ := le_trans h1 hn
      have h1u : (1:ℝ) ≤ u := (Nat.one_le_floor_iff u).mp h1floor
      have hle : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le (by linarith)
      exact le_trans (by exact_mod_cast hn) hle
  -- Rewrite the requested right-hand side as a plain sum over `[1, ⌊u⌋₊]`.
  have hRHS : (∑ n ∈ Finset.Icc 1 x, lam χ n * (if (n:ℝ) ≤ u then (1:ℂ) else 0))
      = ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, lam χ n := by
    rw [← hfilter, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun n _ => by by_cases h : (n:ℝ) ≤ u <;> simp [h])
  rw [Asum, hRHS]

end Work.LinnikAreas

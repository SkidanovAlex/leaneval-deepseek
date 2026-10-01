import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes

namespace Commons.NumberTheory.DirichletCharacter

/-- Interchange the finite sum over `i : ι` with the sum over `n ∈ s`; both sums
commute with the multiplication by `η i` and by `a n`. -/
lemma halasz_sum_swap {ι : Type*} [Fintype ι] (s : Finset ℕ)
    (a : ℕ → ℂ) (f : ι → ℕ → ℂ) (η : ι → ℂ) :
    (∑ i, η i * ∑ n ∈ s, a n * f i n) = ∑ n ∈ s, a n * ∑ i, η i * f i n := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- Weighted Cauchy–Schwarz inequality on a finite set of integers: for complex
functions `a`, `g` and a positive weight `β`,
`‖∑ₙ aₙ gₙ‖² ≤ (∑ₙ ‖aₙ‖²/βₙ) (∑ₙ βₙ ‖gₙ‖²)`. -/
lemma halasz_weighted_cauchy_schwarz (s : Finset ℕ) (a g : ℕ → ℂ) (β : ℕ → ℝ)
    (hβ : ∀ n ∈ s, 0 < β n) :
    ‖∑ n ∈ s, a n * g n‖ ^ 2
      ≤ (∑ n ∈ s, ‖a n‖ ^ 2 / β n) * (∑ n ∈ s, β n * ‖g n‖ ^ 2) := by
  -- Triangle inequality reduces the norm of the sum to a sum of norms.
  have htri : ‖∑ n ∈ s, a n * g n‖ ≤ ∑ n ∈ s, ‖a n‖ * ‖g n‖ := by
    calc ‖∑ n ∈ s, a n * g n‖ ≤ ∑ n ∈ s, ‖a n * g n‖ := norm_sum_le _ _
      _ = ∑ n ∈ s, ‖a n‖ * ‖g n‖ := by simp only [norm_mul]
  -- Weighted Cauchy–Schwarz on the resulting nonnegative real sum.
  have hsq : (∑ n ∈ s, ‖a n‖ * ‖g n‖) ^ 2
      ≤ (∑ n ∈ s, ‖a n‖ ^ 2 / β n) * (∑ n ∈ s, β n * ‖g n‖ ^ 2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro n hn
      exact div_nonneg (sq_nonneg _) (le_of_lt (hβ n hn))
    · intro n hn
      exact mul_nonneg (le_of_lt (hβ n hn)) (sq_nonneg _)
    · intro n hn
      have hb : β n ≠ 0 := ne_of_gt (hβ n hn)
      have h : (‖a n‖ ^ 2 / β n) * (β n * ‖g n‖ ^ 2) = ‖a n‖ ^ 2 * ‖g n‖ ^ 2 := by
        field_simp
      rw [mul_pow, h]
  calc ‖∑ n ∈ s, a n * g n‖ ^ 2
      ≤ (∑ n ∈ s, ‖a n‖ * ‖g n‖) ^ 2 := by
        simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) htri
    _ ≤ (∑ n ∈ s, ‖a n‖ ^ 2 / β n) * (∑ n ∈ s, β n * ‖g n‖ ^ 2) := hsq

theorem halasz_inequality {ι : Type*} [Fintype ι] {N : ℕ}
    (a : ℕ → ℂ) (β : ℕ → ℝ) (hβ : ∀ n ∈ Finset.Icc 1 N, 0 < β n)
    (f : ι → ℕ → ℂ) (η : ι → ℂ) :
    ‖∑ i, η i * ∑ n ∈ Finset.Icc 1 N, a n * f i n‖ ^ 2
      ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / β n) *
        (∑ n ∈ Finset.Icc 1 N, β n * ‖∑ i, η i * f i n‖ ^ 2) := by
  rw [halasz_sum_swap (Finset.Icc 1 N) a f η]
  exact halasz_weighted_cauchy_schwarz (Finset.Icc 1 N) a
    (fun n => ∑ i, η i * f i n) β hβ

end Commons.NumberTheory.DirichletCharacter
import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs

open scoped LSeries.notation

namespace Work.FIArea5.S16Hecke

/-- The Dirichlet series `Σ_n τ(n) n^{-σ}` (with `τ(n) = n.divisors.card` the number of divisors) converges for `σ > 1`; its value is `ζ(σ)²`.  This is the analytic input that makes the Hecke `L`-series `L(s,ψ) = Σ_n λ(n)n^{-s}` absolutely convergent on `re s > 1`, given the elementary bound `‖λ(n)‖ ≤ 4 τ(n)`. -/
lemma summable_card_divisors_mul_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (n.divisors.card : ℝ) * (n : ℝ) ^ (-σ)) := by
  -- `τ = 1 * 1` is the Dirichlet convolution of the constant sequence `1` with itself,
  -- and `ζ(s) = L(1)` is summable for `re s > 1`; convolution of summable `L`-series is summable.
  have hone : LSeriesSummable (fun _ : ℕ => (1 : ℂ)) (σ : ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => by simp) (by simpa using hσ)
  have hconv : LSeriesSummable ((fun _ : ℕ => (1 : ℂ)) ⍟ (fun _ : ℕ => (1 : ℂ))) (σ : ℂ) :=
    hone.convolution hone
  -- identify the convolution with the divisor-counting function (agreement on `n ≠ 0` suffices)
  have hval : ∀ {n : ℕ}, n ≠ 0 →
      ((fun _ : ℕ => (1 : ℂ)) ⍟ (fun _ : ℕ => (1 : ℂ))) n = (n.divisors.card : ℂ) := by
    intro n _
    rw [LSeries.convolution_def]
    simp only [mul_one]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    rw [← Nat.map_div_right_divisors, Finset.card_map]
  have hcard : LSeriesSummable (fun n : ℕ => (n.divisors.card : ℂ)) (σ : ℂ) :=
    (LSeriesSummable_congr (σ : ℂ) hval).mp hconv
  -- extract the (absolutely convergent) real series from the `L`-series of `τ`
  have hnn : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n : ℕ => (n.divisors.card : ℂ)) (σ : ℂ) n‖) := hcard.norm
  refine hnn.congr ?_
  intro n
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [if_neg hn, Complex.norm_natCast, div_eq_mul_inv, Real.rpow_neg (Nat.cast_nonneg n)]
    simp

end Work.FIArea5.S16Hecke

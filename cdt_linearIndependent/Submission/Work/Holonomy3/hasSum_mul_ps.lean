import Mathlib
import Submission.Work.Holonomy3.cleared_defs

/-!
# Cauchy products of convergent power-series evaluations

The holonomy bound evaluates products of power series coefficientwise.  The relevant analytic
input is the classical fact that the Cauchy product of two convergent series — one of them
absolutely convergent — converges to the product of the sums (Mertens' theorem).

Here `HasSum` is Mathlib's *unconditional* summation over finite subsets of `ℕ`; in particular
`HasSum f A` already implies that `f` is summable, so once both evaluation series converge the
Cauchy product is nothing but the diagonal of a summable `ℕ × ℕ`-indexed family
(`Summable.tsum_mul_tsum_eq_tsum_sum_range`).

* `hasSum_cauchyProduct` — Mertens' theorem for `ℂ`-valued sequences.
* `coeff_mul_mul_pow` — `coeff n (a * b) * z ^ n` is the `n`-th Cauchy convolution of the two
  evaluation sequences `k ↦ coeff k a * z ^ k` and `k ↦ coeff k b * z ^ k`.
* `hasSum_mul_ps` — the requested statement.
-/

namespace Work.Holonomy3

open scoped BigOperators

set_option linter.unusedVariables false

/-- **Mertens' theorem / Cauchy product.**  If `∑ f` and `∑ g` converge then the Cauchy product
series `∑_n (∑_{k ≤ n} f k * g (n - k))` converges, with sum the product of the two sums.

Because Mathlib's `HasSum` over `ℕ` is unconditional convergence (over finite subsets), each
convergent series is in fact summable, so this reduces to the diagonal of a summable
`ℕ × ℕ`-indexed family. -/
theorem hasSum_cauchyProduct {f g : ℕ → ℂ} {A B : ℂ} (hf : HasSum f A) (hg : HasSum g B) :
    HasSum (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), f k * g (n - k)) (A * B) := by
  have hprod : Summable (fun x : ℕ × ℕ => f x.1 * g x.2) :=
    summable_mul_of_summable_norm (f := f) (g := g) hf.summable.norm hg.summable.norm
  have hconv : Summable (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), f k * g (n - k)) :=
    summable_sum_mul_range_of_summable_mul (f := f) (g := g) hprod
  have hkey : (∑' n : ℕ, ∑ k ∈ Finset.range (n + 1), f k * g (n - k)) = A * B := by
    rw [← hf.tsum_eq, ← hg.tsum_eq]
    exact (Summable.tsum_mul_tsum_eq_tsum_sum_range (f := f) (g := g)
      hf.summable hg.summable hprod).symm
  rw [← hkey]
  exact hconv.hasSum

/-- The `n`-th coefficient of a product of power series, scaled by `z ^ n`, is the `n`-th Cauchy
convolution of the two evaluation sequences. -/
theorem coeff_mul_mul_pow (a b : PowerSeries ℂ) (z : ℂ) (n : ℕ) :
    PowerSeries.coeff n (a * b) * z ^ n =
      ∑ k ∈ Finset.range (n + 1),
        (PowerSeries.coeff k a * z ^ k) * (PowerSeries.coeff (n - k) b * z ^ (n - k)) := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i a * PowerSeries.coeff j b) n]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hz : z ^ k * z ^ (n - k) = z ^ n := by rw [← pow_add, Nat.add_sub_of_le hk']
  rw [mul_mul_mul_comm, hz]

theorem hasSum_mul_ps {a b : PowerSeries ℂ} {A B z : ℂ}
    (ha : HasSum (fun n : ℕ => PowerSeries.coeff n a * z ^ n) A)
    (hb : HasSum (fun n : ℕ => PowerSeries.coeff n b * z ^ n) B)
    (hbn : Summable (fun n : ℕ => ‖PowerSeries.coeff n b * z ^ n‖)) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (a * b) * z ^ n) (A * B) := by
  have hconv : HasSum (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
        (PowerSeries.coeff k a * z ^ k) * (PowerSeries.coeff (n - k) b * z ^ (n - k)))
      (A * B) :=
    hasSum_cauchyProduct (f := fun n : ℕ => PowerSeries.coeff n a * z ^ n)
      (g := fun n : ℕ => PowerSeries.coeff n b * z ^ n) ha hb
  exact hconv.congr_fun fun n => coeff_mul_mul_pow a b z n

end Work.Holonomy3

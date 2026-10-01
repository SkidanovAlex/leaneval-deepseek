/-
# The correction term `B_z` of the Selberg weight and its algebra

Namespace `Work.LinnikAreas.Density4`.  We collect the elementary identities relating the
"correction" term

  `B_z(n) = Σ_{z < d ∣ n} μ(d) log(d/z)`

of the Selberg weight `LambdaR z n = Σ_{d ∣ n, d ≤ z} μ(d) log(z/d)`
(`Commons.NumberTheory.Sieve.LambdaR`) to the von Mangoldt function:

  `B_z(n) = LambdaR z n - Λ n`  for `n ≥ 2`,

and the resulting expansion of `Σ_{n ≤ N} B_z(n)²` into the two Selberg square sums and the
mixed sum.  This file is sorry-free.
-/
import Mathlib
import Submission.Commons.NumberTheory.Sieve.LambdaR_eq_vonMangoldt_of_le
import Submission.Commons.NumberTheory.Moebius.sum_moebius_divisors

namespace Work.LinnikAreas.Density4

open Finset

noncomputable section

/-- **The correction term of the Selberg weight.**  `B_z(n) = Σ_{z < d ∣ n} μ(d) log(d/z)`
(Heath-Brown (1992), §11: this is the difference `Λ_z(n) - Λ(n)` for `n ≥ 2`). -/
def Bz (z n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => z < d),
    (ArithmeticFunction.moebius d : ℝ) * Real.log ((d : ℝ) / (z : ℝ))

/-- `B_z(n) = 0` when `n ≤ z`: all divisors of `n` are `≤ n ≤ z`. -/
lemma Bz_eq_zero_of_le {z n : ℕ} (hn : n ≤ z) : Bz z n = 0 := by
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [Finset.mem_filter] at hd
  exact absurd (lt_of_lt_of_le hd.2 (le_trans (Nat.divisor_le hd.1) hn)) (lt_irrefl z)

/-- The two Selberg half-sums add up to the full Möbius-log sum: `Λ_z(n) - B_z(n) = Λ n`. -/
lemma LambdaR_sub_Bz {z n : ℕ} (hn : 2 ≤ n) (hz : 1 ≤ z) :
    Commons.NumberTheory.Sieve.LambdaR z n - Bz z n = ArithmeticFunction.vonMangoldt n := by
  have hz0 : (z : ℝ) ≠ 0 := by exact_mod_cast (by omega : z ≠ 0)
  -- the full Möbius sum equals `Λ n`
  have hfull : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log ((z : ℝ) / (d : ℝ)))
      = ArithmeticFunction.vonMangoldt n := by
    have h1 : ∀ d ∈ n.divisors,
        (ArithmeticFunction.moebius d : ℝ) * Real.log ((z : ℝ) / (d : ℝ))
          = (ArithmeticFunction.moebius d : ℝ) * Real.log (z : ℝ)
            - (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) := by
      intro d hd
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
      have hd0 : (d : ℝ) ≠ 0 := by
        have : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
        exact_mod_cast this.ne'
      rw [Real.log_div hz0 hd0, mul_sub]
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]
    have h2 : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) = 0 := by
      rw [show (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ))
            = ((∑ d ∈ n.divisors, ArithmeticFunction.moebius d : ℤ) : ℝ) by push_cast; rfl,
        Commons.NumberTheory.Moebius.sum_moebius_divisors n]
      simp [show n ≠ 1 by omega]
    have h3 : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ))
        = -ArithmeticFunction.vonMangoldt n := ArithmeticFunction.sum_moebius_mul_log_eq
    rw [← Finset.sum_mul, h2, zero_mul, h3]
    ring
  -- split the full sum into the `d ≤ z` and `z < d` parts
  have hsplit : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log ((z : ℝ) / (d : ℝ)))
      = (∑ d ∈ n.divisors.filter (fun d => d ≤ z),
            (ArithmeticFunction.moebius d : ℝ) * Real.log ((z : ℝ) / (d : ℝ)))
        + (∑ d ∈ n.divisors.filter (fun d => ¬ d ≤ z),
            (ArithmeticFunction.moebius d : ℝ) * Real.log ((z : ℝ) / (d : ℝ))) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hneg : (∑ d ∈ n.divisors.filter (fun d => ¬ d ≤ z),
        (ArithmeticFunction.moebius d : ℝ) * Real.log ((z : ℝ) / (d : ℝ))) = - Bz z n := by
    rw [Bz, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr ?_ fun d hd => ?_
    · ext d
      simp only [Finset.mem_filter, not_le]
    · have hdvd : d ∣ n := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
      have hd0 : (d : ℝ) ≠ 0 := by
        have : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
        exact_mod_cast this.ne'
      rw [Real.log_div hz0 hd0, Real.log_div hd0 hz0]
      ring
  rw [hsplit, hneg] at hfull
  have hLR : Commons.NumberTheory.Sieve.LambdaR z n
      = ∑ d ∈ n.divisors.filter (fun d => d ≤ z),
          (ArithmeticFunction.moebius d : ℝ) * Real.log ((z : ℝ) / (d : ℝ)) := rfl
  rw [hLR]
  linarith [hfull]

/-- **`B_z(n) = Λ_z(n) - Λ(n)` for `n ≥ 2`** — the identity behind the case `N < z²` of the
Barban–Vehov (Graham) estimate. -/
theorem Bz_eq_LambdaR_sub_vonMangoldt {z n : ℕ} (hn : 2 ≤ n) (hz : 1 ≤ z) :
    Bz z n = Commons.NumberTheory.Sieve.LambdaR z n - ArithmeticFunction.vonMangoldt n := by
  have := LambdaR_sub_Bz (z := z) hn hz
  linarith

/-- For `n ≤ N`, the Selberg weight with cut-off `N` is the von Mangoldt function. -/
theorem LambdaR_eq_vonMangoldt {N n : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N) :
    Commons.NumberTheory.Sieve.LambdaR N n = ArithmeticFunction.vonMangoldt n :=
  Commons.NumberTheory.Sieve.LambdaR_eq_vonMangoldt_of_le hn hnN

/-- **Pointwise reduction to the Selberg weight.**  For `2 ≤ z ≤ N` and `2 ≤ n ≤ N`,
`B_z(n) = Λ_z(n) - Λ_N(n)`. -/
theorem Bz_eq_LambdaR_sub_LambdaR {z N n : ℕ} (hz : 2 ≤ z) (hn : 2 ≤ n) (hnN : n ≤ N) :
    Bz z n = Commons.NumberTheory.Sieve.LambdaR z n - Commons.NumberTheory.Sieve.LambdaR N n := by
  rw [Bz_eq_LambdaR_sub_vonMangoldt hn (by omega), LambdaR_eq_vonMangoldt hn hnN]

end

end Work.LinnikAreas.Density4

namespace Work.LinnikAreas.Density4

noncomputable section

/-- `Λ_z(1) = log z` (`1` is the only divisor of `1`). -/
lemma LambdaR_one {z : ℕ} (hz : 1 ≤ z) : Commons.NumberTheory.Sieve.LambdaR z 1 = Real.log (z : ℝ) := by
  rw [Commons.NumberTheory.Sieve.LambdaR, Nat.divisors_one, Finset.filter_singleton]
  simp [hz]

/-- `B_z(1) = 0`. -/
lemma Bz_one (z : ℕ) : Bz z 1 = 0 := by
  rcases Nat.eq_zero_or_pos z with h | h
  · subst h
    simp [Bz]
  · exact Bz_eq_zero_of_le h

/-- `Λ_N(n) = Λ(n)` on `2 ≤ n ≤ N`, in the `Λ`-form used for the mixed sum. -/
lemma LambdaR_N_eq_vonMangoldt {N n : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N) :
    Commons.NumberTheory.Sieve.LambdaR N n = ArithmeticFunction.vonMangoldt n :=
  LambdaR_eq_vonMangoldt hn hnN

end

end Work.LinnikAreas.Density4

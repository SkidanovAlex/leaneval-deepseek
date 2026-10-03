import Mathlib
import Submission.Work.FIArea7.sum_divisors_mul_of_coprime

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea7.P231M

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The weighted divisor sum `∑_{d ∣ n} τ(d) · d^{-11/12}` appearing in the statement. -/
def tauWeightSum (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, ((d.divisors.card : ℕ) : ℝ) * (d : ℝ) ^ (-(11 / 12 : ℝ))

lemma tauWeightSum_zero : tauWeightSum 0 = 0 := by
  simp [tauWeightSum]

lemma tauWeightSum_one : tauWeightSum 1 = 1 := by
  simp [tauWeightSum]

/-- `τ(d)·d^{-11/12}` is multiplicative in `d`. -/
lemma tauWeightSum_mul_coprime {m n : ℕ} (hmn : m.Coprime n) :
    tauWeightSum (m * n) = tauWeightSum m * tauWeightSum n := by
  simp only [tauWeightSum]
  refine Work.FIArea7.sum_divisors_mul_of_coprime
    (g := fun d => ((d.divisors.card : ℕ) : ℝ) * (d : ℝ) ^ (-(11 / 12 : ℝ))) hmn ?_
  intro a b hab
  have hτ : ((a * b).divisors.card : ℝ) = (a.divisors.card : ℝ) * (b.divisors.card : ℝ) := by
    rw [Nat.Coprime.card_divisors_mul hab]; push_cast; ring
  have hpow : ((a * b : ℕ) : ℝ) ^ (-(11 / 12 : ℝ))
      = (a : ℝ) ^ (-(11 / 12 : ℝ)) * (b : ℝ) ^ (-(11 / 12 : ℝ)) := by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  rw [hτ, hpow]
  ring

/-- The value of `tauWeightSum` at a prime power: the divisors of `p^a` are `p^j`, `0 ≤ j ≤ a`,
with `τ(p^j) = j+1`. -/
lemma sumTauWeightPrimePow (p a : ℕ) (hp : p.Prime) :
    tauWeightSum (p ^ a)
      = ∑ j ∈ Finset.range (a + 1), (((j + 1 : ℕ)) : ℝ) * ((p : ℝ) ^ (-(11 / 12 : ℝ))) ^ j := by
  rw [tauWeightSum, Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hcard : (((p ^ j).divisors.card : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) := by
    rw [Nat.divisors_prime_pow hp j, Finset.card_map, Finset.card_range]
  have hpow : ((p ^ j : ℕ) : ℝ) ^ (-(11 / 12 : ℝ))
      = ((p : ℝ) ^ (-(11 / 12 : ℝ))) ^ j := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) j,
      ← Real.rpow_natCast ((p : ℝ) ^ (-(11 / 12 : ℝ))) j,
      ← Real.rpow_mul (Nat.cast_nonneg p) (j : ℝ) (-(11 / 12 : ℝ)),
      ← Real.rpow_mul (Nat.cast_nonneg p) (-(11 / 12 : ℝ)) (j : ℝ)]
    congr 1
    ring
  rw [hcard, hpow]

/-- The truncated arithmetico-geometric sum is bounded by the full series `(1-x)^{-2}`. -/
lemma geomTauWeightLe (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (a : ℕ) :
    (∑ j ∈ Finset.range (a + 1), (((j + 1 : ℕ)) : ℝ) * x ^ j) ≤ ((1 - x) ^ 2)⁻¹ := by
  have hnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1
  have hfun : (fun j : ℕ => (((j + 1 : ℕ)) : ℝ) * x ^ j)
      = (fun n : ℕ => ((((n + 1).choose 1 : ℕ)) : ℝ) * x ^ n) := by
    funext n
    rw [Nat.choose_one_right]
  have hsum : HasSum (fun j : ℕ => (((j + 1 : ℕ)) : ℝ) * x ^ j) (((1 - x) ^ 2)⁻¹) := by
    have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 (r := x) hnorm
    rw [one_div, ← hfun] at h
    exact h
  have hle := hsum.summable.sum_le_tsum (Finset.range (a + 1))
    (fun j _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0 j))
  rwa [hsum.tsum_eq] at hle

theorem divisorsTauWeight (n : ℕ) (hn : 1 ≤ n) :
    (∑ d ∈ n.divisors, ((d.divisors.card : ℕ) : ℝ) * (d : ℝ) ^ (-(11 / 12 : ℝ)))
      ≤ ∏ p ∈ n.primeFactors, ((1 - (p : ℝ) ^ (-(11 / 12 : ℝ))) ^ 2)⁻¹ := by
  have hn0 : n ≠ 0 := by omega
  let F : ArithmeticFunction ℝ := ⟨tauWeightSum, tauWeightSum_zero⟩
  have hmult : F.IsMultiplicative :=
    ⟨by dsimp only [F]; exact tauWeightSum_one,
     by
       intro m n hmn
       dsimp only [F]
       exact tauWeightSum_mul_coprime hmn⟩
  have hfac : tauWeightSum n = ∏ p ∈ n.primeFactors, tauWeightSum (p ^ n.factorization p) := by
    have h := ArithmeticFunction.IsMultiplicative.multiplicative_factorization F hmult hn0
    dsimp only [F] at h
    exact h
  change tauWeightSum n ≤ ∏ p ∈ n.primeFactors, ((1 - (p : ℝ) ^ (-(11 / 12 : ℝ))) ^ 2)⁻¹
  rw [hfac]
  refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
  · have hpP : p.Prime := (Nat.mem_primeFactors.mp hp).1
    rw [sumTauWeightPrimePow p (n.factorization p) hpP]
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) j))
  · have hpP : p.Prime := (Nat.mem_primeFactors.mp hp).1
    rw [sumTauWeightPrimePow p (n.factorization p) hpP]
    refine geomTauWeightLe ((p : ℝ) ^ (-(11 / 12 : ℝ)))
      (Real.rpow_nonneg (Nat.cast_nonneg p) _) ?_ (n.factorization p)
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpP.two_le
    exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)

end

end Work.FIArea7.P231M

import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- Gauss' summation formula over `ℤ`: `2 * ∑_{k < n} k = n * (n - 1)`. -/
private lemma sum_range_cast_mul_two (n : ℕ) :
    (∑ k ∈ Finset.range n, (k : ℤ)) * 2 = (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    push_cast
    ring

/-- The sum of cubes identity over `ℤ`: `∑_{k < n} k³ = (∑_{k < n} k)²`. -/
private lemma sum_range_cubes_int (m : ℕ) :
    ∑ k ∈ Finset.range m, (k : ℤ)^3 = (∑ k ∈ Finset.range m, (k : ℤ))^2 := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h := sum_range_cast_mul_two n
    have h' : 2 * (∑ k ∈ Finset.range n, (k : ℤ)) = (n : ℤ) * ((n : ℤ) - 1) := by
      linarith [h]
    have h2 : (n : ℤ)^3
        = 2*(∑ k ∈ Finset.range n, (k : ℤ))*(n : ℤ) + (n : ℤ)^2 := by
      calc (n : ℤ)^3 = (n : ℤ)^2 * (n : ℤ) := by ring
        _ = (n : ℤ)^2 * ((n : ℤ) - 1) + (n : ℤ)^2 := by ring
        _ = ((n : ℤ) * ((n : ℤ) - 1)) * (n : ℤ) + (n : ℤ)^2 := by ring
        _ = (2 * (∑ k ∈ Finset.range n, (k : ℤ))) * (n : ℤ) + (n : ℤ)^2 := by rw [← h']
        _ = 2*(∑ k ∈ Finset.range n, (k : ℤ))*(n : ℤ) + (n : ℤ)^2 := by ring
    rw [h2]; ring

/-- The sum of cubes identity over `ℕ`: `∑_{k < n} k³ = (∑_{k < n} k)²`. -/
private lemma sum_range_cubes (m : ℕ) :
    ∑ k ∈ Finset.range m, k^3 = (∑ k ∈ Finset.range m, k)^2 := by
  apply Nat.cast_injective (R := ℤ)
  push_cast
  exact sum_range_cubes_int m

/-- Shifted form of the sum of cubes identity, convenient for divisor sums on prime powers. -/
private lemma sum_range_succ_cubes (m : ℕ) :
    ∑ j ∈ Finset.range m, (j+1)^3 = (∑ j ∈ Finset.range m, (j+1))^2 := by
  have h := sum_range_cubes (m+1)
  rw [Finset.sum_range_succ' (fun k => k^3) m] at h
  rw [Finset.sum_range_succ' (fun k => k) m] at h
  simpa using h

/-- The arithmetic function `n ↦ τ(n)³`, where `τ(n) = #n.divisors`. -/
private def tau3 : ArithmeticFunction ℕ := ⟨fun n => (n.divisors.card)^3, by simp⟩

private lemma tau3_isMultiplicative : ArithmeticFunction.IsMultiplicative tau3 := by
  refine ⟨?_, ?_⟩
  · show ((1:ℕ).divisors.card)^3 = 1
    simp
  · intro m n hmn
    show ((m*n).divisors.card)^3 = ((m.divisors.card)^3) * ((n.divisors.card)^3)
    rw [Nat.Coprime.card_divisors_mul hmn]
    ring

/-- Both sides of the identity, viewed as arithmetic functions, agree: they are multiplicative
and agree on prime powers, where the identity reduces to `∑ k³ = (∑ k)²`. -/
private lemma tau3_mul_zeta_eq :
    tau3 * ArithmeticFunction.zeta =
      ((ArithmeticFunction.sigma 0) * ArithmeticFunction.zeta).ppow 2 := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ ?_ _ ?_).2 ?_
  · exact tau3_isMultiplicative.mul ArithmeticFunction.isMultiplicative_zeta
  · exact (ArithmeticFunction.isMultiplicative_sigma.mul
      ArithmeticFunction.isMultiplicative_zeta).ppow
  · intro p i hp
    have hcard : ∀ x, (p^x).divisors.card = x + 1 := fun x => by
      rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
    have hL : (∑ x ∈ Finset.range (i+1), tau3 (p^x)) =
        ∑ x ∈ Finset.range (i+1), (x+1)^3 := by
      apply Finset.sum_congr rfl
      intro x _
      show ((p^x).divisors.card)^3 = (x+1)^3
      rw [hcard x]
    have hR : (∑ x ∈ Finset.range (i+1), (ArithmeticFunction.sigma 0) (p^x)) =
        ∑ x ∈ Finset.range (i+1), (x+1) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [ArithmeticFunction.sigma_zero_apply, hcard x]
    rw [ArithmeticFunction.mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
      ArithmeticFunction.ppow_apply (by norm_num : 0 < 2),
      ArithmeticFunction.mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
      hL, hR, sum_range_succ_cubes]

theorem tau_cube_sum_eq_sq_sum (n : ℕ) :
    ∑ d ∈ n.divisors, (d.divisors.card)^3 = (∑ d ∈ n.divisors, d.divisors.card)^2 := by
  have h1 : (tau3 * ArithmeticFunction.zeta) n = ∑ d ∈ n.divisors, (d.divisors.card)^3 := by
    rw [ArithmeticFunction.mul_zeta_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  have h2 : (((ArithmeticFunction.sigma 0) * ArithmeticFunction.zeta).ppow 2) n
      = (∑ d ∈ n.divisors, d.divisors.card)^2 := by
    rw [ArithmeticFunction.ppow_apply (by norm_num : 0 < 2),
      ArithmeticFunction.mul_zeta_apply]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [ArithmeticFunction.sigma_zero_apply]
  rw [← h1, tau3_mul_zeta_eq, h2]

end Commons.NumberTheory.FriedlanderIwaniec
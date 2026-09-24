import Mathlib
import Submission.Work.ChenPlan.LinearSieve.basic
import Submission.Work.ChenPlan.LinearSieve.Buchstab.moebius_identity

/-!
# The linear sieve statement when the level exceeds the modulus

When `D ≥ P = s.prodPrimes` every divisor of `P` is `< D`, so the truncated remainder sum
`remSum s D` dominates the whole Möbius remainder `Σ_{d ∣ P} μ(d) r_d`.  Together with the exact
identity `S = X V + Σ_{d ∣ P} μ(d) r_d` (`Buchstab.moebius_identity`) this gives both interface
bounds with no sieve hypothesis at all: the `D ≥ P` half of
`LinearSieveUpper`/`LinearSieveLower`.
-/

open Finset ArithmeticFunction
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve

/-- If `D ≥ prodPrimes` then all divisors of `prodPrimes` are below `D`. -/
theorem divisors_filter_eq_self (s : BoundingSieve) {D : ℝ} (hD : (s.prodPrimes : ℝ) < D) :
    s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < D) = s.prodPrimes.divisors := by
  refine Finset.filter_true_of_mem ?_
  intro d hd
  have hle : d ≤ s.prodPrimes := Nat.divisor_le hd
  have : (d : ℝ) ≤ (s.prodPrimes : ℝ) := by exact_mod_cast hle
  linarith

/-- The weighted truncated remainder dominates the Möbius remainder in absolute value. -/
theorem abs_moebiusRemSum_le_remSum (s : BoundingSieve) {D : ℝ}
    (hD : (s.prodPrimes : ℝ) < D) :
    |moebiusRemSum s| ≤ Submission.ChenPlan.remSum s D := by
  rw [moebiusRemSum, Submission.ChenPlan.remSum, divisors_filter_eq_self s hD]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun d _ => ?_
  have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ d.primeFactors.card := one_le_pow₀ (by norm_num)
  calc |((ArithmeticFunction.moebius d : ℤ) : ℝ) * s.rem d|
      = |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |s.rem d| := abs_mul _ _
    _ ≤ 1 * |s.rem d| := mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
    _ ≤ (3 : ℝ) ^ d.primeFactors.card * |s.rem d| :=
        mul_le_mul_of_nonneg_right h3 (abs_nonneg _)

/-- Upper bound, trivial case: `S ≤ X V + Σ_{d < D, d ∣ P} 3^{ω(d)} |r_d|` whenever `D ≥ P`. -/
theorem siftedSum_le_trivial (s : BoundingSieve) {D : ℝ} (hD : (s.prodPrimes : ℝ) < D) :
    s.siftedSum ≤ s.totalMass * Submission.ChenPlan.sieveV s + Submission.ChenPlan.remSum s D := by
  have := abs_moebiusRemSum_le_remSum s hD
  have h := Buchstab.moebius_identity s
  have hle : moebiusRemSum s ≤ Submission.ChenPlan.remSum s D := le_trans (le_abs_self _) this
  linarith

/-- Lower bound, trivial case: `X V c - Σ_{d < D, d ∣ P} 3^{ω(d)} |r_d| ≤ S` for every `c ≤ 1`,
whenever `D ≥ P` and `X ≥ 0`. -/
theorem trivial_le_siftedSum (s : BoundingSieve) {D c : ℝ} (hD : (s.prodPrimes : ℝ) < D)
    (hX : 0 ≤ s.totalMass) (hc : c ≤ 1) :
    s.totalMass * Submission.ChenPlan.sieveV s * c - Submission.ChenPlan.remSum s D
      ≤ s.siftedSum := by
  have h := abs_moebiusRemSum_le_remSum s hD
  have hid := Buchstab.moebius_identity s
  have hnn : 0 ≤ s.totalMass * Submission.ChenPlan.sieveV s := by
    refine mul_nonneg hX ?_
    rw [Submission.ChenPlan.sieveV]
    refine Finset.prod_nonneg fun p hp => ?_
    have hpP : p ∣ s.prodPrimes := (Nat.mem_primeFactors.mp hp).2.1
    have := s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) hpP
    linarith
  have hneg : -Submission.ChenPlan.remSum s D ≤ moebiusRemSum s := (abs_le.mp h).1
  linarith [mul_le_mul_of_nonneg_left hc hnn]

end Work.ChenPlan.LinearSieve

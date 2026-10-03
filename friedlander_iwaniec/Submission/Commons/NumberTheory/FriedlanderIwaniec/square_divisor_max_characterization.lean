import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Squarefree
import Mathlib.GroupTheory.GroupAction.Ring

/-!
# The largest square divisor of a natural number, and its squarefree cofactor

For `d > 0` the number
`P d = ∏_{p | d} p ^ (v_p(d) / 2)`
is the (divisibility-)largest `e` with `e ^ 2 ∣ d`: its square is the largest square
dividing `d`, and the complementary factor `d / (P d) ^ 2` is squarefree.  This is the
classical "square part / squarefree part" decomposition that underlies the
Friedlander--Iwaniec analysis of the primes captured by `x ^ 2 + y ^ 4`.

Mathlib already packages `P d` as `Nat.floorRoot 2 d`, the right adjoint of `a ↦ a ^ 2`
for the divisibility order (`Nat.pow_dvd_iff_dvd_floorRoot`), so the three assertions
reduce to elementary properties of `Nat.floorRoot` together with the fact that its
`p`-adic valuation is `v_p(d) / 2`.
-/

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

/-- The explicit product `∏_{p | d} p ^ (v_p(d) / 2)` agrees with `Nat.floorRoot 2 d`
whenever `d ≠ 0`. -/
private lemma prod_primeFactors_factorization_div_two_eq_floorRoot {d : ℕ} (hd : d ≠ 0) :
    (Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2)) = Nat.floorRoot 2 d := by
  rw [Nat.floorRoot, if_neg (by omega)]
  rw [Finsupp.prod, Nat.support_factorization]

/-- The `p`-adic valuation of `∏_{q | d} q ^ (v_q(d) / 2)` is `v_p(d) / 2`. -/
private lemma factorization_prod_primeFactors_factorization_div_two {d p : ℕ} (hd : d ≠ 0) :
    ((Nat.primeFactors d).prod (fun q => q ^ (d.factorization q / 2))).factorization p =
      d.factorization p / 2 := by
  rw [prod_primeFactors_factorization_div_two_eq_floorRoot hd, Nat.factorization_floorRoot]
  simp [Finsupp.floorDiv_apply]

lemma square_divisor_max_characterization {d : ℕ} (hd : 0 < d) :
    ((Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2))) ^ 2 ∣ d ∧
      Squarefree (d / ((Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2))) ^ 2) ∧
      ∀ e : ℕ, e ^ 2 ∣ d → e ∣ (Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2)) := by
  set P := (Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2)) with hP
  have hd0 : d ≠ 0 := by omega
  -- `P` is Mathlib's flooring square root of `d`.
  have hfl : P = Nat.floorRoot 2 d := prod_primeFactors_factorization_div_two_eq_floorRoot hd0
  have hfac : ∀ p, P.factorization p = d.factorization p / 2 := fun p =>
    factorization_prod_primeFactors_factorization_div_two hd0
  have hdvd : P ^ 2 ∣ d := by rw [hfl]; exact Nat.floorRoot_pow_dvd
  refine ⟨hdvd, ?_, ?_⟩
  · -- The cofactor is squarefree: its valuation at `p` is `v_p(d) mod 2 ≤ 1`.
    have hne : d / P ^ 2 ≠ 0 := by
      intro h0
      have h := Nat.div_mul_cancel hdvd
      rw [h0, zero_mul] at h
      omega
    refine Nat.squarefree_of_factorization_le_one hne ?_
    intro p
    rw [Nat.factorization_div hdvd]
    rw [Nat.factorization_pow]
    simp only [Finsupp.tsub_apply, Finsupp.smul_apply, nsmul_eq_mul, hfac]
    omega
  · -- Maximality: `floorRoot 2` is the right adjoint of `a ↦ a ^ 2`.
    intro e he
    rw [hfl]
    exact (Nat.pow_dvd_iff_dvd_floorRoot).mp he

end Commons.NumberTheory.FriedlanderIwaniec
import Mathlib
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.ChenPlan.LinearSieve.RI.lamMinus_sieve_lower

/-!
# The `λ⁻` remainder bound

`Work.ChenPlan.LinearSieve.RI.lamMinus_error_le`:

`|Σ_{d ∣ P(z)} λ⁻(d) · r_d| ≤ Σ_{d ∣ P, d < D} 3^{ω(d)} |r_d|`.

The Rosser–Iwaniec lower weight `λ⁻(d)` is supported on the *lower admissible* divisors of
`P(z)`, and every lower admissible `d` satisfies `d < D` as soon as the primes of `P(z)` are
below `z ≤ D`.  That is the content of `lt_of_rdMinus`: it is what makes the `3^{ω(d)}`-weighted
remainder `remSum` large enough to dominate the error term.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ChenPlan.LinearSieve.RI

noncomputable section

open Classical

attribute [local instance] Classical.propDecidable

/-- `Pz A z` is a divisor of `A.prodPrimes`. -/
lemma Pz_dvd_prodPrimes (A : BoundingSieve) (z : ℝ) : Pz A z ∣ A.prodPrimes := by
  have h := Finset.prod_dvd_prod_of_subset
    (A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z))
    A.prodPrimes.primeFactors (fun p => p) (Finset.filter_subset _ _)
  rw [Nat.prod_primeFactors_of_squarefree A.prodPrimes_squarefree] at h
  exact h

/-! ## Lower admissible numbers are below the level -/

/-- **Key support bound.**  A lower admissible divisor `d` of `Pz A z`, with `z ≤ D`, satisfies
`d < D`.

Indeed, if `ω(d)` is even then `cval d = d·(minFac d)² ≤ D` while `minFac d ≥ 2`.  If `ω(d)` is
odd the same bound applied to the even-`ω` divisor `e = d / minFac d` gives `cval e ≤ D`, and
`d < cval e` because `minFac e > minFac d` (squarefreeness); primes are handled by `d < z`. -/
lemma lt_of_rdMinus (A : BoundingSieve) {z D : ℝ} (hz : 2 ≤ z) (hzD : z ≤ D)
    {d : ℕ} (hddvd : d ∣ Pz A z) (hd : rdMinus D d) : (d : ℝ) < D := by
  have hPz0 : Pz A z ≠ 0 := Pz_ne_zero A z
  have hd0 : d ≠ 0 := fun h => hPz0 (Nat.eq_zero_of_zero_dvd (h ▸ hddvd))
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hddvd (Pz_squarefree A z)
  rcases eq_or_ne d 1 with rfl | hd1
  · push_cast
    linarith
  · by_cases hEv : Even d.primeFactors.card
    · have hmem : d ∈ d.divisors := Nat.mem_divisors_self d hd0
      have hc := hd d hmem hEv hd1
      have hmf : (2 : ℝ) ≤ (d.minFac : ℝ) := by
        exact_mod_cast (Nat.minFac_prime hd1).two_le
      have hdpos : (0 : ℝ) < (d : ℝ) := by
        exact_mod_cast Nat.pos_iff_ne_zero.mpr hd0
      have h4 : (4 : ℝ) ≤ (d.minFac : ℝ) ^ 2 := by nlinarith
      have hbig : (d : ℝ) * 4 ≤ D := by
        have h := mul_le_mul_of_nonneg_left h4 hdpos.le
        linarith
      nlinarith
    · have hOdd : Odd d.primeFactors.card := Nat.not_even_iff_odd.mp hEv
      by_cases hprime : d.Prime
      · have hmem : d ∈ (Pz A z).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hprime, hddvd, hPz0⟩
        rw [Pz_primeFactors] at hmem
        have : (d : ℝ) < z := (Finset.mem_filter.mp hmem).2
        linarith
      · set m := d.minFac with hm
        set e := d / m with he
        have hmprime : m.Prime := by rw [hm]; exact Nat.minFac_prime hd1
        have hmdvd : m ∣ d := by rw [hm]; exact Nat.minFac_dvd d
        have hedvd : e ∣ d := by rw [he]; exact Nat.div_dvd_of_dvd (Nat.minFac_dvd d)
        have hemul : e * m = d := by rw [he, hm]; exact Nat.div_mul_cancel (Nat.minFac_dvd d)
        have hemem : e ∈ d.divisors := Nat.mem_divisors.mpr ⟨hedvd, hd0⟩
        have hcard : d.primeFactors.card = e.primeFactors.card + 1 := by
          rw [he, hm]; exact card_mul_div_minFac d hsq hd1
        have hEve : Even e.primeFactors.card := by
          have hodd : Odd (e.primeFactors.card + 1) := by rw [← hcard]; exact hOdd
          exact even_of_odd_succ hodd
        have he1 : e ≠ 1 := by
          intro h
          have hdm : d = m := by rw [← hemul, h, one_mul]
          exact hprime (hdm ▸ hmprime)
        have hc := hd e hemem hEve he1
        have hemf2 : 2 ≤ e.minFac := (Nat.minFac_prime he1).two_le
        have hemfdvd : e.minFac ∣ d := dvd_trans (Nat.minFac_dvd e) hedvd
        have hle_m : m ≤ e.minFac := by
          rw [hm]; exact Nat.minFac_le_of_dvd hemf2 hemfdvd
        have hne_m : m ≠ e.minFac := by
          intro h
          have hmvdve : m ∣ e := h ▸ Nat.minFac_dvd e
          have hmm : m * m ∣ d := by
            obtain ⟨k, hk⟩ := hmvdve
            refine ⟨k, ?_⟩
            rw [← hemul, hk]; ring
          exact (Nat.squarefree_iff_prime_squarefree.mp hsq m hmprime) hmm
        have hltm : m < e.minFac := lt_of_le_of_ne hle_m hne_m
        have he0 : e ≠ 0 := div_ne_zero_of_dvd hedvd hd0
        have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast Nat.pos_iff_ne_zero.mpr he0
        have hmcast : (m : ℝ) < (e.minFac : ℝ) := by exact_mod_cast hltm
        have hdeq : (d : ℝ) = (e : ℝ) * (m : ℝ) := by
          rw [← hemul]; push_cast; ring
        have h1 : (e : ℝ) * (m : ℝ) < (e : ℝ) * (e.minFac : ℝ) :=
          mul_lt_mul_of_pos_left hmcast hepos
        have h2 : (e : ℝ) * (e.minFac : ℝ) ≤ (e : ℝ) * (e.minFac : ℝ) ^ 2 := by
          have hge1 : (1 : ℝ) ≤ (e.minFac : ℝ) := by
            have : (1 : ℕ) ≤ e.minFac := le_of_lt (Nat.minFac_prime he1).one_lt
            exact_mod_cast this
          have hsq' : (e.minFac : ℝ) ≤ (e.minFac : ℝ) ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_left hsq' hepos.le
        linarith [hc, hdeq, h1, h2]

/-! ## The weight of `λ⁻` is dominated by `3^{ω}` -/

lemma abs_lamMinus_le_card (P : ℕ) (D : ℝ) (d : ℕ) :
    |lamMinus P D d| ≤ (3 : ℝ) ^ d.primeFactors.card := by
  by_cases h : d ∣ P ∧ rdMinus D d
  · have hlm : lamMinus P D d = ((ArithmeticFunction.moebius d : ℤ) : ℝ) := by
      unfold lamMinus; rw [if_pos h]
    rw [hlm]
    have h1 : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h2 : (1 : ℝ) ≤ (3 : ℝ) ^ d.primeFactors.card := one_le_pow₀ (by norm_num)
    linarith
  · have hlm : lamMinus P D d = 0 := by unfold lamMinus; rw [if_neg h]
    rw [hlm, abs_zero]
    positivity

/-! ## The main statement -/

theorem lamMinus_error_le (A : BoundingSieve) {z D : ℝ} (hD : 0 ≤ D) (hz : 2 ≤ z) (hzD : z ≤ D) :
    |∑ d ∈ (Work.ChenPlan.LinearSieve.Pz A z).divisors,
        Work.ChenPlan.LinearSieve.lamMinus (Work.ChenPlan.LinearSieve.Pz A z) D d * A.rem d|
      ≤ Submission.ChenPlan.remSum A D := by
  classical
  have hPzdvd : Pz A z ∣ A.prodPrimes := Pz_dvd_prodPrimes A z
  set S := (Pz A z).divisors.filter (fun d : ℕ => lamMinus (Pz A z) D d ≠ 0) with hS
  set T := A.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < D) with hT
  have hTsum : (∑ d ∈ T, (3 : ℝ) ^ d.primeFactors.card * |A.rem d|)
      = Submission.ChenPlan.remSum A D := by
    rw [hT]
    unfold Submission.ChenPlan.remSum
    rfl
  rw [← hTsum]
  calc |∑ d ∈ (Pz A z).divisors, lamMinus (Pz A z) D d * A.rem d|
      ≤ ∑ d ∈ S, |lamMinus (Pz A z) D d| * |A.rem d| := by
        refine le_trans (Finset.abs_sum_le_sum_abs
          (fun d => lamMinus (Pz A z) D d * A.rem d) (Pz A z).divisors) ?_
        rw [hS, Finset.sum_filter]
        refine Finset.sum_le_sum (fun d hd => ?_)
        by_cases h : lamMinus (Pz A z) D d = 0
        · simp [h]
        · simp [h, abs_mul]
    _ ≤ ∑ d ∈ S, (3 : ℝ) ^ d.primeFactors.card * |A.rem d| :=
        Finset.sum_le_sum (fun d _ =>
          mul_le_mul_of_nonneg_right (abs_lamMinus_le_card _ _ _) (abs_nonneg _))
    _ ≤ ∑ d ∈ T, (3 : ℝ) ^ d.primeFactors.card * |A.rem d| := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro d hd
          rw [hS, Finset.mem_filter] at hd
          obtain ⟨hdmem, hne⟩ := hd
          have hdPz : d ∣ Pz A z := (Nat.mem_divisors.mp hdmem).1
          have hcond : d ∣ Pz A z ∧ rdMinus D d := by
            by_contra hc
            exact hne (by unfold lamMinus; rw [if_neg hc])
          have hlt : (d : ℝ) < D := lt_of_rdMinus A hz hzD hdPz hcond.2
          rw [hT, Finset.mem_filter]
          exact ⟨Nat.mem_divisors.mpr ⟨hdPz.trans hPzdvd, A.prodPrimes_ne_zero⟩, hlt⟩
        · intro d _ _
          exact mul_nonneg (by positivity) (abs_nonneg _)

end

end Work.ChenPlan.LinearSieve.RI

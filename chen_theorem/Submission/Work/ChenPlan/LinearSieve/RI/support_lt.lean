import Mathlib
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.ChenPlan.LinearSieve.RI.lamMinus_sieve_lower

/-!
# The support of the Rosser–Iwaniec weights lies below the level `D`

`Work.ChenPlan.LinearSieve.RI.support_lt`: every squarefree number carrying the upper
(`rdPlus`) or lower (`rdMinus`) Rosser–Iwaniec support condition is `< D` as a real number.

* upper: if `ω(d)` is odd, `d` itself is an odd-`ω` divisor, so `cval d = d·(minFac d)² ≤ D`
  and `minFac d ≥ 2` gives `d < D`.  If `ω(d)` is even (and `d ≠ 1`), the divisor
  `e = d / minFac d` has odd `ω`, so `cval e ≤ D`, and `d < cval e` because the smallest prime
  factor of `e` is strictly larger than `minFac d` (squarefreeness).
* lower: if `ω(d)` is even, `d` itself is admissible.  If `ω(d)` is odd, either `d` is a prime,
  in which case `d < z ≤ z² ≤ D`, or `e = d / minFac d` has even `ω` and `d < cval e ≤ D`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ChenPlan.LinearSieve.RI

noncomputable section

open Classical

attribute [local instance] Classical.propDecidable

/-- **Removing the smallest prime factor increases `cval`.**  If `d` is squarefree, `d ≠ 1`, and
`e · minFac d = d` with `e ≠ 1`, then `d < cval e`.  Indeed `minFac e > minFac d` because
`d` is squarefree, so `d = e · minFac d < e · minFac e ≤ e · (minFac e)² = cval e`. -/
lemma lt_cval_of_mul {d e : ℕ} (hsq : Squarefree d) (hd1 : d ≠ 1)
    (he : e * d.minFac = d) (he1 : e ≠ 1) : (d : ℝ) < cval e := by
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hmprime : (d.minFac).Prime := Nat.minFac_prime hd1
  have hemfprime : (e.minFac).Prime := Nat.minFac_prime he1
  have hemfdvd : e.minFac ∣ d := by
    rw [← he]; exact dvd_mul_of_dvd_left (Nat.minFac_dvd e) _
  have hle : d.minFac ≤ e.minFac := Nat.minFac_le_of_dvd hemfprime.two_le hemfdvd
  have hne : d.minFac ≠ e.minFac := by
    intro h
    have hmvdve : d.minFac ∣ e := h ▸ Nat.minFac_dvd e
    have hmm : d.minFac * d.minFac ∣ d := by
      obtain ⟨k, hk⟩ := hmvdve
      refine ⟨k, ?_⟩
      calc d = e * d.minFac := he.symm
        _ = d.minFac * k * d.minFac := by rw [hk]
        _ = d.minFac * d.minFac * k := by ring
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq d.minFac hmprime) hmm
  have hltm : d.minFac < e.minFac := lt_of_le_of_ne hle hne
  have he0 : e ≠ 0 := by
    intro h; rw [h, zero_mul] at he; exact hd0 he.symm
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast Nat.pos_iff_ne_zero.mpr he0
  have hmcast : (d.minFac : ℝ) < (e.minFac : ℝ) := by exact_mod_cast hltm
  have hdeq : (d : ℝ) = (e : ℝ) * (d.minFac : ℝ) := by
    have h1 : (d : ℝ) = ((e * d.minFac : ℕ) : ℝ) := by rw [he]
    rw [h1]; push_cast; ring
  have h1 : (e : ℝ) * (d.minFac : ℝ) < (e : ℝ) * (e.minFac : ℝ) :=
    mul_lt_mul_of_pos_left hmcast hepos
  have he1le : (1 : ℝ) ≤ (e.minFac : ℝ) := by
    have : (1 : ℕ) ≤ e.minFac := le_of_lt hemfprime.one_lt
    exact_mod_cast this
  have h2 : (e : ℝ) * (e.minFac : ℝ) ≤ (e : ℝ) * (e.minFac : ℝ) ^ 2 := by
    have hsq' : (e.minFac : ℝ) ≤ (e.minFac : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hsq' hepos.le
  unfold cval
  linarith

/-- An upper-admissible squarefree `d` satisfies `d < D` (for `D > 1`). -/
lemma rdPlus_lt {D : ℝ} (hD : 1 < D) {d : ℕ} (hsq : Squarefree d) (hd : rdPlus D d) :
    (d : ℝ) < D := by
  rcases eq_or_ne d 1 with h1 | hd1
  · subst h1; simp only [Nat.cast_one]; exact hD
  · have hd0 : d ≠ 0 := hsq.ne_zero
    by_cases hev : Even d.primeFactors.card
    · have hcard := card_mul_div_minFac d hsq hd1
      have hoddE : Odd (d / d.minFac).primeFactors.card := by
        apply odd_of_even_succ
        rw [← hcard]; exact hev
      have hemem : d / d.minFac ∈ d.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.minFac_dvd d), hd0⟩
      have hc : cval (d / d.minFac) ≤ D := hd _ hemem hoddE
      have hnp : ¬ d.Prime := by
        intro hp
        have hev' := hev
        rw [hp.primeFactors] at hev'
        obtain ⟨k, hk⟩ := hev'
        simp only [Finset.card_singleton] at hk
        omega
      have he1 : d / d.minFac ≠ 1 := by
        intro h
        have hdm : d = d.minFac := by
          calc d = d / d.minFac * d.minFac := (Nat.div_mul_cancel (Nat.minFac_dvd d)).symm
            _ = 1 * d.minFac := by rw [h]
            _ = d.minFac := one_mul _
        exact hnp (hdm.symm ▸ Nat.minFac_prime hd1)
      have hlt := lt_cval_of_mul hsq hd1 (Nat.div_mul_cancel (Nat.minFac_dvd d)) he1
      linarith
    · have hodd : Odd d.primeFactors.card := Nat.not_even_iff_odd.mp hev
      have hmem : d ∈ d.divisors := Nat.mem_divisors_self d hd0
      have hc : cval d ≤ D := hd d hmem hodd
      have hmf2 : (2 : ℝ) ≤ (d.minFac : ℝ) := by
        exact_mod_cast (Nat.minFac_prime hd1).two_le
      have hdpos : (0 : ℝ) < (d : ℝ) := by
        exact_mod_cast Nat.pos_iff_ne_zero.mpr hd0
      have hbig : (d : ℝ) * 4 ≤ cval d := by
        unfold cval
        have h4 : (4 : ℝ) ≤ (d.minFac : ℝ) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left h4 hdpos.le
      linarith

/-- A lower-admissible squarefree `d`, all of whose prime factors are `< z` with `z² ≤ D`,
satisfies `d < D` (for `D > 1`). -/
lemma rdMinus_lt {D z : ℝ} (hD : 1 < D) {d : ℕ} (hsq : Squarefree d)
    (hz : ∀ p ∈ d.primeFactors, (p : ℝ) < z) (hzD : z ^ 2 ≤ D) (hd : rdMinus D d) :
    (d : ℝ) < D := by
  rcases eq_or_ne d 1 with h1 | hd1
  · subst h1; simp only [Nat.cast_one]; exact hD
  · have hd0 : d ≠ 0 := hsq.ne_zero
    by_cases hev : Even d.primeFactors.card
    · have hmem : d ∈ d.divisors := Nat.mem_divisors_self d hd0
      have hc : cval d ≤ D := hd d hmem hev hd1
      have hmf2 : (2 : ℝ) ≤ (d.minFac : ℝ) := by
        exact_mod_cast (Nat.minFac_prime hd1).two_le
      have hdpos : (0 : ℝ) < (d : ℝ) := by
        exact_mod_cast Nat.pos_iff_ne_zero.mpr hd0
      have hbig : (d : ℝ) * 4 ≤ cval d := by
        unfold cval
        have h4 : (4 : ℝ) ≤ (d.minFac : ℝ) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left h4 hdpos.le
      linarith
    · by_cases hp : d.Prime
      · have hmem : d ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, dvd_rfl, hd0⟩
        have hdz : (d : ℝ) < z := hz d hmem
        have h2d : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hp.two_le
        have hz1 : (1 : ℝ) ≤ z := by linarith
        have hzsq : z ≤ z ^ 2 := by nlinarith
        linarith
      · have hcard := card_mul_div_minFac d hsq hd1
        have hEcard : Even (d / d.minFac).primeFactors.card := by
          apply even_of_odd_succ
          rw [← hcard]; exact Nat.not_even_iff_odd.mp hev
        have hemem : d / d.minFac ∈ d.divisors :=
          Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.minFac_dvd d), hd0⟩
        have he1 : d / d.minFac ≠ 1 := by
          intro h
          have hdm : d = d.minFac := by
            calc d = d / d.minFac * d.minFac := (Nat.div_mul_cancel (Nat.minFac_dvd d)).symm
              _ = 1 * d.minFac := by rw [h]
              _ = d.minFac := one_mul _
          exact hp (hdm.symm ▸ Nat.minFac_prime hd1)
        have hc : cval (d / d.minFac) ≤ D := hd _ hemem hEcard he1
        have hlt := lt_cval_of_mul hsq hd1 (Nat.div_mul_cancel (Nat.minFac_dvd d)) he1
        linarith

theorem support_lt {D z : ℝ} (hD : 1 < D) :
    (∀ d : ℕ, Squarefree d → rdPlus D d → (d : ℝ) < D) ∧
    (∀ d : ℕ, Squarefree d → (∀ p ∈ d.primeFactors, (p : ℝ) < z) → z ^ 2 ≤ D →
      rdMinus D d → (d : ℝ) < D) :=
  ⟨fun d hsq hd => rdPlus_lt hD hsq hd,
   fun d hsq hz hzD hd => rdMinus_lt hD hsq hz hzD hd⟩

end

end Work.ChenPlan.LinearSieve.RI

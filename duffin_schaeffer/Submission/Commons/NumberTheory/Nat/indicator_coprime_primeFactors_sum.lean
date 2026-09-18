import Mathlib
import Submission.Commons.Data.Nat.sum_powerset_neg_one_pow_card_real
import Submission.Commons.NumberTheory.Nat.prod_dvd_iff_all_dvd

namespace Commons.NumberTheory.Nat

open scoped BigOperators

/-- A natural `x` is coprime to a nonzero natural `q` iff no prime divisor of
`q` divides `x`. -/
theorem coprime_iff_not_dvd_primeFactors {x q : ℕ} (hq : q ≠ 0) :
    x.Coprime q ↔ ∀ p ∈ q.primeFactors, ¬ p ∣ x := by
  constructor
  · intro hc p hp hpd
    have hpP : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpq : p ∣ q := (Nat.mem_primeFactors.mp hp).2.1
    have hpg : p ∣ x.gcd q := Nat.dvd_gcd hpd hpq
    have hg : x.gcd q = 1 := hc
    exact hpP.not_dvd_one (by simpa [hg] using hpg)
  · intro h
    by_contra hc
    obtain ⟨p, hpP, hpg⟩ := Nat.exists_prime_and_dvd hc
    have hpx : p ∣ x := dvd_trans hpg (Nat.gcd_dvd_left x q)
    have hpq : p ∣ q := dvd_trans hpg (Nat.gcd_dvd_right x q)
    have hpIn : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hpP, hpq, hq⟩
    exact h p hpIn hpx

/-- Inclusion-exclusion over the prime factors of `q`: the indicator that
`x.Coprime q` equals `∑_{S ⊆ primeFactors q} (-1)^|S| [∏_{p ∈ S} p ∣ x]`. -/
theorem indicator_coprime_primeFactors_sum (q x : ℕ) (hq : q ≠ 0) :
    (if x.Coprime q then (1 : ℝ) else 0) =
      ∑ S ∈ q.primeFactors.powerset,
        (-1 : ℝ) ^ S.card * (if (∏ p ∈ S, p) ∣ x then 1 else 0) := by
  classical
  set P : Finset ℕ := q.primeFactors with hP
  set B : Finset ℕ := P.filter (fun p : ℕ => p ∣ x) with hB
  have hBP : B ⊆ P := by
    rw [hB]
    exact Finset.filter_subset (fun p : ℕ => p ∣ x) P
  -- `B` is empty exactly when `x` is coprime to `q`.
  have hcop : x.Coprime q ↔ B = ∅ := by
    simpa [hB, hP, Finset.filter_eq_empty_iff] using (coprime_iff_not_dvd_primeFactors (q := q) (x := x) hq)
  have hif : (if x.Coprime q then (1 : ℝ) else 0) = (if B = ∅ then (1 : ℝ) else 0) := by
    by_cases hc : x.Coprime q
    · have hB0 : B = ∅ := hcop.mp hc
      simp [hc, hB0]
    · have hBne : B ≠ ∅ := by
        intro hB0
        exact hc (hcop.mpr hB0)
      simp [hc, hBne]
  -- for `S` a subset of `P`, the divisibility of the product is equivalent to `S ⊆ B`
  have hSb (S : Finset ℕ) (hS : S ∈ P.powerset) : (∀ p ∈ S, p ∣ x) ↔ S ⊆ B := by
    constructor
    · intro hf p hp
      have hpP : p ∈ P := (Finset.mem_powerset.mp hS) hp
      rw [hB]
      exact Finset.mem_filter.mpr ⟨hpP, hf p hp⟩
    · intro hSB p hp
      have hpB : p ∈ B := hSB hp
      rw [hB] at hpB
      exact (Finset.mem_filter.mp hpB).2
  -- two indicator expressions with equivalent conditions are equal
  have mul_if_congr {c d : Prop} [Decidable c] [Decidable d] (hcd : c ↔ d) (a : ℝ) :
      a * (if c then (1 : ℝ) else 0) = a * (if d then (1 : ℝ) else 0) := by
    by_cases hc : c
    · have hd : d := hcd.mp hc
      rw [if_pos hc, if_pos hd]
    · have hd : ¬ d := fun hd => hc (hcd.mpr hd)
      rw [if_neg hc, if_neg hd]

  have hpf : P.powerset.filter (fun S : Finset ℕ => S ⊆ B) = B.powerset := by
    apply Finset.ext
    intro S
    constructor
    · intro hS
      exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hS).2
    · intro hS
      have hSB : S ⊆ B := Finset.mem_powerset.mp hS
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (by intro a ha; exact hBP (hSB ha)), hSB⟩
  calc
    (if x.Coprime q then (1 : ℝ) else 0) = (if B = ∅ then (1 : ℝ) else 0) := hif
    _ = ∑ S ∈ B.powerset, (-1 : ℝ) ^ S.card := by
      exact (Commons.Data.Nat.sum_powerset_neg_one_pow_card_real B).symm
    _ = ∑ S ∈ (P.powerset.filter (fun S : Finset ℕ => S ⊆ B)), (-1 : ℝ) ^ S.card := by
      rw [hpf]
    _ = ∑ S ∈ P.powerset, (if S ⊆ B then (-1 : ℝ) ^ S.card else 0) := by
      rw [Finset.sum_filter]
    _ = ∑ S ∈ P.powerset, (-1 : ℝ) ^ S.card * (if S ⊆ B then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro S hS
      by_cases h : S ⊆ B <;> simp [h]
    _ = ∑ S ∈ P.powerset, (-1 : ℝ) ^ S.card * (if ∀ p ∈ S, p ∣ x then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact mul_if_congr (hSb S hS).symm ((-1 : ℝ) ^ S.card)
    _ = ∑ S ∈ P.powerset, (-1 : ℝ) ^ S.card *
          (if (∏ p ∈ S, p) ∣ x then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro S hS
      have hdiv : (∏ p ∈ S, p) ∣ x ↔ ∀ p ∈ S, p ∣ x :=
        Commons.NumberTheory.Nat.prod_dvd_iff_all_dvd (q := q) (x := x) (S := S)
          (by simpa [hP] using (Finset.mem_powerset.mp hS))
      exact mul_if_congr hdiv.symm ((-1 : ℝ) ^ S.card)

end Commons.NumberTheory.Nat

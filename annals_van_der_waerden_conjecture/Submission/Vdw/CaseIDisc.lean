import Mathlib
import Submission.Vdw.Omega
import Submission.Vdw.CaseI

open scoped BigOperators

set_option autoImplicit false

/-!
# Case-I discriminant bookkeeping: large-prime / small-prime split (pure `ℕ`)

The Case-I per-discriminant sieve (`CaseIExact.perDiscriminant_exact_le`)
imposes mod-`p` index conditions at the primes `p` dividing the discriminant
`D`; Lemma 24 (field version, `ResidueCompare.lemma24_field_Kpoly`) only
guarantees `index ≥ v_p(D)` at primes `p > n` (tame primes).  Primes
`p ≤ n | D` with wild ramification need separate handling, and the road map
records that for `p ≤ n` the exponent `v_p(D)` is bounded by a constant
depending only on `n` (the classical wild-different bound
`Commons.NumberTheory.NumberField.wild_different_count_le`).

This module carries the *purely arithmetic* part of that bookkeeping: it
splits any `D ≠ 0` into its **large part** (supported on prime factors
`> n`) and **small part** (supported on prime factors `≤ n`):

* `discSplit` : `largePart n D * smallPart n D = D`;
* divisibility / omega / radical bounds for the two parts;
* `discSmallPart_le_primorial_pow` : if every prime `p ≤ n | D` divides `D`
  to exponent at most `C`, then `smallPart n D ≤ primorial n ^ C`, where
  `primorial n` is the product of the primes `≤ n` — a constant in `n` only.

Everything is in `namespace Submission.Vdw`; only `Omega` is imported,
keeping it dependency-light.
-/

namespace Submission.Vdw

/-- The part of `D` supported on prime factors `> n`. -/
noncomputable def discLargePart (n D : ℕ) : ℕ :=
  ∏ p ∈ (Nat.primeFactors D).filter (fun p => n < p), p ^ D.factorization p

/-- The part of `D` supported on prime factors `≤ n`. -/
noncomputable def discSmallPart (n D : ℕ) : ℕ :=
  ∏ p ∈ (Nat.primeFactors D).filter (fun p => p ≤ n), p ^ D.factorization p

/-- The product of the primes `≤ n` (the primorial). -/
noncomputable def primorial (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Icc 1 n).filter (fun p => Nat.Prime p), p

/-- `largePart` and `smallPart` have disjoint prime supports. -/
lemma discParts_disjoint (n D : ℕ) :
    Disjoint ((Nat.primeFactors D).filter (fun p => n < p))
      ((Nat.primeFactors D).filter (fun p => p ≤ n)) := by
  rw [Finset.disjoint_filter]
  intro p hp hpn hle
  exact (not_lt_of_ge hle) hpn

/-- The two filters cover all prime factors. -/
lemma discParts_union (n D : ℕ) :
    ((Nat.primeFactors D).filter (fun p => n < p) ∪
      (Nat.primeFactors D).filter (fun p => p ≤ n)) = Nat.primeFactors D := by
  ext p
  simp only [Finset.mem_union, Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · intro h
    rcases h with h | h <;> exact h.1
  · intro hp
    by_cases h : n < p
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, le_of_not_gt h⟩

/-- `discLargePart * discSmallPart = D` for `D ≠ 0`. -/
lemma discSplit (n D : ℕ) (hD : D ≠ 0) :
    discLargePart n D * discSmallPart n D = D := by
  unfold discLargePart discSmallPart
  calc
    (∏ p ∈ (Nat.primeFactors D).filter (fun p => n < p), p ^ D.factorization p) *
        (∏ p ∈ (Nat.primeFactors D).filter (fun p => p ≤ n), p ^ D.factorization p)
        = ∏ p ∈ ((Nat.primeFactors D).filter (fun p => n < p)) ∪
            ((Nat.primeFactors D).filter (fun p => p ≤ n)), p ^ D.factorization p := by
          rw [Finset.prod_union]
          exact discParts_disjoint n D
    _ = ∏ p ∈ Nat.primeFactors D, p ^ D.factorization p := by
          rw [discParts_union]
    _ = D := (Nat.prod_primeFactors_pow_factorization hD).symm

/-- The large part divides `D`. -/
lemma discLargePart_dvd (n D : ℕ) (hD : D ≠ 0) : discLargePart n D ∣ D := by
  exact ⟨discSmallPart n D, (discSplit n D hD).symm⟩

/-- The small part divides `D`. -/
lemma discSmallPart_dvd (n D : ℕ) (hD : D ≠ 0) : discSmallPart n D ∣ D := by
  exact ⟨discLargePart n D, by rw [mul_comm]; exact (discSplit n D hD).symm⟩

/-- Prime factors of a divisor of `D ≠ 0` are prime factors of `D`. -/
lemma primeFactors_subset_of_dvd {a b : ℕ} (hab : a ∣ b) (hb : b ≠ 0) :
    Nat.primeFactors a ⊆ Nat.primeFactors b := by
  intro p hp
  rcases Nat.mem_primeFactors.mp hp with ⟨pp, hpa, ha⟩
  exact Nat.mem_primeFactors.mpr ⟨pp, dvd_trans hpa hab, hb⟩

/-- omega of the large part is at most omega of `D`. -/
lemma omega_discLargePart_le (n D : ℕ) : omega (discLargePart n D) ≤ omega D := by
  by_cases hD : D = 0
  · subst hD
    simp [discLargePart, omega]
  · rw [omega, omega]
    exact Finset.card_le_card (primeFactors_subset_of_dvd (discLargePart_dvd n D hD) hD)

/-- omega of the small part is at most omega of `D`. -/
lemma omega_discSmallPart_le (n D : ℕ) : omega (discSmallPart n D) ≤ omega D := by
  by_cases hD : D = 0
  · subst hD
    simp [discSmallPart, omega]
  · rw [omega, omega]
    exact Finset.card_le_card (primeFactors_subset_of_dvd (discSmallPart_dvd n D hD) hD)

/-- The radical of the large part is at most the radical of `D`. -/
lemma radical_discLargePart_le (n D : ℕ) : radical (discLargePart n D) ≤ radical D := by
  by_cases hD : D = 0
  · subst hD
    simp [discLargePart, radical]
  · unfold radical
    exact Finset.prod_le_prod_of_subset_of_one_le
      (primeFactors_subset_of_dvd (discLargePart_dvd n D hD) hD)
      (by intro p hp; exact Nat.zero_le p)
      (by
        intro p hp hnp
        exact (Nat.mem_primeFactors.mp hp).1.one_le)

/-- The radical of the small part is at most the radical of `D`. -/
lemma radical_discSmallPart_le (n D : ℕ) : radical (discSmallPart n D) ≤ radical D := by
  by_cases hD : D = 0
  · subst hD
    simp [discSmallPart, radical]
  · unfold radical
    exact Finset.prod_le_prod_of_subset_of_one_le
      (primeFactors_subset_of_dvd (discSmallPart_dvd n D hD) hD)
      (by intro p hp; exact Nat.zero_le p)
      (by
        intro p hp hnp
        exact (Nat.mem_primeFactors.mp hp).1.one_le)

/-- The radical of `D` is the product over the prime factors of `D` of `p`
(the definition, recalled for rewriting). -/
lemma radical_eq_prod_primeFactors (D : ℕ) : radical D = ∏ p ∈ Nat.primeFactors D, p := rfl

/-- Small part bounded by `primorial n ^ C` when every small prime divides `D`
to exponent at most `C`. -/
theorem discSmallPart_le_primorial_pow (n C D : ℕ)
    (hle : ∀ p ∈ Nat.primeFactors D, p ≤ n → D.factorization p ≤ C) :
    discSmallPart n D ≤ primorial n ^ C := by
  classical
  let s : Finset ℕ := (Nat.primeFactors D).filter (fun p => p ≤ n)
  have hsub : s ⊆ (Finset.Icc 1 n).filter (fun p => Nat.Prime p) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpD, hpn⟩
    rcases Nat.mem_primeFactors.mp hpD with ⟨pp, hpd, hD⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨pp.one_le, hpn⟩, pp⟩
  calc
    discSmallPart n D = ∏ p ∈ s, p ^ D.factorization p := rfl
    _ ≤ ∏ p ∈ s, p ^ C := by
      refine Finset.prod_le_prod (by intro p hp; exact Nat.zero_le _) ?_
      intro p hp
      have hmem : p ∈ Nat.primeFactors D := (Finset.mem_filter.mp hp).1
      have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hmem).1
      exact Nat.pow_le_pow_right (by have h2 := Nat.Prime.two_le hpp; omega) (hle p hmem (Finset.mem_filter.mp hp).2)
    _ = (∏ p ∈ s, p) ^ C := by
      rw [Finset.prod_pow]
    _ ≤ (∏ p ∈ (Finset.Icc 1 n).filter (fun p => Nat.Prime p), p) ^ C := by
      refine Nat.pow_le_pow_left ?_ C
      exact Finset.prod_le_prod_of_subset_of_one_le hsub
        (by intro p hp; exact Nat.zero_le p)
        (by
          intro p hp hnp
          exact (Finset.mem_filter.mp hp).2.one_le)
    _ = primorial n ^ C := by
      unfold primorial
      rfl

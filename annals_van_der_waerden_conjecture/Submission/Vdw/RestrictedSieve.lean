import Mathlib
import Submission.Vdw.ResidueCompare
import Submission.Vdw.CaseI
import Submission.Vdw.CaseIDisc
import Submission.Commons.NumberTheory.NumberField.discriminant_valuation_sum

open Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Case-I direct regime: the restricted-prime sieve (entry layer)

The Case-I *direct-regime* assembly (S1 in the Roadmap, Session-41/42) counts
`{f : primitive-proper irreducible bad, C_f ≤ H, D_f > H^(2+2δ)}` per value
`D = D_f` of the field discriminant through the **restricted sieve** over the
*large* primes of `D` only (`p | D` with `p > n`): at those primes Lemma 24
(field version, `ResidueCompare.lemma24_field_Kpoly`) guarantees the residue
index condition `polyIndex(f̄ mod p) ≥ v_p(D_f)` — the entry into the sieve
set — while the small primes `p ≤ n | D` (whose index conditions can fail,
cyclic-cubic counterexample) are excluded from the sieve and absorbed as the
bounded factor `S = discSmallPart n D ≤ S₀(n)` once the wild different bound
(`WildBound.discrVal_le_wild`) is available.

This module is the (β) entry layer: `restrictedSieve_entry` is the per-prime
membership statement; `mem_primeFactors_discLargePart` extracts from
`p ∈ (discLargePart n D).primeFactors` the sieve hypotheses `n < p` and
`p | D` (pure-`ℕ`; the large part is supported exactly on the primes `> n`
dividing `D`).
-/

namespace Submission.Vdw

/-- **Restricted-sieve entry, per prime.**  For a monic irreducible integer
polynomial `f` of degree `n ≥ 1` and a prime `p > n` dividing `D_f =
fieldDisc f`: the residue index of `f` modulo `p` is at least the exponent
`v_p(D_f) = D_f.factorization p` (Lemma 24, field version). -/
theorem restrictedSieve_entry (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (hf : f.Monic) {n : ℕ} (hdeg : f.natDegree = n) (hnpos : 1 ≤ n) {p : ℕ}
    [Fact (Nat.Prime p)] (hpgt : n < p) (_hpD : p ∣ fieldDisc f) :
    (fieldDisc f).factorization p ≤
      polyIndex (F := ZMod p) (f.map (Int.castRingHom (ZMod p))) := by
  classical
  have hfac : (fieldDisc f).factorization p = padicValNat p (fieldDisc f) :=
    Nat.factorization_def (fieldDisc f) (Fact.out (p := Nat.Prime p))
  rw [hfac]
  exact lemma24_field_Kpoly f hf n hdeg hnpos p hpgt

/-- A prime factor of the large part `discLargePart n D` (the primes `> n`
dividing `D`, with their exponents) exceeds `n` and divides `D`. -/
lemma mem_primeFactors_discLargePart {n D : ℕ} (hD : D ≠ 0) {p : ℕ}
    (hp : p ∈ (discLargePart n D).primeFactors) : n < p ∧ p ∣ D := by
  classical
  rcases (Nat.mem_primeFactors.mp hp) with ⟨hpp, hpd, hz⟩
  let s := (Nat.primeFactors D).filter (fun q => n < q)
  have hld : discLargePart n D ∣ D := discLargePart_dvd n D hD
  have hpD : p ∣ D := dvd_trans hpd hld
  have hlt : n < p := by
    by_contra hnot
    have hpn : p ≤ n := le_of_not_gt hnot
    have hdiv : p ∣ ∏ q ∈ s, q ^ D.factorization q := by
      simpa [discLargePart, s] using hpd
    have hcop (q : ℕ) (hq : q ∈ s) : (q ^ D.factorization q).Coprime p := by
      have hqpf : q ∈ Nat.primeFactors D := (Finset.mem_filter.mp hq).1
      have hqp : q.Prime := (Nat.mem_primeFactors.mp hqpf).1
      have hne : q ≠ p := ne_of_gt (lt_of_le_of_lt hpn (Finset.mem_filter.mp hq).2)
      have hqcop : q.Coprime p := (Nat.coprime_primes hqp hpp).mpr hne
      exact Nat.Coprime.pow_left (D.factorization q) hqcop
    have hprod : (∏ q ∈ s, q ^ D.factorization q).Coprime p := by
      exact Nat.Coprime.prod_left (t := s) (fun q hq => hcop q hq)
    have hg1 : p.gcd (∏ q ∈ s, q ^ D.factorization q) = 1 := by
      rw [Nat.gcd_comm]
      exact hprod.gcd_eq_one
    have hg2 : p.gcd (∏ q ∈ s, q ^ D.factorization q) = p := Nat.gcd_eq_left_iff_dvd.mpr hdiv
    have hp1 : p = 1 := by
      rw [hg2] at hg1
      exact hg1
    exact (Nat.Prime.ne_one hpp) hp1
  exact ⟨hlt, hpD⟩

/-- Support of the large part: the prime factors of `discLargePart n D` are
exactly the primes `> n` dividing `D` (both inclusions). -/
theorem primeFactors_discLargePart {n D : ℕ} (hD : D ≠ 0) :
    (discLargePart n D).primeFactors = (Nat.primeFactors D).filter (fun p => n < p) := by
  classical
  apply Finset.Subset.antisymm
  · intro p hp
    have hlt : n < p ∧ p ∣ D := mem_primeFactors_discLargePart hD hp
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    exact Finset.mem_filter.mpr ⟨(Nat.mem_primeFactors.mpr ⟨hpp, hlt.2, hD⟩), hlt.1⟩
  · intro p hp
    rcases (Finset.mem_filter.mp hp) with ⟨hpf, hpn⟩
    rcases (Nat.mem_primeFactors.mp hpf) with ⟨hpp, hpD, hz⟩
    have hps : p ∈ (Nat.primeFactors D).filter (fun q => n < q) :=
      Finset.mem_filter.mpr ⟨hpf, hpn⟩
    have hpdvd : p ^ D.factorization p ∣
        ∏ q ∈ (Nat.primeFactors D).filter (fun q => n < q), q ^ D.factorization q := by
      exact Finset.dvd_prod_of_mem (fun q => q ^ D.factorization q) hps
    have he : 1 ≤ D.factorization p :=
      Nat.Prime.factorization_pos_of_dvd hpp hz hpD
    have hp1 : p ∣ p ^ D.factorization p := by
      simpa using (pow_dvd_pow p he)
    have hpdiv : p ∣ discLargePart n D := by
      simpa [discLargePart] using (dvd_trans hp1 hpdvd)
    have hD0 : discLargePart n D ≠ 0 := by
      exact Nat.ne_of_gt (Nat.pos_of_dvd_of_pos (discLargePart_dvd n D hD) (Nat.pos_of_ne_zero hD))
    exact (Nat.mem_primeFactors.mpr ⟨hpp, hpdiv, hD0⟩)

/-- The exponent of `p` in the large part equals its exponent in `D`, for
`p` a prime factor of the large part (the large part carries the full
`v_p(D)` of every `p | D` with `p > n`). -/
theorem factorization_discLargePart {n D : ℕ} (hD : D ≠ 0) {p : ℕ}
    (hp : p ∈ (discLargePart n D).primeFactors) :
    D.factorization p = (discLargePart n D).factorization p := by
  classical
  let s := (Nat.primeFactors D).filter (fun q => n < q)
  rw [primeFactors_discLargePart hD] at hp
  have hpf' : p ∈ s := by
    dsimp [s]
    exact hp
  have hpf : p ∈ Nat.primeFactors D := (Finset.mem_filter.mp hpf').1
  have hpn : n < p := (Finset.mem_filter.mp hpf').2
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpf
  have hpD : p ∣ D := (Nat.mem_primeFactors.mp hpf).2.1
  have hz : D ≠ 0 := (Nat.mem_primeFactors.mp hpf).2.2
  haveI : Fact (Nat.Prime p) := ⟨hpp⟩
  have hDstar : discLargePart n D ≠ 0 := by
    exact Nat.ne_of_gt (Nat.pos_of_dvd_of_pos (discLargePart_dvd n D hD) (Nat.pos_of_ne_zero hD))
  rw [Nat.factorization_def D hpp, Nat.factorization_def (discLargePart n D) hpp]
  have hsum : padicValNat p (discLargePart n D) =
      ∑ q ∈ s, (D.factorization q) * padicValNat p q := by
    calc
      padicValNat p (discLargePart n D)
          = padicValNat p (∏ q ∈ s, q ^ D.factorization q) := by
            simp [discLargePart, s]
      _ = ∑ q ∈ s, padicValNat p (q ^ D.factorization q) := by
            exact Commons.NumberTheory.NumberField.padicValNat_prod p s (fun q => q ^ D.factorization q)
              (fun q hq => pow_ne_zero _ (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors
                (Finset.mem_filter.mp (by simpa [s] using hq)).1)))
      _ = ∑ q ∈ s, (D.factorization q) * padicValNat p q := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [padicValNat.pow]
  have hterm (q : ℕ) (hq : q ∈ s) :
      (D.factorization q) * padicValNat p q =
        if q = p then D.factorization q else 0 := by
    by_cases hqp : q = p
    · subst q
      simp [padicValNat_self]
    · have hqpp : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (by simpa [s] using hq)).1
      have hnd : ¬ p ∣ q := by
        intro hdiv
        exact hqp ((Nat.Prime.dvd_iff_eq hqpp (ne_of_gt (Nat.Prime.one_lt hpp))).mp hdiv)
      have hv0 : padicValNat p q = 0 := padicValNat.eq_zero_of_not_dvd hnd
      simp [hv0, hqp]
  have hsum' : (∑ q ∈ s, (D.factorization q) * padicValNat p q) =
      (∑ q ∈ s, if q = p then D.factorization q else 0) := by
    apply Finset.sum_congr rfl
    intro q hq
    exact hterm q hq
  have hsingle : (∑ q ∈ s, if q = p then D.factorization q else 0) =
      (if p = p then D.factorization p else 0 : ℕ) := by
    exact Finset.sum_eq_single (s := s) (f := fun q => if q = p then D.factorization q else 0)
      p (by intro q hq hqp; simp [hqp]) (by intro hn; exact False.elim (hn hpf'))
  calc
    padicValNat p D = D.factorization p := (Nat.factorization_def D hpp).symm
    _ = ∑ q ∈ s, if q = p then D.factorization q else 0 := by
          rw [hsingle]
          simp
    _ = ∑ q ∈ s, (D.factorization q) * padicValNat p q := hsum'.symm
    _ = padicValNat p (discLargePart n D) := hsum.symm

end Submission.Vdw

import Mathlib

/-!
# A finite nilpotent group is the product of its Sylow subgroups (cardinality form)

The assembly of DS10a applies its per-case lemmas to the Sylow `r`-subgroups of
`N = F_{2'}(C)`: in a nilpotent group those are normal and their (coprime) orders multiply to
`|N|`, so containment of every Sylow subgroup in a subgroup `L` forces `N ≤ L`.
-/

namespace Work.DSTR.M110

open Subgroup

/-- If `a` and `b` are coprime and both divide `n`, then `a * b` divides `n`. -/
private lemma coprime_mul_dvd {a b n : ℕ} (hab : Nat.Coprime a b) (ha : a ∣ n) (hb : b ∣ n) :
    a * b ∣ n := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, ht⟩ := hab.symm.dvd_of_dvd_mul_left hb
  exact ⟨t, by rw [ht]; ring⟩

/-- A product of pairwise coprime divisors of `n` divides `n`. -/
private lemma prod_dvd_of_pairwise_coprime {ι : Type*} (t : Finset ι) (s : ι → ℕ) {n : ℕ}
    (hcop : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Nat.Coprime (s i) (s j))
    (hdvd : ∀ i ∈ t, s i ∣ n) : ∏ i ∈ t, s i ∣ n := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha]
    have h1 : s a ∣ n := hdvd a (Finset.mem_insert_self a t)
    have h2 : ∏ i ∈ t, s i ∣ n :=
      ih (fun i hi j hj hij => hcop i (Finset.mem_insert_of_mem hi) j
            (Finset.mem_insert_of_mem hj) hij)
        (fun i hi => hdvd i (Finset.mem_insert_of_mem hi))
    have h3 : Nat.Coprime (s a) (∏ i ∈ t, s i) := by
      rw [Nat.coprime_prod_right_iff]
      intro i hi
      exact hcop a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    exact coprime_mul_dvd h3 h1 h2

/-- In a finite nilpotent group, `|N| = ∏_p |Sylow_p(N)|`. -/
theorem card_eq_prod_card_sylow (N : Type*) [Group N] [Finite N] [Group.IsNilpotent N] :
    Nat.card N = ∏ p ∈ (Nat.card N).primeFactors, Nat.card ↥(default : Sylow p N) := by
  classical
  haveI : Nonempty N := ⟨1⟩
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization (Nat.card_pos.ne')]
  exact Finset.prod_congr rfl fun p hp => by
    haveI : Fact (Nat.Prime p) := ⟨Nat.prime_of_mem_primeFactors hp⟩
    exact (Sylow.card_eq_multiplicity (default : Sylow p N)).symm

/-- The Sylow subgroups of a finite nilpotent group have coprime orders. -/
theorem coprime_card_sylow (N : Type*) [Group N] [Finite N] [Group.IsNilpotent N]
    {p q : ℕ} (hp : p ∈ (Nat.card N).primeFactors) (hq : q ∈ (Nat.card N).primeFactors)
    (hpq : p ≠ q) :
    Nat.Coprime (Nat.card ↥(default : Sylow p N)) (Nat.card ↥(default : Sylow q N)) := by
  classical
  have hpn : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hqn : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
  haveI : Fact (Nat.Prime p) := ⟨hpn⟩
  haveI : Fact (Nat.Prime q) := ⟨hqn⟩
  have hpa : Nat.card ↥(default : Sylow p N) = p ^ (Nat.card N).factorization p :=
    Sylow.card_eq_multiplicity (default : Sylow p N)
  have hqa : Nat.card ↥(default : Sylow q N) = q ^ (Nat.card N).factorization q :=
    Sylow.card_eq_multiplicity (default : Sylow q N)
  rw [hpa, hqa]
  have hcp : Nat.Coprime p q := by
    rw [hpn.coprime_iff_not_dvd]
    intro h
    rcases (Nat.dvd_prime hqn).mp h with h1 | h1
    · exact hpn.ne_one h1
    · exact hpq h1
  have h1 : 0 < (Nat.card N).factorization p :=
    hpn.factorization_pos_of_dvd (Nat.card_pos.ne') (Nat.mem_primeFactors.mp hp).2.1
  have h2 : 0 < (Nat.card N).factorization q :=
    hqn.factorization_pos_of_dvd (Nat.card_pos.ne') (Nat.mem_primeFactors.mp hq).2.1
  exact (Nat.coprime_pow_right_iff h2 (p ^ (Nat.card N).factorization p) q).mpr
    ((Nat.coprime_pow_left_iff h1 p q).mpr hcp)

/-- **If every Sylow subgroup of a finite nilpotent group `N` lies in `L ≤ N`, then `L = ⊤`.** -/
theorem eq_top_of_sylow_le {N : Type*} [Group N] [Finite N] [Group.IsNilpotent N]
    {L : Subgroup N} (hL : ∀ (r : ℕ) [Fact r.Prime] (P : Sylow r N), (P : Subgroup N) ≤ L) :
    L = ⊤ := by
  classical
  haveI : Nonempty N := ⟨1⟩
  -- each Sylow subgroup lies in `L`, so its order divides `|L|`
  have hdvd : ∀ p ∈ (Nat.card N).primeFactors, Nat.card ↥(default : Sylow p N) ∣ Nat.card L :=
    fun p hp => by
      haveI : Fact (Nat.Prime p) := ⟨Nat.prime_of_mem_primeFactors hp⟩
      exact Subgroup.card_dvd_of_le (hL p (default : Sylow p N))
  -- hence the whole product of the (pairwise coprime) Sylow orders divides `|L|`
  have hprod : ∏ p ∈ (Nat.card N).primeFactors, Nat.card ↥(default : Sylow p N) ∣ Nat.card L :=
    prod_dvd_of_pairwise_coprime _ _
      (fun p hp q hq hpq => coprime_card_sylow N hp hq hpq) hdvd
  have hcardN : Nat.card N ∣ Nat.card L := by
    rw [card_eq_prod_card_sylow N]; exact hprod
  have hcardL : Nat.card L ∣ Nat.card N := by
    have h := Subgroup.card_dvd_of_le (H := L) (K := ⊤) le_top
    simpa [Subgroup.card_top] using h
  exact Subgroup.eq_top_of_card_eq L (Nat.dvd_antisymm hcardL hcardN)

end Work.DSTR.M110

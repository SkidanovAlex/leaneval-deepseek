import Mathlib
import Submission.Work.A7REC.Char.a7Excl120Common
import Submission.Work.A7REC.Char.a7Excl120Tools

set_option linter.style.haveILetI false

namespace Work.A7REC.Char

open Subgroup

theorem a7Excl120IdxFour {C : Type*} [Group C] [Finite C] {U S : Subgroup C} {τ : C}
    (h : Excl120Setup U S τ)
    (hi : (Subgroup.normalizer (U : Set C)).index = 4) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set N := Subgroup.normalizer (U : Set C) with hNdef
  set K := Subgroup.centralizer (U : Set C) with hKdef
  have hNcard : Nat.card ↥N = 30 := by
    have hmul := Subgroup.card_mul_index N
    rw [hi, h.card_eq] at hmul
    omega
  have hKN : K ≤ N := Subgroup.centralizer_le_normalizer _
  have hKdvd : Nat.card ↥K ∣ 30 := by
    rw [← hNcard]; exact Subgroup.card_dvd_of_le hKN
  have hK5 : 5 ∣ Nat.card ↥K := by
    have hbound := card_normalizer_le_card_centralizer_mul (A := U) h.card_U
    have hKge : 15 ≤ Nat.card ↥K := by
      rw [← hNdef, ← hKdef] at hbound
      rw [hNcard] at hbound
      norm_num at hbound
      omega
    have hmem : Nat.card ↥K ∈ (30 : ℕ).divisors := Nat.mem_divisors.mpr ⟨hKdvd, by norm_num⟩
    have hlist : (30 : ℕ).divisors.filter (fun k => 15 ≤ k) = {15, 30} := by decide
    have hmem' : Nat.card ↥K ∈ (30 : ℕ).divisors.filter (fun k => 15 ≤ k) :=
      Finset.mem_filter.mpr ⟨hmem, hKge⟩
    rw [hlist] at hmem'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
    rcases hmem' with h' | h' <;> rw [h'] <;> norm_num
  obtain ⟨x5, hx5⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 5 hK5
  set p : C := (x5 : C) with hpdef
  have hp5 : orderOf p = 5 := by rw [hpdef, Subgroup.orderOf_coe x5]; exact hx5
  set P : Subgroup C := Subgroup.zpowers p with hPdef
  have hPcard : Nat.card ↥P = 5 := by rw [hPdef, Nat.card_zpowers, hp5]
  have hpK : p ∈ K := by rw [hpdef]; exact x5.2
  have hpK' : ∀ u ∈ U, u * p = p * u := by
    intro u hu
    exact Subgroup.mem_centralizer_iff.mp (by rw [← hKdef]; exact hpK) u hu
  have hUP : U ≤ Subgroup.centralizer (P : Set C) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hn]
    exact ((Commute.symm (hpK' u hu)).zpow_left n)
  have hPle : P ≤ Subgroup.centralizer (P : Set C) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← hm, ← hn]
    exact (Commute.refl p).zpow_zpow n m
  have h3 : 3 ∣ Nat.card ↥(Subgroup.centralizer (P : Set C)) := by
    have h' := Subgroup.card_dvd_of_le hUP
    rwa [h.card_U] at h'
  have h5 : 5 ∣ Nat.card ↥(Subgroup.centralizer (P : Set C)) := by
    have h' := Subgroup.card_dvd_of_le hPle
    rwa [hPcard] at h'
  have h15 : 15 ∣ Nat.card ↥(Subgroup.centralizer (P : Set C)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) h3 h5
  have hN5 : Nat.card ↥(Subgroup.normalizer (P : Set C)) = 20 ∨
      Nat.card ↥(Subgroup.normalizer (P : Set C)) = 120 := by
    have hfac : (Nat.card C).factorization 5 = 1 := by
      rw [h.card_eq]
      rw [show (120 : ℕ) = 5 * 24 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num)]
      simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 5),
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (5 : ℕ) ∣ 24)]
    let Q : Sylow 5 C := Sylow.ofCard P (by rw [hfac, pow_one]; exact hPcard)
    have hQ : (Q : Subgroup C) = P := Sylow.coe_ofCard P _
    have hn5 : Nat.card (Sylow 5 C) = (Subgroup.normalizer (P : Set C)).index := by
      rw [← hQ]; exact Sylow.card_eq_index_normalizer Q
    have hdvd : Nat.card (Sylow 5 C) ∣ 120 := by
      rw [hn5, ← h.card_eq]; exact Subgroup.index_dvd_card _
    have hmod : Nat.card (Sylow 5 C) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 C
    have hcase : Nat.card (Sylow 5 C) = 1 ∨ Nat.card (Sylow 5 C) = 6 := by
      have hm : Nat.card (Sylow 5 C) % 5 = 1 := by simpa [Nat.ModEq] using hmod
      have hmem : Nat.card (Sylow 5 C) ∈ (120 : ℕ).divisors :=
        Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hlist : (120 : ℕ).divisors.filter (fun k => k % 5 = 1) = {1, 6} := by decide
      have hmem' : Nat.card (Sylow 5 C) ∈ (120 : ℕ).divisors.filter (fun k => k % 5 = 1) :=
        Finset.mem_filter.mpr ⟨hmem, hm⟩
      rw [hlist] at hmem'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
      tauto
    have hmul := Subgroup.card_mul_index (Subgroup.normalizer (P : Set C))
    rw [← hn5, h.card_eq] at hmul
    rcases hcase with h1 | h6
    · right; rw [h1, mul_one] at hmul; exact hmul
    · left; rw [h6] at hmul; omega
  have hPbound := card_normalizer_le_card_centralizer_mul (A := P) hPcard
  have h30 : 30 ≤ Nat.card ↥(Subgroup.centralizer (P : Set C)) := by
    rcases hN5 with h20 | h120
    · exfalso
      have hdvd : Nat.card ↥(Subgroup.centralizer (P : Set C)) ∣ 20 := by
        rw [← h20]
        exact Subgroup.card_dvd_of_le (Subgroup.centralizer_le_normalizer (P : Set C))
      have h' : 15 ∣ 20 := h15.trans hdvd
      norm_num at h'
    · rw [h120] at hPbound; omega
  have hCdvd : Nat.card ↥(Subgroup.centralizer (P : Set C)) ∣ 120 := by
    have h1 : Nat.card ↥(Subgroup.centralizer (P : Set C)) ∣
        Nat.card ↥(Subgroup.normalizer (P : Set C)) :=
      Subgroup.card_dvd_of_le (Subgroup.centralizer_le_normalizer (P : Set C))
    have hmul := Subgroup.card_mul_index (Subgroup.normalizer (P : Set C))
    rw [h.card_eq] at hmul
    exact h1.trans ⟨_, hmul.symm⟩
  have heven : 2 ∣ Nat.card ↥(Subgroup.centralizer (P : Set C)) := by
    have hmem : Nat.card ↥(Subgroup.centralizer (P : Set C)) ∈ (120 : ℕ).divisors :=
      Nat.mem_divisors.mpr ⟨hCdvd, by norm_num⟩
    have hlist : (120 : ℕ).divisors.filter (fun k => 30 ≤ k ∧ 15 ∣ k) = {30, 60, 120} := by decide
    have hmem' : Nat.card ↥(Subgroup.centralizer (P : Set C)) ∈
        (120 : ℕ).divisors.filter (fun k => 30 ≤ k ∧ 15 ∣ k) :=
      Finset.mem_filter.mpr ⟨hmem, h30, h15⟩
    rw [hlist] at hmem'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
    rcases hmem' with h' | h' | h' <;> rw [h'] <;> norm_num
  obtain ⟨x2, hx2⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer (P : Set C))) 2 heven
  set x : C := (x2 : C) with hxdef
  have hxord : orderOf x = 2 := by rw [hxdef, Subgroup.orderOf_coe x2]; exact hx2
  have hPx : P ≤ Subgroup.centralizer ({x} : Set C) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact (Subgroup.mem_centralizer_iff.mp x2.2) y hy |>.symm
  have h5c : 5 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set C)) := by
    have h' := Subgroup.card_dvd_of_le hPx
    rwa [hPcard] at h'
  have hdvd24 : Nat.card ↥(Subgroup.centralizer ({x} : Set C)) ∣ 24 := h.cent_dvd x hxord
  have hfin : 5 ∣ 24 := h5c.trans hdvd24
  norm_num at hfin


end Work.A7REC.Char

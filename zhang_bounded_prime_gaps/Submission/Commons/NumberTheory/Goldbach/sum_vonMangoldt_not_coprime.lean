import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit

namespace Commons.NumberTheory.Goldbach

open Finset

/-- If `n` and `q` are not coprime, some prime divides both. -/
private lemma exists_prime_dvd_of_not_coprime {n q : ℕ} (h : ¬ Nat.Coprime n q) :
    ∃ p, p.Prime ∧ p ∣ n ∧ p ∣ q := by
  have hg : Nat.gcd n q ≠ 1 := h
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hg
  exact ⟨p, hp, (Nat.dvd_gcd_iff.mp hpdvd).1, (Nat.dvd_gcd_iff.mp hpdvd).2⟩

theorem sum_vonMangoldt_not_coprime (q M : ℕ) :
    ∑ n ∈ (Finset.Icc 1 M).filter (fun n => ¬ Nat.Coprime n q),
        ArithmeticFunction.vonMangoldt n
      = ∑ p ∈ (Finset.Icc 1 M).filter (fun p => p.Prime ∧ p ∣ q),
          ((Nat.log p M : ℕ) : ℝ) * Real.log p := by
  classical
  let P : Finset ℕ := (Finset.Icc 1 M).filter (fun p => p.Prime ∧ p ∣ q)
  let S : Finset ℕ := (Finset.Icc 1 M).filter (fun n => ¬ Nat.Coprime n q)
  let K : ℕ → Finset ℕ := fun p => Finset.Icc 1 (Nat.log p M)
  let Im : ℕ → Finset ℕ := fun p => (K p).image (fun k => p ^ k)
  let U : Finset ℕ := P.biUnion Im
  have hUsub : U ⊆ S := by
    intro n hn
    dsimp only [U, Im, K, P, S] at hn ⊢
    rw [Finset.mem_biUnion] at hn
    obtain ⟨p, hp, hn⟩ := hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hpM⟩, hpprime, hpdvd⟩ := hp
    rw [Finset.mem_image] at hn
    obtain ⟨k, hk, rfl⟩ := hn
    rw [Finset.mem_Icc] at hk
    obtain ⟨hk1, hklog⟩ := hk
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hMpos : M ≠ 0 := by omega
    have hpowle : p ^ k ≤ M := (Nat.le_log_iff_pow_le hpprime.one_lt hMpos).mp hklog
    refine ⟨⟨Nat.one_le_pow k p hpprime.pos, hpowle⟩, ?_⟩
    intro hc
    have hpgcd : p ∣ Nat.gcd (p ^ k) q := Nat.dvd_gcd (dvd_pow_self p (by omega)) hpdvd
    have hpos : 0 < Nat.gcd (p ^ k) q := Nat.gcd_pos_of_pos_left q (pow_pos hpprime.pos k)
    have hle : p ≤ Nat.gcd (p ^ k) q := Nat.le_of_dvd hpos hpgcd
    have : Nat.gcd (p ^ k) q = 1 := hc
    have hp2 : 2 ≤ p := hpprime.two_le
    omega
  have hvan : ∀ n ∈ S, n ∉ U → ArithmeticFunction.vonMangoldt n = 0 := by
    intro n hn hnU
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
    intro hpw
    dsimp only [S] at hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnM⟩, hncop⟩ := hn
    obtain ⟨p, k, hpprime, hkpos, hpk⟩ := (isPrimePow_nat_iff n).mp hpw
    obtain ⟨r, hrprime, hrn, hrq⟩ := exists_prime_dvd_of_not_coprime hncop
    have hrpk : r ∣ p ^ k := by rw [hpk]; exact hrn
    have hrp : r = p :=
      (Nat.prime_dvd_prime_iff_eq hrprime hpprime).mp (hrprime.dvd_of_dvd_pow hrpk)
    have hpdvdq : p ∣ q := hrp ▸ hrq
    have hpM : p ≤ M := by
      have hle : p ≤ p ^ k := Nat.le_self_pow hkpos.ne' p
      rw [hpk] at hle
      exact hle.trans hnM
    have hpP : p ∈ P := by
      dsimp only [P]
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hpprime.one_le, hpM⟩, hpprime, hpdvdq⟩
    have hklog : k ≤ Nat.log p M :=
      Nat.le_log_of_pow_le hpprime.one_lt (by rw [hpk]; exact hnM)
    have : n ∈ U := by
      dsimp only [U, Im, K]
      rw [Finset.mem_biUnion]
      refine ⟨p, hpP, ?_⟩
      rw [Finset.mem_image]
      exact ⟨k, by rw [Finset.mem_Icc]; exact ⟨hkpos, hklog⟩, hpk⟩
    exact hnU this
  have hdisj : (↑P : Set ℕ).PairwiseDisjoint Im := by
    intro p hp q hq hpq
    refine Finset.disjoint_left.mpr ?_
    intro n hnp hnq
    change p ∈ P at hp
    change q ∈ P at hq
    rw [Finset.mem_filter] at hp hq
    have hpprime : p.Prime := hp.2.1
    have hqprime : q.Prime := hq.2.1
    dsimp only [Im, K] at hnp hnq
    rw [Finset.mem_image] at hnp
    rw [Finset.mem_image] at hnq
    obtain ⟨k, hk, hk'⟩ := hnp
    obtain ⟨l, hl, hl'⟩ := hnq
    have hkpos : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
    have hlpos : l ≠ 0 := by have := (Finset.mem_Icc.mp hl).1; omega
    have heq : p ^ k = q ^ l := by rw [hk', hl']
    exact hpq (Nat.Prime.pow_inj' hpprime hqprime hkpos hlpos heq).1
  show ∑ n ∈ S, ArithmeticFunction.vonMangoldt n
      = ∑ p ∈ P, ((Nat.log p M : ℕ) : ℝ) * Real.log p
  calc
    ∑ n ∈ S, ArithmeticFunction.vonMangoldt n
        = ∑ n ∈ U, ArithmeticFunction.vonMangoldt n := (Finset.sum_subset hUsub hvan).symm
    _ = ∑ p ∈ P, ∑ n ∈ Im p, ArithmeticFunction.vonMangoldt n := by
          dsimp only [U]
          exact Finset.sum_biUnion hdisj
    _ = ∑ p ∈ P, ∑ k ∈ K p, ArithmeticFunction.vonMangoldt (p ^ k) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          dsimp only [P] at hp
          rw [Finset.mem_filter] at hp
          have hpprime : p.Prime := hp.2.1
          dsimp only [Im]
          rw [Finset.sum_image (g := fun k => p ^ k)
                (fun a _ b _ hab => Nat.pow_right_injective hpprime.two_le hab)]
    _ = ∑ p ∈ P, ∑ k ∈ K p, Real.log (p : ℝ) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          dsimp only [P] at hp
          rw [Finset.mem_filter] at hp
          have hpprime : p.Prime := hp.2.1
          refine Finset.sum_congr rfl fun k hk => ?_
          dsimp only [K] at hk
          have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
          rw [ArithmeticFunction.vonMangoldt_apply_pow hk0,
              ArithmeticFunction.vonMangoldt_apply_prime hpprime]
    _ = ∑ p ∈ P, ((Nat.log p M : ℕ) : ℝ) * Real.log p := by
          refine Finset.sum_congr rfl fun p _ => ?_
          dsimp only [K]
          rw [Finset.sum_const, Nat.card_Icc]
          simp

end Commons.NumberTheory.Goldbach
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_bound_of_squarefree
import Submission.Commons.NumberTheory.Divisors.card_divisors_prod_prime_pow
import Submission.Commons.NumberTheory.Divisors.primeFactors_prod_prime_pow

open Finset
open scoped BigOperators
open Commons.NumberTheory.Divisors

namespace Commons.NumberTheory.DivisorSum

private lemma succ_le_div_add_one_pow_five (a : ℕ) (ha : 3 ≤ a) :
    a + 1 ≤ (a / 3 + 1) ^ 5 := by
  have h1 : a + 1 ≤ 3 * (a / 3 + 1) := by omega
  have h2 : 3 * (a / 3 + 1) ≤ (a / 3 + 1) ^ 5 := by
    have h3 : 3 ≤ (a / 3 + 1) ^ 4 :=
      le_trans (by norm_num) (Nat.pow_le_pow_left (by omega : 2 ≤ a / 3 + 1) 4)
    calc 3 * (a / 3 + 1) ≤ (a / 3 + 1) ^ 4 * (a / 3 + 1) := Nat.mul_le_mul_right _ h3
      _ = (a / 3 + 1) ^ 5 := (pow_succ _ 4).symm
  exact le_trans h1 h2

private lemma three_pow_le_five (k : ℕ) : 3 ^ k ≤ 2 ^ (5 * (k / 3) + 5) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ k = 3 * q + r :=
    ⟨k / 3, k % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 3).symm⟩
  have hqr : (3 * q + r) / 3 = q := by omega
  rw [hqr]
  have hA : 3 ^ r ≤ 32 := by
    calc 3 ^ r ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 9 := by norm_num
      _ ≤ 32 := by norm_num
  have hB : 27 ^ q ≤ 32 ^ q := Nat.pow_le_pow_left (by norm_num) _
  calc 3 ^ (3 * q + r) = 3 ^ (3 * q) * 3 ^ r := by rw [pow_add]
    _ = 27 ^ q * 3 ^ r := by rw [pow_mul]; norm_num
    _ ≤ 32 ^ q * 32 := Nat.mul_le_mul hB hA
    _ = 2 ^ (5 * q) * 2 ^ 5 := by
          rw [show (32:ℕ) = 2 ^ 5 by norm_num, ← pow_mul]
    _ = 2 ^ (5 * q + 5) := by rw [pow_add]

/-- For every `n ≥ 1` there is a divisor `d` with `d³ ≤ n` and `τ(n) ≤ (2 τ(d))⁵`. -/
theorem exists_divisor_cube_le_pow_five (n : ℕ) (hn : 1 ≤ n) :
    ∃ d : ℕ, d ∣ n ∧ d ^ 3 ≤ n ∧ (Nat.divisors n).card ≤ (2 * (Nat.divisors d).card) ^ 5 := by
  classical
  have hn0 : n ≠ 0 := by omega
  set P : Finset ℕ := n.primeFactors with hP
  set Pl : Finset ℕ := P.filter (fun p => 3 ≤ n.factorization p) with hPl
  set Ps : Finset ℕ := P.filter (fun p => ¬ (3 ≤ n.factorization p)) with hPs
  have hPmem : ∀ p, p ∈ P ↔ p.Prime ∧ p ∣ n ∧ n ≠ 0 := by
    intro p; rw [hP]; exact Nat.mem_primeFactors
  have hPfac : ∀ p ∈ P, 1 ≤ n.factorization p := by
    intro p hp
    obtain ⟨hp1, hp2, _⟩ := (hPmem p).mp hp
    exact hp1.factorization_pos_of_dvd hn0 hp2
  have hPl_sub : Pl ⊆ P := by rw [hPl]; exact Finset.filter_subset _ _
  have hPs_sub : Ps ⊆ P := by rw [hPs]; exact Finset.filter_subset _ _
  have hPlfac : ∀ p ∈ Pl, 3 ≤ n.factorization p := by
    intro p hp; rw [hPl] at hp; exact (Finset.mem_filter.mp hp).2
  have hPsfac : ∀ p ∈ Ps, n.factorization p ≤ 2 := by
    intro p hp
    rw [hPs] at hp
    have h1 : ¬ (3 ≤ n.factorization p) := (Finset.mem_filter.mp hp).2
    have h2 : 1 ≤ n.factorization p := hPfac p (Finset.mem_filter.mp hp).1
    omega
  have hPlprime : ∀ p ∈ Pl, p.Prime := fun p hp => ((hPmem p).mp (hPl_sub hp)).1
  have hPsprime : ∀ p ∈ Ps, p.Prime := fun p hp => ((hPmem p).mp (hPs_sub hp)).1
  have hdisjPlPs : Disjoint Pl Ps := by
    rw [hPl, hPs]
    exact Finset.disjoint_filter_filter_not P P (fun p => 3 ≤ n.factorization p)
  have hnprod : (∏ p ∈ P, p ^ (n.factorization p)) = n := by
    have h := Nat.prod_factorization_pow_eq_self hn0
    rw [hP, ← Nat.support_factorization]
    exact h
  have hsplit_prod : (∏ p ∈ P, p ^ (n.factorization p))
      = (∏ p ∈ Pl, p ^ (n.factorization p)) * (∏ p ∈ Ps, p ^ (n.factorization p)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not P (fun p => 3 ≤ n.factorization p)
        (fun p => p ^ (n.factorization p)), ← hPl, ← hPs]
  have hnsplit : (∏ p ∈ Pl, p ^ (n.factorization p)) * (∏ p ∈ Ps, p ^ (n.factorization p)) = n := by
    rw [← hsplit_prod]; exact hnprod
  have hNl_dvd : (∏ p ∈ Pl, p ^ (n.factorization p)) ∣ n :=
    ⟨∏ p ∈ Ps, p ^ (n.factorization p), hnsplit.symm⟩
  have hNs_dvd : (∏ p ∈ Ps, p ^ (n.factorization p)) ∣ n :=
    ⟨∏ p ∈ Pl, p ^ (n.factorization p), by rw [mul_comm]; exact hnsplit.symm⟩
  -- g
  set g : ℕ := ∏ p ∈ Pl, p ^ (n.factorization p / 3) with hg
  have hg_e : ∀ p ∈ Pl, 1 ≤ n.factorization p / 3 := by
    intro p hp; have := hPlfac p hp; omega
  have htau_g : (Nat.divisors g).card = ∏ p ∈ Pl, (n.factorization p / 3 + 1) := by
    rw [hg]; exact card_divisors_prod_prime_pow Pl (fun p => n.factorization p / 3) hPlprime hg_e
  have hg_pf : g.primeFactors = Pl := by
    rw [hg]; exact primeFactors_prod_prime_pow Pl (fun p => n.factorization p / 3) hPlprime hg_e
  have hg_ne : g ≠ 0 := by
    rw [hg]
    exact (Finset.prod_pos (fun p hp => pow_pos (hPlprime p hp).pos _)).ne'
  -- f
  set L : List ℕ := Ps.sort (· ≤ ·) with hL
  set s : ℕ := L.length / 3 with hs
  set f : ℕ := (L.take s).prod with hf
  set T : Finset ℕ := (L.take s).toFinset with hT
  have hLnodup : L.Nodup := by rw [hL]; exact Finset.sort_nodup Ps (· ≤ ·)
  have hLsorted : L.SortedLE := by rw [hL]; exact (Finset.sortedLT_sort Ps).sortedLE
  have hLtofinset : L.toFinset = Ps := by rw [hL]; exact Finset.sort_toFinset Ps (· ≤ ·)
  have hLlength : L.length = Ps.card := by rw [hL]; exact Finset.length_sort (s := Ps) (· ≤ ·)
  have hLprod : L.prod = ∏ p ∈ Ps, p := by
    have h := List.prod_toFinset (id : ℕ → ℕ) hLnodup
    simp only [List.map_id] at h
    rw [hLtofinset] at h
    exact h.symm
  have hs_eq : s = Ps.card / 3 := by rw [hs, hLlength]
  have hs_le : s ≤ L.length := by rw [hs]; exact Nat.div_le_self _ _
  have htake_nodup : (L.take s).Nodup := (List.take_sublist s L).nodup hLnodup
  have hT_sub : T ⊆ Ps := by
    intro p hp
    rw [hT, List.mem_toFinset] at hp
    rw [← hLtofinset, List.mem_toFinset]
    exact List.take_subset s L hp
  have hTcard : T.card = s := by
    rw [hT, List.toFinset_card_of_nodup htake_nodup, List.length_take, Nat.min_eq_left hs_le]
  have hf_eq : f = ∏ p ∈ T, p := by
    have h := List.prod_toFinset (id : ℕ → ℕ) htake_nodup
    simp only [List.map_id] at h
    rw [hf, hT]
    exact h.symm
  have hf_ne : f ≠ 0 := by
    rw [hf_eq]
    exact (Finset.prod_pos (fun p hp => (hPsprime p (hT_sub hp)).pos)).ne'
  have hf_pf : f.primeFactors = T := by
    rw [hf_eq]
    simpa only [pow_one] using primeFactors_prod_prime_pow T (fun _ => 1)
      (fun p hp => hPsprime p (hT_sub hp)) (fun p hp => le_refl 1)
  have htau_f : (Nat.divisors f).card = 2 ^ s := by
    have h := card_divisors_prod_prime_pow T (fun _ => 1) (fun p hp => hPsprime p (hT_sub hp))
      (fun p hp => le_refl 1)
    simp only [pow_one] at h
    rw [← hf_eq] at h
    rw [h, Finset.prod_const, hTcard]
  -- coprimality
  have hcop : Nat.Coprime g f := by
    rw [← Nat.disjoint_primeFactors hg_ne hf_ne, hg_pf, hf_pf]
    exact hdisjPlPs.mono_right hT_sub
  -- divisibility
  have hg_dvd : g ∣ n := by
    have h1 : g ∣ ∏ p ∈ Pl, p ^ (n.factorization p) := by
      rw [hg]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun p hp => pow_dvd_pow p (Nat.div_le_self _ _))
    exact dvd_trans h1 hNl_dvd
  have hf_dvd : f ∣ n := by
    have h1 : f ∣ ∏ p ∈ Ps, p := by
      rw [hf_eq]
      refine ⟨∏ x ∈ Ps \ T, x, ?_⟩
      rw [mul_comm]
      exact (Finset.prod_sdiff hT_sub).symm
    have h2 : (∏ p ∈ Ps, p) ∣ ∏ p ∈ Ps, p ^ (n.factorization p) :=
      Finset.prod_dvd_prod_of_dvd _ _ (fun p hp => by
        calc p = p ^ 1 := (pow_one p).symm
          _ ∣ p ^ (n.factorization p) := pow_dvd_pow p (hPfac p (hPs_sub hp)))
    exact dvd_trans (dvd_trans h1 h2) hNs_dvd
  have hd_dvd : (g * f) ∣ n := hcop.mul_dvd_of_dvd_of_dvd hg_dvd hf_dvd
  -- power bound
  have hg3 : g ^ 3 ≤ ∏ p ∈ Pl, p ^ (n.factorization p) := by
    rw [hg, ← Finset.prod_pow]
    exact Finset.prod_le_prod₀ (fun p hp => Nat.zero_le _) (fun p hp => by
      calc (p ^ (n.factorization p / 3)) ^ 3 = p ^ (3 * (n.factorization p / 3)) := by
            rw [← pow_mul]; congr 1; omega
        _ ≤ p ^ (n.factorization p) :=
            Nat.pow_le_pow_right (hPlprime p hp).pos (Nat.mul_div_le _ _))
  have hf3_le_prod : f ^ 3 ≤ ∏ p ∈ Ps, p := by
    have hpos : 0 < L.prod := by
      rw [hLprod]; exact Finset.prod_pos (fun p hp => (hPsprime p hp).pos)
    calc f ^ 3 = (L.take s).prod ^ 3 := by rw [hf]
      _ ≤ (L.take (3 * s)).prod :=
          Commons.NumberTheory.FriedlanderIwaniec.take_prod_pow_le_take_prod (by norm_num) (by rw [hs]; exact Nat.mul_div_le _ _) hLsorted
      _ ≤ L.prod := Nat.le_of_dvd hpos (List.take_sublist (3 * s) L).prod_dvd_prod
      _ = ∏ p ∈ Ps, p := hLprod
  have hf3 : f ^ 3 ≤ ∏ p ∈ Ps, p ^ (n.factorization p) := by
    refine le_trans hf3_le_prod ?_
    exact Finset.prod_le_prod₀ (fun p hp => Nat.zero_le _) (fun p hp => by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (n.factorization p) :=
            Nat.pow_le_pow_right (hPsprime p hp).pos (hPfac p (hPs_sub hp)))
  have hd3 : (g * f) ^ 3 ≤ n := by
    rw [mul_pow]
    exact le_trans (Nat.mul_le_mul hg3 hf3) hnsplit.le
  -- divisor count
  have htau_n : (Nat.divisors n).card = ∏ p ∈ P, (n.factorization p + 1) := by
    rw [Nat.card_divisors hn0, hP]
  have hsplit : (∏ p ∈ P, (n.factorization p + 1))
      = (∏ p ∈ Pl, (n.factorization p + 1)) * (∏ p ∈ Ps, (n.factorization p + 1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not P (fun p => 3 ≤ n.factorization p)
        (fun p => n.factorization p + 1), ← hPl, ← hPs]
  have hPl_le : (∏ p ∈ Pl, (n.factorization p + 1))
      ≤ (∏ p ∈ Pl, (n.factorization p / 3 + 1)) ^ 5 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_le_prod₀ (fun p hp => Nat.zero_le _)
      (fun p hp => succ_le_div_add_one_pow_five _ (hPlfac p hp))
  have hPs_le : (∏ p ∈ Ps, (n.factorization p + 1)) ≤ 3 ^ Ps.card := by
    calc (∏ p ∈ Ps, (n.factorization p + 1)) ≤ ∏ _p ∈ Ps, (3:ℕ) :=
          Finset.prod_le_prod₀ (fun p hp => Nat.zero_le _) (fun p hp => by have := hPsfac p hp; omega)
      _ = 3 ^ Ps.card := Finset.prod_const 3
  have hthree : 3 ^ Ps.card ≤ 2 ^ (5 * s + 5) := by
    rw [hs_eq]; exact three_pow_le_five _
  have htau_d : (Nat.divisors (g * f)).card = (Nat.divisors g).card * (Nat.divisors f).card :=
    Nat.Coprime.card_divisors_mul hcop
  have hpowset : 2 ^ (5 * s) = (Nat.divisors f).card ^ 5 := by
    rw [htau_f, ← pow_mul]
    congr 1
    ring
  have htau_bound : (Nat.divisors n).card
      ≤ 2 ^ 5 * (Nat.divisors g).card ^ 5 * (Nat.divisors f).card ^ 5 := by
    calc (Nat.divisors n).card = ∏ p ∈ P, (n.factorization p + 1) := htau_n
      _ = (∏ p ∈ Pl, (n.factorization p + 1)) * (∏ p ∈ Ps, (n.factorization p + 1)) := hsplit
      _ ≤ (∏ p ∈ Pl, (n.factorization p / 3 + 1)) ^ 5 * 3 ^ Ps.card := Nat.mul_le_mul hPl_le hPs_le
      _ ≤ (∏ p ∈ Pl, (n.factorization p / 3 + 1)) ^ 5 * 2 ^ (5 * s + 5) :=
            Nat.mul_le_mul_left _ hthree
      _ = 2 ^ 5 * (∏ p ∈ Pl, (n.factorization p / 3 + 1)) ^ 5 * 2 ^ (5 * s) := by
            rw [pow_add]; ring
      _ = 2 ^ 5 * (Nat.divisors g).card ^ 5 * (Nat.divisors f).card ^ 5 := by
            rw [← htau_g, hpowset]
  refine ⟨g * f, hd_dvd, hd3, ?_⟩
  calc (Nat.divisors n).card ≤ 2 ^ 5 * (Nat.divisors g).card ^ 5 * (Nat.divisors f).card ^ 5 :=
        htau_bound
    _ = (2 * (Nat.divisors (g * f)).card) ^ 5 := by rw [htau_d]; ring

theorem tau_pow_eight_le_sum_dvd_cube (n : ℕ) (hn : 1 ≤ n) :
    ((n.divisors.card : ℝ) ^ ((8:ℕ):ℝ)) ≤
      ∑ d ∈ n.divisors.filter (fun e => e ^ 3 ≤ n), (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) := by
  obtain ⟨d, hdvd, hd3, htau⟩ := exists_divisor_cube_le_pow_five n hn
  have hmem : d ∈ n.divisors.filter (fun e => e ^ 3 ≤ n) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hdvd, by omega⟩, hd3⟩
  have hterm : (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ)
      ≤ ∑ d ∈ n.divisors.filter (fun e => e ^ 3 ≤ n), (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) :=
    Finset.single_le_sum (s := n.divisors.filter (fun e => e ^ 3 ≤ n))
      (f := fun d => (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ)) (fun b _ => by positivity) hmem
  have hcn : (n.divisors.card : ℝ) ≤ (2 * (d.divisors.card : ℝ)) ^ 5 := by
    exact_mod_cast htau
  calc ((n.divisors.card : ℝ) ^ ((8:ℕ):ℝ))
      = (n.divisors.card : ℝ) ^ 8 := by rw [Real.rpow_natCast]
    _ ≤ ((2 * (d.divisors.card : ℝ)) ^ 5) ^ 8 := by gcongr
    _ = (2 * (d.divisors.card : ℝ)) ^ ((40:ℕ):ℝ) := by
          rw [Real.rpow_natCast, ← pow_mul]
    _ ≤ _ := hterm

end Commons.NumberTheory.DivisorSum
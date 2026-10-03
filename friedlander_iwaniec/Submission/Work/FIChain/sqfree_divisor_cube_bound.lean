import Mathlib

namespace Work.FIChain

open Finset
open scoped BigOperators

private lemma exists_subset_prod_cube_le (s : Finset ℕ) (hpos : ∀ z ∈ s, 0 < z) :
    ∃ T ⊆ s, T.card = s.card / 3 ∧ (∏ z ∈ T, z) ^ 3 ≤ ∏ z ∈ s, z := by
  classical
  obtain ⟨U₀, hU₀sub, hU₀card⟩ :=
    Finset.exists_subset_card_eq (Nat.div_le_self s.card 3)
  have hne : (s.powerset.filter (fun U => U.card = s.card / 3)).Nonempty :=
    ⟨U₀, by simp only [mem_filter, mem_powerset]; exact ⟨hU₀sub, hU₀card⟩⟩
  obtain ⟨T, hTmem, hTmin⟩ :=
    Finset.exists_min_image (s.powerset.filter (fun U => U.card = s.card / 3))
      (fun U => ∏ z ∈ U, z) hne
  have hTsub : T ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp hTmem).1
  have hTcard : T.card = s.card / 3 := (Finset.mem_filter.mp hTmem).2
  have hTpos : ∀ z ∈ T, 0 < z := fun z hz => hpos z (hTsub hz)
  -- the extremal property
  have key : ∀ x ∈ T, ∀ y ∈ s, y ∉ T → x ≤ y := by
    intro x hx y hy hyn
    have hUsub : insert y (T.erase x) ⊆ s := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hy
      · exact hTsub (Finset.mem_of_mem_erase hz)
    have hyer : y ∉ T.erase x := fun h => hyn (Finset.mem_of_mem_erase h)
    have hUcard : (insert y (T.erase x)).card = s.card / 3 := by
      rw [Finset.card_insert_of_notMem hyer, Finset.card_erase_of_mem hx, hTcard]
      have : 0 < s.card / 3 := by rw [← hTcard]; exact Finset.card_pos.mpr ⟨x, hx⟩
      omega
    have hUmem : insert y (T.erase x) ∈ s.powerset.filter (fun U => U.card = s.card / 3) := by
      simp only [mem_filter, mem_powerset]
      exact ⟨hUsub, hUcard⟩
    have hmin := hTmin _ hUmem
    rw [Finset.prod_insert hyer] at hmin
    have hTprod : ∏ z ∈ T, z = (∏ z ∈ T.erase x, z) * x :=
      (Finset.prod_erase_mul T (fun z => z) hx).symm
    rw [hTprod] at hmin
    have hcpos : 0 < ∏ z ∈ T.erase x, z :=
      Finset.prod_pos (fun z hz => hTpos z (Finset.mem_of_mem_erase hz))
    rw [mul_comm y] at hmin
    exact Nat.le_of_mul_le_mul_left hmin hcpos
  refine ⟨T, hTsub, hTcard, ?_⟩
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · rw [hTe, Finset.prod_empty, one_pow]
    have : 0 < ∏ z ∈ s, z := Finset.prod_pos hpos
    omega
  · have hqmem : T.max' hTne ∈ T := Finset.max'_mem T hTne
    have hleT : ∀ z ∈ T, z ≤ T.max' hTne := fun z hz => Finset.le_max' T z hz
    have hprodT : ∏ z ∈ T, z ≤ (T.max' hTne) ^ (s.card / 3) := by
      have := Finset.prod_le_pow_card T (fun z => z) (T.max' hTne) hleT
      rwa [hTcard] at this
    have hcard_diff : (s \ T).card = s.card - s.card / 3 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hTsub, hTcard]
    have hprodST : (T.max' hTne) ^ (s.card - s.card / 3) ≤ ∏ z ∈ s \ T, z := by
      have hge : ∀ z ∈ s \ T, T.max' hTne ≤ z := by
        intro z hz
        rw [Finset.mem_sdiff] at hz
        exact key _ hqmem z hz.1 hz.2
      calc (T.max' hTne) ^ (s.card - s.card / 3)
          = ∏ _z ∈ s \ T, (T.max' hTne) := by rw [Finset.prod_const, hcard_diff]
        _ ≤ ∏ z ∈ s \ T, z := Finset.prod_le_prod₀ (fun z _ => Nat.zero_le _) hge
    have h3t : 3 * (s.card / 3) ≤ s.card := by
      have := Nat.div_mul_le_self s.card 3; omega
    have hpow : (T.max' hTne) ^ (2 * (s.card / 3)) ≤
        (T.max' hTne) ^ (s.card - s.card / 3) :=
      Nat.pow_le_pow_right (hTpos _ hqmem) (by omega)
    have he2 : (∏ z ∈ T, z) ^ 2 ≤ ∏ z ∈ s \ T, z := by
      calc (∏ z ∈ T, z) ^ 2
          ≤ ((T.max' hTne) ^ (s.card / 3)) ^ 2 := Nat.pow_le_pow_left hprodT 2
        _ = (T.max' hTne) ^ (2 * (s.card / 3)) := by rw [← pow_mul, mul_comm]
        _ ≤ (T.max' hTne) ^ (s.card - s.card / 3) := hpow
        _ ≤ ∏ z ∈ s \ T, z := hprodST
    calc (∏ z ∈ T, z) ^ 3
        = (∏ z ∈ T, z) * (∏ z ∈ T, z) ^ 2 := by ring
      _ ≤ (∏ z ∈ T, z) * (∏ z ∈ s \ T, z) := Nat.mul_le_mul_left _ he2
      _ = (∏ z ∈ s \ T, z) * (∏ z ∈ T, z) := by rw [mul_comm]
      _ = ∏ z ∈ s, z := Finset.prod_sdiff hTsub (f := fun z => z)

theorem sqfree_divisor_cube_bound (n : ℕ) (hn : Squarefree n) (hn0 : n ≠ 0) :
    ∃ e : ℕ, e ∣ n ∧ e ^ 3 ≤ n ∧ n.divisors.card ^ 3 ≤ (2 * e.divisors.card) ^ 9 := by
  classical
  have hpos : ∀ z ∈ n.primeFactors, 0 < z :=
    fun z hz => (Nat.mem_primeFactors.mp hz).1.pos
  obtain ⟨T, hTsub, hTcard, hTcube⟩ := exists_subset_prod_cube_le n.primeFactors hpos
  set e : ℕ := ∏ z ∈ T, z with he
  have hprimeT : ∀ z ∈ T, Nat.Prime z := fun z hz => (Nat.mem_primeFactors.mp (hTsub hz)).1
  have hpf : e.primeFactors = T := by
    rw [he]; exact Nat.primeFactors_prod hprimeT
  have he0 : e ≠ 0 := by
    rw [he]; exact Finset.prod_ne_zero_iff.mpr (fun z hz => (hprimeT z hz).ne_zero)
  have hdiv : e ∣ n := by
    rw [he, ← Nat.prod_primeFactors_of_squarefree hn]
    exact Finset.prod_dvd_prod_of_subset T n.primeFactors (fun z => z) hTsub
  have hsq : Squarefree e := Squarefree.squarefree_of_dvd hdiv hn
  have hcub : e ^ 3 ≤ n := by
    rw [he, ← Nat.prod_primeFactors_of_squarefree hn]
    exact hTcube
  have hcardn : n.divisors.card = 2 ^ n.primeFactors.card := by
    rw [Nat.card_divisors hn0]
    have h2 : ∏ x ∈ n.primeFactors, (n.factorization x + 1)
        = ∏ _x ∈ n.primeFactors, (2 : ℕ) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp' := Nat.mem_primeFactors.mp hp
      rw [Nat.factorization_eq_one_of_squarefree hn hp'.1 hp'.2.1]
    rw [h2, Finset.prod_const]
  have hcarde : e.divisors.card = 2 ^ T.card := by
    rw [Nat.card_divisors he0, hpf]
    have h2 : ∏ x ∈ T, (e.factorization x + 1) = ∏ _x ∈ T, (2 : ℕ) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hsq (hprimeT p hp)
        (Finset.dvd_prod_of_mem (fun z => z) hp)]
    rw [h2, Finset.prod_const]
  refine ⟨e, hdiv, hcub, ?_⟩
  rw [hcardn, hcarde]
  have hk2 : n.primeFactors.card ≤ 3 * T.card + 3 := by
    have hdm := Nat.div_add_mod n.primeFactors.card 3
    have hlt := Nat.mod_lt n.primeFactors.card (by norm_num : 0 < 3)
    omega
  calc (2 ^ n.primeFactors.card) ^ 3
      = 2 ^ (3 * n.primeFactors.card) := by rw [← pow_mul, mul_comm]
    _ ≤ 2 ^ (9 * (T.card + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = (2 * 2 ^ T.card) ^ 9 := by rw [← pow_succ', ← pow_mul, mul_comm]

end Work.FIChain

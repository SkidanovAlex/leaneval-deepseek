import Mathlib

namespace Work.FITop

open Finset

/-- Combinatorial core: in any finite set `P` of primes, one finds a subset `T` of size
`|P| / 3` whose product, cubed, is at most the product of all of `P`. -/
theorem exists_small_subset (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    ∃ T : Finset ℕ, T ⊆ P ∧ T.card = P.card / 3 ∧ (∏ p ∈ T, p) ^ 3 ≤ ∏ p ∈ P, p := by
  classical
  set k : ℕ := P.card with hk
  set j : ℕ := k / 3 with hj
  let e : Fin k ↪o ℕ := P.orderEmbOfFin hk.symm
  let a : ℕ → ℕ := fun i => if h : i < k then e ⟨i, h⟩ else 0
  have ha_val : ∀ i (h : i < k), a i = e ⟨i, h⟩ := by
    intro i h
    simp only [a]
    rw [dif_pos h]
  have hjk : j ≤ k := by rw [hj]; exact Nat.div_le_self k 3
  have h3j : 3 * j ≤ k := by
    rw [hj, Nat.mul_comm]; exact Nat.div_mul_le_self k 3
  have h2j : 2 * j ≤ k := by omega
  have ha_inj : Set.InjOn a (Finset.range j : Set ℕ) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_range] at hx hy
    rw [ha_val x (lt_of_lt_of_le hx hjk), ha_val y (lt_of_lt_of_le hy hjk)] at hxy
    have hfin : (⟨x, lt_of_lt_of_le hx hjk⟩ : Fin k) = ⟨y, lt_of_lt_of_le hy hjk⟩ :=
      e.injective hxy
    simpa using congrArg Fin.val hfin
  refine ⟨(Finset.range j).image a, ?_, ?_, ?_⟩
  · rintro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    rw [Finset.mem_range] at hi
    rw [ha_val i (lt_of_lt_of_le hi hjk)]
    exact Finset.orderEmbOfFin_mem P hk.symm _
  · rw [Finset.card_image_iff.mpr ha_inj, Finset.card_range]
  · have hTprod : (∏ p ∈ (Finset.range j).image a, p) = ∏ i ∈ Finset.range j, a i := by
      rw [Finset.prod_image ha_inj]
    have hPprod : (∏ p ∈ P, p) = ∏ i ∈ Finset.range k, a i := by
      conv_lhs => rw [← Finset.map_orderEmbOfFin_univ P hk.symm]
      rw [Finset.prod_map]
      rw [Finset.prod_range a]
      apply Finset.prod_congr rfl
      intro i _
      exact (ha_val i i.2).symm
    rw [hTprod, hPprod]
    have hstepA : (∏ i ∈ Finset.range j, a i) * (∏ i ∈ Finset.range j, a i)
        ≤ (∏ i ∈ Finset.range j, a (i + j)) * (∏ i ∈ Finset.range j, a (i + 2 * j)) := by
      apply Nat.mul_le_mul
      · apply Finset.prod_le_prod₀
        · intro i _; exact Nat.zero_le _
        · intro i hi
          rw [Finset.mem_range] at hi
          rw [ha_val i (lt_of_lt_of_le hi hjk), ha_val (i + j) (by omega)]
          exact (e.le_iff_le).mpr (by simp only [Fin.le_def]; omega)
      · apply Finset.prod_le_prod₀
        · intro i _; exact Nat.zero_le _
        · intro i hi
          rw [Finset.mem_range] at hi
          rw [ha_val i (lt_of_lt_of_le hi hjk), ha_val (i + 2 * j) (by omega)]
          exact (e.le_iff_le).mpr (by simp only [Fin.le_def]; omega)
    have hstepB : (∏ i ∈ Finset.range j, a (i + j)) * (∏ i ∈ Finset.range j, a (i + 2 * j))
        = ∏ i ∈ Finset.range (2 * j), a (i + j) := by
      rw [show 2 * j = j + j by ring, Finset.prod_range_add (fun i => a (i + j)) j j]
      congr 1
      apply Finset.prod_congr rfl
      intro x _
      congr 1
      ring
    have hstepC : (∏ i ∈ Finset.range (2 * j), a (i + j))
        ≤ ∏ i ∈ Finset.range (k - j), a (i + j) := by
      refine Finset.prod_le_prod_of_subset_of_one_le₀ ?_ (fun i _ => Nat.zero_le _) ?_
      · intro x hx
        rw [Finset.mem_range] at hx ⊢
        omega
      · intro i hi _
        rw [Finset.mem_range] at hi
        rw [ha_val (i + j) (by omega)]
        exact le_trans (by norm_num) (hprime _ (Finset.orderEmbOfFin_mem P hk.symm _)).two_le
    have hstep : (∏ i ∈ Finset.range j, a i) * (∏ i ∈ Finset.range j, a i)
        ≤ ∏ i ∈ Finset.range (k - j), a (i + j) :=
      hstepA.trans (hstepB.trans_le hstepC)
    have hfull : (∏ i ∈ Finset.range j, a i) * (∏ i ∈ Finset.range (k - j), a (i + j))
        = ∏ i ∈ Finset.range k, a i := by
      have hprod := Finset.prod_range_add a j (k - j)
      rw [show j + (k - j) = k by omega] at hprod
      rw [hprod]
      congr 1
      apply Finset.prod_congr rfl
      intro x _
      congr 1
      ring
    calc (∏ i ∈ Finset.range j, a i) ^ 3
        = (∏ i ∈ Finset.range j, a i) * ((∏ i ∈ Finset.range j, a i) * (∏ i ∈ Finset.range j, a i)) := by ring
      _ ≤ (∏ i ∈ Finset.range j, a i) * (∏ i ∈ Finset.range (k - j), a (i + j)) :=
          Nat.mul_le_mul_left _ hstep
      _ = ∏ i ∈ Finset.range k, a i := hfull

theorem WolkeSquarefreeTau (n : ℕ) (hn : 1 ≤ n) (hsq : Squarefree n) :
    ∃ d : ℕ, d ∣ n ∧ d ^ 3 ≤ n ∧ n.divisors.card ≤ (2 * d.divisors.card) ^ 3 := by
  classical
  have hn0 : n ≠ 0 := hsq.ne_zero
  obtain ⟨T, hTP, hTcard, hTprod⟩ :=
    exists_small_subset n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hTprime : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hTP hp)
  have hd0 : (∏ p ∈ T, p) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact (hTprime p hp).ne_zero
  refine ⟨∏ p ∈ T, p, ?_, ?_, ?_⟩
  · refine ⟨∏ p ∈ n.primeFactors \ T, p, ?_⟩
    rw [mul_comm]
    exact (Nat.prod_primeFactors_of_squarefree hsq).symm.trans
      (Finset.prod_sdiff hTP (f := fun p => p)).symm
  · rw [← Nat.prod_primeFactors_of_squarefree hsq]
    exact hTprod
  · set k : ℕ := n.primeFactors.card with hk
    set j : ℕ := k / 3 with hj
    have hndiv : n.divisors.card = 2 ^ k := by
      rw [Nat.card_divisors hn0]
      have h2 : ∀ x ∈ n.primeFactors, (n.factorization x + 1) = 2 := by
        intro x hx
        have hp := Nat.prime_of_mem_primeFactors hx
        have hxd := (Nat.mem_primeFactors.mp hx).2.1
        rw [Nat.factorization_eq_one_of_squarefree hsq hp hxd]
      rw [Finset.prod_congr rfl h2, Finset.prod_const, hk]
    have hdj : j ≤ (∏ p ∈ T, p).primeFactors.card := by
      have hsub : T ⊆ (∏ p ∈ T, p).primeFactors := by
        intro p hp
        refine Nat.mem_primeFactors.mpr ⟨hTprime p hp, ?_, hd0⟩
        exact Finset.dvd_prod_of_mem id hp
      calc j = T.card := hTcard.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hdge : 2 ^ j ≤ (∏ p ∈ T, p).divisors.card := by
      rw [Nat.card_divisors hd0]
      calc 2 ^ j ≤ 2 ^ (∏ p ∈ T, p).primeFactors.card :=
            Nat.pow_le_pow_right (by norm_num) hdj
        _ = ∏ x ∈ (∏ p ∈ T, p).primeFactors, 2 := (Finset.prod_const 2).symm
        _ ≤ ∏ x ∈ (∏ p ∈ T, p).primeFactors, ((∏ p ∈ T, p).factorization x + 1) := by
            apply Finset.prod_le_prod₀
            · intro x _; exact Nat.zero_le _
            · intro x hx
              have hx0 : (∏ p ∈ T, p).factorization x ≠ 0 := by
                rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hx
              omega
    have hkj : k ≤ 3 * j + 3 := by
      rw [hj]
      have h1 := Nat.div_add_mod k 3
      have h2 := Nat.mod_lt k (by norm_num : 0 < 3)
      omega
    have hpow : 2 ^ k ≤ (2 * 2 ^ j) ^ 3 := by
      have heq : (2 * 2 ^ j) ^ 3 = 2 ^ (3 * j + 3) := by
        rw [mul_pow, ← pow_mul, ← pow_add]
        congr 1
        ring
      rw [heq]
      exact Nat.pow_le_pow_right (by norm_num) hkj
    calc n.divisors.card = 2 ^ k := hndiv
      _ ≤ (2 * 2 ^ j) ^ 3 := hpow
      _ ≤ (2 * (∏ p ∈ T, p).divisors.card) ^ 3 := by
          apply Nat.pow_le_pow_left
          exact Nat.mul_le_mul_left 2 hdge

end Work.FITop

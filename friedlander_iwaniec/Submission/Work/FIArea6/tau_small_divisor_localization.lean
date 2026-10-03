import Mathlib

/-!
# `Work.FIArea6.tau_small_divisor_localization`

The elementary divisor-sum localization behind the `τ`-sum over the annulus: for squarefree `n`,

`4^{ω(n)} ≤ 16 · ∑_{d ∣ n, d³ ≤ n} τ(d)⁶`.

The point is that the `τ`-sum is dominated by *small* divisors: writing `p₁ < p₂ < … < p_k` for
the prime factors of `n` and `j = ⌊k/3⌋`, the divisor `d = p₁⋯p_j` already satisfies `d³ ≤ n`
and `τ(d) = 2^j`, while `3j ≥ k - 2`, so `4^k ≤ 16 · 4^{3j} = 16 · τ(d)^6`.

The useful form for the caller is the existence statement `tau_key_divisor`, stated directly in
terms of `n.primeFactors.card` and `n.divisors`.
-/

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- **Crux lemma.** For squarefree `n ≥ 1` there is a divisor `d` of `n` with `d³ ≤ n` and
`τ(d)⁶ ≥ 4^{ω(n)} / 16`, i.e. `4^{ω(n)} ≤ 16 · τ(d)⁶`.

The divisor is the product of the `⌊ω(n)/3⌋` smallest prime factors of `n`. -/
lemma tau_key_divisor (n : ℕ) (hn : 1 ≤ n) (hsf : Squarefree n) :
    ∃ d : ℕ, 0 < d ∧ d ∣ n ∧ d ^ 3 ≤ n ∧
      (4 : ℝ) ^ n.primeFactors.card ≤ 16 * (((d.divisors.card : ℕ) : ℝ)) ^ 6 := by
  rcases eq_or_lt_of_le hn with h1 | h2
  · subst h1
    refine ⟨1, by norm_num, by norm_num, by norm_num, ?_⟩
    simp
  have hn0 : n ≠ 0 := by omega
  set L := n.primeFactorsList with hLdef
  set k := L.length with hkdef
  set j := k / 3 with hjdef
  have hnodupL : L.Nodup := by rw [hLdef]; exact hsf.nodup_primeFactorsList
  have hsort : L.SortedLE := by rw [hLdef]; exact Nat.primeFactorsList_sorted n
  have hprodL : L.prod = n := by rw [hLdef]; exact Nat.prod_primeFactorsList hn0
  have hcard : n.primeFactors.card = k := by
    rw [hkdef, ← List.toFinset_card_of_nodup hnodupL, hLdef, Nat.toFinset_factors]
  have hjle : j ≤ k := by rw [hjdef]; exact Nat.div_le_self k 3
  have h3j : 3 * j ≤ k := by rw [hjdef]; exact Nat.mul_div_le k 3
  have hk1 : 1 ≤ k := by
    rw [hkdef, hLdef]
    have : 0 < (n.primeFactorsList).length :=
      List.length_pos_iff.mpr ((Nat.primeFactorsList_ne_nil n).mpr h2)
    omega
  have hjlt : j < L.length := by
    rw [hjdef, hkdef]
    exact Nat.div_lt_self (by omega) (by norm_num)
  set H := L.take j with hHdef
  set T := L.drop j with hTdef
  set d := H.prod with hddef
  set t := L[j]'hjlt with htdef
  have hnodupH : H.Nodup := by rw [hHdef]; exact (List.take_sublist j L).nodup hnodupL
  have hnodupT : T.Nodup := by rw [hTdef]; exact (List.drop_sublist j L).nodup hnodupL
  have hHlen : H.length = j := by
    rw [hHdef, List.length_take]
    exact min_eq_left hjle
  have hTlen : T.length = k - j := by rw [hTdef, List.length_drop, hkdef]
  have hdT : d * T.prod = n := by
    rw [hddef, hHdef, hTdef, List.prod_take_mul_prod_drop, hprodL]
  have hdivd : d ∣ n := ⟨T.prod, hdT.symm⟩
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdivd (by omega)
  have ht1 : 1 ≤ t := by
    rw [htdef]
    have hmem : L[j]'hjlt ∈ n.primeFactorsList := by
      rw [← hLdef]; exact List.getElem_mem hjlt
    exact (Nat.prime_of_mem_primeFactorsList hmem).one_lt.le
  have hHle : ∀ a ∈ H, a ≤ t := by
    intro a ha
    rw [hHdef] at ha
    obtain ⟨i, hi, hia⟩ := List.mem_take_iff_getElem.mp ha
    have hij : i < j := lt_of_lt_of_le hi (min_le_left _ _)
    have hiL : i < L.length := lt_of_lt_of_le hi (min_le_right _ _)
    rw [← hia, htdef]
    exact hsort.getElem_le_getElem_of_le (le_of_lt hij)
  have hTge : ∀ b ∈ T, t ≤ b := by
    intro b hb
    rw [hTdef] at hb
    obtain ⟨i, hi, hib⟩ := List.mem_drop_iff_getElem.mp hb
    rw [← hib, htdef]
    exact hsort.getElem_le_getElem_of_le (Nat.le_add_right j i)
  have hd_eq : d = ∏ p ∈ H.toFinset, p := by
    rw [hddef, List.prod_toFinset (fun x => x) hnodupH, List.map_id']
  have hd_le : d ≤ t ^ j := by
    rw [hd_eq]
    have h1 := Finset.prod_le_pow_card H.toFinset (fun p => p) t
      (fun p hp => hHle p (by rwa [List.mem_toFinset] at hp))
    rw [List.toFinset_card_of_nodup hnodupH, hHlen] at h1
    exact h1
  have hT_ge_prod : t ^ (k - j) ≤ T.prod := by
    have h1 : ∏ p ∈ T.toFinset, t ≤ ∏ p ∈ T.toFinset, p := by
      apply Finset.prod_le_prod₀
      · intro i hi; exact Nat.zero_le _
      · intro i hi
        exact hTge i (by rwa [List.mem_toFinset] at hi)
    have h2 : ∏ p ∈ T.toFinset, p = T.prod := by
      rw [List.prod_toFinset (fun x => x) hnodupT, List.map_id']
    have h3 : ∏ p ∈ T.toFinset, t = t ^ (k - j) := by
      rw [Finset.prod_const, List.toFinset_card_of_nodup hnodupT, hTlen]
    rw [h3, h2] at h1
    exact h1
  have h2j_le_kj : 2 * j ≤ k - j := by omega
  have hd2 : d ^ 2 ≤ T.prod := by
    calc d ^ 2 ≤ (t ^ j) ^ 2 := Nat.pow_le_pow_left hd_le 2
      _ = t ^ (2 * j) := by rw [← pow_mul]; congr 1; omega
      _ ≤ t ^ (k - j) := Nat.pow_le_pow_right (by omega) h2j_le_kj
      _ ≤ T.prod := hT_ge_prod
  have hd3 : d ^ 3 ≤ n := by
    calc d ^ 3 = d * d ^ 2 := by ring
      _ ≤ d * T.prod := Nat.mul_le_mul_left d hd2
      _ = n := hdT
  have hge : j ≤ d.primeFactors.card := by
    have hsub : H.toFinset ⊆ d.primeFactors := by
      intro p hp
      rw [List.mem_toFinset] at hp
      rw [Nat.mem_primeFactors]
      refine ⟨?_, ?_, hdpos.ne'⟩
      · have hmem : p ∈ n.primeFactorsList := by
          rw [← hLdef]
          exact List.mem_of_mem_take hp
        exact Nat.prime_of_mem_primeFactorsList hmem
      · rw [hddef]
        exact List.dvd_prod hp
    calc j = H.toFinset.card := by rw [List.toFinset_card_of_nodup hnodupH, hHlen]
      _ ≤ d.primeFactors.card := Finset.card_le_card hsub
  have h2j_le : 2 ^ j ≤ d.divisors.card := by
    have hd0 : d ≠ 0 := hdpos.ne'
    have h : 2 ^ j ≤ ∏ x ∈ d.primeFactors, (d.factorization x + 1) := by
      calc 2 ^ j ≤ 2 ^ d.primeFactors.card := Nat.pow_le_pow_right (by norm_num) hge
        _ = ∏ x ∈ d.primeFactors, 2 := (Finset.prod_const 2).symm
        _ ≤ ∏ x ∈ d.primeFactors, (d.factorization x + 1) := by
            apply Finset.prod_le_prod₀
            · intro i hi; positivity
            · intro i hi
              have hx : i ∈ d.factorization.support := by
                rw [Nat.support_factorization]; exact hi
              have : d.factorization i ≠ 0 := Finsupp.mem_support_iff.mp hx
              omega
    rw [← Nat.card_divisors hd0] at h
    exact h
  have hk_le : k ≤ 3 * j + 2 := by
    have hmod : k % 3 ≤ 2 := by
      have := Nat.mod_lt k (by norm_num : 0 < 3); omega
    have h := Nat.div_add_mod k 3
    omega
  have hreal : (4:ℝ) ^ k ≤ 16 * (((d.divisors.card : ℕ) : ℝ)) ^ 6 := by
    have h1 : (4:ℝ)^k ≤ (4:ℝ)^(3*j+2) := pow_le_pow_right₀ (by norm_num) hk_le
    have h2 : (4:ℝ)^(3*j+2) = 16 * (4:ℝ)^(3*j) := by
      rw [pow_add]; norm_num; ring
    have h3 : (4:ℝ)^(3*j) ≤ (((d.divisors.card : ℕ) : ℝ))^6 := by
      have h4 : (4:ℝ)^(3*j) = ((2:ℝ)^j)^6 := by
        rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, ← pow_mul, ← pow_mul]
        congr 1
        ring
      rw [h4]
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast h2j_le
    linarith
  exact ⟨d, hdpos, hdivd, hd3, by rw [hcard]; exact hreal⟩

theorem tau_small_divisor_localization : ∃ C : ℝ, 0 < C ∧ C ≤ 100 ∧
    ∀ n : ℕ, 1 ≤ n → Squarefree n →
      ((4 : ℝ) ^ n.primeFactors.card)
        ≤ C * ∑ d ∈ n.divisors.filter (fun d => d ^ 3 ≤ n), (((d.divisors.card : ℕ) : ℝ)) ^ 6 := by
  refine ⟨16, by norm_num, by norm_num, ?_⟩
  intro n hn1 hsf
  obtain ⟨d, hdpos, hddvd, hd3, hineq⟩ := tau_key_divisor n hn1 hsf
  have hn0 : n ≠ 0 := by omega
  have hmem : d ∈ n.divisors.filter (fun x => x ^ 3 ≤ n) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hddvd, hn0⟩, hd3⟩
  have hS : (((d.divisors.card : ℕ) : ℝ)) ^ 6 ≤
      ∑ d ∈ n.divisors.filter (fun x => x ^ 3 ≤ n),
        (((d.divisors.card : ℕ) : ℝ)) ^ 6 := by
    apply Finset.single_le_sum (fun x _ => by positivity) hmem
  calc (4 : ℝ) ^ n.primeFactors.card
      ≤ 16 * (((d.divisors.card : ℕ) : ℝ)) ^ 6 := hineq
    _ ≤ 16 * ∑ d ∈ n.divisors.filter (fun x => x ^ 3 ≤ n),
          (((d.divisors.card : ℕ) : ℝ)) ^ 6 :=
        mul_le_mul_of_nonneg_left hS (by norm_num)

end Work.FIArea6

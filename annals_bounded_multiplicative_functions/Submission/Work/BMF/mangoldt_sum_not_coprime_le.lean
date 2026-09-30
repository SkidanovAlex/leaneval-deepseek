import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset ArithmeticFunction

/-- A finite set `S ⊆ ℕ` consisting of positive integers and closed downwards contains its own
cardinality: if `1 ≤ j ≤ #S` then `j ∈ S`. -/
lemma card_mem_of_downward {S : Finset ℕ} (hpos : ∀ k ∈ S, 1 ≤ k)
    (hdc : ∀ k ∈ S, ∀ j, 1 ≤ j → j ≤ k → j ∈ S) :
    ∀ j, 1 ≤ j → j ≤ S.card → j ∈ S := by
  intro j hj1 hjcard
  by_contra hj
  have hsub : S ⊆ Finset.Icc 1 (j - 1) := by
    intro k hk
    rw [Finset.mem_Icc]
    refine ⟨hpos k hk, ?_⟩
    by_contra h
    push Not at h
    exact hj (hdc k hk j hj1 (by omega))
  have hle : S.card ≤ (Finset.Icc 1 (j - 1)).card := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hle
  omega

/-- The prime powers of `p` up to `N`: the image of the exponents `k ∈ [1,N]` with `p^k ≤ N`
under `k ↦ p^k`. -/
def ppow (p N : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 N).filter (fun k : ℕ => p ^ k ≤ N)).image (fun k => p ^ k)

/-- The von Mangoldt sum over the prime powers of a prime `p` up to `N` equals
`(#ppow p N) · log p`: every element is `p^k` with `k ≥ 1`, where `Λ (p^k) = Λ p = log p`. -/
lemma sum_ppow {p N : ℕ} (hp : p.Prime) :
    ∑ n ∈ ppow p N, ArithmeticFunction.vonMangoldt n
      = ((ppow p N).card : ℝ) * Real.log p := by
  classical
  rw [ppow, Finset.sum_image ((Nat.pow_right_injective hp.two_le).injOn)]
  have hcongr :
      ∑ k ∈ (Finset.Icc 1 N).filter (fun k : ℕ => p ^ k ≤ N),
          ArithmeticFunction.vonMangoldt (p ^ k)
        = ∑ k ∈ (Finset.Icc 1 N).filter (fun k : ℕ => p ^ k ≤ N),
            Real.log (p : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := by
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      exact hk.1.1
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0),
        ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [hcongr, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_image_of_injective _ (Nat.pow_right_injective hp.two_le)]

/-- For a prime `p` and `1 ≤ N`, `p ^ (#ppow p N) ≤ N`. -/
lemma pow_card_ppow_le {p N : ℕ} (hp : p.Prime) (hN : 1 ≤ N) : p ^ (ppow p N).card ≤ N := by
  classical
  set K := (Finset.Icc 1 N).filter (fun k : ℕ => p ^ k ≤ N) with hK
  have hcard : (ppow p N).card = K.card := by
    rw [ppow, hK, Finset.card_image_of_injective _ (Nat.pow_right_injective hp.two_le)]
  rw [hcard]
  have hpos : ∀ k ∈ K, 1 ≤ k := by
    intro k hk
    rw [hK, Finset.mem_filter, Finset.mem_Icc] at hk
    exact hk.1.1
  have hdc : ∀ k ∈ K, ∀ j, 1 ≤ j → j ≤ k → j ∈ K := by
    intro k hk j hj1 hjk
    rw [hK, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    exact ⟨⟨hj1, le_trans hjk hk.1.2⟩, le_trans (Nat.pow_le_pow_right hp.pos hjk) hk.2⟩
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · rw [hKe, Finset.card_empty, pow_zero]; exact hN
  · have hcard1 : 1 ≤ K.card := Finset.card_pos.mpr hKne
    have hmem := card_mem_of_downward hpos hdc K.card hcard1 le_rfl
    rw [hK, Finset.mem_filter] at hmem
    exact hmem.2

/-- The prime powers of one prime `p` up to `N` contribute at most `log N`. -/
lemma sum_ppow_le_log {p N : ℕ} (hp : p.Prime) (hN : 1 ≤ N) :
    ∑ n ∈ ppow p N, ArithmeticFunction.vonMangoldt n ≤ Real.log N := by
  rw [sum_ppow hp]
  have hR : ((p : ℝ)) ^ (ppow p N).card ≤ (N : ℝ) := by
    exact_mod_cast pow_card_ppow_le hp hN
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have h := Real.log_le_log (pow_pos hppos _) hR
  rwa [Real.log_pow] at h

/-- For distinct primes `p, p'`, the prime powers of `p` and of `p'` up to `N` are disjoint. -/
lemma ppow_disjoint {p p' N : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hne : p ≠ p') :
    Disjoint (ppow p N) (ppow p' N) := by
  rw [Finset.disjoint_left]
  intro n hn hn'
  rw [ppow, Finset.mem_image] at hn hn'
  obtain ⟨k, hk, hkeq⟩ := hn
  obtain ⟨l, hl, hleq⟩ := hn'
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
  have hpdvd_n : p ∣ n := by
    rw [← hkeq]; exact dvd_pow_self p (by omega)
  have hpdvd : p ∣ p' ^ l := by rw [hleq]; exact hpdvd_n
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hp').mp (hp.dvd_of_dvd_pow hpdvd))

/-- The family of prime-power sets `ppow p N`, `p` ranging over the prime factors of `q`, is
pairwise disjoint. -/
lemma pairwiseDisjoint_ppow (q N : ℕ) :
    (↑(q.primeFactors) : Set ℕ).PairwiseDisjoint (fun p => ppow p N) := by
  intro p hp p' hp' hne
  simp only [Finset.mem_coe] at hp hp'
  rw [Nat.mem_primeFactors] at hp hp'
  exact ppow_disjoint hp.1 hp'.1 hne

/-- Every integer `≤ N` that is not coprime to `q` and has `Λ n ≠ 0` is a prime power of some
prime dividing `q`. -/
lemma filter_subset_biUnion_ppow (q N : ℕ) [NeZero q] :
    ((Finset.Icc 1 N).filter (fun n : ℕ => ¬ n.Coprime q)).filter
        (fun n => ArithmeticFunction.vonMangoldt n ≠ 0)
      ⊆ q.primeFactors.biUnion (fun p => ppow p N) := by
  classical
  intro n hn
  rw [Finset.mem_filter] at hn
  obtain ⟨hnS, hΛ⟩ := hn
  rw [Finset.mem_filter] at hnS
  obtain ⟨hnI, hcop⟩ := hnS
  rw [Finset.mem_Icc] at hnI
  have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
  obtain ⟨r, k, hr, hkpos, hrk⟩ := (isPrimePow_nat_iff n).mp hpp
  obtain ⟨p, hpprime, hpn, hpq⟩ := (Nat.Prime.not_coprime_iff_dvd).mp hcop
  have hpr : p = r := by
    have h2 : p ∣ r ^ k := by rw [hrk]; exact hpn
    exact (Nat.prime_dvd_prime_iff_eq hpprime hr).mp (hpprime.dvd_of_dvd_pow h2)
  have hrq : r ∣ q := hpr ▸ hpq
  rw [Finset.mem_biUnion]
  refine ⟨r, ?_, ?_⟩
  · rw [Nat.mem_primeFactors]; exact ⟨hr, hrq, NeZero.ne q⟩
  · rw [ppow, Finset.mem_image]
    refine ⟨k, ?_, hrk⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hkpos, ?_⟩, ?_⟩
    · calc k ≤ 2 ^ k := le_of_lt Nat.lt_two_pow_self
        _ ≤ r ^ k := Nat.pow_le_pow_left hr.two_le k
        _ = n := hrk
        _ ≤ N := hnI.2
    · rw [hrk]; exact hnI.2

/-- The von Mangoldt sum over integers `≤ N` that are **not** coprime to `q` is at most
`ω(q) · log N`: each such `n` with `Λ n ≠ 0` is a prime power `p^k` with `p | q` (and these
`n` are counted once each, attached to their unique prime divisor), and for a fixed prime
`p | q` the contribution `∑_{k : p^k ≤ N} log p = ⌊log_p N⌋ log p ≤ log N`.  Used in `N10`
(`vk_prime_sums`) to compare the prime sum twisted by the principal character mod `q` with the
untwisted one. -/
theorem mangoldt_sum_not_coprime_le {q : ℕ} [NeZero q] (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => ¬ n.Coprime q),
        (ArithmeticFunction.vonMangoldt n : ℝ)
      ≤ (q.primeFactors.card : ℝ) * Real.log N := by
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0; simp [Real.log_zero]
  set S := (Finset.Icc 1 N).filter (fun n : ℕ => ¬ n.Coprime q) with hS
  set S' := S.filter (fun n => ArithmeticFunction.vonMangoldt n ≠ 0) with hS'
  have h1 : ∑ n ∈ S', ArithmeticFunction.vonMangoldt n
      = ∑ n ∈ S, ArithmeticFunction.vonMangoldt n := by
    rw [hS']
    exact Finset.sum_subset (Finset.filter_subset _ _) (fun n hn hnnot => by
      by_contra h
      exact hnnot (Finset.mem_filter.mpr ⟨hn, h⟩))
  have h2 : ∑ n ∈ S', ArithmeticFunction.vonMangoldt n
      ≤ ∑ n ∈ q.primeFactors.biUnion (fun p => ppow p N),
          ArithmeticFunction.vonMangoldt n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · rw [hS', hS]
      exact filter_subset_biUnion_ppow q N
    · intro n _ _; exact ArithmeticFunction.vonMangoldt_nonneg
  have h3 : ∑ n ∈ q.primeFactors.biUnion (fun p => ppow p N),
        ArithmeticFunction.vonMangoldt n
      = ∑ p ∈ q.primeFactors, ∑ n ∈ ppow p N, ArithmeticFunction.vonMangoldt n :=
    Finset.sum_biUnion (pairwiseDisjoint_ppow q N)
  have h4 : ∑ p ∈ q.primeFactors, ∑ n ∈ ppow p N, ArithmeticFunction.vonMangoldt n
      ≤ ∑ _p ∈ q.primeFactors, Real.log N := by
    apply Finset.sum_le_sum
    intro p hp
    exact sum_ppow_le_log (Nat.mem_primeFactors.mp hp).1 hN
  have h5 : ∑ _p ∈ q.primeFactors, Real.log N = (q.primeFactors.card : ℝ) * Real.log N := by
    rw [Finset.sum_const, nsmul_eq_mul]
  calc ∑ n ∈ S, ArithmeticFunction.vonMangoldt n
      = ∑ n ∈ S', ArithmeticFunction.vonMangoldt n := h1.symm
    _ ≤ ∑ n ∈ q.primeFactors.biUnion (fun p => ppow p N),
          ArithmeticFunction.vonMangoldt n := h2
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ ppow p N, ArithmeticFunction.vonMangoldt n := h3
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log N := h4
    _ = (q.primeFactors.card : ℝ) * Real.log N := h5

end Work.BMF

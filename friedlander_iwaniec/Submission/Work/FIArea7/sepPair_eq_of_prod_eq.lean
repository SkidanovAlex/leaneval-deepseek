/-
# `Submission.Work.FIArea7.sepPair_eq_of_prod_eq`

Injectivity of the *FI* §24 separation triple `(d, m, n)` in its product `d·m·n`.

`IsSepPair r d m n` (`SepDiv.lean`) says that `(d, m, n)` is obtained from the *decreasing*
enumeration `p₁ > p₂ > … > p_k` of the prime factors of `l = d·m·n` by the interleaved block
pattern (24.2), (24.4), (24.5): `d`, `m`, `n` are the products of the primes at the positions of
`dIdx`, `mIdx`, `nIdx` respectively.

The combinatorial content is that this decreasing enumeration is *unique*: any two
`IsPrimeList l k p`, `IsPrimeList l k' p'` have the same length and the same values.  The proof
here is elementary and avoids unique factorisation:

* **(i)** `Finset.univ.image p = l.primeFactors`, because `l = ∏ pᵢ` and the `pᵢ` are distinct
  primes (strict antitonicity), so the primes dividing `l` are exactly the values of `p`
  (`IsPrimeList.image_eq_primeFactors`);
* **(ii)** for a strictly antitone `p`, the number of values of `p` that exceed `p i` is exactly
  `i`, i.e. `((image p).filter (· > p i)).card = i.val` (`rank_eq`);
* **(iii)** the map `x ↦ (s.filter (· > x)).card` is injective on any finset `s` of naturals
  (`rank_injOn`), since `x < y` makes `s.filter (· > y)` a *proper* subset of `s.filter (· > x)`.

Combining (i)–(iii) identifies the common enumeration, and the products over the three index sets
are transported along the resulting equality `k = k'` (`prod_{d,m,n}Idx_cast`).
-/
import Mathlib
import Submission.Work.FIArea7.SepDiv

set_option autoImplicit false

namespace Work.FIArea7

open Finset

/-! ## The number of elements of `Fin k` below a given one -/

lemma card_fin_lt {k : ℕ} (i : Fin k) :
    (Finset.univ.filter (fun j : Fin k => j < i)).card = i.val := by
  have : Finset.univ.filter (fun j : Fin k => j < i) = Finset.Iio i := by
    ext j; simp [Finset.mem_Iio]
  rw [this, Fin.card_Iio]

/-! ## The rank of a value in a strictly antitone enumeration -/

lemma rank_eq {k : ℕ} {p : Fin k → ℕ} (hp : StrictAnti p) (i : Fin k) :
    ((Finset.univ.image p).filter (fun z => p i < z)).card = i.val := by
  have hset : Finset.univ.filter (fun j : Fin k => p i < p j)
      = Finset.univ.filter (fun j : Fin k => j < i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hij
      rcases lt_trichotomy j i with h | h | h
      · exact h
      · exact absurd hij (by rw [h]; exact lt_irrefl _)
      · exact absurd (hp h) (not_lt.mpr (le_of_lt hij))
    · intro hji; exact hp hji
  rw [Finset.filter_image, hset, Finset.card_image_of_injective _ hp.injective]
  exact card_fin_lt i

/-! ## The rank map is injective on any finset of naturals -/

lemma rank_injOn {s : Finset ℕ} {x y : ℕ} (hx : x ∈ s) (hy : y ∈ s)
    (h : (s.filter (fun z => x < z)).card = (s.filter (fun z => y < z)).card) : x = y := by
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · have hsub : s.filter (fun z => y < z) ⊆ s.filter (fun z => x < z) := by
      intro z hz
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hz).1, lt_trans hlt (Finset.mem_filter.mp hz).2⟩
    have hss : s.filter (fun z => y < z) ⊂ s.filter (fun z => x < z) := by
      rw [Finset.ssubset_iff_of_subset hsub]
      exact ⟨y, Finset.mem_filter.mpr ⟨hy, hlt⟩,
        fun hc => lt_irrefl y (Finset.mem_filter.mp hc).2⟩
    have := Finset.card_lt_card hss
    omega
  · have hsub : s.filter (fun z => x < z) ⊆ s.filter (fun z => y < z) := by
      intro z hz
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hz).1, lt_trans hlt (Finset.mem_filter.mp hz).2⟩
    have hss : s.filter (fun z => x < z) ⊂ s.filter (fun z => y < z) := by
      rw [Finset.ssubset_iff_of_subset hsub]
      exact ⟨x, Finset.mem_filter.mpr ⟨hx, hlt⟩,
        fun hc => lt_irrefl x (Finset.mem_filter.mp hc).2⟩
    have := Finset.card_lt_card hss
    omega

/-! ## Uniqueness of `IsPrimeList` -/

lemma IsPrimeList.prod_pos {l k : ℕ} {p : Fin k → ℕ} (hp : IsPrimeList l k p) : 0 < l := by
  obtain ⟨-, hprime, hprod⟩ := hp
  rw [hprod]
  exact Finset.prod_pos (fun i _ => (hprime i).pos)

/-- The values of a decreasing prime list of product `l` are exactly the primes dividing `l`. -/
lemma IsPrimeList.image_eq_primeFactors {l k : ℕ} {p : Fin k → ℕ} (H : IsPrimeList l k p) :
    Finset.univ.image p = l.primeFactors := by
  have hl0 : l ≠ 0 := ne_of_gt (IsPrimeList.prod_pos H)
  obtain ⟨hmono, hprime, hprod⟩ := H
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    rw [Nat.mem_primeFactors]
    exact ⟨hprime i, by rw [hprod]; exact Finset.dvd_prod_of_mem p (Finset.mem_univ i), hl0⟩
  · intro x hx
    rw [Nat.mem_primeFactors] at hx
    obtain ⟨hxp, hxdvd, -⟩ := hx
    rw [Finset.mem_image]
    have hdvd' : x ∣ ∏ i, p i := by rw [← hprod]; exact hxdvd
    rw [Nat.prime_iff] at hxp
    obtain ⟨i, -, hdi⟩ := (Prime.dvd_finsetProd_iff hxp p).mp hdvd'
    refine ⟨i, Finset.mem_univ i, ?_⟩
    rcases (Nat.dvd_prime (hprime i)).mp hdi with h1 | h1
    · exact absurd h1 hxp.ne_one
    · exact h1.symm

/-- Two decreasing prime lists with the same product have the same length and the same values. -/
lemma IsPrimeList.eq_of_eq {l k k' : ℕ} {p : Fin k → ℕ} {p' : Fin k' → ℕ}
    (hp : IsPrimeList l k p) (hp' : IsPrimeList l k' p') :
    ∃ hc : k = k', ∀ i : Fin k, p i = p' (Fin.cast hc i) := by
  have him : Finset.univ.image p = Finset.univ.image p' := by
    rw [IsPrimeList.image_eq_primeFactors hp, IsPrimeList.image_eq_primeFactors hp']
  obtain ⟨hmono, hprime, hprod⟩ := hp
  obtain ⟨hmono', hprime', hprod'⟩ := hp'
  have hcard : k = k' := by
    have h1 : (Finset.univ.image p).card = k := by
      rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
    have h2 : (Finset.univ.image p').card = k' := by
      rw [Finset.card_image_of_injective _ hmono'.injective, Finset.card_univ, Fintype.card_fin]
    rw [← h1, ← h2, him]
  refine ⟨hcard, fun i => ?_⟩
  have hri : ((Finset.univ.image p).filter (fun z => p i < z)).card = i.val := rank_eq hmono i
  have hrj : ((Finset.univ.image p).filter (fun z => p' (Fin.cast hcard i) < z)).card = i.val := by
    have h := rank_eq hmono' (Fin.cast hcard i)
    rw [← him] at h
    simpa [Fin.val_cast] using h
  have hx : p i ∈ Finset.univ.image p := Finset.mem_image_of_mem p (Finset.mem_univ i)
  have hy : p' (Fin.cast hcard i) ∈ Finset.univ.image p := by
    rw [him]; exact Finset.mem_image_of_mem p' (Finset.mem_univ _)
  exact rank_injOn hx hy (by rw [hri, hrj])

/-! ## Transporting a product along `k = k'` -/

lemma prod_filter_cast {k k' : ℕ} (h : k = k') (q : Fin k' → ℕ)
    (P : ℕ → Prop) [DecidablePred P] :
    (∏ i ∈ (Finset.univ.filter (fun i : Fin k => P i.val)), q (Fin.cast h i))
      = ∏ j ∈ (Finset.univ.filter (fun j : Fin k' => P j.val)), q j := by
  apply Finset.prod_bij (fun i _ => Fin.cast h i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rwa [Fin.val_cast]
  · intro i _ j _ hij
    exact Fin.cast_injective h hij
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    refine ⟨Fin.cast h.symm b, ?_, ?_⟩
    · rwa [Fin.val_cast]
    · apply Fin.ext; simp
  · intro i _; rfl

lemma prod_dIdx_cast {r k k' : ℕ} (h : k = k') (q : Fin k' → ℕ) :
    (∏ i ∈ dIdx r k, q (Fin.cast h i)) = ∏ j ∈ dIdx r k', q j := by
  unfold dIdx
  exact prod_filter_cast h q (fun n => n < r ∨ ((n + 1) % r = 0 ∧ 2 * r ≤ n + 1))

lemma prod_mIdx_cast {r k k' : ℕ} (h : k = k') (q : Fin k' → ℕ) :
    (∏ i ∈ mIdx r k, q (Fin.cast h i)) = ∏ j ∈ mIdx r k', q j := by
  unfold mIdx
  exact prod_filter_cast h q (fun n => 0 < (n + 1) % r ∧ ((n + 1) / r) % 2 = 1)

lemma prod_nIdx_cast {r k k' : ℕ} (h : k = k') (q : Fin k' → ℕ) :
    (∏ i ∈ nIdx r k, q (Fin.cast h i)) = ∏ j ∈ nIdx r k', q j := by
  unfold nIdx
  exact prod_filter_cast h q (fun n => 0 < (n + 1) % r ∧ ((n + 1) / r) % 2 = 0 ∧ 0 < (n + 1) / r)

/-! ## The main theorem -/

theorem sepPair_eq_of_prod_eq {r d m n d' m' n' : ℕ}
    (h : IsSepPair r d m n) (h' : IsSepPair r d' m' n') (hp : d * m * n = d' * m' * n') :
    d = d' ∧ m = m' ∧ n = n' := by
  obtain ⟨k, p, hpl, hd, hm, hn⟩ := h
  obtain ⟨k', p', hpl', hd', hm', hn'⟩ := h'
  have hpl2 : IsPrimeList (d * m * n) k' p' := by rw [hp]; exact hpl'
  obtain ⟨hc, hpk⟩ := IsPrimeList.eq_of_eq hpl hpl2
  refine ⟨?_, ?_, ?_⟩
  · rw [hd, hd']
    exact (Finset.prod_congr rfl (fun i _ => hpk i)).trans (prod_dIdx_cast hc p')
  · rw [hm, hm']
    exact (Finset.prod_congr rfl (fun i _ => hpk i)).trans (prod_mIdx_cast hc p')
  · rw [hn, hn']
    exact (Finset.prod_congr rfl (fun i _ => hpk i)).trans (prod_nIdx_cast hc p')

end Work.FIArea7

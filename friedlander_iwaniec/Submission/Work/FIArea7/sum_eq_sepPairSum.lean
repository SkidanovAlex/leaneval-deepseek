import Mathlib
import Submission.Work.FIArea7.SepDiv
import Submission.Work.FIArea7.sepIdx_partition
import Submission.Work.FIArea7.sepPair_eq_of_prod_eq
import Submission.Work.FIArea7.sepPair_squarefree

/-!
# `Work.FIArea7.sum_eq_sepPairSum` — *FI* Lemma 24.1 / (24.11)

The sum of `f` over squarefree `ℓ ⩽ x` free of prime factors `> z` equals the double sum over
separation triples `(d, m, n)` with `d ⩽ D`, `m, n ⩽ x` and product `ℓ`; the point is that every
squarefree `ℓ` has a *unique* separation triple (the one of *FI* (24.2)/(24.4)/(24.5)), so both
sides are the same sum of `f` over the squarefree `ℓ ⩽ x` with all prime factors `⩽ z`.
-/

open Finset
open scoped BigOperators

namespace Work.FIArea7

/-! ### The decreasing prime list is unique -/

/-- Two strictly decreasing prime lists with the same product are equal. -/
theorem list_eq_of_sortedGT_of_prod_eq {u v : List ℕ} (hu : u.SortedGT) (hv : v.SortedGT)
    (hu' : ∀ q ∈ u, q.Prime) (hv' : ∀ q ∈ v, q.Prime) (h : u.prod = v.prod) : u = v := by
  have hpu : u.Perm u.prod.primeFactorsList := Nat.primeFactorsList_unique rfl hu'
  have hpv : v.Perm v.prod.primeFactorsList := Nat.primeFactorsList_unique rfl hv'
  rw [h] at hpu
  exact List.Perm.eq_of_sortedGE hu.sortedGE hv.sortedGE (hpu.trans hpv.symm)

/-- A positional product (over a filtered `Finset.univ`) depends only on the list
`List.ofFn p`, not on how the index set `Fin k` is presented. -/
theorem prod_filter_univ_eq {k k' : ℕ} {c : ℕ → Prop} [DecidablePred c] (p : Fin k → ℕ)
    (p' : Fin k' → ℕ) (h : List.ofFn p = List.ofFn p') :
    (∏ i ∈ (Finset.univ : Finset (Fin k)).filter (fun i => c i.val), p i) =
      ∏ i ∈ (Finset.univ : Finset (Fin k')).filter (fun i => c i.val), p' i := by
  have hk : k = k' := by simpa using congrArg List.length h
  subst hk
  exact Finset.prod_congr rfl fun i _ => congrFun (List.ofFn_injective h) i

/-- The three components of a separation triple are positive. -/
theorem IsSepPair.pos {r d m n : ℕ} (h : IsSepPair r d m n) : 0 < d ∧ 0 < m ∧ 0 < n := by
  obtain ⟨k, p, hpl, hd, hm, hn⟩ := h
  rw [hd, hm, hn]
  exact ⟨Finset.prod_pos fun i _ => (hpl.2.1 i).pos,
    Finset.prod_pos fun i _ => (hpl.2.1 i).pos,
    Finset.prod_pos fun i _ => (hpl.2.1 i).pos⟩

/-- The three index sets of *FI* §24 split the full index set, hence split the product. -/
theorem prod_sepIdx_split (r k : ℕ) (hr : 2 ≤ r) (p : Fin k → ℕ) :
    (∏ i ∈ dIdx r k, p i) * (∏ i ∈ mIdx r k, p i) * (∏ i ∈ nIdx r k, p i) = ∏ i, p i := by
  obtain ⟨hun, hdm, hdn, hmn⟩ := sepIdx_partition r k hr
  rw [← hun, Finset.prod_union (Finset.disjoint_union_left.mpr ⟨hdn, hmn⟩),
    Finset.prod_union hdm]

/-! ### Existence of the separation triple of a squarefree number -/

/-- The prime factors of `l`, listed in *decreasing* order. -/
def canonList (l : ℕ) : List ℕ := l.primeFactorsList.reverse

theorem isPrimeList_canonList (l : ℕ) (hl : l ≠ 0) (hsf : Squarefree l) :
    IsPrimeList l (canonList l).length (canonList l).get := by
  have hnod : (canonList l).Nodup := by
    rw [canonList, List.nodup_reverse]
    exact (Nat.squarefree_iff_nodup_primeFactorsList hl).mp hsf
  have hsortGE : (canonList l).SortedGE := by
    rw [canonList]
    exact (Nat.primeFactorsList_sorted l).reverse
  have hsort : (canonList l).SortedGT := hsortGE.sortedGT_of_nodup hnod
  refine ⟨?_, ?_, ?_⟩
  · exact List.sortedGT_ofFn_iff.mp (by rw [List.ofFn_get]; exact hsort)
  · intro i
    refine Nat.prime_of_mem_primeFactorsList (n := l) ?_
    exact List.mem_reverse.mp (List.get_mem (canonList l) i)
  · rw [← List.prod_ofFn, List.ofFn_get, canonList, List.prod_reverse,
      Nat.prod_primeFactorsList hl]

/-- Every squarefree positive integer has a separation triple with product `l`. -/
theorem exists_isSepPair (r l : ℕ) (hr : 2 ≤ r) (hl : l ≠ 0) (hsf : Squarefree l) :
    ∃ d m n, IsSepPair r d m n ∧ d * m * n = l ∧ 0 < d ∧ 0 < m ∧ 0 < n := by
  have hpl := isPrimeList_canonList l hl hsf
  have hsplit := prod_sepIdx_split r (canonList l).length hr (canonList l).get
  refine ⟨_, _, _, ⟨(canonList l).length, (canonList l).get,
    ⟨hpl.1, hpl.2.1, hsplit⟩, rfl, rfl, rfl⟩, hsplit.trans hpl.2.2.symm, ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun i _ => (hpl.2.1 i).pos
  · exact Finset.prod_pos fun i _ => (hpl.2.1 i).pos
  · exact Finset.prod_pos fun i _ => (hpl.2.1 i).pos

/-! ### The main identity -/

/-- **FI Lemma 24.1 / (24.11)**, in the form in which the paper's §24 uses it: the sum over
squarefree `ℓ ⩽ x` with all prime factors `⩽ z` is the same as the triple sum over separation
triples with `d ⩽ D`. -/
theorem sum_eq_sepPairSum (r x z D : ℕ) (hr : 2 ≤ r) (f : ℕ → ℂ)
    (hsupp : ∀ l, f l ≠ 0 → Squarefree l ∧ l ≤ x ∧ ∀ p, p.Prime → p ∣ l → p ≤ z)
    (hD : ∀ l d m n, Squarefree l → l ≤ x → (∀ p, p.Prime → p ∣ l → p ≤ z) →
            IsSepPair r d m n → d * m * n = l → d ≤ D) :
    sepSumLHS x z f = sepPairSum r D x z f := by
  classical
  rw [sepSumLHS, sepPairSum]
  symm
  have hboxeq : (∑ t ∈ ((Finset.Icc 1 D ×ˢ Finset.Icc 1 x) ×ˢ Finset.Icc 1 x),
        (if IsSepPair r t.1.1 t.1.2 t.2 ∧
              (∀ p, p.Prime → p ∣ t.1.1 * t.1.2 * t.2 → p ≤ z)
            then f (t.1.1 * t.1.2 * t.2) else 0))
      = ∑ d ∈ Finset.Icc 1 D, ∑ m ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x,
          (if IsSepPair r d m n ∧ (∀ p, p.Prime → p ∣ d * m * n → p ≤ z)
            then f (d * m * n) else 0) := by
    rw [Finset.sum_product, Finset.sum_product]
  rw [← hboxeq]
  rw [← Finset.sum_filter]
  have hfilter : (∑ t ∈ (((Finset.Icc 1 D ×ˢ Finset.Icc 1 x) ×ˢ Finset.Icc 1 x)).filter
        (fun t => (IsSepPair r t.1.1 t.1.2 t.2 ∧
            (∀ p, p.Prime → p ∣ t.1.1 * t.1.2 * t.2 → p ≤ z)) ∧
              t.1.1 * t.1.2 * t.2 ≤ x),
        f (t.1.1 * t.1.2 * t.2))
      = ∑ t ∈ (((Finset.Icc 1 D ×ˢ Finset.Icc 1 x) ×ˢ Finset.Icc 1 x)).filter
        (fun t => IsSepPair r t.1.1 t.1.2 t.2 ∧
            (∀ p, p.Prime → p ∣ t.1.1 * t.1.2 * t.2 → p ≤ z)),
        f (t.1.1 * t.1.2 * t.2) := by
    refine Finset.sum_subset ?_ ?_
    · intro t ht
      rw [Finset.mem_filter] at ht ⊢
      exact ⟨ht.1, ht.2.1⟩
    · intro t ht hnt
      rw [Finset.mem_filter] at ht
      have hgt : x < t.1.1 * t.1.2 * t.2 := by
        by_contra hc
        exact hnt (Finset.mem_filter.mpr ⟨ht.1, ht.2, Nat.le_of_not_lt hc⟩)
      by_contra hf
      exact absurd (hsupp (t.1.1 * t.1.2 * t.2) hf).2.1 (not_le.mpr hgt)
  rw [← hfilter]
  have hbij : (∑ t ∈ (((Finset.Icc 1 D ×ˢ Finset.Icc 1 x) ×ˢ Finset.Icc 1 x)).filter
        (fun t => (IsSepPair r t.1.1 t.1.2 t.2 ∧
            (∀ p, p.Prime → p ∣ t.1.1 * t.1.2 * t.2 → p ≤ z)) ∧
              t.1.1 * t.1.2 * t.2 ≤ x),
        f (t.1.1 * t.1.2 * t.2))
      = ∑ l ∈ (Finset.Icc 1 x).filter
          (fun l => Squarefree l ∧ ∀ p, p.Prime → p ∣ l → p ≤ z), f l := by
    refine Finset.sum_bij (fun t _ => t.1.1 * t.1.2 * t.2) ?_ ?_ ?_ ?_
    · rintro ⟨⟨d, m⟩, n⟩ ht
      rw [Finset.mem_filter] at ht
      obtain ⟨-, ⟨hisp, hQ⟩, hle⟩ := ht
      dsimp only at hisp hQ hle
      rw [Finset.mem_filter, Finset.mem_Icc]
      change (1 ≤ d * m * n ∧ d * m * n ≤ x) ∧ (Squarefree (d * m * n) ∧
        ∀ p, p.Prime → p ∣ d * m * n → p ≤ z)
      obtain ⟨hdp, hmp, hnp⟩ := hisp.pos
      have hpos : 0 < d * m * n := by positivity
      exact ⟨⟨by omega, hle⟩, sepPair_squarefree hisp, hQ⟩
    · rintro ⟨⟨d, m⟩, n⟩ ht ⟨⟨d', m'⟩, n'⟩ ht' heq
      rw [Finset.mem_filter] at ht ht'
      obtain ⟨-, ⟨hisp, -⟩, -⟩ := ht
      obtain ⟨-, ⟨hisp', -⟩, -⟩ := ht'
      dsimp only at hisp hisp' heq
      obtain ⟨e1, e2, e3⟩ := sepPair_eq_of_prod_eq hisp hisp' heq
      rw [e1, e2, e3]
    · rintro l hl
      rw [Finset.mem_filter, Finset.mem_Icc] at hl
      obtain ⟨⟨hl1, hlx⟩, hsf, hQ⟩ := hl
      have hl0 : l ≠ 0 := by omega
      obtain ⟨d, m, n, hisp, hdmn, hdp, hmp, hnp⟩ := exists_isSepPair r l hr hl0 hsf
      refine ⟨((d, m), n), ?_, hdmn⟩
      · rw [Finset.mem_filter]
        refine ⟨?_, ⟨hisp, ?_⟩, ?_⟩
        · rw [Finset.mem_product, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc,
            Finset.mem_Icc]
          change ((1 ≤ d ∧ d ≤ D) ∧ (1 ≤ m ∧ m ≤ x)) ∧ (1 ≤ n ∧ n ≤ x)
          have hdD : d ≤ D := hD l d m n hsf hlx hQ hisp hdmn
          have hmx : m ≤ x := by
            have h : m ≤ d * m * n := by
              have h1 : m ≤ m * (d * n) := Nat.le_mul_of_pos_right m (Nat.mul_pos hdp hnp)
              calc m ≤ m * (d * n) := h1
                _ = d * m * n := by ring
            omega
          have hnx : n ≤ x := by
            have h : n ≤ d * m * n := by
              have h1 : n ≤ n * (d * m) := Nat.le_mul_of_pos_right n (Nat.mul_pos hdp hmp)
              calc n ≤ n * (d * m) := h1
                _ = d * m * n := by ring
            omega
          exact ⟨⟨⟨by omega, hdD⟩, ⟨by omega, hmx⟩⟩, ⟨by omega, hnx⟩⟩
        · change ∀ p, p.Prime → p ∣ d * m * n → p ≤ z
          rwa [hdmn]
        · change d * m * n ≤ x
          rwa [hdmn]
    · intro t ht
      rfl
  exact hbij

end Work.FIArea7

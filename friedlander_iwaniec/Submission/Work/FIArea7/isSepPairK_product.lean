/-
# `Submission.Work.FIArea7.isSepPairK_product` — the fixed-`k` separation condition is a product

*FI* §24 splits a sum over squarefree `ℓ ≤ x` into a double sum over `(m,n)` and a small
"separation" divisor `d`, with `ℓ = d·m·n` and `d, m, n` read off from the (decreasing) list of
prime factors of `ℓ` by the interleaved block pattern (24.2), (24.4), (24.5).  The predicate
`IsSepPairK r k d m n` (`Submission/Work/FIArea7/prop172defs.lean`) is the fixed-`k` version.

This file proves that for fixed `r, k, d` the set of admissible `(m,n)` is a *product set*:
there are predicates `A`, `B` on `ℕ` alone with

  `IsSepPairK r k d m n ↔ A m ∧ B n`    for all `m, n`.

This is what turns *FI* (24.11) into a bilinear form in `(m,n)` to which Proposition 23.1 applies.

The index sets `dIdx`, `mIdx`, `nIdx` partition `Fin k` (`sepIdx_partition`).  Since the sets are
interleaved as the word `d…d m…m d n…n d m…m d n…n …`, two *adjacent* positions always lie in
`dIdx ∪ mIdx` or in `dIdx ∪ nIdx` — never one in `mIdx` and the other in `nIdx`
(`mIdx_nIdx_not_adjacent`).  Consequently the whole "the merged list is strictly decreasing"
condition is the conjunction of a condition on `(d,m)` (encoded by `A`) and one on `(d,n)`
(encoded by `B`), and the prime factorisation of `d` over `dIdx` — which is what the two parts
share — is uniquely determined (`primeDecr_prod_inj`), so the two parts glue.
-/
import Mathlib
import Submission.Work.FIArea7.prop172defs
import Submission.Work.FIArea7.primeDecr_prod_inj

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

/-- `f` assigns primes to the positions in `S` in strictly decreasing order of position. -/
def PrimeDecrOn {k : ℕ} (S : Finset (Fin k)) (f : Fin k → ℕ) : Prop :=
  (∀ i ∈ S, (f i).Prime) ∧ ∀ i j : Fin k, i ∈ S → j ∈ S → i < j → f j < f i

/-- On `Fin k` a function that decreases at every adjacent pair is strictly antitone. -/
theorem strictAnti_of_adj {k : ℕ} {f : Fin k → ℕ}
    (h : ∀ i j : Fin k, j.val = i.val + 1 → f j < f i) : StrictAnti f := by
  intro a b hab
  have key : ∀ m : ℕ, ∀ (hm : m < k) (a : Fin k), a.val < m → f ⟨m, hm⟩ < f a := by
    intro m
    induction m with
    | zero => intro hm a ha; exact absurd ha (Nat.not_lt_zero _)
    | succ m ih =>
      intro hm a ha
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ha) with hlt | heq
      · have hstep : f ⟨m + 1, hm⟩ < f ⟨m, by omega⟩ := h ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl
        exact lt_trans hstep (ih (by omega) a hlt)
      · have haeq : a = ⟨m, by omega⟩ := Fin.ext heq
        rw [haeq]
        exact h ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl
  exact key b.val b.isLt a hab

/-- Two adjacent positions of `Fin k` cannot have one in `mIdx` and the other in `nIdx`: between an
`m`-run and an `n`-run there is always a `dIdx` position `j = q·r`. -/
theorem mIdx_nIdx_not_adjacent {r k : ℕ} (hr : 2 ≤ r) {i j : Fin k} (hij : j.val = i.val + 1) :
    (i ∈ mIdx r k → j ∉ nIdx r k) ∧ (i ∈ nIdx r k → j ∉ mIdx r k) := by
  have hr0 : 0 < r := by omega
  have key : ∀ v : ℕ, ((v + 1) / r) % 2 = (v / r) % 2 ∨ (v + 1) % r = 0 := by
    intro v
    have hs := Nat.mod_lt v hr0
    have hv : v = r * (v / r) + v % r := (Nat.div_add_mod v r).symm
    have hv1 : v + 1 = r * (v / r) + (v % r + 1) := by omega
    rcases lt_or_eq_of_le (show v % r + 1 ≤ r by omega) with hlt | heq
    · left
      have hd : (v + 1) / r = v / r := by
        rw [hv1, Nat.mul_add_div hr0 (v / r) (v % r + 1), Nat.div_eq_of_lt hlt, add_zero]
      rw [hd]
    · right
      have hh : r * (v / r) + (v % r + 1) = (v / r + 1) * r := by rw [heq]; ring
      rw [hv1, hh, Nat.mul_mod_left]
  constructor
  · intro hi hj
    rw [mem_mIdx] at hi
    rw [mem_nIdx] at hj
    obtain ⟨hsi, hqi⟩ := hi
    obtain ⟨hsj, hqj, -⟩ := hj
    have hjv : j.val + 1 = (i.val + 1) + 1 := by omega
    rw [hjv] at hsj hqj
    rcases key (i.val + 1) with h | h
    · rw [h] at hqj; omega
    · omega
  · intro hi hj
    rw [mem_nIdx] at hi
    rw [mem_mIdx] at hj
    obtain ⟨hsi, hqi, -⟩ := hi
    obtain ⟨hsj, hqj⟩ := hj
    have hjv : j.val + 1 = (i.val + 1) + 1 := by omega
    rw [hjv] at hsj hqj
    rcases key (i.val + 1) with h | h
    · rw [h] at hqj; omega
    · omega

/-- **The fixed-`k` separation condition is a product of a condition on `m` alone and a condition
on `n` alone** (`r`, `k`, `d` being parameters).  This is what makes the *FI* (24.11) double sum
`Σ_{d ≤ D} Σ_{m,n} f (d m n)` a bilinear form in `(m,n)`: for fixed `d` and `k` the admissible
pairs form a product set `{m | A m} ×ˢ {n | B n}`, so the summand can be written `A m · B n ·
(λ-part)` with `A`, `B` bounded, and *FI* Proposition 23.1 applies.

Reason: `dIdx, mIdx, nIdx` partition `Fin k` (`sepIdx_partition`); a prime list `p : Fin k → ℕ`
with `d = ∏_{dIdx} p` determines `p` on `dIdx` (the primes of `d` in decreasing order), and
likewise `m`, `n` determine `p` on their own index sets.  So `IsSepPairK r k d m n` reduces to: the
counts match and the merged list is strictly decreasing — and every comparison of adjacent merged
positions is between a `dIdx`-position and an `mIdx`- or `nIdx`-position, hence involves only
`(d,m)` or `(d,n)`. -/
theorem isSepPairK_product (r k : ℕ) (hr : 2 ≤ r) (d : ℕ) :
    ∃ A B : ℕ → Prop, ∀ m n : ℕ, IsSepPairK r k d m n ↔ A m ∧ B n := by
  obtain ⟨hcover, hdm, hdn, hmn⟩ := sepIdx_partition r k hr
  refine ⟨fun m => ∃ f : Fin k → ℕ, PrimeDecrOn (dIdx r k ∪ mIdx r k) f ∧
      ∏ i ∈ dIdx r k, f i = d ∧ ∏ i ∈ mIdx r k, f i = m,
    fun n => ∃ g : Fin k → ℕ, PrimeDecrOn (dIdx r k ∪ nIdx r k) g ∧
      ∏ i ∈ dIdx r k, g i = d ∧ ∏ i ∈ nIdx r k, g i = n, ?_⟩
  intro m n
  constructor
  · intro h
    obtain ⟨p, hp, hd, hm, hn⟩ := h
    obtain ⟨hpanti, hpprime, -⟩ := hp
    constructor
    · exact ⟨p, ⟨fun i _ => hpprime i, fun i j _ _ hij => hpanti hij⟩, hd.symm, hm.symm⟩
    · exact ⟨p, ⟨fun i _ => hpprime i, fun i j _ _ hij => hpanti hij⟩, hd.symm, hn.symm⟩
  · rintro ⟨⟨f, hf, hdf, hmf⟩, ⟨g, hg, hdg, hng⟩⟩
    -- The `d`-parts of the two witnesses agree, because over `dIdx` they are both the decreasing
    -- enumeration of the prime factors of `d`.
    have hagree : ∀ i ∈ dIdx r k, f i = g i :=
      primeDecr_prod_inj (dIdx r k)
        (fun i hi => hf.1 i (Finset.mem_union_left _ hi))
        (fun i j hi hj hij =>
          hf.2 i j (Finset.mem_union_left _ hi) (Finset.mem_union_left _ hj) hij)
        (fun i hi => hg.1 i (Finset.mem_union_left _ hi))
        (fun i j hi hj hij =>
          hg.2 i j (Finset.mem_union_left _ hi) (Finset.mem_union_left _ hj) hij)
        (by rw [hdf, hdg])
    let p : Fin k → ℕ := fun i => if i ∈ dIdx r k ∪ mIdx r k then f i else g i
    have hpmem : ∀ i, i ∈ dIdx r k ∪ mIdx r k → p i = f i := by
      intro i hi; simp only [p, if_pos hi]
    have hpnot : ∀ i, i ∉ dIdx r k ∪ mIdx r k → p i = g i := by
      intro i hi; simp only [p, if_neg hi]
    have hpin : ∀ i, i ∉ dIdx r k ∪ mIdx r k → i ∈ nIdx r k := by
      intro i hi
      have hmem : i ∈ dIdx r k ∪ mIdx r k ∪ nIdx r k := by rw [hcover]; exact Finset.mem_univ i
      rcases Finset.mem_union.mp hmem with h' | h'
      · exact absurd h' hi
      · exact h'
    have hpg : ∀ i, i ∈ dIdx r k ∪ nIdx r k → p i = g i := by
      intro i hi
      rcases Finset.mem_union.mp hi with hd | hn
      · rw [hpmem i (Finset.mem_union_left _ hd), hagree i hd]
      · rw [hpnot i (by
          rw [Finset.mem_union, not_or]
          exact ⟨Finset.disjoint_right.mp hdn hn, Finset.disjoint_right.mp hmn hn⟩)]
    have hpprime : ∀ i, (p i).Prime := by
      intro i
      by_cases hi : i ∈ dIdx r k ∪ mIdx r k
      · rw [hpmem i hi]; exact hf.1 i hi
      · rw [hpnot i hi]; exact hg.1 i (Finset.mem_union_right _ (hpin i hi))
    have hpd : ∏ i ∈ dIdx r k, p i = d :=
      (Finset.prod_congr rfl (fun i hi => by rw [hpmem i (Finset.mem_union_left _ hi)])).trans hdf
    have hpm : ∏ i ∈ mIdx r k, p i = m :=
      (Finset.prod_congr rfl (fun i hi => by rw [hpmem i (Finset.mem_union_right _ hi)])).trans hmf
    have hpn : ∏ i ∈ nIdx r k, p i = n :=
      (Finset.prod_congr rfl (fun i hi => by rw [hpg i (Finset.mem_union_right _ hi)])).trans hng
    -- `p` is strictly decreasing: every adjacent pair lies in `dIdx ∪ mIdx` or `dIdx ∪ nIdx`.
    have hpanti : StrictAnti p := by
      refine strictAnti_of_adj (fun i j hij => ?_)
      have hijlt : i < j := by rw [Fin.lt_def]; omega
      by_cases hboth : i ∈ dIdx r k ∪ mIdx r k ∧ j ∈ dIdx r k ∪ mIdx r k
      · rw [hpmem i hboth.1, hpmem j hboth.2]
        exact hf.2 i j hboth.1 hboth.2 hijlt
      · by_cases hi' : i ∈ dIdx r k ∪ mIdx r k
        · have hj' : j ∉ dIdx r k ∪ mIdx r k := fun h => hboth ⟨hi', h⟩
          have hjn : j ∈ nIdx r k := hpin j hj'
          have him : i ∉ mIdx r k := fun him =>
            absurd hjn ((mIdx_nIdx_not_adjacent hr hij).1 him)
          have hid : i ∈ dIdx r k := by
            rcases Finset.mem_union.mp hi' with h | h
            · exact h
            · exact absurd h him
          rw [hpg i (Finset.mem_union_left _ hid), hpg j (Finset.mem_union_right _ hjn)]
          exact hg.2 i j (Finset.mem_union_left _ hid) (Finset.mem_union_right _ hjn) hijlt
        · have hin : i ∈ nIdx r k := hpin i hi'
          have hjm : j ∉ mIdx r k := (mIdx_nIdx_not_adjacent hr hij).2 hin
          have hjn : j ∈ dIdx r k ∪ nIdx r k := by
            have hmem : j ∈ dIdx r k ∪ mIdx r k ∪ nIdx r k := by
              rw [hcover]; exact Finset.mem_univ j
            rcases Finset.mem_union.mp hmem with h | h
            · rcases Finset.mem_union.mp h with hd | hm
              · exact Finset.mem_union_left _ hd
              · exact absurd hm hjm
            · exact Finset.mem_union_right _ h
          rw [hpg i (Finset.mem_union_right _ hin), hpg j hjn]
          exact hg.2 i j (Finset.mem_union_right _ hin) hjn hijlt
    refine ⟨p, ⟨hpanti, hpprime, ?_⟩, hpd.symm, hpm.symm, hpn.symm⟩
    have huniv : ∏ i ∈ dIdx r k ∪ mIdx r k ∪ nIdx r k, p i = ∏ i : Fin k, p i := by rw [hcover]
    rw [← huniv, Finset.prod_union ((Finset.disjoint_union_left).mpr ⟨hdn, hmn⟩),
      Finset.prod_union hdm, hpd, hpm, hpn]

end Work.FIArea7

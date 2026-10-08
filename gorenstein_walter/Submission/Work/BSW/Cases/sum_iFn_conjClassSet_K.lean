/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Area BSW: the `i`-sum over the TI-saturation of `K`

Bender, *The Brauer–Suzuki–Wall theorem*, Illinois J. Math. **18** (1974) 229–235, §3
(opening paragraph): with `K# = K ∖ {1}` the TI-subset of `K` (`Work.BSW.Char.isTISubset_Kdiff`,
bound `L = C_G(t)`) and `I = |G : C_G(t)| = |involutions of G|`
(`Work.BSW.Api.ncard_involutions_eq_index`), the conjugacy saturation `𝒞_G(K) = K^G = H^G`
carries exactly

  `∑_{x ∈ 𝒞_G(K)} i(x) = I + I·∑_{a ∈ K#} i(a) = I(k² − k + 2)`,  `k = |K|`,

in the *inclusive* convention of `Work.BSW.iFn` (Bender's own `i` omits `u = x` on involutions).
The second factor is Bender's count on the pieces of `K#`: `i(t) = k + 1`
(`Work.BSW.Char.iFn_t`) and `i(a) = k` for the remaining `k − 2` elements
(`Work.BSW.Char.iFn_eq_card_of_mem_K`), so `∑_{a ∈ K#} i(a) = (k+1) + (k−2)k`.

The transport over the saturation is the disjoint-union count for a TI-subset,
`OddOrder.GroupTheory.IsTISubset.sum_conjClassSet` (the weighted refinement of
`|A^G| = |A|·[G:L]`): the conjugates `g·K#·g⁻¹` indexed by the cosets `gL` are pairwise
disjoint, each contributing the same sum because `i` is conjugation invariant.
-/
import Mathlib
import Submission.OddOrder.GroupTheory.TISubsetCounting
import Submission.Work.BSW.Char.isTISubset_Kdiff
import Submission.Work.BSW.Char.iFn_t
import Submission.Work.BSW.Char.iFn_eq_card_of_mem_K
import Submission.Work.BSW.Char.coset_sK_involutions
import Submission.Work.BSW.Api.ncard_involutions_eq_index
import Submission.Work.BSW.Api.normalizer_K_eq
import Submission.Work.BSW.Cases.bswCompletionBase

open scoped BigOperators Pointwise

namespace Work.BSW.Cases

open Subgroup Work.GW2

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}

/-- The elements of `C_G(t) = K⟨s⟩` normalize `K` (`Work.BSW.Api.centralizer_t_le_normalizer`),
so conjugation by them preserves `K# = K ∖ {1}`.  This is the stability hypothesis required by
the TI-subset sum `OddOrder.GroupTheory.IsTISubset.sum_conjClassSet`. -/
theorem conj_smul_sdiff_one (h : BSWHyps2 G t s K) {l : G}
    (hl : l ∈ Subgroup.centralizer ({t} : Set G)) :
    MulAut.conj l • ((K : Set G) \ {1}) = (K : Set G) \ {1} := by
  have hnorm : l ∈ Subgroup.normalizer (K : Set G) :=
    Work.BSW.Api.centralizer_t_le_normalizer h hl
  have hK : MulAut.conj l • (K : Set G) = (K : Set G) := by
    rw [show (MulAut.conj l • (K : Set G)) = ⇑(MulAut.conj l) '' (K : Set G) from rfl,
      ← show Work.GW2.conjSub l K = ⇑(MulAut.conj l) '' (K : Set G) from rfl,
      Work.BSW.Api.conjSub_eq_of_mem_normalizer hnorm]
  rw [Set.smul_set_sdiff, hK, Set.smul_set_singleton, MulAut.smul_def, map_one]

/-- The saturation `𝒞_G(K)` is the union of `{1}` and the saturation of `K#`: every conjugate of
an element of `K` is either `1` (the conjugate of `1`) or lies in `𝒞_G(K#)`. -/
theorem conjClassSet_K_eq_insert_one_sdiff (h : BSWHyps2 G t s K) :
    OddOrder.GroupTheory.conjClassSet (K : Set G)
      = insert (1 : G) (OddOrder.GroupTheory.conjClassSet ((K : Set G) \ {1})) := by
  ext y
  rw [OddOrder.GroupTheory.mem_conjClassSet, Set.mem_insert_iff,
    OddOrder.GroupTheory.mem_conjClassSet]
  constructor
  · rintro ⟨k, hk, g, hg⟩
    by_cases hk1 : k = 1
    · exact Or.inl (by rw [← hg, hk1]; simp)
    · exact Or.inr ⟨k, ⟨hk, hk1⟩, g, hg⟩
  · rintro (rfl | ⟨k, ⟨hk, hk1⟩, g, hg⟩)
    · exact ⟨1, K.one_mem, 1, by simp⟩
    · exact ⟨k, hk, g, hg⟩

/-- The Finset split of the saturation of a subgroup containing `1`: summing over `𝒞_G(K)` is
summing over `𝒞_G(K#)` (whose elements are conjugates of elements `≠ 1`) and then adding the term
at the fixed point `1`. -/
theorem sum_conjClassSet_K_eq_one_add (h : BSWHyps2 G t s K) {M : Type*} [AddCommMonoid M]
    (f : G → M) :
    ∑ x ∈ (Set.toFinite (OddOrder.GroupTheory.conjClassSet (K : Set G))).toFinset, f x
      = f 1
        + ∑ x ∈ (Set.toFinite
            (OddOrder.GroupTheory.conjClassSet ((K : Set G) \ {1}))).toFinset, f x := by
  classical
  have hfin : (Set.toFinite (OddOrder.GroupTheory.conjClassSet (K : Set G))).toFinset
      = insert (1 : G) (Set.toFinite
          (OddOrder.GroupTheory.conjClassSet ((K : Set G) \ {1}))).toFinset := by
    ext x
    rw [Set.Finite.mem_toFinset, conjClassSet_K_eq_insert_one_sdiff h, Set.mem_insert_iff,
      Finset.mem_insert, Set.Finite.mem_toFinset]
  have h1 : (1 : G) ∉ (Set.toFinite
      (OddOrder.GroupTheory.conjClassSet ((K : Set G) \ {1}))).toFinset := by
    rw [Set.Finite.mem_toFinset, OddOrder.GroupTheory.mem_conjClassSet]
    rintro ⟨k, ⟨_, hk1⟩, g, hg⟩
    refine hk1 ?_
    have h2 : k = g⁻¹ * (g * k * g⁻¹) * g := by group
    rw [h2, hg]; simp
  rw [hfin, Finset.sum_insert h1]

/-- Bender's count on `K#`: `i(t) = |K| + 1` for the involution `t` of `K`, and `i` takes the
constant value `|K|` on the remaining `|K| − 2` elements, so

  `∑_{a ∈ K#} i(a) = (|K| + 1) + (|K| − 2)·|K|`. -/
theorem sum_iFn_sdiff_one_K (h : BSWHyps2 G t s K) :
    ∑ x ∈ (Set.toFinite ((K : Set G) \ {1})).toFinset, (Work.BSW.iFn G x : ℤ)
      = (Nat.card ↥K : ℤ) + 1 + ((Nat.card ↥K : ℤ) - 2) * (Nat.card ↥K : ℤ) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  set FK : Finset G := Finset.univ.filter (fun x : G => x ∈ K) with hFK
  have hmem : ∀ x : G, x ∈ FK ↔ x ∈ K := by
    intro x; rw [hFK, Finset.mem_filter]; simp
  have hcard : FK.card = Nat.card ↥K := by
    rw [hFK, ← Fintype.card_subtype (fun x : G => x ∈ K), ← Nat.card_eq_fintype_card]
  have hfin : (Set.toFinite ((K : Set G) \ {1})).toFinset = FK.erase 1 := by
    ext x
    rw [Set.Finite.mem_toFinset, Finset.mem_erase, hmem]
    simp only [Set.mem_sdiff, Set.mem_singleton_iff]
    tauto
  rw [hfin]
  have h1 : (1 : G) ∈ FK := (hmem 1).mpr K.one_mem
  have ht : t ∈ FK := (hmem t).mpr (Work.BSW.t_mem_K h)
  have htne : t ≠ (1 : G) := Work.BSW.t_ne_one h
  have h2le : 2 ≤ Nat.card ↥K := by
    rw [← hcard]
    have hsub : ({(1 : G), t} : Finset G) ⊆ FK := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx1 | hxt
      · rw [hx1]; exact h1
      · rw [hxt]; exact ht
    have hc := Finset.card_le_card hsub
    rwa [Finset.card_pair htne.symm] at hc
  have htmem : t ∈ FK.erase 1 := by
    rw [Finset.mem_erase]; exact ⟨htne, ht⟩
  have hsplit : ∑ x ∈ FK.erase 1, (Work.BSW.iFn G x : ℤ)
      = (Work.BSW.iFn G t : ℤ) + ∑ x ∈ (FK.erase 1).erase t, (Work.BSW.iFn G x : ℤ) := by
    rw [← Finset.sum_erase_add (FK.erase 1) (fun x => (Work.BSW.iFn G x : ℤ)) htmem,
      add_comm]
  have hrest : ∑ x ∈ (FK.erase 1).erase t, (Work.BSW.iFn G x : ℤ)
      = (((FK.erase 1).erase t).card : ℤ) * (Nat.card ↥K : ℤ) := by
    trans ∑ x ∈ (FK.erase 1).erase t, (Nat.card ↥K : ℤ)
    · refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [Finset.mem_erase, Finset.mem_erase] at hx
      obtain ⟨hxt, hx1, hxK⟩ := hx
      rw [Work.BSW.Char.iFn_eq_card_of_mem_K h ((hmem x).mp hxK) hx1 hxt]
    · rw [Finset.sum_const, nsmul_eq_mul]
  have hcard2' : ((FK.erase 1).erase t).card = Nat.card ↥K - 2 := by
    rw [Finset.card_erase_of_mem htmem, Finset.card_erase_of_mem h1, hcard]
    omega
  have hcard2 : (((FK.erase 1).erase t).card : ℤ) = (Nat.card ↥K : ℤ) - 2 := by
    rw [hcard2', Nat.cast_sub h2le]
    norm_num
  rw [hsplit, hrest, hcard2, Work.BSW.Char.iFn_t h]
  push_cast
  ring

/-- The index of `C_G(t)` is the number of involutions of `G`
(`Work.BSW.Api.ncard_involutions_eq_index`). -/
theorem index_centralizer_eq_invCount (h : BSWHyps2 G t s K) :
    (Subgroup.centralizer ({t} : Set G)).index = Work.BSW.invCount G := by
  rw [← Work.BSW.Api.ncard_involutions_eq_index h]
  rfl

/-- **The `i`-sum over the conjugacy saturation of `K`** (Bender 1974, §3, p. 232):

  `∑_{x ∈ K^G} i(x) = I·(k² − k + 1) + I`,  `I = |involutions of G| = |G : C_G(t)|`,
  `k = |K|`,

in the inclusive convention of `Work.BSW.iFn`.  Equivalently `∑_{x ∈ H^G} i(x) = I(k² − k + 2)`
for Bender's `i` (the number of involutions `≠ x` inverting `x`). -/
theorem sum_iFn_conjClassSet_K {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) :
    ∑ x ∈ (Set.toFinite (OddOrder.GroupTheory.conjClassSet (K : Set G))).toFinset,
        (Work.BSW.iFn G x : ℤ)
      = (Work.BSW.invCount G : ℤ) * ((Nat.card ↥K : ℤ) ^ 2 - (Nat.card ↥K : ℤ) + 1)
        + (Work.BSW.invCount G : ℤ) := by
  classical
  -- The saturation of `K#` is the disjoint union of the `[G : C_G(t)]` conjugates of `K#`, each
  -- contributing the same sum because `i` is conjugation invariant.
  have htisub := (Work.BSW.Char.isTISubset_Kdiff h).sum_conjClassSet
    (fun x => (Work.BSW.iFn G x : ℤ))
    (fun l hl => conj_smul_sdiff_one h hl)
    (fun g x => by rw [Work.BSW.Cases.iFn_conj g x])
  rw [nsmul_eq_mul, index_centralizer_eq_invCount h] at htisub
  -- Split off the trivial class, evaluate `i(1)` and the sum on `K#`, then close by arithmetic.
  rw [sum_conjClassSet_K_eq_one_add h (fun x => (Work.BSW.iFn G x : ℤ)), htisub,
    sum_iFn_sdiff_one_K h]
  simp only [Work.BSW.iFn_one]
  ring

end Work.BSW.Cases

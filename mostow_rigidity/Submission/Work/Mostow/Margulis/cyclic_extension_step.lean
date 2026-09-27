import Mathlib
import Submission.Work.Mostow.Margulis.finiteIndex_subgroupOf_sup_zpowers
import Submission.Work.Mostow.Margulis.exists_pow_conj_mem_sup

set_option linter.style.haveILetI false

namespace Work.Mostow.Margulis

open Subgroup
open scoped commutatorElement

/-- Any subgroup `M` with `N ≤ M ≤ A`, where `⁅⊤, A⁆ ≤ N`, is normal in `G`: for `m ∈ M ≤ A`,
`g * m * g⁻¹ = ⁅g, m⁆ * m` with `⁅g, m⁆ ∈ ⁅⊤, A⁆ ≤ N ≤ M`. -/
lemma normal_of_commutator_le {G : Type*} [Group G] {A N M : Subgroup G}
    (hNM : N ≤ M) (hMA : M ≤ A) (hcen : ⁅(⊤ : Subgroup G), A⁆ ≤ N) : M.Normal :=
  ⟨fun m hm g => by
    have h1 : ⁅g, m⁆ ∈ ⁅(⊤ : Subgroup G), A⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (hMA hm)
    have h2 : ⁅g, m⁆ ∈ N := hcen h1
    have heq : g * m * g⁻¹ = ⁅g, m⁆ * m := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact M.mul_mem (hNM h2) hm⟩

/-- If `K` is normal and conjugation by every `g` sends `x` into `K ⊔ ⟨x⟩`, then `K ⊔ ⟨x⟩` is
normal. -/
lemma normal_sup_zpowers_of_conj_mem {G : Type*} [Group G] {K : Subgroup G} (hK : K.Normal)
    {x : G} (hx : ∀ g : G, g * x * g⁻¹ ∈ K ⊔ Subgroup.zpowers x) :
    (K ⊔ Subgroup.zpowers x).Normal :=
  ⟨fun n hn g => by
    haveI : K.Normal := hK
    obtain ⟨k, hk, z, hz, hkz⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := K) (t := Subgroup.zpowers x)).mp hn
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hz
    have h1 : g * k * g⁻¹ ∈ K ⊔ Subgroup.zpowers x := Subgroup.mem_sup_left (hK.conj_mem k hk g)
    have h2 : (g * x * g⁻¹) ^ j ∈ K ⊔ Subgroup.zpowers x := Subgroup.zpow_mem _ (hx g) j
    have heq : g * n * g⁻¹ = (g * k * g⁻¹) * (g * x * g⁻¹) ^ j := by
      rw [← hkz, ← hj, conj_zpow]; group
    rw [heq]
    exact mul_mem h1 h2⟩

theorem cyclic_extension_step {G : Type*} [Group G] (A N K : Subgroup G) (x : G)
    (hN : N.Normal) (hA : A.Normal) (hK : K.Normal) (hKN : K ≤ N) (hNA : N ≤ A)
    (hcen : ⁅(⊤ : Subgroup G), A⁆ ≤ N) (hgen : A = N ⊔ Subgroup.zpowers x)
    (htf : ∀ y ∈ K, IsOfFinOrder y → y = 1) (hidx : (K.subgroupOf N).FiniteIndex) :
    ∃ K' : Subgroup G, K'.Normal ∧ K' ≤ A ∧ (∀ y ∈ K', IsOfFinOrder y → y = 1) ∧
      (K'.subgroupOf A).FiniteIndex := by
  have hxA : x ∈ A := by
    rw [hgen]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  by_cases hfin : ∃ d : ℕ, 0 < d ∧ x ^ d ∈ N
  · -- Case 1: `x` has finite order modulo `N`; take `K' = K`.
    obtain ⟨d, hd, hxd⟩ := hfin
    refine ⟨K, hK, le_trans hKN hNA, htf, ?_⟩
    haveI h1 : N.IsFiniteRelIndex A :=
      Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr
        (finiteIndex_subgroupOf_sup_zpowers hNA hN hxA hgen hd hxd)
    haveI h2 : K.IsFiniteRelIndex N :=
      Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr hidx
    haveI h3 : K.IsFiniteRelIndex A := h2.trans h1
    exact h3.to_finiteIndex_subgroupOf
  · -- Case 2: `x` has infinite order modulo `N`.
    have hzero : ∀ t : ℤ, x ^ t ∈ N → t = 0 := by
      intro t ht
      rcases lt_trichotomy t 0 with hlt | heq | hgt
      · exfalso
        have hpos : 0 < (-t).toNat := by omega
        have hmem : x ^ ((-t).toNat : ℕ) ∈ N := by
          have h1 : x ^ ((-t).toNat : ℕ) = (x ^ t)⁻¹ := by
            rw [← zpow_natCast, Int.toNat_of_nonneg (show (0:ℤ) ≤ -t by omega), zpow_neg]
          rw [h1]; exact N.inv_mem ht
        exact hfin ⟨(-t).toNat, hpos, hmem⟩
      · exact heq
      · exfalso
        have hpos : 0 < t.toNat := by omega
        have hmem : x ^ (t.toNat : ℕ) ∈ N := by
          have h1 : x ^ (t.toNat : ℕ) = x ^ t := by
            rw [← zpow_natCast, Int.toNat_of_nonneg (show (0:ℤ) ≤ t by omega)]
          rw [h1]; exact ht
        exact hfin ⟨t.toNat, hpos, hmem⟩
    have hxcomm : ∀ g : G, g * x * g⁻¹ * x⁻¹ ∈ N := by
      intro g
      have hmem : ⁅g, x⁆ ∈ ⁅(⊤ : Subgroup G), A⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hxA
      simpa [commutatorElement_def] using hcen hmem
    obtain ⟨m, hmpos, hmconj⟩ := exists_pow_conj_mem_sup K N hKN hK hN hidx hxcomm
    refine ⟨K ⊔ Subgroup.zpowers (x ^ m), ?_, ?_, ?_, ?_⟩
    · exact normal_sup_zpowers_of_conj_mem hK hmconj
    · exact sup_le (le_trans hKN hNA) (Subgroup.zpowers_le.mpr (A.pow_mem hxA m))
    · intro y hy hfo
      haveI : K.Normal := hK
      obtain ⟨k, hk, z, hz, hkz⟩ :=
        (Subgroup.mem_sup_of_normal_left (s := K) (t := Subgroup.zpowers (x ^ m))).mp hy
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hy_eq : y = k * (x ^ m) ^ j := by rw [← hkz, hj]
      have hconv : (x ^ m) ^ j = x ^ (m * j) := by rw [← zpow_natCast, ← zpow_mul]
      have hj0 : j = 0 := by
        obtain ⟨n, hnpos, hyn⟩ := isOfFinOrder_iff_pow_eq_one.mp hfo
        have hk1 : (QuotientGroup.mk' N) k = 1 :=
          (QuotientGroup.eq_one_iff k).mpr (hKN hk)
        have h1 : (QuotientGroup.mk' N) y = (QuotientGroup.mk' N) (x ^ (m * j)) := by
          rw [hy_eq, hconv, map_mul, hk1, one_mul]
        have h2 : ((QuotientGroup.mk' N) (x ^ (m * j))) ^ n = 1 := by
          rw [← h1, ← map_pow, hyn, map_one]
        have h3 : (QuotientGroup.mk' N) (x ^ (m * j * (n : ℤ))) = 1 := by
          rw [zpow_mul, zpow_natCast, map_pow]; exact h2
        have hkey : x ^ (m * j * (n : ℤ)) ∈ N := (QuotientGroup.eq_one_iff _).mp h3
        have hz0 := hzero _ hkey
        have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hmpos.ne'
        have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hnpos.ne'
        have h1 : (m : ℤ) * j = 0 := (mul_eq_zero.mp hz0).resolve_right hn0
        exact (mul_eq_zero.mp h1).resolve_left hm0
      have hyk : y = k := by rw [hy_eq, hj0, zpow_zero, mul_one]
      rw [hyk]
      exact htf k hk (hyk ▸ hfo)
    · haveI hA1n : (N ⊔ Subgroup.zpowers (x ^ m)).Normal :=
        normal_of_commutator_le le_sup_left
          (sup_le hNA (Subgroup.zpowers_le.mpr (A.pow_mem hxA m))) hcen
      haveI hK'n : (K ⊔ Subgroup.zpowers (x ^ m)).Normal :=
        normal_sup_zpowers_of_conj_mem hK hmconj
      have hgenA : A = (N ⊔ Subgroup.zpowers (x ^ m)) ⊔ Subgroup.zpowers x := by
        rw [hgen, sup_assoc,
          sup_eq_right.mpr (Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers x m))]
      have hA1_le : N ⊔ Subgroup.zpowers (x ^ m) ≤ A :=
        sup_le hNA (Subgroup.zpowers_le.mpr (A.pow_mem hxA m))
      have hA1A : ((N ⊔ Subgroup.zpowers (x ^ m)).subgroupOf A).FiniteIndex :=
        finiteIndex_subgroupOf_sup_zpowers (H := N ⊔ Subgroup.zpowers (x ^ m)) (K := A)
          hA1_le hA1n hxA hgenA hmpos
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers (x ^ m)))
      haveI h21 : (N ⊔ Subgroup.zpowers (x ^ m)).IsFiniteRelIndex A :=
        Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr hA1A
      have hK'inN : (K ⊔ Subgroup.zpowers (x ^ m)) ⊓ N = K := by
        refine le_antisymm ?_ ?_
        · intro y hy
          obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
          haveI : K.Normal := hK
          obtain ⟨k, hk, z, hz, hkz⟩ :=
            (Subgroup.mem_sup_of_normal_left (s := K) (t := Subgroup.zpowers (x ^ m))).mp hy1
          obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hz
          have hxmem : x ^ (m * j) ∈ N := by
            have hconv : (x ^ m) ^ j = x ^ (m * j) := by rw [← zpow_natCast, ← zpow_mul]
            rw [← hconv]
            rw [show (x ^ m) ^ j = k⁻¹ * y by rw [← hkz, ← hj]; group]
            exact N.mul_mem (N.inv_mem (hKN hk)) hy2
          have hz0 := hzero _ hxmem
          have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hmpos.ne'
          have hj0 : j = 0 := (mul_eq_zero.mp hz0).resolve_left hm0
          rw [← hkz, ← hj, hj0, zpow_zero, mul_one]
          exact hk
        · intro y hy
          exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hy, hKN hy⟩
      haveI h2' : K.IsFiniteRelIndex N := Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr hidx
      have h22 : (K ⊔ Subgroup.zpowers (x ^ m)).IsFiniteRelIndex (N ⊔ Subgroup.zpowers (x ^ m)) := by
        refine ⟨?_⟩
        have hsup : N ⊔ Subgroup.zpowers (x ^ m) = N ⊔ (K ⊔ Subgroup.zpowers (x ^ m)) := by
          rw [← sup_assoc, sup_eq_left.mpr hKN]
        rw [hsup, Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_right, hK'inN]
        exact Subgroup.relIndex_ne_zero
      haveI h23 : (K ⊔ Subgroup.zpowers (x ^ m)).IsFiniteRelIndex A := h22.trans h21
      exact h23.to_finiteIndex_subgroupOf

end Work.Mostow.Margulis

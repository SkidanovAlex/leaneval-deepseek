/-
Gorenstein–Walter / Bender–Glauberman, area BG: the leaf `IndexOddProp` of BG Theorem A.

`Work.GW2.C16.IndexOddProp` says that for a `BGData G` (Bender–Glauberman Hypothesis 1.1)
the number `|G : H|` of conjugates of the involution `t` is odd and that `k > 0`.

The mathematical content of the oddness is that `t` is *central* in a Sylow 2-subgroup `S`
of `G`:  `S₀ = ⟨t₁t₂⟩` is cyclic of index two in `S` and contains `t`, `t₁` lies in `S ∖ S₀`
and is an involution, so `t₁` inverts `t₁t₂` and hence inverts every element of `S₀ = ⟨t₁t₂⟩`,
in particular the involution `t`; thus `t₁` commutes with `t`, `S₀` commutes with `t` (cyclic),
and `S = S₀ ⊔ ⟨t₁⟩`.  Hence `S ≤ H` and `H.index ∣ S.index`, which is odd because
`Sylow.not_dvd_index` says the index of a Sylow `2`-subgroup is not even.
The second component is `k = |H : C_H(t₁)| + |H : C_H(t₂)| ≥ 2 > 0`.

The three auxiliary lemmas are general group theory (no dihedral hypothesis is used).
-/
import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.GLUE.Defs

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

/-- If `H ≤ K` has index two in `K`, and `a ∈ K ∖ H`, then `K = H ⊔ ⟨a⟩`.  (A subgroup of
index two is maximal.) -/
lemma sup_zpowers_eq_of_relIndex_eq_two {G : Type*} [Group G] {H K : Subgroup G} {a : G}
    (hH : H ≤ K) (hidx : H.relIndex K = 2) (ha : a ∈ K) (hna : a ∉ H) :
    H ⊔ Subgroup.zpowers a = K := by
  have hLK : H ⊔ Subgroup.zpowers a ≤ K := sup_le hH (Subgroup.zpowers_le.mpr ha)
  have hne : H.relIndex (H ⊔ Subgroup.zpowers a) ≠ 1 := by
    intro h1
    refine hna (Subgroup.relIndex_eq_one.mp h1 ?_)
    exact (le_sup_right : Subgroup.zpowers a ≤ H ⊔ Subgroup.zpowers a) (Subgroup.mem_zpowers a)
  have hmul := Subgroup.relIndex_mul_relIndex H (H ⊔ Subgroup.zpowers a) K le_sup_left hLK
  rw [hidx] at hmul
  have hdvd : H.relIndex (H ⊔ Subgroup.zpowers a) ∣ 2 := ⟨_, hmul.symm⟩
  have h2 : H.relIndex (H ⊔ Subgroup.zpowers a) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  refine le_antisymm hLK ?_
  rw [← Subgroup.relIndex_eq_one]
  rw [h2, mul_comm] at hmul
  omega

/-- If `a` and `b` are involutions and `c` is an involution in `⟨ab⟩`, then `a` commutes with
`c`.  Indeed `a (ab) a⁻¹ = (ab)⁻¹`, so `a` inverts every element of `⟨ab⟩`, in particular the
involution `c`, which is therefore fixed. -/
lemma commute_of_mem_zpowers_mul {G : Type*} [Group G] {a b c : G}
    (ha : a * a = 1) (hb : b * b = 1)
    (hc : c ∈ Subgroup.zpowers (a * b)) (hc2 : c * c = 1) : a * c = c * a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hu : MulAut.conj a (a * b) = (a * b)⁻¹ := by
    rw [MulAut.conj_apply, mul_inv_rev, hainv, hbinv,
      show a * (a * b) * a = a * a * b * a by group, ha, one_mul]
  have hconj : MulAut.conj a ((a * b) ^ k) = ((a * b) ^ k)⁻¹ := by
    rw [map_zpow, hu, inv_zpow]
  have h1 : a * (a * b) ^ k * a⁻¹ = (a * b) ^ k := by
    rw [← MulAut.conj_apply, hconj]
    exact inv_eq_of_mul_eq_one_right hc2
  calc a * (a * b) ^ k = a * (a * b) ^ k * 1 := by rw [mul_one]
    _ = a * (a * b) ^ k * (a⁻¹ * a) := by rw [inv_mul_cancel]
    _ = (a * (a * b) ^ k * a⁻¹) * a := by group
    _ = (a * b) ^ k * a := by rw [h1]

/-- Two elements of a cyclic subgroup commute. -/
lemma commute_of_mem_zpowers {G : Type*} [Group G] {u a b : G}
    (ha : a ∈ Subgroup.zpowers u) (hb : b ∈ Subgroup.zpowers u) : a * b = b * a := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← zpow_add, ← zpow_add, add_comm]

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem indexOdd : Work.GW2.C16.IndexOddProp := by
  intro G _ _ D
  have ht_sq : D.t * D.t = 1 := by
    have h := pow_orderOf_eq_one D.t
    rw [D.t_order] at h
    simpa [pow_two] using h
  have ht1_sq : D.t1 * D.t1 = 1 := by
    have h := pow_orderOf_eq_one D.t1
    rw [D.t1_order] at h
    simpa [pow_two] using h
  have ht2_sq : D.t2 * D.t2 = 1 := by
    have h := pow_orderOf_eq_one D.t2
    rw [D.t2_order] at h
    simpa [pow_two] using h
  -- `t` and `t₁` are involutions with `t ∈ ⟨t₁t₂⟩`
  have ht_mem : D.t ∈ Subgroup.zpowers (D.t1 * D.t2) := by
    rw [← D.gen]
    exact D.t_mem
  have hcomm1 : D.t1 * D.t = D.t * D.t1 :=
    commute_of_mem_zpowers_mul ht1_sq ht2_sq ht_mem ht_sq
  -- `S₀ = ⟨t₁t₂⟩` is cyclic, so it centralizes `t`
  have hS0C : D.S0 ≤ Subgroup.centralizer ({D.t} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain rfl := Set.mem_singleton_iff.mp hh
    have hsu : s ∈ Subgroup.zpowers (D.t1 * D.t2) := by
      rw [← D.gen]
      exact hs
    exact (commute_of_mem_zpowers hsu ht_mem).symm
  -- `S = S₀ ⊔ ⟨t₁⟩`
  have hSup : D.S0 ⊔ Subgroup.zpowers D.t1 = (D.S : Subgroup G) :=
    sup_zpowers_eq_of_relIndex_eq_two D.S0_le D.S0_index D.t1_mem D.t1_nmem
  -- hence `t` is central in `S`
  have hS_le_H : (D.S : Subgroup G) ≤ D.H := by
    rw [← hSup]
    refine sup_le hS0C ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm1
  constructor
  · have hoddS : Odd (D.S : Subgroup G).index := by
      have h : ¬ 2 ∣ (D.S : Subgroup G).index := D.S.not_dvd_index
      exact Nat.not_even_iff_odd.mp (by rw [even_iff_two_dvd]; exact h)
    exact Odd.of_dvd_nat hoddS (Subgroup.index_dvd_of_le hS_le_H)
  · have h1 : 0 < (Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H := by
      rw [Subgroup.relIndex]
      exact Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero)
    have h2 : 0 < (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H := by
      rw [Subgroup.relIndex]
      exact Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero)
    unfold BGData.k
    omega

end Work.BG

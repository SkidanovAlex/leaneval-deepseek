import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-- In a cyclic group, two subgroups with the same finite index are equal. -/
theorem cyclic_subgroup_eq_of_index_eq {C : Type*} [Group C] [IsCyclic C]
    {A B : Subgroup C} (h : A.index = B.index) (h0 : A.index ≠ 0) : A = B := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  have key : ∀ (H : Subgroup C), H.index = A.index → H = Subgroup.zpowers (g ^ A.index) := by
    intro H hH
    have hd : A.index ≠ 0 := h0
    have hmem : g ^ A.index ∈ H := by
      have hgen : ∀ y : C ⧸ H, y ∈ Subgroup.zpowers (QuotientGroup.mk' H g) := by
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H y
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
        exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [← map_zpow, hn]⟩
      have hord : orderOf (QuotientGroup.mk' H g) = A.index := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hgen, ← Subgroup.index_eq_card H, hH]
      have hdiv : orderOf (QuotientGroup.mk' H g) ∣ A.index := hord.symm ▸ dvd_rfl
      have hpow : (QuotientGroup.mk' H g) ^ A.index = 1 := orderOf_dvd_iff_pow_eq_one.mp hdiv
      rw [← map_pow, QuotientGroup.mk'_apply] at hpow
      exact (QuotientGroup.eq_one_iff (g ^ A.index)).mp hpow
    have hsub : Subgroup.zpowers (g ^ A.index) ≤ H := Subgroup.zpowers_le_of_mem hmem
    have hdvd : (Subgroup.zpowers (g ^ A.index)).index ∣ A.index := by
      have hgen : ∀ y : C ⧸ Subgroup.zpowers (g ^ A.index),
          y ∈ Subgroup.zpowers (QuotientGroup.mk' (Subgroup.zpowers (g ^ A.index)) g) := by
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
        exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [← map_zpow, hn]⟩
      have hord : orderOf (QuotientGroup.mk' (Subgroup.zpowers (g ^ A.index)) g)
          = (Subgroup.zpowers (g ^ A.index)).index := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hgen,
          ← Subgroup.index_eq_card (Subgroup.zpowers (g ^ A.index))]
      have hpow : (QuotientGroup.mk' (Subgroup.zpowers (g ^ A.index)) g) ^ A.index = 1 := by
        rw [← map_pow, QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff (g ^ A.index)).mpr (Subgroup.mem_zpowers (g ^ A.index))
      have hdiv : orderOf (QuotientGroup.mk' (Subgroup.zpowers (g ^ A.index)) g) ∣ A.index :=
        orderOf_dvd_iff_pow_eq_one.mpr hpow
      rwa [hord] at hdiv
    have h1 : (Subgroup.zpowers (g ^ A.index)).relIndex H * H.index
        = (Subgroup.zpowers (g ^ A.index)).index := Subgroup.relIndex_mul_index hsub
    rw [hH] at h1
    have hidx : (Subgroup.zpowers (g ^ A.index)).index = A.index := by
      refine Nat.dvd_antisymm hdvd ?_
      rw [← h1]
      exact Nat.dvd_mul_left _ _
    have hr1 : (Subgroup.zpowers (g ^ A.index)).relIndex H = 1 := by
      have h2 : (Subgroup.zpowers (g ^ A.index)).relIndex H * A.index = 1 * A.index := by
        rw [one_mul, h1, hidx]
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hd) h2
    have hle : H ≤ Subgroup.zpowers (g ^ A.index) := Subgroup.relIndex_eq_one.mp hr1
    exact le_antisymm hle hsub
  rw [key A rfl, key B h.symm]

theorem subgroup_eq_of_index_eq_of_isProCyclicQuotients {Q : Type*} [Group Q]
    (hQ : ∀ (N : Subgroup Q) [N.Normal], N.FiniteIndex → IsCyclic (Q ⧸ N))
    {K K' : Subgroup Q} (h : K.index = K'.index) (h0 : K.index ≠ 0) : K = K' := by
  have hK' : K'.index ≠ 0 := by rw [← h]; exact h0
  have hinf : (K ⊓ K').FiniteIndex := ⟨Subgroup.index_inf_ne_zero h0 hK'⟩
  let N : Subgroup Q := (K ⊓ K').normalCore
  have hNle : N ≤ K ⊓ K' := Subgroup.normalCore_le _
  haveI : N.Normal := Subgroup.normalCore_normal _
  have hNfin : N.FiniteIndex := Subgroup.finiteIndex_normalCore (K ⊓ K')
  haveI : IsCyclic (Q ⧸ N) := hQ N hNfin
  let f : Q →* Q ⧸ N := QuotientGroup.mk' N
  have hker : f.ker = N := QuotientGroup.ker_mk' N
  have hleK : N ≤ K := hNle.trans inf_le_left
  have hleK' : N ≤ K' := hNle.trans inf_le_right
  have hkerK : f.ker ≤ K := by rw [hker]; exact hleK
  have hkerK' : f.ker ≤ K' := by rw [hker]; exact hleK'
  have hidxK : (K.map f).index = K.index :=
    Subgroup.index_map_eq K (QuotientGroup.mk'_surjective N) hkerK
  have hidxK' : (K'.map f).index = K'.index :=
    Subgroup.index_map_eq K' (QuotientGroup.mk'_surjective N) hkerK'
  have hidx : (K.map f).index = (K'.map f).index := by rw [hidxK, hidxK', h]
  have hidx0 : (K.map f).index ≠ 0 := by rw [hidxK]; exact h0
  have heq : K.map f = K'.map f := cyclic_subgroup_eq_of_index_eq hidx hidx0
  have h1 : Subgroup.comap f (K.map f) = K := by
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hkerK]
  have h2 : Subgroup.comap f (K'.map f) = K' := by
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hkerK']
  rw [← h1, ← h2, heq]

end Work.SSGRoute

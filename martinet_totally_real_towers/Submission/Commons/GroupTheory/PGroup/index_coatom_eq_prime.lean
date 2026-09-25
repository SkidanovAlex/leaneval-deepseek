import Mathlib.GroupTheory.Nilpotent

namespace Commons.GroupTheory.PGroup

theorem index_coatom_eq_prime {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) {M : Subgroup G} (hM : IsCoatom M) : M.index = p := by
  have hNilp : Group.IsNilpotent G := hG.isNilpotent
  have hMnorm : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M
      (Group.normalizerCondition_of_isNilpotent (G := G)) hM
  let Q := G ⧸ M
  have hQpg : IsPGroup p Q := hG.to_quotient M
  -- The quotient by a maximal subgroup has no proper nontrivial subgroups.
  have htriv : ∀ S : Subgroup Q, S = ⊥ ∨ S = ⊤ := by
    intro S
    let φ : G →* Q := QuotientGroup.mk' M
    have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective M
    have hMle : M ≤ S.comap φ := by
      intro g hg
      rw [Subgroup.mem_comap]
      have h1 : φ g = 1 := by
        show (g : G ⧸ M) = 1
        exact (QuotientGroup.eq_one_iff g).mpr hg
      rw [h1]
      exact S.one_mem
    rcases eq_or_lt_of_le hMle with h | h
    · left
      have hker : (⊥ : Subgroup Q).comap φ = M := by
        rw [MonoidHom.comap_bot, QuotientGroup.ker_mk' M]
      exact Subgroup.comap_injective hsurj (h.symm.trans hker.symm)
    · right
      have htop : S.comap φ = ⊤ := hM.2 (S.comap φ) h
      exact Subgroup.comap_injective hsurj (by rw [htop, Subgroup.comap_top])
  have hx : ∃ x : G, x ∉ M := by
    by_contra h
    exact hM.1 ((Subgroup.eq_top_iff' M).mpr fun x => by
      by_contra hx
      exact h ⟨x, hx⟩)
  obtain ⟨x, hxM⟩ := hx
  have hQnt : Nontrivial Q := ⟨x, 1, fun h => hxM ((QuotientGroup.eq_one_iff x).mp h)⟩
  obtain ⟨n, hnpos, hn⟩ := (IsPGroup.nontrivial_iff_card hQpg).mp hQnt
  have hdvd : p ∣ Nat.card Q := by
    rw [hn]
    exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hnpos)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Q) p hdvd
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    exact (Fact.out : p.Prime).ne_one hy.symm
  have hzpow : Subgroup.zpowers y = ⊤ := by
    rcases htriv (Subgroup.zpowers y) with h | h
    · exfalso
      have hmem : y ∈ (⊥ : Subgroup Q) := by rw [← h]; exact Subgroup.mem_zpowers y
      exact hy1 (by simpa using hmem)
    · exact h
  have hcardQ : Nat.card Q = p := by
    have h1 : Nat.card (Subgroup.zpowers y) = Nat.card Q := by
      rw [hzpow, Subgroup.card_top]
    rw [Nat.card_zpowers, hy] at h1
    exact h1.symm
  rw [Subgroup.index_eq_card]
  exact hcardQ

end Commons.GroupTheory.PGroup
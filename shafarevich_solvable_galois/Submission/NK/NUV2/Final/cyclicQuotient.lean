import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A cyclic quotient of a finite abelian group separating a proper subgroup

For a finite abelian group `G` and a proper subgroup `H < G` there is a subgroup `K` with
`H ≤ K`, `K ≠ ⊤` and `G ⧸ K` **cyclic**.  This is the group-theoretic input of the last step of
L7 (`NK.NUV2.Final.levelSymbol_ker`): if the image `H = θ_L(Fˣ)` of a level symbol were proper,
one restricts to the subfield `L^K`, whose Galois group `G ⧸ K` is cyclic, and the level symbol
there is known to be injective modulo norms.

The proof takes a maximal proper subgroup `K` above `H` (it exists because the lattice of subgroups
of a finite group is coatomic, `isCoatomic_of_orderTop_gt_wellFounded`), so `G ⧸ K` has no proper
nontrivial subgroup; any nontrivial element of `G ⧸ K` therefore generates it.
-/

namespace NK.NUV2.Final

universe u

/-- **A cyclic quotient of a finite abelian group separating a proper subgroup.**  For a proper
subgroup `H < G` there is `H ≤ K`, `K ≠ ⊤` with `G ⧸ K` cyclic. -/
theorem exists_cyclic_quotient_of_ne_top {G : Type u} [CommGroup G] [Finite G] (H : Subgroup G)
    (hH : H ≠ ⊤) :
    ∃ K : Subgroup G, H ≤ K ∧ K ≠ ⊤ ∧ IsCyclic (G ⧸ K) := by
  haveI : IsCoatomic (Subgroup G) := inferInstance
  obtain ⟨K, hKmax, hHK⟩ := (IsCoatomic.eq_top_or_exists_le_coatom H).resolve_left hH
  have hKne : K ≠ ⊤ := hKmax.ne_top
  haveI : K.Normal := Subgroup.normal_of_comm K
  obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hKne)
  have hgne : (QuotientGroup.mk' K) g ≠ 1 := by
    rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    exact hg
  refine ⟨K, hHK, hKne, ?_⟩
  rw [isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨QuotientGroup.mk' K g, ?_⟩
  have hsup : K ⊔ Subgroup.zpowers g = ⊤ := by
    rcases eq_or_lt_of_le (le_sup_left : K ≤ K ⊔ Subgroup.zpowers g) with h | h
    · exact absurd (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers g)) hg
    · exact hKmax.lt_iff.mp h
  have hmap : Subgroup.map (QuotientGroup.mk' K) (K ⊔ Subgroup.zpowers g)
      = Subgroup.zpowers (QuotientGroup.mk' K g) := by
    have hbot : Subgroup.map (QuotientGroup.mk' K) K = ⊥ :=
      (Subgroup.map_eq_bot_iff K).mpr (le_of_eq (QuotientGroup.ker_mk' K).symm)
    rw [Subgroup.map_sup, hbot, bot_sup_eq]
    apply Subgroup.ext
    intro y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxy⟩
      rw [Subgroup.mem_zpowers_iff] at hx
      obtain ⟨n, rfl⟩ := hx
      exact ⟨n, by rw [← hxy, map_zpow]⟩
    · rintro ⟨n, hn⟩
      refine ⟨g ^ n, ?_, ?_⟩
      · rw [Subgroup.mem_zpowers_iff]
        exact ⟨n, rfl⟩
      · rw [map_zpow]; exact hn
  rw [← hmap, hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]

end NK.NUV2.Final

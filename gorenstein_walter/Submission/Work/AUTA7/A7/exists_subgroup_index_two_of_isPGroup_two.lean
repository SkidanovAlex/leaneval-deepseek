import Mathlib

namespace Work.AUTA7.A7

/-- In a finite `p`-group, every proper subgroup `D` is contained in a subgroup `P₀`
in which it has index `p`.

A `p`-group is nilpotent, hence every maximal subgroup has index `p`.  We argue by
strong induction on the cardinality of the ambient group: if `D` is a maximal proper
subgroup, the whole group works; otherwise there is a subgroup `K` strictly between
`D` and the top, and we apply the induction hypothesis inside `K`. -/
theorem exists_relIndex_eq_prime_of_isPGroup (p : ℕ) [Fact p.Prime] :
    ∀ (n : ℕ) (G : Type*) [Group G] [Finite G], IsPGroup p G → Nat.card G = n →
      ∀ D : Subgroup G, D ≠ ⊤ → ∃ P₀ : Subgroup G, D ≤ P₀ ∧ D.relIndex P₀ = p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hG hcard D hD
    by_cases hcoat : IsCoatom D
    · -- `D` is a maximal proper subgroup, so it has prime index `p`; the whole group works.
      have hDp : D.index = p :=
        (@IsPGroup.isCoatom_iff_index_eq_prime G _ p _ (hG.isNilpotent) hG D).mp hcoat
      exact ⟨⊤, le_top, by rw [Subgroup.relIndex_top_right, hDp]⟩
    · -- `D` is not maximal: find a subgroup `K` with `D < K < ⊤` and recurse inside `K`.
      rw [IsCoatom] at hcoat
      push Not at hcoat
      obtain ⟨K, hDK, hKne⟩ := hcoat hD
      have hle : D ≤ K := le_of_lt hDK
      have hKlt : K < ⊤ := lt_top_iff_ne_top.mpr hKne
      have hcardK : Nat.card K < n := by
        rw [← hcard, ← Subgroup.card_top (G := G)]
        exact Subgroup.card_lt_of_lt hKlt
      have hDsub : D.subgroupOf K ≠ ⊤ :=
        fun h => not_le_of_gt hDK ((Subgroup.subgroupOf_eq_top).mp h)
      obtain ⟨P₀', hle', hidx'⟩ :=
        ih (Nat.card K) hcardK K (hG.to_subgroup K) rfl (D.subgroupOf K) hDsub
      refine ⟨P₀'.map K.subtype, ?_, ?_⟩
      · rw [← Subgroup.map_subgroupOf_eq_of_le hle]
        exact Subgroup.map_mono hle'
      · rw [← Subgroup.map_subgroupOf_eq_of_le hle]
        exact (Subgroup.relIndex_map_map_of_injective (D.subgroupOf K) P₀'
          K.subtype_injective).trans hidx'

theorem exists_subgroup_index_two_of_isPGroup_two {X : Type*} [Group X] [Finite X]
    (hX : IsPGroup 2 X) {D : Subgroup X} (hD : D ≠ ⊤) :
    ∃ P₀ : Subgroup X, D ≤ P₀ ∧ (D.subgroupOf P₀).index = 2 := by
  obtain ⟨P₀, hle, hidx⟩ :=
    exists_relIndex_eq_prime_of_isPGroup 2 (Nat.card X) X hX rfl D hD
  exact ⟨P₀, hle, hidx⟩

end Work.AUTA7.A7

import Mathlib.GroupTheory.PGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.BNPair

/-- A nontrivial finite `2`-subgroup has even order. -/
lemma even_card_of_isPGroup_two {G : Type*} [Group G] (U : Subgroup G)
    (hU2 : IsPGroup 2 U) (hne : U ≠ ⊥) : Even (Nat.card U) := by
  rcases IsPGroup.card_eq_or_dvd hU2 (p := 2) with h1 | h2
  · exact absurd (Subgroup.card_eq_one.mp h1) hne
  · exact even_iff_two_dvd.mpr h2

theorem normalizer_eq_borel {G : Type*} [Group G] [Finite G] (B U T : Subgroup G)
    (hMne : B ≠ ⊤) (hEven : Even (Nat.card B))
    (hOdd : ∀ g : G, g ∉ B → Odd (Nat.card (B ⊓ B.map (MulAut.conj g).toMonoidHom : Subgroup G)))
    (hB : B = U ⊔ T) (hTnU : T ≤ Subgroup.normalizer (U : Set G))
    (hUne : U ≠ ⊥) (hU2 : IsPGroup 2 U) : Subgroup.normalizer (U : Set G) = B := by
  have hUB : U ≤ B := by rw [hB]; exact le_sup_left
  apply le_antisymm
  · -- `N(U) ≤ B`: if `g ∈ N(U)` normalized `U` and `g ∉ B`, then `U ≤ B ∩ B^g`
    -- has even order, contradicting `hOdd`.
    intro g hg
    by_contra hgn
    have hUle : U ≤ B ⊓ B.map (MulAut.conj g).toMonoidHom := by
      refine le_inf hUB ?_
      intro u hu
      rw [Subgroup.mem_map]
      refine ⟨(MulAut.conj g⁻¹) u, ?_, ?_⟩
      · have h1 : g⁻¹ * u * g ∈ U := (Subgroup.mem_normalizer_iff''.mp hg u).mp hu
        exact hUB (by simpa [MulAut.conj_apply] using h1)
      · change MulAut.conj g ((MulAut.conj g⁻¹) u) = u
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group
    have hdvd : Nat.card U ∣ Nat.card (B ⊓ B.map (MulAut.conj g).toMonoidHom : Subgroup G) :=
      Subgroup.card_dvd_of_le hUle
    have heven : Even (Nat.card (B ⊓ B.map (MulAut.conj g).toMonoidHom : Subgroup G)) :=
      even_iff_two_dvd.mpr
        (dvd_trans (even_iff_two_dvd.mp (even_card_of_isPGroup_two U hU2 hUne)) hdvd)
    exact (Nat.not_even_iff_odd.mpr (hOdd g hgn)) heven
  · -- `B ≤ N(U)`: `U` normalizes itself and `T ≤ N(U)`, so `U ⊔ T = B ≤ N(U)`.
    rw [hB]
    exact sup_le Subgroup.le_normalizer hTnU

end Commons.GroupTheory.BNPair
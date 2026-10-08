import Mathlib.GroupTheory.Sylow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

/-- If a subgroup `M ≤ G` has even order, and `P` is a Sylow 2-subgroup of `G`
contained in `M`, then any element normalizing the subgroup `P` lies in `M`.

The argument: take `g ∈ N_G(P)` with `g ∉ M`.  Then `P ≤ M` and also
`P ≤ g M g⁻¹` (because `g` normalizes `P ⊆ M`), so `P ≤ M ∩ Mᵍ`.  Since `|P|`
is even (a Sylow 2-subgroup of a group of even order), the intersection
`M ∩ Mᵍ` has even order, contradicting the hypothesis that it has odd order
for every `g ∉ M`. -/
theorem normalizer_le {G : Type*} [Group G] [Finite G] (M : Subgroup G)
    (hEven : Even (Nat.card M))
    (hOdd : ∀ g : G, g ∉ M → Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    (P : Sylow 2 G) (hP : (P : Subgroup G) ≤ M) :
    Subgroup.normalizer (P : Set G) ≤ M := by
  classical
  -- |P| is even: 2 | |M| | |G| and P is a Sylow 2-subgroup of G.
  have hPeven : Even (Nat.card (P : Subgroup G)) := by
    have h2M : 2 ∣ Nat.card M := even_iff_two_dvd.mp hEven
    have h2G : 2 ∣ Nat.card G := dvd_trans h2M (Subgroup.card_subgroup_dvd_card M)
    exact even_iff_two_dvd.mpr (P.dvd_card_of_dvd_card (p := 2) h2G)
  intro g hgN
  by_contra hgM
  -- g normalizes P (as a set), so conjugation by g⁻¹ preserves P.
  have hgN' : ∀ h : G, h ∈ (P : Subgroup G) ↔ g⁻¹ * h * g ∈ (P : Subgroup G) := by
    exact (Subgroup.mem_set_normalizer_iff'').mp hgN
  -- P ≤ Mᵍ = g M g⁻¹.
  have hPleMg : (P : Subgroup G) ≤ M.map (MulAut.conj g).toMonoidHom := by
    intro p hp
    refine (Subgroup.mem_map).mpr ⟨g⁻¹ * p * g, ?_, ?_⟩
    · exact hP ((hgN' p).mp hp)
    · change g * (g⁻¹ * p * g) * g⁻¹ = p
      group
  -- P ≤ M ∩ Mᵍ, hence 2 | |M ∩ Mᵍ|.
  have hPle : (P : Subgroup G) ≤
      (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G) :=
    le_inf hP hPleMg
  have h2inter : 2 ∣ Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G)) :=
    dvd_trans (even_iff_two_dvd.mp hPeven) (Subgroup.card_dvd_of_le hPle)
  -- contradiction: M ∩ Mᵍ has odd order for g ∉ M.
  exact (Nat.not_even_iff_odd.mpr (hOdd g hgM)) (even_iff_two_dvd.mpr h2inter)

end Commons.GroupTheory.StronglyEmbedded
import Mathlib.Tactic.Group
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.map_conj_map
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.map_eq_top_iff_of_ker_le
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.card_map_mul_card_ker

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

theorem stronglyEmbedded_map_of_surjective {G H : Type*} [Group G] [Group H] [Finite G] [Finite H] (φ : G →* H) (hφ : Function.Surjective φ) (M : Subgroup G) (hM : M ≠ ⊤) (hEven : Even (Nat.card M)) (hOdd : ∀ g : G, g ∉ M → Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G)))) (hker : φ.ker ≤ M) (hcent : φ.ker ≤ Subgroup.center G) (hkerodd : Odd (Nat.card φ.ker)) : (M.map φ ≠ ⊤) ∧ Even (Nat.card (M.map φ)) ∧ ∀ h : H, h ∉ M.map φ → Odd (Nat.card ((M.map φ ⊓ (M.map φ).map (MulAut.conj h).toMonoidHom : Subgroup H))) := by
  have hFintypeG : Fintype G := Fintype.ofFinite G
  refine ⟨?_, ?_, ?_⟩
  · -- `M.map φ ≠ ⊤`: preimage of a proper subgroup.
    intro htop
    exact hM ((Commons.GroupTheory.Subgroup.map_eq_top_iff_of_ker_le φ hφ hker).mp htop)
  · -- `Even (Nat.card (M.map φ))`: from `|M.map φ| * |ker| = |M|` with `|ker|` odd.
    have hcard := Commons.GroupTheory.Subgroup.card_map_mul_card_ker φ M hker
    have hEven' : Even (Nat.card (M.map φ) * Nat.card φ.ker) := hcard ▸ hEven
    rcases Nat.even_mul.mp hEven' with h | h
    · exact h
    · exact absurd h (Nat.not_even_iff_odd.mpr hkerodd)
  · -- Strong embedding passes to the quotient.
    intro h hh
    obtain ⟨g, hg⟩ := hφ h
    have hgM : g ∉ M := fun hgmem =>
      hh (Subgroup.mem_map.mpr ⟨g, hgmem, hg⟩)
    -- The intersection of the images is the image of the intersection.
    have hEq : (M ⊓ M.map (MulAut.conj g).toMonoidHom).map φ =
        M.map φ ⊓ (M.map φ).map (MulAut.conj h).toMonoidHom := by
      rw [Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le φ M
            (M.map (MulAut.conj g).toMonoidHom) hker,
          Commons.GroupTheory.Subgroup.map_conj_map φ M g, ← hg]
    -- The kernel is contained in `M ⊓ Mᵍ`, since it is central.
    have hker' : φ.ker ≤ M ⊓ M.map (MulAut.conj g).toMonoidHom := by
      intro x hx
      refine Subgroup.mem_inf.mpr ⟨hker hx, ?_⟩
      rw [Subgroup.mem_map]
      have hxM : x ∈ M := hker hx
      have hxc : ∀ y : G, y * x = x * y := (Subgroup.mem_center_iff.mp (hcent hx))
      have hgx : g⁻¹ * x * g = x := by rw [hxc g⁻¹]; group
      exact ⟨g⁻¹ * x * g, by rw [hgx]; exact hxM, by
        change (MulAut.conj g) (g⁻¹ * x * g) = x
        rw [MulAut.conj_apply]; group⟩
    have hcardA := Commons.GroupTheory.Subgroup.card_map_mul_card_ker φ
      (M ⊓ M.map (MulAut.conj g).toMonoidHom) hker'
    have hodd1 : Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom).map φ) *
        Nat.card φ.ker) := by
      rw [hcardA]; exact hOdd g hgM
    have hodd2 : Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom).map φ)) :=
      Nat.Odd.of_mul_left hodd1
    rwa [hEq] at hodd2

end Commons.GroupTheory.StronglyEmbedded
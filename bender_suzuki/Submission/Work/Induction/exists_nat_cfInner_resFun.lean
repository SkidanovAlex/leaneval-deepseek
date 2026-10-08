import Mathlib
import Submission.Work.Induction.Defs
import Submission.Work.CharCore.star_char
import Submission.Work.CharCore.irreducible_character_mem_Irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

-- The multiplicity of an irreducible character in the restriction of an irreducible
-- character is a natural number: for `χ ∈ Irr G` and `θ ∈ Irr H`,
-- `⟨Res_H^G χ, θ⟩_H = |H|⁻¹ ∑_h χ h * conj (θ h)` is a natural number.
-- Proof route: write `χ` (resp. `θ`) as the character of a simple submodule `N ⊆ ℂ[G]`
-- (resp. `M ⊆ ℂ[H]`), view them as `FDRep`s, restrict `V := FDRep.of (submoduleRep N)` to `H`;
-- Mathlib's `FDRep.scalar_product_char_eq_finrank_equivariant` applied in the group `H` gives
-- `|H|⁻¹ ∑_h W.character h * V'.character h⁻¹ = finrank (V' ⟶ W)`, and
-- `Work.CharCore.star_char` plus the reindexing `h ↦ h⁻¹` identify the left side with
-- `⟨Res_H^G χ, θ⟩_H`.
theorem exists_nat_cfInner_resFun {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    {χ : G → ℂ} (hχ : χ ∈ Work.CharCore.Irr G) {θ : H → ℂ} (hθ : θ ∈ Work.CharCore.Irr H) :
    ∃ n : ℕ, Work.CharCore.cfInner (Work.Induction.resFun H χ) θ = n := by
  classical
  -- write `χ` and `θ` as characters of simple submodules of the respective regular modules
  obtain ⟨N, _hN, hNχ⟩ := Work.CharCore.exists_mem_irrSubmodules_of_mem_Irr hχ
  obtain ⟨M, _hM, hMθ⟩ := Work.CharCore.exists_mem_irrSubmodules_of_mem_Irr hθ
  -- the restriction of the representation of `G` on `N` to the subgroup `H`
  let ρ' : Representation ℂ H ↥N := (Work.CharCore.submoduleRep N).comp H.subtype
  let σ : Representation ℂ H ↥M := Work.CharCore.submoduleRep M
  have hρ' : Representation.character ρ' = Work.Induction.resFun H χ := by
    funext h
    change Representation.character (Work.CharCore.submoduleRep N) (h : G) = χ h
    rw [hNχ]
  have hσ : Representation.character σ = θ := hMθ
  -- the answer is the dimension of the space of intertwining maps
  refine ⟨Module.finrank ℂ (Representation.IntertwiningMap ρ' σ), ?_⟩
  have key := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ' σ
  rw [Work.CharCore.cfInner_apply]
  have hcard : (Fintype.card H : ℂ) = (Nat.card H : ℂ) := by
    rw [Fintype.card_eq_nat_card]
  rw [hcard]
  have hsum : ∑ x : H, Work.Induction.resFun H χ x * starRingEnd ℂ (θ x)
      = ∑ x : H, Representation.character σ x * Representation.character ρ' x⁻¹ := by
    rw [← Equiv.sum_comp (Equiv.inv H)
      (fun x => Representation.character σ x * Representation.character ρ' x⁻¹)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← hρ', ← hσ, Work.CharCore.star_char σ x]
    simp only [Equiv.inv_apply, inv_inv]
    ring
  rw [hsum]
  exact key

end Work.Induction

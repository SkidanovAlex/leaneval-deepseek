import Mathlib
import Submission.Work.Clifford.Basic
import Submission.Work.CharCore.mem_Irr_iff_fdrep
import Submission.Work.CharCore.fdRep_simple_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.irr_precomp_mulEquiv`

Precomposition of an irreducible character with a group isomorphism.

If `e : H ≃* K` is an isomorphism of groups and `θ` is an irreducible complex character
of `K`, then `h ↦ θ (e h)` is an irreducible complex character of `H`.

The proof is a transport of representations: an irreducible representation `V` of `K` with
character `θ` is pulled back along `e` to a representation `ρ' = V.ρ ∘ e` of `H` on the same
space, and `FDRep.of ρ'` is simple because the lattice of subrepresentations of `ρ'` is
isomorphic to that of `V.ρ` (a subspace is stable under `ρ' (h) = V.ρ (e h)` for all `h ∈ H`
iff it is stable under `V.ρ k` for all `k ∈ K`).  Its character is `h ↦ trace (V.ρ (e h)) =
θ (e h)`.
-/

namespace Work.Clifford

open CategoryTheory

theorem irr_precomp_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K) {θ : K → ℂ}
    (hθ : θ ∈ Work.Clifford.Irr K) :
    (fun h => θ (e h)) ∈ Work.Clifford.Irr H := by
  obtain ⟨V, hV, hchar⟩ := hθ
  -- The pullback of `V.ρ` along `e`.
  let ρ' : Representation ℂ H ↥V := V.ρ.comp e.toMonoidHom
  have hρ' : ∀ h : H, ρ' h = V.ρ (e h) := fun h => rfl
  have hIrr : Representation.IsIrreducible V.ρ :=
    @Work.CharCore.isIrreducible_of_simple_fdRep K _ V hV
  -- A subspace of `↥V` is stable under `ρ'` iff it is stable under `V.ρ`.
  have hSO' : IsSimpleOrder (Subrepresentation ρ') := by
    let f : Subrepresentation V.ρ → Subrepresentation ρ' := fun S =>
      { toSubmodule := S.toSubmodule
        apply_mem_toSubmodule := fun h v hv => S.apply_mem_toSubmodule (e h) hv }
    let g : Subrepresentation ρ' → Subrepresentation V.ρ := fun T =>
      { toSubmodule := T.toSubmodule
        apply_mem_toSubmodule := fun k v hv => by
          obtain ⟨h, rfl⟩ := e.surjective k
          exact T.apply_mem_toSubmodule h hv }
    have hfg : ∀ S, g (f S) = S := fun S => Subrepresentation.toSubmodule_injective rfl
    have hgf : ∀ T, f (g T) = T := fun T => Subrepresentation.toSubmodule_injective rfl
    have hbot : f ⊥ = (⊥ : Subrepresentation ρ') :=
      Subrepresentation.toSubmodule_injective rfl
    have htop : f ⊤ = (⊤ : Subrepresentation ρ') :=
      Subrepresentation.toSubmodule_injective rfl
    obtain ⟨a, b, hab⟩ := hIrr.exists_pair_ne
    have hne : f a ≠ f b := fun h => hab (by rw [← hfg a, ← hfg b, h])
    exact { toNontrivial := ⟨f a, f b, hne⟩
            eq_bot_or_eq_top := fun S => by
              rcases hIrr.eq_bot_or_eq_top (g S) with h | h
              · left; rw [← hgf S, h]; exact hbot
              · right; rw [← hgf S, h]; exact htop }
  refine ⟨FDRep.of ρ', ?_, ?_⟩
  · rw [Work.CharCore.fdRep_simple_iff, FDRep.of_ρ']
    exact hSO'
  · funext h
    simp only [FDRep.character, FDRep.of_ρ']
    rw [hρ' h, ← hchar]
    rfl

end Work.Clifford

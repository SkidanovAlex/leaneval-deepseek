import Mathlib
import Submission.Work.Clifford.CFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.autChar_mem_Irr`

The set `Work.Clifford.Irr G` of irreducible complex characters of a finite group is stable
under precomposition with an automorphism of `G`: the twist `autChar e χ = χ ∘ e.symm` of an
irreducible character is again irreducible.

The proof pulls back a simple representation `V` realising `χ` along `e`.  The pull-back
`Action.res (FGModuleCat ℂ) e.symm` is the functor of the equivalence `Action.resEquiv` induced
by the monoid isomorphism `e.symm`, so it preserves simple objects
(`CategoryTheory.simple_obj`); concretely it is the representation `FDRep.of (V.ρ.comp e.symm)`,
with the same underlying module but action precomposed with `e.symm`.  Hence it is a simple
representation whose character is `χ ∘ e.symm`.
-/

noncomputable section

open Classical

set_option linter.style.haveILetI false

namespace Work.Clifford

theorem autChar_mem_Irr {G : Type*} [Group G] [Fintype G] (e : G ≃* G) {χ : G → ℂ}
    (hχ : χ ∈ Work.Clifford.Irr G) : Work.Clifford.autChar e χ ∈ Work.Clifford.Irr G := by
  obtain ⟨V, hVsimple, hVχ⟩ := (Work.Clifford.mem_Irr (G := G) (χ := χ)).mp hχ
  -- The pull-back of `V` along `e`: same module, action precomposed with `e.symm`.
  let W : FDRep ℂ G := FDRep.of (V.ρ.comp (e.symm : G →* G))
  have hWρ : W.ρ = V.ρ.comp (e.symm : G →* G) := FDRep.of_ρ' _
  -- Its character is the twist of `χ`.
  have hchar : W.character = autChar e χ := by
    ext g
    rw [FDRep.character, autChar]
    show LinearMap.trace ℂ V (W.ρ g) = χ (e.symm g)
    rw [hWρ, ← hVχ]
    rfl
  -- It is simple, because it is the image of the simple `V` under the restriction functor
  -- along the monoid isomorphism `e.symm`, an equivalence of categories.
  have hWsimple : CategoryTheory.Simple W := by
    haveI : CategoryTheory.Simple V := hVsimple
    have h := CategoryTheory.simple_obj
      ((Action.resEquiv (FGModuleCat ℂ) e.symm).functor) V
    rw [Action.resEquiv_functor] at h
    exact h
  exact ⟨W, hWsimple, hchar⟩

end Work.Clifford

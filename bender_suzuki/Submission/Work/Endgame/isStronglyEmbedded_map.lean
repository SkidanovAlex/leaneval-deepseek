import Submission.Work.Endgame.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Transport of `IsStronglyEmbedded` along a group isomorphism

`IsStronglyEmbedded` is isomorphism-invariant: if `e : G ≃* H` and `K ≤ G` is strongly embedded,
then so is `K.map e` in `H`.  Card of the image is preserved
(`Subgroup.card_map_of_injective`), properness is preserved, and the defining odd-order condition
transports because `conj_map_mulEquiv` turns conjugation in `H` into conjugation in `G` and
`Subgroup.map_inf` distributes the image over the intersection.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.Endgame

theorem isStronglyEmbedded_map {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {K : Subgroup G} (h : IsStronglyEmbedded K) :
    IsStronglyEmbedded (K.map e.toMonoidHom) := by
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    apply h.1
    rw [Subgroup.eq_top_iff']
    intro x
    have hx : e x ∈ K.map e.toMonoidHom := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rwa [e.injective hyx] at hy
  · rw [Subgroup.card_map_of_injective e.injective]
    exact h.2.1
  · intro g hg
    have hg' : e.symm g ∉ K := by
      intro hmem
      exact hg (Subgroup.mem_map.mpr ⟨e.symm g, hmem, e.apply_symm_apply g⟩)
    have hkey : K.map e.toMonoidHom ⊓ (K.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom
        = (K ⊓ K.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ e.injective, ← conj_map_mulEquiv e K (e.symm g),
        e.apply_symm_apply]
    rw [hkey, Subgroup.card_map_of_injective e.injective]
    exact h.2.2 (e.symm g) hg'

end Work.Endgame

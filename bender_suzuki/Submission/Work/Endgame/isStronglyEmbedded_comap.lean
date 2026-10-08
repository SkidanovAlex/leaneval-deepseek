import Mathlib
import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.isStronglyEmbedded_map

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Endgame

/-- Since `e : G ≃* H` is a bijection, the preimage of `K ≤ H` under `e` is the image of `K`
under `e.symm`.  This lets us deduce the `comap` statement from the `map` statement
`isStronglyEmbedded_map`. -/
theorem comap_eq_map_symm {G H : Type*} [Group G] [Group H] (e : G ≃* H) (K : Subgroup H) :
    Subgroup.comap e.toMonoidHom K = K.map e.symm.toMonoidHom := by
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · intro hg; exact ⟨e g, hg, e.symm_apply_apply g⟩
  · rintro ⟨k, hk, rfl⟩; simpa using hk

theorem isStronglyEmbedded_comap {G H : Type*} [Group G] [Group H] (e : G ≃* H) {K : Subgroup H} (h : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K) : LeanEval.GroupTheory.Defs.IsStronglyEmbedded (Subgroup.comap e.toMonoidHom K) := by
  rw [comap_eq_map_symm e K]
  exact isStronglyEmbedded_map e.symm h

end Work.Endgame

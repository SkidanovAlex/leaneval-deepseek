/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# Finite generation of a subgroup and of its preimage along a bijective homomorphism

For a bijective group homomorphism `π : H →* G`, a subgroup `K ≤ G` is finitely generated
if and only if its preimage `K.comap π` is: `π` restricts to an isomorphism
`K.comap π ≃* K`, and finite generation of a group is preserved by a surjective homomorphism.
-/
import Mathlib
import Submission.Work.ORDunwoody.Basic

set_option autoImplicit false

namespace Work.ORDunwoody.Lemmas

/-- For a bijective homomorphism `π : H →* G` and a subgroup `K ≤ G`, the preimage
`K.comap π` is finitely generated if and only if `K` is. -/
theorem subgroup_fg_comap_iff_of_bijective {G H : Type*} [Group G] [Group H] (π : H →* G)
    (hπ : Function.Bijective π) (K : Subgroup G) : (K.comap π).FG ↔ K.FG := by
  -- `π` restricts to an isomorphism between the preimage of `K` and `K`.
  let e : (K.comap π) ≃* K :=
  { toFun := fun a => ⟨π a.1, a.2⟩
    invFun := fun b => ⟨(hπ.surjective b.1).choose, by
      show π (hπ.surjective b.1).choose ∈ K
      rw [(hπ.surjective b.1).choose_spec]; exact b.2⟩
    left_inv := fun a => Subtype.ext (hπ.injective ((hπ.surjective (π a.1)).choose_spec))
    right_inv := fun b => Subtype.ext ((hπ.surjective b.1).choose_spec)
    map_mul' := fun a b => Subtype.ext (map_mul π a.1 b.1) }
  rw [← Group.fg_iff_subgroup_fg (K.comap π), ← Group.fg_iff_subgroup_fg K]
  constructor
  · intro h
    exact Group.fg_of_surjective (G := K.comap π) (G' := K) (hG := h) (f := e.toMonoidHom)
      e.surjective
  · intro h
    exact Group.fg_of_surjective (G := K) (G' := K.comap π) (hG := h) (f := e.symm.toMonoidHom)
      e.symm.surjective

end Work.ORDunwoody.Lemmas

import Mathlib
import Submission.Work.ORReductions.Basic

namespace Work.ORReductions.Coherent

/-- The image of a finitely generated subgroup under a group homomorphism is finitely
generated. -/
theorem subgroup_fg_map {G H : Type*} [Group G] [Group H] (f : G →* H) {K : Subgroup G}
    (hK : K.FG) : (K.map f).FG := by
  rw [Subgroup.fg_iff] at hK ⊢
  obtain ⟨S, hS, hSfin⟩ := hK
  exact ⟨f '' S, by rw [← MonoidHom.map_closure f S, hS], hSfin.image f⟩

/-- Coherence of groups is invariant under isomorphism.  Given `e : G ≃* H` and a finitely
generated subgroup `K ≤ H`, its preimage `K.map e.symm ≤ G` is finitely generated, hence
finitely presented by coherence of `G`; transporting back along the isomorphism
`K ≃* K.map e.symm` gives that `K` is finitely presented. -/
theorem groupCoherent_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Group.Coherent G → Group.Coherent H := by
  intro hG K hK
  have hLfg : (K.map e.symm.toMonoidHom).FG := subgroup_fg_map e.symm.toMonoidHom hK
  have hLfp : Group.IsFinitelyPresented (K.map e.symm.toMonoidHom) := hG _ hLfg
  exact Group.IsFinitelyPresented.equiv
    (Subgroup.equivMapOfInjective K e.symm.toMonoidHom e.symm.injective).symm
    (h := hLfp)

end Work.ORReductions.Coherent

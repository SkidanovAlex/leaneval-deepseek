import Mathlib

namespace Work.ORAssembly.FP2

/-- Pulling back a finitely generated subgroup along a group isomorphism yields a finitely
generated subgroup, and the pullback subgroup is isomorphic to the original one. -/
theorem fg_comap_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (K : Subgroup H)
    (hK : K.FG) :
    (Subgroup.comap e.toMonoidHom K).FG ∧ Nonempty (↥(Subgroup.comap e.toMonoidHom K) ≃* ↥K) := by
  have hcomap : Subgroup.comap e.toMonoidHom K = Subgroup.map e.symm.toMonoidHom K :=
    Subgroup.comap_equiv_eq_map_symm' e K
  refine ⟨?_, ?_⟩
  · rw [hcomap, Subgroup.fg_iff_submonoid_fg, Subgroup.map_toSubmonoid]
    exact Submonoid.FG.map ((Subgroup.fg_iff_submonoid_fg K).mp hK) e.symm.toMonoidHom
  · exact ⟨(MulEquiv.subgroupCongr hcomap).trans (MulEquiv.subgroupMap e.symm K).symm⟩

end Work.ORAssembly.FP2

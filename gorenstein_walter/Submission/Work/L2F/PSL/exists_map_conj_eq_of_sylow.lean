import Mathlib

namespace Work.L2F.PSL

/-- **Sylow conjugacy, in subgroup form.**  Any two Sylow `p`-subgroups of a finite group are
conjugate: for `Q S : Sylow p G` there is `g : G` with `S = Q.map (MulAut.conj g)` as subgroups of
`G`. -/
theorem exists_map_conj_eq_of_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (Q S : Sylow p G) :
    ∃ g : G, (S : Subgroup G) = (Q : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  exact ⟨g, by rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]; congr 1⟩

end Work.L2F.PSL

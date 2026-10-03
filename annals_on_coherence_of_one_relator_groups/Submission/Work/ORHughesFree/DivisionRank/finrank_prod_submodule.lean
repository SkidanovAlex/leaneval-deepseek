import Mathlib

namespace Work.ORHughesFree.DivisionRank

/-- The canonical linear equivalence between a product of two submodules and the
product of the submodules. -/
noncomputable def prodSubmoduleEquiv {D : Type*} [DivisionRing D] {M M' : Type*}
    [AddCommGroup M] [Module D M] [AddCommGroup M'] [Module D M']
    (S : Submodule D M) (S' : Submodule D M') : ↥(S.prod S') ≃ₗ[D] ↥S × ↥S' :=
  LinearEquiv.ofBijective
    { toFun := fun x =>
        (⟨x.1.1, (Submodule.mem_prod.mp x.2).1⟩, ⟨x.1.2, (Submodule.mem_prod.mp x.2).2⟩)
      map_add' := by intro a b; ext <;> rfl
      map_smul' := by intro a b; ext <;> rfl }
    (by
      constructor
      · intro a b h
        have h1 : a.1.1 = b.1.1 := congrArg (fun t : ↥S × ↥S' => (t.1 : M)) h
        have h2 : a.1.2 = b.1.2 := congrArg (fun t : ↥S × ↥S' => (t.2 : M')) h
        exact Subtype.ext (Prod.ext h1 h2)
      · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        exact ⟨⟨(a, b), Submodule.mem_prod.mpr ⟨ha, hb⟩⟩, rfl⟩)

theorem finrank_prod_submodule {D : Type*} [DivisionRing D] {M M' : Type*} [AddCommGroup M] [Module D M]
    [AddCommGroup M'] [Module D M'] (S : Submodule D M) (S' : Submodule D M')
    [Module.Finite D ↥S] [Module.Finite D ↥S'] :
    Module.finrank D ↥(S.prod S') = Module.finrank D ↥S + Module.finrank D ↥S' := by
  rw [(prodSubmoduleEquiv S S').finrank_eq, Module.finrank_prod]

end Work.ORHughesFree.DivisionRank

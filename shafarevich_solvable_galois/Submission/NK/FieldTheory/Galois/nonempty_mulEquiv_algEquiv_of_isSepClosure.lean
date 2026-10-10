import Mathlib.FieldTheory.IsSepClosed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.FieldTheory.Galois

/-- Any two separable closures of the same field `K` have isomorphic groups of
`K`-algebra automorphisms: a (`K`-linear) isomorphism `L ≃ₐ[K] M` between the two
separable closures induces such a group isomorphism by conjugation
(`AlgEquiv.autCongr`). -/
theorem nonempty_mulEquiv_algEquiv_of_isSepClosure {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [IsSepClosure K L] [IsSepClosure K M] :
    Nonempty ((L ≃ₐ[K] L) ≃* (M ≃ₐ[K] M)) :=
  ⟨AlgEquiv.autCongr (IsSepClosure.equiv K L M)⟩

end NK.FieldTheory.Galois

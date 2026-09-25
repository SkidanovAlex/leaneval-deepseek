import Mathlib

namespace NK.CFTLib

open CategoryTheory Limits

/-- **Exactness of Tate cohomology at the middle term of a short exact sequence.**

If `S : X₁ ⟶ X₂ ⟶ X₃` is a short exact sequence of `ℤ[G]`-modules and both
`Ĥ^r(G, X₁)` and `Ĥ^r(G, X₃)` are trivial, then so is `Ĥ^r(G, X₂)`.

This is a formal consequence of the long exact sequence in Tate cohomology: the
sequence `Ĥ^r(G,X₁) → Ĥ^r(G,X₂) → Ĥ^r(G,X₃)` is exact at the middle term (this
is `ShortComplex.ShortExact.homology_exact₂` applied to the short exact sequence
of Tate complexes) and an exact sequence whose two outer terms are zero has
zero middle term (`ShortComplex.Exact.isZero_of_both_isZero`). -/
theorem subsingleton_tateCohomology_of_shortExact_middle {G : Type} [Group G] [Fintype G]
    (S : CategoryTheory.ShortComplex (Rep ℤ G))
    (hS : CategoryTheory.ShortComplex.ShortExact S) (r : ℤ)
    (h1 : Subsingleton (tateCohomology S.X₁ r)) (h3 : Subsingleton (tateCohomology S.X₃ r)) :
    Subsingleton (tateCohomology S.X₂ r) := by
  -- The Tate complex functor turns `S` into a short exact sequence of complexes.
  let K : ShortComplex (CochainComplex (ModuleCat ℤ) ℤ) := S.map (tateComplexFunctor ℤ G)
  have hK : K.ShortExact := TateCohomology.map_tateComplexFunctor_shortExact (R := ℤ) (G := G) hS
  -- The long exact sequence in homology is exact at the middle term.
  have hex := hK.homology_exact₂ r
  -- The two outer terms are trivial.
  have h1' : Subsingleton ↥(K.X₁.homology r) := h1
  have h3' : Subsingleton ↥(K.X₃.homology r) := h3
  have hz : IsZero (K.X₂.homology r) :=
    hex.isZero_of_both_isZero
      (@ModuleCat.isZero_of_subsingleton ℤ _ (K.X₁.homology r) h1')
      (@ModuleCat.isZero_of_subsingleton ℤ _ (K.X₃.homology r) h3')
  exact ModuleCat.subsingleton_of_isZero hz

end NK.CFTLib

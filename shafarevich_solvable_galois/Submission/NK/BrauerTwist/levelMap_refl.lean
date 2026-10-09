import Mathlib
import Submission.NK.BrauerTwist.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.BrauerTwist

universe u

/-- **Reflexivity of the level transition maps.**  For a finite Galois level `L` of `K'/K`, the
transition map `levelMap p U (le_refl L) : H²(U ⧸ (U ⊓ Gal(K'/L)), μ_p(L)) ⟶ H²(…, μ_p(L))` is the
identity.

Both ingredients degenerate at `L' = L`: the quotient map
`U ⧸ (U ⊓ Gal(K'/L)) →* U ⧸ (U ⊓ Gal(K'/L))` attached to the reflexive inclusion is the identity
(`QuotientGroup.map_id`), and the coefficient morphism `μ_p(L) ↪ μ_p(L)` is the identity of linear
maps `muInclLinearMap (le_refl L) = LinearMap.id` (definitionally: `muIncl (le_refl L)` is the
identity of subtypes).  The two facts are combined with `groupCohomology.map_congr`, which compares
`groupCohomology.map` for two pairs `(f, φ)`, `(g, ψ)` with `f = g` and `φ.hom = ψ.hom` as linear
maps, followed by `groupCohomology.map_id`. -/
theorem levelMap_refl {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    NK.BrauerTwist.levelMap p U (le_refl L) =
      CategoryTheory.CategoryStruct.id (NK.BrauerTwist.LevelH2 p U L) := by
  -- The quotient map of the reflexive inclusion is the identity group homomorphism.
  have hq : NK.BrauerHasse.levelQuotHom (U := U) (le_refl L) =
      MonoidHom.id (NK.BrauerHasse.LevelGroup U L) := by
    simp only [NK.BrauerHasse.levelQuotHom]
    exact QuotientGroup.map_id _ _
  -- The coefficient morphism of the reflexive inclusion is the identity (as a linear map).
  exact (groupCohomology.map_congr (n := 2)
      (f := NK.BrauerHasse.levelQuotHom (U := U) (le_refl L))
      (g := MonoidHom.id (NK.BrauerHasse.LevelGroup U L))
      (φ := NK.BrauerTwist.levelMapCoeff p U (le_refl L))
      (ψ := CategoryTheory.CategoryStruct.id (NK.BrauerTwist.levelRep p U L))
      hq rfl).trans (groupCohomology.map_id 2)

end NK.BrauerTwist

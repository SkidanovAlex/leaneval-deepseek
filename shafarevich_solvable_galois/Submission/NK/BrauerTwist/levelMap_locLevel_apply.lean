import Mathlib
import Submission.NK.BrauerTwist.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the level-wise localisation map in the level

For `L ≤ L'` two finite Galois levels of `K'/K` and a closed subgroup `U ≤ Gal(K'/K)`, the
level-wise localisation map `locLevel` (restriction from the level group `U ⧸ (U ⊓ Gal(K'/L))` to
the local level group `(U ⊓ D_A) ⧸ ((U ⊓ D_A) ⊓ Gal(K'/L))`, with coefficients `μ_p(L)`) is
compatible with the level transition (inflation) maps `levelMap`:

```
LevelH2 L  -- locLevel -->  LocalLevelH2 L
   |                              |
levelMap                     localLevelMap
   |                              |
LevelH2 L' -- locLevel -->  LocalLevelH2 L'
```

This is the statement that `locLevel` is a map of the two filtered systems, and it is what makes
the localisation map of the twisted profinite cohomology
(`NK.BrauerTwist.H2Twist.loc`, `Submission/Work/BrauerTwist/Profinite.lean`) descend to the
colimit.

Both `levelMap` and `localLevelMap` are `groupCohomology.map` applied to (i) the quotient
homomorphism of the level groups and (ii) the morphism of representations induced by the
coefficient inclusion `μ_p(L) ↪ μ_p(L')`; likewise `locLevel` is `groupCohomology.map` applied to
the inclusion of the local level group into the global one and the coefficient identity.  The
square is therefore an instance of the functoriality `groupCohomology.map_comp` together with the
compatibility of the two "inclusion of the local level group" homomorphisms
(`NK.BrauerHasse.localInclHom_comp`), the two composites of coefficient morphisms agreeing
because their underlying linear maps are both the coefficient inclusion `muInclLinearMap h`.
-/

open CategoryTheory

namespace NK.BrauerTwist

universe u

/-- **The square of the level transition and the localisation map.**  Inflation between the levels
`L ≤ L'` commutes with the level-wise localisation at a place `A`, in the local and global level
cohomology with coefficients in `μ_p`.

Both sides are `groupCohomology.map` of the composite of the level quotient homomorphism
`U ⧸ (U ⊓ Gal(K'/L')) →* U ⧸ (U ⊓ Gal(K'/L))` with the inclusion of the local level group
`(U ⊓ D_A) ⧸ (…) →* U ⧸ (U ⊓ Gal(K'/L'))`; the equality of the two group homomorphisms is exactly
`NK.BrauerHasse.localInclHom_comp` and the two coefficient morphisms have the same underlying
linear map `muInclLinearMap h`, so `groupCohomology.map_congr` applies. -/
private lemma levelMap_comp_locLevel {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') :
    (NK.BrauerTwist.levelMap p U h) ≫ (NK.BrauerTwist.locLevel p U A L') =
      (NK.BrauerTwist.locLevel p U A L) ≫ (NK.BrauerTwist.localLevelMap p U A h) := by
  -- Unfold the three maps into instances of `groupCohomology.map`.
  simp only [NK.BrauerTwist.levelMap, NK.BrauerTwist.locLevel, NK.BrauerTwist.localLevelMap]
  -- Combine each composite of `groupCohomology.map`s into a single one (`map_comp`), so that
  -- both sides become `groupCohomology.map` of a composite group homomorphism.  On the left this
  -- is `levelQuotHom h` after `localInclHom L'`; on the right `localInclHom L` after
  -- `localLevelQuotHom h`.
  rw [← groupCohomology.map_comp (f := NK.BrauerHasse.levelQuotHom (U := U) h)
        (g := NK.BrauerHasse.localInclHom U A L')
        (NK.BrauerTwist.levelMapCoeff p U h) (NK.BrauerTwist.locCoeff p U A L') 2]
  rw [← groupCohomology.map_comp (f := NK.BrauerHasse.localInclHom U A L)
        (g := NK.BrauerHasse.localLevelQuotHom U A h)
        (NK.BrauerTwist.locCoeff p U A L) (NK.BrauerTwist.localLevelMapCoeff p U A h) 2]
  -- The two group homomorphisms agree (`localInclHom_comp`), and the two coefficient morphisms
  -- have the same underlying linear map `muInclLinearMap h` (definitionally: the restriction
  -- functor does not change the underlying linear map and `μ_p(L) ↪ μ_p(L')` absorbs the identity
  -- inclusions `μ_p(L) ↪ μ_p(L)`, `μ_p(L') ↪ μ_p(L')`).
  exact groupCohomology.map_congr (NK.BrauerHasse.localInclHom_comp U A h) rfl 2

/-- Elementwise form of `levelMap_comp_locLevel`: the level-wise localisation is compatible with
the level transition maps. -/
theorem levelMap_locLevel_apply {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (a : NK.BrauerTwist.LevelH2 p U L) :
    (NK.BrauerTwist.locLevel p U A L') ((NK.BrauerTwist.levelMap p U h) a) =
      (NK.BrauerTwist.localLevelMap p U A h) ((NK.BrauerTwist.locLevel p U A L) a) := by
  have hsq := levelMap_comp_locLevel p U A h
  have hApp := congrArg
    (fun (f : NK.BrauerTwist.LevelH2 p U L ⟶ NK.BrauerTwist.LocalLevelH2 p U A L') => f a) hsq
  simpa [CategoryTheory.comp_apply] using hApp

end NK.BrauerTwist

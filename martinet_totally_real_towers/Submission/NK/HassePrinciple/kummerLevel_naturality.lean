/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Naturality of the Kummer morphism between the level systems

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4 item 1, §10.4).

The Kummer morphism of this chapter is level-wise

`kummerLevel p V L : MuLevelH2 p V L ⟶ UnitsLevelH2 V L`,

the map `H²(LevelGroup V L, μ_p(L)) → H²(LevelGroup V L, Lˣ)` induced by the coefficient inclusion
`μ_p(L) ↪ Lˣ` (`KummerLevel.lean`).  This file proves that it is **natural** with respect to the
transition morphisms `muLevelMap p V h` and `unitsLevelMap V h` of the two level systems
(`MuLevelMap.lean`, `exists_unitsLevelMapCoeff.lean`):

`kummerLevel p V L ≫ unitsLevelMap V h = muLevelMap p V h ≫ kummerLevel p V L'`  (`h : L ≤ L'`).

That is the compatibility which makes the Kummer morphism descend to the colimits of the level
systems, `MuColimit V → H2Units V` (README §10.4, `UnitsColimit.lean`).

The mathematical content is the commutation of the *coefficient* inclusions with the transition
maps: the square

```
res(levelQuotHom h)(μ_p(L)) -- res(muToUnits) --> res(levelQuotHom h)(Lˣ)
   | muLevelMapCoeff                                    | unitsLevelMapCoeff
   v                                                    v
μ_p(L')        ---- muToUnits ------>                 L'ˣ
```

whose two ways around send an element of `μ_p(L)` to the unit of `L'` obtained by transporting its
underlying root of unity along `L ≤ L'`; both the `μ_p` inclusion and the unit inclusion are built
from the same `IntermediateField.inclusion`, so the two composites coincide
(`muToUnits_naturality`).  The statement about the `H²`s then follows from
`groupCohomology.map_comp` on each side and `groupCohomology.map_congr`.
-/

import Mathlib
import Submission.NK.HassePrinciple.KummerLevel
import Submission.NK.HassePrinciple.MuLevelMap
import Submission.NK.HassePrinciple.unitsLevelMap_refl

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u

namespace NK.HassePrinciple

open CategoryTheory Representation

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **Coherence of the coefficient inclusions**: the square

```
res(levelQuotHom h)(μ_p(L)) -- res(muToUnits) --> res(levelQuotHom h)(Lˣ)
   | muLevelMapCoeff                                    | unitsLevelMapCoeff
   v                                                    v
μ_p(L')        ---- muToUnits ------>                 L'ˣ
```

commutes.  Both composites have the same underlying map: an element of `μ_p(L)` goes to the unit of
`L'` obtained by transporting its underlying root of unity along the inclusion `L ≤ L'` (and the two
coefficient inclusions `μ_p(L) ↪ μ_p(L')` and `Lˣ ↪ L'ˣ` are both built from
`IntermediateField.inclusion`). -/
theorem muToUnits_naturality (p : ℕ) (V : Subgroup Gal(K'/K))
    {L L' : FiniteGaloisIntermediateField K K'}
    (h : (L : IntermediateField K K') ≤ (L' : IntermediateField K K')) :
    (Rep.resMap (levelQuotHom (U := V) h) (muToUnits p V L) ≫ unitsLevelMapCoeff V h)
      = (Rep.resMap (MonoidHom.id (LevelGroup V L')) (muLevelMapCoeff p V h)
          ≫ muToUnits p V L') := by
  apply Rep.hom_ext
  ext x
  change Additive.ofMul (unitsInclHom L L' h ((Additive.toMul x : ↥(rootsOfUnity p ↥L)) : (↥L)ˣ))
      = Additive.ofMul (unitsInclHom L L' h ((Additive.toMul x : ↥(rootsOfUnity p ↥L)) : (↥L)ˣ))
  rfl

/-- **Naturality of the Kummer morphism in the level**: the Kummer morphisms
`kummerLevel p V L : H²(LevelGroup V L, μ_p(L)) → H²(LevelGroup V L, Lˣ)` commute with the
transition maps of the `μ_p` and the units level systems,

`kummerLevel p V L ≫ unitsLevelMap V h = muLevelMap p V h ≫ kummerLevel p V L'`  (`h : L ≤ L'`),

so that the Kummer morphism descends to the colimits `lim H²(·, μ_p) → lim H²(·, ·ˣ)`.

Both sides are `groupCohomology.map` of the same inflation hom `levelQuotHom h` along the two
composites of coefficient inclusions, which agree by `muToUnits_naturality`; the identification is
`groupCohomology.map_comp` on each side and `groupCohomology.map_congr`. -/
theorem kummerLevel_naturality {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) (V : Subgroup (K' ≃ₐ[K] K')) {L L' : FiniteGaloisIntermediateField K K'}
    (h : (L : IntermediateField K K') ≤ (L' : IntermediateField K K')) :
    CategoryTheory.CategoryStruct.comp (NK.HassePrinciple.kummerLevel p V L)
        (NK.HassePrinciple.unitsLevelMap V h) =
      CategoryTheory.CategoryStruct.comp (NK.HassePrinciple.muLevelMap p V h)
        (NK.HassePrinciple.kummerLevel p V L') := by
  -- Both sides are `groupCohomology.map` of the *same* inflation `levelQuotHom h`; unfold the
  -- level maps and pull the coefficient inclusions out of `groupCohomology.map` via `map_comp`.
  simp only [kummerLevel, unitsLevelMap, muLevelMap]
  have h1 := groupCohomology.map_comp (A := muLevelRep p V L) (B := unitsLevelRep V L)
      (C := unitsLevelRep V L') (MonoidHom.id (LevelGroup V L)) (levelQuotHom (U := V) h)
      (muToUnits p V L) (unitsLevelMapCoeff V h) 2
  have h2 := groupCohomology.map_comp (A := muLevelRep p V L) (B := muLevelRep p V L')
      (C := unitsLevelRep V L') (levelQuotHom (U := V) h) (MonoidHom.id (LevelGroup V L'))
      (muLevelMapCoeff p V h) (muToUnits p V L') 2
  rw [← h1, ← h2]
  -- It remains to compare the two composites of coefficient inclusions, which is
  -- `muToUnits_naturality` (both are the transport of a root of unity along `L ≤ L'`).
  refine groupCohomology.map_congr (A := muLevelRep p V L) (B := unitsLevelRep V L')
    (f := (MonoidHom.id (LevelGroup V L)).comp (levelQuotHom (U := V) h))
    (g := (levelQuotHom (U := V) h).comp (MonoidHom.id (LevelGroup V L')))
    (φ := (Rep.resFunctor (levelQuotHom (U := V) h)).map (muToUnits p V L)
      ≫ unitsLevelMapCoeff V h)
    (ψ := (Rep.resFunctor (MonoidHom.id (LevelGroup V L'))).map (muLevelMapCoeff p V h)
      ≫ muToUnits p V L') ?_ ?_ 2
  · -- the two group homs are the same: `levelQuotHom h` composed with identities
    ext x
    rfl
  · -- the two composites of coefficient inclusions agree elementwise
    ext x
    change Additive.ofMul (unitsInclHom L L' h ((Additive.toMul x : ↥(rootsOfUnity p ↥L)) : (↥L)ˣ))
        = Additive.ofMul (unitsInclHom L L' h ((Additive.toMul x : ↥(rootsOfUnity p ↥L)) : (↥L)ˣ))
    rfl

end NK.HassePrinciple

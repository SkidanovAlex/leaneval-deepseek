/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Restriction of profinite cohomology `H²(·, Z/p)` along an inclusion of closed subgroups

For an inclusion `V ≤ U` of closed subgroups of `Gal(K'/K)` there is a *restriction* map

`H²(U, Z/p) ⟶ H²(V, Z/p)`,

induced level-wise by the quotient maps `V/(V ∩ Gal(K'/L)) →* U/(U ∩ Gal(K'/L))` and
passing to the colimit.  The point of this file is that these level-wise maps are compatible
with the inflation maps `levelMap`, so that they descend to the filtered colimit
`H2Profinite p U`; this is the content of `H2Profinite.lift`.

## Main results

* `NK.BrauerHasse.levelQuotHom_comp_levelInclHom` — the square expressing that the
  inclusion of level groups is a morphism of filtered systems;
* `NK.BrauerHasse.exists_restriction_map` — existence of the restriction map, characterised
  by its values on the finite levels.
-/

import Mathlib
import Submission.NK.BrauerHasse.Profinite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.BrauerHasse

set_option autoImplicit false

universe u

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The inclusion of the level groups `V/(V ∩ Gal(K'/L)) →* U/(U ∩ Gal(K'/L))` for `V ≤ U`
is compatible with the quotient maps `levelQuotHom` defining the transition maps of the two
filtered systems: the square

```
V/(V ∩ Gal(K'/L')) --levelQuotHom--> V/(V ∩ Gal(K'/L))
     |                                   |
levelInclHom                        levelInclHom
     v                                   v
U/(U ∩ Gal(K'/L')) --levelQuotHom--> U/(U ∩ Gal(K'/L))
```

commutes.  This is what makes the level-wise restriction maps compatible with inflation. -/
lemma levelQuotHom_comp_levelInclHom {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    {L L' : FiniteGaloisIntermediateField K K'} (hLL' : L ≤ L') :
    (levelQuotHom (U := U) hLL').comp (levelInclHom h L') =
      (levelInclHom h L).comp (levelQuotHom (U := V) hLL') := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H y => rfl

/-- **Existence of the restriction map.**  For an inclusion `V ≤ U` of closed subgroups of
`Gal(K'/K)` there is a map `H²(U, Z/p) → H²(V, Z/p)` whose value on the class of a finite
level `H²(U/(U ∩ Gal(K'/L)), Z/p)` is given by the level-wise restriction
`H2.map (levelInclHom h L)`. -/
theorem exists_restriction_map {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U) :
    ∃ f : NK.BrauerHasse.H2Profinite p U → NK.BrauerHasse.H2Profinite p V,
      ∀ (L : FiniteGaloisIntermediateField K K') (a : NK.BrauerHasse.LevelH2 p U L),
        f (NK.BrauerHasse.H2Profinite.ofLevel L a) =
          NK.BrauerHasse.H2Profinite.ofLevel L
            ((NK.BrauerHasse.H2.map (NK.BrauerHasse.levelInclHom h L)) a) := by
  refine ⟨H2Profinite.lift (p := p) (U := U)
      (fun L a => H2Profinite.ofLevel (U := V) L ((H2.map (levelInclHom h L)) a)) ?_, ?_⟩
  · -- Compatibility of the level-wise restriction maps with the inflation maps.
    intro L L' hLL' a
    rw [levelMap_apply]
    rw [← CategoryTheory.comp_apply, ← H2.map_comp,
        levelQuotHom_comp_levelInclHom h hLL', H2.map_comp, CategoryTheory.comp_apply]
    exact H2Profinite.ofLevel_levelMap (p := p) (U := V) hLL' _
  · intro L a
    rfl

end NK.BrauerHasse

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The cardinality of a level group is the degree of the level extension

`NK.BrauerHasse.LevelGroup V L = V ⧸ (V ⊓ Gal(K'/L))` is, by the level dictionary
(`Submission/Work/HassePrinciple/LevelDictionary.lean`), the Galois group of the finite extension

  `L / (L ⊓ K'^V) = L / fixedField (V.map (levelRestrict L))`

of number fields.  This module records the resulting cardinality statement

`Nat.card (LevelGroup V L) = [L : L ⊓ K'^V]`,

i.e. the level group has as many elements as the extension `L / L ⊓ K'^V` has degree.  It is the
form in which the level group is used as a *number* (e.g. when comparing the order of a level group
with the order of a local level group, or with the cardinality of `H²` computed by the cyclic
computations of the chapter).

## Proof

The level dictionary gives an isomorphism of groups

`LevelGroup V L ≃* Gal(L / fixedField (V.map (levelRestrict L)))`

(`NK.HassePrinciple.levelGroupMulEquivLevelGalois`), and for a finite Galois extension the
cardinality of its Galois group is the degree of the extension
(`IsGalois.card_aut_eq_finrank`).  The extension `L / fixedField (V.map (levelRestrict L))` is
Galois because it is the extension of a field by the finite group of automorphisms
`V.map (levelRestrict L) ≤ Gal(L/K)` (Mathlib's instance `IntermediateField.fixedField`), and
finite dimensional because `L/K` is (`FiniteGaloisIntermediateField`).
-/

import Mathlib
import Submission.NK.HassePrinciple.LevelDictionary

universe u

namespace NK.HassePrinciple

theorem natCard_levelGroup {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (V : Subgroup (K' ≃ₐ[K] K')) (L : FiniteGaloisIntermediateField K K') :
    Nat.card (NK.BrauerHasse.LevelGroup V L) =
      Module.finrank ↥(IntermediateField.fixedField (V.map (NK.HassePrinciple.levelRestrict L))) ↥L := by
  rw [Nat.card_congr (NK.HassePrinciple.levelGroupMulEquivLevelGalois V L).toEquiv]
  exact IsGalois.card_aut_eq_finrank _ _

end NK.HassePrinciple

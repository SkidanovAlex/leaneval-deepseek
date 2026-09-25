/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Decomposition subgroups are placement data

Umbrella development: `Submission/Work/HassePrinciple/` (README §20.3, §21).

The Hasse-principle chapter studies, for a closed subgroup `U ≤ Gal(K'/K)`, the *fine* local
groups

`LocalLevelGroup U A L = (U ⊓ D_A) / ((U ⊓ D_A) ⊓ Gal(K'/L))`

at the places `A` of `K'` over the finite primes of `K` (`D_A = stabSubgroup A`).  The classical
theorems of the chapter (`NK.HassePrinciple.HBNUnits`, hence everything derived from the licensed
cyclic input) localise instead at the *stabilisers*

`MulAction.stabilizer Gal(L/K) w`  (`w : Place L`)

of the places of a finite Galois extension `L/K` of number fields.  For a general closed `U` these
two local groups differ (README §14.6, §20.2); the identification is exactly the content of the
*placement* of the decomposition subgroups, and it is the missing formal step of the finite-index
(`U` open) boundary case of the Hasse principle (README §21).

This module sets up the vocabulary of that comparison: the stabiliser `valuationStab A` of a
valuation subring `A` of a field `L` under the pointwise action of `L ≃ₐ[K] L`, which is the form in
which the decomposition subgroups appear on the `ValuationSubring` side of the chapter, together
with the statement (`NK.HassePrinciple.map_levelRestrict_stabSubgroup`) that restricting a
decomposition group of `K'` to a finite Galois level `L` gives the decomposition group of the
restricted place.
-/

import Submission.NK.HassePrinciple.LevelDictionary
import Mathlib.RingTheory.Valuation.ValuationSubring

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

/-- **The stabiliser of a valuation subring** under the pointwise action of the `K`-algebra
automorphisms of `L`: the decomposition group of the corresponding place, in the
`ValuationSubring` (rather than `Place`) parametrisation. -/
noncomputable abbrev valuationStab {K L : Type u} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  MulAction.stabilizer (L ≃ₐ[K] L) A

end NK.HassePrinciple

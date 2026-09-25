/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The level groups coincide cofinally only at an inert place

Umbrella development: `Submission/Work/HassePrinciple/` (README §14.6).

The fine local group of a closed subgroup `U ≤ Gal(K'/K)` at a place `A` and a level `L` is
`(U ⊓ D_A)/((U ⊓ D_A) ∩ Gal(K'/L))`, whereas the level group is `U/(U ∩ Gal(K'/L))`.  The two
coincide exactly when `U ≤ D_A ⊔ Gal(K'/L)`.  This module records the profinite fact that pins down
the *only* way this can happen cofinally:

```lean
NK.HassePrinciple.iInf_sup_fixingSubgroup_eq_stabSubgroup :
  (⨅ L : FiniteGaloisIntermediateField K K', (D_A ⊔ Gal(K'/L))) = D_A
```

i.e. `⋂_L D_A·Gal(K'/L) = D_A` (proved in
`Submission/Work/HassePrinciple/iInf_sup_fixingSubgroup_eq_stabSubgroup.lean`), and its
consequence:

```lean
NK.HassePrinciple.le_stabSubgroup_of_forall_le_sup_fixingSubgroup :
  (∀ L, U ≤ D_A ⊔ Gal(K'/L)) → U ≤ D_A
```

So the level-wise coincidence at *all* levels — equivalently, by downward closure, at cofinally
many levels — forces `U` to be contained in the decomposition group of `A`: it happens only at an
*inert* place.  This is the formal content of README §14.6: the finite-level (and level-wise) route
to the surjectivity of the localisation produces the level-wise bijection only from Neukirch's own
conclusion `U ≤ D_A`, which is why the Hasse principle cannot be obtained from the finite-case
theorem `NK.HassePrinciple.hbnUnits_of_cyclicInput` and why the chapter's input is stated in the
dual (surjectivity) form.
-/

import Submission.NK.HassePrinciple.iInf_sup_fixingSubgroup_eq_stabSubgroup

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The level-wise coincidence of the local and global level groups forces inertness.**  If for
every finite Galois level `L` the subgroup `U` is contained in `D_A · Gal(K'/L)`, then `U ≤ D_A`:
by `iInf_sup_fixingSubgroup_eq_stabSubgroup`, the intersection over the levels is exactly `D_A`.
Equivalently: `(U ⊓ D_A)/((U ⊓ D_A) ∩ Gal(K'/L)) = U/(U ∩ Gal(K'/L))` for all `L` only if `U` is
contained in the decomposition group of `A` — the obstruction recorded in README §14.6. -/
theorem le_stabSubgroup_of_forall_le_sup_fixingSubgroup {U : Subgroup Gal(K'/K)}
    (A : ValuationSubring K')
    (h : ∀ L : FiniteGaloisIntermediateField K K', U ≤ stabSubgroup A ⊔ L.fixingSubgroup) :
    U ≤ stabSubgroup A := by
  rw [← iInf_sup_fixingSubgroup_eq_stabSubgroup (K := K) (K' := K') A]
  exact le_iInf h

end NK.HassePrinciple

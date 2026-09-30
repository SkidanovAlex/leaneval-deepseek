/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A `k`-basis of `k'` indexed by the Galois group

For a finite Galois extension `k'/k` the Galois group has `[k' : k]` elements, so `k'` has a
`k`-basis indexed by `Gal k k'`.  This is the input for the "dual coefficient" lemmas of
`Submission/Work/Descent/exists_coeffs_left.lean` and `exists_coeffs_right.lean`, which in turn are
the linear-algebra input for Speiser's lemma.
-/
import Submission.Work.Descent.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

namespace Work.Descent

/-- A `k`-basis of `k'` indexed by the Galois group, for a finite Galois extension `k'/k`. -/
noncomputable def galoisBasis (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] : Module.Basis (Gal k k') k k' :=
  (Module.finBasis k k').reindex
    (Fintype.equivFinOfCardEq (by
      rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank])).symm

@[simp] lemma galoisBasis_repr_self (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (σ : Gal k k') :
    galoisBasis k k' σ = (Module.finBasis k k') (Fintype.equivFinOfCardEq (by
      rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]) σ) := by
  rw [galoisBasis, Module.Basis.reindex_apply, Equiv.symm_symm]

end Work.Descent

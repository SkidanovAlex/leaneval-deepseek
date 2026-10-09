/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The cardinality of the inertia subgroup

For a finite Galois extension `L/K` of number fields and a finite prime `w` of `L` lying over a
finite prime `v` of `K`, the inertia subgroup `I_w ≤ D_w` has cardinality equal to the
ramification index of `v` in `L`:
`#I_w = e(w/v)`.

This is the standard exact sequence
`1 → I_w → D_w → Gal(κ_w/κ_v) → 1`
together with `#D_w = e · f` and `#Gal(κ_w/κ_v) = f`.  Formally it is an immediate consequence of
Mathlib's `Ideal.card_inertia_eq_ramificationIdxIn` (applied to the extension of rings of integers
`𝓞 K → 𝓞 L`) together with the fact that `I_w` is computed inside `D_w` as the inertia subgroup of
`w` in `Gal(L/K)`.
-/
import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

theorem card_inertiaSubgroup {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    Nat.card (Work.LocalFields.inertiaSubgroup K w) =
      v.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) := by
  -- `I_w` is the inertia subgroup of `w` in `Gal(L/K)`, computed inside the decomposition group
  -- `D_w = MulAction.stabilizer Gal(L/K) w`, and `subgroupOf` does not change the cardinality.
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (Ideal.inertia_le_stabilizer (M := Gal(L/K)) w.asIdeal)).toEquiv]
  -- The inertia subgroup of `w` in `Gal(L/K)` has cardinality the ramification index of `v` in
  -- `𝓞 L`, by the fundamental identity for the extension `𝓞 K → 𝓞 L`.
  exact Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) v.asIdeal w.asIdeal

end Work.LocalFields

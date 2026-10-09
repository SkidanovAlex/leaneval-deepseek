import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Pointwise Valued WithZero

/-- A finite prime `w` of `L` is unramified over `K` (i.e. its inertia subgroup `I_w`, as a
subgroup of the decomposition group `D_w`, is trivial) if and only if the inertia subgroup of
`w` inside the full Galois group `Gal(L/K)` is trivial.

This is the translation between the bundled definition `IsUnramifiedAt` (which uses
`inertiaSubgroup K w = (Ideal.inertia Gal(L/K) w.asIdeal).subgroupOf (decompositionGroup K w)`)
and the "absolute" statement `Ideal.inertia Gal(L/K) w.asIdeal = ⊥`.  The two are equivalent
because `Ideal.inertia Gal(L/K) w.asIdeal ≤ decompositionGroup K w`
(`Ideal.inertia_le_stabilizer`), so the `subgroupOf` has no effect on triviality. -/
theorem unramifiedAt_iff_inertia_eq_bot {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (w : Work.LocalFields.FinitePrime L) :
    Work.LocalFields.IsUnramifiedAt K w ↔ Ideal.inertia Gal(L/K) w.asIdeal = ⊥ := by
  have hle : Ideal.inertia Gal(L/K) w.asIdeal ≤ decompositionGroup K w :=
    Ideal.inertia_le_stabilizer w.asIdeal
  change (Ideal.inertia Gal(L/K) w.asIdeal).subgroupOf (decompositionGroup K w) = ⊥ ↔
    Ideal.inertia Gal(L/K) w.asIdeal = ⊥
  rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hle]

end Work.LocalFields

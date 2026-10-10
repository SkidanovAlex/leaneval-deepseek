import Mathlib.NumberTheory.RamificationInertia.Galois
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

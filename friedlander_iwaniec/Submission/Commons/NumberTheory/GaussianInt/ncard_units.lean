import Mathlib.Data.Set.Card
import Submission.Commons.NumberTheory.GaussianInt.units_classification

namespace Commons.NumberTheory.GaussianInt

/-- The Gaussian integers have exactly four units, namely `±1` and `±i`: the set
`{z : ℤ[i] | IsUnit z}` has cardinality `4`.

This is the `ncard` (cardinality of a set as a natural number, with junk value `0`
for infinite sets) form of `units_classification`, packaged as an explicit finite
enumeration of the units. -/
theorem ncard_units : ({z : GaussianInt | IsUnit z}).ncard = 4 := by
  -- Rewrite the set of units as an explicit finset.
  have hset : {z : GaussianInt | IsUnit z} =
      ({(1 : GaussianInt), -1, (⟨0, 1⟩ : GaussianInt), (⟨0, -1⟩ : GaussianInt)} :
        Finset GaussianInt) := by
    ext z
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    rw [units_classification z]
  rw [hset, Set.ncard_coe_finset]
  decide

end Commons.NumberTheory.GaussianInt
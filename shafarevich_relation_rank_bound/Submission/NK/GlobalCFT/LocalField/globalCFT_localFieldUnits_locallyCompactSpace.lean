import Mathlib
import Submission.NK.GlobalCFT.Place

/-!
# The local unit group `K_vˣ` of a number field is locally compact

For a number field `K` and a place `v` of `K`, the completion `K_v` is a locally compact
field: at an archimedean place `K_v` is `ℝ` or `ℂ`, at a nonarchimedean place `K_v` is the
`v`-adic completion, whose ring of integers `𝒪_v` is compact (it is complete, a discrete
valuation ring, with finite residue field), so that `K_v` is a proper, hence locally compact,
valued field.

Consequently the group of units `K_vˣ` — an open subgroup of `K_v` — is locally compact.
This is the local input for the restricted direct product `𝕀_K = ∏'_v K_vˣ` defining the
idèle group.
-/

open scoped Valued

set_option linter.style.haveILetI false

namespace NK.GlobalCFT.LocalField

theorem globalCFT_localFieldUnits_locallyCompactSpace {K : Type*} [Field K] [NumberField K]
    (v : NK.GlobalCFT.Place K) :
    LocallyCompactSpace ((NK.GlobalCFT.Place.localField K v)ˣ) := by
  cases v with
  | inl w => infer_instance
  | inr q =>
      -- The ring of integers of `K_v` is compact.
      haveI hInt : CompactSpace (q.adicCompletionIntegers K) :=
        Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers K q
      -- Rephrase it as compactness of `𝒪[K_v]` (`Valued.integer`).
      haveI : CompactSpace ↥𝒪[q.adicCompletion K] := hInt
      -- A valued field with compact valuation ring is proper, hence locally compact.
      haveI : ProperSpace (q.adicCompletion K) :=
        (Valued.integer.properSpace_iff_compactSpace_integer
          (K := q.adicCompletion K)).mpr inferInstance
      -- Units of a locally compact topological monoid are locally compact.
      infer_instance

end NK.GlobalCFT.LocalField

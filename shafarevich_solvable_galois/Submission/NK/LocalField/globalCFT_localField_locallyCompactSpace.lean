/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.Place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local compactness of the local fields `K_v`

For a number field `K` and a place `v` of `K`, the completion `K_v` is a locally compact
topological field: at an archimedean place it is `ℝ` or `ℂ`, and at a nonarchimedean place
its ring of integers `𝒪_v` is compact (it is a complete discrete valuation ring with finite
residue field), which exhibits `K_v` as a proper space.

## Main results

* `NK.LocalField.locallyCompactSpace_adicCompletion`: `K_v` is locally compact at a finite
  place.
* `NK.LocalField.globalCFT_localField_locallyCompactSpace`: `K_v` is locally compact at every
  place `v` of `K`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped WithZero

noncomputable section

namespace NK.LocalField

/-- The completion of a number field at a finite place is locally compact: its ring of integers
`𝒪_v` is compact (being a complete discrete valuation ring with finite residue field), so `K_v`
is a proper space. -/
theorem locallyCompactSpace_adicCompletion {K : Type*} [Field K] [NumberField K]
    (q : HeightOneSpectrum (𝓞 K)) :
    LocallyCompactSpace (q.adicCompletion K) := by
  have h : CompactSpace (Valued.integer (q.adicCompletion K)) := by
    have := Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers K q
    change CompactSpace (q.adicCompletionIntegers K)
    infer_instance
  have : ProperSpace (q.adicCompletion K) :=
    Valued.integer.properSpace_iff_compactSpace_integer.mpr h
  infer_instance

theorem globalCFT_localField_locallyCompactSpace {K : Type*} [Field K] [NumberField K]
    (v : NK.GlobalCFT.Place K) :
    LocallyCompactSpace (NK.GlobalCFT.Place.localField K v) := by
  cases v with
  | inl w => exact inferInstance
  | inr q => exact locallyCompactSpace_adicCompletion q

end NK.LocalField

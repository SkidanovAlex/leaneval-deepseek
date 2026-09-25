/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `p = 2` route, unconditionally: the comparison is a theorem

`NK.IndecomposedDeep.twistTwoComparison`
(`Submission/Work/IndecomposedDeep/twistTwoComparison.lean`) proves that the twisted and
trivial-coefficient cohomology theories agree at `p = 2`
(`NK.IndecomposedDeep.TwistTwoComparison`), so the `p = 2` route needs no extra input:

* `NK.IndecomposedDeep.rankDataTrivial_two_of_deepInputs` — the twisted catalogue `DeepInputs 2`
  alone produces `NK.Indecomposed.RankDataTrivial 2 K K' κ κ'`;
* `NK.IndecomposedDeep.indecomposedPrime_two_of_deepInputs` — end to end, with the local
  reconstruction at `p = 2`, it produces `NK.LocalDecomposition.IndecomposedPrime 2 K K' κ κ'`
  through the on-disk `NK.Indecomposed.indecomposedPrime_two_of_rankData`.
-/

import Submission.NK.IndecomposedDeep.TrivialTwo
import Submission.NK.IndecomposedDeep.twistTwoComparison

open IsDedekindDomain.HeightOneSpectrum

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.IndecomposedDeep

variable {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The trivial-coefficient rank data at `p = 2` from the twisted catalogue alone.**

The comparison of the two coefficient theories at `p = 2` is a theorem
(`NK.IndecomposedDeep.twistTwoComparison`), so `NK.IndecomposedDeep.DeepInputs 2` — the twisted
catalogue of this chapter, instantiated at `p = 2` — produces `NK.Indecomposed.RankDataTrivial 2`,
which is what the `p = 2` consumer `NK.Indecomposed.indecomposedPrime_two_of_rankData` expects. -/
theorem rankDataTrivial_two_of_deepInputs (h : DeepInputs 2 K K' κ κ') :
    NK.Indecomposed.RankDataTrivial 2 K K' κ κ' :=
  rankDataTrivial_two_of_comparison h (Classical.choice (twistTwoComparison K K'))

/-- **The `p = 2` consumer, end to end and unconditional.**

The twisted catalogue at `p = 2` together with the local reconstruction at `p = 2` produces
`NK.LocalDecomposition.IndecomposedPrime 2 K K' κ κ'`. -/
theorem indecomposedPrime_two_of_deepInputs (h : DeepInputs 2 K K' κ κ')
    (hrec : NK.Indecomposed.LocalReconstruction 2 K K' κ κ') :
    NK.LocalDecomposition.IndecomposedPrime 2 K K' κ κ' :=
  NK.Indecomposed.indecomposedPrime_two_of_rankData (K := K) (K' := K') (κ := κ) (κ' := κ')
    (rankDataTrivial_two_of_deepInputs h) hrec

end NK.IndecomposedDeep

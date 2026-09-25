/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `isTameInertia` for the corrected wild inertia

The field `isTameInertia` of `NK.TameData.TameInertiaInput` says that `I_κ/V_κ` is the maximal
closed normal pro-cyclic subgroup of `G_κ^{tr} = G_κ/V_κ`.  For the corrected wild inertia
`V_κ = Gal(K'/κ^{tr}) = Tame.correctedWildInertia p π` this is a **theorem** of this chapter: all
four conjuncts of `NK.LocalTame.IsMaxNormalProCyclicInQuotient` are proved

* `Tame.correctedWildInertia_le_inertia` (`V_κ ≤ I_κ`),
* `Support.quotientImage_normal_iff` + `I_κ ◁ G_κ` (`I_κ/V_κ ◁ G_κ/V_κ`),
* `Tame.isProCyclic_correctedWildInertia` (`I_κ/V_κ` pro-cyclic),
* `Tame.isMaximal_correctedWildInertia` (maximality),

see `NK.TameStructureDeep.Tame.isMaxNormalProCyclicInQuotient_correctedWildInertia` below.
The passage from the corrected `V_κ` to the *join* `NK.LocalTame.wildInertiaSubgroup p`, which is
what `TameInertiaInput` is stated for, is the identity `V_κ = wildInertiaSubgroup p` of README
§7.2(b)/(c): the join is `≤ V_κ` (every normal pro-`p` subgroup meets `T = I_κ/V_κ` trivially in a
pro-`p` group, and `V_κ ≤ I_κ`), and conversely `V_κ` is pro-`p`.
-/
import Mathlib
import Submission.NK.TameStructureDeep.Tame.CorrectedResidual
import Submission.NK.TameStructureDeep.Tame.isMaximal_correctedWildInertia
import Submission.NK.TameStructureDeep.Support.quotientImage_normal_iff

open scoped Classical

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
  [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']

/-- **`isTameInertia` for the corrected wild inertia.**  `I_κ/V_κ` *is* the maximal closed normal
pro-cyclic subgroup of `G_κ/V_κ`, for `V_κ = Gal(K'/κ^{tr})`.  This is the field `isTameInertia` of
`NK.TameData.TameInertiaInput`, proved with the corrected `V_κ`; composing with the identity
`V_κ = NK.LocalTame.wildInertiaSubgroup p` (README §7.2(b)/(c)) gives it for the join. -/
theorem isMaxNormalProCyclicInQuotient_correctedWildInertia {π : 𝔭.adicCompletionIntegers K}
    (hπ : IsUniformizerAt 𝔭 π)
    [hV : (correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)
      (π : 𝔭.adicCompletion K)).Normal] :
    NK.LocalTame.IsMaxNormalProCyclicInQuotient
      (correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)
        (π : 𝔭.adicCompletion K))
      (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
        (resCharAt 𝔭)) := by
  have hle := correctedWildInertia_le_inertia (K' := K') (resCharAt 𝔭) (π : 𝔭.adicCompletion K)
  refine ⟨hle, ?_, ?_, ?_⟩
  · exact (NK.TameStructureDeep.Support.quotientImage_normal_iff hle).mpr inferInstance
  · exact isProCyclic_correctedWildInertia 𝔭 hπ
  · exact isMaximal_correctedWildInertia 𝔭 hπ

end

end NK.TameStructureDeep.Tame

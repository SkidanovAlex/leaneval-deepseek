import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.TameStructureDeep.Tame.isMaximal_correctedWildInertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

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

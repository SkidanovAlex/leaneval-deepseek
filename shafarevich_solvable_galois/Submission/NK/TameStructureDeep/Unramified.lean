import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Submission.NK.TameStructureDeep.Degree.galoisGroup_unramifiedClosure_mulEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical

namespace NK.TameStructureDeep

universe u

noncomputable section

/-- **The unramified quotient of a `𝔭`-adic field is `Ẑ`**: `Gal(K'/κ) ⧸ I_κ ≅ Ẑ`.  This is the
field `unramifiedQuotient` of the residual, proved. -/
theorem unramifiedQuotient_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] :
    Nonempty ((Gal(K'/𝔭.adicCompletion K) ⧸
        NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
          (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)))) ≃*
      NK.LocalAnabelian.Zhat) := by
  obtain ⟨e⟩ :=
    NK.LocalAnabelian.ResidueField.quotient_inertiaSubgroup_mulEquiv_unramifiedClosure
      (κ := 𝔭.adicCompletion K) (K' := K')
      (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)))
      (NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure
        (κ := 𝔭.adicCompletion K) (K' := K')
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))))
  obtain ⟨e'⟩ := Degree.galoisGroup_unramifiedClosure_mulEquiv (K := K) 𝔭 (K' := K')
  exact ⟨e.trans e'⟩

end

end NK.TameStructureDeep

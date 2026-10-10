import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.NUV2.normGroup_quadratic_faithful_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Summary.NUV2

/-- **The minimal case of Hasse's Normensatz**: two *distinct* quadratic levels of
`F = Q.adicCompletion K` have distinct norm groups.  See `NOTES.md` in this directory: over the
whole lattice of levels, (A2) is now known for pairs inside a cyclic envelope, for coprime-degree
pairs and at tower levels, so this is the first configuration left; equivalently it is the
non-degeneracy of the Kummer/Hilbert pairing `Fˣ/(Fˣ)² × Fˣ/(Fˣ)² → μ₂` for `n = 2`. -/
theorem normGroup_quadratic_faithful {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L₁ L₂ : IntermediateField (Q.adicCompletion K)
      (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
        (SeparableClosure (Q.adicCompletion K))))
    [FiniteDimensional (Q.adicCompletion K) ↥L₁] [Normal (Q.adicCompletion K) ↥L₁]
    [FiniteDimensional (Q.adicCompletion K) ↥L₂] [Normal (Q.adicCompletion K) ↥L₂]
    (h₁ : Module.finrank (Q.adicCompletion K) ↥L₁ = 2)
    (h₂ : Module.finrank (Q.adicCompletion K) ↥L₂ = 2)
    (hne : L₁ ≠ L₂) :
    NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L₁
      ≠ NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L₂ :=
  NK.NUV2.normGroup_quadratic_faithful_anyPlace Q L₁ L₂ h₁ h₂ hne

end NK.Summary.NUV2

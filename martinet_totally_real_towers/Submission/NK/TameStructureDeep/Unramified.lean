/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The unramified quotient of a `𝔭`-adic field is `Ẑ`

`NK.TameStructureDeep.unramifiedQuotient_adicCompletion`: for every number field `K`, every
finite prime `𝔭` and every separable closure `K'` of `κ = K_𝔭`,

  `G_κ ⧸ I_κ ≅ Gal(κ^ur/κ) ≅ Ẑ`.

This is the field `unramifiedQuotient` of the residual `NK.TameStructureDeep.TameRamificationCore`,
*proved*: the arithmetic content `Gal(κ^ur/κ) ≅ Ẑ` is
`NK.TameStructureDeep.Degree.galoisGroup_unramifiedClosure_mulEquiv` (from the cyclotomic
computation `[κ(ζ_n) : κ] = ord_n(q)` of `Degree/`), and the Galois-correspondence bridge
`NK.LocalAnabelian.ResidueField.quotient_inertiaSubgroup_mulEquiv_unramifiedClosure` is the
proved identification of `G_κ ⧸ I_κ` with `Gal(κ(μ_{p'})/κ)`.
-/
import Submission.NK.TameStructureDeep.Degree.galoisGroup_unramifiedClosure_mulEquiv
import Submission.NK.LocalAnabelian.ResidueField.quotient_inertiaSubgroup_mulEquiv_unramifiedClosure
import Submission.NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure

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

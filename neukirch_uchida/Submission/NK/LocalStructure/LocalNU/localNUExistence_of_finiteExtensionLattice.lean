import Mathlib
import Submission.NK.LocalStructure.Defs

namespace NK.LocalStructure.LocalNU

open scoped Classical Pointwise
open IsDedekindDomain.HeightOneSpectrum

universe u

/-- **The local Neukirch–Uchida existence theorem, reduced to the lattice input.**

`NK.LocalStructure.LocalNUExistence` (Neukirch, *Kennzeichnung der `p`-adischen und der
endlichen algebraischen Zahlkörper*, Invent. Math. **6** (1969), CoNF (12.1.4)–(12.1.5)) is
assembled here out of the two halves of the reduction recorded in
`Submission/Work/LocalStructure/Defs.lean`:

* `h : LocalFieldFromFiniteExtensionLattice` — Neukirch's Kennzeichnung in field-theoretic form:
  a `p`-adic field is determined by its lattice of finite extensions, i.e. by a
  `NK.LocalStructure.FiniteExtensionCorrespondence` along an isomorphism `Φ` of absolute Galois
  groups;
* `hcorr` — the *existence* of such a correspondence for every isomorphism `Φ` of absolute Galois
  groups of `p`-adic fields, i.e. the Galois-correspondence half of the reduction, proved in
  `NK.LocalStructure.LocalNU.finiteExtensionCorrespondence_of_groupIso`.

The statement of `LocalNUExistence` quantifies over an arbitrary finite extension `M` of
`𝔮.adicCompletion L` inside the separable closure `L'`; this is *verbatim* the setting of
`LocalFieldFromFiniteExtensionLattice`, so the assembly is the direct application of `h` at the
level `M = N` (the finite extension `M` of the goal) with the correspondence extracted from
`hcorr`. -/
theorem localNUExistence_of_finiteExtensionLattice
    (h : NK.LocalStructure.LocalFieldFromFiniteExtensionLattice.{u})
    (hcorr : ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
      (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
      [IsSepClosure (𝔮.adicCompletion L) L']
      (N : IntermediateField (𝔮.adicCompletion L) L') [FiniteDimensional (𝔮.adicCompletion L) ↥N]
      (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
      [IsSepClosure (𝔭.adicCompletion K) K']
      (Φ : Gal(L'/↥N) ≃* Gal(K'/𝔭.adicCompletion K)),
      Nonempty (NK.LocalStructure.FiniteExtensionCorrespondence Φ)) :
    NK.LocalStructure.LocalNUExistence.{u} := by
  rintro K L _ _ _ _ 𝔭 𝔮 L' _ _ _ M _ K' _ _ _ ⟨Φ⟩
  obtain ⟨C⟩ := hcorr K L 𝔭 𝔮 L' M K' Φ
  exact h K L 𝔭 𝔮 L' M K' Φ C

end NK.LocalStructure.LocalNU

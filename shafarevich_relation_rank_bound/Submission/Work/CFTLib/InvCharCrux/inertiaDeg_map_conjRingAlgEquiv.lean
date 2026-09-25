import Mathlib
import Submission.Work.CFTLib.InvCharCrux.ConjField

namespace Work.CFTLib.InvCharCrux

set_option linter.style.haveILetI false

/-- **The inertia degree over the bottom field is preserved by the isomorphism of the conjugate
field.**

Let `M : IntermediateField K K'`, `g : K' ≃ₐ[F] K'`, and let
`φ = Work.CFTLib.InvCharCrux.conjRingAlgEquiv g M : 𝓞 ↥M ≃ₐ[𝓞 F] 𝓞 ↥(conjField g M)` be the
`𝓞 F`-algebra isomorphism induced by `g` (see the module
`Submission.Work.CFTLib.InvCharCrux.ConjField`).  For a prime `P` of `𝓞 ↥M`, the inertia degree of
its image `P.map φ` over the bottom ring `𝓞 F` equals that of `P`.

Proof: `φ` induces an isomorphism of the residue fields of `P` and `P.map φ` over the residue
field of the common contraction `P.under (𝓞 F) = (P.map φ).under (𝓞 F)`
(`Ideal.residueFieldAlgEquiv'`), so the two `Module.finrank`s in the definition of
`Ideal.inertiaDeg` agree; see `Work.CFTLib.Transport.inertiaDegIn_algEquiv_eq` for a similar
computation. -/
theorem inertiaDeg_map_conjRingAlgEquiv {F K K' : Type} [Field F] [NumberField F] [Field K]
    [NumberField K] [Field K'] [NumberField K'] [Algebra F K] [Algebra F K'] [Algebra K K']
    [IsScalarTower F K K'] [FiniteDimensional F K] [FiniteDimensional F K'] [IsGalois F K]
    [IsGalois F K'] (g : K' ≃ₐ[F] K') (M : IntermediateField K K') [FiniteDimensional K M]
    [IsGalois K M] (P : Ideal (NumberField.RingOfIntegers ↥M)) [P.IsPrime] :
    (P.map (Work.CFTLib.InvCharCrux.conjRingAlgEquiv g M).toRingHom).inertiaDeg
        (NumberField.RingOfIntegers F)
      = P.inertiaDeg (NumberField.RingOfIntegers F) := by
  let φ := Work.CFTLib.InvCharCrux.conjRingAlgEquiv g M
  change (P.map φ).inertiaDeg (NumberField.RingOfIntegers F)
      = P.inertiaDeg (NumberField.RingOfIntegers F)
  let p : Ideal (NumberField.RingOfIntegers F) := P.under (NumberField.RingOfIntegers F)
  haveI hφprime : (P.map φ).IsPrime := Ideal.map_isPrime_of_equiv φ
  letI := Localization.AtPrime.algebraOfLiesOver p P
  letI := Localization.AtPrime.algebraOfLiesOver p (P.map φ)
  rw [Ideal.inertiaDeg_eq p (P.map φ), Ideal.inertiaDeg_eq p P]
  let e := Ideal.residueFieldAlgEquiv' p P (P.map φ) φ
    (Ideal.comap_map_of_bijective φ φ.bijective).symm
  exact e.toLinearEquiv.finrank_eq.symm

end Work.CFTLib.InvCharCrux

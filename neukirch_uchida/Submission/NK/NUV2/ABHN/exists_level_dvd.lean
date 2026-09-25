import Mathlib
import Submission.NK.HassePrinciple.MuColimit
import Submission.NK.TameStructureDeep.Tame.finrank_levelField

/-!
# A finite Galois level of `p`-divisible degree over a local field

For a number field `K`, a finite place `𝔮` of `K` and a prime `p`, the `𝔮`-adic completion
`κ = 𝔮.adicCompletion K` is a `p`-adic field, all of whose Galois extensions of degree
divisible by `p` exist: the maximal *unramified* extension of `κ` has Galois group `Ẑ`, so it has
a (cyclic) quotient of order `p`.  Concretely, if `q` denotes the cardinality of the residue
field of `κ`, then `κ⟮ζ_{q ^ p - 1}⟯` is unramified of degree `p` over `κ`.

That cyclotomic ("level") field is available in the workspace as
`NK.TameStructureDeep.Degree.levelField 𝔮 d`: the field `κ⟮ζ_{q ^ d - 1}⟯`, with

* `NK.TameStructureDeep.Degree.isGalois_levelField` — it is Galois over `κ`,
* `NK.TameStructureDeep.Tame.finrank_levelField` — its degree over `κ` is `d`.

Taking `d = p` (the field is realised inside `SeparableClosure κ`) gives the required finite
Galois intermediate field, of degree exactly `p`.  The same argument works for any `d ≥ 1`.
-/

namespace NK.NUV2.ABHN

open IsDedekindDomain

theorem exists_level_dvd
    (K : Type) [Field K] [NumberField K]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime) :
    ∃ L : FiniteGaloisIntermediateField (𝔮.adicCompletion K)
      (SeparableClosure (𝔮.adicCompletion K)),
      p ∣ Module.finrank (𝔮.adicCompletion K) ↥L := by
  haveI hpne : NeZero p := ⟨hp.ne_zero⟩
  -- the unramified level `κ⟮ζ_{q ^ p - 1}⟯`, realised in the separable closure of `κ`
  let A : IntermediateField (𝔮.adicCompletion K) (SeparableClosure (𝔮.adicCompletion K)) :=
    NK.TameStructureDeep.Degree.levelField 𝔮 p
  haveI hcyc : IsCyclotomicExtension {NK.TameStructureDeep.Degree.levelN 𝔮 p}
      (𝔮.adicCompletion K) ↥A :=
    NK.TameStructureDeep.Degree.isCyclotomicExtension_levelField 𝔮 p hp.ne_zero
  haveI hfd : FiniteDimensional (𝔮.adicCompletion K) ↥A :=
    IsCyclotomicExtension.finiteDimensional {NK.TameStructureDeep.Degree.levelN 𝔮 p}
      (𝔮.adicCompletion K) _
  haveI hgal : IsGalois (𝔮.adicCompletion K) ↥A :=
    NK.TameStructureDeep.Degree.isGalois_levelField 𝔮 p
  refine ⟨@FiniteGaloisIntermediateField.mk (𝔮.adicCompletion K)
      (SeparableClosure (𝔮.adicCompletion K)) _ _ _ A hfd hgal, ?_⟩
  change p ∣ Module.finrank (𝔮.adicCompletion K) ↥A
  rw [show Module.finrank (𝔮.adicCompletion K) ↥A = p from
    NK.TameStructureDeep.Tame.finrank_levelField 𝔮 p hp.ne_zero]

end NK.NUV2.ABHN

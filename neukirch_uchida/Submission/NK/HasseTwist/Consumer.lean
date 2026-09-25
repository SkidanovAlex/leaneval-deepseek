/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The endgame input (a) with the Hasse principle supplied by `Sha2Input`

This module is the *consumer-facing* form of the chapter: it is
`NK.BrauerTwist.preservesDecompositionGroups_of_localGalois` /
`NK.BrauerTwist.exists_place_of_localData` (the coefficient-corrected form of the endgame input
(a) of the Neukirch–Uchida development) with the per-prime Hasse principle
`NK.BrauerTwist.Sha2Vanishing` replaced by the *input catalogue* of this chapter.

The remaining hypotheses are

* `NK.BrauerTwist.LocalH2Input` — the local Brauer input `Br(κ)[p] ≅ Z/p` of local class field
  theory (unconditional for a `p`-adic `κ`, cf. `BrauerTwist/README.md` §4);
* **`NK.HasseTwist.Sha2Input`** — the inputs of this chapter (Hasse norm theorem, labelled
  level-wise Hasse–Brauer–Noether, exhaustion of the kernel), which yield
  `NK.BrauerTwist.Sha2Vanishing` by `NK.HasseTwist.sha2Vanishing`;
* `NK.BrauerTwist.LocalDecompositionCriterion` — Neukirch's local finishing step.
-/

import Submission.NK.HasseTwist.Main
import Submission.NK.BrauerTwist.Preserves

open scoped Pointwise

set_option autoImplicit false

universe u

namespace NK.HasseTwist

open NK.BrauerTwist

/-- **The place correspondence (the endgame input (a), local form) from the input catalogue.** -/
theorem exists_place_of_localData_of_sha2Input
    {K K' L L' : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field K'] [Field L'] [Algebra K K'] [Algebra L L']
    [IsSepClosure K K'] [IsSepClosure L L']
    (ϕ : Gal(K'/K) ≃* Gal(L'/L)) (he : IsHomeomorph ϕ)
    (h : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        ∃ p : ℕ, p.Prime ∧
          LocalH2Input p L L'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)) ∧
          Sha2Input p L L'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)) ∧
          LocalDecompositionCriterion p L L'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭))) :
    ∀ A : ValuationSubring K', A.comap (algebraMap K K') ≠ ⊤ →
      ∃ B : ValuationSubring L', B.comap (algebraMap L L') ≠ ⊤ ∧
        (NK.Mine.decompositionGroupOf K K' A).map (ϕ : Gal(K'/K) →* Gal(L'/L)) =
          NK.Mine.decompositionGroupOf L L' B :=
  NK.BrauerTwist.exists_place_of_localData ϕ he fun 𝔭 => by
    obtain ⟨p, hp, hLoc, hSha, hStep⟩ := h 𝔭
    exact ⟨p, hp, hLoc, sha2Vanishing p hSha, hStep⟩

/-- **The endgame input (a), with the Hasse principle supplied by the input catalogue of this
chapter.**  If the local data — the local Brauer input, the inputs of this chapter, and Neukirch's
local finishing step — is available in both directions, then the homeomorphic isomorphism `ϕ` of
absolute Galois groups preserves the decomposition groups, i.e.
`Submission.NeukirchUchida.PreservesDecompositionGroups ϕ`. -/
theorem preservesDecompositionGroups_of_sha2Input
    {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (h₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
        ∃ p : ℕ, p.Prime ∧
          LocalH2Input p K₂ K₂'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭)) ∧
          Sha2Input p K₂ K₂'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭)) ∧
          LocalDecompositionCriterion p K₂ K₂'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭)))
    (h₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
        ∃ p : ℕ, p.Prime ∧
          LocalH2Input p K₁ K₁'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔮)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔮)) ∧
          Sha2Input p K₁ K₁'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔮)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔮)) ∧
          LocalDecompositionCriterion p K₁ K₁'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔮)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔮))) :
    Submission.NeukirchUchida.PreservesDecompositionGroups ϕ :=
  NK.BrauerTwist.preservesDecompositionGroups_of_localGalois ϕ he
    (fun 𝔭 => by
      obtain ⟨p, hp, hLoc, hSha, hStep⟩ := h₁ 𝔭
      exact ⟨p, hp, hLoc, sha2Vanishing p hSha, hStep⟩)
    (fun 𝔮 => by
      obtain ⟨p, hp, hLoc, hSha, hStep⟩ := h₂ 𝔮
      exact ⟨p, hp, hLoc, sha2Vanishing p hSha, hStep⟩)

end NK.HasseTwist

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The endgame input (a): per-prime twisted local data implies `PreservesDecompositionGroups`

This is the coefficient-corrected version of
`Submission/Work/Mine/preservesDecompositionGroups_of_localGalois.lean`: instead of the
trivial-coefficient inputs `NK.BrauerHasse.LocalH2Input`, `Sha2Vanishing`,
`LocalDecompositionCriterion` (which are false for odd `p` when `μ_p ⊄ κ`), it consumes the twisted
inputs of `Submission/Work/BrauerTwist/Hasse.lean`, which are the classical ones
(`Br(κ)[p] ≅ Z/p`, Hasse–Brauer–Noether, Neukirch's local step).

The conclusion is exactly the input (a) of the endgame
(`Submission/NeukirchUchida/Reduction.lean`): `Submission.NeukirchUchida.PreservesDecompositionGroups
ϕ`.  Nothing in the argument is coefficient-specific; the point of the file is that the *data* that
has to be supplied is now the correct one.
-/

import Submission.NK.BrauerTwist.Main
import Submission.NK.Mine.CompletionAPI
import Submission.NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois
import Submission.NK.NeukirchUchida.isHomeomorph_conjHomEquiv

open scoped Pointwise

set_option autoImplicit false

universe u

namespace NK.BrauerTwist

/-- **Per-prime twisted local data produces the place correspondence.**  Let `K`, `L` be number
fields with separable closures `K'`, `L'` and `ϕ : Gal(K'/K) ≃* Gal(L'/L)` a homeomorphism.
Suppose that for every finite prime `𝔭` of `K` the *twisted* local Brauer data at
`K_𝔭 = adicCompletion K 𝔭` — `LocalH2Input`, `Sha2Vanishing` and `LocalDecompositionCriterion`
with `μ_p`-coefficients — is available at `L`.  Then for every place `A` of `K'` over a finite
prime of `K`, the image `ϕ(D_A)` of its decomposition group is the decomposition group of a place
`B` of `L'` over a finite prime of `L`. -/
theorem exists_place_of_localData
    {K K' L L' : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field K'] [Field L'] [Algebra K K'] [Algebra L L']
    [IsSepClosure K K'] [IsSepClosure L L']
    (ϕ : Gal(K'/K) ≃* Gal(L'/L)) (he : IsHomeomorph ϕ)
    (h : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        ∃ p : ℕ, p.Prime ∧
          LocalH2Input p L L'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)) ∧
          Sha2Vanishing p L L'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)) ∧
          LocalDecompositionCriterion p L L'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭))) :
    ∀ A : ValuationSubring K', A.comap (algebraMap K K') ≠ ⊤ →
      ∃ B : ValuationSubring L', B.comap (algebraMap L L') ≠ ⊤ ∧
        (NK.Mine.decompositionGroupOf K K' A).map (ϕ : Gal(K'/K) →* Gal(L'/L)) =
          NK.Mine.decompositionGroupOf L L' B := by
  intro A hA
  obtain ⟨𝔭, h𝔭⟩ := NK.BrauerHasse.exists_heightOneSpectrum_eq_comap (K := K) (K' := K') A hA
  obtain ⟨p, hp, hLoc, hHasse, hStep⟩ := h 𝔭
  let D : Subgroup Gal(K'/K) := NK.Mine.decompositionGroupOf K K' A
  have hDclosed : IsClosed ((D : Set Gal(K'/K))) :=
    Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A
  have hHclosed : IsClosed (((D.map (ϕ : Gal(K'/K) →* Gal(L'/L))) : Subgroup Gal(L'/L)) :
      Set Gal(L'/L)) := by
    rw [Subgroup.coe_map]
    exact (Homeomorph.isClosed_image (IsHomeomorph.homeomorph (⇑ϕ) he)).mpr hDclosed
  have hND : Subgroup.normalizer D = D :=
    Submission.NeukirchUchida.normalizer_decompositionGroup (K₁ := K) (K₁' := K') 𝔭 A h𝔭
  have hN : Subgroup.normalizer (D.map (ϕ : Gal(K'/K) →* Gal(L'/L))) =
      D.map (ϕ : Gal(K'/K) →* Gal(L'/L)) := by
    rw [← Subgroup.map_normalizer_eq_of_bijective D ϕ.bijective, hND]
  have hκ : Nonempty ((D.map (ϕ : Gal(K'/K) →* Gal(L'/L))) ≃* Gal(SeparableClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭) /
      IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)) := by
    obtain ⟨e⟩ := NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois
      (K := K) (K' := K') 𝔭 A h𝔭
    exact ⟨(Subgroup.equivMapOfInjective D (ϕ : Gal(K'/K) →* Gal(L'/L)) ϕ.injective).symm.trans e⟩
  obtain ⟨B, hB, hBstab⟩ :=
    exists_decompositionGroup_of_localGalois
      (K := L) (K' := L') (κ := IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭)
      (κ' := SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭))
      p hp (D.map (ϕ : Gal(K'/K) →* Gal(L'/L))) hHclosed hN hκ hLoc hHasse hStep
  refine ⟨B, hB, ?_⟩
  have h1 : NK.Mine.decompositionGroupOf L L' B = D.map (ϕ : Gal(K'/K) →* Gal(L'/L)) := hBstab
  rw [h1]

/-- **The endgame input (a), coefficient-corrected.**  If the *twisted* local data is available in
both directions (per finite prime of `K₁` for the local fields of `K₁` at `K₂`, and conversely),
then the homeomorphic isomorphism `ϕ` of absolute Galois groups preserves the decomposition groups
— i.e. `Submission.NeukirchUchida.PreservesDecompositionGroups ϕ`, the input (a) of
`Submission/NeukirchUchida/Endgame.lean`. -/
theorem preservesDecompositionGroups_of_localGalois
    {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (h₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
        ∃ p : ℕ, p.Prime ∧
          LocalH2Input p K₂ K₂'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭)) ∧
          Sha2Vanishing p K₂ K₂'
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
          Sha2Vanishing p K₁ K₁'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔮)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔮)) ∧
          LocalDecompositionCriterion p K₁ K₁'
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔮)
            (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔮))) :
    Submission.NeukirchUchida.PreservesDecompositionGroups ϕ := by
  constructor
  · intro A hA
    exact exists_place_of_localData (K := K₁) (K' := K₁') (L := K₂) (L' := K₂') ϕ he h₁ A hA
  · intro B hB
    obtain ⟨A, hA, hAB⟩ := exists_place_of_localData (K := K₂) (K' := K₂') (L := K₁) (L' := K₁')
      ϕ.symm (Submission.NeukirchUchida.isHomeomorph_symm ϕ he) h₂ B hB
    refine ⟨A, hA, ?_⟩
    show (NK.Mine.decompositionGroupOf K₁ K₁' A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      NK.Mine.decompositionGroupOf K₂ K₂' B
    rw [← hAB, Subgroup.map_map]
    have hcomp : ((ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)).comp
        (ϕ.symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁))) = MonoidHom.id Gal(K₂'/K₂) := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]

end NK.BrauerTwist

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The corrected global corollary: corresponding places have the same residue characteristic and
local degree

This is the corrected form of
`NK.LocalInputs.residueChar_and_localDegree_eq_of_decompositionGroup`
(`Submission/Work/LocalInputs/Global.lean`): for number fields `K₁`, `K₂` with separable closures
`K₁'`, `K₂'`, an isomorphism `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)`, places `A` of `K₁'` and `B` of `K₂'`
over finite primes `𝔭`, `𝔮`, and the hypothesis `ϕ(D_A) = D_B` (the local correspondence),

* `p = q`: the residue characteristics of the two completions coincide;
* `localDegree K₁ 𝔭 = localDegree K₂ 𝔮`, i.e. `[K₁,𝔭 : ℚ_p] = [K₂,𝔮 : ℚ_q]`.

The *only* change with respect to the existing theorem is the local input: instead of
`LocalFieldInputs` + `LocalGaloisInputs` (whose `p_torsion_iff` field is about the abstract
abelianisation and cannot be discharged) it takes `LocalFieldInputs` + the corrected
`NK.PTorsionTop.LocalGaloisInputsTop`, whose `p_torsion_iff_top` is *proved* by
`NK.PTorsionTop.padicGaloisInputsTop_of_localInputs`.

Since the corrected `δ`-invariant lives in the *topological* abelianisation, the transport needs
the local isomorphism to be a homeomorphism: `NK.PTorsionTop.hasPTorsionAbelianizationTop_congr_iff_of_isHomeomorph`.
For the residue characteristic no continuity is needed (Ivanov's invariant is an invariant of the
abstract group), so that conclusion is available unconditionally; the local degree conclusion
carries the hypothesis `IsHomeomorph ψ` on the local isomorphism `ψ`.  (Choosing `ψ` to be the
isomorphism produced by the place correspondence is legitimate — that is what `ϕ` restricted to the
decomposition groups is — but the workspace's existing
`NK.LocalInputs.Global.nonempty_mulEquiv_sepClosure_of_decompositionGroup_map` produces it only
as a `Nonempty`, so homeomorphy is recorded as a hypothesis here.)

## Main results

* `NK.PTorsionTop.residueChar_eq_of_decompositionGroupTop`
* `NK.PTorsionTop.localDegree_eq_of_decompositionGroupTop`
* `NK.PTorsionTop.residueChar_and_localDegree_eq_of_decompositionGroupTop`
-/
import Mathlib
import Submission.NK.PTorsionTop.InputsTop
import Submission.NK.LocalInputs.Global

open scoped Classical Pointwise
open IsDedekindDomain.HeightOneSpectrum

namespace NK.PTorsionTop

universe u

noncomputable section

/-- **The corrected global corollary**: corresponding places have the same residue characteristic
and the same absolute local degree. -/
theorem residueChar_and_localDegree_eq_of_decompositionGroupTop
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂))
    (A : ValuationSubring K₁') (B : ValuationSubring K₂')
    (hA : A.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭)
    (hB : B.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ 𝔮)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hAB : (NK.Mine.decompositionGroupOf K₁ K₁' A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      NK.Mine.decompositionGroupOf K₂ K₂' B)
    (ψ : Gal(SeparableClosure (𝔭.adicCompletion K₁)/𝔭.adicCompletion K₁) ≃*
      Gal(SeparableClosure (𝔮.adicCompletion K₂)/𝔮.adicCompletion K₂))
    (hψ : IsHomeomorph ψ)
    {p q : ℕ} (hF₁ : NK.LocalInputs.LocalFieldInputs K₁ 𝔭 p)
    (hG₁ : LocalGaloisInputsTop K₁ 𝔭 (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (hF₂ : NK.LocalInputs.LocalFieldInputs K₂ 𝔮 q)
    (hG₂ : LocalGaloisInputsTop K₂ 𝔮 (SeparableClosure (𝔮.adicCompletion K₂)) q) :
    p = q ∧ NK.LocalInputs.localDegree K₁ 𝔭 = NK.LocalInputs.localDegree K₂ 𝔮 := by
  obtain ⟨hpq, -, hd⟩ := residueChar_and_degree_eq_of_padicGaloisInputsTop
    (padicGaloisInputsTop_of_localInputs 𝔭 _ hF₁ hG₁)
    (padicGaloisInputsTop_of_localInputs 𝔮 _ hF₂ hG₂) ψ hψ
  exact ⟨hpq, hd⟩

/-- The residue-characteristic half of the corrected global corollary, which needs no continuity:
Ivanov's invariant is an invariant of the abstract group. -/
theorem residueChar_eq_of_decompositionGroupTop
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂))
    (A : ValuationSubring K₁') (B : ValuationSubring K₂')
    (hA : A.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭)
    (hB : B.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ 𝔮)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hAB : (NK.Mine.decompositionGroupOf K₁ K₁' A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      NK.Mine.decompositionGroupOf K₂ K₂' B)
    (ψ : Gal(SeparableClosure (𝔭.adicCompletion K₁)/𝔭.adicCompletion K₁) ≃*
      Gal(SeparableClosure (𝔮.adicCompletion K₂)/𝔮.adicCompletion K₂))
    {p q : ℕ} (hF₁ : NK.LocalInputs.LocalFieldInputs K₁ 𝔭 p)
    (hG₁ : LocalGaloisInputsTop K₁ 𝔭 (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (hF₂ : NK.LocalInputs.LocalFieldInputs K₂ 𝔮 q)
    (hG₂ : LocalGaloisInputsTop K₂ 𝔮 (SeparableClosure (𝔮.adicCompletion K₂)) q) :
    p = q :=
  residueChar_eq_of_padicGaloisInputsTop
    (padicGaloisInputsTop_of_localInputs 𝔭 _ hF₁ hG₁)
    (padicGaloisInputsTop_of_localInputs 𝔮 _ hF₂ hG₂) ψ

/-- The local-degree half of the corrected global corollary. -/
theorem localDegree_eq_of_decompositionGroupTop
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂))
    (A : ValuationSubring K₁') (B : ValuationSubring K₂')
    (hA : A.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭)
    (hB : B.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ 𝔮)
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hAB : (NK.Mine.decompositionGroupOf K₁ K₁' A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      NK.Mine.decompositionGroupOf K₂ K₂' B)
    (ψ : Gal(SeparableClosure (𝔭.adicCompletion K₁)/𝔭.adicCompletion K₁) ≃*
      Gal(SeparableClosure (𝔮.adicCompletion K₂)/𝔮.adicCompletion K₂))
    (hψ : IsHomeomorph ψ)
    {p q : ℕ} (hF₁ : NK.LocalInputs.LocalFieldInputs K₁ 𝔭 p)
    (hG₁ : LocalGaloisInputsTop K₁ 𝔭 (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (hF₂ : NK.LocalInputs.LocalFieldInputs K₂ 𝔮 q)
    (hG₂ : LocalGaloisInputsTop K₂ 𝔮 (SeparableClosure (𝔮.adicCompletion K₂)) q) :
    NK.LocalInputs.localDegree K₁ 𝔭 = NK.LocalInputs.localDegree K₂ 𝔮 :=
  degree_eq_of_padicGaloisInputsTop
    (padicGaloisInputsTop_of_localInputs 𝔭 _ hF₁ hG₁)
    (padicGaloisInputsTop_of_localInputs 𝔮 _ hF₂ hG₂) ψ hψ

end

end NK.PTorsionTop

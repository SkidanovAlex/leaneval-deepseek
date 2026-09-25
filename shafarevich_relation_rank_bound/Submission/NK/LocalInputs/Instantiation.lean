/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Instantiating `PadicGaloisInputs` for a `p`-adic completion

This is the point of the `NK.LocalInputs` area: the sibling chapter
`Submission/Work/LocalAnabelian/` proves its local invariance results *conditionally* on
`NK.LocalAnabelian.PadicGaloisInputs p d δ κ K'`, and that structure was never instantiated.
Here it is instantiated for a genuine `p`-adic field, namely

  `κ = 𝔭.adicCompletion K`

for a number field `K` and a finite prime `𝔭`, with `K'` a separable closure of `κ`, with

* `d = localDegree K 𝔭 = [κ : ℚ_p]` (the absolute degree, computed as a `ℚ_p`-dimension), and
* `δ = zetaIndicator p κ ∈ {0,1}`, the indicator of `ζ_p ∈ κ`.

The hypotheses are the explicitly named classical inputs of `NK.LocalInputs.Inputs`:
`LocalFieldInputs K 𝔭 p` (the residue characteristic `p` and the structure of the principal units
`U¹ = 1 + 𝔪`) and `LocalGaloisInputs K 𝔭 K' p` (Ivanov's detection of the residue characteristic
and the local-reciprocity computation of `G_κ^{ab}`).  Both are discharged classically; see the
docstrings there.  Everything *else* is proved here, in particular the power-class count
`|κˣ/(κˣ)^p| = p^{d+1+δ}` (from the principal units and the residue field), which is the
"missing case `ζ_p ∉ κ`" of the commons.

The main consequences (`Submission/NeukirchUchida/Reduction.lean`,
`Submission/NeukirchUchida/LocalSubgroup.lean`):

* `NK.LocalAnabelian.residueChar_and_degree_eq_of_padicGaloisInputs` now applies to genuine
  `p`-adic fields of number fields (see `NK.LocalInputs.Global`);
* conversely, the local invariants of a `p`-adic field of a number field are recovered from the
  abstract group `Gal(κ̄/κ)`.
-/
import Submission.NK.LocalInputs.Inputs
import Submission.NK.LocalInputs.PowerQuotient.natCard_KummerGroup_eq_pow_of_principalUnits
import Submission.NK.LocalInputs.PowerQuotient.natCard_residueUnits_quot_pow_eq_one

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalInputs

noncomputable section

universe u

/-- **The power-class count for a `p`-adic completion**, assembled from the two arithmetic
inputs: `|U¹/(U¹)^p| = p^{[κ:ℚ_p]+δ}` (the structure of the principal units) and
`|F_qˣ/(F_qˣ)^p| = 1` (the residue field is finite of characteristic `p`), giving

  `|κˣ/(κˣ)^p| = p^{[κ:ℚ_p] + 1 + δ}`,

i.e. `Nat.card (KummerGroup p κ) = p ^ (localDegree K 𝔭 + 1 + zetaIndicator p κ)`. -/
theorem natCard_KummerGroup_adicCompletion_eq_pow {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hF : LocalFieldInputs K 𝔭 p) :
    Nat.card (NK.LocalAnabelian.KummerGroup p (𝔭.adicCompletion K)) =
      p ^ (localDegree K 𝔭 + 1 + zetaIndicator p (𝔭.adicCompletion K)) :=
  NK.LocalInputs.PowerQuotient.natCard_KummerGroup_eq_pow_of_principalUnits 𝔭 hF.hp
    (NK.LocalInputs.PowerQuotient.natCard_residueUnits_quot_pow_eq_one 𝔭 hF.hp hF.residue_char)
    hF.principal_units_card

/-- **The instantiation of `PadicGaloisInputs` for a `p`-adic completion.**  For a number field
`K`, a finite prime `𝔭`, a separable closure `K'` of `κ = K_𝔭` and the inputs
`LocalFieldInputs K 𝔭 p` and `LocalGaloisInputs K 𝔭 K' p`,

  `PadicGaloisInputs p [κ : ℚ_p] δ κ K'`

holds, with `δ` the indicator of `ζ_p ∈ κ`. -/
theorem padicGaloisInputs_of_localInputs {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hF : LocalFieldInputs K 𝔭 p) (hG : LocalGaloisInputs K 𝔭 K' p) :
    NK.LocalAnabelian.PadicGaloisInputs p (localDegree K 𝔭)
      (zetaIndicator p (𝔭.adicCompletion K)) (𝔭.adicCompletion K) K' where
  hp := hF.hp
  hδ := zetaIndicator_le_one p (𝔭.adicCompletion K)
  zeta_iff := zetaIndicator_eq_one_iff p (𝔭.adicCompletion K)
  powerQuotient_card := natCard_KummerGroup_adicCompletion_eq_pow 𝔭 hF
  abelian_rank := hG.abelian_rank
  p_torsion_iff := hG.p_torsion_iff
  residueChar_detected := residueCharDetectedBy_of_localGaloisInputs hG

/-- **The instantiation at the canonical separable closure**, i.e. with
`K' = SeparableClosure (𝔭.adicCompletion K)`. -/
theorem padicGaloisInputs_of_localInputs_sepClosure {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hF : LocalFieldInputs K 𝔭 p)
    (hG : LocalGaloisInputs K 𝔭 (SeparableClosure (𝔭.adicCompletion K)) p) :
    NK.LocalAnabelian.PadicGaloisInputs p (localDegree K 𝔭)
      (zetaIndicator p (𝔭.adicCompletion K)) (𝔭.adicCompletion K)
      (SeparableClosure (𝔭.adicCompletion K)) :=
  padicGaloisInputs_of_localInputs 𝔭 _ hF hG

/-- **Part (2) of the deliverable, in the hypotheses of the instantiation**: Ivanov's detection of
the residue characteristic for the completion of a number field at a finite prime,
`NK.LocalAnabelian.ResidueCharDetectedBy p (Gal(K'/K_𝔭))`. -/
theorem residueCharDetectedBy_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (_hF : LocalFieldInputs K 𝔭 p) (hG : LocalGaloisInputs K 𝔭 K' p) :
    NK.LocalAnabelian.ResidueCharDetectedBy p (Gal(K'/𝔭.adicCompletion K)) :=
  residueCharDetectedBy_of_localGaloisInputs hG

/-- **Part (3) of the deliverable, in the hypotheses of the instantiation**: the abelianised
pro-`p` rank of `Gal(K'/K_𝔭)` is `[K_𝔭 : ℚ_p] + 1 + δ`. -/
theorem hasAbelianFrattiniRank_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (_hF : LocalFieldInputs K 𝔭 p) (hG : LocalGaloisInputs K 𝔭 K' p) :
    NK.LocalAnabelian.HasAbelianFrattiniRank p
      (localDegree K 𝔭 + 1 + zetaIndicator p (𝔭.adicCompletion K)) (Gal(K'/𝔭.adicCompletion K)) :=
  hG.abelian_rank

/-- **Part (1) of the deliverable**, restated with the `PadicGaloisInputs` field: the `p`-torsion of
the abelianisation detects `ζ_p ∈ κ`. -/
theorem p_torsion_iff_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (_hF : LocalFieldInputs K 𝔭 p) (hG : LocalGaloisInputs K 𝔭 K' p) :
    (zetaIndicator p (𝔭.adicCompletion K) = 1) ↔
      NK.LocalAnabelian.HasPTorsionAbelianization p (Gal(K'/𝔭.adicCompletion K)) :=
  hG.p_torsion_iff

end

end NK.LocalInputs

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.LocalInputs.PowerQuotient.natCard_KummerGroup_eq_pow_of_principalUnits
import Submission.NK.LocalInputs.PowerQuotient.natCard_residueUnits_quot_pow_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

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

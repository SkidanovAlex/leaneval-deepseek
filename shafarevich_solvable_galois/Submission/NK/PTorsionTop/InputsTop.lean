/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The corrected local input bundles

The bundles of `NK.LocalAnabelian.PadicGaloisInputs`, `NK.LocalInputs.LocalGaloisInputs` and
`NK.LocalInputs.LocalGaloisInputsOfUnits` carry the field

  `p_torsion_iff : (δ = 1) ↔ HasPTorsionAbelianization p (Gal(K'/κ))`

about the **abstract** commutator quotient `Abelianization G = G ⧸ commutator G`.  That predicate
is not the one local class field theory computes (the topological abelianisation
`G ⧸ (commutator G).topologicalClosure` is, cf. `NK.PTorsionTop.HasPTorsionAbelianizationTop`),
and the field is not dischargeable: a `ℤ/p`-quotient does not produce `p`-torsion.

This file provides the corrected bundles, mirroring the existing ones field by field:

* `NK.PTorsionTop.LocalGaloisInputsTop K 𝔭 K' p` — the same fields as
  `NK.LocalInputs.LocalGaloisInputs` (`hp`, `proP_unbounded`, `other_bounded`, `abelian_rank`)
  with `p_torsion_iff` replaced by the **local reciprocity datum**
  `reciprocity : Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K) K')`
  (the same input that `NK.LocalInputs.LocalGaloisInputsOfUnits.lubinTate` records);
* `NK.PTorsionTop.PadicGaloisInputsTop p d δ κ K'` — the same fields as
  `NK.LocalAnabelian.PadicGaloisInputs`, with `p_torsion_iff` stated for the *corrected*
  predicate: `(δ = 1) ↔ HasPTorsionAbelianizationTop p (Gal(K'/κ))`.

The point is that the corrected `p_torsion_iff` is a **theorem** for genuine `p`-adic fields:

* `NK.PTorsionTop.padicGaloisInputsTop_of_localInputs` instantiates
  `PadicGaloisInputsTop p (localDegree K 𝔭) (zetaIndicator p κ) κ K'` from the *arithmetic* input
  `LocalFieldInputs` (discharged unconditionally by
  `NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime`) and `LocalGaloisInputsTop`, the
  `p_torsion_iff` field being produced by `NK.PTorsionTop.hasPTorsionAbelianizationTop_iff_zeta`;
* `NK.PTorsionTop.localGaloisInputsTop_of_units` shows that the (satisfiable) bundle
  `NK.LocalInputs.LocalGaloisInputsOfUnits` *implies* `LocalGaloisInputsTop`.

## Main definitions and results

* `NK.PTorsionTop.PadicGaloisInputsTop`, `NK.PTorsionTop.LocalGaloisInputsTop`
* `NK.PTorsionTop.residueCharDetectedBy_of_localGaloisInputsTop`
* `NK.PTorsionTop.localGaloisInputsTop_of_units`
* `NK.PTorsionTop.padicGaloisInputsTop_of_localInputs`
-/
import Mathlib
import Submission.NK.PTorsionTop.Main
import Submission.NK.LocalInputs.InputsOfUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.PTorsionTop

universe u

noncomputable section

/-- **The corrected local arithmetic data of a `p`-adic field.**  The fields are those of
`NK.LocalAnabelian.PadicGaloisInputs`, except that `p_torsion_iff` is stated for the *topological*
abelianisation (`HasPTorsionAbelianizationTop`), for which it is true — it is derived from local
reciprocity and the arithmetic of `κˣ` in
`NK.PTorsionTop.padicGaloisInputsTop_of_localInputs`. -/
structure PadicGaloisInputsTop (p d δ : ℕ) (κ K' : Type*) [Field κ] [Field K'] [Algebra κ K']
    [IsSepClosure κ K'] : Prop where
  /-- `p` is a prime. -/
  hp : p.Prime
  /-- `δ ∈ {0,1}`. -/
  hδ : δ ≤ 1
  /-- `κ` contains a primitive `p`-th root of unity exactly when `δ = 1`. -/
  zeta_iff : (δ = 1) ↔ ∃ ζ : κ, IsPrimitiveRoot ζ p
  /-- `|κˣ/(κˣ)^p| = p^{d+1+δ}`. -/
  powerQuotient_card : Nat.card (NK.LocalAnabelian.KummerGroup p κ) = p ^ (d + 1 + δ)
  /-- the abelianised pro-`p` rank is `d + 1 + δ`. -/
  abelian_rank : NK.LocalAnabelian.HasAbelianFrattiniRank p (d + 1 + δ) (Gal(K'/κ))
  /-- **Ivanov's detection of the residue characteristic.** -/
  residueChar_detected : NK.LocalAnabelian.ResidueCharDetectedBy p (Gal(K'/κ))
  /-- **The corrected `p`-torsion detection**: the topological abelianisation of `Gal(K'/κ)` has
  non-trivial `p`-torsion exactly when `δ = 1`. -/
  p_torsion_iff_top : (δ = 1) ↔
    HasPTorsionAbelianizationTop p (Gal(K'/κ))

/-- **The corrected local Galois-theoretic inputs for `κ = K_𝔭`.**  The fields are those of
`NK.LocalInputs.LocalGaloisInputs` with `p_torsion_iff` replaced by the local reciprocity datum,
from which `p_torsion_iff_top` is derived (see
`NK.PTorsionTop.hasPTorsionAbelianizationTop_iff_zeta`). -/
structure LocalGaloisInputsTop (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] (p : ℕ) : Prop where
  /-- `p` is a prime. -/
  hp : p.Prime
  /-- **Ivanov, Lemma 3.12, the `ℓ = p` case**: the `p`-tower rank of `G_κ` is unbounded. -/
  proP_unbounded : NK.LocalAnabelian.HasUnboundedTowerRank p (Gal(K'/𝔭.adicCompletion K))
  /-- **Ivanov, Lemma 3.12, the `ℓ ≠ p` case**: the `ℓ`-tower rank is bounded for `ℓ ≠ p`. -/
  other_bounded : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
    ¬ NK.LocalAnabelian.HasUnboundedTowerRank ℓ (Gal(K'/𝔭.adicCompletion K))
  /-- **The abelianised pro-`p` rank** (local reciprocity): `(ℤ/p)^{[κ:ℚ_p] + 1 + δ}`. -/
  abelian_rank : NK.LocalAnabelian.HasAbelianFrattiniRank p
    (NK.LocalInputs.localDegree K 𝔭 + 1 + NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K))
    (Gal(K'/𝔭.adicCompletion K))
  /-- **The local reciprocity datum** (Lubin–Tate / local class field theory): the same input that
  `NK.LocalInputs.LocalGaloisInputsOfUnits.lubinTate` records, in the corrected form of
  `NK.LocalCFT` (whose Artin map targets `Gal(κ^{ab}/κ)`). -/
  reciprocity : Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K) K')

/-- **Ivanov's detection of the residue characteristic**, from the two tower-rank inputs. -/
theorem residueCharDetectedBy_of_localGaloisInputsTop {K : Type*} [Field K] [NumberField K]
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ} (h : LocalGaloisInputsTop K 𝔭 K' p) :
    NK.LocalAnabelian.ResidueCharDetectedBy p (Gal(K'/𝔭.adicCompletion K)) := by
  intro ℓ hℓ
  constructor
  · intro hunb
    by_contra hne
    exact h.other_bounded ℓ hℓ hne hunb
  · rintro rfl
    exact h.proP_unbounded

/-- **The (satisfiable) `LocalGaloisInputsOfUnits` implies the corrected bundle**: only the
`p_torsion_iff` field is dropped, `lubinTate` being *by definition*
`Nonempty (ArtinReciprocity _ _)` (that is `NK.LocalCFT.LubinTateInput`). -/
theorem localGaloisInputsTop_of_units {K : Type*} [Field K] [NumberField K]
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hF : NK.LocalInputs.LocalFieldInputs K 𝔭 p)
    (h : NK.LocalInputs.LocalGaloisInputsOfUnits K 𝔭 K' p)
    (hD : Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K) K')) :
    LocalGaloisInputsTop K 𝔭 K' p where
  hp := h.hp
  proP_unbounded := h.proP_unbounded
  other_bounded := h.other_bounded
  abelian_rank := (NK.LocalInputs.localGaloisInputs_of_units hF h).abelian_rank
  reciprocity := hD

/-- The same, from the corrected Lubin–Tate input
(`NK.LocalCFT.LubinTateInput := Nonempty (ArtinReciprocity _ _)`).

*Note.*  The `lubinTate` field of the existing `NK.LocalInputs.LocalGaloisInputsOfUnits` is the
**sibling area's** `NK.LocalReciprocity.LubinTateInput = Nonempty (LocalReciprocityDatum _ _)`,
whose Artin map targets the *absolute* group `Gal(F'/F)`; that datum is empty for `p`-adic fields
(see the module docstring of `Submission/Work/LocalCFT/Basic.lean`).  What the corrected bundle
carries is the corrected datum `NK.LocalCFT.LubinTateInput`, and the two are genuinely different
inputs. -/
theorem localGaloisInputsTop_of_lubinTate {K : Type*} [Field K] [NumberField K]
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hF : NK.LocalInputs.LocalFieldInputs K 𝔭 p)
    (h : NK.LocalInputs.LocalGaloisInputsOfUnits K 𝔭 K' p)
    (hD : NK.LocalCFT.LubinTateInput (𝔭.adicCompletion K) K') :
    LocalGaloisInputsTop K 𝔭 K' p :=
  localGaloisInputsTop_of_units hF h hD

-- **The corrected `p_torsion_iff` for the local Galois bundle** — the direct replacement of the
-- old field.
theorem p_torsion_iff_top_of_localGaloisInputsTop {K : Type*} [Field K] [NumberField K]
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hF : NK.LocalInputs.LocalFieldInputs K 𝔭 p) (hG : LocalGaloisInputsTop K 𝔭 K' p) :
    (NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K) = 1) ↔
      HasPTorsionAbelianizationTop p (Gal(K'/𝔭.adicCompletion K)) :=
  hasPTorsionAbelianizationTop_iff_zeta 𝔭 hF.hp hF.residue_char K'
    (Classical.choice hG.reciprocity)

/-- **The instantiation of the corrected bundle** `PadicGaloisInputsTop` for a `p`-adic
completion.  The `p_torsion_iff_top` field — the corrected `δ`-detection — is *proved* here from
`NK.PTorsionTop.hasPTorsionAbelianizationTop_iff_zeta` applied to the reciprocity datum carried
by `LocalGaloisInputsTop` and the arithmetic `LocalFieldInputs`. -/
theorem padicGaloisInputsTop_of_localInputs {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hF : NK.LocalInputs.LocalFieldInputs K 𝔭 p) (hG : LocalGaloisInputsTop K 𝔭 K' p) :
    PadicGaloisInputsTop p (NK.LocalInputs.localDegree K 𝔭)
      (NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K)) (𝔭.adicCompletion K) K' where
  hp := hF.hp
  hδ := NK.LocalInputs.zetaIndicator_le_one p (𝔭.adicCompletion K)
  zeta_iff := NK.LocalInputs.zetaIndicator_eq_one_iff p (𝔭.adicCompletion K)
  powerQuotient_card := NK.LocalInputs.natCard_KummerGroup_adicCompletion_eq_pow 𝔭 hF
  abelian_rank := hG.abelian_rank
  residueChar_detected := residueCharDetectedBy_of_localGaloisInputsTop hG
  p_torsion_iff_top :=
    hasPTorsionAbelianizationTop_iff_zeta 𝔭 hF.hp hF.residue_char K'
      (Classical.choice hG.reciprocity)

/-- **The instantiation at the canonical separable closure.** -/
theorem padicGaloisInputsTop_of_localInputs_sepClosure {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hF : NK.LocalInputs.LocalFieldInputs K 𝔭 p)
    (hG : LocalGaloisInputsTop K 𝔭 (SeparableClosure (𝔭.adicCompletion K)) p) :
    PadicGaloisInputsTop p (NK.LocalInputs.localDegree K 𝔭)
      (NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K)) (𝔭.adicCompletion K)
      (SeparableClosure (𝔭.adicCompletion K)) :=
  padicGaloisInputsTop_of_localInputs 𝔭 _ hF hG

/-- **The corrected `p_torsion_iff` at the canonical separable closure.** -/
theorem p_torsion_iff_top_sepClosure {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hF : NK.LocalInputs.LocalFieldInputs K 𝔭 p)
    (hG : LocalGaloisInputsTop K 𝔭 (SeparableClosure (𝔭.adicCompletion K)) p) :
    (NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K) = 1) ↔
      HasPTorsionAbelianizationTop p
        (Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K)) :=
  p_torsion_iff_top_of_localGaloisInputsTop hF hG

/-! ## The corrected transport lemmas

The proofs are those of `Submission/Work/LocalAnabelian/Assembly.lean`, with the only changes that
(a) the `p`-torsion is taken in the *topological* abelianisation, so the invariance of the
predicate under the group isomorphism `ϕ` requires `ϕ` to be a homeomorphism
(`NK.PTorsionTop.hasPTorsionAbelianizationTop_congr_iff_of_isHomeomorph`), and
(b) the corrected field `p_torsion_iff_top` replaces the old one. -/

/-- **Isomorphic absolute Galois groups of `p`-adic fields have the same residue characteristic.** -/
theorem residueChar_eq_of_padicGaloisInputsTop {κ κ₂ K' L' : Type*} [Field κ] [Field κ₂] [Field K']
    [Field L'] [Algebra κ K'] [Algebra κ₂ L'] [IsSepClosure κ K'] [IsSepClosure κ₂ L']
    {p d δ q e ε : ℕ} (h : PadicGaloisInputsTop p d δ κ K')
    (h' : PadicGaloisInputsTop q e ε κ₂ L') (ϕ : Gal(K'/κ) ≃* Gal(L'/κ₂)) : p = q :=
  NK.LocalAnabelian.residueCharDetectedBy_unique ϕ h.hp h'.hp h.residueChar_detected
    h'.residueChar_detected

/-- **The indicator `δ = 1 ⟺ ζ_p ∈ κ` is an invariant of the absolute Galois group**, for the
corrected predicate. -/
theorem delta_eq_of_padicGaloisInputsTop {κ κ₂ K' L' : Type*} [Field κ] [Field κ₂] [Field K']
    [Field L'] [Algebra κ K'] [Algebra κ₂ L'] [IsSepClosure κ K'] [IsSepClosure κ₂ L']
    {p d δ q e ε : ℕ} (h : PadicGaloisInputsTop p d δ κ K')
    (h' : PadicGaloisInputsTop q e ε κ₂ L') (ϕ : Gal(K'/κ) ≃* Gal(L'/κ₂))
    (hϕ : IsHomeomorph ϕ) : δ = ε := by
  have hpq : p = q := residueChar_eq_of_padicGaloisInputsTop h h' ϕ
  subst hpq
  have htor : HasPTorsionAbelianizationTop p (Gal(K'/κ)) ↔
      HasPTorsionAbelianizationTop p (Gal(L'/κ₂)) :=
    hasPTorsionAbelianizationTop_congr_iff_of_isHomeomorph ϕ hϕ p
  have hδε1 : δ = 1 ↔ ε = 1 := by rw [h.p_torsion_iff_top, h'.p_torsion_iff_top]; exact htor
  have hδ1 : δ ≤ 1 := h.hδ
  have hε1 : ε ≤ 1 := h'.hδ
  have hd : δ = 0 ∨ δ = 1 := by omega
  have he : ε = 0 ∨ ε = 1 := by omega
  rcases hd with hd | hd <;> rcases he with he | he
  · omega
  · rw [hd] at hδε1; exact absurd (hδε1.mpr he) (by omega)
  · rw [he] at hδε1; exact absurd (hδε1.mp hd) (by omega)
  · omega

/-- **Isomorphic absolute Galois groups of `p`-adic fields have the same absolute degree over
`ℚ_p`.** -/
theorem degree_eq_of_padicGaloisInputsTop {κ κ₂ K' L' : Type*} [Field κ] [Field κ₂] [Field K']
    [Field L'] [Algebra κ K'] [Algebra κ₂ L'] [IsSepClosure κ K'] [IsSepClosure κ₂ L']
    {p d δ q e ε : ℕ} (h : PadicGaloisInputsTop p d δ κ K')
    (h' : PadicGaloisInputsTop q e ε κ₂ L') (ϕ : Gal(K'/κ) ≃* Gal(L'/κ₂))
    (hϕ : IsHomeomorph ϕ) : d = e := by
  have hδε : δ = ε := delta_eq_of_padicGaloisInputsTop h h' ϕ hϕ
  have hpq : p = q := residueChar_eq_of_padicGaloisInputsTop h h' ϕ
  subst hpq
  have h1 : NK.LocalAnabelian.HasAbelianFrattiniRank p (d + 1 + δ) (Gal(L'/κ₂)) :=
    NK.LocalAnabelian.hasAbelianFrattiniRank_congr ϕ h.abelian_rank
  have h2 : d + 1 + δ = e + 1 + ε :=
    NK.LocalAnabelian.eq_of_hasAbelianFrattiniRank h.hp h1 h'.abelian_rank
  omega

/-- **The combined transport**: an isomorphism of absolute Galois groups of `p`-adic fields
preserves the residue characteristic, the `δ`-indicator and the absolute degree. -/
theorem residueChar_and_degree_eq_of_padicGaloisInputsTop {κ κ₂ K' L' : Type*} [Field κ]
    [Field κ₂] [Field K'] [Field L'] [Algebra κ K'] [Algebra κ₂ L'] [IsSepClosure κ K']
    [IsSepClosure κ₂ L'] {p d δ q e ε : ℕ} (h : PadicGaloisInputsTop p d δ κ K')
    (h' : PadicGaloisInputsTop q e ε κ₂ L') (ϕ : Gal(K'/κ) ≃* Gal(L'/κ₂))
    (hϕ : IsHomeomorph ϕ) : p = q ∧ δ = ε ∧ d = e :=
  ⟨residueChar_eq_of_padicGaloisInputsTop h h' ϕ, delta_eq_of_padicGaloisInputsTop h h' ϕ hϕ,
    degree_eq_of_padicGaloisInputsTop h h' ϕ hϕ⟩

/-- The abelianised `p`-Frattini rank `d + 1 + δ` is likewise an invariant. -/
theorem frattiniRank_eq_of_padicGaloisInputsTop {κ κ₂ K' L' : Type*} [Field κ] [Field κ₂]
    [Field K'] [Field L'] [Algebra κ K'] [Algebra κ₂ L'] [IsSepClosure κ K']
    [IsSepClosure κ₂ L'] {p d δ q e ε : ℕ} (h : PadicGaloisInputsTop p d δ κ K')
    (h' : PadicGaloisInputsTop q e ε κ₂ L') (ϕ : Gal(K'/κ) ≃* Gal(L'/κ₂)) :
    d + 1 + δ = e + 1 + ε := by
  have hpq : p = q := residueChar_eq_of_padicGaloisInputsTop h h' ϕ
  subst hpq
  have h1 : NK.LocalAnabelian.HasAbelianFrattiniRank p (d + 1 + δ) (Gal(L'/κ₂)) :=
    NK.LocalAnabelian.hasAbelianFrattiniRank_congr ϕ h.abelian_rank
  exact NK.LocalAnabelian.eq_of_hasAbelianFrattiniRank h.hp h1 h'.abelian_rank

end

end NK.PTorsionTop

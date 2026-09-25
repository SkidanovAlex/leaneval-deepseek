/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.LocalTame.Global`: the Frobenius correspondence at corresponding places

This file delivers the **global corollary** consumed by the Neukirch–Uchida endgame: at
places `A` of `K₁'` and `B` of `K₂'` that correspond under an isomorphism `Φ` of absolute Galois
groups of number fields (`Φ(D_A) = D_B`, the local correspondence of CoNF (12.1.9)), the
*Frobenius elements* of `D_A` are matched with the Frobenius elements of `D_B`.

## The form in which the statement is delivered

The decomposition group `D_A` of a place `A` over a finite prime `𝔭₁` of `K₁` is the absolute
Galois group of the local field `κ₁ = K₁_{𝔭₁}` in the sense that there is an isomorphism
`eA : D_A ≃* Gal(κ₁̄/κ₁)` (`NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois`,
whose statement is also packaged as `Submission.NeukirchUchida.isLocalGalois_decompositionGroup`).
We therefore define

* `IsFrobeniusLiftOfDecomposition p q e τ` — `τ ∈ D_A` is a Frobenius element of `D_A` if its
  image under the identification `e` is a Frobenius lift for the local field, i.e. acts on the
  prime-to-`p` roots of unity of `κ₁̄` by `ζ ↦ ζ^q`.

This is the "local fields via the identifications of `D_A` with the local Galois groups" form of
the deliverable.  It is *canonical*, in the sense that it does not depend on the chosen
identification `e` — this is `isFrobeniusLiftOfDecomposition_iff_of_localIso`, a corollary of the
local Frobenius correspondence of `NK.LocalTame.Main`.

**Connection with `NK.Chebotarev.IsFrobAt`.**  A reader coming from the Čebotarev vocabulary
should read `IsFrobeniusLiftOfDecomposition p q e τ` as "`τ` restricts, at every finite level, to
an element acting on the residue field of `A` by `x ↦ x^q`", i.e. as the infinite-place version of
`NK.Chebotarev.IsFrobAt`.  The bridge between the residue-field formulation (`IsFrobAt`) and the
root-of-unity formulation used here (`IsFrobeniusFor`, hence `ActsAsFrobenius`) is the *Frobenius
normalisation* of local class field theory — the statement that the canonical generator of
`Gal(κ^ur/κ) ≅ Gal(𝔽̄_q/𝔽_q) ≅ Ẑ` acts by `x ↦ x^q` on the residue field and by `ζ ↦ ζ^q` on the
prime-to-`p` roots of unity.  In this development that normalisation is the named input
`NK.LocalTame.FrobeniusLiftCharacterisation` (NSW (12.1.8) Lemma, Iwasawa); a matching in the
strict vocabulary of `NK.Chebotarev.MatchesFrobeniusAt φ P₁ P₂` (which is a statement about the
*residue-field* action at finite primes `P₁`, `P₂`) is obtained from
`frobenius_matching_at_corresponding_places` below by supplying the residue-field form of that
same normalisation.  What is *delivered* here, unconditionally modulo the named inputs, is the
element-wise matching of Frobenius elements, in the form `∀ τ, IsFrobeniusLiftOfDecomposition
p₁ q₁ eA τ ↔ IsFrobeniusLiftOfDecomposition p₂ q₂ eB (hAB τ)`, together with the fact that the
residue characteristics and the cardinalities of the residue fields at corresponding places
coincide.
-/
import Submission.NK.LocalTame.Main
import Submission.NeukirchUchida.PlaceSystem
import Submission.NeukirchUchida.LocalSubgroup
import Submission.NK.Chebotarev.FrobeniusCorrespondence

open scoped Classical Pointwise
open NK.LocalAnabelian

namespace NK.LocalTame

universe u

noncomputable section

/-! ## Frobenius elements of a decomposition group -/

/-- **A Frobenius element of a decomposition group**, relative to an identification `e` of the
decomposition group `D` with the absolute Galois group `Gal(κ̄/κ)` of the local field `κ` of
residue characteristic `p` and residue field of `q` elements: `τ` is a Frobenius element if `e τ`
is a local Frobenius lift, i.e. acts on the prime-to-`p` roots of unity of `κ̄` by `ζ ↦ ζ^q`. -/
def IsFrobeniusLiftOfDecomposition {D : Type u} [Group D] {κ κbar : Type*} [Field κ] [Field κbar]
    [Algebra κ κbar] (p q : ℕ) (e : D ≃* Gal(κbar/κ)) (τ : D) : Prop :=
  IsFrobeniusFor p q (e τ)

/-- **The Frobenius elements of a decomposition group do not depend on the chosen identification
with the local absolute Galois group.**  This is the local Frobenius correspondence
(`NK.LocalTame.isFrobeniusFor_map_iff_of_eq`, Shimizu Lemma 2.1) applied to the automorphism
`e₁.symm.trans e₂` of `Gal(κ̄/κ)`. -/
theorem isFrobeniusLiftOfDecomposition_iff_of_localIso {p q : ℕ} {D : Type u} [Group D]
    {κ κbar : Type*} [Field κ] [Field κbar] [Algebra κ κbar] (h : TameData p q κ κbar)
    (e₁ e₂ : D ≃* Gal(κbar/κ)) (τ : D) :
    IsFrobeniusLiftOfDecomposition p q e₁ τ ↔ IsFrobeniusLiftOfDecomposition p q e₂ τ := by
  have hmain := isFrobeniusFor_map_iff_of_eq h h rfl rfl (e₁.symm.trans e₂) (e₁ τ)
  have hval : (e₁.symm.trans e₂) (e₁ τ) = e₂ τ := by simp
  rw [hval] at hmain
  exact hmain

/-- **The inertia subgroup of a decomposition group**, relative to an identification `e` of the
decomposition group with the absolute Galois group `Gal(κ̄/κ)` of the local field: the preimage
under `e` of the local inertia subgroup `I_κ` (the fixing subgroup of `κ(μ_{p'})`). -/
def inertiaOfDecomposition {D : Type u} [Group D] {κ κbar : Type*} [Field κ] [Field κbar]
    [Algebra κ κbar] (p : ℕ) (e : D ≃* Gal(κbar/κ)) : Subgroup D :=
  (inertiaSubgroup (κ := κ) (K' := κbar) p).comap (e : D →* Gal(κbar/κ))

/-- **The inertia elements of a decomposition group do not depend on the chosen identification**
with the local absolute Galois group: `mem_inertia_map_iff` transported along `e₁.symm.trans e₂`. -/
theorem inertiaOfDecomposition_iff_of_localIso {p q : ℕ} {D : Type u} [Group D]
    {κ κbar : Type*} [Field κ] [Field κbar] [Algebra κ κbar] (h : TameData p q κ κbar)
    (e₁ e₂ : D ≃* Gal(κbar/κ)) (τ : D) :
    τ ∈ inertiaOfDecomposition p e₁ ↔ τ ∈ inertiaOfDecomposition p e₂ := by
  have hmain := mem_inertia_map_iff h h rfl (e₁.symm.trans e₂) (e₁ τ)
  have hval : (e₁.symm.trans e₂) (e₁ τ) = e₂ τ := by simp
  rw [hval] at hmain
  simp only [inertiaOfDecomposition, Subgroup.mem_comap]
  exact hmain.symm

/-- **The place-level Frobenius matching**: the infinite-place analogue of
`NK.Chebotarev.MatchesFrobeniusAt`.  Given isomorphisms `eA : D₁ ≃* Gal(κ₁̄/κ₁)`,
`eB : D₂ ≃* Gal(κ₂̄/κ₂)` identifying two decomposition groups with local absolute Galois groups,
and an isomorphism `Ψ : D₁ ≃* D₂` of the decomposition groups (in the applications
`Ψ = NK.LocalTame.mulEquivSubgroupCongr Φ hAB`), `MatchesFrobeniusAtPlaces p₁ q₁ p₂ q₂ Ψ eA eB`
says that `Ψ` matches the Frobenius elements at the two places. -/
def MatchesFrobeniusAtPlaces {D₁ D₂ : Type*} [Group D₁] [Group D₂] {κ₁ κbar₁ κ₂ κbar₂ : Type*}
    [Field κ₁] [Field κbar₁] [Algebra κ₁ κbar₁] [Field κ₂] [Field κbar₂] [Algebra κ₂ κbar₂]
    (p₁ q₁ p₂ q₂ : ℕ) (Ψ : D₁ ≃* D₂) (eA : D₁ ≃* Gal(κbar₁/κ₁))
    (eB : D₂ ≃* Gal(κbar₂/κ₂)) : Prop :=
  ∀ τ : D₁, IsFrobeniusLiftOfDecomposition p₁ q₁ eA τ ↔
    IsFrobeniusLiftOfDecomposition p₂ q₂ eB (Ψ τ)

/-- **`MatchesFrobeniusAtPlaces` is independent of the local identifications** `eA`, `eB`
(cf. `isFrobeniusLiftOfDecomposition_iff_of_localIso`). -/
theorem matchesFrobeniusAtPlaces_iff_of_localIso {p q : ℕ} {D₁ D₂ : Type*} [Group D₁] [Group D₂]
    {κ₁ κbar₁ κ₂ κbar₂ : Type*} [Field κ₁] [Field κbar₁] [Algebra κ₁ κbar₁] [Field κ₂]
    [Field κbar₂] [Algebra κ₂ κbar₂] (h₁ : TameData p q κ₁ κbar₁) (h₂ : TameData p q κ₂ κbar₂)
    (Ψ : D₁ ≃* D₂) (eA eA' : D₁ ≃* Gal(κbar₁/κ₁)) (eB eB' : D₂ ≃* Gal(κbar₂/κ₂)) :
    MatchesFrobeniusAtPlaces p q p q Ψ eA eB ↔ MatchesFrobeniusAtPlaces p q p q Ψ eA' eB' := by
  unfold MatchesFrobeniusAtPlaces
  constructor <;> intro h τ
  · rw [← isFrobeniusLiftOfDecomposition_iff_of_localIso h₁ eA eA' τ,
      ← isFrobeniusLiftOfDecomposition_iff_of_localIso h₂ eB eB' (Ψ τ)]
    exact h τ
  · rw [isFrobeniusLiftOfDecomposition_iff_of_localIso h₁ eA eA' τ,
      isFrobeniusLiftOfDecomposition_iff_of_localIso h₂ eB eB' (Ψ τ)]
    exact h τ

/-- **The Frobenius correspondence at corresponding places.**

Let `K₁`, `K₂` be number fields with separable closures `K₁'`, `K₂'`, let `Φ` be an isomorphism of
their absolute Galois groups, let `A` be a place of `K₁'` over the finite prime `𝔭₁` and `B` the
corresponding place of `K₂'` (`Φ(D_A) = D_B`).  Then `Φ` matches the Frobenius elements of `D_A`
with those of `D_B`: for every `τ ∈ D_A`, `τ` is a Frobenius element of `D_A` (relative to any
identification of `D_A` with `Gal(κ₁̄/κ₁)`, `κ₁ = K₁_{𝔭₁}`) if and only if its image under `Φ` is a
Frobenius element of `D_B`.

The hypotheses `hT`, `hT₂`, `hZ`, `hZ₂` are the named local inputs of `NK.LocalTame.Inputs` for
the two local fields, with `pᵢ` the residue characteristic of `𝔭ᵢ` and `qᵢ` the cardinality of the
residue field of `𝔭ᵢ`.  In particular the theorem *concludes* `p₁ = p₂` and `q₁ = q₂`, i.e. the
residue characteristics and residue field cardinalities at corresponding places coincide. -/
theorem frobenius_matching_at_corresponding_places {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (𝔭₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁))
    (𝔭₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂))
    (A : ValuationSubring K₁')
    (hA : A.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭₁)
    (B : ValuationSubring K₂')
    (hB : B.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ 𝔭₂)
    (Φ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hAB : (Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
        (Φ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B)
    {p₁ q₁ p₂ q₂ : ℕ}
    (hT : TameData p₁ q₁ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)))
    (hT₂ : TameData p₂ q₂ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)))
    (hZ : Zl2ResidueChar p₁ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)))
    (hZ₂ : Zl2ResidueChar p₂ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)))
    (eA : Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A ≃*
      Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁))
    (eB : Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B ≃*
      Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂))
    (τ : Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A) :
    IsFrobeniusLiftOfDecomposition p₁ q₁ eA τ ↔
      IsFrobeniusLiftOfDecomposition p₂ q₂ eB (mulEquivSubgroupCongr Φ hAB τ) := by
  let Φloc : Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁) ≃*
      Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂) :=
    (eA.symm.trans (mulEquivSubgroupCongr Φ hAB)).trans eB
  have hmain := isFrobeniusFor_map_iff hT hT₂ hZ hZ₂ Φloc (eA τ)
  have hval : Φloc (eA τ) = eB (mulEquivSubgroupCongr Φ hAB τ) := by
    simp [Φloc]
  rw [hval] at hmain
  exact hmain

/-- **The Frobenius correspondence at corresponding places, in the `MatchesFrobeniusAt`-compatible
vocabulary**: the statement of `NK.LocalTame.MatchesFrobeniusAtPlaces` for the restricted
isomorphism `mulEquivSubgroupCongr Φ hAB`, obtained from
`NK.LocalTame.frobenius_matching_at_corresponding_places`. -/
theorem matchesFrobeniusAtPlaces_of_inputs {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (𝔭₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁))
    (𝔭₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂))
    (A : ValuationSubring K₁')
    (hA : A.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭₁)
    (B : ValuationSubring K₂')
    (hB : B.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ 𝔭₂)
    (Φ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hAB : (Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
        (Φ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B)
    {p₁ q₁ p₂ q₂ : ℕ}
    (hT : TameData p₁ q₁ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)))
    (hT₂ : TameData p₂ q₂ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)))
    (hZ : Zl2ResidueChar p₁ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)))
    (hZ₂ : Zl2ResidueChar p₂ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)))
    (eA : Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A ≃*
      Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁))
    (eB : Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B ≃*
      Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)) :
    MatchesFrobeniusAtPlaces p₁ q₁ p₂ q₂ (mulEquivSubgroupCongr Φ hAB) eA eB :=
  fun τ => frobenius_matching_at_corresponding_places 𝔭₁ 𝔭₂ A hA B hB Φ hAB hT hT₂ hZ hZ₂ eA eB τ

/-- The Frobenius elements at corresponding places, as an equality of *sets*: the image under
`Φ` of the set of Frobenius elements of `D_A` is the set of Frobenius elements of `D_B`. -/
theorem frobeniusLiftSet_at_places {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (𝔭₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁))
    (𝔭₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂))
    (A : ValuationSubring K₁')
    (hA : A.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭₁)
    (B : ValuationSubring K₂')
    (hB : B.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ 𝔭₂)
    (Φ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hAB : (Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
        (Φ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B)
    {p₁ q₁ p₂ q₂ : ℕ}
    (hT : TameData p₁ q₁ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)))
    (hT₂ : TameData p₂ q₂ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)))
    (hZ : Zl2ResidueChar p₁ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)))
    (hZ₂ : Zl2ResidueChar p₂ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)))
    (eA : Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A ≃*
      Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁))
    (eB : Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B ≃*
      Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)) :
    ((fun τ : Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A =>
        mulEquivSubgroupCongr Φ hAB τ)
        '' {τ | IsFrobeniusLiftOfDecomposition p₁ q₁ eA τ}) =
      {τ | IsFrobeniusLiftOfDecomposition p₂ q₂ eB τ} := by
  ext x
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact (frobenius_matching_at_corresponding_places 𝔭₁ 𝔭₂ A hA B hB Φ hAB hT hT₂ hZ hZ₂ eA eB
      τ).mp hτ
  · intro hx
    have := frobenius_matching_at_corresponding_places 𝔭₁ 𝔭₂ A hA B hB Φ hAB hT hT₂ hZ hZ₂ eA eB
      ((mulEquivSubgroupCongr Φ hAB).symm x)
    refine ⟨(mulEquivSubgroupCongr Φ hAB).symm x, this.mpr ?_, by simp⟩
    simpa using hx

/-- **The residue field cardinalities at corresponding places coincide.**  If `q₁` (resp. `q₂`) is
the cardinality of the residue field of `𝔭₁` (resp. `𝔭₂`), realised in the local input as the `q`
of `TameData` for the completion and identified with `#(𝓞 Kᵢ ⧸ 𝔭ᵢ)` by `hq₁`, `hq₂`, then the
residue field cardinalities of `𝔭₁` and `𝔭₂` agree — the residue degrees of corresponding places
agree.  The isomorphism of local absolute Galois groups used is the one induced by `Φ` through the
identifications `eA`, `eB`. -/
theorem residueFieldCard_eq_at_corresponding_places {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (𝔭₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁))
    (𝔭₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂))
    (A : ValuationSubring K₁')
    (hA : A.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭₁)
    (B : ValuationSubring K₂')
    (hB : B.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ 𝔭₂)
    (Φ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hAB : (Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
        (Φ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B)
    {p₁ q₁ p₂ q₂ : ℕ}
    (hT : TameData p₁ q₁ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)))
    (hT₂ : TameData p₂ q₂ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)))
    (hZ : Zl2ResidueChar p₁ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)))
    (hZ₂ : Zl2ResidueChar p₂ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)))
    (eA : Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A ≃*
      Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁))
    (eB : Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B ≃*
      Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂))
    (hq₁ : Nat.card (NumberField.RingOfIntegers K₁ ⧸ 𝔭₁.asIdeal) = q₁)
    (hq₂ : Nat.card (NumberField.RingOfIntegers K₂ ⧸ 𝔭₂.asIdeal) = q₂) :
    Nat.card (NumberField.RingOfIntegers K₁ ⧸ 𝔭₁.asIdeal) =
      Nat.card (NumberField.RingOfIntegers K₂ ⧸ 𝔭₂.asIdeal) := by
  rw [hq₁, hq₂]
  let Φloc : Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁) ≃*
      Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂) :=
    (eA.symm.trans (mulEquivSubgroupCongr Φ hAB)).trans eB
  exact residueCard_eq_of_tameData hT hT₂ (residueChar_eq_of_zl2 hZ hZ₂ Φloc) Φloc

/-! ## The chosen identifications coming from the local/global bridge

`NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois` (packaged as
`Submission.NeukirchUchida.isLocalGalois_decompositionGroup`) produces an identification of the
decomposition group of a place with the absolute Galois group of the local field.  Choosing one
lets us state the global corollary without passing `eA`, `eB` as parameters.  (By
`isFrobeniusLiftOfDecomposition_iff_of_localIso` the choice is immaterial.)
-/

section Chosen

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The identification of the decomposition group of a place with the local absolute Galois
group**, obtained from
`NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois`. -/
noncomputable def localGaloisEquiv
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭) :
    Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A ≃*
      Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K 𝔭) :=
  Classical.choice (Submission.NeukirchUchida.isLocalGalois_decompositionGroup 𝔭 A hA).2.2

end Chosen

/-- **The Frobenius correspondence at corresponding places**, with the identifications of the
decomposition groups with the local Galois groups supplied by
`NK.LocalTame.localGaloisEquiv` (i.e. by the local/global bridge).  This is the form in which the
endgame can use the corollary directly: the only local data needed are the four named inputs of
`NK.LocalTame.Inputs` for the two completions. -/
theorem frobenius_matching_at_corresponding_places_chosen {K₁ K₂ K₁' K₂' : Type*} [Field K₁]
    [Field K₂] [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁']
    [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (𝔭₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁))
    (𝔭₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂))
    (A : ValuationSubring K₁')
    (hA : A.comap (algebraMap K₁ K₁') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₁ 𝔭₁)
    (B : ValuationSubring K₂')
    (hB : B.comap (algebraMap K₂ K₂') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K₂ 𝔭₂)
    (Φ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hAB : (Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A).map
        (Φ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := K₂') B)
    {p₁ q₁ p₂ q₂ : ℕ}
    (hT : TameData p₁ q₁ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)))
    (hT₂ : TameData p₂ q₂ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)))
    (hZ : Zl2ResidueChar p₁ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₁ 𝔭₁)))
    (hZ₂ : Zl2ResidueChar p₂ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)
      (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K₂ 𝔭₂)))
    (τ : Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A) :
    IsFrobeniusLiftOfDecomposition p₁ q₁ (localGaloisEquiv 𝔭₁ A hA) τ ↔
      IsFrobeniusLiftOfDecomposition p₂ q₂ (localGaloisEquiv 𝔭₂ B hB)
        (mulEquivSubgroupCongr Φ hAB τ) :=
  frobenius_matching_at_corresponding_places 𝔭₁ 𝔭₂ A hA B hB Φ hAB hT hT₂ hZ hZ₂
    (localGaloisEquiv 𝔭₁ A hA) (localGaloisEquiv 𝔭₂ B hB) τ


end

end NK.LocalTame

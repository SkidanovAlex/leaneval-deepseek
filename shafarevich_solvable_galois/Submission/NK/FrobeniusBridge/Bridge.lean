import Submission.NK.FrobeniusBridge.Basic
import Submission.NK.Reconstruct.LevelMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Frobenius bridge: the named inputs

This file states the **named bridge inputs** of the area, i.e. the remaining arithmetic content
that relates the local Frobenius condition (`NK.FrobeniusBridge.localFrobAt`, the vocabulary of
`Submission/Work/LocalTame/`) to the finite-level residue-field condition
(`NK.FrobeniusBridge.frobAtLevel`, the vocabulary of `NK.Chebotarev.IsFrobAt`).

The bridge is *not* an assumption about `ϕ`: it is a statement about a single number field `K`,
its separable closure `K'` and a place `A` of `K'` over a finite prime `𝔭` of `K`, namely the
classical dictionary

> the elements of `Gal(K'/K)` lying in the Frobenius coset of the decomposition group of `A`
> (i.e. acting by `ζ ↦ ζ^q` on the prime-to-`p` roots of unity of the local field `K_𝔭`) are
> exactly those whose restriction to **every** finite normal level `L ⊆ K'` acts on the residue
> field of `L` at `A ∩ L` by `x ↦ x^{#(𝓞K/𝔭)}`.

The two halves of this dictionary are used separately by the reconstruction:

* `PlaceLevelBridge.local_of_level` ("up"): a Frobenius element at a single level `L` agrees on `L`
  with a local Frobenius lift.  This is where the Frobenius coset structure of the decomposition
  group (a coset of the inertia subgroup, `NK.LocalTame.IsFrobeniusFor.mul_mem_inertia`) and the
  surjectivity of the level inertia subgroups enter;
* `PlaceLevelBridge.level_of_local` ("down"): a local Frobenius lift restricts to a Frobenius
  element at every level.  This is the *residue-field form of the Frobenius normalisation*
  (`NK.LocalTame.FrobeniusLiftCharacterisation` in its residue-field form, NSW (12.1.8) Lemma;
  Shimizu, arXiv:2009.10431, Lemma 2.1), i.e. the statement that the canonical generator of
  `Gal(κ^ur/κ) ≅ Gal(𝔽̄_q/𝔽_q) ≅ Ẑ` acts on the residue field by `x ↦ x^q`.

Both are classical statements about local fields and their completions, connecting the local
field `κ = K_𝔭` to the (finite) residue fields `κ(P_L)` of the levels; they are **not** yet
formalised anywhere in the workspace (in particular `Submission/Work/LocalTame/` records the
root-of-unity form of the same normalisation and explicitly leaves the residue-field form to a
bridge such as this one).
-/

namespace NK.FrobeniusBridge

open scoped Classical Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The named bridge inputs -/

/-- **The local–global dictionary at a place** (the named input of the Frobenius bridge).

`A` is a place of `K'` over a finite prime `𝔭` of `K`; `localFrobAt A g` is the local Frobenius
condition (the image of `g` under `D_A ≃* Gal(κ̄/κ)` acts on the prime-to-`p` roots of unity by
`ζ ↦ ζ^q`), and `frobAtLevel A L g` is the residue-field condition at the finite normal level `L`
(`g|_L` acts on `κ(P_L)` by `x ↦ x^{#(𝓞K/𝔭)}`).

This is the dictionary of Fujiwara–Shimizu Lemma 2.1 / CoNF (12.1.8) in the two forms in which the
reconstruction consumes it: `level_of_local` is the Frobenius normalisation (the residue-field form
of `NK.LocalTame.FrobeniusLiftCharacterisation`), and `local_of_level` is the statement that the
Frobenius elements at a level are the restrictions of the local Frobenius lifts (the Frobenius
coset of `D_A` modulo the inertia subgroup `I_A` surjects onto the corresponding coset of `D_{P_L}`
modulo `I_{P_L}`). -/
structure PlaceLevelBridge (A : FinitePlaceOf K K') : Prop where
  /-- **down**: a local Frobenius lift restricts to a Frobenius element at every finite level. -/
  level_of_local : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L]
      [NumberField ↥L] (g : Gal(K'/K)), localFrobAt A g → frobAtLevel A L g
  /-- **up**: a Frobenius element at a finite level agrees on that level with a local Frobenius
  lift. -/
  local_of_level : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L]
      [NumberField ↥L] (g : Gal(K'/K)), frobAtLevel A L g →
    ∃ g₀ : Gal(K'/K), AlgEquiv.restrictNormalHom L g₀ = AlgEquiv.restrictNormalHom L g ∧
      localFrobAt A g₀

/-- The local–global dictionary at every place of `K'` over a finite prime of `K`. -/
def FrobDictionary (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K'] [Algebra K K']
    [IsSepClosure K K'] : Prop :=
  ∀ A : FinitePlaceOf K K', PlaceLevelBridge A

/-- The elements of `Gal(K'/K)` acting trivially on the residue field of the finite level `L` at
the prime below the place `A`. -/
noncomputable def IsTrivialOnResidueAtLevel (A : FinitePlaceOf K K')
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    (g : Gal(K'/K)) : Prop :=
  ∀ x : NumberField.RingOfIntegers ↥L,
    galRestrict (NumberField.RingOfIntegers K) K ↥L (NumberField.RingOfIntegers ↥L)
      (AlgEquiv.restrictNormalHom L g) x - x ∈
      (NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)).asIdeal

/-- **The inertia half of the local–global dictionary**: an element of the decomposition group of
`A` acting trivially on the residue field of *every* finite level lies in the local inertia
subgroup `I_A ≅ I_κ` (`κ = K_𝔭`).

Equivalently: the compositum of the finite unramified levels below `A` is the maximal unramified
extension of the local field `κ`, i.e. `I_A` is the fixing subgroup of the maximal unramified
extension *at the place* `A`.  This is the projective-limit description of the inertia subgroup
(the companion of `Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubring_iff_forall_restrict`,
which gives the same statement for the *decomposition* subgroup). -/
structure InertiaLevelBridge (A : FinitePlaceOf K K') : Prop where
  inertia_of_levels : ∀ (g : Gal(K'/K)),
    (∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L],
      IsTrivialOnResidueAtLevel A L g) →
    ∀ (p q : ℕ), NK.LocalTame.TameData p q (localField A) (localClosure A) →
    ∀ (hg : g ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1),
      localGaloisEquiv A ⟨g, hg⟩ ∈
        NK.LocalAnabelian.inertiaSubgroup (κ := localField A) (K' := localClosure A) p

/-! ## The Frobenius correspondence at the places, in the local vocabulary -/

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The place-level Frobenius correspondence for `ϕ`, in the local vocabulary** (the hypothesis
`hB` of the deliverable): `ϕ` maps the local Frobenius lifts at a place `A` of `K₁'` to the local
Frobenius lifts at the corresponding place `a.placeMap A`.

The word "infinite level" is expressed here by the local predicate `localFrobAt`, i.e. by the
action on the prime-to-`p` roots of unity of the local field; by
`NK.FrobeniusBridge.isFrobAtPlace_iff_localFrob` this is equivalent to the "for every finite
normal level" condition, given the local–global dictionary.

This is exactly the shape of `NK.LocalTame.matchesFrobeniusAtPlaces_of_inputs`, and it is
*proved* from the named local inputs by
`NK.FrobeniusBridge.localFrobCorrespondencePlace_of_tameData`. -/
def LocalFrobCorrespondencePlace (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) : Prop :=
  ∀ (A : FinitePlaceOf K₁ K₁') (g : Gal(K₁'/K₁)), localFrobAt A g → localFrobAt (a.placeMap A) (ϕ g)

/-- **The bundle of inputs of the Frobenius bridge**, in the exact shape consumed by
`NK.FrobeniusBridge.frobeniusCorrespondencePlace`: the local–global dictionary at every place of
both fields, together with the place-level Frobenius correspondence for `ϕ`.

The second component is *proved* from the local structure theory of the two fields
(`NK.FrobeniusBridge.localFrobCorrespondencePlace_of_tameData`, which is
`NK.LocalTame.frobenius_matching_at_corresponding_places`); the first component is the named
arithmetic input documented in `PlaceLevelBridge`. -/
structure PlaceFrobeniusData (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) : Prop where
  /-- the local–global dictionary at the places of `K₁'` -/
  bridge₁ : FrobDictionary K₁ K₁'
  /-- the local–global dictionary at the places of `K₂'` -/
  bridge₂ : FrobDictionary K₂ K₂'
  /-- the place-level Frobenius correspondence for `ϕ` -/
  correspondence : LocalFrobCorrespondencePlace ϕ hϕ a

/-- **The finite-level correspondence in the vocabulary of this area**: the endgame's
`NK.Reconstruct.FrobeniusCorrespondencePlace` is the statement that `ϕ` carries the level-wise
Frobenius elements at every place `A` to the level-wise Frobenius elements at `a.placeMap A`. -/
theorem frobeniusCorrespondencePlace_iff (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) :
    NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a ↔
      (∀ (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
        [NumberField ↥(NK.Reconstruct.levelMap ϕ L)] [Normal K₂ (NK.Reconstruct.levelMap ϕ L)]
        (A : FinitePlaceOf K₁ K₁') (g : Gal(K₁'/K₁)),
        frobAtLevel A L g → frobAtLevel (a.placeMap A) (NK.Reconstruct.levelMap ϕ L) (ϕ g)) :=
  Iff.rfl

end NK.FrobeniusBridge

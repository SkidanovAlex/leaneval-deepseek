import Submission.NeukirchUchida.PlaceSystem
import Submission.NeukirchUchida.PrimeCorrespondence
import Submission.NK.Chebotarev.DenseFrobeniusSet
import Submission.NK.Chebotarev.FrobeniusGenerateTop
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The vocabulary of the reconstruction step of Neukirch–Uchida

This file sets up the *global vocabulary* in which the reconstruction step of Neukirch–Uchida
(CoNF XII §12.2, resp. Shimizu's proof) is phrased, and it isolates the three named inputs of the
reconstruction theorem `NK.Reconstruct.exists_sigma_of_localCorrespondence`.

The setting is that of the theorem: `K₁`, `K₂` number fields with separable closures `K₁'`, `K₂'`,
and `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` a homeomorphic isomorphism of absolute Galois groups.

* **(a) `GoodLocalCorrespondence ϕ`** — the *good local correspondence* of CoNF (12.1.9) /
  Shimizu Theorem 2.5: a Galois-equivariant bijection `Φ` between the places of `K₁'` over the
  finite primes of `K₁` and those of `K₂'` over the finite primes of `K₂`, compatible with `ϕ` on
  decomposition groups, preserving the induced correspondence of primes of the two number fields,
  the residue characteristic, and the local degree, *together with* a field isomorphism
  `σ : K₂' ≃+* K₁'` mapping the embedded `K₂` onto the embedded `K₁` and realizing `Φ` (i.e.
  carrying the place `Φ A` of `K₂'` to the place `A` of `K₁'`).  The existence of this `σ` is the
  genuinely deep part of the reconstruction (Neukirch CoNF XII §12.2 constructs it from Čebotarev;
  Shimizu's Theorems 4.0–4.3 give the base-field isomorphism and the extension step), and it is
  isolated here as the field `sigma` of the structure.

* **(b) `FrobeniusCorrespondence ϕ σ`** — the *Frobenius correspondence*: at corresponding
  (finite) places — the correspondence being the one realized by `σ` — `ϕ` matches the arithmetic
  Frobenius elements.  This is Shimizu's Lemma 2.1.5 (the isomorphism commutes with the `ℓ`-adic
  cyclotomic character, hence maps `Frob_𝔭` to `Frob_{𝔭'}`), in the finite-level form produced by
  `Submission.NK.Chebotarev.FrobeniusCorrespondence`.

* **(c) `ChebotarevInput K K'`** — the Čebotarev density input: every element of the Galois group
  of a finite Galois extension of number fields is an arithmetic Frobenius element at a prime
  unramified in that extension.  This is the classical Čebotarev density theorem; the density form
  used in Shimizu's Prop. 4f.3 (Serre, *Abelian ℓ-adic representations*, Ch. I §2.2 Cor. 2) is
  recovered from it in `NK.Reconstruct.dense_frobeniusSet_of_chebotarev`.

The main theorem of the area, `NK.Reconstruct.exists_sigma_of_localCorrespondence`, is proved from
(a), (b), (c) **together with a candidate field isomorphism `σ`** (the `sigma` field of
`GoodLocalCorrespondence`, resp. hypothesis (d) of the σ-free forms): the Čebotarev input upgrades
the Frobenius correspondence into the identity `ϕ g = σ⁻¹ g σ` for *all* `g : Gal(K₁'/K₁)`.
*Producing* that `σ` from (a) + (b) + (c) is the remaining mathematical input; the two reductions of
it proved in this area are `NK.Reconstruct.exists_realizing_sigma_of_conj_normal` (given one
`MapsBase` isomorphism, the obstruction `Φ_{σ₀} ∘ ϕ⁻¹` must be inner) and
`NK.Reconstruct.exists_sigma_of_weak_and_placeRigidity` (weak half + `PlaceRigidity`).
-/

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- The places of `K'` over the finite primes of the number field `K` (a synonym of
`Submission.NeukirchUchida.FinitePlace`, kept here so that the reconstruction vocabulary is
self-contained). -/
abbrev FinitePlaceOf (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K'] [Algebra K K'] :=
  {A : ValuationSubring K' // A.comap (algebraMap K K') ≠ ⊤}

section Basic

/-- The action of the Galois group on the places over the finite primes. -/
def placeSmul (g : Gal(K₁'/K₁)) (A : FinitePlaceOf K₁ K₁') : FinitePlaceOf K₁ K₁' :=
  ⟨g • A.1, Submission.NeukirchUchida.smul_comap_ne_top g A.2⟩

@[simp] lemma placeSmul_val (g : Gal(K₁'/K₁)) (A : FinitePlaceOf K₁ K₁') :
    (placeSmul g A).1 = g • A.1 := rfl

/-- The action of the Galois group on the places over the finite primes, for the second field. -/
def placeSmul₂ (g : Gal(K₂'/K₂)) (A : FinitePlaceOf K₂ K₂') : FinitePlaceOf K₂ K₂' :=
  ⟨g • A.1, Submission.NeukirchUchida.smul_comap_ne_top g A.2⟩

@[simp] lemma placeSmul₂_val (g : Gal(K₂'/K₂)) (A : FinitePlaceOf K₂ K₂') :
    (placeSmul₂ g A).1 = g • A.1 := rfl

end Basic

/-! ## (c) The Čebotarev density input -/

/-- **The Čebotarev density input.**  Every element of the Galois group of a finite Galois
extension `L/K` of number fields is an arithmetic Frobenius element at a prime of `L` lying over a
prime of `K` that is unramified in `L/K`.

This is the classical Čebotarev density theorem in the finite-level form consumed by the whole
Neukirch–Uchida development (it is exactly the hypothesis `hC` of
`NK.Chebotarev.DenseFrobeniusSet` and of `NK.Chebotarev.ExistsFrobeniusOfRestriction`). -/
def ChebotarevInput (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K'] [Algebra K K'] :
    Prop :=
  ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    (τ : Gal(↥L/K)),
    ∃ (p : NK.Chebotarev.PrimeIdeal K) (P : NK.Chebotarev.PrimeIdeal ↥L),
      P.asIdeal.LiesOver p.asIdeal ∧
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
      NK.Chebotarev.IsFrobAt P τ

/-- **Čebotarev implies the density of the Frobenius elements.**  The form of Čebotarev's theorem
used by Shimizu (Prop. 4f.3; Serre, *Abelian ℓ-adic representations*, Ch. I §2.2 Cor. 2) is the
statement that a Frobenius element with a prescribed restriction to every finite normal
subextension may be found at a single prime `p` of `K`.  This is
`NK.Chebotarev.DenseFrobeniusSet`, restated for the present input. -/
theorem dense_frobeniusSet_of_chebotarev [IsGalois K₁ K₁'] (hc : ChebotarevInput K₁ K₁') :
    Dense {σ : Gal(K₁'/K₁) | ∃ p : NK.Chebotarev.PrimeIdeal K₁,
      ∀ (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L],
        ∃ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver p.asIdeal ∧
          NK.Chebotarev.IsFrobAt P (AlgEquiv.restrictNormalHom L σ)} :=
  NK.Chebotarev.DenseFrobeniusSet (K := K₁) (K' := K₁') hc

/-! ## Frobenius elements of an absolute Galois group -/

/-- **A Frobenius element of the absolute Galois group.**  An element of `Gal(K'/K)` is a
*Frobenius element* if it is an arithmetic Frobenius element at some prime of some finite normal
subextension of `K'/K`.  These elements topologically generate `Gal(K'/K)`
(`NK.Reconstruct.topologicalClosure_isFrobElement_eq_top`), which is why an isomorphism of absolute
Galois
groups agreeing on them is determined (`NK.Reconstruct.eq_of_eq_on_isFrobElement`). -/
def IsFrobElement (g : Gal(K₁'/K₁)) : Prop :=
  ∃ (L : IntermediateField K₁ K₁') (_ : FiniteDimensional K₁ L) (_ : Normal K₁ L)
    (_ : NumberField ↥L) (p : NK.Chebotarev.PrimeIdeal K₁) (P : NK.Chebotarev.PrimeIdeal ↥L),
    P.asIdeal.LiesOver p.asIdeal ∧
      NK.Chebotarev.IsFrobAt P (AlgEquiv.restrictNormalHom L g)

/-- `IsFrobElement` unfolded: a witness is a finite normal level, a prime of its ring of integers
and a prime of `K` below it. -/
theorem isFrobElement_iff (g : Gal(K₁'/K₁)) :
    IsFrobElement g ↔
      ∃ (L : IntermediateField K₁ K₁') (_ : FiniteDimensional K₁ L) (_ : Normal K₁ L)
        (_ : NumberField ↥L) (p : NK.Chebotarev.PrimeIdeal K₁)
        (P : NK.Chebotarev.PrimeIdeal ↥L),
        P.asIdeal.LiesOver p.asIdeal ∧
          NK.Chebotarev.IsFrobAt P (AlgEquiv.restrictNormalHom L g) :=
  Iff.rfl

/-! ## (a) The good local correspondence -/

/-- **The good local correspondence** — input (a) of the reconstruction, *without* the realizing
field isomorphism: the local correspondence of CoNF (12.1.9) (Shimizu, Theorem 2.5).

The fields are:

* `placeMap`: the induced Galois-equivariant bijection of the place systems over the finite primes;
* `map_smul`: Galois-equivariance of `placeMap`;
* `map_decomp`: compatibility of `placeMap` with `ϕ` on decomposition groups;
* `primeMap`: the induced bijection of the finite primes of the two number fields;
* `primeMap_spec`: coherence of `placeMap` and `primeMap` (the prime below a place maps to the prime
  below its image);
* `residueChar`: preservation of the residue characteristic;
* `localDegree`: preservation of the local degree `[K_𝔭 : ℚ_p]` (expressed as `f(𝔭/p)·e(𝔭/p)`). -/
structure LocalCorrespondence (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) where
  /-- the bijection of the place systems over the finite primes -/
  placeMap : FinitePlaceOf K₁ K₁' ≃ FinitePlaceOf K₂ K₂'
  /-- the place map is Galois-equivariant -/
  map_smul : ∀ (g : Gal(K₁'/K₁)) (A : FinitePlaceOf K₁ K₁'),
    placeMap (placeSmul g A) = placeSmul₂ (ϕ g) (placeMap A)
  /-- the place map is compatible with `ϕ` on decomposition groups -/
  map_decomp : ∀ A : FinitePlaceOf K₁ K₁',
    (Submission.NeukirchUchida.decompositionGroup A.1).map
        (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
      Submission.NeukirchUchida.decompositionGroup (placeMap A).1
  /-- the induced correspondence of finite primes -/
  primeMap : NK.Chebotarev.PrimeIdeal K₁ ≃ NK.Chebotarev.PrimeIdeal K₂
  /-- coherence of the two correspondences -/
  primeMap_spec : ∀ A : FinitePlaceOf K₁ K₁',
    primeMap (Submission.NeukirchUchida.primeOf A.1 A.2) =
      Submission.NeukirchUchida.primeOf (placeMap A).1 (placeMap A).2
  /-- preservation of the residue characteristic -/
  residueChar : ∀ (A : FinitePlaceOf K₁ K₁') (ℓ : ℕ),
    CharP (NumberField.RingOfIntegers K₁ ⧸
        (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) ℓ →
      CharP (NumberField.RingOfIntegers K₂ ⧸
        (Submission.NeukirchUchida.primeOf (placeMap A).1 (placeMap A).2).asIdeal) ℓ
  /-- preservation of the local degree `[K_𝔭 : ℚ_p]` -/
  localDegree : ∀ A : FinitePlaceOf K₁ K₁',
    ((Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.inertiaDeg ℤ) *
        ((Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.ramificationIdx ℤ) =
      ((Submission.NeukirchUchida.primeOf (placeMap A).1 (placeMap A).2).asIdeal.inertiaDeg ℤ) *
        ((Submission.NeukirchUchida.primeOf (placeMap A).1 (placeMap A).2).asIdeal.ramificationIdx ℤ)

/-- **The good local correspondence realized by a field isomorphism** — input (a) of the
reconstruction in the form in which the core theorem
`NK.Reconstruct.exists_sigma_of_localCorrespondence` consumes it: the local correspondence
`LocalCorrespondence ϕ` of CoNF (12.1.9) together with a field isomorphism `σ : K₂' ≃+* K₁'`
mapping the embedded copy of `K₂` onto the embedded copy of `K₁` and realizing the place
correspondence.

The existence of this `σ` is the genuinely deep part of the reconstruction (Neukirch CoNF XII §12.2,
resp. Shimizu §4, Theorems 4.0–4.3 followed by the extension step); it is isolated here as the
field `sigma`.  It can be assembled from the group-theoretic input
`Submission.NeukirchUchida.RealizesPlaceMap` by
`NK.Reconstruct.goodLocalCorrespondenceOf` together with
`NK.Reconstruct.comap_placeMap_eq_of_realizesPlaceMap`. -/
structure GoodLocalCorrespondence (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    extends LocalCorrespondence ϕ where
  /-- the realizing field isomorphism -/
  sigma : K₂' ≃+* K₁'
  /-- it maps the embedded copy of `K₂` onto the embedded copy of `K₁` -/
  sigma_mapsBase : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') sigma
  /-- it realizes the place correspondence -/
  sigma_realizes : ∀ A : FinitePlaceOf K₁ K₁',
    (placeMap A).1.comap (sigma.symm : K₁' →+* K₂') = A.1

end NK.Reconstruct

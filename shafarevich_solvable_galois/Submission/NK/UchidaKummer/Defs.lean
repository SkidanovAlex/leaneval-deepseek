/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.UchidaKummer`: the reconstruction by Uchida's Kummer method

Reference: the LaTeX sources of arXiv:2601.01251, *Pro-`ℓ`-by-cyclotomic and tamely ramified
variants of the Neukirch–Uchida Theorem*, §5 (*Full Neukirch–Uchida*) and §6 (*Weak
Neukirch–Uchida*), specialised to the separable closures `Ω_i = K̄_i`, where the `ℓ`-sealed and
abundance hypotheses are automatic.

This file fixes the vocabulary of the area; `README.md` records the interface.  Briefly:

* **(A)** the place correspondence `NK.Reconstruct.LocalCorrespondence ϕ` is *given* (produced by
  `Submission/Work/BrauerHasse/` and the local structure theory);
* **(K)** the Kummer-theoretic inputs of §5 are `IsKummerSurjective` (Prop. `K^x/K^ell local
  surjection`), `IsDifferentiable` (§5 Lemma `lem:ell prime differentiation`) and the
  full-density prime identification of §5 `lem:alpha identifies with sigma on primes`;
* **(W)** the *weak* Neukirch–Uchida theorem of §6 is `IsWeakUchida`, whose input — Uchida's
  Kummer-theoretic embedding problem — is `IsKummerEmbeddingProblem`.

Everything here is a definition or a proved consequence; the named inputs above are `Prop`-valued
definitions, so a caller can state theorems conditionally on them.
-/

import Mathlib
import Submission.NK.Chebotarev.Basic
import Submission.NK.Reconstruct.Basic
import Submission.NeukirchUchida.Conjugation
import Submission.NeukirchUchida.Detection
import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.NK.Reconstruct.LevelMap
import Submission.NK.LocalAnabelian.Kummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.UchidaKummer

open IsDedekindDomain

noncomputable section

/-! ## Local degrees and completely split primes -/

section LocalDegrees

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The local degree** `[L_𝔓 : K_𝔭] = e(𝔓|𝔭) · f(𝔓|𝔭)`, written multiplicatively as in
`NK.Reconstruct.LocalCorrespondence.localDegree`. -/
def localDeg (P : NK.Chebotarev.PrimeIdeal L) (p : NK.Chebotarev.PrimeIdeal K) : ℕ :=
  P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
    P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)

/-- The primes of `𝓞 L` above the prime `p` of `𝓞 K`. -/
def primesAbove (p : NK.Chebotarev.PrimeIdeal K) : Set (NK.Chebotarev.PrimeIdeal L) :=
  {P | P.asIdeal.LiesOver p.asIdeal}

/-- **`p` splits completely in `L / K`**: the number of primes of `𝓞 L` above `p` is the degree
`[L : K]`, equivalently (for `L/K` Galois) every such prime is unramified of residue degree one.

This is the predicate of
`Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely`. -/
def SplitsCompletely (p : NK.Chebotarev.PrimeIdeal K) : Prop :=
  (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank K L

/-- The predicate `SplitsCompletely` is the contraction of the defining condition. -/
theorem splitsCompletely_iff (p : NK.Chebotarev.PrimeIdeal K) :
    SplitsCompletely (L := L) p ↔
      (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank K L :=
  Iff.rfl

/-- The primes in `primesAbove` are exactly the primes lying over `p`. -/
theorem mem_primesAbove {p : NK.Chebotarev.PrimeIdeal K} {P : NK.Chebotarev.PrimeIdeal L} :
    P ∈ primesAbove (L := L) p ↔ P.asIdeal.LiesOver p.asIdeal :=
  Iff.rfl

/-- **The prescribed local degree condition of §5.**  The extension `L/K` has local degree
`a i` at the place `𝔭 i`: every prime of `𝓞 L` above `𝔭 i` has `e · f = a i`. -/
def HasLocalDegrees {ι : Type*} (𝔭 : ι → NK.Chebotarev.PrimeIdeal K) (a : ι → ℕ) : Prop :=
  ∀ i : ι, ∀ P : NK.Chebotarev.PrimeIdeal L, P.asIdeal.LiesOver (𝔭 i).asIdeal →
    localDeg P (𝔭 i) = a i

/-- Unfolding of `HasLocalDegrees`. -/
theorem hasLocalDegrees_iff {ι : Type*} (𝔭 : ι → NK.Chebotarev.PrimeIdeal K) (a : ι → ℕ) :
    HasLocalDegrees (L := L) 𝔭 a ↔
      ∀ i : ι, ∀ P : NK.Chebotarev.PrimeIdeal L, P.asIdeal.LiesOver (𝔭 i).asIdeal →
        localDeg P (𝔭 i) = a i :=
  Iff.rfl

end LocalDegrees

/-! ## Full-density sets of primes -/

/-- **A set of primes of full Dirichlet density**: its complement has Dirichlet density `0`. -/
def HasFullDensity (K : Type*) [Field K] [NumberField K]
    (R : Set (NK.Chebotarev.PrimeIdeal K)) : Prop :=
  NumberField.Set.HasDirichletDensity Rᶜ 0

/-- Unfolding of `HasFullDensity`. -/
theorem hasFullDensity_iff (K : Type*) [Field K] [NumberField K]
    (R : Set (NK.Chebotarev.PrimeIdeal K)) :
    HasFullDensity K R ↔ NumberField.Set.HasDirichletDensity Rᶜ 0 :=
  Iff.rfl

/-! ## The Kummer-theoretic inputs of §5 -/

/-- The subgroup of `ℓ`-th powers in the unit group of a field. -/
def ellPowSubgroup (k : Type*) [Field k] (ℓ : ℕ) : Subgroup kˣ :=
  (powMonoidHom ℓ : kˣ →* kˣ).range

section KummerInputs

variable (K : Type*) [Field K] [NumberField K]

/-- **The local `ℓ`-power class of a global unit.**  For a finite prime `𝔮` of `K`, this is the
composite `Kˣ → K_𝔮ˣ → K_𝔮ˣ / (K_𝔮ˣ)^ℓ`. -/
def localPowClass (ℓ : ℕ) (𝔮 : NK.Chebotarev.PrimeIdeal K) :
    Kˣ →* (𝔮.adicCompletion K)ˣ ⧸ ellPowSubgroup (𝔮.adicCompletion K) ℓ :=
  (QuotientGroup.mk' (ellPowSubgroup (𝔮.adicCompletion K) ℓ)).comp
    (Units.map (algebraMap K (𝔮.adicCompletion K)).toMonoidHom)

/-- **Weak approximation** for a number field at a finite set of finite primes: the diagonal
image of `K` in `∏_{𝔮 ∈ S} K_𝔮` is dense.

This is the approximation theorem of Neukirch, *Algebraic Number Theory*, Chap. II, 5.7 (the
"Chinese remainder theorem" quoted in the proof of §5's Prop. `K^x/K^ell local surjection`).  It is
the analytic/algebraic input behind `IsKummerSurjective`. -/
def IsWeakApproximation (K : Type*) [Field K] [NumberField K]
    (S : Finset (NK.Chebotarev.PrimeIdeal K)) : Prop :=
  DenseRange fun a : K => fun 𝔮 : S => algebraMap K (𝔮.1.adicCompletion K) a

/-- The subgroup of `ℓ`-th powers of the unit group of a completion is open.  This is the local
input of the proof of `IsKummerSurjective`: `K_𝔮ˣ/(K_𝔮ˣ)^ℓ` is finite (from the structure theory
`K_𝔮ˣ ≅ ℤ × μ × U¹`, `U¹ ≅ ℤ_p^d`), so `(K_𝔮ˣ)^ℓ` is a closed subgroup of finite index. -/
def IsOpenEllPowSubgroup (K : Type*) [Field K] [NumberField K] (ℓ : ℕ) : Prop :=
  ∀ 𝔮 : NK.Chebotarev.PrimeIdeal K,
    IsOpen ((ellPowSubgroup (𝔮.adicCompletion K) ℓ : Subgroup (𝔮.adicCompletion K)ˣ) :
      Set (𝔮.adicCompletion K)ˣ)

/-- **The Kummer local surjection of §5** (nu2d, Proposition `K^x/K^ell local surjection`).

For a number field `K` and a finite set `S` of finite primes, the map
`Kˣ / (Kˣ)^ℓ → ∏_{𝔮 ∈ S} K_𝔮ˣ / (K_𝔮ˣ)^ℓ` is surjective: every tuple of local `ℓ`-power classes
is the diagonal image of a global unit class.

In the paper this is deduced from the weak approximation theorem for number fields (the diagonal
image of `K` in `∏_{𝔮 ∈ S} K_𝔮` is dense, and the `ℓ`-th power subgroups are open); the Chinese
remainder theorem is quoted in Neukirch's *Algebraic Number Theory*, Chap. II, 5.7.

It is *not* used to prove the present file's theorems — it is the input of the differentiation
lemma `IsDifferentiable`. -/
def IsKummerSurjective (ℓ : ℕ) (S : Finset (NK.Chebotarev.PrimeIdeal K)) : Prop :=
  ∀ y : ∀ 𝔮 : S,
      (𝔮.1.adicCompletion K)ˣ ⧸ ellPowSubgroup (𝔮.1.adicCompletion K) ℓ,
    ∃ b : Kˣ, ∀ 𝔮 : S, localPowClass K ℓ 𝔮.1 b = y 𝔮

end KummerInputs

/-- **The local Kummer dichotomy** (the local content of §5's differentiation lemma).

For a Kummer extension `L = K(a^{1/ℓ})` of `K` inside `K'`, a finite prime `𝔭` of `K` splits
completely in `L` — equivalently every prime `P` of `𝓞 L` above `𝔭` has `e · f = 1` — exactly when
`a` is an `ℓ`-th power in the completion `K_𝔭`.

This is the statement that makes the Kummer method work: it converts the `ℓ`-divisibility of the
local classes of an element of `Kˣ` into the splitting/ramification behaviour of `K(a^{1/ℓ})`. -/
def IsKummerLocalDichotomy (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) : Prop :=
  ∀ (a : Kˣ) (L : IntermediateField K K') (_ : FiniteDimensional K L) (_ : NumberField ↥L),
    L = NK.LocalAnabelian.kummerField (K' := K') ℓ a → ∀ 𝔮 : NK.Chebotarev.PrimeIdeal K,
      ((∀ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver 𝔮.asIdeal →
          localDeg P 𝔮 = 1) ↔
        ∃ b : (𝔮.adicCompletion K)ˣ,
          algebraMap K (𝔮.adicCompletion K) (a : K) = (b : 𝔮.adicCompletion K) ^ ℓ)

/-! ## The differentiation lemma of §5 -/

section Differentiation

variable (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K'] [Algebra K K']

/-- **The differentiation lemma of §5** (nu2d, Lemma `lem:ell prime differentiation`), in the
separable-closure setting.

Let `K` be a number field containing `μ_ℓ` (the containment is not part of this definition: it is
needed for the proof, via Kummer theory; for `Ω = K̄` the constructibility of the relevant Kummer
extensions inside `K'` is automatic).  For any finite list `𝔭` of distinct finite primes of `K`
and any prescription `a : Fin n → ℕ` of non-negative exponents, there is a finite extension
`L / K` inside `K'` whose local degree at `𝔭 i` is `ℓ ^ (a i)` for every `i`.

The extension need *not* be Galois (the paper remarks this explicitly). -/
def IsDifferentiable (ℓ : ℕ) : Prop :=
  ∀ (n : ℕ) (𝔭 : Fin n → NK.Chebotarev.PrimeIdeal K), Function.Injective 𝔭 →
    ∀ a : Fin n → ℕ,
      ∃ (L : IntermediateField K K') (_ : FiniteDimensional K L) (_ : NumberField ↥L),
        HasLocalDegrees (L := ↥L) 𝔭 fun i => ℓ ^ a i

/-- **The Kummer machinery over all finite intermediate fields.**

This is the uniform form of the two Kummer inputs of §5, quantified over every finite intermediate
field `E` of `K'/K` *with its own separable closure* `K'`.  The base change is essential: §5's
differentiation lemma is proved by induction, and after exhibiting `K(α^{1/ℓ})` with local degree
`ℓ` at `𝔭` one re-applies the construction with `K(α^{1/ℓ})` as the base field.  Working with a
fixed base field `K` only yields composita of radicals of `K`, whose local degree at a prime `𝔭`
with `ℓ ∤ 𝔭` and `μ_ℓ ⊆ K` is bounded by `ℓ ^ dim_{𝔽_ℓ} K_𝔭ˣ/(K_𝔭ˣ)^ℓ = ℓ ^ 2`.

The four components are

* `μ_ℓ ⊆ E`;
* the local Kummer surjection `IsKummerSurjective E ℓ S` for every finite `S`
  (§5 Prop. `K^x/K^ell local surjection`);
* a local unit at each prime of `E` which is not an `ℓ`-th power (this is what makes the
  differentiation *separate* the primes);
* the local dichotomy `IsKummerLocalDichotomy E K' ℓ`. -/
def HasKummerMachinery (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) : Prop :=
  ∀ (E : IntermediateField K K') (_ : FiniteDimensional K E) (_ : NumberField ↥E)
    (_ : IsSepClosure ↥E K'),
    (∃ ζ : ↥E, IsPrimitiveRoot ζ ℓ) ∧
    (∀ S : Finset (NK.Chebotarev.PrimeIdeal ↥E), IsKummerSurjective ↥E ℓ S) ∧
    (∀ 𝔭 : NK.Chebotarev.PrimeIdeal ↥E, ∃ u : (𝔭.adicCompletion ↥E)ˣ,
      ∀ b : (𝔭.adicCompletion ↥E)ˣ, b ^ ℓ ≠ u) ∧
    IsKummerLocalDichotomy ↥E K' ℓ

end Differentiation

/-! ## The prime-identification step of §5 -/

section PrimeIdentification

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The prime-identification input of the Kummer route** (§5 Lemmas `lem:ell prime
differentiation` + `lem:alpha identifies with sigma on primes`).

The Kummer method produces a `MapsBase` field isomorphism `σ : K₂' ≃+* K₁'` together with:

* the *level correspondence* `AgreesOnLevels ϕ hϕ σ hσ`: `σ` carries the finite Galois
  subextensions of `K₁'/K₁` onto the subextensions of `K₂'/K₂` corresponding to them under `ϕ`
  (this is the σ-free content of CoNF (12.1.9), i.e. input (A) of the development);
* the *place identification*: outside a set of primes of Dirichlet density zero, `σ` realises the
  place correspondence `a` of `ϕ`.

The paper's `lem:alpha identifies with sigma on primes` produces exactly this: an isomorphism
`σ : K₁' → K₂'` induced by a base-field isomorphism and carrying `α(𝔓)` to `𝔓` for every place
`𝔓` over the primes of a full-density set.  The *finiteness* of the set of isomorphisms
`K₁ → K₂` is what upgrades "for every finite `R' ⊆ R`" to "for all of `R`".

The conclusion `Conjugates σ ϕ` is *not* part of the input; the upgrade from the density-one
place identification to the group-theoretic statement is
`NK.UchidaKummer.Identification.conjugates_of_kummerPrimeIdentification`, and it is where the
completely split primes enter (`NK.UchidaKummer.SplitPrimes`). -/
def KummerPrimeIdentification {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) : Prop :=
  ∃ (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
    NK.Reconstruct.AgreesOnLevels ϕ hϕ σ hσ ∧
      ∃ R : Set (NK.Chebotarev.PrimeIdeal K₁), HasFullDensity K₁ R ∧
        ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
          Submission.NeukirchUchida.primeOf A.1 A.2 ∈ R →
            (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1

end PrimeIdentification

/-! ## The σ-free identification step of §5 -/

section PrimeMapStep

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}

/-- **§5 Lemma 5.2 (`lem:alpha identifies with sigma on primes`), σ-free form.**

There is an isomorphism `τ` of the *base fields* `K₁ ≃+* K₂` whose induced correspondence of finite
primes agrees with the prime correspondence `a.primeMap` of the local correspondence outside a set
of primes of Dirichlet density zero.

This is *σ-free*: it speaks of a base-field isomorphism, not of a field isomorphism `K₂' ≃+* K₁'`.

**Recorded negative finding.**  Two reviewers of the derivation
`KummerPrimeMapStep → ∃ σ, Conjugates σ ϕ` both judged it insufficient: prime-level agreement does
not give the *place*-level realization, because for a place `A` over `𝔭 ∈ R` one only learns that
`a.placeMap A` and `A.comap σ` both lie over `τ 𝔭`, and the Galois group acts transitively on the
places over `τ 𝔭`, leaving an uncontrolled twist.  In this workspace prime compatibility and place
realization are indeed independent inputs (`Work/ReconstructField/Targets.lean`).  So the honest
input of §5's identification step is necessarily *place*-level: `KummerPrimeIdentification`. -/
def KummerPrimeMapStep (ℓ : ℕ) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) : Prop :=
  ∃ (τ : K₁ ≃+* K₂) (R : Set (NK.Chebotarev.PrimeIdeal K₁)), HasFullDensity K₁ R ∧
    ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K₁, 𝔭 ∈ R →
      a.primeMap 𝔭 = NK.Reconstruct.primeTransport τ 𝔭

end PrimeMapStep

/-- **The weak Neukirch–Uchida theorem at levels** (§6 in the form §5 consumes), *σ-free*.

For every finite Galois level `L` of `K₁'/K₁`, the corresponding level `levelMap ϕ L` of `K₂'/K₂`
is ring-isomorphic to `L`, compatibly with the two base fields (`MapsBaseLevel`).  No field
isomorphism of the *separable closures* is asserted: this is a family of isomorphisms of finite
levels only.

§5 obtains this by applying its weak theorem to the pair `(L, levelMap ϕ L)` (via the induced
isomorphism `Gal(K₁'/L) ≃* Gal(K₂'/levelMap ϕ L)`); the base compatibility is the step of §5's
`lem:alpha identifies with sigma on primes` that invokes the arithmetic equivalence
"the Galois closure of `K₂` intersected with `Ω₂` is `K₂`", which is the classical Perlis input.

**Caveat.**  As an input of §5's identification step this is *not* sufficient by itself: §5's
compactness argument needs the level isomorphisms to be mutually compatible (there they are the
restrictions of a single element of `Gal(K₂'/K₂)`), and an arbitrary family of level
isomorphisms need not be.  Adding that compatibility makes the datum equivalent to a single
`MapsBase` isomorphism, i.e. to the conclusion.  The definition is kept as the precise vocabulary
of "§6 at levels". -/
def IsWeakUchidaLevels {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] (ℓ : ℕ)
    {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ) : Prop :=
  ∀ (L : IntermediateField K₁ K₁') (_ : FiniteDimensional K₁ L) (_ : IsGalois K₁ L)
    (_ : NumberField ↥L),
    ∃ (τ : ↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L)),
      NK.Reconstruct.MapsBaseLevel L (NK.Reconstruct.levelMap ϕ L) τ

/-! ## The weak Neukirch–Uchida theorem of §6 -/

/-- **Uchida's Kummer-theoretic embedding problem** (nu2d §6, Lemma `lem:embedding problem`).

For a finite Galois extension `L / ℚ` and a finite set `S` of primes of `L` there is a finite
abelian extension `M / L`, Galois over `ℚ`, of degree `ℓ ^ |Gal(L/ℚ)|` over `L`, in which every
prime of `S` splits completely.  (In the paper `Gal(M/L) ≅ 𝔽_ℓ[Gal(L/ℚ)]^n` as a module for
`Gal(L/ℚ)`; the module structure — which is what the arithmetic-equivalence argument uses — is
not recorded here, only the underlying group-theoretic content of degrees and splitting.)

The existence of the completely split primes used in the proof is unconditional in this workspace,
`Commons.NumberTheory.NumberField.exists_prime_splitsCompletely`; the rest of the proof is Kummer
theory (`IsKummerSurjective`). -/
def IsKummerEmbeddingProblem (ℓ : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L],
    (∃ ζ : L, IsPrimitiveRoot ζ ℓ) →
    ∀ (S : Finset (NK.Chebotarev.PrimeIdeal L)),
      ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra L M) (_ : FiniteDimensional L M)
        (_ : IsGalois L M),
        (∀ 𝔮 : S, SplitsCompletely (K := L) (L := M) 𝔮.1) ∧
        Nat.card Gal(M/L) = ℓ ^ Nat.card Gal(L/ℚ)

/-- **The weak Neukirch–Uchida theorem** (nu2d §6, Theorem `thm:uchida isomorphism`), in the
separable-closure case `Ω_i = K̄_i`, where the `ℓ`-sealed and abundance hypotheses are automatic
(a separable closure has no nontrivial finite extension, hence no `ℤ/ℓ`-extension in which places
can split completely; and its completions are separably closed, hence abundant).

Number fields containing `μ_ℓ` with isomorphic absolute Galois groups are isomorphic.  The
existence of the isomorphism is what §6 proves, from `IsKummerEmbeddingProblem` together with the
arithmetic-equivalence theory of Perlis. -/
def IsWeakUchida (ℓ : ℕ) : Prop :=
  ∀ (K₁ K₂ : Type) [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
    (K₁' : Type) [Field K₁'] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']
    (K₂' : Type) [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂'],
    Nonempty (Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) → Nonempty (K₁ ≃+* K₂)

end

end NK.UchidaKummer

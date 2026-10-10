import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.FrobeniusBridge.Core
import Submission.NK.ResidueFrob.decompositionToAdjoin_bijective
import Submission.NK.ResidueFrob.isSepClosure_adjoinPlaceCompletion

/-!
# The residue-field dictionary at a place: the identification of the decomposition group

This file builds the *explicit* identification of the decomposition group `D_A` of a place `A` of
`K'` over a prime `𝔭` of `K` with the absolute Galois group of the local field `κ = K_𝔭` that is
used by the rest of `Submission/Work/ResidueFrob/`.

The identification `NK.FrobeniusBridge.localGaloisEquiv A` of the sibling area is defined as
`Classical.choice` of a `Nonempty`, so no property of it beyond the fact that it *is* an isomorphism
can be extracted from its definition.  The point of this file is that this is enough: by
`NK.LocalTame.isFrobeniusLiftOfDecomposition_iff_of_localIso` the predicate
`NK.LocalAnabelian.IsFrobeniusFor` (and hence `NK.FrobeniusBridge.localFrobAt`) does not depend
on the chosen identification, as soon as the local structure input `NK.LocalTame.TameData` is
available.  We may therefore compute with our own identification `localGaloisEquivAdjoin`, which is
*built* from

* the isomorphism `D_A ≃* Gal(M/K_𝔭)` with `M = K_𝔭·K' ⊆ placeCompletion A`, given by restricting
  the continuous extension of `σ ∈ D_A` to `M` (`NK.NeukirchUchida.decompositionToAdjoin`), and
* an isomorphism `M ≃ₐ[K_𝔭] SeparableClosure K_𝔭` of separable closures.

The payoff is `IsFrobeniusFor D.p D.q (localGaloisEquivAdjoin A u) → ∀ ζ, u ζ = ζ ^ D.q`: a Frobenius
lift at `A`, read through the *explicit* identification, acts on the roots of unity of `K'` (of
order prime to `p`) by `ζ ↦ ζ ^ q`.
-/

namespace NK.ResidueFrob

open scoped Pointwise Classical
open IntermediateField

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

section Adjoin

variable (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (A : ValuationSubring K')
  (hA : A.comap (algebraMap K K') =
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
  [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
    (NK.NeukirchUchida.placeCompletion A)]
  (halg : ∀ z : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p,
    algebraMap _ _ z = NK.NeukirchUchida.adicCompletionToPlaceCompletion p A hA z)


/-- **The restriction of the extension of `σ ∈ D_A` to `M = K_𝔭·K'`**, as a monoid homomorphism
(in `Submission/Work/NeukirchUchida/nonempty_mulEquiv_decompositionGroupOf_adjoin.lean` it is only a
function; we need the monoid structure in order to build a `MulEquiv` whose underlying function is
this map). -/
noncomputable def decompositionAdjoinHom :
    NK.Mine.decompositionGroupOf K K' A →*
      (NK.NeukirchUchida.adjoinPlaceCompletion p A ≃ₐ[
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K p]
        NK.NeukirchUchida.adjoinPlaceCompletion p A) where
  toFun σ := NK.NeukirchUchida.decompositionToAdjoin p A hA halg σ
  map_one' := by
    refine NK.NeukirchUchida.algEquiv_ext_adjoin p A hA halg _ _ fun y => ?_
    rw [NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin p A hA halg 1 y]
    rfl
  map_mul' σ τ := by
    refine NK.NeukirchUchida.algEquiv_ext_adjoin p A hA halg _ _ fun y => ?_
    rw [AlgEquiv.mul_apply,
      NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin p A hA halg τ y,
      NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin p A hA halg σ (τ.1 y),
      NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin p A hA halg (σ * τ) y]
    rfl

@[simp]
theorem decompositionAdjoinHom_apply (σ : NK.Mine.decompositionGroupOf K K' A) :
    decompositionAdjoinHom p A hA halg σ
      = NK.NeukirchUchida.decompositionToAdjoin p A hA halg σ := rfl

/-- **The identification `D_A ≃* Gal(M/K_𝔭)`** whose underlying function is
`NK.NeukirchUchida.decompositionToAdjoin`. -/
noncomputable def decompositionAdjoinEquiv
    (hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion p A hA) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K p) :
    NK.Mine.decompositionGroupOf K K' A ≃*
      (NK.NeukirchUchida.adjoinPlaceCompletion p A ≃ₐ[
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K p]
        NK.NeukirchUchida.adjoinPlaceCompletion p A) :=
  MulEquiv.ofBijective (decompositionAdjoinHom p A hA halg)
    (decompositionToAdjoin_bijective p A hA halg hW)

@[simp]
theorem decompositionAdjoinEquiv_apply
    (hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion p A hA) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K p)
    (σ : NK.Mine.decompositionGroupOf K K' A) :
    decompositionAdjoinEquiv p A hA halg hW σ
      = NK.NeukirchUchida.decompositionToAdjoin p A hA halg σ := rfl

/-- The image of `y : K'` in the adjoining field `M = K_𝔭·K'`, as a ring homomorphism. -/
noncomputable def coInAdjoinHom :
    K' →+* (NK.NeukirchUchida.adjoinPlaceCompletion p A) where
  toFun y := NK.NeukirchUchida.coInAdjoin p A y
  map_one' := NK.NeukirchUchida.coInAdjoin_one p A
  map_mul' a b := NK.NeukirchUchida.coInAdjoin_mul p A a b
  map_zero' := NK.NeukirchUchida.coInAdjoin_zero p A
  map_add' a b := NK.NeukirchUchida.coInAdjoin_add p A a b

theorem coInAdjoinHom_injective : Function.Injective (coInAdjoinHom p A) := by
  intro a b hab
  have h1 : ((NK.NeukirchUchida.coInAdjoin p A a : NK.NeukirchUchida.adjoinPlaceCompletion p A) :
      NK.NeukirchUchida.placeCompletion A) =
      ((NK.NeukirchUchida.coInAdjoin p A b : NK.NeukirchUchida.adjoinPlaceCompletion p A) :
        NK.NeukirchUchida.placeCompletion A) := by
    exact congrArg (fun z : NK.NeukirchUchida.adjoinPlaceCompletion p A =>
      (z : NK.NeukirchUchida.placeCompletion A)) hab
  rw [NK.NeukirchUchida.coe_coInAdjoin, NK.NeukirchUchida.coe_coInAdjoin] at h1
  exact RingHom.injective (NK.NeukirchUchida.placeCompletionCoe A) h1

/-- The isomorphism of separable closures `M ≃ₐ[K_𝔭] κ̄` used to define
`localGaloisEquivAdjoin`. -/
noncomputable def adjoinSepEquiv :
    ↥(NK.NeukirchUchida.adjoinPlaceCompletion p A) ≃ₐ[
      IsDedekindDomain.HeightOneSpectrum.adicCompletion K p]
      SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) := by
  haveI : IsSepClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion p A) :=
    isSepClosure_adjoinPlaceCompletion p A hA halg
  exact IsSepClosure.equiv (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
    ↥(NK.NeukirchUchida.adjoinPlaceCompletion p A)
    (SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p))

/-- **The explicit identification of `D_A` with the local absolute Galois group**: the composite of
the map `σ ↦ σ̂|_M` with an isomorphism of separable closures. -/
noncomputable def adjoinLocalIso
    (hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion p A hA) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K p) :
    NK.Mine.decompositionGroupOf K K' A ≃*
      Gal(SeparableClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) /
        IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) :=
  (decompositionAdjoinEquiv p A hA halg hW).trans (AlgEquiv.autCongr (adjoinSepEquiv p A hA halg))

/-- **The extraction of the action on roots of unity.**  For a Frobenius lift at `A` read through
the explicit identification `adjoinLocalIso`, and a root of unity in `K'` of order prime to `p`,
the element `u` acts on it by `ζ ↦ ζ ^ q`. -/
theorem actsOnRootsOfUnity_of_isFrobeniusFor_adjoinLocalIso
    (hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion p A hA) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K p)
    {p' q : ℕ} {u : Gal(K'/K)} (hu : u ∈ NK.Mine.decompositionGroupOf K K' A)
    (h : NK.LocalAnabelian.IsFrobeniusFor p' q (adjoinLocalIso p A hA halg hW ⟨u, hu⟩)) :
    ∀ n : ℕ, ¬ p' ∣ n → ∀ ζ : K', IsPrimitiveRoot ζ n → u ζ = ζ ^ q := by
  haveI : IsSepClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion p A) :=
    isSepClosure_adjoinPlaceCompletion p A hA halg
  intro n hn ζ hζ
  have hInj : Function.Injective (coInAdjoinHom p A) :=
    fun a b h => coInAdjoinHom_injective p A h
  set ι := adjoinSepEquiv p A hA halg with hι
  have hζ' : IsPrimitiveRoot (NK.NeukirchUchida.coInAdjoin p A ζ) n :=
    hζ.map_of_injective hInj
  have hη : IsPrimitiveRoot (ι (NK.NeukirchUchida.coInAdjoin p A ζ)) n :=
    hζ'.map_of_injective ι.injective
  have hkey := h.2 n hn (ι (NK.NeukirchUchida.coInAdjoin p A ζ)) hη
  have hpow : NK.NeukirchUchida.coInAdjoin p A (ζ ^ q)
      = (NK.NeukirchUchida.coInAdjoin p A ζ) ^ q :=
    map_pow (coInAdjoinHom p A) ζ q
  have hcoe : NK.NeukirchUchida.coInAdjoin p A (u ζ)
      = NK.NeukirchUchida.coInAdjoin p A (ζ ^ q) := by
    apply ι.injective
    have h1 : ι (NK.NeukirchUchida.coInAdjoin p A (u ζ))
        = (ι (NK.NeukirchUchida.coInAdjoin p A ζ)) ^ q := by
      rw [← hkey]
      simp only [hι, adjoinLocalIso, MulEquiv.trans_apply, AlgEquiv.autCongr_apply,
        AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, decompositionAdjoinEquiv_apply,
        NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin]
    rw [h1, hpow, map_pow ι (NK.NeukirchUchida.coInAdjoin p A ζ) q]
  exact hInj hcoe

end Adjoin

/-! ## The chosen identification of `D_A` with the local absolute Galois group -/

section Place

variable (A : NK.FrobeniusBridge.FinitePlaceOf K K')

/-- **Our identification of the decomposition group of the place `A` with the absolute Galois group
of the local field** `Gal(κ̄/κ)`, built from the explicit map `σ ↦ σ̂|_M` and an isomorphism
`M ≃ₐ[κ] κ̄` of separable closures.

It is an isomorphism `D_A ≃* Gal(κ̄/κ)`, so by
`NK.LocalTame.isFrobeniusLiftOfDecomposition_iff_of_localIso` (which uses the local structure
input `NK.LocalTame.TameData`) the predicate `NK.LocalAnabelian.IsFrobeniusFor` takes the same
value on `localGaloisEquivAdjoin A σ` as on `NK.FrobeniusBridge.localGaloisEquiv A σ` — see
`isFrobeniusFor_localGaloisEquivAdjoin_iff`. -/
noncomputable def localGaloisEquivAdjoin :
    Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1 ≃*
      Gal(NK.FrobeniusBridge.localClosure A / NK.FrobeniusBridge.localField A) :=
  letI : Algebra (NK.FrobeniusBridge.localField A)
      (NK.NeukirchUchida.placeCompletion A.1) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion
      (Submission.NeukirchUchida.primeOf A.1 A.2) A.1
      (Submission.NeukirchUchida.primeOf_spec A.1 A.2)).toAlgebra
  adjoinLocalIso (Submission.NeukirchUchida.primeOf A.1 A.2) A.1
    (Submission.NeukirchUchida.primeOf_spec A.1 A.2) (fun z => rfl)
    (NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
      (Submission.NeukirchUchida.primeOf A.1 A.2) A.1
      (Submission.NeukirchUchida.primeOf_spec A.1 A.2))

/-- **The independence of the local Frobenius predicate from the chosen identification.**  For a
place `A` with local data (`p`, `q`, `NK.LocalTame.TameData`, see
`NK.FrobeniusBridge.PlaceLevelData`) and any `σ ∈ D_A`, the element `σ` is a local Frobenius lift
for the identification `localGaloisEquivAdjoin A` if and only if it is one for the identification
`NK.FrobeniusBridge.localGaloisEquiv A`. -/
theorem isFrobeniusFor_localGaloisEquivAdjoin_iff {p q : ℕ}
    (hT : NK.LocalTame.TameData p q (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A))
    (σ : Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1) :
    NK.LocalAnabelian.IsFrobeniusFor p q (localGaloisEquivAdjoin A σ) ↔
      NK.LocalAnabelian.IsFrobeniusFor p q (NK.FrobeniusBridge.localGaloisEquiv A σ) := by
  have h := NK.LocalTame.isFrobeniusLiftOfDecomposition_iff_of_localIso hT
    (localGaloisEquivAdjoin A) (NK.FrobeniusBridge.localGaloisEquiv A) σ
  simpa only [NK.LocalTame.IsFrobeniusLiftOfDecomposition] using h

/-- **The extraction of the action on roots of unity, in the vocabulary of a place.**  If `u` is a
Frobenius lift at the place `A` — read through the explicit identification
`localGaloisEquivAdjoin A` — then `u` acts on every root of unity in `K'` of order prime to `p` by
`ζ ↦ ζ ^ q`. -/
theorem actsOnRootsOfUnity_of_isFrobeniusFor_localGaloisEquivAdjoin
    {p q : ℕ} {u : Gal(K'/K)}
    (hu : u ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1)
    (h : NK.LocalAnabelian.IsFrobeniusFor p q (localGaloisEquivAdjoin A ⟨u, hu⟩)) :
    ∀ n : ℕ, ¬ p ∣ n → ∀ ζ : K', IsPrimitiveRoot ζ n → u ζ = ζ ^ q := by
  letI : Algebra (NK.FrobeniusBridge.localField A)
      (NK.NeukirchUchida.placeCompletion A.1) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion
      (Submission.NeukirchUchida.primeOf A.1 A.2) A.1
      (Submission.NeukirchUchida.primeOf_spec A.1 A.2)).toAlgebra
  exact actsOnRootsOfUnity_of_isFrobeniusFor_adjoinLocalIso
    (Submission.NeukirchUchida.primeOf A.1 A.2) A.1
    (Submission.NeukirchUchida.primeOf_spec A.1 A.2) (fun z => rfl)
    (NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
      (Submission.NeukirchUchida.primeOf A.1 A.2) A.1
      (Submission.NeukirchUchida.primeOf_spec A.1 A.2)) hu h


end Place

end NK.ResidueFrob

import Submission.NK.Reconstruct.PlaceCorrespondence
import Submission.NK.LocalTame.Global
import Submission.NK.Chebotarev.FrobRestriction
import Submission.NeukirchUchida.Local.InfiniteDecomposition

/-!
# The Frobenius bridge: vocabulary

This area bridges the *local* Frobenius correspondence delivered by `Submission/Work/LocalTame/`
(the elements of the decomposition group of a place that act on the prime-to-`p` roots of unity of
the local field by `ζ ↦ ζ ^ q`) to the *finite level, residue-field* Frobenius statement
`NK.Reconstruct.FrobeniusCorrespondencePlace` consumed by the Neukirch–Uchida endgame.

The two vocabularies are

* `NK.FrobeniusBridge.frobAtLevel A L g`: `g : Gal(K'/K)` restricts to an *arithmetic Frobenius*
  at the prime of the finite normal level `L` below the place `A`
  (`NK.Chebotarev.IsFrobAt`, the residue-field normalisation);
* `NK.FrobeniusBridge.IsFrobAtPlace A g`: the same condition at **every** finite normal level
  `L` — the *infinite-level* (or "σ-free place-level") Frobenius predicate;
* `NK.FrobeniusBridge.localFrobAt A g`: the **local** condition, phrased through the
  identification `D_A ≃* Gal(κ̄/κ)` of the decomposition group of `A` with the absolute Galois
  group of the local field `κ = K_𝔭`, and `NK.LocalAnabelian.IsFrobeniusFor` (action on the
  prime-to-`p` roots of unity by `ζ ↦ ζ ^ q`).

The bridge between the two is the named input `NK.FrobeniusBridge.PlaceLevelBridge` (see
`Bridge.lean`), a restatement of the classical Frobenius normalisation in residue-field form
(NSW (12.1.8) Lemma; Shimizu, arXiv:2009.10431, Lemma 2.1) that `Submission/Work/LocalTame/`
records in root-of-unity form.
-/

namespace NK.FrobeniusBridge

open scoped Classical Pointwise

universe u

set_option linter.unusedSectionVars false

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The places of `K'` over the finite primes of `K` (a local synonym, to keep the statements of
this area readable). -/
abbrev FinitePlaceOf (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K'] [Algebra K K'] :=
  NK.Reconstruct.FinitePlaceOf K K'

/-- **The level-wise Frobenius condition at a place**: the restriction of `g` to the finite normal
level `L` is an arithmetic Frobenius at the prime of `𝓞 L` below the place `A`. -/
noncomputable def frobAtLevel (A : FinitePlaceOf K K') (L : IntermediateField K K')
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L] (g : Gal(K'/K)) : Prop :=
  NK.Chebotarev.IsFrobAt (NK.Reconstruct.primeOfLevel A.1 L
    (NK.Reconstruct.comap_level_ne_top A.2 L)) (AlgEquiv.restrictNormalHom L g)

/-- `frobAtLevel` unfolded. -/
theorem frobAtLevel_def (A : FinitePlaceOf K K') (L : IntermediateField K K')
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L] (g : Gal(K'/K)) :
    frobAtLevel A L g ↔
      NK.Chebotarev.IsFrobAt (NK.Reconstruct.primeOfLevel A.1 L
        (NK.Reconstruct.comap_level_ne_top A.2 L)) (AlgEquiv.restrictNormalHom L g) :=
  Iff.rfl

/-- **The infinite-level (place-level) Frobenius predicate**: `g` is a Frobenius element at the
place `A` if it restricts to an arithmetic Frobenius at *every* finite normal level below `A`.

This is the "for every finite normal level" form of Shimizu's Lemma 2.1.5 / CoNF (12.1.9); it is
the σ-free substitute for "`g` lies in the Frobenius coset of the decomposition group at `A`". -/
def IsFrobAtPlace (A : FinitePlaceOf K K') (g : Gal(K'/K)) : Prop :=
  ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L],
    frobAtLevel A L g

/-- `IsFrobAtPlace` unfolded. -/
theorem isFrobAtPlace_iff (A : FinitePlaceOf K K') (g : Gal(K'/K)) :
    IsFrobAtPlace A g ↔
      ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L],
        frobAtLevel A L g :=
  Iff.rfl

/-- Every level-wise condition at a single level is a consequence of the infinite-level one. -/
theorem IsFrobAtPlace.frobAtLevel {A : FinitePlaceOf K K'} {g : Gal(K'/K)}
    (h : IsFrobAtPlace A g) (L : IntermediateField K K')
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L] : frobAtLevel A L g :=
  h L

/-! ## The local vocabulary: Frobenius lifts at a place -/

/-- The local field of the place `A`: the `𝔭`-adic completion of `K` at the prime `𝔭` of `K`
below `A`. -/
noncomputable abbrev localField (A : FinitePlaceOf K K') : Type _ :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletion K (Submission.NeukirchUchida.primeOf A.1 A.2)

/-- The separable closure of the local field of the place `A`. -/
noncomputable abbrev localClosure (A : FinitePlaceOf K K') : Type _ :=
  SeparableClosure (localField A)

/-- **The identification of the decomposition group of the place `A` with the absolute Galois
group of the local field**, obtained from
`Submission.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois` (via
`NK.LocalTame.localGaloisEquiv`). -/
noncomputable def localGaloisEquiv (A : FinitePlaceOf K K') :
    Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1 ≃*
      Gal(localClosure A / localField A) :=
  NK.LocalTame.localGaloisEquiv (Submission.NeukirchUchida.primeOf A.1 A.2) A.1
    (Submission.NeukirchUchida.primeOf_spec A.1 A.2)

/-- **The local Frobenius condition at a place** (the vocabulary of `NK.LocalTame`): `g` lies in
the decomposition group of `A` and its image under the identification `localGaloisEquiv A` with
`Gal(κ̄/κ)` is a Frobenius lift for the local field — i.e. it acts on the prime-to-`p` roots of
unity by `ζ ↦ ζ ^ q`, where `p` is the residue characteristic and `q` the residue field
cardinality of the local field.

The local structure inputs `NK.LocalTame.TameData` and `NK.LocalTame.Zl2ResidueChar` for the
local field are required as part of the predicate: they are what makes `p` and `q` the *actual*
residue characteristic and residue field cardinality of the local field. -/
noncomputable def localFrobAt (A : FinitePlaceOf K K') (g : Gal(K'/K)) : Prop :=
  ∃ (hg : g ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1) (p q : ℕ),
    NK.LocalTame.TameData p q (localField A) (localClosure A) ∧
    NK.LocalTame.Zl2ResidueChar p (localField A) (localClosure A) ∧
    NK.LocalAnabelian.IsFrobeniusFor p q (localGaloisEquiv A ⟨g, hg⟩)

/-- `localFrobAt` unfolded. -/
theorem localFrobAt_iff (A : FinitePlaceOf K K') (g : Gal(K'/K)) :
    localFrobAt A g ↔
      ∃ (hg : g ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1)
        (p q : ℕ),
        NK.LocalTame.TameData p q (localField A) (localClosure A) ∧
        NK.LocalTame.Zl2ResidueChar p (localField A) (localClosure A) ∧
        NK.LocalAnabelian.IsFrobeniusFor p q (localGaloisEquiv A ⟨g, hg⟩) :=
  Iff.rfl

/-- The witness of the local data of `localFrobAt`: `g` is a local Frobenius lift at `A` with
local parameters `p`, `q`. -/
theorem localFrobAt.exists_data {A : FinitePlaceOf K K'} {g : Gal(K'/K)} (h : localFrobAt A g) :
    ∃ (hg : g ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1)
      (p q : ℕ),
      NK.LocalTame.TameData p q (localField A) (localClosure A) ∧
      NK.LocalTame.Zl2ResidueChar p (localField A) (localClosure A) ∧
      NK.LocalAnabelian.IsFrobeniusFor p q (localGaloisEquiv A ⟨g, hg⟩) := h

/-- A local Frobenius element at a place lies in the decomposition group of that place. -/
theorem localFrobAt.mem_decompositionGroup {A : FinitePlaceOf K K'} {g : Gal(K'/K)}
    (h : localFrobAt A g) :
    g ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1 :=
  h.choose

end NK.FrobeniusBridge

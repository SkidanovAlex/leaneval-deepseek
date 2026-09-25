import Mathlib
import Submission.NK.NUV2.LCLeaves
import Submission.NK.HasseTwist.Localisation
import Submission.NK.Indecomposed.All
import Submission.NK.BrauerHasse.Main
import Submission.NK.HassePrinciple.LocalUnits

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

/-!
# Neukirch's containment: the arithmetic inputs and the assembly

This module holds the *definitions* and the *assembly* of the leaf
`NK.NUV2.DecompContainment` (Neukirch's containment — the hard half of CoNF (12.1.9),
NSW 12.1.9, Neukirch, Invent. Math. **6** (1969), Theorem 1), together with the proofs of
everything that is not arithmetic.  The arithmetic content is isolated as the structure
`NK.NUV2.LC.LeafInputs`, produced from `hFC` and `hKC` in the sibling modules of
`Submission/Work/NUV2/LC/`.

## The mathematics

Let `K` be a number field with separable closure `K'`, and let `H ≤ Gal(K'/K)` be a **closed**
subgroup topologically isomorphic to the absolute Galois group `Gal(κ'/κ)` of a `p`-adic field
`κ = 𝔮.adicCompletion L` (a completion of a number field).  Then `H` is contained in the
decomposition group `D_A` of a place `A` of `K'` over a finite prime of `K`.

Neukirch's proof has four steps:

1. **a non-zero class exists**: `|H²(H, Z/2)| = 2` for `H ≅ Gal(κ'/κ)`, `κ` `p`-adic
   (local class field theory: `Br(κ)[2] ≅ Z/2`; NSW (7.1.7), (7.2.6)) — `LeafRank.card_global`;
2. **it has a non-zero local component at some place** — the Hasse principle in the labelled form
   (`HasseTwo`, i.e. Albert–Brauer–Hasse–Noether lifted to the fixed field of `H`; global class
   field theory, from `hFC`);
3. **the prime below that place is indecomposed**: at most one non-trivial local group occurs over
   it.  This is Neukirch's rank count, proved *here* (`eq_of_nontrivial_of_surjective_prod`): the
   localisation at the prime `𝔭` below `A` is surjective (NSW (9.2.1) — `LeafRank.surj`) while the
   source has two elements, so the product of the local groups has at most two elements and hence
   at most one non-trivial factor;
4. **the FKS normalizer property** upgrades uniqueness to `H ≤ D_A`: for `h ∈ H`, the conjugate
   place `h • A` is either `A` or — if not — the local group at `h • A` is a conjugate of the local
   group at `A`, hence non-trivial (`ConjTransport`), so the rank count forces the two local groups
   to be equal, contradicting the disjointness of the decomposition groups of distinct places
   (CoNF (12.1.3), `NK.LocalDecomposition.stabSubgroup_inf_eq_bot_of_ne`).
   The step `ConjTransport` is pure profinite-cohomology bookkeeping (the conjugation action on the
   level system), with no arithmetic content.

## Why `p = 2` with trivial coefficients

For `p = 2` the coefficient module `μ_2 = {±1} = Z/2` carries the *trivial* action in every field
of characteristic `≠ 2`, so the twisted (`μ_p`) and the trivial (`Z/p`) coefficient theories agree;
in particular no passage to an open subgroup `Gal(κ'/κ(ζ_p))` (with `κ(ζ_p)` presented as a
completion of a number field) is needed.  The archimedean defect of the Hasse principle at `p = 2`
is excluded by the labelling: `Gal(κ'/κ)` for a `p`-adic `κ` is `2`-torsion-free, so `K'^H` has no
real places (the corrected statement of `Submission/Work/HassePrinciple/README.md` §13.0, §14.3).

## Contents

* `Guarded` — the condition on a finite prime `𝔭` under which the rank count is demanded (a prime
  carrying a non-zero local component);
* `CardGlobalTwo`, `SurjTwo`, `HasseTwo`, `ConjTransport` — the four arithmetic/bookkeeping inputs;
* `LeafRank`, `RankDataTwo`, `LeafInputs` — the bundles;
* `eq_of_nontrivial_of_surjective_prod` — **the rank count**, proved;
* `decompContainment_of_inputs` — **the assembly**, proved;
* `IndecomposedTwo` — the *strong* form of the rank count (all *non-trivial* local groups coincide,
  not only those with non-trivial `H²`), kept because a sibling lemma
  (`Submission/Work/NUV2/LC/indecomposedTwo_of_fc_kc.lean`) is stated against it; it is stronger
  than what the assembly needs.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open IsDedekindDomain
open scoped Pointwise

namespace NK.NUV2.LC

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The guard of the rank data.**  A finite prime `𝔭` of `K` *carries a non-zero local component*
if some class of `H²(H, Z/2)` has a non-zero local component at some place of `K'` over `𝔭`.  This
is the situation in which Neukirch's argument produces the prime, and the prime at which the rank
count (hence the localisation surjectivity and the local computations) is demanded. -/
def Guarded (K K' : Type) [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K']
    (H : Subgroup Gal(K'/K))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : Prop :=
  ∃ (A : NK.HasseTwist.PlacesOverPrime K K' 𝔭)
    (x : NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 H),
    NK.BrauerHasse.H2Profinite.loc 2 H x A.toOverFinitePrime ≠ 0

/-- The `PlacesOverPrime.toOverFinitePrime` of the place over `𝔭` attached to a place over a finite
prime of `K` is that place. -/
lemma toOverFinitePrime_mk {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (A : NK.BrauerHasse.OverFinitePrime K K')
    (h : A.1.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭) :
    NK.HasseTwist.PlacesOverPrime.toOverFinitePrime (K := K) (K' := K') (𝔭 := 𝔭)
      (⟨A.1, h⟩ : NK.HasseTwist.PlacesOverPrime K K' 𝔭) = A :=
  Subtype.ext rfl

/-- A type with a zero and exactly two elements has a non-zero element. -/
theorem exists_ne_zero_of_card_eq_two {X : Type} [Zero X] (h : Nat.card X = 2) :
    ∃ x : X, x ≠ 0 := by
  obtain ⟨x, y, hxy, -⟩ := Nat.card_eq_two_iff.mp h
  rcases eq_or_ne x 0 with hx | hx
  · exact ⟨y, fun hy => hxy (by rw [hx, hy])⟩
  · exact ⟨x, hx⟩

/-- A finite non-trivial type has at least two elements. -/
theorem two_le_card_of_finite_of_nontrivial {X : Type*} [Finite X] [Nontrivial X] :
    2 ≤ Nat.card X := by
  haveI := Fintype.ofFinite X
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- **Neukirch's rank count.**  If `S` is a type with a zero and exactly two elements, `f : S →
∀ i, T i` is surjective and `T i`, `T j` are both non-trivial, then `i = j`.

The proof is the cardinality squeeze of Neukirch's argument in the sharpest form: the composite
`S → T i × T j` is surjective, so `T i × T j` (hence `T i` and `T j`) is finite and
`|T i| * |T j| ≤ |S| = 2`, while non-triviality gives `|T i|, |T j| ≥ 2`. -/
theorem eq_of_nontrivial_of_surjective_prod {ι : Type*} {T : ι → Type*} {S : Type} [Zero S]
    (hS : Nat.card S = 2) {i j : ι} (hi : Nontrivial (T i)) (hj : Nontrivial (T j))
    (f : S → ∀ i, T i) (hf : Function.Surjective f) : i = j := by
  classical
  by_contra hij
  have hSpos : 0 < Nat.card S := by rw [hS]; norm_num
  obtain ⟨hNe, hFin⟩ := Nat.card_pos_iff.mp hSpos
  obtain ⟨s0⟩ := hNe
  have hsurj : Function.Surjective (fun s : S => (f s i, f s j)) := by
    rintro ⟨a, b⟩
    obtain ⟨s₁, hs₁⟩ := hf (Function.update (f s0) i a)
    have h1 : f s₁ i = a := by rw [hs₁, Function.update_self]
    obtain ⟨s₂, hs₂⟩ := hf (Function.update (f s₁) j b)
    have h2 : f s₂ j = b := by rw [hs₂, Function.update_self]
    have h3 : f s₂ i = f s₁ i := by rw [hs₂, Function.update_of_ne hij]
    exact ⟨s₂, by change (f s₂ i, f s₂ j) = (a, b); rw [h3, h1, h2]⟩
  have hfin : Finite (T i × T j) := Finite.of_surjective _ hsurj
  have hfinI : Finite (T i) :=
    Finite.of_injective (fun x : T i => (x, f s0 j)) (fun a b h => (Prod.ext_iff.mp h).1)
  have hfinJ : Finite (T j) :=
    Finite.of_injective (fun x : T j => (f s0 i, x)) (fun a b h => (Prod.ext_iff.mp h).2)
  haveI := hfinI
  haveI := hfinJ
  have hle : Nat.card (T i × T j) ≤ Nat.card S :=
    Nat.card_le_card_of_surjective _ hsurj
  rw [hS, Nat.card_prod] at hle
  have h1 : 2 ≤ Nat.card (T i) := two_le_card_of_finite_of_nontrivial
  have h2 : 2 ≤ Nat.card (T j) := two_le_card_of_finite_of_nontrivial
  nlinarith

/-! ## The arithmetic inputs -/

/-- **The rank data at a labelled subgroup `H ≅ Gal(κ'/κ)`** (`κ` a `p`-adic field), in the guarded
form in which Neukirch's argument produces it:

* `card_global` — `|H²(U, Z/2)| = 2` for every closed subgroups `U ≤ Gal(K'/K)` continuously
  isomorphic to `Gal(κ'/κ)`.  This is local class field theory at `κ`
  (`H²(G_κ, Z/2) ≅ Br(κ)[2] ≅ Z/2`, NSW (7.1.7), (7.2.6)) transported along the labelling.
* `surj` — at a finite prime `𝔭` of `K` carrying a non-zero local component (i.e. `Guarded`), the
  localisation `H²(H, Z/2) → ∏_{A | 𝔭} H²(H ⊓ D_A, Z/2)` is **surjective**: Neukirch's modified
  surjectivity (NSW (9.2.1), the `eq:NeukirchH2modifiedsurj` of his proof), i.e. the cokernel form
  of the global Hasse principle (`Σ_v inv_v = 0`, from the global fundamental class `hFC`). -/
structure LeafRank (K K' κ κ' : Type) [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ'] : Prop where
  /-- the local computation at the labelled subgroups: `|H²(U, Z/2)| = 2`. -/
  card_global : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (↥U ≃ₜ* Gal(κ'/κ)) →
    Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 U) = 2
  /-- Neukirch's modified surjectivity (NSW (9.2.1)) at a prime carrying a non-zero local
  component. -/
  surj : ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
    Nonempty (↥H ≃ₜ* Gal(κ'/κ)) →
    ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      Guarded (K := K) (K' := K') H 𝔭 →
      Function.Surjective (NK.Indecomposed.localisationToTrivial (K := K) (K' := K') 2 H 𝔭)

/-- **The local computation at the labelled subgroups**, for every descent datum: this is the
`card_global` field of `LeafRank`, quantified over all `(K, K', L, 𝔮)`. -/
def CardGlobalTwo : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (L : Type) [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (↥U ≃ₜ* Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) →
    Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 U) = 2

/-- **The colimit cardinality transport**: a continuous isomorphism `↥H ≅ Gal(κ'/κ)` matches the two
colimit descriptions of the profinite cohomology `H²(·, Z/p)`, hence the two cardinalities.  (This is
the *cardinality* form of the transport whose non-vanishing form is
`NK.LocalCFT.Brauer.exists_ne_zero_H2Profinite_of_mulEquiv`; the continuous labelling supplies the
openness of finite-index subgroups that the transport needs.) -/
def H2CardTransport : Prop :=
  ∀ (p : ℕ) (K K' κ κ' : Type) [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
    (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
    (e : ↥H ≃ₜ* Gal(κ'/κ)) →
    Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p H) =
      Nat.card (NK.BrauerHasse.H2Profinite (K := κ) (K' := κ') p ⊤)

/-- **The rank-data cardinality from the local Brauer computation and the colimit transport.**

`NK.BrauerHasse.LocalFieldBrauerCyclic 2 κ κ'` is, by
`NK.LocalCFT.localFieldBrauerCyclic_iff`, the conjunction of the cardinality
`H²(G_κ, Z/2) ≅ Z/2` and the non-vanishing `H²(G_κ, Z/2) ≠ 0`; the transport
`H2CardTransport` carries the cardinality to the labelled subgroups `U ≤ Gal(K'/K)`. -/
theorem cardGlobalTwo_of_localBrauer_of_transport
    (hloc : ∀ (L : Type) [Field L] [NumberField L]
      (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)),
      NK.BrauerHasse.LocalFieldBrauerCyclic (κ := 𝔮.adicCompletion L)
        (κ' := SeparableClosure (𝔮.adicCompletion L)) 2)
    (htrans : H2CardTransport) : CardGlobalTwo := by
  intro K K' _ _ _ _ _ L _ _ 𝔮 U hU he
  obtain ⟨e⟩ := he
  have hcard := (NK.LocalCFT.localFieldBrauerCyclic_iff (p := 2)
    (κ := 𝔮.adicCompletion L) (κ' := SeparableClosure (𝔮.adicCompletion L))).mp (hloc L 𝔮)
  obtain ⟨e0⟩ := hcard.1
  rw [htrans 2 K K' (𝔮.adicCompletion L) (SeparableClosure (𝔮.adicCompletion L)) U hU e]
  rw [Nat.card_congr e0]
  simp [NK.BrauerHasse.Coeff]

/-- **Neukirch's modified surjectivity (NSW (9.2.1))**, for every descent datum: the `surj` field of
`LeafRank`, quantified over all `(K, K', L, 𝔮)`. -/
def SurjTwo : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (L : Type) [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
    Nonempty (↥H ≃ₜ* Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) →
    ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      Guarded (K := K) (K' := K') H 𝔭 →
      Function.Surjective (NK.Indecomposed.localisationToTrivial (K := K) (K' := K') 2 H 𝔭)

/-- **The rank data at every completion**: `LeafRank` for every descent datum. -/
def RankDataTwo : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (L : Type) [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)),
    LeafRank K K' (𝔮.adicCompletion L) (SeparableClosure (𝔮.adicCompletion L))

/-- The rank data from its two halves. -/
theorem rankDataTwo_of_cardGlobalTwo_of_surjTwo (h1 : CardGlobalTwo) (h2 : SurjTwo) :
    RankDataTwo :=
  fun K K' _ _ _ _ _ L _ _ 𝔮 =>
    ⟨fun U hU hκ => h1 K K' L 𝔮 U hU hκ,
      fun H hH hκ 𝔭 hg => h2 K K' L 𝔮 H hH hκ 𝔭 hg⟩

/-- **The Hasse principle in the labelled form, with a *continuous* labelling.**

For every number field `K` with separable closure `K'` and every `p`-adic field
`κ = 𝔮.adicCompletion L`: a class of `H²(H, Z/2)`, where `H ≤ Gal(K'/K)` is closed and continuously
isomorphic to `Gal(κ'/κ)`, all of whose local components at the places of `K'` over the finite
primes of `K` vanish, is zero.

This is Albert–Brauer–Hasse–Noether lifted to the fixed field of `H`, in the labelled form in which
it is true (the `κ`-labelling is not cosmetic: without it the finite-place product misses the
archimedean invariants — the quaternion class `(-1,-1)` over `ℚ(√2)`,
`Submission/Work/HassePrinciple/README.md` §13.1).  Classically it is obtained from the global
fundamental class: the `H²(·, Z/2)`-form of the Hasse principle is Poitou–Tate duality over the
fixed field of `H`, whose arithmetic input is `hFC`. -/
def HasseTwo : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (L : Type) [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
    Nonempty (↥H ≃ₜ* Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) →
    ∀ x : NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 H,
      (∀ A : NK.BrauerHasse.OverFinitePrime K K',
        NK.BrauerHasse.H2Profinite.loc 2 H x A = 0) → x = 0

/-- **The conjugation transport for the profinite cohomology `H²(·, Z/2)`.**

The colimit defining `H2Profinite 2 V` is taken over the finite Galois levels of `K'/K`; an element
`σ ∈ Gal(K'/K)` permutes these levels (`L ↦ σ • L`) and matches the level groups of `V` with those
of `σVσ⁻¹`, so that the cohomologies are isomorphic.  In particular non-triviality is transported.
This is pure profinite-cohomology bookkeeping — no arithmetic enters. -/
def ConjTransport : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K)),
    Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 V) →
    Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2
      (V.map (MulAut.conj σ).toMonoidHom))

/-- The additive map whose components are the localisations `locUnits K L w` of a class of
`H²(Gal(L/K), Lˣ) = Br(L/K)` to the local groups `H²(Γ_w, L_wˣ)` (`Γ_w` the decomposition group of
the place `w` of `L`). -/
noncomputable def locUnitsHom (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    groupCohomology (NK.HassePrinciple.unitsRep K L) 2 →+
      (∀ w : NK.GlobalCFT.Place L,
        groupCohomology (NK.HassePrinciple.localUnitsRep K L w) 2) where
  toFun a := fun w => (NK.HassePrinciple.locUnits K L w).hom a
  map_zero' := by ext w; exact map_zero _
  map_add' a b := by ext w; exact map_add _ a b

/-- **The finite-level localisation index** (Milne, *Class Field Theory*, VIII.4.3): for a finite
Galois extension `L/K` of number fields, the image of the localisation
`H²(Gal(L/K), Lˣ) → ∏_w H²(Γ_w, L_wˣ)` has index `[L : K]` in the product.

Equivalently, the cokernel of the localisation is finite of order `[L:K]` — the order statement that
Neukirch's rank count consumes in place of the invariant-sum relation `Σ_v inv_v = 0`. -/
def LocalisationIndex : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    (locUnitsHom K L).range.index = Nat.card (L ≃ₐ[K] L)

/-- **Neukirch's rank count at a guarded prime, as an input.**

At a finite prime `𝔭` of `K` carrying a non-zero local component (`Guarded`), at most one of the
local groups `H ⊓ D_A` of a closed labelled `H` over `𝔭` has non-trivial `H²(·, Z/2)`.

This is the *conclusion* of Neukirch's rank count (the combination of the localisation surjectivity
NSW (9.2.1) with the cardinality `|H²(H, Z/2)| = 2` of local class field theory), and it is the
part of Neukirch's argument that the FKS normalizer step consumes. -/
def UniqLocal : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (L : Type) [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
    Nonempty (↥H ≃ₜ* Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) →
    ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      Guarded (K := K) (K' := K') H 𝔭 →
      ∀ V W, V ∈ NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K') H 𝔭 →
        W ∈ NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K') H 𝔭 →
        Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 V) →
        Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 W) → V = W

/-- **The strong form of the rank count**: all the *non-trivial* local groups `H ⊓ D_A` of a closed
labelled `H` over a prime carrying a non-zero local component coincide.  (This is stronger than
what the assembly needs, which asks only for the local groups with non-trivial `H²` to coincide; it
is the shape in which the sibling lemma
`Submission/Work/NUV2/LC/indecomposedTwo_of_fc_kc.lean` is stated.) -/
def IndecomposedTwo : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (L : Type) [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
    Nonempty (↥H ≃ₜ* Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) →
    ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      Guarded (K := K) (K' := K') H 𝔭 →
      ∀ V W, V ∈ NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K') H 𝔭 →
        W ∈ NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K') H 𝔭 →
        V ≠ ⊥ → W ≠ ⊥ → V = W

/-- **The arithmetic input of Neukirch's containment**: the rank data (local class field theory at
the labelled subgroups plus Neukirch's modified surjectivity), the Hasse principle in the labelled
form, and the conjugation transport. -/
structure LeafInputs : Prop where
  /-- the rank data at every completion -/
  rank : RankDataTwo
  /-- the Hasse principle at every completion -/
  hasse : HasseTwo
  /-- the conjugation transport of `H²(·, Z/2)` -/
  conj : ConjTransport

/-! ## The assembly -/

/-- **The local group of a place is non-trivial when the local component of a class does not
vanish.**  The local cohomology `LocalH2 2 H A` is the profinite cohomology `H²(H ⊓ D_A, Z/2)` of
the local group (both are the filtered colimit of the same level cohomologies), so a non-zero local
component exhibits two distinct elements of `H²(H ⊓ D_A, Z/2)`. -/
theorem nontrivial_h2Profinite_of_loc_ne_zero {H : Subgroup Gal(K'/K)}
    (A : NK.BrauerHasse.OverFinitePrime K K')
    {x : NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 H}
    (hx : NK.BrauerHasse.H2Profinite.loc 2 H x A ≠ 0) :
    Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2
      (H ⊓ NK.BrauerHasse.stabSubgroup A.1)) := by
  rw [← NK.HassePrinciple.LocalH2_eq_H2Profinite (K := K) (K' := K') 2 H A.1]
  exact ⟨0, NK.BrauerHasse.H2Profinite.loc 2 H x A, fun h => hx h.symm⟩

/-- A place over a finite prime of `K`, viewed as a place over its prime below, satisfies the guard
of the rank data as soon as the class has a non-zero local component there. -/
theorem guarded_of_loc_ne_zero {H : Subgroup Gal(K'/K)}
    (A : NK.BrauerHasse.OverFinitePrime K K')
    {x : NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 H}
    (hx : NK.BrauerHasse.H2Profinite.loc 2 H x A ≠ 0) :
    Guarded (K := K) (K' := K') H (NK.HasseTwist.primeUnder A) := by
  refine ⟨⟨A.1, NK.HasseTwist.primeUnder_spec A⟩, x, ?_⟩
  rw [toOverFinitePrime_mk A (NK.HasseTwist.primeUnder_spec A)]
  exact hx

/-- A subgroup with non-trivial `H²(·, Z/2)` is non-trivial. -/
theorem ne_bot_of_nontrivial_h2Profinite {V : Subgroup Gal(K'/K)}
    (h : Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 V)) : V ≠ ⊥ := by
  intro hbot
  haveI : Subsingleton ↥V := by rw [hbot]; infer_instance
  have hsub : Subsingleton (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 V) :=
    NK.Indecomposed.subsingleton_h2Profinite_of_subsingleton (K := K) (K' := K') 2
  exact (not_subsingleton_iff_nontrivial.mpr h) hsub

/-- **Neukirch's containment from the arithmetic input.**

Let `H ≤ Gal(K'/K)` be closed and topologically isomorphic to `Gal(κ'/κ)` with `κ` a `p`-adic
field (a completion of a number field).  Then `H` is contained in the decomposition group of a
place of `K'` over a finite prime of `K`.

The rank data gives `|H²(H, Z/2)| = 2`, hence a non-zero class `x`; the Hasse principle produces a
place `A` with `x` non-zero locally at `A`; Neukirch's rank count at the prime `𝔭` below `A` (the
surjectivity of the localisation, proved here as `eq_of_nontrivial_of_surjective_prod`) says that
at most one local group over `𝔭` has non-trivial `H²`; and the conjugation transport shows that
the local group of every `H`-conjugate of `A` is non-trivial, so all those local groups coincide —
which by the disjointness of the decomposition groups of distinct places forces every conjugate of
`A` to be `A`, i.e. `H ≤ D_A`. -/
theorem decompContainment_of_inputs (hin : LeafInputs) : NK.NUV2.DecompContainment := by
  intro K K' _ _ _ _ _ H hHcl hHtop
  -- unpack the labelling: `κ = 𝔮.adicCompletion L`, `κ'` its separable closure
  obtain ⟨L, _hLf, _hLn, 𝔮, ⟨e⟩⟩ := hHtop
  have hrank := hin.rank K K' L 𝔮
  have hκ : Nonempty (↥H ≃ₜ* Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) :=
    ⟨e⟩
  -- step 1: a non-zero class in `H²(H, Z/2)`
  have hcardH : Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 H) = 2 :=
    hrank.card_global H hHcl hκ
  obtain ⟨x, hx⟩ := exists_ne_zero_of_card_eq_two hcardH
  -- step 2: the Hasse principle gives a place with a non-zero local component
  have hloc : ∃ A : NK.BrauerHasse.OverFinitePrime K K',
      NK.BrauerHasse.H2Profinite.loc 2 H x A ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (hin.hasse K K' L 𝔮 H hHcl hκ x hcon)
  obtain ⟨A, hA⟩ := hloc
  -- the finite prime below `A`, and `A` as a place over it
  set 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    NK.HasseTwist.primeUnder A with h𝔭def
  have h𝔭 : A.1.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 :=
    NK.HasseTwist.primeUnder_spec A
  let A₀ : NK.HasseTwist.PlacesOverPrime K K' 𝔭 := ⟨A.1, h𝔭⟩
  have hA₀ : A₀.toOverFinitePrime = A := toOverFinitePrime_mk A h𝔭
  have hguard : Guarded (K := K) (K' := K') H 𝔭 :=
    guarded_of_loc_ne_zero (K := K) (K' := K') (H := H) A hA
  -- step 3: the rank count: at most one local group over `𝔭` has non-trivial `H²`
  have huniq : ∀ V W, V ∈ NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K') H 𝔭 →
      W ∈ NK.HasseTwist.localGroupSubgroupsOver (K := K) (K' := K') H 𝔭 →
      Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 V) →
      Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 W) → V = W := by
    intro V W hV hW hVn hWn
    exact Subtype.ext_iff.mp
      (eq_of_nontrivial_of_surjective_prod (T := fun i : ↥(NK.HasseTwist.localGroupSubgroupsOver
          (K := K) (K' := K') H 𝔭) => NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 i.1)
        hcardH (i := ⟨V, hV⟩) (j := ⟨W, hW⟩) hVn hWn
        (NK.Indecomposed.localisationToTrivial (K := K) (K' := K') 2 H 𝔭)
        (hrank.surj H hHcl hκ 𝔭 hguard))
  -- the local group at `A₀` has non-trivial `H²`
  have hVnontriv : Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2
      (H ⊓ NK.BrauerHasse.stabSubgroup A₀.1)) :=
    nontrivial_h2Profinite_of_loc_ne_zero (K := K) (K' := K') (H := H) A hA
  -- step 4: every `H`-conjugate of `A₀` is `A₀`, i.e. `H ≤ D_{A₀}`
  refine ⟨A₀.1, ?_, ?_⟩
  · rw [A₀.2]
    exact NK.HasseTwist.isDedekindDomain_valuationSubringAtPrime_ne_top (K := K) 𝔭
  · intro h hh
    show h • A₀.1 = A₀.1
    by_contra hne
    -- the place `h • A₀.1` is again a place over `𝔭`
    have hA₁mem : (h • A₀.1).comap (algebraMap K K') =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 := by
      rw [NK.LocalDecomposition.comap_smul]; exact A₀.2
    let A₁ : NK.HasseTwist.PlacesOverPrime K K' 𝔭 := ⟨h • A₀.1, hA₁mem⟩
    -- the local group at `h • A₀` is the conjugate of the local group at `A₀`
    have hconj : H ⊓ MulAction.stabilizer Gal(K'/K) A₁.1 =
        (H ⊓ MulAction.stabilizer Gal(K'/K) A₀.1).map (MulAut.conj h).toMonoidHom := by
      have hmapeq : H.map (MulAut.conj h).toMonoidHom = H :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hh)
      rw [show A₁.1 = h • A₀.1 from rfl,
        NK.LocalDecomposition.stabSubgroup_smul (K := K) (K' := K') A₀.1 h,
        Subgroup.map_inf _ _ _ (MulAut.conj h).injective, hmapeq]
    -- hence it has non-trivial `H²`, by the conjugation transport
    have hA₁nontriv : Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2
        (H ⊓ MulAction.stabilizer Gal(K'/K) A₁.1)) := by
      rw [hconj]
      exact hin.conj K K' (H ⊓ MulAction.stabilizer Gal(K'/K) A₀.1) h hVnontriv
    -- the rank count forces the two local groups to be equal
    have heq : H ⊓ MulAction.stabilizer Gal(K'/K) A₀.1
        = H ⊓ MulAction.stabilizer Gal(K'/K) A₁.1 :=
      huniq _ _ ⟨A₀, rfl⟩ ⟨A₁, rfl⟩ hVnontriv hA₁nontriv
    -- the decomposition groups of the distinct places `A₀` and `h • A₀` are disjoint
    have hbot : MulAction.stabilizer Gal(K'/K) A₀.1 ⊓
        MulAction.stabilizer Gal(K'/K) A₁.1 = ⊥ :=
      NK.LocalDecomposition.stabSubgroup_inf_eq_bot_of_ne (A := A₀.1) (A' := A₁.1)
        (by rw [show A₁.1 = h • A₀.1 from rfl]; exact Ne.symm hne)
        (by rw [A₀.2]
            exact NK.HasseTwist.isDedekindDomain_valuationSubringAtPrime_ne_top (K := K) 𝔭)
        (by rw [hA₁mem]
            exact NK.HasseTwist.isDedekindDomain_valuationSubringAtPrime_ne_top (K := K) 𝔭)
    have hVbot : H ⊓ MulAction.stabilizer Gal(K'/K) A₀.1 = ⊥ := by
      have h1 : H ⊓ MulAction.stabilizer Gal(K'/K) A₀.1 ≤
          MulAction.stabilizer Gal(K'/K) A₀.1 ⊓ MulAction.stabilizer Gal(K'/K) A₁.1 := by
        refine le_inf inf_le_right ?_
        exact le_trans (le_of_eq heq) inf_le_right
      rw [hbot] at h1
      exact le_bot_iff.mp h1
    exact ne_bot_of_nontrivial_h2Profinite hVnontriv hVbot

/-- **The assembly from the *strong* rank-count input** (fallback route).

If instead of the rank data one directly has the strong "the prime is indecomposed" statement
`IndecomposedTwo` (all the non-trivial local groups over a prime carrying a non-zero local
component coincide), then the containment follows without the conjugation transport, through the
FKS normalizer lemma `NK.Indecomposed.le_stabSubgroup_of_unique_localGroup` that is already
proved in the workspace. -/
theorem decompContainment_of_cardGlobalTwo_of_indecomposedTwo_of_hasseTwo
    (hcard : CardGlobalTwo) (hind : IndecomposedTwo) (hhasse : HasseTwo) :
    NK.NUV2.DecompContainment := by
  intro K K' _ _ _ _ _ H hHcl hHtop
  obtain ⟨L, _hLf, _hLn, 𝔮, ⟨e⟩⟩ := hHtop
  have hκ : Nonempty (↥H ≃ₜ* Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) :=
    ⟨e⟩
  have hcardH : Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 H) = 2 :=
    hcard K K' L 𝔮 H hHcl hκ
  obtain ⟨x, hx⟩ := exists_ne_zero_of_card_eq_two hcardH
  have hloc : ∃ A : NK.BrauerHasse.OverFinitePrime K K',
      NK.BrauerHasse.H2Profinite.loc 2 H x A ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (hhasse K K' L 𝔮 H hHcl hκ x hcon)
  obtain ⟨A, hA⟩ := hloc
  set 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    NK.HasseTwist.primeUnder A with h𝔭def
  have h𝔭 : A.1.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 :=
    NK.HasseTwist.primeUnder_spec A
  let A₀ : NK.HasseTwist.PlacesOverPrime K K' 𝔭 := ⟨A.1, h𝔭⟩
  have hguard : Guarded (K := K) (K' := K') H 𝔭 :=
    guarded_of_loc_ne_zero (K := K) (K' := K') (H := H) A hA
  have huniq := hind K K' L 𝔮 H hHcl hκ 𝔭 hguard
  have hVne : H ⊓ NK.BrauerTwist.stabSubgroup A₀.1 ≠ ⊥ :=
    NK.Indecomposed.inf_stabSubgroup_ne_bot_of_loc_ne_zero_trivial (K := K) (K' := K') 2 H A hA
  have hle : H ≤ MulAction.stabilizer Gal(K'/K) A₀.1 :=
    NK.Indecomposed.le_stabSubgroup_of_unique_localGroup (K := K) (K' := K') 𝔭 A₀ H hVne
      (fun A' A'' h1 h2 => huniq _ _ ⟨A', rfl⟩ ⟨A'', rfl⟩ h1 h2)
  refine ⟨A₀.1, ?_, hle⟩
  rw [A₀.2]
  exact NK.HasseTwist.isDedekindDomain_valuationSubringAtPrime_ne_top (K := K) 𝔭

/-- **The leaf from the local computation, the rank count, the Hasse principle and the conjugation
transport**: `CardGlobalTwo → UniqLocal → HasseTwo → ConjTransport → DecompContainment`.

The proof is Neukirch's: the cardinality gives a non-zero class `x` and the Hasse principle a place
`A` where `x` is locally non-zero; the rank count (`UniqLocal`) says that no *other* place over the
prime `𝔭` below `A` has non-trivial local group; the conjugation transport (`ConjTransport`) shows
that every `H`-conjugate of `A` would; and the FKS disjointness of the decomposition groups of
distinct places then forces every conjugate of `A` to be `A`, i.e. `H ≤ D_A`. -/
theorem decompContainment_of_card_of_uniq_of_hasse (hcard : CardGlobalTwo) (huniq : UniqLocal)
    (hhasse : HasseTwo) (hconjT : ConjTransport) : NK.NUV2.DecompContainment := by
  intro K K' _ _ _ _ _ H hHcl hHtop
  obtain ⟨L, _hLf, _hLn, 𝔮, ⟨e⟩⟩ := hHtop
  have hκ : Nonempty (↥H ≃ₜ* Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) :=
    ⟨e⟩
  have hcardH : Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 H) = 2 :=
    hcard K K' L 𝔮 H hHcl hκ
  obtain ⟨x, hx⟩ := exists_ne_zero_of_card_eq_two hcardH
  have hloc : ∃ A : NK.BrauerHasse.OverFinitePrime K K',
      NK.BrauerHasse.H2Profinite.loc 2 H x A ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (hhasse K K' L 𝔮 H hHcl hκ x hcon)
  obtain ⟨A, hA⟩ := hloc
  set 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    NK.HasseTwist.primeUnder A with h𝔭def
  have h𝔭 : A.1.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 :=
    NK.HasseTwist.primeUnder_spec A
  let A₀ : NK.HasseTwist.PlacesOverPrime K K' 𝔭 := ⟨A.1, h𝔭⟩
  have hguard : Guarded (K := K) (K' := K') H 𝔭 :=
    guarded_of_loc_ne_zero (K := K) (K' := K') (H := H) A hA
  have huniq := huniq K K' L 𝔮 H hHcl hκ 𝔭 hguard
  have hVnontriv : Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2
      (H ⊓ NK.BrauerHasse.stabSubgroup A₀.1)) :=
    nontrivial_h2Profinite_of_loc_ne_zero (K := K) (K' := K') (H := H) A hA
  refine ⟨A₀.1, ?_, ?_⟩
  · rw [A₀.2]
    exact NK.HasseTwist.isDedekindDomain_valuationSubringAtPrime_ne_top (K := K) 𝔭
  · intro h hh
    show h • A₀.1 = A₀.1
    by_contra hne
    have hA₁mem : (h • A₀.1).comap (algebraMap K K') =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 := by
      rw [NK.LocalDecomposition.comap_smul]; exact A₀.2
    let A₁ : NK.HasseTwist.PlacesOverPrime K K' 𝔭 := ⟨h • A₀.1, hA₁mem⟩
    have hconj : H ⊓ MulAction.stabilizer Gal(K'/K) A₁.1 =
        (H ⊓ MulAction.stabilizer Gal(K'/K) A₀.1).map (MulAut.conj h).toMonoidHom := by
      have hmapeq : H.map (MulAut.conj h).toMonoidHom = H :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hh)
      rw [show A₁.1 = h • A₀.1 from rfl,
        NK.LocalDecomposition.stabSubgroup_smul (K := K) (K' := K') A₀.1 h,
        Subgroup.map_inf _ _ _ (MulAut.conj h).injective, hmapeq]
    have hA₁nontriv : Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2
        (H ⊓ MulAction.stabilizer Gal(K'/K) A₁.1)) := by
      rw [hconj]
      exact hconjT K K' (H ⊓ MulAction.stabilizer Gal(K'/K) A₀.1) h hVnontriv
    have heq : H ⊓ MulAction.stabilizer Gal(K'/K) A₀.1
        = H ⊓ MulAction.stabilizer Gal(K'/K) A₁.1 :=
      huniq _ _ ⟨A₀, rfl⟩ ⟨A₁, rfl⟩ hVnontriv hA₁nontriv
    have hbot : MulAction.stabilizer Gal(K'/K) A₀.1 ⊓
        MulAction.stabilizer Gal(K'/K) A₁.1 = ⊥ :=
      NK.LocalDecomposition.stabSubgroup_inf_eq_bot_of_ne (A := A₀.1) (A' := A₁.1)
        (by rw [show A₁.1 = h • A₀.1 from rfl]; exact Ne.symm hne)
        (by rw [A₀.2]
            exact NK.HasseTwist.isDedekindDomain_valuationSubringAtPrime_ne_top (K := K) 𝔭)
        (by rw [hA₁mem]
            exact NK.HasseTwist.isDedekindDomain_valuationSubringAtPrime_ne_top (K := K) 𝔭)
    have hVbot : H ⊓ MulAction.stabilizer Gal(K'/K) A₀.1 = ⊥ := by
      have h1 : H ⊓ MulAction.stabilizer Gal(K'/K) A₀.1 ≤
          MulAction.stabilizer Gal(K'/K) A₀.1 ⊓ MulAction.stabilizer Gal(K'/K) A₁.1 := by
        refine le_inf inf_le_right ?_
        exact le_trans (le_of_eq heq) inf_le_right
      rw [hbot] at h1
      exact le_bot_iff.mp h1
    exact ne_bot_of_nontrivial_h2Profinite hVnontriv hVbot

end NK.NUV2.LC

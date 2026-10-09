/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.LocalStructure`: the structure theory of the absolute Galois group of a `p`-adic field

This chapter is the *local structure theory* of the absolute Galois group `G_κ = Gal(κ̄/κ)` of a
`p`-adic field `κ = K_𝔭`, in the form in which the Neukirch–Uchida development consumes it.  It
discharges (or reduces to strictly smaller classical statements) the six named inputs listed in
the deliverable

1. `NK.LocalTame.TameStructureInput` — the tame structure theorem (NSW (7.5.7), (7.5.11));
2. `NK.LocalTame.FrobeniusLiftCharacterisation` — the Frobenius normalisation (NSW (12.1.8));
3. `NK.LocalInputs.LocalFieldInputs.principal_units_card` — the `p`-power class count
   `|κˣ/(κˣ)^p| = p^{[κ:ℚ_p]+1+δ}` (Serre, *Local Fields* II §5);
4. `NK.LocalInputs.LocalGaloisInputsOfUnits.proP_unbounded`, `other_bounded` — the pro-`p`
   tower ranks (Ivanov, arXiv:1309.3046, Lemma 3.12; NSW (7.5.11));
5. `NK.BrauerHasse.LocalDecompositionCriterion` — Neukirch's local characterisation of
   decomposition subgroups (Neukirch, Invent. Math. 6 (1969), Theorem 1; CoNF (12.1.9));
6. the local Neukirch–Uchida theorem (Neukirch, Invent. Math. 6 (1969); CoNF (12.1.4)–(12.1.6)).

## Conventions

`κ = 𝔭.adicCompletion K` is the `𝔭`-adic completion of a number field `K` at a finite prime `𝔭`
(`𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)`), and `K'` is a
separable closure of `κ` (`[Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']`).
`q` is the residue field cardinality `residueCard K 𝔭` of `κ`, `d = localDegree K 𝔭` is the
absolute degree `[κ : ℚ_p]`, and `δ = zetaIndicator p κ` is the indicator of `ζ_p ∈ κ`.

The *reduced inputs* are bundled in the structures below; the imports of this chapter show what
each one is reduced *to*.
-/
import Submission.NK.LocalTame.All
import Submission.NK.LocalInputs.All
import Submission.NK.BrauerHasse.All
import Submission.NK.Mine.CommonsAdicSumAPI
import Submission.NeukirchUchida.Conjugation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open scoped Pointwise
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalStructure

universe u

noncomputable section

/-! ## The residue field -/

/-- **The residue field cardinality of the local field `κ = K_𝔭`**, i.e. the `q` of the local
structure theory: `q = #(𝒪_κ/𝔪_κ) = #(𝓞 K/𝔭)`. -/
noncomputable def residueCard (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : ℕ :=
  Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))

/-- **The `p`-torsion of the units of a field**: the roots of `X ^ p = 1`.  For a `p`-adic field
this is `μ_p(κ)`, of order `p ^ δ` with `δ = zetaIndicator p κ`. -/
def pRootsOfUnity (p : ℕ) (κ : Type*) [Monoid κ] : Type _ :=
  {ζ : κ // ζ ^ p = 1}

/-! ## Item 1: the tame structure theorem

The input `NK.LocalTame.TameStructureInput p q κ K'` has eight fields.  Three of them are
*derived* in this chapter:

* `q_eq` — from the arithmetic of the completion, via the commons
  `card_residueField_adicCompletionIntegers_eq_pow_inertiaDeg`
  (`NK.LocalStructure.residueCard_eq_pow_of_charP`);
* `wildInertia_le_inertia` — immediately from `isTameInertia`, whose definition contains
  `V_κ ≤ I_κ`;
* `exists_frobeniusLift` — from `Gal(κ^ur/κ) ≅ Ẑ`: `Ẑ` is non-trivial, so the unramified quotient
  is non-trivial and there is an element outside the inertia
  (`NK.LocalStructure.exists_notMem_inertiaSubgroup_of_unramifiedQuotient`).

What remains is the *core*, recorded below: six fields, of which five are genuinely arithmetic
(the sixth, `tameInertia_commutator_mem`, is the abelian consequence of the pro-cyclicity of
`I_κ/V_κ`; see its docstring for the formalisation gap). -/

/-- **Item 1, reduced: the core of the tame structure theorem for `κ = K_𝔭`.**

The fields are

* `hp` — `p` is a prime;
* `residue_char` — the residue characteristic of `κ` is `p` (elementary, and part of
  `NK.LocalInputs.LocalFieldInputs`);
* `unramifiedQuotient` — `Gal(κ^ur/κ) ≅ Ẑ` (NSW (7.5.6); the input
  `NK.LocalAnabelian.UnramifiedQuotientInput`, owned by the sibling chapter
  `Submission/Work/LocalAnabelian/`; provable from `κ^ur = κ(μ_{p'})` and
  `Gal(𝔽̄_q/𝔽_q) ≅ Ẑ`);
* `isTameInertia` — `I_κ/V_κ` is the maximal closed normal pro-cyclic subgroup of `G_κ/V_κ`
  (NSW (7.5.7) Corollary; Iwasawa);
* `isProPrimeToP_tameInertia` — the tame inertia is pro-prime-to-`p` (NSW (7.5.11)).

Classically the two last fields are the statement that the maximal tamely ramified extension
`κ^{tr}` of `κ` is `κ^ur(κ^{1/n} : (n,p) = 1)` with `Gal(κ^{tr}/κ^ur) ≅ ∏_{ℓ ≠ p} ℤ_ℓ(1)`, so
that `G_κ^{tr} = G_κ/V_κ ≅ Ẑ ⋉ ∏_{ℓ ≠ p} ℤ_ℓ(1)`. -/
structure TameCore (p : ℕ) (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] : Prop where
  hp : p.Prime
  /-- the residue characteristic of `κ = K_𝔭` is `p` -/
  residue_char : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p
  /-- `Gal(κ^ur/κ) ≅ Ẑ`, i.e. the unramified quotient of `G_κ` is the profinite completion of `ℤ` -/
  unramifiedQuotient :
    Nonempty (Gal(K'/𝔭.adicCompletion K) ⧸
      NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p ≃*
        NK.LocalAnabelian.Zhat)
  /-- `I_κ/V_κ` is the maximal closed normal pro-cyclic subgroup of `G_κ/V_κ` -/
  isTameInertia : NK.LocalTame.IsMaxNormalProCyclicInQuotient
    (NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p)
    (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p)
  /-- the tame inertia `I_κ/V_κ` is pro-prime-to-`p` -/
  isProPrimeToP_tameInertia : NK.LocalTame.IsProPrimeToP p
    ↥(NK.LocalTame.tameInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p)
  /-- the tame inertia is abelian modulo the wild inertia: the commutator of two inertia elements
  lies in `V_κ`.  This is the abelian consequence of the pro-cyclicity of `I_κ/V_κ` in
  `isTameInertia`; the formal derivation uses that a compact totally disconnected topological
  group all of whose finite quotients are cyclic is abelian
  (`NK.LocalStructure.commute_of_isProCyclic_of_profinite`), a step that Mathlib does not
  currently support for the quotient `Gal(K'/κ) ⧸ V_κ` (the instance
  `TotallyDisconnectedSpace` of a quotient group is missing), which is why the field is recorded
  rather than derived.  It is a formalisation gap, not a mathematical one. -/
  tameInertia_commutator_mem : ∀ y ∈ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K)
      (K' := K') p,
    ∀ z ∈ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p,
      y * z * y⁻¹ * z⁻¹ ∈ NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K)
        (K' := K') p

/-! ## Item 2: the Frobenius normalisation

`NK.LocalTame.FrobeniusLiftCharacterisation p q κ K'` identifies the Frobenius elements — those
lying outside the inertia subgroup and acting on the prime-to-`p` roots of unity by `ζ ↦ ζ^q`
(`NK.LocalAnabelian.IsFrobeniusFor`) — with the elements conjugating the tame inertia by the
`q`-th power map (`NK.LocalTame.IsTameFrobeniusLift`).

It is reduced below to

* the *normalisation* of the canonical Frobenius: the element `frob` of
  `NK.LocalAnabelian.ResidueCardInput p q κ K'` (which exists because `κ^ur = κ(μ_{p'})` and
  `Gal(κ^ur/κ) ≅ Ẑ` acts on `μ_{p'}` through `ζ ↦ ζ^q`) conjugates `I_κ/V_κ` by the `q`-th power
  map — the forward direction of the cyclotomic character (NSW (12.1.8); Iwasawa);
* the *injectivity* of the cyclotomic character: acting on the tame inertia `I_κ/V_κ` by the
  `q`-th power map forces the action on `μ_{p'}` to be `ζ ↦ ζ^q`. -/

/-- **Item 2, reduced: the Frobenius normalisation.**

The classical input `NK.LocalAnabelian.ResidueCardInput p q κ K'` (the canonical Frobenius,
normalised by `ζ ↦ ζ^q` on the prime-to-`p` roots of unity) together with the two halves of the
cyclotomic character statement (NSW (12.1.8)) — forward and injective. -/
structure TameFrobeniusCore (p q : ℕ) (κ K' : Type*) [Field κ] [Field K']
    [Algebra κ K'] [IsSepClosure κ K'] : Prop where
  hp : p.Prime
  /-- **NSW (12.1.8), forward**: the canonical Frobenius — the element lying outside `I_κ` and
  acting on the prime-to-`p` roots of unity by `ζ ↦ ζ^q` (`NK.LocalAnabelian.IsFrobeniusFor`,
  whose existence is the classical normalisation `NK.LocalAnabelian.ResidueCardInput`) —
  conjugates the tame inertia by the `q`-th power map.  Equivalently, the cyclotomic character
  identifies `G_κ/I_κ ≅ Ẑ` with the cyclic subgroup of `Aut(I_κ/V_κ) = ∏_{ℓ ≠ p} ℤ_ℓ^×`
  generated by the `q`-th power map -/
  exists_frob : ∃ x : Gal(K'/κ), NK.LocalAnabelian.IsFrobeniusFor p q x ∧
    NK.LocalTame.IsTameFrobeniusLift q
      (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
      (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) x
  /-- **NSW (12.1.8), injectivity**: an element acting on the tame inertia `I_κ/V_κ` by the
  `q`-th power map acts on the prime-to-`p` roots of unity by `ζ ↦ ζ^q` -/
  actsAsFrobenius_of_isTameFrobeniusLift : ∀ x : Gal(K'/κ),
    NK.LocalTame.IsTameFrobeniusLift q
      (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
      (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) x →
    NK.LocalAnabelian.ActsAsFrobenius (κ := κ) (K' := K') p q x

/-! ## Item 3: the `p`-power class count

The arithmetic input of `NK.LocalInputs.LocalFieldInputs` is

  `Nat.card (U¹ ⧸ (U¹)^p) = p ^ ([κ : ℚ_p] + δ)`,  `U¹ = 1 + 𝔪_κ` the principal units,

whose classical content (Serre, *Local Fields*, Ch. II §5) is the `p`-adic logarithm: `U¹` modulo
its `p`-power torsion `μ_{p^∞}(κ)` is a free `ℤ_p`-module of rank `d`, so
`U¹/(U¹)^p ≅ (ℤ/p)^d × μ_p(κ)`.  The reduction below makes this splitting explicit. -/

/-- **Item 3, reduced: the `p`-adic logarithm structure of the principal units.**

`U¹/(U¹)^p ≅ (ℤ/p)^{[κ:ℚ_p]} × μ_p(κ)`: the `p`-th power quotient of the principal units splits
as the image of `𝔪/p𝔪` (of order `p^d`, under the logarithm) and the `p`-torsion `μ_p(κ)`.
Equivalently — and this is where the content is — the `p`-adic logarithm identifies `U¹/μ_{p^∞}(κ)`
with the additive group `𝔪_κ` of rank `d` over `ℤ_p`. -/
structure PrincipalUnitsCore (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (p : ℕ) : Prop where
  hp : p.Prime
  /-- `U¹/(U¹)^p ≅ (ℤ/p)^{[κ:ℚ_p]} × μ_p(κ)`: the `p`-th power quotient of the principal units
  has order `p^d` times the number of `p`-th roots of unity in `κ` -/
  quot_torsion : Nat.card (↥(NK.LocalInputs.principalUnits K 𝔭) ⧸
      (powMonoidHom p).range) =
    p ^ NK.LocalInputs.localDegree K 𝔭 *
      Nat.card (pRootsOfUnity p (𝔭.adicCompletion K))

/-! ## Item 4: the pro-`p` tower ranks

Ivanov's Lemma 3.12 (arXiv:1309.3046) — equivalently the Demushkin structure of `G_κ^{(p)}`,
NSW (7.5.11) — says

* for `ℓ = p` the ranks of the `p`-Frattini quotients of the open subgroups of `G_κ` with
  `p`-power index (`HasUnboundedTowerRank p (G_κ)`) are unbounded;
* for `ℓ ≠ p` they are bounded.

The abelian rank of `G_κ` is *already* available in this workspace
(`NK.LocalInputs.hasAbelianFrattiniRank_of_lubinTate`, `..._of_isPrimitiveRoot_adicCompletion`);
what is missing is the passage to finite `p`-power extensions, which is what the structure below
records: the abelian rank of `Gal(K'/M)` for the finite extensions `M/κ` of `p`-power degree
(each of which gives an open subgroup of `p`-power index), and — in the other direction — the
boundedness of the number of degree-`ℓ` extensions of `M` for `ℓ ≠ p`. -/

/-- **Item 4, reduced: the tower-rank data.**

* `abelian_tower` — the number of degree-`p` extensions of the finite `p`-power extensions of
  `κ` is unbounded; classically the number of index-`p` subgroups of `Gal(κ̄/M)` is
  `(p^{[M:ℚ_p] + 1 + δ_M} - 1)/(p - 1)`, which grows with `[M : κ]` (NSW (7.5.11), Demushkin),
  and `NK.LocalStructure.le_numIndexSubgroups_of_hasAbelianFrattiniRank` is the conversion from
  the abelian rank `HasAbelianFrattiniRank p r` to this count.
* `card_extensions_le` — for `ℓ ≠ p` the number of degree-`ℓ` extensions of `M` is bounded,
  uniformly over the finite extensions `M/κ` of `ℓ`-power degree; classically this is Kummer
  theory plus the fact that the maximal pro-`ℓ` extension of a `p`-adic field is free pro-`ℓ` of
  rank `≤ 2` (NSW (7.5.7)).
* `finiteIndex_isClosed` — Nikolov–Segal: `Gal(κ̄/M)` is topologically finitely generated, so every
  finite-index subgroup is open (hence closed).  The tower-rank predicate `HasUnboundedTowerRank`
  quantifies over all finite-index subgroups; this field is what reduces it to the closed ones,
  i.e. to the Galois-theoretic levels. -/
structure TowerRankCore (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] (p : ℕ) : Prop where
  hp : p.Prime
  /-- the number of degree-`p` extensions of the finite `p`-power extensions `M/κ` grows without
  bound: for every `N` there is `M/κ` of degree `p ^ e` whose absolute Galois group has more than
  `N` index-`p` subgroups.  Classically the number of index-`p` subgroups of `Gal(κ̄/M)` is
  `(p^{[M:ℚ_p] + 1 + δ_M} - 1)/(p - 1)` (NSW (7.5.11), Demushkin; `δ_M = 1` iff `ζ_p ∈ M`), so it
  grows without bound with `[M : κ]` (`NK.LocalStructure.le_numIndexSubgroups_of_hasAbelianFrattiniRank`
  converts the abelian rank `HasAbelianFrattiniRank p r` into this count). -/
  abelian_tower : ∀ N : ℕ, ∃ (M : IntermediateField (𝔭.adicCompletion K) K') (e : ℕ),
    Module.finrank (𝔭.adicCompletion K) M = p ^ e ∧
      N < Nat.card {H : Subgroup (Gal(K'/↥M)) // H.index = p}
  /-- for `ℓ ≠ p` the number of degree-`ℓ` extensions of a finite extension `M/κ` of `ℓ`-power
  degree is bounded -/
  card_extensions_le : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∃ B : ℕ,
    ∀ (M : IntermediateField (𝔭.adicCompletion K) K') (e : ℕ),
      Module.finrank (𝔭.adicCompletion K) M = ℓ ^ e →
      Nat.card {L : IntermediateField ↥M K' // Module.finrank ↥M L = ℓ} ≤ B
  /-- **Nikolov–Segal**: every finite-index subgroup of the absolute Galois group of a finite
  extension of `κ` is closed (the group is topologically finitely generated, so every finite-index
  subgroup is open).  This is what lets the tower-rank statements — which quantify over *all*
  finite-index subgroups — be reduced to the Galois-theoretic levels. -/
  finiteIndex_isClosed : ∀ (M : IntermediateField (𝔭.adicCompletion K) K'),
    ∀ H : Subgroup Gal(K'/↥M), H.FiniteIndex → IsClosed (H : Set Gal(K'/↥M))

/-! ## Item 5: Neukirch's local characterisation of decomposition subgroups -/

/-- **Item 5, reduced (a): the local Brauer/localisation step.**

Neukirch's Theorem 1 (Invent. Math. 6 (1969); CoNF (12.1.9), (12.1.5)): a class in `H²(H, ℤ/p)`
whose localisation at a place `A` above a finite prime is non-zero forces `H` into the
decomposition group of `A`, and of *finite index* in it.  This is the local computation of the
Brauer group (`Br(κ)[p] ≅ ℤ/p` for a `p`-adic field `κ`, local class field theory — the sibling
chapter `Submission/Work/LocalCFT/`) together with the Hasse principle: the restriction map
`Br(κ)[p] → Br(L)[p]` for a finite extension `L/κ` is multiplication by the degree, so a non-zero
local component forces the local degree to be prime to `p` (hence finite). -/
structure LocalBrauerLocalisation (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- a non-zero local component at a place over a finite prime puts `H` in the decomposition
  group of a place, with finite index -/
  exists_stabilizer : ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
    Nonempty (H ≃* Gal(κ'/κ)) → ∀ (A : NK.BrauerHasse.OverFinitePrime K K')
      (x : NK.BrauerHasse.H2Profinite p H),
    NK.BrauerHasse.H2Profinite.loc p H x A ≠ 0 →
    ∃ A' : ValuationSubring K', A'.comap (algebraMap K K') ≠ ⊤ ∧
      H ≤ MulAction.stabilizer Gal(K'/K) A' ∧
        0 < H.relIndex (MulAction.stabilizer Gal(K'/K) A')

/-- **Item 5, reduced (c): the finishing step of Neukirch's Theorem 1.**

Neukirch, *Kennzeichnung der `p`-adischen und der endlichen algebraischen Zahlkörper*,
Invent. Math. **6** (1969), Theorem 1; CoNF (12.1.9) "if".  This is the *global* arithmetic core of
the criterion: a closed, self-normalising subgroup `H ≤ G_K` which is contained in the decomposition
group of a place over a finite prime with finite index, and which is isomorphic to the absolute
Galois group of a `p`-adic field, is itself the decomposition group of a place over a finite prime.

This is where Neukirch's Korollar 1 (`NK.LocalStructure.Korollar1Local`, derived here from the
local Neukirch–Uchida statement) is consumed: passing to the local field `L = K_𝔭` of the place,
the finite-index subgroup `H ≤ D_A` becomes the absolute Galois group of a finite extension `N/L`
(`NK.LocalStructure.Brauer.exists_intermediateField_of_le_stabilizer`), and Korollar 1 identifies
`N` with the `p`-adic field `κ` whose Galois group `H` is.  The step formalised here is the one that
produces, from that local identification, a *place* whose full decomposition group is `H` — the
"indecomposed prime" argument, which is global. -/
def LocalFinishingStep (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) → Subgroup.normalizer H = H →
    Nonempty (H ≃* Gal(κ'/κ)) →
    ∀ (A : ValuationSubring K'), A.comap (algebraMap K K') ≠ ⊤ →
      H ≤ MulAction.stabilizer Gal(K'/K) A →
        0 < H.relIndex (MulAction.stabilizer Gal(K'/K) A) →
      ∃ A' : ValuationSubring K', A'.comap (algebraMap K K') ≠ ⊤ ∧
        MulAction.stabilizer Gal(K'/K) A' = H

/-- **Item 5, reduced (b): Neukirch's Korollar 1 in the form of the local reconstruction of a
`p`-adic field.**

Neukirch's Korollar 1 (Invent. Math. 6 (1969), cf. CoNF (12.1.4)–(12.1.6)) is the statement that
the absolute Galois group of a `p`-adic field determines the field.  In the form consumed by
Neukirch's Theorem 1 it reads: if `M` is a finite extension of a `p`-adic field `L` (realised
inside a separable closure `L'`) and the absolute Galois group `Gal(L'/M)` of `M` is isomorphic to
the absolute Galois group of a `p`-adic field `κ`, then `M ≅ κ` as fields.

The hypothesis is stated through the fixing subgroup `H = M.fixingSubgroup` of the finite
extension, so that it is phrased purely in the group-theoretic vocabulary of the criterion.

*Note.*  The conclusion is deliberately `κ ≅ M` and **not** `H = Gal(L'/L)`: the latter is false,
since for `M/L` finite of degree `> 1` the subgroup `Gal(L'/M) ≤ Gal(L'/L)` is itself the absolute
Galois group of a `p`-adic field `M`, but is properly contained in `Gal(L'/L)`.  In Neukirch's
argument the reconstruction is what upgrades the inclusions among the local groups to equalities
of the corresponding *fields*.

This is derived in `NK.LocalStructure.korollar1Local_of_localNUExistence` from the local
Neukirch–Uchida existence statement (item 6) together with the Galois correspondence; it is the
local input (b) of the deliverable's item 5. -/
def Korollar1Local (p : ℕ) : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    (M : IntermediateField (𝔮.adicCompletion L) L')
    (H : Subgroup Gal(L'/𝔮.adicCompletion L)),
    H = M.fixingSubgroup → H.FiniteIndex →
      Nonempty (H ≃* Gal(K'/𝔭.adicCompletion K)) →
      Nonempty (↥M ≃+* 𝔭.adicCompletion K)

/-! ## Item 6: the local Neukirch–Uchida theorem -/

/-! The local Neukirch–Uchida theorem (Neukirch, *Kennzeichnung der `p`-adischen und der
endlichen algebraischen Zahlkörper*, Invent. Math. 6 (1969); CoNF (12.1.4)–(12.1.6)): every
isomorphism `Gal(κ̄/κ) ≃* Gal(κ̄'/κ')` of absolute Galois groups of `p`-adic fields is induced by a
field isomorphism `κ ≅ κ'`, *unique* up to inner automorphisms.

Every `p`-adic field is presented below as either a completion `𝔭.adicCompletion K` of a number
field or as a *finite extension* `M` of such a completion inside a separable closure; that is the
generality needed by the development, and it keeps the statement on the side of what is true (the
same statement for arbitrary fields is false: `𝔽̄_p` and `ℂ` both have trivial absolute Galois
group but are not isomorphic as fields). -/

/-- **Item 6, existence (the classical input).**  Let `M` be a finite extension of a `p`-adic
field `𝔮.adicCompletion L`, realised inside a separable closure `L'`, and let `𝔭.adicCompletion K`
be another `p`-adic field with separable closure `K'`.  Every isomorphism of absolute Galois groups
`Gal(L'/M) ≃* Gal(K'/𝔭.adicCompletion K)` forces `M ≅ 𝔭.adicCompletion K` — Neukirch's local
theorem (CoNF (12.1.4)–(12.1.5)).

Taking `M = ⊥` recovers the two-completions form, and taking a finite extension `M` covers the
form of Neukirch's Korollar 1 used by Neukirch's Theorem 1
(`NK.LocalStructure.korollar1Local_of_localNUExistence`). -/
def LocalNUExistence : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (M : IntermediateField (𝔮.adicCompletion L) L')
    [FiniteDimensional (𝔮.adicCompletion L) ↥M]
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'],
    Nonempty (Gal(L'/↥M) ≃* Gal(K'/𝔭.adicCompletion K)) →
    Nonempty (↥M ≃+* 𝔭.adicCompletion K)

/-- **Item 6, the canonical (strong) form**: the inducing field isomorphism, on the level of the
separable closures, conjugated with the group isomorphism — `Conjugates σ Φ` in the vocabulary of
`Submission.NeukirchUchida.Conjugation`.  This is the form in which the theorem is stated in the
literature (CoNF Thm. 12.2.1, local case); `NK.LocalStructure.LocalNUUniqueness` is the matching
uniqueness statement. -/
def LocalNUExistenceConjugates : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (M : IntermediateField (𝔮.adicCompletion L) L')
    [FiniteDimensional (𝔮.adicCompletion L) ↥M]
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    (Φ : Gal(L'/↥M) ≃* Gal(K'/𝔭.adicCompletion K)),
    ∃ σ : K' ≃+* L', Submission.NeukirchUchida.Conjugates σ Φ

/-- **Item 6, uniqueness** — the local analogue of CoNF (12.1.6): the inducing field isomorphism
is unique.  (Stated for `p`-adic fields, where it is Neukirch's rigidity statement; the analogous
statement for arbitrary fields is false.) -/
def LocalNUUniqueness : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    (Φ : Gal(L'/𝔮.adicCompletion L) ≃* Gal(K'/𝔭.adicCompletion K))
    (σ₁ σ₂ : K' ≃+* L'),
    Submission.NeukirchUchida.Conjugates σ₁ Φ →
      Submission.NeukirchUchida.Conjugates σ₂ Φ → σ₁ = σ₂

/-! ## Item 6, reduced: the lattice of finite extensions

The local Neukirch–Uchida theorem is not deducible from the invariants of items 1–4 (which determine
only `p`, `q`, `d`, `δ`), so it is reduced here to a *field-theoretic* classical statement, namely
Neukirch's Kennzeichnung: the isomorphism class of a `p`-adic field is determined by its lattice of
finite extensions (with their degrees and inclusions).

The reduction has two halves, of which the first is **proved** in this chapter:

* `NK.LocalStructure.LocalNU.finiteExtensionCorrespondence_of_groupIso` — an isomorphism of
  absolute Galois groups of `p`-adic fields induces a correspondence of the lattices of finite
  extensions, preserving degrees and inclusions (and hence the ramified/unramified type of every
  extension, and the Frobenius correspondence of item 2), by the Galois correspondence and the
  group-theoretic definability of `I_κ` and `V_κ` (items 1–2);
* `NK.LocalStructure.LocalFieldFromFiniteExtensionLattice` — fields with such a correspondence are
  isomorphic (Neukirch, Invent. Math. **6** (1969), the local case of CoNF (12.1.4)–(12.1.5)).

The assembly is `NK.LocalStructure.LocalNU.localNUExistence_of_finiteExtensionLattice`. -/

/-- **A correspondence between the lattices of finite extensions** of two `p`-adic fields (presented
as the base fields of separable closures), induced by a group isomorphism `Φ`.

Concretely: every finite extension `M` of the source is assigned a finite extension `N = level M` of
the target, of the same degree, whose fixing subgroup is the `Φ`-image of the fixing subgroup of
`M`.  Together with the Galois correspondence this determines the inclusion lattice, the
Galois-ness of each level, and — since `Φ` carries the inertia and wild inertia subgroups of items
1–2 — the ramified/unramified and tame/wild type of every extension. -/
structure FiniteExtensionCorrespondence {κ K' κ₂ L' : Type u} [Field κ] [Field K']
    [Algebra κ K'] [Field κ₂] [Field L'] [Algebra κ₂ L'] (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) where
  /-- the finite extension of the target corresponding to a finite extension of the source -/
  level : {M : IntermediateField κ K' // FiniteDimensional κ ↥M} → IntermediateField κ₂ L'
  /-- the corresponding extension is finite over the target -/
  level_finite : ∀ M, FiniteDimensional κ₂ ↥(level M)
  /-- the correspondence preserves degrees -/
  level_finrank : ∀ M, Module.finrank κ₂ ↥(level M) = Module.finrank κ ↥(M.1)
  /-- the correspondence matches fixing subgroups -/
  level_fixing : ∀ M, (level M).fixingSubgroup =
    (M.1.fixingSubgroup).map (Φ : Gal(K'/κ) →* Gal(L'/κ₂))

/-- **Neukirch's Kennzeichnung in field-theoretic form**: the lattice of finite extensions of a
`p`-adic field determines the field.  Stated for fields presented as completions of number fields
and finite extensions of such, with the correspondence of finite extensions supplied as data
(`NK.LocalStructure.FiniteExtensionCorrespondence`).

This is the second of the two named inputs to which item 6 is reduced; the classical proof recovers
from the lattice (i) the ramification filtration of the wild inertia and (ii) the field itself from
the residue data together with that filtration.  Formalising (i) requires the ramification theory of
complete discretely valued fields, which is not available in this workspace; it is therefore
recorded here as a named input rather than derived. -/
def LocalFieldFromFiniteExtensionLattice : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (N : IntermediateField (𝔮.adicCompletion L) L') [FiniteDimensional (𝔮.adicCompletion L) ↥N]
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    (Φ : Gal(L'/↥N) ≃* Gal(K'/𝔭.adicCompletion K)),
    FiniteExtensionCorrespondence Φ → Nonempty (↥N ≃+* 𝔭.adicCompletion K)

/-! ## The bundle -/

/-- **The reduced input catalogue of the local structure theory.**  All six items at a single
`p`-adic field `κ = K_𝔭` with residue field of `q` elements, abstract degree `d` and `δ` the
indicator of `ζ_p ∈ κ`.  Everything the Neukirch–Uchida endgame consumes from the local theory is
derived from these in `Submission/Work/LocalStructure/`. -/
structure LocalStructureInputs (p q d δ : ℕ) (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] : Prop where
  tame : TameCore p K 𝔭 K'
  frobenius : TameFrobeniusCore p q (𝔭.adicCompletion K) K'
  principalUnits : PrincipalUnitsCore K 𝔭 p
  tower : TowerRankCore K 𝔭 K' p
  q_eq : ∃ f : ℕ, 0 < f ∧ q = p ^ f
  d_eq : d = NK.LocalInputs.localDegree K 𝔭
  δ_eq : δ = NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K)

end

end NK.LocalStructure

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.LocalDecomposition`: Neukirch's characterisation of decomposition groups

This chapter attacks the linchpin of the `(a)`-chain of the Neukirch–Uchida development:
**Neukirch's characterisation of decomposition groups**, i.e. the "if" direction of
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, (12.1.9), which is Theorem 1 of
J. Neukirch, *Kennzeichnung der `p`-adischen und der endlich algebraischen Zahlkörper*,
Invent. Math. **6** (1969).

The statement delivered is

`NK.BrauerHasse.LocalDecompositionCriterion p K K' κ κ'`:

for a number field `K` with separable closure `K'`, a `p`-adic field `κ` with separable closure
`κ'`, a closed subgroup `H ≤ Gal(K'/K)` with `Subgroup.normalizer H = H` and an isomorphism
`H ≃* Gal(κ'/κ)`, a place `A` of `K'` over a finite prime of `K` and a class
`x : H²(H, Z/p)` whose localisation at `A` is non-zero, there is a place `A'` of `K'` over a
finite prime of `K` with `MulAction.stabilizer Gal(K'/K) A' = H`.

The chapter's content is a *reduction* of that statement to four named classical inputs, with all
the intermediate steps proved (see `Submission/Work/LocalDecomposition/README.md` for the full
account).  This file fixes the vocabulary: the four inputs

* `NK.LocalDecomposition.IndecomposedPrime` — the localisation ("the prime is indecomposed")
  step, CoNF (9.2.1) + (12.1.9), the rank count of Neukirch's argument;
* `NK.LocalDecomposition.IndexOneOfSelfNormalizing` — the maximality of decomposition groups
  among closed subgroups isomorphic to absolute Galois groups of `p`-adic fields
  (Neukirch, Invent. Math. **6** (1969) Theorem 1; CoNF (12.1.9)–(12.1.10));
* `NK.LocalDecomposition.LocalGaloisInfinite` — the absolute Galois group of a `p`-adic field
  is infinite;
* `NK.LocalDecomposition.LocalInjectionFiniteIndex` — Neukirch's Korollar 1 in local form
  (CoNF (12.1.9) end, Neukirch, Invent. Math. **6** (1969) Korollar 1);

together with the derived (proved) statements in `Basic.lean` and `Reduction.lean`.

## Coefficient warning

`NK.BrauerHasse.Coeff p` is the *trivial* `Z/p`-module, whereas the classical coefficient
module is `μ_p = Z/p(1)`; the two coincide for `p = 2` (where `μ_2 = Z/2` for every field of
characteristic `≠ 2`).  The reduction below is coefficient-agnostic: it uses the cohomology
classes and the localisation map only through the two statements `IndecomposedPrime` and
`IndexOneOfSelfNormalizing`, so specialising to `p = 2` (see `Main.lean`) gives the criterion at a
prime where the two coefficient modules agree.

## Hypothesis warning

The criterion is *false* for a non-`p`-adic `κ`: for `K = ℚ`, `H = ⊤ ≅ Gal(ℚ̄/ℚ)`, the
localisation of the Brauer group of `ℚ` into the product of the local Brauer groups is injective
with infinite `p`-torsion, so the hypothesis of the criterion is met at `κ = ℚ`, `κ' = ℚ̄`, while
`⊤` is not the decomposition group of any place over a finite prime of `ℚ` (those are isomorphic
to `Gal(ℚ̄_ℓ/ℚ_ℓ)`, not to `Gal(ℚ̄/ℚ)`).  Consequently each of the four inputs above is to be read
with `κ` a `p`-adic field — which is the setting in which the development consumes the criterion
(`κ = 𝔭.adicCompletion K₁` for a finite prime `𝔭` of `K₁`, see
`NK.Mine.preservesDecompositionGroups_of_localData_two`).  The four inputs are classical
theorems *for `p`-adic* `κ`, and the main theorem of this chapter is an implication, hence valid
in either case.
-/
import Submission.NK.BrauerHasse.All
import Submission.NK.LocalStructure.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false


open scoped Classical Pointwise
open IsDedekindDomain.HeightOneSpectrum

universe u

namespace NK.LocalDecomposition

noncomputable section

open NK.BrauerHasse

/-! ## The reduction inputs -/

/-- **The indecomposed-prime step** of Neukirch's Theorem 1.

A non-zero local component of a class `x : H²(H, Z/p)` at a place `A` of `K'` over a finite prime
of `K` forces `H` to contain an *open* subgroup `H₀` which lies in the decomposition group of some
place `A'` of `K'` over a finite prime of `K`, with `H₀` of finite index in that decomposition
group.

Classically this is the "the prime is indecomposed" argument of Neukirch (Invent. Math. **6**
(1969), Theorem 1; CoNF (12.1.9) and (9.2.1); A. Ivanov, arXiv:1309.2801, proof of
Proposition `classobstrdec`, equations `eq:NeukirchH2modified` and `eq:NeukirchH2modifiedsurj`):
the localisation maps `H²(H', μ_p) → ⊕_{𝔭' | 𝔭} H²(D_{𝔭'}, μ_p)` are surjective for every open
`H' ≤ H` (global class field theory, the vanishing of the limiting `Sha²`), while the source has
`p`-rank one and each summand is non-zero (local class field theory, `Br(κ)[p] ≅ Z/p`); counting
ranks, there is exactly one prime over `𝔭` in every finite extension of the fixed field of `H₀`,
i.e. `H₀ = D_{𝔭} ∩ H` for suitable `H₀`.

Note that the output is an *open subgroup* of `H` inside a decomposition group — the passage from
`H₀` to `H` itself is the FKS normalizer argument, which is **proved** in this chapter
(`NK.LocalDecomposition.le_stabSubgroup_of_openSubgroup_le`) from the disjointness of the
decomposition groups of distinct places (CoNF (12.1.3)) together with
`NK.LocalDecomposition.LocalGaloisInfinite`. -/
def IndecomposedPrime (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
    Nonempty (H ≃* Gal(κ'/κ)) →
    ∀ (A : OverFinitePrime K K') (x : H2Profinite p H),
      H2Profinite.loc p H x A ≠ 0 →
      ∃ (H₀ : Subgroup Gal(K'/K)) (A' : ValuationSubring K'),
        H₀ ≤ H ∧ 0 < H₀.relIndex H ∧ A'.comap (algebraMap K K') ≠ ⊤ ∧
          H₀ ≤ MulAction.stabilizer Gal(K'/K) A'

/-- **The indecomposed-prime step, with the presentation of the open subgroup.**

The same statement as `IndecomposedPrime`, with the additional recording that the open subgroup `H₀`
is *presented* as the absolute Galois group of a finite extension `κ₀` of `κ` inside `κ'` — which is
automatic classically: an open subgroup of `Gal(κ'/κ)` is the fixing subgroup of a finite extension
`κ₀/κ`, so `H₀ ≅ Gal(κ'/κ₀)`.  This is the form of Neukirch's localisation output that can be fed
to the local form `LocalInjectionFiniteIndexSubgroup` of Neukirch's Korollar 1, and hence is the form
in which the *finiteness of the relative index* of `H₀` in `D_{A'}` is *proved* rather than assumed
(see `Submission/Work/LocalDecomposition/Local/Korollar1Global.lean`). -/
def IndecomposedPrimePresented (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
    Nonempty (H ≃* Gal(κ'/κ)) →
    ∀ (A : OverFinitePrime K K') (x : H2Profinite p H),
      H2Profinite.loc p H x A ≠ 0 →
      ∃ (κ₀ : IntermediateField κ κ') (H₀ : Subgroup Gal(K'/K)) (A' : ValuationSubring K'),
        H₀ ≤ H ∧ 0 < H₀.relIndex H ∧ Nonempty (H₀ ≃* Gal(κ'/↥κ₀)) ∧
          A'.comap (algebraMap K K') ≠ ⊤ ∧ H₀ ≤ MulAction.stabilizer Gal(K'/K) A'

/-- **Neukirch's Korollar 1**, in the *global* form used by the criterion (CoNF (12.1.9), end of
the proof; A. Ivanov, arXiv:1309.2801, Lemma `lm:locfinindex`; Invent. Math. **6** (1969),
Korollar 1).

Let `H₀ ≤ H ≤ Gal(K'/K)` with `H₀` of finite relative index in `H`, let `H` be isomorphic to the
absolute Galois group `Gal(κ'/κ)` of a `p`-adic field `κ`, and let `H₀` be contained in the
decomposition group `D_A` of a place `A` over a finite prime.  Then `H₀` has *finite relative index*
in `D_A`.

Classically (Neukirch's Korollar 1) this is the statement that an injection of absolute Galois
groups of `p`-adic fields `Gal_L ⊆ Gal_M` has finite index: here `H₀` is open in `H ≅ Gal(κ'/κ)`,
hence `H₀` is the absolute Galois group of a finite extension of `κ` (Galois correspondence), and
passing to the local field of the place `A` (via `D_A ≅ Gal(K_𝔭̄/K_𝔭)`) the injection
`H₀ ↪ D_A` is an injection of absolute Galois groups of `p`-adic fields.

What would discharge it: the local form `LocalInjectionFiniteIndex` together with the
global–local comparison of fixing subgroups at the place `A` (the cofinality statement that every
finite extension of `K_𝔭` is the completion of a finite extension of `K` inside `K'`, available in
the commons as `exists_algEquiv_adicCompletion_of_finiteDimensional`). -/
def InjectionFiniteIndex (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (H H₀ : Subgroup Gal(K'/K)) (A : ValuationSubring K'),
    H₀ ≤ H → 0 < H₀.relIndex H → Nonempty (H ≃* Gal(κ'/κ)) →
    A.comap (algebraMap K K') ≠ ⊤ → H₀ ≤ MulAction.stabilizer Gal(K'/K) A →
      0 < H₀.relIndex (MulAction.stabilizer Gal(K'/K) A)

/-- **The maximality of decomposition groups** among closed subgroups isomorphic to absolute
Galois groups of `p`-adic fields.

Let `H ≤ Gal(K'/K)` be closed, self-normalising, isomorphic to `Gal(κ'/κ)` for a `p`-adic field
`κ`, and suppose `H` is contained in the decomposition group of a place `A` of `K'` over a finite
prime of `K`, with finite relative index.  Then `H` *is* that decomposition group.

This is the "indecomposed case" of Neukirch's Theorem 1 (Invent. Math. **6** (1969); CoNF
(12.1.9)–(12.1.10)): a decomposition group is maximal among the closed subgroups of `Gal(K'/K)`
isomorphic to absolute Galois groups of `p`-adic fields (A. Ivanov, arXiv:1309.2801, the Corollary
following Proposition `cycloDecChar`; the uniqueness statement for the prime is Ivanov,
Corollary 2.7(ii)).  Its classical proof consumes the local reconstruction (Neukirch's Korollar 1,
`NK.LocalDecomposition.LocalInjectionFiniteIndex`, together with the local Neukirch–Uchida
theorem) — see `Submission/Work/LocalDecomposition/Local/`.

Equivalently — and this is the content of `NK.LocalDecomposition.localFinishingStep_iff` — it is
`NK.LocalStructure.LocalFinishingStep`, given the disjointness of the decomposition groups of
distinct places (which is proved in this chapter). -/
def IndexOneOfSelfNormalizing (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) → Subgroup.normalizer H = H →
    Nonempty (H ≃* Gal(κ'/κ)) →
    ∀ (A : ValuationSubring K'), A.comap (algebraMap K K') ≠ ⊤ →
      H ≤ MulAction.stabilizer Gal(K'/K) A →
        0 < H.relIndex (MulAction.stabilizer Gal(K'/K) A) →
      MulAction.stabilizer Gal(K'/K) A = H

/-- **Neukirch's Korollar 1 in the local form used to derive the finiteness of the index.**

Let `L` be a `p`-adic field (presented as a completion `𝔮.adicCompletion L` of a number field at a
finite prime), `L'` a separable closure, and `H ≤ Gal(L'/L)` an *arbitrary* subgroup which is
isomorphic to the absolute Galois group of a *finite extension* `κ₀` of a `p`-adic field `κ`
(realised inside a separable closure `κ'` of `κ`).  Then `H` has finite index in `Gal(L'/L)`.

This is the statement quoted by A. Ivanov (arXiv:1309.2801, Lemma `lm:locfinindex`, attributed to
Neukirch, Invent. Math. **6** (1969), Korollar 1, and proved at the end of the proof of CoNF
(12.1.9)): *an injection `Gal_L ⊆ Gal_M` of absolute Galois groups of local fields, with `L`
`p`-adic, forces `M` to be `p`-adic and `Gal_L` to have finite index in `Gal_M`*.  It carries **no**
closedness hypothesis on `H` (whence its usefulness: the isomorphism `D_A ≅ Gal(L'/L)` on disk is
only an abstract `MulEquiv`, so closedness cannot be transported along it).

The parameter `κ₀` is the field of the *open subgroup* of the reduction (an open subgroup of
`Gal(κ'/κ)` is the absolute Galois group of a finite extension `κ₀/κ`), so this form is the one
applicable to the output of `NK.LocalDecomposition.IndecomposedPrime`; see
`Submission/Work/LocalDecomposition/Local/Korollar1Global.lean`. -/
def LocalInjectionFiniteIndexSubgroup (κ κ' : Type u) [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (κ₀ : IntermediateField κ κ')
    (L : Type u) [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (H : Subgroup Gal(L'/𝔮.adicCompletion L)),
    Nonempty (H ≃* Gal(κ'/↥κ₀)) → 0 < H.relIndex ⊤

/-- **The absolute Galois group of a `p`-adic field is infinite.**

This is the only quantitative statement about `κ` used by the reduction (it is what makes an open
subgroup of `H` non-trivial).  Classically: a `p`-adic field has unramified extensions of every
degree, so `Gal(κ̄/κ)` surjects onto `Ẑ`; it also follows from
`NK.LocalTame.TameStructureInput`/`NK.LocalInputs.LocalGaloisInputs`
(`NK.LocalAnabelian.HasUnboundedTowerRank p (Gal(κ̄/κ))`, which implies infinitude). -/
def LocalGaloisInfinite (κ κ' : Type u) [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  Infinite (Gal(κ'/κ))

/-- **Neukirch's Korollar 1 in local form** (CoNF (12.1.9); Invent. Math. **6** (1969), Korollar 1;
A. Ivanov, arXiv:1309.2801, Lemma `lm:locfinindex`).

Let `N` be an intermediate field of a separable closure `L'` of a `p`-adic field `L`, and suppose
the absolute Galois group `Gal(L'/N)` of `N` is isomorphic to the absolute Galois group of a
`p`-adic field.  Then `N` is a *finite* extension of `L`.  (Classically one also gets that `N` is
itself `p`-adic and, with the local Neukirch–Uchida theorem, that `N ≅ κ` — see
`NK.LocalDecomposition.localInjection_ringEquiv`.) -/
def LocalInjectionFiniteIndex (κ κ' : Type u) [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (L : Type u) [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (N : IntermediateField (𝔮.adicCompletion L) L'),
    Nonempty (Gal(L'/↥N) ≃* Gal(κ'/κ)) → FiniteDimensional (𝔮.adicCompletion L) ↥N

end

end NK.LocalDecomposition

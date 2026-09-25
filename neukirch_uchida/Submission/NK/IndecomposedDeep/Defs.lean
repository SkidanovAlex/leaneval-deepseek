/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Submission/Work/IndecomposedDeep/` — the classical input catalogue of block (i)

**Namespace** `NK.IndecomposedDeep`.
**Import everything with** `import Submission.NK.IndecomposedDeep.All`.

The sibling chapter `Submission/Work/Indecomposed/` assembles Neukirch's local characterisation of
decomposition groups from two structures,

```
NK.Indecomposed.RankData          p K K' κ κ'
NK.Indecomposed.LocalReconstruction p K K' κ κ'
```

This chapter *instantiates* those two structures.  Its content is to decompose each of their fields
as far as the mathematics honestly allows, to name the residual classical inputs, to prove every
step in between, and to compose the result with the endgame of the Neukirch–Uchida development.

## The catalogue

Write `κ = 𝔭.adicCompletion K₁` for the local field at a finite prime, `κ'` for its separable
closure, `K = K₂`, `K' = K₂'` for the number field and separable closure *on the other side* of the
homeomorphism (this is the orientation in which
`NK.Indecomposed.preservesDecompositionGroups_of_hasseAt` consumes the data).

| input | content | reference / owner |
|---|---|---|
| `NK.BrauerTwist.LocalFieldBrauerCyclic p κ κ'` | `H²(G_κ, μ_p) ≅ ℤ/p` | Kummer sequence + `Br(κ)[p] ≅ ℤ/p` (NSW (7.1.7), (7.2.6)); on disk, reduced by `Submission/Work/LocalCFT/Brauer/` |
| `NK.IndecomposedDeep.GlobalBrauerTransport p K K' κ κ'` | the *labelling transport*: a closed `U ≤ G_K` isomorphic to `G_κ` has the same twisted cohomology as `G_κ` | NSW (7.1.7)–(7.1.8) + the cyclotomic compatibility of the labelling (Neukirch's Theorem 1); **not** formalised anywhere in the workspace — see `README.md` §3 |
| `NK.IndecomposedDeep.LocalGroupBrauer p K K' κ κ'` | `p ≤ |H²(H ⊓ D_A, μ_p)|` for the non-trivial local groups | NSW (7.1.8)(i),(ii); see `README.md` §3 |
| `NK.HasseTwist.NeukirchH2modifiedsurj p K K' κ κ'` | Neukirch's modified surjectivity (NSW (9.2.1)) | the name used by `Submission/Work/HasseTwist/`; global class field theory (Poitou–Tate / the idèle class group) |
| `NK.IndecomposedDeep.LocalSubgroupClosed κ κ'` | a subgroup of the absolute Galois group of a `p`-adic field isomorphic to a `p`-adic absolute Galois group is closed | Serre (`p`-adic analytic pro-`p` groups); see `README.md` §5 |
| `NK.LocalDecomposition.LocalInjectionFiniteIndex κ κ'` | Neukirch's Korollar 1, finiteness form (Ivanov, `lm:locfinindex`) | on disk; **used to prove** `NK.Indecomposed.LocalKorollar1` |
| `NK.LocalDecomposition.IndexOneOfSelfNormalizing p K K' κ κ'` | Neukirch's Theorem 1, maximality of decomposition groups | on disk; **used to prove** `NK.Indecomposed.LocalReconstruction.finishingStep` |

The two structures themselves are *proved* from this catalogue in `RankData.lean` /
`Reconstruction.lean`; `Endgame.lean` composes them into
`Submission.NeukirchUchida.PreservesDecompositionGroups ϕ` and into the per-prime form consumed by
`NK.Mine.neukirch_uchida_of_localStructureData_residuals`.
-/

import Submission.NK.Indecomposed.All
import Submission.NK.LocalDecomposition.Local.Korollar1Global

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open IsDedekindDomain.HeightOneSpectrum

universe u

namespace NK.IndecomposedDeep

open NK.BrauerTwist NK.HasseTwist

variable {p : ℕ} {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-! ## (A) The `μ_p`-twisted local Brauer computations -/

/-- **The labelling transport for the twisted local Brauer computation.**

Let `U ≤ Gal(K'/K)` be closed and isomorphic to `Gal(κ'/κ)` for a `p`-adic field `κ`.  Then the
twisted cohomology `H²(U, μ_p)` — computed with the cyclotomic coefficient module `μ_p ⊆ K'` and the
level system of `K'/K` (`NK.BrauerTwist.H2Twist`) — is in bijection with `H²(G_κ, μ_p)`.

Classically this is the "labelling" step of Neukirch's proof: the isomorphism `U ≅ Gal(κ'/κ)`
matches the two level systems (the Galois correspondence on both sides, as in
`Submission/Work/LocalCFT/Brauer/Transport.lean` for the trivial coefficients), and it is compatible
with the coefficient modules because an isomorphism of absolute Galois groups of `p`-adic fields
carries the cyclotomic character to the cyclotomic character (Neukirch, Invent. Math. **6** (1969),
Theorem 1; NSW (12.1.4)–(12.1.6)); the two combine into `H²(U, μ_p) ≅ H²(G_κ, μ_p) ≅ ℤ/p`
(NSW (7.1.7)).

The transport is not formalised in this workspace for the twisted coefficients (only the
trivial-coefficient analogue, `NK.LocalCFT.Brauer.exists_ne_zero_H2Profinite_of_mulEquiv`, is);
it is therefore recorded here as a named classical input.  It is *satisfiable*: at
`K = ℚ`, `p = 2`, `κ = ℚ_2` and `U = D_2` (the decomposition group at 2), both sides are
`Br(ℚ_2)[2] ≅ ℤ/2`.  See `README.md` §3 and `Audit.lean`. -/
structure GlobalBrauerTransport (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- the twisted cohomology of a labelled closed subgroup is that of its labelling -/
  equiv : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (U ≃* Gal(κ'/κ)) →
      Nonempty (H2Twist p U ≃ H2Twist (K := κ) (K' := κ') p ⊤)

/-- **The `μ_p`-twisted Brauer computation at the non-trivial local groups.**

For every closed `H ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)`, every finite prime `𝔭` of `K` and every
*non-trivial* local group `V = H ⊓ D_A` at a place over `𝔭`, the twisted cohomology `H²(V, μ_p)` has
at least `p` elements.

Classically: a non-trivial local group of a labelled `H` is the decomposition group of a place of
the fixed field of `H`, i.e. the absolute Galois group of the corresponding `p`-adic field, and
`H²(G_λ, μ_p) ≅ ℤ/p` (NSW (7.1.8)(i),(ii), used by Ivanov, arXiv:1309.2801, in the proof of
`classobstrdec`).  The restriction `V ≠ ⊥` is necessary and correct: at `V = ⊥` the twisted
cohomology is a point (`NK.Indecomposed.subsingleton_h2Twist_bot`) and `⊥` occurs as a local
group exactly when the prime is decomposed in `K'/K`
(`NK.Indecomposed.not_forall_card_local_of_bot_mem`); imposing the hypothesis there would be
unsatisfiable.  See `README.md` §3. -/
structure LocalGroupBrauer (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- the cardinality bound at the non-trivial local groups -/
  card_local : ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) →
    Nonempty (H ≃* Gal(κ'/κ)) →
    ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ∀ V ∈ localGroupSubgroupsOver (K := K) (K' := K') H 𝔭,
        V ≠ ⊥ → p ≤ Nat.card (H2Twist p V)

/-! ## (C) Neukirch's local reconstruction -/

/-- **Closedness of subgroups of a `p`-adic absolute Galois group.**

Every subgroup of the absolute Galois group `Gal(L'/L_𝔮)` of a `p`-adic field which is isomorphic
(as an abstract group) to the absolute Galois group `Gal(κ'/κ)` of a `p`-adic field is *closed*.

Classically: `G_κ` is a `p`-adic analytic pro-`p` group (Serre, *Lie algebras and `p`-adic analytic
groups*, §II.3, and NSW (7.5.11)), and a subgroup of a `p`-adic analytic group which is isomorphic
to a `p`-adic analytic group is closed (Serre, *Galois Cohomology*, I §1.4; the argument is that an
abstract isomorphism with a `p`-adic analytic group makes the subgroup an analytic subgroup, and
analytic subgroups are closed).  The input is needed to reduce the requester's form of Neukirch's
Korollar 1 (arbitrary subgroups, as in `NK.Indecomposed.LocalKorollar1`) to the classical form for
*closed* subgroups (`NK.LocalDecomposition.LocalInjectionFiniteIndex`, Ivanov's `lm:locfinindex`
— "an injection `Gal_L ⊆ Gal_M` of absolute Galois groups of local fields" is an injection of
*closed* subgroups, since `Gal_L`, `Gal_M` are absolute Galois groups of fields).

See `README.md` §5 for the audit of this input (in particular for the classical *counterexample* to
the analogous statement for `ℤ_p`, which is why it is recorded as an input rather than derived). -/
def LocalSubgroupClosed (κ κ' : Type u) [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop :=
  ∀ (L : Type u) [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (H : Subgroup Gal(L'/𝔮.adicCompletion L)),
    Nonempty (H ≃* Gal(κ'/κ)) → IsClosed (H : Set Gal(L'/𝔮.adicCompletion L))

end NK.IndecomposedDeep

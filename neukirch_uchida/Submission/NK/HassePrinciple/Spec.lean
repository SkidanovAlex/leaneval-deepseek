/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The (corrected) specification of the Hasse principle, and its inputs

Umbrella development: `Submission/Work/HassePrinciple/` (README §13, §14, §22).

The requested target `NK.BrauerHasse.Sha2Vanishing p K K' κ κ'` is **false as a universally
quantified statement** (its hypotheses do not require `κ` to be `p`-adic): with
`K = κ = ℚ(√2)`, `p = 2`, the quaternion class `(-1,-1)` is non-zero in `H²(Gal(K'/K), Z/2)`
while all its localisations at places *over finite primes* vanish (its only non-trivial invariants
are at the two real places, and `OverFinitePrime` contains no archimedean place).  See README
§13.1 and `NK.HassePrinciple.ArchimedeanDefect`.

This module records the corrected statement and the input it consumes.  There are two *routes*,
both proved here, with different inputs:

* `NK.HassePrinciple.RankInput` (in `RankInput.lean`) — **Neukirch's input**: the *surjectivity*
  of the localisation at a place (Neukirch, Invent. Math. **6** (1969), Theorem 1; NSW (9.2.1))
  together with the local computations of local class field theory
  (`H²(G_κ, Z/p) ≅ Z/p` or `0`).  The reduction is `NK.HassePrinciple.sha2Vanishing_of_rankInput`,
  which does *not* assume the Hasse principle in any form.  This is the operative input of
  `NK.HassePrinciple.Sha2Spec` below.
* `NK.HassePrinciple.LimitPassage` — the **Hasse principle in the limit** (Ivanov,
  arXiv:1309.2801, Thm 2.14; Neukirch, Invent. Math. **6** (1969), Thm 1): the level-wise
  local *injectivity* statement, i.e. the Hasse principle itself, in the κ-labelled form.  The
  reduction is `NK.HassePrinciple.sha2Vanishing_of_limitPassage`.  It is recorded because it is
  the exact form of the classical theorem, but it is *not* the interface the chapter uses: it
  assumes what the chapter is supposed to supply.

## `NK.HassePrinciple.Sha2Spec`: which field is operative, and why there is no `cyclic` field

`Sha2Spec` has exactly two fields and both are used:

* `Sha2Spec.rank : RankInput` — **the operative field**: `sha2Vanishing_of_spec` is literally
  `sha2Vanishing_of_rankInput h.rank`, and `Sha2Spec.hp` is read off from it (`RankInput.hp`).
* `Sha2Spec.archimedean : NoTwoTorsion Gal(κ'/κ)` — the condition under which the *literal* target
  is non-vacuous: it is extracted at the level of the labelled subgroup by
  `Sha2Spec.noTwoTorsion` (`NoTwoTorsion ↥U` for `U ≅ Gal(κ'/κ)`, the form consumed by
  `Literal`/`LimitPassage`), and it is what rules out the archimedean defect
  (`NK.HassePrinciple.not_archimedeanDefect_of_sha2Vanishing`, README §19).  It is *not* needed
  for the implication `RankInput → Sha2Vanishing` — an implication does not need the hypotheses
  that make its conclusion true — and this is stated here explicitly rather than hidden by an
  unused field.

**There is deliberately no `cyclic : CyclicHasseInput` field.**  A field that no proof consumes is
worse than no field: it suggests that the licensed cyclic input (the Hasse norm theorem for cyclic
extensions together with the Herbrand quotient, `NK.HassePrinciple.CyclicHasseInput`) is part of
the reduction, which is *false* and *proved* false:

* `NK.HassePrinciple.le_stabSubgroup_iff_localInclHom_surjective`;
* `NK.HassePrinciple.iInf_sup_fixingSubgroup_eq_stabSubgroup` (`⋂_L D_A·Gal(K'/L) = D_A`);
* `NK.HassePrinciple.sha2Vanishing_iff_localCharacterisation` (the target is equivalent to
  Neukirch's local characterisation of the decomposition groups).

The licensed cyclic input is consumed by the chapter where it *does* have content:
`NK.HassePrinciple.hbnUnits_from_cyclicInput` (the relative Hasse–Brauer–Noether theorem for
every finite Galois extension of number fields) and
`NK.HassePrinciple.fieldAxiom_of_hasseNormTheorem` (the field axiom of the on-disk global class
field theory).  It is available to a caller as `NK.HassePrinciple.CyclicHasseInput`; a caller who
wants it next to the reduction should use `NK.HassePrinciple.Sha2Spec` together with
`NK.HassePrinciple.hbnUnits_from_cyclicInput`, not a decorative field.  See README §22 and §16.4.
-/

import Mathlib
import Submission.NK.HassePrinciple.Defs
import Submission.NK.HassePrinciple.RankInput
import Submission.NK.HassePrinciple.ArchimedeanDefect
import Submission.NK.HassePrinciple.LocalCharacterisation
import Submission.NK.BrauerHasse.Main

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

noncomputable section

namespace NK.HassePrinciple

open NK.BrauerHasse
open scoped Pointwise

/-- **The archimedean condition**: the subgroup `U ≤ Gal(K'/K)` contains no element of order `2`,
equivalently (Artin–Schreier) the fixed field `K'^U` has no real place.  This is the condition that
Hasse–Brauer–Noether needs in order to be a statement about the *finite* places, and it is supplied
by the labelling `U ≅ Gal(κ'/κ)` whenever `κ` is not formally real — in particular for every
`p`-adic `κ`. -/
def NoTwoTorsion (G : Type*) [Group G] : Prop :=
  ∀ σ : G, σ ≠ 1 → σ * σ ≠ 1

/-- The archimedean condition is preserved by (and transported along) group isomorphisms. -/
theorem noTwoTorsion_of_mulEquiv {G H : Type*} [Group G] [Group H] (h : NoTwoTorsion G)
    (e : G ≃* H) : NoTwoTorsion H := by
  intro σ hσ hσ2
  have h1 : e.symm σ * e.symm σ = 1 := by
    rw [← map_mul, hσ2, map_one]
  have hτ : e.symm σ ≠ 1 := by
    intro hx
    exact hσ (by rw [← MulEquiv.apply_symm_apply e σ, hx, map_one])
  exact h (e.symm σ) hτ h1

/-- **The limit passage: the Hasse principle for `H²(·, Z/p)` over the field `K'^U`, in the
κ-labelled form.**

For a closed `U ≤ Gal(K'/K)` with `Nonempty (U ≃* Gal(κ'/κ))` whose fixed field has no real place
(`NoTwoTorsion ↥U`), a level class whose fine localisation `locLevel` vanishes at every place of
`K'` over a finite prime of `K` is zero in the colimit `H2Profinite p U`.

This is the classical theorem Neukirch, Invent. Math. **6** (1969), Theorem 1 ≡ Ivanov,
arXiv:1309.2801, Theorem 2.14 — the Hasse principle in the limit — in the form in which the
chapter consumes it.  **The κ-labelling is not cosmetic**: without it the statement is false.
Indeed, for `K = ℚ` and `p = 3`, the subgroup `U = Gal(ℚ̄/ℚ(ζ_{3^∞}))` has `NoTwoTorsion ↥U`
(the field `ℚ(ζ_{3^∞})` is totally imaginary) but `Ш²(K'^U, Z/3) ≠ 0`: by Poitou–Tate duality for
the cyclotomic `Z_3`-extension, `Ш²(Z/3) ≅ Ш¹(μ_3)^*`, the `3`-Selmer group of `ℚ(ζ_{3^∞})`, and
`Cl(ℚ(ζ_{3^n}))[3] ≠ 0` for `n ≥ 2` (Iwasawa: `h(ℚ(ζ_9)) = 3`, `λ`-invariant `≠ 0`), so the
kernel of the localisation is non-trivial.  The labelling `U ≅ Gal(κ'/κ)` with `κ` `p`-adic
excludes this: it makes `U` a *local* group, and Neukirch's theorem is precisely the statement that
such subgroups are decomposition groups, where the Hasse principle holds.

The statement is *not* derivable from the finite-level Hasse–Brauer–Noether theorem
`NK.HassePrinciple.HBNUnits` (Milne VII.7.1, proved in this chapter): see README §13.7(iv).  In
the limit the fine local group `U ⊓ D_A = G_{K'^U_v}` is the *decomposition group of the infinite
extension*, whereas the finite-level localisation is at the coarser stabilisers, and
`[C_M(A) : F_M(A)] = [M ⊓ K'^U·F_A : M ⊓ F_A] > 1` in general.  This is why the chapter's primary
interface is `NK.HassePrinciple.RankInput` instead. -/
def LimitPassage (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ'] (p : ℕ) : Prop :=
  ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) → NoTwoTorsion ↥U →
    Nonempty (U ≃* Gal(κ'/κ)) →
    ∀ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L),
      levelLocVanishing p U L a → H2Profinite.ofLevel L a = 0

/-- **The Hasse principle from the limit passage.**  This is the reduction along the *injectivity*
route: the limit passage of `NK.HassePrinciple.LimitPassage` is the Hasse principle itself in
level formulation (`NK.HassePrinciple.sha2Vanishing_iff_levelForm`), so the Hasse principle
follows immediately. -/
theorem sha2Vanishing_of_limitPassage {K K' κ κ' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] (p : ℕ) (harch : NoTwoTorsion Gal(κ'/κ))
    (h : LimitPassage K K' κ κ' p) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' := by
  refine sha2Vanishing_of_levelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p ?_
  intro U hU hUκ L a ha
  exact h U hU (noTwoTorsion_of_mulEquiv harch hUκ.some.symm) hUκ L a ha

/-- **The corrected input structure of the Hasse principle.**  Its fields are:

1. `archimedean` — the archimedean condition on the labelling field `κ`:
   `NoTwoTorsion Gal(κ'/κ)`.  It holds for every `p`-adic `κ` (Artin–Schreier: a `p`-adic field is
   not formally real, so its absolute Galois group is torsion-free, a statement owed by
   `NK.LocalCFT`) and it is *necessary* for the truth of the target (README §13.1).  It is
   consumed by `NK.HassePrinciple.Sha2Spec.noTwoTorsion` (which extracts `NoTwoTorsion ↥U` at
   every labelled closed `U`, the form in which the condition enters
   `NK.HassePrinciple.LimitPassage` and the archimedean analysis of
   `NK.HassePrinciple.ArchimedeanDefect`) and by
   `NK.HassePrinciple.not_archimedeanDefect_of_sha2Vanishing`.
2. `rank` — **the operative field**: `NK.HassePrinciple.RankInput` (Neukirch's *surjectivity* at
   a place plus the local computations of local class field theory), from which the reduction
   `NK.HassePrinciple.sha2Vanishing_of_spec` is literally
   `NK.HassePrinciple.sha2Vanishing_of_rankInput h.rank`.  Its fields and their discharge
   recipes are documented in `RankInput.lean` and README §14.

The licensed cyclic input (`NK.HassePrinciple.CyclicHasseInput`) is deliberately **not** a field
of `Sha2Spec`; see the module docstring and README §22. -/
structure Sha2Spec (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- **The archimedean input**: the labelling field `κ` has no real place.  For a `p`-adic `κ`
  this holds (`κ` is not formally real, so `Gal(κ'/κ)` is torsion-free, by Artin–Schreier), and it
  is transported to `↥U` along the labelling by
  `NK.HassePrinciple.noTwoTorsion_of_mulEquiv`.  It is the weakest correct form of the
  archimedean hypothesis; for odd `p` it is unnecessary. -/
  archimedean : NoTwoTorsion Gal(κ'/κ)
  /-- **Neukirch's input** — the operative field: the rank count (see
  `NK.HassePrinciple.RankInput`). -/
  rank : RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p

namespace Sha2Spec

variable {p : ℕ} {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- The prime case, read off from the operative field `rank` (whose first field is `p.Prime`). -/
theorem hp (h : Sha2Spec p K K' κ κ') : p.Prime := h.rank.hp

/-- **The archimedean condition at the level of the labelled subgroup**: a closed `U ≤ Gal(K'/K)`
isomorphic to `Gal(κ'/κ)` has no element of order `2`.  This is the form in which the archimedean
field of `Sha2Spec` is consumed (e.g. by `NK.HassePrinciple.LimitPassage`, and in the statement
that no archimedean defect can exist). -/
theorem noTwoTorsion (h : Sha2Spec p K K' κ κ') {U : Subgroup Gal(K'/K)}
    (hκ : Nonempty (U ≃* Gal(κ'/κ))) : NoTwoTorsion ↥U :=
  noTwoTorsion_of_mulEquiv h.archimedean hκ.some.symm

/-- A `Sha2Spec` is determined by the archimedean condition together with Neukirch's input; this is
the constructor a caller uses. -/
theorem mk' (harch : NoTwoTorsion Gal(κ'/κ))
    (hrank : RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    Sha2Spec p K K' κ κ' := ⟨harch, hrank⟩

end Sha2Spec

variable {p : ℕ} {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The Hasse principle in the corrected form, from the corrected inputs.**  The operative field
is `Sha2Spec.rank` (`NK.HassePrinciple.RankInput`, Neukirch's surjectivity plus the local
computations): this is `NK.HassePrinciple.sha2Vanishing_of_rankInput` applied to it.  The
archimedean field is *not* used here — an implication `RankInput → Sha2Vanishing` needs no
hypothesis making its conclusion true — but it is consumed by
`NK.HassePrinciple.Sha2Spec.noTwoTorsion` and by
`NK.HassePrinciple.not_archimedeanDefect_of_sha2Vanishing`; see the module docstring. -/
theorem sha2Vanishing_of_spec (h : Sha2Spec p K K' κ κ') :
    Sha2Vanishing (K := K) (K' := K') p κ κ' :=
  sha2Vanishing_of_rankInput h.rank

/-- **The rank-count route also yields the classical limit form.**  Neukirch's input
(`NK.HassePrinciple.RankInput`) implies the κ-labelled Hasse principle in the limit
(`NK.HassePrinciple.LimitPassage`): this is the coherence of the two interfaces of the chapter —
the *surjectivity* route and the *injectivity* route reach the same conclusion. -/
theorem limitPassage_of_rankInput (h : RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    LimitPassage (K := K) (K' := K') κ κ' p :=
  fun U hU _ hκ L a ha =>
    levelForm_of_sha2Vanishing (K := K) (K' := K') (κ := κ) (κ' := κ') p
      (sha2Vanishing_of_rankInput h) U hU hκ L a ha

/-- **The corollary in the vocabulary of the Neukirch–Uchida development**: under the corrected
inputs, every non-zero class of `H²(H, Z/p)` has a non-zero local component at some place of `K'`
over a finite prime of `K`.  This is `NK.BrauerHasse.exists_loc_ne_zero` fed with
`NK.HassePrinciple.sha2Vanishing_of_spec`. -/
theorem exists_loc_ne_zero_of_spec (h : Sha2Spec p K K' κ κ') (H : Subgroup Gal(K'/K))
    (hH : IsClosed (H : Set Gal(K'/K))) (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  NK.BrauerHasse.exists_loc_ne_zero p (sha2Vanishing_of_spec h) H hH hκ hx

/-- **The consumer-facing corollary in the sharpest form**: from Neukirch's input
`NK.HassePrinciple.RankInput` (the chapter's obligation) together with the local Brauer input
`NK.BrauerHasse.LocalH2Input`, every non-zero class of `H²(H, Z/p)` (`H ≤ Gal(K'/K)` closed and
isomorphic to `Gal(κ'/κ)`) has a non-zero local component at some place of `K'` over a finite prime
of `K`.

The local input appears because that is the vocabulary of the consumer
(`NK.BrauerHasse.Main`); it is not used by the argument.  The `LocalH2Input`-first argument order
is the one a caller in the Neukirch–Uchida development expects; the same theorem with the chapter
input first is `NK.HassePrinciple.exists_loc_ne_zero_of_rankInput_and_localH2Input`. -/
theorem exists_loc_ne_zero_of_localH2Input_and_rankInput
    (hLoc : LocalH2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (h : RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p) (H : Subgroup Gal(K'/K))
    (hH : IsClosed (H : Set Gal(K'/K))) (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  NK.BrauerHasse.exists_loc_ne_zero p (sha2Vanishing_of_rankInput h) H hH hκ hx

/-- **The consumer-facing corollary with Neukirch's input written first** (the historical name kept
for the record; `NK.HassePrinciple.exists_loc_ne_zero_of_localH2Input_and_rankInput` is the same
statement in the argument order the consumer's code uses). -/
theorem exists_loc_ne_zero_of_rankInput_and_localH2Input
    (h : RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (_hl : NK.BrauerHasse.LocalH2Input p K K' κ κ') (H : Subgroup Gal(K'/K))
    (hH : IsClosed (H : Set Gal(K'/K))) (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  NK.BrauerHasse.exists_loc_ne_zero p (sha2Vanishing_of_rankInput h) H hH hκ hx

/-- **The consumer-facing corollary in its bundled form**: from the corrected inputs
`NK.HassePrinciple.Sha2Spec` together with the local Brauer input
`NK.BrauerHasse.LocalH2Input`, every non-zero class of `H²(H, Z/p)` (`H ≤ Gal(K'/K)` closed and
isomorphic to `Gal(κ'/κ)`) has a non-zero local component at some place of `K'` over a finite prime
of `K`. -/
theorem exists_loc_ne_zero_of_localH2Input_and_spec (h : Sha2Spec p K K' κ κ')
    (_hl : NK.BrauerHasse.LocalH2Input p K K' κ κ') (H : Subgroup Gal(K'/K))
    (hH : IsClosed (H : Set Gal(K'/K))) (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    {x : H2Profinite p H} (hx : x ≠ 0) :
    ∃ A : OverFinitePrime K K', H2Profinite.loc p H x A ≠ 0 :=
  exists_loc_ne_zero_of_spec h H hH hκ hx

/-- **Neukirch's characterisation of decomposition groups**, with the Hasse-principle hypothesis
discharged by the rank-count route (i.e. from Neukirch's surjectivity input and local class field
theory, *without* assuming the Hasse principle): a closed, self-normalising subgroup
`H ≤ Gal(K'/K)` isomorphic to the absolute Galois group of a `p`-adic field is the decomposition
group of a place of `K'` over a finite prime of `K`.

This is the statement that the consumer's development (`NK.LocalDecomposition`) consumes, in the
vocabulary of the inputs of this chapter. -/
theorem exists_decompositionGroup_of_rankInput
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hN : Subgroup.normalizer H = H) (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    (hLoc : NK.BrauerHasse.LocalH2Input p K K' κ κ')
    (h : RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p)
    (hStep : NK.BrauerHasse.LocalDecompositionCriterion p K K' κ κ') :
    ∃ A : ValuationSubring K', A.comap (algebraMap K K') ≠ ⊤ ∧
      MulAction.stabilizer Gal(K'/K) A = H :=
  NK.BrauerHasse.exists_decompositionGroup_of_localGalois p h.hp H hH hN hκ hLoc
    (sha2Vanishing_of_rankInput h) hStep

/-- **The same, from the corrected bundled input `Sha2Spec`.**  The prime is read off from the
operative field (`NK.HassePrinciple.Sha2Spec.hp`, i.e. `RankInput.hp`), and the archimedean field
is available alongside it in the form `NK.HassePrinciple.Sha2Spec.noTwoTorsion`
(`NoTwoTorsion ↥U` for the labelled `U`) — which is the condition under which the criterion is the
statement the Neukirch–Uchida development uses, the fixed field `K'^U` then having no real place
(README §13.0, §19). -/
theorem exists_decompositionGroup_of_spec
    (h : Sha2Spec p K K' κ κ')
    (H : Subgroup Gal(K'/K)) (hH : IsClosed (H : Set Gal(K'/K)))
    (hN : Subgroup.normalizer H = H) (hκ : Nonempty (H ≃* Gal(κ'/κ)))
    (hLoc : NK.BrauerHasse.LocalH2Input p K K' κ κ')
    (hStep : NK.BrauerHasse.LocalDecompositionCriterion p K K' κ κ') :
    ∃ A : ValuationSubring K', A.comap (algebraMap K K') ≠ ⊤ ∧
      MulAction.stabilizer Gal(K'/K) A = H :=
  exists_decompositionGroup_of_rankInput (K := K) (K' := K') (κ := κ) (κ' := κ')
    H hH hN hκ hLoc h.rank hStep

end NK.HassePrinciple

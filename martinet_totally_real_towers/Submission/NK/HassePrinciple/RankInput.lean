/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Neukirch's input: the rank count, and the Hasse principle without the Hasse principle

Umbrella development: `Submission/Work/HassePrinciple/` (README §14).

The chapter's other route to the Hasse principle `NK.BrauerHasse.Sha2Vanishing` (the level-wise
strong form `NK.HassePrinciple.Sha2Input`, or the limit form `NK.HassePrinciple.LimitPassage`)
*assumes* the Hasse principle in some form.  This module implements the classical alternative —
Neukirch's argument — which assumes instead the **surjectivity** of the localisation at a place,
together with the two cardinality computations of local class field theory:

* `NK.HassePrinciple.locAt p U A` — the localisation at a single place, as a plain function
  `H²(U, Z/p) → H²(U ⊓ D_A, Z/p)` (the place-indexed component of `H2Profinite.loc`);
* `NK.HassePrinciple.PlacesOverPrime K K' 𝔭` — the places of `K'` over a fixed finite prime `𝔭`
  of `K`, with `PlacesOverPrime.toOverFinitePrime`;
* `NK.HassePrinciple.RankInput p K K' κ κ'` — **the input**: (i) `H²(U, Z/p)` is finite of order
  `≤ p` for every closed `U ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)` (local class field theory at
  `κ`: `H²(G_κ, Z/p) ≅ Z/p` or `0`), and (ii) for every such `U` there is a place `A` at which the
  localisation is *surjective* and the local group is at least as large as the global one
  (`Nat.card (H²(U, Z/p)) ≤ Nat.card (H²(U ⊓ D_A, Z/p))`);
* `NK.HassePrinciple.sha2Vanishing_of_rankInput` — **the Hasse principle**
  `NK.BrauerHasse.Sha2Vanishing p K K' κ κ'` from that input.

## Why this is the right input

The two bullets of (ii) are exactly the two halves of Neukirch's argument, with the coefficient
module `Z/p` (so that the local groups enter through local Tate duality rather than through the
Brauer group), and *neither* is the Hasse principle: surjectivity of a localisation is the
`eq:NeukirchH2modifiedsurj` of Neukirch's proof (Neukirch, *Kennzeichnung der p-adischen und der
endlich algebraischen Zahlkörper*, Invent. Math. 6 (1969), Theorem 1; Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, (9.2.1); quoted in this workspace as
`NK.HasseTwist.NeukirchH2modifiedsurj`), and the cardinality statements are the local
computations `H²(G_κ, Z/p) ≅ Z/p` (local Tate duality, NSW (7.1.7)-(7.1.8)).

Given (ii), the argument is the rank count in its sharpest form: a surjection whose target is at
least as large as its source is a bijection, hence injective on the source, so a class whose
localisation at *every* place vanishes must be zero.

The classical way to obtain the place `A` of (ii): take a prime `𝔭` of `K` split completely over a
rational prime `ℓ ≡ 1 mod p` (so that `μ_p ⊆ K_𝔭 ⊆ E_v` for the places `v` of `E = K'^U` over
`𝔭`, hence the coefficient twist `Z/p ≅ μ_p` is invisible there and local Tate duality gives the
local groups `H²(U ⊓ D_A, Z/p)` their expected order), and use the surjectivity of the
localisation onto the product over the places over `𝔭` (Neukirch's input).  Every one of these
ingredients is local or a surjectivity statement; none is the Hasse principle.  See README §14 for
the detailed discussion, for the relation to the other routes, and for the precise reason the
*injectivity* statements (`LimitPassage`, `Sha2Input.level`) are not subsumed by this one.
-/

import Submission.NK.HassePrinciple.Defs
import Submission.NK.BrauerHasse.exists_heightOneSpectrum_eq_comap

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The places over a fixed finite prime -/

/-- **The places of `K'` over a fixed finite prime `𝔭` of `K`**: the places `A` of `K'` whose
restriction to `K` is the valuation ring `𝒪_𝔭`, i.e. the primes of the fixed field of a closed
subgroup sitting over `𝔭`.  This is the index set of Neukirch's rank count. -/
abbrev PlacesOverPrime (K K' : Type u) [Field K] [NumberField K] [Field K'] [Algebra K K']
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : Type u :=
  {A : ValuationSubring K' //
    A.comap (algebraMap K K') = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭}

/-- The valuation ring of a finite prime of a number field is not the whole field. -/
theorem isDedekindDomain_valuationSubringAtPrime_ne_top
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 ≠ ⊤ := by
  intro h
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.valuationSubring_eq_top_iff] at h
  exact h inferInstance

/-- A place of `K'` over the finite prime `𝔭` is a place over a finite prime of `K`. -/
noncomputable def PlacesOverPrime.toOverFinitePrime
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (A : PlacesOverPrime K K' 𝔭) : OverFinitePrime K K' :=
  ⟨A.1, by rw [A.2]; exact isDedekindDomain_valuationSubringAtPrime_ne_top (K := K) 𝔭⟩

/-! ## The local cohomology at a place is the cohomology of the local group

The local colimit `NK.BrauerHasse.LocalH2 p U A` is, *definitionally*, the protinite cohomology
`NK.BrauerHasse.H2Profinite p (U ⊓ D_A)` of the local group: both are the filtered colimit of the
level cohomologies of the level groups `(U ⊓ D_A)/((U ⊓ D_A) ∩ Gal(K'/L))`.  This identification is
recorded because it makes the local computations of the input (`p ≤ Nat.card (LocalH2 p U A.1)`, and
the localisation itself) statements about the profinite cohomology of a closed subgroup of a
`p`-adic local Galois group, i.e. exactly what the local side (`NK.LocalCFT`) computes by local
Tate duality. -/
theorem LocalH2_eq_H2Profinite (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K') :
    LocalH2 p U A = H2Profinite p (U ⊓ stabSubgroup A) := rfl

/-- **At an inert place the fine local cohomology is the global one.**  If `U ≤ D_A` then
`LocalH2 p U A = H2Profinite p U` (by `LocalH2_eq_H2Profinite` and `U ⊓ D_A = U`), so the fine
localisation at such a place is an isomorphism of the global cohomology onto the *classical* local
group of `E = K'^U`.  This is the point at which the target statement `Sha2Vanishing` is genuine:
the fine (colimit) local group is always the classical local group `G_{E_v}`, whereas the
finite-level theorem `HBNUnits` localises at the *coarser* stabilisers `C_M(A)`, whose limit over
the levels is `D_A·U/U` (of order `[U : U ⊓ D_A]`) and not `U ⊓ D_A` — different groups unless the
place is inert.  See README §14.6. -/
theorem LocalH2_eq_H2Profinite_of_le_stabSubgroup (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : ValuationSubring K') (h : U ≤ stabSubgroup A) :
    LocalH2 p U A = H2Profinite p U := by
  rw [LocalH2_eq_H2Profinite, inf_eq_left.mpr h]

/-! ## The localisation at a single place -/

/-- **The localisation at a single place**, as a plain function: the `A`-component of
`NK.BrauerHasse.H2Profinite.loc`. -/
noncomputable def locAt (p : ℕ) (U : Subgroup Gal(K'/K)) (A : OverFinitePrime K K') :
    H2Profinite p U → LocalH2 p U A.1 :=
  fun x => H2Profinite.loc p U x A

theorem locAt_zero (p : ℕ) (U : Subgroup Gal(K'/K)) (A : OverFinitePrime K K') :
    locAt p U A 0 = 0 :=
  H2Profinite.loc_zero p U A

/-- The localisation at a fixed prime `𝔭`, as a map to the product of the local groups over the
places of `K'` above `𝔭`.  This is the map whose *surjectivity* is Neukirch's input
(`eq:NeukirchH2modifiedsurj`). -/
noncomputable def localisationAt (p : ℕ) (U : Subgroup Gal(K'/K))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    H2Profinite p U → ((A : PlacesOverPrime K K' 𝔭) → LocalH2 p U A.1) :=
  fun x A => locAt p U A.toOverFinitePrime x

/-- Surjectivity onto the product over the places over `𝔭` implies surjectivity of every
component; this is the formal link between Neukirch's input (a statement about the product) and the
single-place input used by the rank count. -/
theorem surjective_locAt_of_surjective_localisationAt (p : ℕ) (U : Subgroup Gal(K'/K))
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : Function.Surjective (localisationAt (K := K) (K' := K') p U 𝔭))
    (A₀ : PlacesOverPrime K K' 𝔭) :
    Function.Surjective (locAt (K := K) (K' := K') p U A₀.toOverFinitePrime) := by
  classical
  have hcomp : (fun f : (A : PlacesOverPrime K K' 𝔭) → LocalH2 p U A.1 => f A₀) ∘
      (localisationAt (K := K) (K' := K') p U 𝔭) =
      locAt (K := K) (K' := K') p U A₀.toOverFinitePrime := rfl
  rw [← hcomp]
  have hev : Function.Surjective (fun f : (A : PlacesOverPrime K K' 𝔭) → LocalH2 p U A.1 => f A₀) :=
    fun y => ⟨Function.update (fun _ => (0 : LocalH2 p U _)) A₀ y,
      Function.update_self A₀ y (fun _ => (0 : LocalH2 p U _))⟩
  exact hev.comp h

/-! ## The rank count -/

/-- **A surjection whose target is at least as large as its source is injective.**  This is the
cardinality computation at the heart of Neukirch's rank count.  (For finite types, a surjection
that is not injective strictly decreases the cardinality
(`Fintype.card_lt_of_surjective_not_injective`).) -/
theorem injective_of_surjective_of_card_le {α β : Type*} [Finite α] (f : α → β)
    (hf : Function.Surjective f) (h : Nat.card α ≤ Nat.card β) : Function.Injective f := by
  have hβ : Finite β := Finite.of_surjective f hf
  by_contra hinj
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite β
  have hlt : Nat.card β < Nat.card α := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_lt_of_surjective_not_injective f hf hinj
  omega


/-! ## The input, and the Hasse principle from it -/

section Input

variable {p : ℕ} {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **Neukirch's input for the Hasse principle, in the form of a rank count.**

The fields are:

1. `hp` — `p` is a prime;
2. `card_global` — for every closed subgroup `U ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)`, the group
   `H²(U, Z/p)` is *finite* of order at most `p`.  Classically `H²(G_κ, Z/p) ≅ Z/p` or `0`
   (local Tate duality for the `p`-adic field `κ`: `H²(G_κ, Z/p) ≅ Hom(μ_p(κ), Q/Z)`), transported
   along the labelling `U ≅ Gal(κ'/κ)`;
3. `local` — for every such `U` **whose `H²(U, Z/p)` is non-trivial**, there is a place `A` of `K'`
   over a finite prime of `K` at which
   * the localisation `H²(U, Z/p) → H²(U ⊓ D_A, Z/p)` is **surjective**, and
   * the local group is at least as large as the global one:
     `Nat.card (H²(U, Z/p)) ≤ Nat.card (H²(U ⊓ D_A, Z/p))`.

   Both halves are Neukirch's: the surjectivity of the localisation at a place over a fixed prime
   is the `eq:NeukirchH2modifiedsurj` of his proof of the local characterisation of decomposition
   groups (Neukirch, Invent. Math. 6 (1969), Theorem 1; NSW (9.2.1)), and the comparison of
   orders is the local computation of local class field theory at the local group
   (`H²(G_κ', Z/p) ≅ Hom(μ_p(κ'), Q/Z)`, NSW (7.1.7)-(7.1.8)).  The hypothesis `Nontrivial` is
   there to make the statement vacuity-safe: when `H²(U, Z/p) = 0` the conclusion of the Hasse
   principle is automatic and no place is demanded.

The classical way to produce the place is Neukirch's rank count: choose the prime `𝔭` so that
`μ_p ⊆ K_𝔭` (e.g. split completely over a rational prime `ℓ ≡ 1 mod p`); then for every place `v`
of `K'^U` over `𝔭` the coefficient twist `Z/p ≅ μ_p` is invisible and local Tate duality gives
`H²(U ⊓ D_A, Z/p) ≅ Z/p`.  The surjectivity onto the product over the places over `𝔭` then forces
all the components to be `Z/p` and, comparing orders, the localisation at a place over `𝔭` to be
bijective — in particular surjective with matching orders, which is the field above.  `p = 2` and
`κ = Q_2` is the case of the Neukirch–Uchida development.

Compare `NK.HasseTwist.NeukirchH2modifiedsurj`, the same input for the cyclotomic coefficient
module `μ_p` (where the local groups are computed through the Brauer group `Br(κ)[p] ≅ Z/p`); the
present module is its trivial-coefficient counterpart, which is the one the sibling chapter
`NK.HassePrinciple` consumes. -/
structure RankInput (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- the case of interest: `p` is a prime. -/
  hp : p.Prime
  /-- **Finiteness of `H²(U, Z/p)`** — the only non-surjectivity ingredient of the input.  It is a
  statement about `U` alone: no cohomology of `κ` enters, beyond the labelling `U ≃* Gal(κ'/κ)`.
  Classically it is the finiteness in local Tate duality at `κ`
  (`H²(G_κ, Z/p) ≅ Hom(μ_p(κ), Q/Z)`, which is `0` or `Z/p`), transported to `U` along the
  labelling; README §14.2. -/
  card_global : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (U ≃* Gal(κ'/κ)) → Finite (H2Profinite p U)
  /-- Neukirch's rank count: at some place the localisation is surjective and the local group is at
  least as large as the global one. -/
  rank : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (U ≃* Gal(κ'/κ)) → Nontrivial (H2Profinite p U) →
      ∃ A : OverFinitePrime K K',
        Function.Surjective (locAt (K := K) (K' := K') p U A) ∧
          Nat.card (H2Profinite p U) ≤ Nat.card (LocalH2 p U A.1)

/-- **The Hasse principle from Neukirch's input.**  A class of `H²(U, Z/p)` whose localisation
vanishes at *every* place of `K'` over a finite prime of `K` is zero.

The proof is the rank count in its sharpest form: at the place `A` supplied by the input, the
localisation is a surjection whose target is at least as large as its source, hence a bijection,
hence injective; a class killed at `A` is therefore zero.  No injectivity statement about the
localisation is assumed — the input is a *surjectivity* statement together with two cardinality
computations. -/
theorem sha2Vanishing_of_rankInput (h : RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' := by
  intro U hU hκ x hx
  by_cases hnt : Nontrivial (H2Profinite p U)
  · have hfin := h.card_global U hU hκ
    obtain ⟨A, hsurj, hcomp⟩ := h.rank U hU hκ hnt
    haveI := hfin
    have hinj : Function.Injective (locAt (K := K) (K' := K') p U A) :=
      injective_of_surjective_of_card_le _ hsurj hcomp
    exact hinj ((hx A).trans (locAt_zero p U A).symm)
  · haveI : Subsingleton (H2Profinite p U) := not_nontrivial_iff_subsingleton.mp hnt
    exact Subsingleton.elim x 0

/-- **The chapter's main theorem, under its canonical name.**  From Neukirch's input
(`NK.HassePrinciple.RankInput`: the finiteness of `H²(U, Z/p)` at the labelled subgroups, the
*surjectivity* of the localisation at a place, and the comparison of orders at the local group — all
of them statements of local class field theory together with Neukirch's `eq:NeukirchH2modifiedsurj`,
NSW (9.2.1), and **no** Hasse-principle statement), the Hasse principle
`NK.BrauerHasse.Sha2Vanishing p K K' κ κ'` holds.

This is the name the chapter's interface promises: see `Submission/Work/HassePrinciple/
Deliverable.lean` for the consumer corollaries, and README §22 for the amended interface.  (The
legacy `NK.HassePrinciple.sha2Vanishing_of_sha2Input` in `Inputs.lean` is the reduction from the
superseded level-wise input.) -/
theorem sha2Vanishing (h : RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' :=
  sha2Vanishing_of_rankInput h

/-! ## The product form of Neukirch's input

Neukirch's `eq:NeukirchH2modifiedsurj` is a statement about the *product* of the local groups over
all the places above a fixed prime: the localisation `H²(U, Z/p) → ∏_{A | 𝔭} H²(U ⊓ D_A, Z/p)` is
surjective.  The single-place input `NK.HassePrinciple.RankInput` is the componentwise form of
this statement together with the comparison of orders, which is what the rank count uses.  The
derivation is proved here. -/

/-- **The product form of Neukirch's input** (NSW (9.2.1)), together with the local computations of
local class field theory:

1. `card_global` — `H²(U, Z/p)` is finite (local Tate duality at `κ`);
2. `surj` — for every closed labelled `U` there is a prime `𝔭` and a place `A₀` over `𝔭` such that
   the localisation at `𝔭` is surjective onto the *product* over the places over `𝔭` (Neukirch's
   `eq:NeukirchH2modifiedsurj`, NSW (9.2.1)) and `H²(U ⊓ D_{A₀}, Z/p)` is at least as large as
   `H²(U, Z/p)` (the local computation at the local group).  **Neither field mentions the
   cohomology of `κ`**, other than through the labelling `U ≃* Gal(κ'/κ)`.

This is the form in which Neukirch's input is classically quoted; the single-place form
`NK.HassePrinciple.RankInput` used by the Hasse principle is derived from it below. -/
structure SurjInput (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- the case of interest: `p` is a prime. -/
  hp : p.Prime
  /-- **Finiteness of `H²(U, Z/p)`** — the only non-surjectivity ingredient. -/
  card_global : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (U ≃* Gal(κ'/κ)) → Finite (H2Profinite p U)
  /-- **Neukirch's surjectivity** onto the product over the places over a prime, together with the
  comparison of orders at a place over that prime (the local computation at the local group: the
  local group over `𝔭` is at least as large as the global one). -/
  surj : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (U ≃* Gal(κ'/κ)) →
      ∃ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
        (A₀ : PlacesOverPrime K K' 𝔭),
        Function.Surjective (localisationAt (K := K) (K' := K') p U 𝔭) ∧
          Nat.card (H2Profinite p U) ≤ Nat.card (LocalH2 p U A₀.1)

/-- **The product form of Neukirch's input implies the single-place form.**  The only content is
that surjectivity onto a product implies surjectivity of every component
(`surjective_locAt_of_surjective_localisationAt`) and that `card (H²(U, Z/p)) ≤ p ≤ card` of the
local group at `A₀` gives the required comparison of orders. -/
theorem rankInput_of_surjInput
    (h : SurjInput (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    RankInput (K := K) (K' := K') (κ := κ) (κ' := κ') p where
  hp := h.hp
  card_global := h.card_global
  rank U hU hκ _ := by
    obtain ⟨𝔭, A₀, hsurj, hcmp⟩ := h.surj U hU hκ
    exact ⟨A₀.toOverFinitePrime,
      surjective_locAt_of_surjective_localisationAt p U 𝔭 hsurj A₀, hcmp⟩


end Input

end NK.HassePrinciple

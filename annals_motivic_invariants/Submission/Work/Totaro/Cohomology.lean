import Submission.Work.Totaro.Defs
import Submission.Work.Totaro.StablyBirational_of_isoOver

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Totaro.Cohomology` — the cohomological content of Totaro's theorem

This module carries the **honest split** of the Totaro input: *what* of the appendix of
Lin–Shinder is cohomological machinery (named, since Mathlib has none of it) and *what* is the
abstract implication layer (proved here).

## What Totaro's theorem really uses

The appendix proves `thm:BurtCY` by the negativity lemma (a birational map of smooth projective
varieties with nef canonical classes is a pseudo-isomorphism), then `Pic(X₂) ≅ Pic(X₁)`,
`NS(X₂) ≅ NS(X₁)` and a `Proj` argument (an isomorphism in Picard rank one), then `lem-stbirCY` (a
birational map `Z × W ⇢ Z' × W` descends to `Z ⇢ Z'` when `Z`, `Z'` are not separably uniruled and
`W` is separably rationally connected), and finally observes that `K`-trivial varieties are not
separably uniruled (`cor-CYnSB`).  That route is recorded in
`Submission/Work/Totaro/Paper.lean`.

The *content* which the two L-link chapters consume as the named input `TotaroInput` — and which
no library supplies — is that the two `K`-trivial varieties of Picard rank one are distinguished by
a birational invariant of their cohomology: over an algebraically closed field, `H³(-)(1)` with the
Tate twist for the `G₂`-Grassmannian centres (Ito–Miura–Okawa–Ueda) and `H²(-)` for the K3 centres
(Hassett–Lai/Oguiso); over a general (infinite) field, the cohomology together with the Galois
action on it / the `c₁`-, `c₃`-type numbers.  The certificate recorded below asks of `I` that

1. **`I` does not change along a birational map.**  (For smooth projective `K`-trivial varieties of
   Picard rank one this is `thm:BurtCY`'s second clause: birationality forces isomorphism there.
   For arbitrary varieties it is a *strong* requirement — `H³` is not a birational invariant in
   general, a blow-up changes it — and it is what the "strength" section below is about.)
2. **Künneth** — `I (X × Y) = I X * I Y`, where `*` is the tensor product of cohomology objects.
3. **Tate-twist normalisation** — `I 𝔸ⁿ = 1`, i.e. affine space has the cohomology of a point in
   the Tate-twisted degrees in which `I` lives.

Consequences (2) and (3) together are the **product decomposition argument**:
`I (X × 𝔸ⁿ) = I X * I 𝔸ⁿ = I X * 1 = I X` (`affine_eq_of_kunneth` below).  Hence `I` is a *stable*
birational invariant, and a pair which is separated by `I` is not stably birational with *any*
exponents — which is exactly the conclusion of `cor-CYnSB` that the `cInv` count of the two
chapters needs.

## What the cohomology really contributes, and the strength of the certificate

In the paper's own proof the cohomological computations (Ito–Miura–Okawa–Ueda's
`c₁(M|_Z)³ = 14 ≠ 42 = c₁(M'|_{Z'})³` for the CY3 centres, Hassett–Lai's `H²` with its Hodge
structure for the K3 centres) provide exactly one thing: the two centres are **not isomorphic** —
the hypothesis `¬ IsoOver 𝕜 Z Z'` of `lem-nSBG2`, which both chapters already have.  The passage
from *non-isomorphism* to *non-stable-birationality* is the geometric content of the paper's
appendix (`thm:BurtCY` + `lem-stbirCY`), recorded in `Submission/Work/Totaro/Paper.lean`.

The certificate `CohSeparation` below packages that whole passage as a single hypothesis about an
invariant: `I` birational-invariant, multiplicative (Künneth), normalised on affine space (Tate
twist), and separating the pair.  Two remarks on its strength, for honesty:

* such a certificate implies `¬ StablyBirational 𝕜 X Y` (the theorem below) and hence, with no
  further hypotheses, `¬ IsoOver 𝕜 X Y` (`CohSeparation.not_isoOver`) — i.e. it is at least as
  strong as the cohomological input the paper's own proof uses;
* conversely, morally it is *equivalent* to `¬ StablyBirational 𝕜 X Y` (the invariant is the stable
  birational class; the converse is not proved here, see `NOTES.md` §6).  So the certificate is a
  *strong* named input: the layer proved in this module is the algebra of the passage (the product
  decomposition argument, Künneth, the Tate twist, and the pairing with the `ℙ¹`-bundle bridge),
  not an independent reduction of Totaro's theorem.  The reductions to statements of the geometry
  Mathlib lacks are the paper's own route of `Paper.lean` (`ThmBurtCY` + `LemStbirCY` +
  `K`-triviality ⇒ `cor-CYnSB` ⇒ `TotaroInput`) and the per-link certificates
  (`Work.Totaro.CY3CentreCohomology`, `Work.Totaro.K3CentreCohomology`).

## The two structures of this module

* `CohSeparation 𝕜 X Y` — the *usable certificate* for the pair: `α`, `toFun`, `bir_eq`,
  `affine_eq`, `separates`.  From it, `not_stablyBirational` (the abstract implication layer).
* `CohKunneth 𝕜 X Y` — the *faithful cohomological input* for the pair: the same plus the
  commutative monoid, Künneth and the Tate-twist normalisation instead of `affine_eq`.  The
  product decomposition argument `CohKunneth.toCohSeparation` proves that the former follows.

`CohDistinguishing 𝕜 Pic1` is the universal packaging (a certificate for every pair of
non-isomorphic `K`-trivial varieties of Picard rank one), i.e. the exact shape of the two
chapters' `TotaroInput` but carrying the cohomological certificate;
`Submission/Work/Totaro/Interface.lean` derives both `TotaroInput`s from it.

## Conventions

`toFun : Scheme.{0} → α` is a function of the *scheme*, not of a `𝕜`-variety with its instances, so
that `I (X × 𝔸ⁿ)` and `I X` are compared without instance bookkeeping; the multiplicative structure
lives on `α` alone.  `prodOver`, `AffineN`, `IsKTrivial`, `IsoOver`, `StablyBirational` are those
of `Work.Totaro.Defs` (i.e. of the K3/CY3 chapters).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Totaro

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-! ## 1. The usable certificate -/

/-- **The cohomological separation of a pair `(X, Y)`** (usable form).

The data is a *birational invariant of varieties* `toFun : Scheme.{0} → α` together with

* `bir_eq` — invariance of `toFun` under birational maps;
* `affine_eq` — the conclusion of the product decomposition argument: `I (A × 𝔸ⁿ) = I A`, i.e. `I`
  is a *stable* birational invariant (obtained from Künneth + the Tate-twist normalisation by
  `CohKunneth.toCohSeparation`);
* `separates` — the distinguishing `I X ≠ I Y` for the pair at hand.

For the two centres of the CY3/K3 links, `I` is `H³(-)(1)` resp. `H²(-)`; the fields are then
theorems of the cohomology theory. -/
structure CohSeparation (𝕜 : Type) [Field 𝕜] (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y]
    where
  /-- the type of cohomology objects (for `l`-adic cohomology: graded `ℚ_l`-vector spaces) -/
  α : Type
  /-- the birational invariant `I` -/
  toFun : Scheme.{0} → α
  /-- **birational invariance**: `I` is constant along birational maps -/
  bir_eq : ∀ {A B : Scheme.{0}} [Variety 𝕜 A] [Variety 𝕜 B],
    Nonempty (A.BirationalMap B) → toFun A = toFun B
  /-- **the product decomposition argument's conclusion**: `I (A × 𝔸ⁿ) = I A` -/
  affine_eq : ∀ (A : Scheme.{0}) [Variety 𝕜 A] (n : ℕ)
    [Variety 𝕜 (prodOver 𝕜 A (AffineN 𝕜 n))], toFun (prodOver 𝕜 A (AffineN 𝕜 n)) = toFun A
  /-- **the distinguishing**: for this pair, the invariants differ -/
  separates : toFun X ≠ toFun Y

namespace CohSeparation

variable {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]

/-- **`CohSeparation` implies that the pair is not birational**: if `X ⇢ Y` were birational, `I`
would take the same value on both, contradicting the distinguishing. -/
theorem not_nonempty_birationalMap (C : CohSeparation 𝕜 X Y) :
    ¬ Nonempty (X.BirationalMap Y) :=
  fun hφ => C.separates (C.bir_eq hφ)

/-- **The abstract implication layer of Totaro's theorem.**

If a pair `(X, Y)` of varieties is separated by a birational invariant of its cohomology which is
insensitive to multiplication by affine space (the product decomposition argument), then `X` and
`Y` are **not stably birational** — with *all* exponents, equal or not, since `I` cannot see the
difference between `X` and `X × 𝔸ⁿ`.

This is `cor-CYnSB`'s "in particular `Z` is not stably birational to `Z'`" once the cohomological
distinguishing is supplied, and it is stronger than the paper's same-`W` statement: no dimension
theory is needed. -/
theorem not_stablyBirational (C : CohSeparation 𝕜 X Y) : ¬ StablyBirational 𝕜 X Y := by
  rintro ⟨n, m, hXn, hYm, hφ⟩
  refine C.separates ?_
  rw [← C.affine_eq X n, C.bir_eq hφ, C.affine_eq Y m]

/-- **The certificate witnesses the non-isomorphism of the pair**: the honest cohomological content
of Totaro's corollary for the two concrete centres (Ito–Miura–Okawa–Ueda's `c₁³ = 14 ≠ 42` for the
CY3 centres, Hassett–Lai's `H²` with its Hodge structure for the K3 centres) is exactly that they
are not isomorphic over `𝕜` — the hypothesis `¬ IsoOver 𝕜 Z Z'` of `lem-nSBG2`, which the two
chapters already have — and the passage to non-isomorphism *up to stable birationality* is the
geometric content of `thm:BurtCY` + `lem-stbirCY` (`Submission/Work/Totaro/Paper.lean`).  This
statement records that the cohomologically phrased certificate is *at least* as strong as that
input: it yields `¬ IsoOver 𝕜 X Y`. -/
theorem not_isoOver (C : CohSeparation 𝕜 X Y) : ¬ IsoOver 𝕜 X Y :=
  fun h => C.not_stablyBirational (StablyBirational_of_isoOver h)

/-- **The certificate is a *stable* birational invariant of the pair.**  If `I` separates `X` and
`Y`, then it separates `X × 𝔸ⁿ` and `Y × 𝔸ᵐ`, for arbitrary exponents `n`, `m`: this is the form
in which the `cInv` count of the two L-link chapters consumes the certificate, since the coefficient
is read at a base point whose residue field is the *cylinder* function field `κ(Z)(t)` of a centre,
and the two sides of a link may be modelled with different exponents.  The proof uses only the
`affine_eq` field (the product decomposition argument). -/
def prod_affine (C : CohSeparation 𝕜 X Y) (n m : ℕ)
    [Variety 𝕜 (prodOver 𝕜 X (AffineN 𝕜 n))] [Variety 𝕜 (prodOver 𝕜 Y (AffineN 𝕜 m))] :
    CohSeparation 𝕜 (prodOver 𝕜 X (AffineN 𝕜 n)) (prodOver 𝕜 Y (AffineN 𝕜 m)) where
  α := C.α
  toFun := C.toFun
  bir_eq := C.bir_eq
  affine_eq := C.affine_eq
  separates := fun h => C.separates ((C.affine_eq X n).symm.trans (h.trans (C.affine_eq Y m)))

/-- The certificate is symmetric in the pair (`I X ≠ I Y` is symmetric). -/
def symm (C : CohSeparation 𝕜 X Y) : CohSeparation 𝕜 Y X where
  α := C.α
  toFun := C.toFun
  bir_eq := C.bir_eq
  affine_eq := C.affine_eq
  separates := C.separates.symm

/-- **The certificate is a birational invariant of the pair**: if `X'` is birational to `X` and
`Y'` to `Y` over `𝕜`, then the same invariant separates `X'` and `Y'`.  This is what lets the
certificate of the two centres of an L-link be transported to any other model of them — e.g. along
the base change `Z_ℚ ⤏ Z_𝕜` used by the K3 chapter, or from `Z` to the base point `z₀` of the CY3
chapter. -/
def congr {X' Y' : Scheme.{0}} [Variety 𝕜 X'] [Variety 𝕜 Y'] (C : CohSeparation 𝕜 X Y)
    (hX : Nonempty (X.BirationalMap X')) (hY : Nonempty (Y.BirationalMap Y')) :
    CohSeparation 𝕜 X' Y' where
  α := C.α
  toFun := C.toFun
  bir_eq := C.bir_eq
  affine_eq := C.affine_eq
  separates := fun h => C.separates ((C.bir_eq hX).trans (h.trans (C.bir_eq hY).symm))

end CohSeparation

/-! ## 2. The product decomposition argument -/

/-- **The product decomposition argument.**  If `I` takes values in a commutative monoid and is
multiplicative under products (Künneth) with affine space having the invariant of a point (the
Tate-twist normalisation `I 𝔸ⁿ = 1`), then `I` is insensitive to multiplication by affine space:

`I (A × 𝔸ⁿ) = I A * I 𝔸ⁿ = I A * 1 = I A`.

The hypotheses are stated with an *explicit* `CommMonoid` instance (rather than one carried by a
structure) so that the multiplicative structure used in the statement is the same on both sides of
the equalities. -/
theorem affine_eq_of_kunneth {α : Type} [CommMonoid α] (toFun : Scheme.{0} → α)
    (kunneth : ∀ (A B : Scheme.{0}) [Variety 𝕜 A] [Variety 𝕜 B]
      [Variety 𝕜 (prodOver 𝕜 A B)], toFun (prodOver 𝕜 A B) = toFun A * toFun B)
    (unit_affine : ∀ (n : ℕ) [Variety 𝕜 (AffineN 𝕜 n)], toFun (AffineN 𝕜 n) = 1)
    (A : Scheme.{0}) [Variety 𝕜 A] (n : ℕ)
    [Variety 𝕜 (prodOver 𝕜 A (AffineN 𝕜 n))] :
    toFun (prodOver 𝕜 A (AffineN 𝕜 n)) = toFun A := by
  rw [kunneth A (AffineN 𝕜 n), unit_affine n, mul_one]

/-! ## 3. The faithful cohomological input -/

/-- **The cohomological input for a pair** (faithful form): the four named fields of the
cohomological distinguishing, before the product decomposition argument.

For the two centres of the CY3/K3 links these are theorems of `l`-adic/Betti cohomology —
`bir_eq` from `thm:BurtCY` (an isomorphism invariant is a birational invariant for `K`-trivial
varieties of Picard rank one), `kunneth` from the Künneth formula with the tensor product of
cohomology objects, `unit_affine` from the Tate-twist normalisation combined with the vanishing of
the cohomology of affine space above degree `0`, and `separates` from the classification of the
`K`-trivial varieties of Picard rank one by their `H³` (threefolds) resp. `H²` (K3 surfaces). -/
structure CohKunneth (𝕜 : Type) [Field 𝕜] (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y]
    where
  /-- the type of cohomology objects -/
  α : Type
  /-- the tensor product of cohomology objects, with unit the cohomology of a point -/
  [commMonoid : CommMonoid α]
  /-- the birational invariant `I` -/
  toFun : Scheme.{0} → α
  /-- **birational invariance** -/
  bir_eq : ∀ {A B : Scheme.{0}} [Variety 𝕜 A] [Variety 𝕜 B],
    Nonempty (A.BirationalMap B) → toFun A = toFun B
  /-- **Künneth**: `I (A × B) = I A * I B` -/
  kunneth : ∀ (A B : Scheme.{0}) [Variety 𝕜 A] [Variety 𝕜 B]
    [Variety 𝕜 (prodOver 𝕜 A B)], toFun (prodOver 𝕜 A B) = toFun A * toFun B
  /-- **Tate-twist normalisation**: affine space has the cohomology of a point -/
  unit_affine : ∀ (n : ℕ) [Variety 𝕜 (AffineN 𝕜 n)], toFun (AffineN 𝕜 n) = 1
  /-- **the distinguishing** -/
  separates : toFun X ≠ toFun Y

namespace CohKunneth

variable {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]

/-- **Künneth + Tate-twist normalisation ⟹ the product decomposition argument**: the faithful
cohomological input yields the usable certificate.  This is the *proved* layer of the split. -/
def toCohSeparation (K : CohKunneth 𝕜 X Y) : CohSeparation 𝕜 X Y where
  α := K.α
  toFun := K.toFun
  bir_eq := K.bir_eq
  affine_eq := fun A hA n hn =>
    @affine_eq_of_kunneth 𝕜 _ K.α K.commMonoid K.toFun K.kunneth K.unit_affine A hA n hn
  separates := K.separates

/-- The abstract implication layer, in the notation of the faithful input: `I Z ≠ I Z'` and
`I (Z × 𝔸ⁿ) = I Z` imply that `Z` and `Z'` are not stably birational. -/
theorem not_stablyBirational (K : CohKunneth 𝕜 X Y) : ¬ StablyBirational 𝕜 X Y :=
  K.toCohSeparation.not_stablyBirational

end CohKunneth

/-! ## 4. The universal packaging (the shape of the two chapters' `TotaroInput`) -/

/-- **The cohomological distinguishing input.**

This is `CohKunneth` for every pair of non-isomorphic `K`-trivial varieties of Picard rank one —
the exact shape of the two chapters' `TotaroInput`, with the cohomological certificate carried as
data instead of the bare conclusion, and stated uniformly in the family `Pic1` of Picard-rank-one
predicates (instantiate it at `Work.CY3.PicardRankOne` resp. `Work.K3.PicardRankOneGeom`; see
`Submission/Work/Totaro/Interface.lean`).

It is a *named input* of this area: its four fields are theorems of `l`-adic/Betti cohomology for
the pairs at hand, and Mathlib has neither `l`-adic cohomology, nor Betti cohomology, nor the
Künneth formula, nor Tate twists.  The per-pair form `CohSeparation`/`CohKunneth` is the
mathematically sharpest one and the one to use when only the two concrete centres matter. -/
def CohDistinguishing (𝕜 : Type) [Field 𝕜] (Pic1 : Pic1Family 𝕜) : Prop :=
  ∀ (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y],
    IsKTrivial 𝕜 X → IsKTrivial 𝕜 Y → Pic1 X → Pic1 Y → ¬ IsoOver 𝕜 X Y →
    Nonempty (CohKunneth 𝕜 X Y)

/-- **The per-pair form of the cohomological input**: for every pair of non-isomorphic `K`-trivial
varieties of Picard rank one there is a *certificate* (rather than a Künneth-form invariant).  This is
the weakest form of the named input — it is what the cohomology theory actually produces for the two
concrete centres — and `Work.Totaro.totaroInput_CY3_of_separation` /
`Work.Totaro.totaroInput_K3_of_separation` in `Submission/Work/Totaro/Interface.lean` derive the two
chapters' `TotaroInput`s from it. -/
def CohSeparationDistinguishing (𝕜 : Type) [Field 𝕜] (Pic1 : Pic1Family 𝕜) : Prop :=
  ∀ (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y],
    IsKTrivial 𝕜 X → IsKTrivial 𝕜 Y → Pic1 X → Pic1 Y → ¬ IsoOver 𝕜 X Y →
    Nonempty (CohSeparation 𝕜 X Y)

variable {Pic1 : Pic1Family 𝕜}

/-- The faithful Künneth-form input implies the per-pair form (apply the product decomposition
argument to each pair). -/
theorem CohSeparationDistinguishing.of_kunneth (h : CohDistinguishing 𝕜 Pic1) :
    CohSeparationDistinguishing 𝕜 Pic1 :=
  fun X Y _ _ hX hY pX pY hne => (h X Y hX hY pX pY hne).map CohKunneth.toCohSeparation

/-- **Totaro's theorem from the cohomological input**: the `not_stablyBirat_of_not_iso` field of
the two chapters' `TotaroInput`, at the level of `CohDistinguishing`. -/
theorem not_stablyBirational_of_distinguishing (h : CohDistinguishing 𝕜 Pic1)
    {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]
    (hX : IsKTrivial 𝕜 X) (hY : IsKTrivial 𝕜 Y) (pX : Pic1 X) (pY : Pic1 Y)
    (hne : ¬ IsoOver 𝕜 X Y) : ¬ StablyBirational 𝕜 X Y :=
  CohKunneth.not_stablyBirational (h X Y hX hY pX pY hne).some

/-- **Totaro's theorem from the cohomological input**, in the exact bundled shape
`∀ X Y, _ → _ → _ → _ → ¬ IsoOver → ¬ StablyBirational` of the two chapters' `TotaroInput` field,
for an arbitrary Picard-rank-one predicate family `Pic1`.

This is the statement which `Submission/Work/Totaro/Interface.lean` packages into
`Work.CY3.TotaroInput` and `Work.K3.TotaroInput`. -/
theorem not_stablyBirat_of_not_iso_of_distinguishing (h : CohDistinguishing 𝕜 Pic1)
    (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y]
    (hX : IsKTrivial 𝕜 X) (hY : IsKTrivial 𝕜 Y) (pX : Pic1 X) (pY : Pic1 Y)
    (hne : ¬ IsoOver 𝕜 X Y) : ¬ StablyBirational 𝕜 X Y :=
  not_stablyBirational_of_distinguishing h hX hY pX pY hne

end

end Work.Totaro

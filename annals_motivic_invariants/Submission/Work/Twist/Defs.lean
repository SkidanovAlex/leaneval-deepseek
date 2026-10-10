/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Twist
-/
import Mathlib
import ChallengeDeps
import Submission.Work.PointlessIndexFive.All

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Twist` — the twist realization and the pointless twist

This is the interface of the area `Submission/Work/Twist`, which attacks the two **named
residuals** of `Submission/Work/PointlessIndexFive` for Lin–Shinder, *Motivic invariants of
birational maps*, Annals of Math. **199** (1), 2024, Theorem 1.2 (1) (a)–(d):

* `TwistRealization 𝕜` — the **geometric** residual: for every quintic twist `D : QuinticTwist 𝕜`
  (an elliptic curve `E/𝕜` with a rational point `P` of exact order `5` and `j ≠ 1728`, together
  with a cyclic quintic extension `L/𝕜`), the quotient `C = (E_L)/G` of the twist construction
  exists as a smooth proper geometrically integral curve over `𝕜` of dimension one, with the two
  Galois-descent bridges (`TwistCurveModel`);
* `HasPointlessTwist 𝕜` — the **arithmetic** residual: some quintic twist has non-vanishing class
  in `H¹(ℤ/5, E(L)) = ker N/(σ - 1)E(L)`, i.e. `P ∉ (σ - 1)E(L)` (Clark–Lacy, Theorem 1.10 for
  the classes (a)–(c); Lang–Tate, Theorem 7 for class (d)).

The composition `TwistRealization 𝕜 → HasPointlessTwist 𝕜 → HasPointlessIndexFiveCurve 𝕜` is
proved in `Work.PointlessIndexFive` (`hasPointlessIndexFiveCurve_of_twistRealization`); this area
builds the mathematics that the two halves need.

## What this file provides

1. **Short names** for the parent chapters' interface, so that a caller of `Work.Twist` needs a
   single import.
2. The **twist with respect to another generator** of `Gal(L/𝕜)`: `QuinticTwist.genPow`,
   `QuinticTwist.galMapPow` (the action of `σ ^ k` on `E(L)`), and the predicates
   `PointlessPow`, `TorsorHasPointPow`, `TorsorDivisorOfDegreePow`, `TwistBridges`.  This is what
   makes the residual statements **well posed**: the class of the cocycle `σ ↦ P` in
   `H¹(ℤ/5, E(L))` depends on the chosen generator of the Galois group, and both
   `Pointless` and the descent bridges must (and do) come out independent of that choice; see
   `pointless_pow_iff`, `torsorHasPointPow_iff`, `torsorDivisorOfDegreePow_iff` and
   `twistCurveModel_bridges` (proved in the sibling modules of this directory).
   This is the *only* place where the choice of generator could have entered the paper's argument.
3. The residuals **on the paper's own data**: `RealizationOf C₅ L`, `PointlessOf C₅ L`, and
   `PointlessTwistData 𝕜` — "one curve with a rational point of order `5` and `j ≠ 1728`, one
   cyclic quintic extension, whose twist is pointless and is realized by a curve model".
4. The **local-obstruction datum** `LocalObstruction D` — the form in which the paper decides
   `cls ≠ 0`: an additive map `φ` out of `E(L)` that annihilates the coboundaries
   `(σ - 1)E(L)` and does not annihilate `P`.  In the paper `φ` is the reduction map at a place
   `v` of `𝕜`: `σ` acts trivially on the residue field of `v` (so `φ` kills `(σ - 1)E(L)`), and
   `P` has good reduction of order `5` at `v` (so `φ P ≠ 0`).  The criterion
   `LocalObstruction D → D.Pointless` is proved in the sibling file `localObstruction_pointless`.

## Honest status

The two residuals are **not** discharged here, and `NOTES.md` records exactly why in the pinned
Mathlib (`5ed2965256`):

* the geometric half needs a quotient of a scheme by a finite group action (equivalently Galois
  descent of schemes along `L/𝕜`), together with the identification `Jac^n C ≅ E` behind the
  divisor-degree bridge — Mathlib has neither, and no smooth proper curve over a field at all;
* the arithmetic half needs the reduction map on points of a Weierstrass curve over a discrete
  valuation ring (Silverman, *AEC*, VII.2.1–2.2) together with the integrality/Néron-model
  argument, or weak Mordell–Weil (`E(𝕜)/5E(𝕜)` finite, Clark–Lacy Prop. 1.4) — Mathlib has
  neither; its *criterion* form is `LocalObstruction` below and is proved here.

What *is* delivered is the whole structure around the two residuals: the generator-independence
of the class (so that the residuals are invariants of the mathematical data and not of the
formalisation), the bridges between the additive and the multiplicative presentation of the class
(`nsmul_cls_eq_zero_iff` and friends), the criterion for `Pointless`, the assembly from the
paper's own data, and the roadmap in `NOTES.md`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry

namespace Work.Twist

noncomputable section

/-! ## 0. Names of the parent chapters' interface -/

abbrev FiveTorsionCurve (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] :=
  Work.TorsorExistence.FiveTorsionCurve 𝕜

abbrev CyclicExtension (𝕜 : Type) [Field 𝕜] (n : ℕ) :=
  Work.TorsorExistence.CyclicExtension 𝕜 n

abbrev QuinticTwist (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] :=
  Work.TorsorExistence.QuinticTwist 𝕜

/-- The twist data of the paper's proof: step (B) (a `FiveTorsionCurve`) and step (A) (a cyclic
quintic extension `L/𝕜`) assembled into a `QuinticTwist`. -/
abbrev quinticTwistOf {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (C₅ : FiveTorsionCurve 𝕜)
    (L : CyclicExtension 𝕜 5) : QuinticTwist 𝕜 := Work.PointlessIndexFive.quinticTwistOf C₅ L

abbrev CurveModel (𝕜 : Type) [Field 𝕜] := Work.PointlessIndexFive.CurveModel 𝕜

abbrev TwistCurveModel {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) :=
  Work.PointlessIndexFive.TwistCurveModel D

abbrev TwistRealization (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] : Prop :=
  Work.PointlessIndexFive.TwistRealization 𝕜

abbrev HasPointlessTwist (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] : Prop :=
  Work.PointlessIndexFive.HasPointlessTwist 𝕜

abbrev HasPointlessIndexFiveCurve (𝕜 : Type) [Field 𝕜] : Prop :=
  Work.TorsorExistence.HasPointlessIndexFiveCurve 𝕜

/-! ## 1. The twist with respect to another generator of the Galois group

The class `cls = [σ ↦ P]` of the twist lives in `H¹(ℤ/5, E(L)) = ker N / (σ - 1)E(L)`, where
`σ = D.ext.gen` is the *chosen* generator of the cyclic group `Gal(L/𝕜)`.  A prover who rebuilds
the twist data with the generator `σ ^ k` in place of `σ` (for `k` coprime to `5`) obtains an
a priori different group `ker N / (σ ^ k - 1)E(L)` and a different class.  The predicates below
express "the class formed with the generator `σ ^ k`" inside the *same* twist datum `D`, so that
the independence statements (`pointless_pow_iff` and its siblings) can be stated without
rebuilding `D`. -/

namespace QuinticTwist

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜)

/-- The `k`-th power of the chosen generator of `Gal(L/𝕜)`, as an algebra homomorphism of `L`
(the group power `D.ext.gen ^ k` of the Galois group, transported along
`AlgEquiv.toAlgHomHom`). -/
noncomputable def genPow (k : ℕ) : D.ext.L →ₐ[𝕜] D.ext.L :=
  (D.ext.gen : D.ext.L →ₐ[𝕜] D.ext.L) ^ k

/-- The action of `σ ^ k` on `E(L)`: this is the Galois action obtained by rebuilding the twist
with the generator `σ ^ k` in place of `σ`. -/
noncomputable def galMapPow (k : ℕ) : D.LPoints →+ D.LPoints :=
  WeierstrassCurve.Affine.Point.map (W' := D.E) (D.genPow k)

/-- `PointlessPow k`: the class of the cocycle `σ ^ k ↦ P` is non-zero, i.e. `P` is not of the
form `σ ^ k R - R`. -/
def PointlessPow (k : ℕ) : Prop := ¬ ∃ R : D.LPoints, D.galMapPow k R - R = D.PL

/-- `TorsorHasPointPow k`: `P` *is* of the form `σ ^ k R - R`, i.e. the class of the cocycle
`σ ^ k ↦ P` is trivial (`D.PointlessPow k` is its negation; this is the additive presentation of
`(D.toTorsor).HasPoint`). -/
def TorsorHasPointPow (k : ℕ) : Prop := ∃ R : D.LPoints, D.galMapPow k R - R = D.PL

/-- The degree-`n` divisor condition of the twist, in the presentation given by the generator
`σ ^ k`: `n • [σ ^ k ↦ P] = 0`, i.e. `nP` is a coboundary for `σ ^ k - 1`.  For `k = 1` this is
`D.toTorsor.DivisorOfDegree n`. -/
def TorsorDivisorOfDegreePow (k : ℕ) (n : ℕ) : Prop :=
  ∃ R : D.LPoints, D.galMapPow k R - R = (n : ℕ) • D.PL

/-- **The action of `σ ^ k` is the `k`-th iterate of the action of `σ`.**  This is what makes
`galMapPow` the Galois action of the twist rebuilt with the generator `σ ^ k`; it is the iterate
form of `WeierstrassCurve.Affine.Point.map_map` and of `AlgEquiv.toAlgHomHom` being a monoid
homomorphism. -/
theorem galMapPow_apply (k : ℕ) (P : D.LPoints) :
    D.galMapPow k P = (D.galMap)^[k] P :=
  (Work.PointlessIndexFive.galMap_iterate D k P).symm

/-- `galMapPow 1` is the original Galois action `σ ↦ σ`. -/
theorem galMapPow_one : D.galMapPow 1 = D.galMap := by
  dsimp only [galMapPow, genPow]
  rw [pow_one]
  rfl

/-- `galMapPow 0 = σ ^ 0 = 1` acts trivially. -/
theorem galMapPow_zero_apply (P : D.LPoints) : D.galMapPow 0 P = P := by
  rw [galMapPow_apply, Function.iterate_zero_apply]

/-- `TorsorHasPointPow` is the negation of `PointlessPow`; recorded so that the two forms can be
rewritten into each other. -/
theorem torsorHasPointPow_iff_not_pointlessPow (k : ℕ) :
    D.TorsorHasPointPow k ↔ ¬ D.PointlessPow k := by
  classical
  simp [PointlessPow, TorsorHasPointPow]

end QuinticTwist

/-! ## 1b. Isomorphic presentations of the cyclic extension

The twist data `QuinticTwist 𝕜` carries a *chosen* cyclic quintic extension `L/𝕜` (`D.ext`); a
prover constructing `L` by Kummer theory, by Artin–Schreier theory or from a cyclotomic field
obtains a *specific* model of it.  The residual statements must not depend on that choice, and
they do not: an isomorphism of the extension which carries the chosen generator to the chosen
generator transports the whole twist, hence `Pointless` and `TwistCurveModel`.  (The proof is
`Work.Twist.pointless_iff_of_extIso` and `Work.Twist.realizationOf_iff_of_extIso`; for the choice
of *generator* within a fixed extension see `PointlessPow`/`TwistBridges` above and
`Work.Twist.pointless_pow_iff`.) -/

/-- An isomorphism between two models of the same cyclic quintic extension of `𝕜`, compatible with
the chosen generators (`e ∘ σ = σ' ∘ e`). -/
structure ExtIso {𝕜 : Type} [Field 𝕜] (L L' : CyclicExtension 𝕜 5) where
  /-- The isomorphism of the top fields. -/
  toAlgEquiv : L.L ≃ₐ[𝕜] L'.L
  /-- It carries the chosen generator of `Gal(L/𝕜)` to the chosen generator of `Gal(L'/𝕜)`. -/
  gen_eq : ∀ x : L.L, toAlgEquiv (L.gen x) = L'.gen (toAlgEquiv x)

/-! ## 2. The two descent bridges of a twist model, for an arbitrary generator -/

/-- **The Galois-descent bridges of `TwistCurveModel`, stated with the generator `σ ^ k`.**
`TwistBridges D C k` says that a curve `C` has a `𝕜`-rational point iff `P` is a `(σ ^ k - 1)`-
coboundary, and a `𝕜`-rational divisor of degree `n` iff `nP` is one.  This Prop does **not**
depend on `k`: `twistBridges_one_iff` (sibling module) identifies the case `k = 1` with the two
`TwistCurveModel` bridges, and `torsorHasPointPow_iff`/`torsorDivisorOfDegreePow_iff` transport it
to every `k` coprime to `5`; conversely `twistCurveModel_bridges` reads the bridges off any curve
model.  It is the descent statement of the twist, not of the auxiliary generator used to write it
down. -/
def TwistBridges {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) (C : Scheme)
    [C.Over (Spec (CommRingCat.of 𝕜))] (k : ℕ) : Prop :=
  (Work.Arithmetic.HasRatPoint 𝕜 C ↔ D.TorsorHasPointPow k) ∧
    (∀ n : ℕ, Work.Arithmetic.HasRatDivisorOfDegree 𝕜 C n ↔ D.TorsorDivisorOfDegreePow k n)

/-! ## 3. The residual on the paper's own data -/

/-- The geometric residual for a *single* twist: the quotient `(E_L)/G` of the twist construction
is realized by a curve model. -/
def RealizationAt {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) : Prop :=
  Nonempty (TwistCurveModel D)

/-- The geometric residual for the twist built from the paper's own data: a curve with a rational
point of order `5` and `j ≠ 1728` (step (B)) and a cyclic quintic extension (step (A)). -/
def RealizationOf {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (C₅ : FiveTorsionCurve 𝕜)
    (L : CyclicExtension 𝕜 5) : Prop := RealizationAt (quinticTwistOf C₅ L)

/-- The arithmetic residual for the twist built from the paper's own data. -/
def PointlessOf {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (C₅ : FiveTorsionCurve 𝕜)
    (L : CyclicExtension 𝕜 5) : Prop :=
  Work.TorsorExistence.QuinticTwist.Pointless (quinticTwistOf C₅ L)

/-- **The residual of this area, on the paper's own data.**  There is a curve `E/𝕜` with a
rational point `P` of exact order `5` and `j ≠ 1728`, and a cyclic quintic extension `L/𝕜`, such
that the twist `C = (E_L)/G` of `E` by the cocycle `σ ↦ P` is pointless and is realized by a curve
model over `𝕜`.

This is the whole remaining content of the paper's Lemma `lem:torsors` *together with* the
scheme-theoretic realization, stated on the data that the paper itself produces (steps (A) and
(B)); `Work.Twist.hasPointlessIndexFiveCurve_of_pointlessTwistData` (module
`Submission.Work.Twist.Assembly`) turns it into `HasPointlessIndexFiveCurve 𝕜`, and hence into
`Work.Arithmetic.HasLLinkCurve 𝕜`. -/
def PointlessTwistData (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] : Prop :=
  ∃ (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5),
    PointlessOf C₅ L ∧ RealizationOf C₅ L

/-! ## 4. The local obstruction -/

/-- **The local-obstruction datum of the twist.**  An additive map `φ` out of `E(L)` which
annihilates the coboundaries `(σ - 1)E(L)` and does not annihilate `P`.

In the paper's proof `φ` is the reduction map at a place `v` of `𝕜` at which `L/𝕜` is totally
ramified with residue degree `1`, `E` has good reduction, and `P` reduces to a point of order `5`
of the reduced curve: `σ` acts trivially on the residue field, so `φ (σ R - R) = 0` for every
`R ∈ E(L)` (for `R` integral at the place above `v`), while `φ P ≠ 0`.

The criterion `LocalObstruction D → D.Pointless` is `Work.Twist.localObstruction_pointless`
(module `Submission.Work.Twist.Assembly`), the bundled form of
`Work.PointlessIndexFive.pointless_of_shift_mem_ker`; conversely every pointless twist admits such
an obstruction (`hasLocalObstruction_of_pointless`), so the obstruction form of the residual is
faithful (`hasPointlessTwistByObstruction_iff`). -/
structure LocalObstruction {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) where
  /-- The target of the obstruction, typically the group of `𝔽`-points of the reduced curve at a
  place of `𝕜` (in additive notation). -/
  G : Type
  [addCommGroup : AddCommGroup G]
  /-- The obstruction map, typically reduction at a place. -/
  toFun : D.LPoints →+ G
  /-- `P` does not reduce to zero: it has good reduction of order `5`. -/
  map_PL : toFun D.PL ≠ 0
  /-- Every coboundary `σ R - R` is killed by the obstruction, because `σ` acts trivially on the
  residue field at the place. -/
  map_shift : ∀ R : D.LPoints, toFun (D.galMap R - R) = 0

/-- `Nonempty (LocalObstruction D)` in `Prop` form. -/
def HasLocalObstruction {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) : Prop :=
  Nonempty (LocalObstruction D)

/-- **The arithmetic residual in local-obstruction form**: some quintic twist is forced to be
pointless by a local obstruction. -/
def HasPointlessTwistByObstruction (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] : Prop :=
  ∃ D : QuinticTwist 𝕜, HasLocalObstruction D

end

end Work.Twist

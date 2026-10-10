/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.PointlessTwist
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Twist.All

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.PointlessTwist` — the pointless-twist arithmetic

This is the interface of the area `Submission/Work/PointlessTwist`, one of the two named
residuals of the `Twist` chapter (read `Submission/Work/Twist/NOTES.md` §5, which is the spec):

* **the arithmetic residual** `Work.PointlessIndexFive.HasPointlessTwist 𝕜`, equivalently
  `Work.Twist.PointlessTwistData 𝕜`'s arithmetic half: a **concrete** choice of
  `(C₅ : FiveTorsionCurve 𝕜, L : CyclicExtension 𝕜 5)` with `PointlessOf C₅ L`, i.e. the class
  `cls = [σ ↦ P]` of the twist in `H¹(ℤ/5, E(L)) = ker N / (σ - 1)E(L)` is **non-zero**, i.e.

  `¬ ∃ R : E(L), σ R - R = P`   (`pointlessOf_iff_not_exists_shift`),

  for one field `𝕜` in each of the four classes of Lin–Shinder, *Motivic invariants of birational
  maps*, Annals of Math. **199** (1), 2024, Theorem 1.2 (1) (a)–(d):
  number fields, and function fields over a number field / a finite field / an algebraically
  closed field.

The criterion (`LocalObstruction D → D.Pointless`) and its faithfulness are **delivered** in
`Work.Twist`; what is left is the *instantiation* at a concrete `(E, P, L)` per class, and this
area is where that instantiation lives.

## The two forms of the residual used here

Both are sharp forms of `cls ≠ 0`, and both are *strictly* what a place of `L` produces:

* `HasInvariantObstruction D` — an additive map `φ` out of `E(L)` with `φ ∘ σ = φ` and
  `φ P ≠ 0`.  This is the form the **reduction map at a place** has: at a place `v` of `L` with
  `σ` acting trivially on the residue field, the reduction `E(L) → Ẽ(κ_v)` is additive and
  `σ`-invariant, and it does not kill `P` because `P` has good reduction (a point of order `5`
  at a place of residue characteristic `≠ 5` cannot reduce to `0`).  Proved equivalent to the
  local-obstruction form by `hasLocalObstruction_of_hasInvariantObstruction` and
  `hasInvariantObstruction_of_localObstruction` (the second only when `5 ≠ 0` in the target, so
  the two forms are genuinely different only in characteristic `5`).
* `HasSpecialization E₀ σ P` — for the *constant curve* classes: the concrete group homomorphism
  `E₀(𝔽(s)) →+ E₀(𝔽)` which is the specialization of an `𝔽(s)`-point at `s = 0`
  (Silverman, *AEC*, VII.2.1: the reduction map on the points of a Weierstrass curve with good
  reduction is a homomorphism, with kernel the points of negative valuation).

## Main results of the area

| name (module) | statement |
|---|---|
| `pointlessOf_iff_not_exists_shift` | `PointlessOf C₅ L ↔ ¬ ∃ R, σ R - R = P` — the criterion in the form a place decides |
| `pointlessOf_of_invariantObstruction` | an additive `σ`-invariant `φ` with `φ P ≠ 0` gives `PointlessOf` |
| `pointlessOf_of_forall_galMap_eq` | if `σ` acts trivially on `E(L)` then `PointlessOf` |
| `pointlessOf_iff_of_extIso` | `PointlessOf` depends only on the *model* of the extension |
| `hasInvariantObstruction_iff_pointless` | the place datum is *equivalent* to the residual: it loses nothing |
| `Place.pointlessOf_of_hasReductionPlace` | **the general place criterion**: a reduction datum at any place gives `PointlessOf` |
| `Place.not_exists_galMap_eq_add_of_specialization` | **the constant-curve criterion**: the specialization datum at `s = 0` gives `PointlessOf` |
| `FunctionField.pointlessOf_of_trivialGaloisAction` | **the constant-curve classes (b)–(d)**: trivial Galois action on `E(L)` gives `PointlessOf` |
| `Assembly.hasPointlessTwist_of_kummerResidualSharp` | **the closed chain** `ConstantsOnly → PointlessOf → HasPointlessTwist (RatFunc 𝔽)` |

## Honest status

`PointlessOf` at the concrete data is **not** proved in any class, and `NOTES.md` records exactly
which single missing theorem is responsible in each case (both are theorems of Silverman, *AEC*,
VII.2.1–2.2 — the reduction map on the points of a Weierstrass curve over a discretely valued
field — which Mathlib has only for the *equation* and not for the *points*).  What is delivered
is: the criterion in the intermediate form `HasInvariantObstruction` / `HasSpecialization` in which
a place produces it, the proof that these forms imply `PointlessOf` at the paper's own data, the
concrete `(C₅, L)` per class, the Galois-fixed-point dictionary (`galMap_eq_self_iff`: the
`σ`-fixed points of `E(L)` are exactly `E(𝕜)`), and the full reduction of the residual to that one
missing theorem per class.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry

namespace Work.PointlessTwist

noncomputable section

/-! ## 1. The paper's data and the residual -/

/-- An elliptic curve `E/𝕜` with `j ≠ 1728` and a rational point of exact order `5` (step (B) of
the paper's proof). -/
abbrev FiveTorsionCurve (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] :=
  Work.TorsorExistence.FiveTorsionCurve 𝕜

/-- A cyclic extension of degree `n` of `𝕜` with a chosen generator of its Galois group (step (A)
of the paper's proof). -/
abbrev CyclicExtension (𝕜 : Type) [Field 𝕜] (n : ℕ) := Work.TorsorExistence.CyclicExtension 𝕜 n

/-- The input of the twist construction: a `FiveTorsionCurve` together with a cyclic quintic
extension. -/
abbrev QuinticTwist (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] :=
  Work.TorsorExistence.QuinticTwist 𝕜

/-- The twist data of the paper's proof: step (B) and step (A) assembled. -/
abbrev twistOf {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (C₅ : FiveTorsionCurve 𝕜)
    (L : CyclicExtension 𝕜 5) : QuinticTwist 𝕜 := Work.PointlessIndexFive.quinticTwistOf C₅ L

/-- **The arithmetic residual of the area, at the paper's own data.**  The class of the cocycle
`σ ↦ P` in `H¹(ℤ/5, E(L)) = ker N / (σ - 1)E(L)` is non-zero — equivalently
`¬ ∃ R : E(L), σ R - R = P` (`pointlessOf_iff_not_exists_shift`), equivalently the twist
`C = (E_L)/G` has no `𝕜`-rational point. -/
abbrev PointlessOf {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (C₅ : FiveTorsionCurve 𝕜)
    (L : CyclicExtension 𝕜 5) : Prop := Work.Twist.PointlessOf C₅ L

/-- The arithmetic half of the parent chapter's residual: *some* quintic twist over `𝕜` is
pointless.  This is `Work.PointlessIndexFive.HasPointlessTwist 𝕜`, the Clark–Lacy (a)–(c) /
Lang–Tate (d) input. -/
abbrev HasPointlessTwist (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] : Prop :=
  Work.PointlessIndexFive.HasPointlessTwist 𝕜

/-! ## 2. The criterion, at the paper's data

`Work.Twist.localObstruction_pointless` already gives `LocalObstruction D → D.Pointless`, and
`Work.PointlessIndexFive.pointless_iff_not_exists_shift` the element-level form.  Here are the
instantiations at the paper's data, in the form in which a *place* of `L` produces the datum. -/

/-- **The criterion in the form a place decides it.**  `PointlessOf C₅ L` says exactly that `P` is
not a coboundary for the generator `σ` of `Gal(L/𝕜)`; this is the statement a local computation
(valuations at a place of `L`) refutes. -/
theorem pointlessOf_iff_not_exists_shift {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5) :
    PointlessOf C₅ L ↔
      ¬ ∃ R : (twistOf C₅ L).LPoints, (twistOf C₅ L).galMap R - R = (twistOf C₅ L).PL :=
  Work.PointlessIndexFive.pointless_iff_not_exists_shift (twistOf C₅ L)

/-- `PointlessOf C₅ L` is `(twistOf C₅ L).Pointless`; recorded so that the parent chapter's
element-level API applies to the data-level statement. -/
theorem pointlessOf_iff_pointless {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5) :
    PointlessOf C₅ L ↔ (twistOf C₅ L).Pointless := Iff.rfl

/-- **The criterion at the paper's data.**  A `Work.Twist.LocalObstruction` of the twist (an
additive map out of `E(L)` killing the coboundaries `(σ - 1)E(L)` but not `P`) forces
`PointlessOf C₅ L`. -/
theorem pointlessOf_of_localObstruction {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5)
    (h : Work.Twist.HasLocalObstruction (twistOf C₅ L)) : PointlessOf C₅ L :=
  Work.Twist.localObstruction_pointless _ h

/-- **The `σ`-invariant form of the obstruction.**  An additive map `φ` out of `E(L)` with
`φ ∘ σ = φ` (equivalently `φ` kills `(σ - 1)E(L)`) and `φ P ≠ 0`.  This is what the *reduction map
at a place* is: `σ` acts trivially on the residue field, so the reduction is `σ`-invariant. -/
def HasInvariantObstruction {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) : Prop :=
  ∃ (G : Type) (_ : AddCommGroup G) (φ : D.LPoints →+ G),
    (∀ x : D.LPoints, φ (D.galMap x) = φ x) ∧ φ D.PL ≠ 0

/-- `HasInvariantObstruction` at the paper's data. -/
abbrev HasInvariantObstructionOf {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5) : Prop :=
  HasInvariantObstruction (twistOf C₅ L)

/-- **The criterion in `σ`-invariant form, at the paper's data.** -/
theorem pointlessOf_of_invariantObstruction {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5)
    (h : HasInvariantObstructionOf C₅ L) : PointlessOf C₅ L := by
  obtain ⟨G, hG, φ, hgal, hP⟩ := h
  exact pointlessOf_of_localObstruction C₅ L
    (Work.Twist.localObstruction_of_galTrivial (twistOf C₅ L) G φ hgal hP)

/-- **The criterion with the data given as a single map.**  Every `σ`-invariant additive
`φ : E(L) →+ G` with `φ P ≠ 0` forces `PointlessOf C₅ L`. -/
theorem pointlessOf_of_galTrivial {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5) (G : Type) [AddCommGroup G]
    (φ : (twistOf C₅ L).LPoints →+ G)
    (hgal : ∀ x : (twistOf C₅ L).LPoints, φ ((twistOf C₅ L).galMap x) = φ x)
    (hP : φ (twistOf C₅ L).PL ≠ 0) : PointlessOf C₅ L :=
  pointlessOf_of_invariantObstruction C₅ L ⟨G, inferInstance, φ, hgal, hP⟩

/-- **The degenerate case.**  If `σ` acts trivially on `E(L)` (i.e. `E(L) = E(𝕜)`, as for a
constant elliptic curve over a rational function field with algebraically closed constants), then
`(σ - 1)E(L) = 0` and `PointlessOf` follows from `P ≠ 0`.  This is the form the constant-curve
construction of class (d) uses. -/
theorem pointlessOf_of_forall_galMap_eq {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5)
    (h : ∀ R : (twistOf C₅ L).LPoints, (twistOf C₅ L).galMap R = R) : PointlessOf C₅ L :=
  Work.PointlessIndexFive.pointless_of_galMap_eq (twistOf C₅ L) h

/-- **Faithfulness of the invariant form.**  Conversely, a pointless twist admits a `σ`-invariant
obstruction: the quotient map `E(L) → E(L)/(σ - 1)E(L)` is additive, `σ`-invariant (with the
trivial action on the quotient — indeed this is the *only* thing used, since
`cls = 0` would put `P` in the quotient of the coboundaries), and does not kill `P`.

Together with `pointlessOf_of_invariantObstruction` this says that the form of the residual in
which a place produces it loses nothing: the residual is *equivalent* to the existence of a
`σ`-invariant obstruction. -/
theorem hasInvariantObstruction_of_pointless {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5) (h : PointlessOf C₅ L) :
    HasInvariantObstructionOf C₅ L := by
  refine ⟨(twistOf C₅ L).LPoints ⧸ (twistOf C₅ L).shift.range, inferInstance,
    QuotientAddGroup.mk' (twistOf C₅ L).shift.range, fun x => ?_, ?_⟩
  · -- `σ` acts trivially on the quotient by the coboundaries: `σ x - x ∈ range shift`
    have hmem : (twistOf C₅ L).galMap x - x ∈ (twistOf C₅ L).shift.range :=
      AddMonoidHom.mem_range.mpr ⟨x, rfl⟩
    exact (QuotientAddGroup.eq_iff_sub_mem).mpr hmem
  · intro h0
    have hPLmem : (twistOf C₅ L).PL ∈ (twistOf C₅ L).shift.range :=
      (QuotientAddGroup.eq_zero_iff (twistOf C₅ L).PL).mp h0
    obtain ⟨R, hR⟩ := AddMonoidHom.mem_range.mp hPLmem
    exact (pointlessOf_iff_not_exists_shift C₅ L).mp h ⟨R, hR⟩

/-- **The residual in invariant-obstruction form is equivalent to the residual.** -/
theorem hasInvariantObstruction_iff_pointless {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5) :
    HasInvariantObstructionOf C₅ L ↔ PointlessOf C₅ L :=
  ⟨pointlessOf_of_invariantObstruction C₅ L, hasInvariantObstruction_of_pointless C₅ L⟩

/-! ## 3. Independence of the model of `L` -/

/-- `PointlessOf` is insensitive to replacing `L` by an isomorphic model of the extension
(`Work.Twist.ExtIso`), so the construction of the concrete `L` per class is free. -/
theorem pointlessOf_iff_of_extIso {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) {L L' : CyclicExtension 𝕜 5} (e : Work.Twist.ExtIso L L') :
    PointlessOf C₅ L ↔ PointlessOf C₅ L' :=
  Work.Twist.pointless_iff_of_extIso C₅ e

/-- `HasPointlessTwist 𝕜` from a data-level witness. -/
theorem hasPointlessTwist_of_pointlessOf {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5) (h : PointlessOf C₅ L) :
    HasPointlessTwist 𝕜 :=
  ⟨twistOf C₅ L, h⟩

/-- **The arithmetic residual of the area, in witness form**: there is a concrete `(C₅, L)` with
`PointlessOf C₅ L`.  This is `HasPointlessTwist 𝕜` (the twist data carries its own `C₅` and `L`),
stated on the paper's data. -/
def HasPointlessOf (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] : Prop :=
  ∃ (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5), PointlessOf C₅ L

/-- `twistOf` rebuilds a `QuinticTwist` from its own data (`Work.Twist`'s
`quinticTwistOf_toFiveTorsionCurve`, stated in the presentation used in this area). -/
theorem twistOf_toFiveTorsionCurve {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : QuinticTwist 𝕜) :
    Work.PointlessIndexFive.quinticTwistOf
      (Work.TorsorExistence.QuinticTwist.toFiveTorsionCurve D) D.ext = D :=
  Work.Twist.quinticTwistOf_toFiveTorsionCurve D

/-- `HasPointlessOf 𝕜` is the same statement as `HasPointlessTwist 𝕜`. -/
theorem hasPointlessOf_iff_hasPointlessTwist {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] :
    HasPointlessOf 𝕜 ↔ HasPointlessTwist 𝕜 := by
  constructor
  · rintro ⟨C₅, L, h⟩
    exact ⟨twistOf C₅ L, h⟩
  · rintro ⟨D, hD⟩
    exact ⟨Work.TorsorExistence.QuinticTwist.toFiveTorsionCurve D, D.ext,
      (twistOf_toFiveTorsionCurve D).symm ▸ hD⟩


end

end Work.PointlessTwist

/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.PointlessTwist
-/
import Mathlib
import ChallengeDeps
import Submission.Work.PointlessTwist.Place

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The function-field classes: constant curves, and the residual `E(𝔽(s)) = E(𝔽)`

The classes (b), (c), (d) of Lin–Shinder Theorem 1.2 (1) are function fields `𝕜 = 𝔽(t)` of a
positive-dimensional variety over a field `𝔽` (a number field, a finite field, or an algebraically
closed field).  The concrete model of the *data* that the parent chapters produce is

* `𝕜 = 𝔽(t)`, `L = 𝕜(s)` the Kummer extension with `s ^ 5 = t` (equivalently the Artin–Schreier
  extension `s ^ 5 - s = t` in characteristic `5`), `σ ∈ Gal(L/𝕜)` the automorphism `s ↦ ζ₅ s`
  (`s ↦ s + 1` in characteristic `5`) — `existsCyclicExtension_of_zeta5` /
  `existsCyclicExtension_of_charP_five`;
* `E` the **constant** elliptic curve over `𝔽` in Tate normal form (`Tate.tateCurve c`) with the
  rational point `P = (0,0)` of exact order `5` (`Tate.tate_five_smul`), base-changed to `𝕜`.

The place of `L` is `s = 0`; its residue field is `𝔽`, on which `σ` acts trivially.  The
**arithmetic residual** in this case is the classical

  `E(𝔽(s)) = E(𝔽)`   (every point of a constant curve over a rational function field is constant)

which is equivalent to "there is no non-constant morphism `ℙ¹ → E`", i.e. to the statement that an
elliptic curve is not unirational (Riemann–Hurwitz, or equivalently Lüroth's theorem together with
`genus E = 1`).  This is the paper's route (iii) (`Submission/Work/Twist/NOTES.md` §5): `σ` fixes
`𝔽` pointwise, so if every `L`-point of `E` is constant then `σ` acts trivially on `E(L)`, and then
`(σ - 1)E(L) = 0` while `P ≠ 0` — `pointless_of_galMap_eq`, i.e. `TrivialGaloisAction` below.

## Main results

* `ConstantsOnly 𝔽 E K` — the statement `E(K) = E(𝔽)` for a constant curve.
* `Point.map_eq_of_constantsOnly` — every `σ ∈ Gal(K/𝔽)` acts trivially on `E(K)` if
  `ConstantsOnly 𝔽 E K`; **proved here** (it is `Point.map_baseChange`).
* `TrivialGaloisAction C₅ L` — the residual at the paper's data: `σ` acts trivially on `E(L)`.
* `pointlessOf_of_trivialGaloisAction` — **the criterion**: `TrivialGaloisAction C₅ L` gives
  `PointlessOf C₅ L` (via the delivered `pointless_of_galMap_eq`).
* `ConstantsOnly_iff_of_extIso`-style transport is not needed: the residual is *provable* from
  `ConstantsOnly` at the concrete data by `pointlessOf_of_constantsOnly` (delegated plumbing).

## Honest status

`ConstantsOnly 𝔽 E K` is **not** proved: Mathlib has no theory of curves (no genus, no
Riemann–Hurwitz, no Lüroth).  What is delivered here is the reduction of the whole class to that
one classical statement, together with its identifiable consequences.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.PointlessTwist

noncomputable section

/-! ## 1. The constant-curve statement `E(K) = E(𝔽)` -/

/-- **`E(𝔽) = E(K)` for a constant Weierstrass curve `E` over `𝔽`.**  Every point of the base
change `E_K` over `K ⊇ 𝔽` is the base change of a point of `E(𝔽)`.

For `K = 𝔽(s)` this is the classical `E(𝔽(s)) = E(𝔽)`: a `K`-point of a constant elliptic curve is
a morphism `ℙ¹ → E`, and there is no non-constant such morphism by Riemann–Hurwitz (an elliptic
curve is not unirational).  This is the missing input in Mathlib. -/
def ConstantsOnly (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] (E : WeierstrassCurve 𝔽)
    (K : Type) [Field K] [DecidableEq K] [Algebra 𝔽 K] : Prop :=
  ∀ R : WeierstrassCurve.Affine.Point (E.baseChange K),
    ∃ Q : WeierstrassCurve.Affine.Point E,
      WeierstrassCurve.Affine.Point.baseChange (W' := E) 𝔽 K Q = R

/-- **`ConstantsOnly` makes the Galois action trivial.**  If every `K`-point of the constant curve
`E` is constant, then every `𝔽`-algebra automorphism `σ` of `K` (in particular the generator of
`Gal(L/𝕜) ⊂ Gal(L/𝔽)`) acts trivially on `E(K)`: `σ` fixes `𝔽`, and the base change of a constant
point is fixed (`Point.map_baseChange`). -/
theorem map_eq_self_of_constantsOnly {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] (E : WeierstrassCurve 𝔽)
    {K : Type} [Field K] [DecidableEq K] [Algebra 𝔽 K] (σ : K ≃ₐ[𝔽] K)
    (h : ConstantsOnly 𝔽 E K) (R : WeierstrassCurve.Affine.Point (E.baseChange K)) :
    WeierstrassCurve.Affine.Point.map (W' := E) (σ : K →ₐ[𝔽] K) R = R := by
  obtain ⟨Q, rfl⟩ := h R
  exact WeierstrassCurve.Affine.Point.map_baseChange (W' := E) (σ : K →ₐ[𝔽] K) Q

/-! ## 2. The residual at the paper's data -/

/-- **The residual of the function-field classes.**  For the concrete data of the classes
(b), (c), (d) — the constant Tate model `E` over `𝔽`, base-changed to `𝕜 = 𝔽(t)`, and the Kummer
(or Artin–Schreier) extension `L = 𝕜(s)` — the Galois generator `σ` acts trivially on `E(L)`.

This is exactly `ConstantsOnly 𝔽 E L` in the form used at the paper's data
(`map_eq_self_of_constantsOnly`), and it is what the classical `E(𝔽(s)) = E(𝔽)` provides. -/
def TrivialGaloisAction {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (C₅ : FiveTorsionCurve 𝕜)
    (L : CyclicExtension 𝕜 5) : Prop :=
  ∀ R : (twistOf C₅ L).LPoints, (twistOf C₅ L).galMap R = R

/-- **The criterion of the function-field classes.**  If `σ` acts trivially on `E(L)` then the
twist is pointless: `(σ - 1)E(L) = 0` while `P ≠ 0`.  (This is
`Work.PointlessIndexFive.pointless_of_galMap_eq` at the paper's data; no hypothesis on the field
class is used.) -/
theorem pointlessOf_of_trivialGaloisAction {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5) (h : TrivialGaloisAction C₅ L) :
    PointlessOf C₅ L :=
  pointlessOf_of_forall_galMap_eq C₅ L h

end

end Work.PointlessTwist

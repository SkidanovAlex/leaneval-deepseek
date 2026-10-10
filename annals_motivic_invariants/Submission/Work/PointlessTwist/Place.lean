/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.PointlessTwist
-/
import Mathlib
import ChallengeDeps
import Submission.Work.PointlessTwist.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The place datum: how a place of `L` decides `cls ≠ 0`

The criterion of `Submission.Work.PointlessTwist.Defs` reduces `PointlessOf C₅ L` to a
`σ`-invariant additive map `φ` out of `E(L)` with `φ P ≠ 0`.  This file fixes the two ways in
which a **place** of `L` produces such a map — the two named residuals of the area — and proves
that each of them gives `PointlessOf`:

* `ReductionPlace D` — the **general** place datum: an additive map
  `red : E(L) →+ G` into the group of points of the reduction of `E` at a place of `L`, which is
  `σ`-invariant because `σ` acts trivially on the residue field (the place being totally ramified
  with residue degree `1`), and which does not kill `P` because `P` has good reduction and its
  order is `5` while the residue characteristic is `≠ 5`.

  Silverman, *AEC*, VII.2.1–2.2: for a Weierstrass curve with good reduction at a place of a
  discretely valued field, the reduction map on points `E₀(L_v) → Ẽ(κ_v)` is a surjective
  homomorphism with kernel `E₁(L_v)` (the points of negative valuation), and it extends to all of
  `E(L_v)` (kernel `E₁`) through the Néron model.  **This is the missing theorem**: Mathlib has the
  reduction of the *equation* (`AlgebraicGeometry/EllipticCurve/Reduction.lean`:
  `IsMinimal`, `reduction`, `IsGoodReduction`) but not the reduction of *points*.

* `SpecializationResidual 𝔽 E K σ` — the **constant-curve** form used for the function-field
  classes: for `E` defined over the constant field `𝔽` and `K ⊇ 𝔽`, a homomorphism
  `E(K) →+ E(𝔽)` which is the specialization at the place `s = 0` (`K = 𝔽(s)`, `σ : s ↦ ζ₅ s`):
  it is the identity on the constant points (the special fibre of the constant model
  `E ×_𝔽 Spec 𝔽[s]_{(s)}` is `E` itself) and `σ`-invariant because `σ` fixes `𝔽` pointwise.
  For the *tangent normal form* with coefficients in `𝔽`, `P = (0,0)` is a constant point of order
  `5`, so `red P = P ≠ 0` and `PointlessOf` follows.

## Main results

* `pointless_of_hasReductionPlace` — the criterion for `ReductionPlace`.
* `pointlessOf_of_hasReductionPlace` — the same at the paper's data.
* `not_exists_galMap_eq_add_of_specialization` — the constant-curve criterion: if the
  specialization datum exists then no `K`-point `R` satisfies `σ R = R + P`, and hence the twist
  is pointless (`pointlessOf_of_specialization`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.PointlessTwist

noncomputable section

/-! ## 1. The general place datum -/

/-- **The reduction-place datum of the twist.**  The data by which a place of `L` decides the
class of the twist:

* `G` — the group of points of the reduction `Ẽ(κ_v)` of `E` at the place (in additive notation);
* `red` — the reduction map on points `E(L_v) → Ẽ(κ_v)`, which is additive (Silverman, *AEC*,
  VII.2.1: this is the theorem Mathlib is missing);
* `red_galMap` — `σ` acts trivially on the residue field of the place, so the reduction is
  `σ`-invariant;
* `red_PL_ne_zero` — `P` has good reduction and its reduction is non-zero. -/
structure ReductionPlace {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) where
  /-- The group of points of the reduced curve over the residue field. -/
  G : Type
  [addCommGroup : AddCommGroup G]
  /-- The reduction map on points at the place. -/
  red : D.LPoints →+ G
  /-- `σ` acts trivially on the residue field, so the reduction is `σ`-invariant. -/
  red_galMap : ∀ R : D.LPoints, red (D.galMap R) = red R
  /-- `P` has good reduction of order `5` at the place. -/
  red_PL_ne_zero : red D.PL ≠ 0

attribute [instance] ReductionPlace.addCommGroup

/-- `Nonempty (ReductionPlace D)` in `Prop` form. -/
def HasReductionPlace {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) : Prop :=
  Nonempty (ReductionPlace D)

/-- **The criterion for a place.**  A reduction place forces the twist to be pointless: if
`σ R = R + P` then `red P = red (σ R) - red R = 0`, but `red P ≠ 0`. -/
theorem pointless_of_hasReductionPlace {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : QuinticTwist 𝕜) (h : HasReductionPlace D) : D.Pointless := by
  obtain ⟨r⟩ := h
  refine Work.PointlessIndexFive.pointless_of_shift_mem_ker D r.red r.red_PL_ne_zero ?_
  intro R
  change r.red (D.galMap R - R) = 0
  rw [map_sub, r.red_galMap R, sub_self]

/-- **The criterion for a place, at the paper's data.** -/
theorem pointlessOf_of_hasReductionPlace {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5)
    (h : HasReductionPlace (twistOf C₅ L)) : PointlessOf C₅ L :=
  pointless_of_hasReductionPlace _ h

/-- **The invariant-obstruction datum is the reduction-place datum.**  (Every
`HasInvariantObstruction` is a `ReductionPlace`, and conversely.)  This is recorded so that the
callers can move between the two presentations. -/
theorem hasReductionPlace_iff_hasInvariantObstruction {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : QuinticTwist 𝕜) : HasReductionPlace D ↔ HasInvariantObstruction D := by
  constructor
  · rintro ⟨r⟩
    exact ⟨r.G, r.addCommGroup, r.red, r.red_galMap, r.red_PL_ne_zero⟩
  · rintro ⟨G, hG, φ, hgal, hP⟩
    exact ⟨{ G := G, addCommGroup := hG, red := φ, red_galMap := hgal, red_PL_ne_zero := hP }⟩

/-! ## 2. The constant-curve specialization datum

For the function-field classes the base field is `𝕜 = 𝔽(t)` and the extension is the Kummer
extension `L = 𝔽(s)`, `s ^ 5 = t`; the place is `s = 0`, its residue field is `𝔽`, and
`σ ∈ Gal(L/𝕜)` sends `s ↦ ζ₅ s`, hence fixes `𝔽` pointwise.  The reduction at that place of a
curve **defined over `𝔽`** has target `E(𝔽)` itself (the special fibre of the constant model is
`E`), and it is the identity on the constant points.  This is the datum below. -/

/-- **The specialization datum of a constant Weierstrass curve.**  `E` is a curve over the
constant field `𝔽`, `K ⊇ 𝔽` is the function field (`K = 𝔽(s)`), and `σ` is the Galois automorphism
of `K/𝔽` of order `5` (`s ↦ ζ₅ s`); the datum is a homomorphism
`red : E(K) →+ E(𝔽)` — the specialization of a `K`-point at the place `s = 0` — which is the
identity on the constant points (`red_const`) and is `σ`-invariant (`red_galMap`), because `σ`
fixes the residue field `𝔽` pointwise.

Both properties are exactly Silverman, *AEC*, VII.2.1 for the constant model
`E ×_𝔽 Spec 𝔽[s]_{(s)}`; the missing ingredient in Mathlib is the reduction map on *points*. -/
structure SpecializationResidual (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] (E : WeierstrassCurve 𝔽)
    (K : Type) [Field K] [DecidableEq K] [Algebra 𝔽 K] (σ : K ≃ₐ[𝔽] K) where
  /-- The specialization map on points. -/
  red : WeierstrassCurve.Affine.Point (E.baseChange K) →+ WeierstrassCurve.Affine.Point E
  /-- It is the identity on the constant points. -/
  red_const : ∀ Q : WeierstrassCurve.Affine.Point E,
    red (WeierstrassCurve.Affine.Point.baseChange (W' := E) 𝔽 K Q) = Q
  /-- `σ` fixes `𝔽` pointwise, so the specialization is `σ`-invariant. -/
  red_galMap : ∀ R : WeierstrassCurve.Affine.Point (E.baseChange K),
    red (WeierstrassCurve.Affine.Point.map (W' := E) (σ : K →ₐ[𝔽] K) R) = red R

/-- **The constant-curve criterion.**  If the specialization datum exists (`E` constant over `𝔽`,
`K ⊇ 𝔽`, `σ` of order `5`), then there is no `K`-point `R` with `σ R = R + Q` for a **non-zero
constant point** `Q ∈ E(𝔽)`.  This is `P ∉ (σ - 1)E(K)` in the constant-curve case. -/
theorem not_exists_galMap_eq_add_of_specialization {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽]
    {E : WeierstrassCurve 𝔽} {K : Type} [Field K] [DecidableEq K] [Algebra 𝔽 K]
    {σ : K ≃ₐ[𝔽] K} (h : SpecializationResidual 𝔽 E K σ)
    (Q : WeierstrassCurve.Affine.Point E) (hQ : Q ≠ 0) :
    ¬ ∃ R : WeierstrassCurve.Affine.Point (E.baseChange K),
      WeierstrassCurve.Affine.Point.map (W' := E) (σ : K →ₐ[𝔽] K) R
        = R + WeierstrassCurve.Affine.Point.baseChange (W' := E) 𝔽 K Q := by
  rintro ⟨R, hR⟩
  have h2 : h.red R
      = h.red R + Q := by
    calc h.red R
        = h.red (WeierstrassCurve.Affine.Point.map (W' := E) (σ : K →ₐ[𝔽] K) R) :=
          (h.red_galMap R).symm
      _ = h.red (R + WeierstrassCurve.Affine.Point.baseChange (W' := E) 𝔽 K Q) := by rw [hR]
      _ = h.red R + h.red (WeierstrassCurve.Affine.Point.baseChange (W' := E) 𝔽 K Q) :=
          map_add _ _ _
      _ = h.red R + Q := by rw [h.red_const Q]
  refine hQ ?_
  have h4 : h.red R + Q = h.red R + 0 := by rw [add_zero]; exact h2.symm
  exact add_left_cancel h4

end

end Work.PointlessTwist

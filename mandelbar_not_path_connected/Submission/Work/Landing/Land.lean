import Submission.Work.Landing.Rays

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The landing theorem for the tricorn: interface and inputs

This file collects the landing-theorem statements and the classical inputs they rest on, in the
form used by the top-level argument (`NOTES_LEAD_mandelbar_arc_top.md` §2.3, §4).

**Scope.**  Everything in the landing area is phrased with `Work.ParamRays.IsDynBottcher`, a
Böttcher coordinate of `T_c` on the whole escaping set.  Such a coordinate exists **iff
`c ∈ M*`**, so these notions are only meaningful for parameters in the mandelbar; off it one must
use `Work.ParamRays.IsCritBottcher` (a coordinate on the critical domain `{G_c > G_c 0}`).  The
dynamical rays consumed by the `EL` areas and by `FSeed` are all instantiated at parameters in
`M*`, so this is not a restriction there.  (The former definition `CritOnRay`, which was
`≡ False` off `M*` because it used `IsDynBottcher`, has been deleted.)

## The theorem (Milnor, *Dynamics in one complex variable*, Theorem 18.10)

For every parameter `c`, a periodic dynamic ray `R_c(θ)` of `T_c` lands at a periodic point of
`T_c` which is repelling or parabolic.  The two ingredients are

* `PeriodicRaysLand c` (the ray lands) — Douady–Hubbard, and
* `AttractingCyclesInner c` (the landing point is not an interior point of the filled Julia set,
  because the only unbounded Fatou component is the basin of infinity).

The dichotomy "repelling or parabolic" then follows from `IsRepelling c k x ∨ IsParabolic c k x`;
the realness of the multiplier of the second return map at an odd-period point
(`deriv_tsq_iterate_odd_real`) is what converts "not attracting" into exactly this dichotomy.

## The two used instances

* **Root rays (`F*`, `root_rays`).** At the root-arc parameter of the non-real period-`5`
  component, the two rays at angles `371/1023` and `404/1023` land at the characteristic parabolic
  point `z₁`: `RootRaysLand c z`.  Both angles have period `10` and are exchanged by the first
  return map, so `(T_c)^[5] z = z` and `(T_c)^[10] z = z`.
* **`hθ` (`23/63`).** The angle `23/63` has exact period `6`.  A ray landing at the characteristic
  parabolic point has period dividing `2·5 = 10` (rotation number zero, `RotationNumberZero`);
  since `6 ∤ 10` the ray `R_c(23/63)` cannot land there, so by Milnor 18.10 it lands at a
  *repelling* periodic point, and Goldberg–Milnor B.1 makes this stable in the parameter.

## Classical inputs used as hypotheses

* `PeriodicRaysLand` — periodic rays land (Douady–Hubbard, Milnor 18.10).
* `AttractingCyclesInner` — attracting cycles lie in the interior of the filled Julia set.
* `RotationNumberZero` — at a simple parabolic point (second-return multiplier `1`) every ray
  landing there has period dividing `2k` (Goldberg–Milnor orbit portraits; Milnor 18.10).
* `OnlyParabolicIsPeriodK` — for a *simple* parabolic parameter of period `k` the only parabolic
  cycle is the period-`k` cycle.
-/

noncomputable section

namespace Work.Landing

open Function
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.ParamRays (IsDynBottcher Escaping escapingSet)

/-- Geometric input to the landing theorem: an attracting periodic point of `T_c` has a
neighbourhood consisting of non-escaping points.  (Equivalently: the only unbounded Fatou
component of `T_c` is the basin of infinity, so attracting cycles lie in the interior of the
filled Julia set.  This is the topological half of Milnor 18.10.) -/
def AttractingCyclesInner (c : ℂ) : Prop :=
  ∀ z : ℂ, (∃ k : ℕ, IsAttracting c k z) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, ‖w - z‖ < ε → w ∉ escapingSet c

/-- The two root rays of the non-real period-`5` component land at `z`: this is the `root_rays`
clause of the root-parabolic parameter `RootParabolic` of
`NOTES_LEAD_mandelbar_arc_top.md` §4. -/
def RootRaysLand (c : ℂ) (z : ℂ) : Prop := landsAt c rootAngle1 z ∧ landsAt c rootAngle2 z

/-- **Rotation number zero** (Goldberg–Milnor orbit portraits; Milnor 18.10): at a simple
parabolic point `z` of odd period `k` whose holomorphic second return map has multiplier `1`,
every dynamic ray landing at `z` is fixed by the second return map, i.e. has period dividing
`2k`.

**Angle normalisation (this statement was repaired).**  Angles label rays only modulo `1`:
`landsAt c (θ + n) z ↔ landsAt c θ z` for every integer `n`
(`Work.FSeed.landsAt_add_int_iff`).  A conclusion of the form `PeriodicAngle θ (2 * k)`, i.e.
`angDouble^[2*k] θ = θ` with a *raw* real `θ`, is therefore **false**: if `θ` is replaced by
`θ + 1` the hypothesis `landsAt c (θ+1) z` still holds while `angDouble^[2*k] (θ+1) = 0 ≠ θ + 1`
for `2*k ≥ 1`.  The conclusion is consequently stated in the canonical representative of the
angle class, i.e. with `Int.fract θ`; on `θ ∈ [0,1)` this is literally the same statement
(`Work.LandLeaves.rotationNumberZero_iff_Ico`).  See
`Submission/Work/LandLeaves/NOTES_FALSE_RotationNumberZero.md` and
`Work.LandLeaves.refute_rotationNumberZero_raw`. -/
def RotationNumberZero (c : ℂ) (k : ℕ) : Prop :=
  ∀ z : ℂ, IsParabolic c k z → ∀ θ : ℝ, landsAt c θ z → PeriodicAngle (Int.fract θ) (2 * k)

/-- For a *simple* parabolic parameter of period `k`, the only parabolic cycle is the period-`k`
cycle (a "multi-parabolic" parameter, where two parabolic cycles coexist, is excluded). -/
def OnlyParabolicIsPeriodK (c : ℂ) (k : ℕ) : Prop :=
  ∀ z : ℂ, (∃ m : ℕ, IsParabolic c m z) → (Tantibar c)^[k] z = z

end Work.Landing

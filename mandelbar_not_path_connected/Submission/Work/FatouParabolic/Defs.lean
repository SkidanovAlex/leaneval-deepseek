/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# `Work.FatouParabolic` — Fatou's theorem on parabolic cycles

This area provides the two classical statements that the landing area `Work.LANDCL` leaves
open at the root-parabolic parameter and at `c = 1/4` (ledger §5, `LANDCL/Defs.lean:206` and
`LANDCL/Defs.lean:167`):

* `Work.LANDCL.ParabolicCycleInOmegaLimit c` — every parabolic point of `T_c` is an
  `ω`-limit point of the critical orbit of `T_c` (proved here as
  `Work.FatouParabolic.parabolicCycleInOmegaLimit`);
* `Work.LANDCL.QuarterParabolicIsFixed` — every parabolic point of `T_{1/4}` is fixed (proved
  here as `Work.FatouParabolic.quarterParabolicIsFixed`).

## The primitive input

The one primitive classical input used by this area is **Fatou's theorem on parabolic cycles**,
`Work.FatouParabolic.FatouParabolicInput`: for a polynomial map `F : ℂ → ℂ` of degree `≥ 2`, a
fixed point `z₀` with multiplier `1` has a critical point of `F` in its basin.

It is a named `Prop`, in the same style as the other primitive classical inputs of the
workspace (`Work.LANDCL.GoldbergMilnorB1`, `Work.LANDCL.SnailDichotomy`,
`Work.LANDCL.QuarterParabolicIsFixed`, ...) — never an `axiom`.  The *reduction* of the two
`LANDCL` statements to it, and the explicit real dynamics at `c = 1/4`, are proved in this area.

The classical proof of the input is the petal/Liouville argument of `Submission/Work/FatouParabolic/NOTES.md`
§2: the immediate basin of the parabolic point contains an attracting petal with a Fatou
coordinate `φ`; if the basin contained no critical point of `F`, then `F` would be a covering of
degree `≥ 2` of the basin, the inverse branch along the petal would extend to the whole basin,
so `φ` would be a biholomorphism of the (bounded) basin onto `ℂ`, contradicting Liouville.  The
formalisation of that reduction, on the flower of `Submission/Work/FatouCoord/`, is the subject
of `Submission/Work/FatouParabolic/Core/`.

## Main definitions

* `Work.FatouParabolic.basin`, `puncturedBasin` — the basin of a fixed point, and its punctured
  version (the points whose orbit converges to the point without ever attaining it);
* `Work.FatouParabolic.IsCriticalPoint` — `deriv F w = 0`;
* `Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo` — `F` is the evaluation of a
  polynomial of `natDegree ≥ 2`;
* `Work.FatouParabolic.FatouParabolicInput` — the primitive classical input.

## Main results

* `Work.FatouParabolic.parabolicCycleInOmegaLimit` — `LANDCL.ParabolicCycleInOmegaLimit c` from
  the input;
* `Work.FatouParabolic.quarterParabolicIsFixed` — `LANDCL.QuarterParabolicIsFixed` from the
  input and the explicit real dynamics of `T_{1/4}`;
* `Work.FatouParabolic.tendsto_quarter_criticalOrbit` — `(T_{1/4})^[n] (1/4) → 1/2`;
* `Work.FatouParabolic.quarter_parabolic_orbit_argument` — the elementary core of the `1/4`
  argument: a parabolic point in the closure of a critical orbit converging to `1/2` is `1/2`.

Import one module: `Submission.Work.FatouParabolic.All`.
-/
import Mathlib
import Submission.Work.LANDCL.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter

namespace Work.FatouParabolic

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-! ## Basins -/

/-- The **basin** of the fixed point `z₀` for `f`: the set of points whose forward orbit
converges to `z₀`.  This contains `z₀` itself when `z₀` is a fixed point. -/
def basin (f : ℂ → ℂ) (z₀ : ℂ) : Set ℂ :=
  {z : ℂ | Tendsto (fun n : ℕ => f^[n] z) atTop (𝓝 z₀)}

/-- The **punctured basin** of `z₀`: the points of the basin whose orbit never attains `z₀`.
For a parabolic fixed point this is the immediate basin minus the point itself together with its
preperiodic preimages. -/
def puncturedBasin (f : ℂ → ℂ) (z₀ : ℂ) : Set ℂ :=
  {z : ℂ | (∀ n : ℕ, f^[n] z ≠ z₀) ∧ z ∈ basin f z₀}

@[simp] theorem mem_basin {f : ℂ → ℂ} {z₀ z : ℂ} :
    z ∈ basin f z₀ ↔ Tendsto (fun n : ℕ => f^[n] z) atTop (𝓝 z₀) := Iff.rfl

@[simp] theorem mem_puncturedBasin {f : ℂ → ℂ} {z₀ z : ℂ} :
    z ∈ puncturedBasin f z₀ ↔ (∀ n : ℕ, f^[n] z ≠ z₀) ∧ z ∈ basin f z₀ := Iff.rfl

theorem puncturedBasin_subset_basin {f : ℂ → ℂ} {z₀ : ℂ} :
    puncturedBasin f z₀ ⊆ basin f z₀ := fun _ h => h.2

theorem puncturedBasin.not_mem_self {f : ℂ → ℂ} {z₀ : ℂ} : z₀ ∉ puncturedBasin f z₀ :=
  fun h => h.1 0 rfl

/-- A critical point of `f`. -/
def IsCriticalPoint (f : ℂ → ℂ) (w : ℂ) : Prop := deriv f w = 0

/-- A **fixed point of multiplier `1`** (a parabolic fixed point). -/
def IsMultiplierOneFixedPoint (F : ℂ → ℂ) (z₀ : ℂ) : Prop := F z₀ = z₀ ∧ deriv F z₀ = 1

/-- A **polynomial map of degree at least two**: `F` is the evaluation of a polynomial of
`natDegree ≥ 2`.  This excludes the constant, linear and identity maps, which is what the
classical theorem needs. -/
def IsPolynomialMapOfDegreeAtLeastTwo (F : ℂ → ℂ) : Prop :=
  ∃ P : Polynomial ℂ, 2 ≤ P.natDegree ∧ ∀ z : ℂ, F z = P.eval z

/-! ## The primitive classical input -/

/-- **Fatou's theorem on parabolic cycles** (Fatou; Milnor, *Dynamics in one complex variable*,
§13; Beardon, *Iteration of rational functions*, §9.3).

For a polynomial map `F : ℂ → ℂ` of degree `≥ 2` and a fixed point `z₀` of multiplier `1`, the
basin of `z₀` contains a critical point of `F`.

Equivalently: the immediate basin of a parabolic fixed point of a polynomial of degree `≥ 2`
cannot be free of critical points — the return map on the basin would then be a genuine covering
of degree `≥ 2`, the inverse branch along the petal would extend to the whole basin, and the
Fatou coordinate would exhibit the (bounded) basin as biholomorphic to `ℂ`.

This is the primitive classical input of the area, a named `Prop`; it is used as a hypothesis by
`Work.FatouParabolic.parabolicCycleInOmegaLimit` and
`Work.FatouParabolic.quarterParabolicIsFixed`. -/
def FatouParabolicInput : Prop :=
  ∀ (F : ℂ → ℂ) (z₀ : ℂ), IsPolynomialMapOfDegreeAtLeastTwo F →
    F z₀ = z₀ → deriv F z₀ = 1 →
    ∃ w : ℂ, IsCriticalPoint F w ∧ w ∈ basin F z₀

end

end Work.FatouParabolic

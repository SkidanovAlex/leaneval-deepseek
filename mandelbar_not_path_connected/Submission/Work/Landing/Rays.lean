import Submission.Work.ParamRays.Bottcher
import Submission.Work.Landing.Core
import Submission.Work.Landing.Angles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Dynamic rays and landing for the tricorn family

This file is the interface of the landing area for the tricorn family `T_c(z) = z̄² + c`.
It is phrased on top of the Böttcher coordinate `Work.ParamRays.IsDynBottcher c φ` of the
sibling parameter-ray area, so that everything here is consumable together with
`Work.ParamRays.Phi` and the parameter rays.

* `rayDirection θ`  : the direction `e^{2πiθ}`.
* `radialRay θ`     : the radial line `{r e^{2πiθ} : r > 1}` of the Böttcher coordinate.
* `dynRay c φ θ`    : the dynamic ray `R_c(θ)`, i.e. the preimage under `φ` of `radialRay θ`
  (intersected with the escaping set, so that no junk values of `φ` enter).
* `rayAccum c φ θ`  : the accumulation set of `R_c(θ)` near the Julia set — the points that are
  limits of ray points whose Böttcher coordinate tends to the unit circle.
* `RayLands c φ θ z`: the ray at angle `θ` lands at `z`, i.e. `rayAccum c φ θ = {z}`.
* `landsAt c θ z`   : the same, quantified over the (unique) Böttcher coordinate of `T_c`, so it
  does not mention `φ`; this is the shape in which the top-level argument uses landing.
* `coLands c θ θ'`  : the two rays land at a common point.
* `PeriodicRaysLand c`: the analytic input (Douady–Hubbard, Milnor 18.10) that every periodic
  ray lands.

The definitions only use `IsDynBottcher`, so they apply verbatim to `p_c = T_c ∘ T_c` or to any
unicritical (anti)polynomial family with a Böttcher coordinate.
-/

noncomputable section

open Classical

namespace Work.Landing

open Function
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.ParamRays (IsDynBottcher Escaping escapingSet)

/-- The direction `e^{2πiθ}` of the external ray at angle `θ`. -/
noncomputable def rayDirection (θ : ℝ) : ℂ :=
  Complex.exp (↑(2 * Real.pi * θ) * Complex.I)

/-- The radial line of angle `θ` in the exterior of the unit disk: `{r e^{2πiθ} : r > 1}`. -/
def radialRay (θ : ℝ) : Set ℂ := {w : ℂ | ∃ r : ℝ, 1 < r ∧ w = ↑r * rayDirection θ}

/-- The dynamic ray `R_c(θ)` for the Böttcher coordinate `φ`: the points of the escaping set
whose Böttcher coordinate lies on the radial line of angle `θ`.

**Scope.**  This is stated with `IsDynBottcher c φ` (a Böttcher coordinate on the whole escaping
set), which exists **iff `c ∈ M*`**; the notion is therefore only meaningful for parameters in
the mandelbar.  (Off `M*` the analogous object is defined on the critical domain
`Work.ParamRays.critDomain c = {G_c > G_c 0}`.) -/
def dynRay (c : ℂ) (φ : ℂ → ℂ) (θ : ℝ) : Set ℂ :=
  {z : ℂ | Escaping c z ∧ φ z ∈ radialRay θ}

/-- The accumulation set of the dynamic ray `R_c(θ)` near the Julia set: the set of points which
are limits of ray points with Böttcher coordinate of modulus arbitrarily close to `1`. -/
def rayAccum (c : ℂ) (φ : ℂ → ℂ) (θ : ℝ) : Set ℂ :=
  {x : ℂ | ∀ ρ : ℝ, 1 < ρ → x ∈ closure {z : ℂ | z ∈ dynRay c φ θ ∧ ‖φ z‖ ≤ ρ}}

/-- The dynamic ray at angle `θ` lands at `z` (relative to a fixed Böttcher coordinate `φ`). -/
def RayLands (c : ℂ) (φ : ℂ → ℂ) (θ : ℝ) (z : ℂ) : Prop := rayAccum c φ θ = {z}

/-- The dynamic ray `R_c(θ)` lands at `z`.  The Böttcher coordinate is existentially quantified;
by uniqueness of the Böttcher coordinate this does not depend on the choice.

**Scope.**  `landsAt` is meant for parameters `c ∈ M*` (it is used at the parabolic parameter of
`FSeed`/`EL`, and at parameters in the mandelbar); off the mandelbar it is *false by design*,
since `IsDynBottcher c φ` is unsatisfiable for `c ∉ M*` (`Work.ParamRays.critDomain`: the
parameter-plane coordinate lives on the critical domain instead). -/
def landsAt (c : ℂ) (θ : ℝ) (z : ℂ) : Prop :=
  ∃ φ : ℂ → ℂ, IsDynBottcher c φ ∧ RayLands c φ θ z

/-- The rays at angles `θ` and `θ'` co-land: they land at the same point. -/
def coLands (c : ℂ) (θ θ' : ℝ) : Prop := ∃ z : ℂ, landsAt c θ z ∧ landsAt c θ' z

/-- The analytic input of the landing theorem (Douady–Hubbard; Milnor, *Dynamics in one complex
variable*, Theorem 18.10): every periodic ray of `T_c` lands. -/
def PeriodicRaysLand (c : ℂ) : Prop := ∀ θ : ℝ, IsPeriodicAngle θ → ∃ z : ℂ, landsAt c θ z

/-- The dynamic rays are nonempty near the unit circle: for every angle and every `ρ > 1` the ray
has a point whose Böttcher modulus is at most `ρ`.  This is the surjectivity half of Böttcher's
theorem (the Böttcher coordinate maps the escaping set *onto* the exterior of the unit disk); it
is *not* implied by the characterisation `IsDynBottcher`, so it is carried as an explicit
hypothesis where the closure computations need it. -/
def RaysNearCircle (c : ℂ) (φ : ℂ → ℂ) : Prop :=
  ∀ θ : ℝ, ∀ ρ : ℝ, 1 < ρ → ∃ z : ℂ, z ∈ dynRay c φ θ ∧ ‖φ z‖ ≤ ρ


/-- A **Böttcher homeomorphism**: the Böttcher coordinate `φ` is injective on the escaping set and
maps it onto the exterior of the unit disk.  These two properties are part of Böttcher's theorem
but are *not* implied by the characterisation `IsDynBottcher`; they are supplied by the Böttcher
theory of the sibling areas (`Work.ParamRays.DynBottcherHomeo` for the concrete coordinate
`dynPhi`).  They are exactly what makes the ray transfer `T_c '' rayAccum θ = rayAccum (angDouble θ)`
elementary. -/
def IsDynBottcherHomeo (c : ℂ) (φ : ℂ → ℂ) : Prop :=
  IsDynBottcher c φ ∧
    (∀ z w : ℂ, Escaping c z → Escaping c w → φ z = φ w → z = w) ∧
    (∀ w : ℂ, 1 < ‖w‖ → ∃ z : ℂ, Escaping c z ∧ φ z = w)

/-- The inverse Böttcher coordinate extends continuously to the closed exterior of the unit disk.
This is the **Carathéodory/local-connectivity input**: for a hyperbolic or parabolic parameter the
Julia set is locally connected, the inverse Böttcher coordinate extends to `{1 ≤ ‖w‖}`, and every
dynamic ray lands (`Landing/Carathéodory/*`).  It is the existence half of Milnor 18.10, isolated
here as one hypothesis. -/
def InverseBottcherExtends (c : ℂ) (φ : ℂ → ℂ) : Prop :=
  ∃ Ψ : ℂ → ℂ, ContinuousOn Ψ {w : ℂ | 1 ≤ ‖w‖} ∧
    ∀ w : ℂ, 1 < ‖w‖ → Escaping c (Ψ w) ∧ φ (Ψ w) = w

/-- The landing point of the ray at angle `θ`, chosen once and for all (a junk value `0` when the
ray does not land, which for periodic angles only happens if `¬ PeriodicRaysLand c`). -/
noncomputable def landingPoint (c : ℂ) (θ : ℝ) : ℂ :=
  if h : ∃ z : ℂ, landsAt c θ z then Classical.choose h else 0

theorem landingPoint_spec {c : ℂ} {θ : ℝ} (h : ∃ z : ℂ, landsAt c θ z) :
    landsAt c θ (landingPoint c θ) := by
  rw [landingPoint]
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The dynamic ray is contained in the escaping set. -/
theorem dynRay_subset_escaping (c : ℂ) (φ : ℂ → ℂ) (θ : ℝ) :
    dynRay c φ θ ⊆ escapingSet c := fun _ hz => hz.1

/-- The accumulation set is contained in the closure of the escaping set, i.e. the landing point
of a ray is never an interior point of the filled Julia set. -/
theorem rayAccum_subset_closure_escaping (c : ℂ) (φ : ℂ → ℂ) (θ : ℝ) :
    rayAccum c φ θ ⊆ closure (escapingSet c) := fun _ hx =>
  closure_mono (dynRay_subset_escaping c φ θ)
    (closure_mono (fun _ hz => hz.1) (hx 2 one_lt_two))

end Work.Landing

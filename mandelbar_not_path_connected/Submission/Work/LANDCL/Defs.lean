/-
Copyright: subproject `Submission/Work/LANDCL/` of `mandelbar_not_path_connected`.

# LANDCL — the classical landing inputs of the tricorn

This area (`Submission/Work/LANDCL/`, namespace `Work.LANDCL`) supplies the three rows `gm`,
`repAngle`, `repAngle_quarter` of the delivery table of
`Submission/Work/NOTES_LEAD_mandelbar_residuals.md` §4:

* **`gm`** — Goldberg–Milnor Lemma B.1 in the *parameter* form consumed by `FSeed`,
  `Work.FSeed.RepellingRayParamStable`: a parameter at which the ray `R_c(θ)` lands at a
  *repelling* periodic point is not a limit point of the parameter ray `R(θ)`.  It is *proved*
  here (`Work.LANDCL.repellingRayParamStable`) from
  * the *dynamical* form of Goldberg–Milnor B.1 (the stability of the landing at a repelling
    point; `Work.LANDCL.GoldbergMilnorB1`), which is the primitive classical statement — its
    proof is the linearization of `T_c` at the repelling point, the description of the ray tail
    as the image of a fundamental segment under the inverse branch, and the joint continuity of
    the Böttcher coordinate;
  * `Work.ParamRays.NakaneInput` (the parameter Böttcher map; already the input of the
    `ParamRays` area, from which `Work.ParamRays.continuous_potential` is proved);
  * the dichotomy `Work.LANDCL.DynBottcherOnlyOnMandelbar` (a Böttcher coordinate on the
    *whole* escaping set exists only inside the mandelbar — the monodromy of the Böttcher
    coordinate around an escaping critical value is non-trivial; this is the standing scope
    warning of `Submission/Work/Landing/` and of `Submission/Work/ParamRays/`).
  The reduction itself is the content of §2 of `NOTES.md`: the critical value of a parameter on
  the parameter ray `R(θ)` is a point of the critical ray of `T_{c}` at angle `θ`, at level
  `‖Φ c‖ → 1`; its limit is the landing point `y` of `R_c(θ)`; hence `c = y`, a *repelling*
  periodic point which is also the critical value — impossible, because the only preimage of the
  critical value under `T_c` is the critical point `0`
  (`Work.LANDCL.not_isRepelling_criticalValue`).

* **`repAngle`** — `Work.Final.ParamAngleRepelling c` at the root-arc parameter: the ray
  `R_c(23/63)` lands at a repelling periodic point.  Assembled from the primitive landing
  inputs of `Work.Landing` (`PeriodicRaysLand`, `EvenPeriodLandingDichotomy`) and the
  non-parabolicity of the landing point, which follows from the *uniqueness of the parabolic
  cycle* at the root-parabolic parameter (`Work.LANDCL.OnlyParabolicIsCycleOf`) together with
  the arithmetic of `23/63` (`Work.Landing.landsAt_paramAngle_not_parabolic`).

* **`repAngle_quarter`** — the same at `c = 1/4`, where the unique parabolic cycle is the
  *fixed* point `1/2` of the period-`1` component: the input
  `Work.LANDCL.QuarterParabolicIsFixed` together with `Work.Landing.RotationNumberZero (1/4) 1`
  (`23/63` has exact period `6`, so it cannot be fixed by the second return map).  The conclusion
  of `RotationNumberZero` is normalised with `Int.fract` (the definition was repaired in area
  `LandLeaves`: it used to conclude the unnormalised `PeriodicAngle θ (2k)`, which is false since
  `landsAt` is `1`-periodic in the angle — see
  `Submission/Work/LandLeaves/NOTES_FALSE_RotationNumberZero.md`); `23/63 ∈ [0,1)`, so it applies
  verbatim here.

## Main definitions

* `Work.LANDCL.dynRaySet`, `Work.LANDCL.rayClosure`, `Work.LANDCL.critRaySet` — the dynamic and
  critical-domain rays as *sets of points of the plane*, i.e. with the Böttcher coordinate
  existentially quantified (this makes them usable both on and off the mandelbar).
* `Work.LANDCL.GoldbergMilnorB1`, `Work.LANDCL.DynBottcherOnlyOnMandelbar`,
  `Work.LANDCL.OnlyParabolicIsCycleOf`, `Work.LANDCL.QuarterParabolicIsFixed`,
  `Work.LANDCL.HyperbolicContraction` — the primitive classical inputs, as `Prop`s (never
  `axiom`s).

## Main results

* `Work.LANDCL.not_isRepelling_criticalValue` — the critical value is never a repelling periodic
  point.
* `Work.LANDCL.repellingRayParamStable` — `gm`.
* `Work.LANDCL.paramAngleRepelling_of_classical`,
  `Work.LANDCL.paramAngleRepelling_of_rootParabolic`, `Work.LANDCL.paramAngleRepelling_quarter`.

Import one module: `Submission.Work.LANDCL.All`.
-/
import Submission.Work.Landing.Land.Landing
import Submission.Work.Landing.Land.Caratheodory
import Submission.Work.ParamRays.continuous_potential
import Submission.Work.Final.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Work.LANDCL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Rays as sets of points of the plane -/

/-- **The dynamic ray of `T_c` at angle `θ`**, as a set of points of the plane: the points whose
Böttcher coordinate (for *some* Böttcher coordinate of `T_c`) lies on the radial line of angle
`θ`.  Existentially quantifying the coordinate makes the notion independent of the choice of
coordinate (by `Work.ParamRays.isDynBottcher_unique`) and usable at every parameter.

Scope: `Work.ParamRays.IsDynBottcher c φ` is satisfiable only for `c ∈ Mb` (see
`Work.LANDCL.DynBottcherOnlyOnMandelbar`), so `dynRaySet c θ` is empty off the mandelbar; the
critical-domain analogue `critRaySet` is the right notion outside. -/
def dynRaySet (c : ℂ) (θ : ℝ) : Set ℂ :=
  {z : ℂ | ∃ φ : ℂ → ℂ,
    Work.ParamRays.IsDynBottcher c φ ∧ z ∈ Work.Landing.dynRay c φ θ}

/-- The closure of the dynamic ray: the ray together with its landing set. -/
def rayClosure (c : ℂ) (θ : ℝ) : Set ℂ := closure (dynRaySet c θ)

/-- **The critical-domain ray of `T_c` at angle `θ`**: the points of the critical domain
`Work.ParamRays.critDomain c` whose critical Böttcher coordinate lies on the radial line of angle
`θ`, i.e. the points `z` with `φ z = r · e^{2πiθ}`, `1 < r`.  This is the dynamical ray in the
form in which it exists *outside* the mandelbar; compare the parameter ray
`Work.ParamRays.paramRay θ`, which by definition asks this of the critical value `z = c`. -/
def critRaySet (c : ℂ) (θ : ℝ) : Set ℂ :=
  {z : ℂ | ∃ (φ : ℂ → ℂ) (r : ℝ),
    Work.ParamRays.IsCritBottcher c φ ∧ z ∈ Work.ParamRays.critDomain c ∧ 1 < r ∧
      φ z = (r : ℂ) * Work.ParamRays.rayDir θ}

/-! ## The primitive classical inputs -/

/-- **Goldberg–Milnor Lemma B.1**, in its dynamical form: *the landing of a dynamic ray at a
repelling periodic point is stable under perturbation of the parameter*.

Precisely: if `R_c(θ)` lands at a repelling periodic point `y` of `T_c`, then any accumulation
point of ray points at nearby parameters and nearby levels (`cₙ → c`, `zₙ` a point of the
critical ray of `T_{cₙ}` at angle `θ` with `‖wₙ‖ → 1`) is the landing point `y` itself.

This is the classical content: near a repelling periodic point the ray tail is the image of a
fundamental segment under the inverse branch of `T_c^{2k}` (linearization at the repelling
point), and by the joint continuity of the Böttcher coordinate this description is stable in the
parameter; in particular the ray tail and its landing point move continuously.

Notation warning: this is *not* the parameter-ray statement `Work.FSeed.RepellingRayParamStable`
— it says nothing about the parameter ray `R(θ)`; the passage to the parameter ray is the
reduction proved in `Submission/Work/LANDCL/GM.lean`. -/
def GoldbergMilnorB1 : Prop :=
  ∀ (c : ℂ) (θ : ℝ) (k : ℕ) (y : ℂ), Work.Landing.IsRepelling c k y →
    Work.Landing.landsAt c θ y →
    ∀ (cn wn zn : ℕ → ℂ),
      (∀ n : ℕ, ∃ φ : ℂ → ℂ,
        Work.ParamRays.IsCritBottcher (cn n) φ ∧
          zn n ∈ Work.ParamRays.critDomain (cn n) ∧ φ (zn n) = wn n) →
      (∀ n : ℕ, ∃ r : ℝ, 1 < r ∧ wn n = (r : ℂ) * Work.ParamRays.rayDir θ) →
      Tendsto cn atTop (𝓝 c) →
      Tendsto (fun n : ℕ => ‖wn n‖) atTop (𝓝 1) →
      ∀ z : ℂ, Tendsto zn atTop (𝓝 z) → z = y

/-- **A Böttcher coordinate on the whole escaping set exists only inside the mandelbar.**  If
`φ` satisfies `Work.ParamRays.IsDynBottcher c φ` — continuous on the whole escaping set, solving
`φ (T_c z) = conj (φ z)²` there, and asymptotic to the identity at infinity — then `c ∈ Mb`.

This is the standing scope restriction of the Landing/ParamRays areas, recorded in their
docstrings ("`IsDynBottcher c φ` is satisfiable **iff `c ∈ M*`**"; "off `M*` the analogous object
is defined on the critical domain").  The reason is the monodromy of the Böttcher coordinate
around an escaping critical value: if `c ∉ Mb` then the critical value `c = T_c(0)` escapes and
is surrounded by the escaping set, and travelling once around it changes the branch of the
Böttcher coordinate (the equation `φ (T_c z) = conj (φ z)²` forces a sign change across the
critical value), so no single-valued continuous solution on the whole escaping set can exist.

Taken here as a named classical input: it is the existence half of Böttcher's theorem outside
the connectedness locus, and the workspace does not prove it (the topological/monodromy
argument is not formalized anywhere in `Submission/Work/`). -/
def DynBottcherOnlyOnMandelbar : Prop :=
  ∀ c : ℂ, (∃ φ : ℂ → ℂ, Work.ParamRays.IsDynBottcher c φ) → c ∈ Mandelbar

/-- **The unique parabolic cycle at the root-parabolic parameter.**  Every parabolic point of
`T_c` lies on the *exact* period-`5` cycle of the characteristic point `z₁`.

This is the classical portrait statement at the root of the odd period-`5` hyperbolic component
(Douady–Hubbard; Milnor 18.10; cf. `Work.Landing.OnlyParabolicIsPeriodK`, which only gives
`(T_c)^[5] z = z` without exactness and without locating `z` on the cycle of `z₁`).  It is the
input which rules out the landing point of `R(23/63)` being parabolic: such a point would lie on
the period-`5` cycle, but `R_c(23/63)` lands at a point of period dividing `6`, and `6 ∤ 10`. -/
def OnlyParabolicIsCycleOf (c z₁ : ℂ) : Prop :=
  (Tantibar c)^[5] z₁ = z₁ ∧ (Tantibar c) z₁ ≠ z₁ ∧
    ∀ z : ℂ, (∃ m : ℕ, Work.Landing.IsParabolic c m z) →
      ∃ j : ℕ, j < 5 ∧ z = (Tantibar c)^[j] z₁

/-- **The unique parabolic cycle at `c = 1/4` is a fixed point.**  Every parabolic point of
`T_{1/4}` is fixed by `T_{1/4}` (the cusp `1/2` of the period-`1` hyperbolic component).  The
second-return multiplier at it is `1`; this is recovered from the fixed-point condition in
`Work.LANDCL.parabolic_fixed_multiplier_one`. -/
def QuarterParabolicIsFixed : Prop :=
  ∀ z : ℂ, (∃ m : ℕ, Work.Landing.IsParabolic (1 / 4 : ℂ) m z) →
    Tantibar (1 / 4 : ℂ) z = z

/-- **The hyperbolic (Douady–Hubbard) contraction input**: for a parameter with a hyperbolic
critical orbit the inverse Böttcher coordinate extends continuously to the closed exterior of
the unit disk, so (by `Work.Landing.PeriodicRaysLand_of_extension`) every periodic ray of `T_c`
lands.

The classical proof of the extension is the contraction argument on `ℂ ∖ P`, `P` the closure of
the postcritical set (`P` is a countable closed set with empty interior; `T_c^{2n}` restricted
to the complement of a neighbourhood of `P` is expanding, so its inverse branches contract the
hyperbolic metric uniformly on compacts, and the inverse Böttcher iterates converge uniformly on
`{1 ≤ ‖w‖}`).  Packaged here as a `Prop`; it is *not* assumed anywhere in `Submission/Work/`
(the Landing area takes `InverseBottcherExtends` / the Carathéodory statement as its input). -/
def HyperbolicContraction (c : ℂ) : Prop :=
  ∃ φ : ℂ → ℂ, Work.Landing.IsDynBottcherHomeo c φ ∧
    Work.Landing.InverseBottcherExtends c φ

/-- **The Snail lemma in its landing form** (Douady–Hubbard; Milnor, *Dynamics in one complex
variable*, 18.10, whose proof uses the Snail lemma): a periodic point which is the landing point
of a dynamic ray and is **not attracting** is repelling or parabolic.

This is the primitive behind `Work.Landing.EvenPeriodLandingDichotomy`: a ray landing at `z`
prevents `z` from being an attracting (or indifferent, non-parabolic) point — the orbit of a
point of the ray spirals into `z`, and the Snail lemma forces the multiplier of the (second)
return map to be a root of unity, which for the tricorn means `1` (parabolic) or a repelling
point.  It is taken here as a named input; the workspace proves only the *odd* period case
(`Work.Landing.landsAt_repelling_or_parabolic`, from `AttractingCyclesInner` and the realness of
the multiplier of the second return map at odd-period points). -/
def SnailDichotomy : Prop :=
  ∀ (c : ℂ) (θ : ℝ) (k : ℕ) (z : ℂ), 0 < k → Work.Landing.PeriodicAngle θ k →
    Work.Landing.landsAt c θ z → ¬ Work.Landing.IsAttracting c k z →
    Work.Landing.IsRepelling c k z ∨ Work.Landing.IsParabolic c k z

/-- **Fatou's theorem on parabolic cycles** (Fatou; Milnor §10): every parabolic cycle is an
`ω`-limit cycle of the critical orbit.  Consequently, if the critical orbit converges to the
characteristic point `z₁` of a parabolic cycle, that cycle is the *only* parabolic cycle of the
map. -/
def ParabolicCycleInOmegaLimit (c : ℂ) : Prop :=
  ∀ z : ℂ, (∃ m : ℕ, Work.Landing.IsParabolic c m z) →
    z ∈ closure (Set.range (fun n : ℕ => (Tantibar c)^[n] c))

end Work.LANDCL

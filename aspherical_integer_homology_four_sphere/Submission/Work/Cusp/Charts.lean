/-
# The cusp charts: the boxes, the strata and the chart maps (definition layer)

This file fixes the *chart* conventions of the area `Work.Cusp`.  The mathematical content
(continuity, injectivity, openness, the round-trip identities of the explicit inverses, the cover)
is in the modules next to it, one lemma per module.

## The filling piece

The filling piece of the `v`-th cusp is `W_v = [-1,1]² × (ℝ/ℤ)²` (`W` in `Work.Cusp.Basic`),
parametrised by `(p,y)` with `p` the layer parameter in the square and `y = (y₂,y₃)` the two torus
coordinates `y₂κ_{v,2} + y₃κ_{v,3}`.  Since `(σ_v, κ_{v,2}, κ_{v,3})` is a basis of the lattice and
`σ_v = κ_{v,1} + b_v κ_{v,2}` lies in the `κ₁κ₂`-plane, the whole picture is a product of the
perimeter circle `u(p)σ_v` with the `(y₂,y₃)`-torus, and the metric model is

* `coreBox`/`polarBox`/`cuspBox`: the warped metric `dr² + f(r)²dθ² + h(r)²|dw|²` of
  profile `Work.Profiles.FillProfile` (with `f = r`, `h = h₀` in the core, and `f = Ce^r`, `h = De^r` in the
  collar, where the warped metric is the UHS metric under `polarToUHS`),
* `cuspBox`: the UHS metric `(|dx|²+ds²)/s²`, i.e. `Work.HypModel.uhsMetric`.

The link to the metric models (`Work.HypModel.uhsMetric`, `Work.HypModel.warpedMetric` and
`Work.Profiles.FillProfile`) is made in `Work.Cusp.ModelMetric`, so that this definition layer does
not depend on those areas.

## The strata

`coreStratum = {‖p‖∞ < 1/12}` (`r < 1/2`), `polarStratum = {1/24 < ‖p‖∞ ≤ 1}` (`r > 1/4`) and
`cuspStratum = {1/2 < ‖p‖∞ ≤ 1}` (`r_J < r`); they cover the square (`strata_cover`).  On the collar stratum `Θ_v` is the inverse of the UHS coordinates
(`ThetaOuter`), at `‖p‖∞ = 1` its height is the ceiling `β(x)` (so the layer `‖p‖∞ = 1` is the
truncation torus `T_v`, i.e. `τ_v`), and at `‖p‖∞ = ½` the polar and UHS coordinates agree through
`polarToUHS` at the junction `s_J = e^{R₀−r_J}`.

## The charts

`coreChart v`, `polarChart v` and `cuspChart v c δ` are the `OpenPartialHomeomorph`s
`E4 → W_v` whose `toFun` are the explicit inverses `cuspInvCore`, `cuspInvInner` and
`cuspInvOuter` of `Work.Cusp.Basic`; a chart on `M̂` is obtained from them by composing with the
open inclusion `W_v ∖ (∂Sq × (ℝ/ℤ)²) → M̂` of the assembly area.

## How the assembly area uses this file

The charts are defined on the **cover** `E2 × E2` of the filling piece: `z = (p, y)` with `p` the
layer parameter in the square and `y` the *real* pair of cusp coordinates (the projection to
`(ℝ/ℤ)²` is the local homeomorphism `E2 → W_v`; the maps below are equivariant under `y ↦ y + m`,
`m ∈ ℤ²`, by `ThetaOuter_add_int`, `ThetaPolar_add_int`, `ThetaCore_add_int`).  To get a chart on
`M̂`:

1. take a small open box `B` of the chart's target coordinate space and the corresponding open
   source `polarSourceS v c k B` (or `coreSource`, or `{z | z.1 ∈ wedge k ∧ Θ ∈ cuspBoxInterior}`);
2. compose with the projection of the cover onto `W_v ∖ (∂Sq × (ℝ/ℤ)²)` and with the open
   embedding of (the interior of) `W_v` into `M̂` given by the adjunction \(\sim_3\).

The three chart families and their model metrics are

| chart | source (cover) | target | model metric |
|---|---|---|---|
| `exists_coreChart` | `coreSource v` | `coreBox` | flat: `warpedMetric (fun r => r) (fun _ => P.h₀)` |
| `exists_polarChartS` | `polarSourceS v c k B` | `polarTargetS v c k B` | `warpedMetric P.f P.h` |
| `exists_cuspChart` | `{z | z.1 ∈ wedge k ∧ Θ ∈ cuspBoxInterior}` | `cuspTargetI v c δ k` | `uhsMetric` |

with `P : Work.Profiles.FillProfile` the profile of the area `PROF` (the link to those metric
models is made in the `CURV` area; this file only fixes the coordinates).

## The cover theorem

`strata_cover` covers the filling piece.  For `M̂`: every point of the hyperbolic piece which is not
on a truncation torus lies in a fold chart (area `FOLD`), every point of a truncation torus is a
point of the layer `‖p‖∞ = 1` of a filling piece (the gluing), every point of the collar layer
`‖p‖∞ ∈ (1/2,1]` is in a `cuspChart` and every point with `‖p‖∞ ≤ 1/2` is in a `polarChart` or a
`coreChart`; see `Work.Cusp.strata_cover` and `Work.Cusp.collarHeight_mem`.
-/
import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace
open Function

/-- The horizontal part `x` of a UHS coordinate `q = (x,s)`. -/
def xOf (q : E4) : E3 := !₂[q 0, q 1, q 2]

/-! ### The open boxes: the targets of the coordinate-chart maps -/

/-- The target of the core chart: the disk of radius `1/2` in the Cartesian `(a,b)`-plane
(`r = √(a²+b²) < 1/2`, where the profile has `f = r`, `h = h₀`). -/
def coreBox : Set E4 := {q | Real.sqrt (q 0 ^ 2 + q 1 ^ 2) < 1/2}

/-- The target of the polar chart: the annulus `1/4 < r < r_J + 1` in polar coordinates
`(r,θ,w₁,w₂)`.  The extra margin past `r_J = 3` covers the collar, where the same coordinates are
the UHS coordinates of the cusp chart through `polarToUHS`; this is the overlap of the two charts. -/
def polarBox : Set E4 := {q | 1/4 < q 0 ∧ q 0 < rJ + 1}

/-- The target of the cusp chart: an open box in `ℝ³ × ℝ` of side `2δ` in `x`, centred at `c`, with
the height in `(s₁, s_J)`.  Blueprint §1 takes `δ < 1/2` (so that the box meets few cubes) and the
box is required to lie in the slab `0 ≤ outerU v x < 1` of the `σ`-direction (so that the
perimeter coordinate of `x` is the representative in `[0,1)`). -/
def cuspBox (v : Fin 5) (c : E3) (δ : ℝ) : Set E4 :=
  {q | (∀ i, |xOf q i - c i| < δ) ∧ s1 < q 3 ∧ q 3 < sJ ∧
    0 ≤ outerU v (xOf q) ∧ outerU v (xOf q) < 1}

/-- The part of the box which lies in the filling piece, i.e. on or above the ceiling `s = β(x)`
(the part below is the chimney of `M̄`, and it is what makes the cusp chart cross the gluing).
This set is closed at the ceiling, so it is *not* open in `E4`; the open source of the collar chart
is `cuspBoxInterior` below. -/
def cuspSource (v : Fin 5) (c : E3) (δ : ℝ) : Set E4 :=
  {q | q ∈ cuspBox v c δ ∧ beta (xOf q) ≤ q 3}

/-- The **open** part of the box: strictly inside the box, strictly above the ceiling and strictly
inside the slab `0 < outerU v x < 1`.  This is the source of the collar chart `cuspChart` on the
filling piece (all its conditions are strict, and `beta`, `outerU` and the coordinates are
continuous).  The boundary pieces it omits are the gluing strata (`s = β`, `outerU = 0`), which are
covered by the charts of the adjacent cubes. -/
def cuspBoxInterior (v : Fin 5) (c : E3) (δ : ℝ) : Set E4 :=
  {q | (∀ i, |xOf q i - c i| < δ) ∧ s1 < q 3 ∧ q 3 < sJ ∧
    0 < outerU v (xOf q) ∧ outerU v (xOf q) < 1 ∧ beta (xOf q) < q 3}

/-- **The perimeter lift with the cut moved to `c`.**  `uS c p = c + frac (u p − c)` is the unique
lift of the circle-valued perimeter parameter `u` taking values in `[c, c+1)`; its jumps are at the
single direction on which `u p = frac c` (for `c = 0`: the ray through the vertex `(1,1)`).  On the
arcs where the lift is continuous it is the angle coordinate of the `c`-shifted polar chart
`ThetaPolarS`. -/
def uS (c : ℝ) (p : E2) : ℝ := c + Int.fract (u p - c)

/-- The `k`-th wedge of the `c`-shifted family: the directions whose perimeter parameter, measured
from the shifted cut, lies in `(k/4, (k+1)/4)`.  Each such wedge is an open arc of directions on
which the lift `uS c` is continuous, and the four wedges miss exactly the four directions
`frac c + k/4`. -/
def wedgeS (c : ℝ) (k : Fin 4) : Set E2 :=
  {p | 0 < nrm p ∧ Int.fract (u p - c) ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4)}

/-- The `k`-th wedge of the unshifted family; definitionally `wedgeS 0 k` (because `u p ∈ [0,1)`
off the origin), with `Int.fract (u p) = u p`. -/
def wedge (k : Fin 4) : Set E2 :=
  {p | 0 < nrm p ∧ u p ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4)}

/-! ### The charts as open partial homeomorphisms of the `(p,y)`-cover of the filling piece

The chart maps `ThetaOuter`, `ThetaPolar` and `ThetaCore` are equivariant under the torus
translations `y ↦ y + m` (`m : Fin 2 → ℤ`), by a lattice translation in the UHS chart and by a
rotation of the `(a,b)`-plane plus a translation of `w` in the inner charts.  They therefore live on
the *cover* `E2 × E2` of the filling piece (i.e. `(p,y)` with `y` a real pair); a chart of `W_v` (and
so of `M̂`) is obtained by restricting to an open set on which the projection to `(ℝ/ℤ)²` is
injective, which is the business of the assembly area.  The sources below are small open sets of the
cover already, and the targets are open boxes of `E4`. -/

/-- The perimeter coordinate recovered from the polar coordinates `q = (r,θ,w₁,w₂)`: `y` from `w`,
then `u = (θ − 2π⟪y,σ⟫/‖σ‖²)/(2π)`. -/
def uqOf (v : Fin 5) (q : E4) : ℝ :=
  (q 1 - 2 * π * inner ℝ (cuspY v (invY v !₂[q 2, q 3])) (slope v) / ‖slope v‖ ^ 2) / (2 * π)

/-- The layer parameter `‖p‖∞` recovered from the UHS coordinates `q = (x,s)`. -/
def nrmOf (v : Fin 5) (q : E4) : ℝ := nrm (cuspInvOuter v q).1

/-- **The `c`-shifted polar chart map.**  It is the polar chart `ThetaPolar` with the angle
coordinate read off the lift `uS c`; the two differ by `2π` on the arc where `u p < c`, so they
describe the *same* point of the filling piece, but the shifted version is continuous on the
`c`-shifted wedges, where the unshifted one jumps. -/
def ThetaPolarS (v : Fin 5) (c : ℝ) (p y : E2) : E4 :=
  !₂[radial v p y, 2 * π * uS c p + 2 * π * inner ℝ (cuspY v y) (slope v) / ‖slope v‖ ^ 2,
    wOf v y 0, wOf v y 1]

/-- The source of the `(c,k)`-th polar chart: the points of the cover whose layer parameter is
`> 1/24` (`r > 1/4`), whose direction lies in the `(c,k)`-wedge, and whose polar coordinates lie in
`B`.  It is open in the cover, and `ThetaPolarS v c` is continuous and injective on it. -/
def polarSourceS (v : Fin 5) (c : ℝ) (k : Fin 4) (B : Set E4) : Set (E2 × E2) :=
  {z | z.1 ∈ wedgeS c k ∧ 1/24 < nrm z.1 ∧ ThetaPolarS v c z.1 z.2 ∈ B}

/-- The target of the `(c,k)`-th polar chart: the points `q` of `B` whose recovered perimeter lift
`uqOf v q` lies in the wedge, i.e. `uqOf v q − c ∈ [0,1)` with fractional part in
`(k/4, (k+1)/4)`.  This is an open condition on `q`. -/
def polarTargetS (v : Fin 5) (c : ℝ) (k : Fin 4) (B : Set E4) : Set E4 :=
  {q | q ∈ B ∧ uqOf v q - c ∈ Set.Ico 0 1 ∧
    Int.fract (uqOf v q - c) ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4)}

/-- The source of the `k`-th (unshifted) polar chart. -/
def polarSource (v : Fin 5) (k : Fin 4) (B : Set E4) : Set (E2 × E2) := polarSourceS v 0 k B

/-- The target of the `k`-th (unshifted) polar chart. -/
def polarTarget (v : Fin 5) (k : Fin 4) (B : Set E4) : Set E4 := polarTargetS v 0 k B

/-- The source of the core chart: the points of the cover whose Cartesian core coordinates lie in
`coreBox`. -/
def coreSource (v : Fin 5) : Set (E2 × E2) := {z | ThetaCore v z.1 z.2 ∈ coreBox}

/-- The source of the cusp chart with box `cuspBox v c δ`: the points of the cover whose UHS
coordinates lie in the box.  It crosses the ceiling `s = β(x)`: the part below is the chimney of
`M̄`, the part above is the collar of the filling piece. -/
def cuspSourceOf (v : Fin 5) (c : E3) (δ : ℝ) : Set (E2 × E2) :=
  {z | ThetaOuter v z.1 z.2 ∈ cuspBox v c δ}

/-- The target of the cusp chart with box `cuspBox v c δ`: the box, cut down to the collar
(`‖p‖∞ > 1/2`, which is automatic from the height being `< s_J`). -/
def cuspTargetOf (v : Fin 5) (c : E3) (δ : ℝ) : Set E4 :=
  {q | q ∈ cuspBox v c δ ∧ 1/2 < nrmOf v q}

/-- The target of the collar chart `cuspChart v c δ k`: the open box interior, cut down to the
points whose recovered layer direction lies in the `k`-th wedge (the chart is continuous there). -/
def cuspTargetI (v : Fin 5) (c : E3) (δ : ℝ) (k : Fin 4) : Set E4 :=
  {q | q ∈ cuspBoxInterior v c δ ∧ (cuspInvOuter v q).1 ∈ wedge k}

end Work.Cusp

/-
# The cusp geometry of the Dehn filling: definition layer

This is the *definition* file of the chapter `Work.Cusp`: the cusp model of the Dehn filling of the
Ratcliffe–Tschantz hyperbolic 4-manifold `M̄`, in the upper half space coordinates of blueprint §1.

## The picture

Each of the five cusps of `M̄` is a flat 3-torus `T_v = ℝ³/Λ_v`, developed in the upper half space
model `UHS = {(x,s) : x ∈ ℝ³, s > 0}` (the hyperbolic models of the area `Work.HypModel`; this
file only needs the coordinates, and the metric link is made in `Work.Cusp.ModelMetric`).  The ideal vertices of the 24-cell `Q` become
`∞` in the UHS; the walls through the root vertex become the faces of a **unit cube**, and the cubes
of one cusp tile `ℝ³` periodically under `Λ_v ⊂ ℤ³` (index 4 for cusps 1–4, 32 for cusp 5).

* `Sq = [-1,1]²` is the filling disk `D²` (blueprint: `p ∈ [-1,1]²`, `‖p‖∞` its sup norm,
  `u(p)` the piecewise-linear perimeter parameter of the ray through `p`).
* `beta x` is the **ceiling**: over the unit cube with centre `c` the truncation face of `Q̄` is the
  hemisphere `s = √(ρ² − ‖x‖²)` with `ρ² = 9/4`; the data shows that every cube of every cusp has
  centre `corner + (½,½,½)` and `ρ² = 9/4`, so `β` is the `ℤ³`-periodic function below.  `β` is the
  height at which the filling torus `∂W_v` is glued to the truncation torus `T_v`.
* `slope v` is `σ_v = κ_{v,1} + b_v κ_{v,2} + c_v κ_{v,3}` (the meridian, with `c_v = 0`), and
  `lam2 v = κ_{v,2}`, `lam3 v = κ_{v,3}` complete `(σ_v, κ_{v,2}, κ_{v,3})` to a basis of `Λ_v`.
* `ThetaOuter v p y` is the **outer** chart of blueprint §1 (the collar, `½ ≤ ‖p‖∞ ≤ 1`, in UHS
  coordinates `(x, s)` with `x = u(p)σ_v + y` and `s = β(x)^{2‖p‖∞−1} s_J^{2−2‖p‖∞} ∈ [β(x), s_J]`);
  at `‖p‖∞ = 1` it is the ceiling `s = β(x)`, i.e. `τ_v`.
* `ThetaPolar v p y` and `ThetaCore v p y` are the **inner** charts (`‖p‖∞ ≤ ½`): polar coordinates
  `(r,θ,w₁,w₂)` with `r = 2 r_J ‖p‖∞`, `θ = 2πu(p) + 2π⟪y,σ⟫/‖σ‖²`, and `w` the
  `σ^⊥`-components of `y` in the orthonormal frame `(frame2, frame3)`; at `‖p‖∞ = ½` the polar
  coordinates are the UHS coordinates of the outer chart at the junction `s_J = e^{R₀−r_J}`.
* `polarToUHS v` is the isometry `(r,θ,w₁,w₂) ↦ (x,s)` with `x = (‖σ‖/2π)θ·frame1 + w₁ frame2 +
  w₂ frame3` and `s = e^{R₀−r}`, turning the warped metric `dr² + (Ce^r)²dθ² + (De^r)²|dw|²`
  (and the flat metric in the core, where `f = r`, `h = h₀`) into the UHS metric.

All the geometric content is in the modules next to this one; here we only fix the conventions.
-/
import Mathlib
import Submission.Work.Cusp.Data

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

/-! ### The three coordinate spaces -/

/-- The square `[-1,1]²`: the filling disk `D²`. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The UHS horizontal space `ℝ³` (cusp coordinates, cube coordinates). -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The chart target: UHS coordinates `(x, s)`, polar coordinates `(r,θ,w₁,w₂)`. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-! ### The parameters (blueprint §1, data file `Data.lean`) -/

/-- Klein truncation parameter `δ_K = 1/5` (blueprint §1). -/
def deltaK : ℝ := 1/5

/-- The scaling radius `R₀ = 7/2` with `s = e^{R₀−r}`. -/
def R0 : ℝ := 7/2

/-- The horotorus level `s₁ = 11/10` (constraint (iii): every other facet of `Q̄` has height
`< s₁ < min β`). -/
def s1 : ℝ := 11/10

/-- `r_J = 3`: the radial coordinate of the inner/outer junction. -/
def rJ : ℝ := 3

/-- `s_J = e^{R₀−r_J} = √e`: the height of the junction. -/
def sJ : ℝ := Real.exp (1/2)

/-- `sTop = 33/20`: the upper end of the height window `(s₁, sTop)` of the *unslabbed* collar
chart `cuspBoxTop`.  Its two defining properties are

* `sJ_lt_sTop : s_J = √e < sTop`, so that the window *contains the junction* `s = s_J` of the
  inner and outer charts (which the slabbed window `(s₁, s_J)` does not — this is the second of the
  two reasons the slabbed family cannot cover the collar);
* `sTop_sq_mul_betaMax_lt_sJ_cu : sTop² · β_max < s_J³`, i.e. `(33/20)²(3/2) = 3267/800 < e^{3/2}`,
  which — together with `sTop · β_max < s_J²` — bounds the layer parameter `t` recovered from a
  point of the collar box: it satisfies `1/4 < t ≤ 1` (`Work.Cusp.cuspInvOuter_nrm_Top`), so that
  the recovered point does not merely lie in the square `Sq` but in its collar
  `{1/4 < ‖·‖∞ ≤ 1}`, which is the domain of the layer chart `layerPtI`.

`33/20 = 1.65` is only slightly above `s_J ≈ 1.6487`, which is what makes both comparisons
comfortable with rational arithmetic (`e > 2.7182818283` and `√e > 8/5`). -/
def sTop : ℝ := 33/20

/-! ### The square, its sup norm and its perimeter parameter -/

/-- The square `[-1,1]²`. -/
def Sq : Set E2 := {p | |p 0| ≤ 1 ∧ |p 1| ≤ 1}

/-- The sup norm `‖p‖∞ = max(|p 0|, |p 1|)`; this is the layer parameter of the filling. -/
def nrm (p : E2) : ℝ := max |p 0| |p 1|

/-- The radial projection of `p` to `∂Sq`, i.e. `p / ‖p‖∞` (equal to `0` at `p = 0`), so that
`p = ‖p‖∞ • bnd p` for `p ∈ Sq`. -/
def bnd (p : E2) : E2 := (nrm p)⁻¹ • p

/-- The point of `∂Sq` with perimeter parameter `frac u`: the inverse of `uPerim` composed with the
fractional part, so that `bndOfU` is `1`-periodic and `uPerim (bndOfU u) = frac u`.
`(1,1)` is `u = 0` and the boundary is traversed counterclockwise. -/
def bndOfU (u : ℝ) : E2 :=
  let v := Int.fract u
  if v < 1/4 then !₂[1, 1 - 8 * v]
  else if v < 1/2 then !₂[3 - 8 * v, -1]
  else if v < 3/4 then !₂[-1, 8 * v - 5]
  else !₂[8 * v - 7, 1]

/-- The piecewise-linear perimeter parameter of a point of `∂Sq`, counterclockwise from `(1,1)`
and normalised to total length `1`.  Each edge has length `2`, so `u` increases by `1/8` per unit
of arclength. -/
def uPerim (q : E2) : ℝ :=
  if q 0 = 1 then (1 - q 1) / 8
  else if q 1 = -1 then (3 - q 0) / 8
  else if q 0 = -1 then (5 + q 1) / 8
  else (7 + q 0) / 8

/-- The perimeter parameter `u(p)` of the ray through `p`, `p ∈ Sq` (blueprint §1). -/
def u (p : E2) : ℝ := uPerim (bnd p)

/-- The real vector of an integer triple. -/
def ofInt3 (m : Fin 3 → ℤ) : E3 := !₂[(m 0 : ℝ), (m 1 : ℝ), (m 2 : ℝ)]

/-- The real vector of an integer pair. -/
def ofInt2 (m : Fin 2 → ℤ) : E2 := !₂[(m 0 : ℝ), (m 1 : ℝ)]

/-! ### The ceiling `β` -/

/-- `½ − |frac t − ½|`: the distance of `t` to the nearest half-integer, i.e. the `i`-th coordinate
offset of a point from the centre of the unit cube it lies in. -/
def off (t : ℝ) : ℝ := 1/2 - |Int.fract t - 1/2|

/-- **The ceiling function `β`.**  Over the unit cube with centre `c` the truncation face is the
hemisphere `s = √(9/4 − ‖x−c‖²)`; `x` lies in the unit cube with centre `frac(x) − ½`, so this is a
single `ℤ³`-periodic formula.  Its range is `[√(3/2), 3/2]`. -/
def beta (x : E3) : ℝ := Real.sqrt (9/4 - ∑ i, (off (x i)) ^ 2)

/-- The largest possible ceiling height, `max β = 3/2`. -/
def betaMax : ℝ := 3/2

/-- The smallest possible ceiling height, `min β = √(3/2)`. -/
def betaMin : ℝ := Real.sqrt (3/2)

/-! ### The cusp lattices and the slopes -/

/-- The `i`-th lattice vector `κ_{v,i} ∈ ℤ³ ⊂ ℝ³` of the `v`-th cusp (`i = 0,1,2` for
`κ_{v,1}, κ_{v,2}, κ_{v,3}`); the three are orthogonal. -/
def kv (v : Fin 5) (i : Fin 3) : E3 :=
  !₂[(kappa v i 0 : ℝ), (kappa v i 1 : ℝ), (kappa v i 2 : ℝ)]

/-- `λ₂ = κ_{v,2}`: the second cusp coordinate direction. -/
def lam2 (v : Fin 5) : E3 := kv v 1

/-- `λ₃ = κ_{v,3}`: the third cusp coordinate direction. -/
def lam3 (v : Fin 5) : E3 := kv v 2

/-- **The slope** `σ_v = κ_{v,1} + b_v κ_{v,2} + c_v κ_{v,3}` (the meridian of the filling, which
bounds the disk `D²`).  With `c_v = 0` it lies in the coordinate plane of `κ_{v,1}, κ_{v,2}`. -/
def slope (v : Fin 5) : E3 := kv v 0 + (slopeB v : ℝ) • kv v 1 + (slopeC v : ℝ) • kv v 2

/-- The `y`-part `y₂λ₂ + y₃λ₃` of a cusp coordinate `x = uσ + y`. -/
def cuspY (v : Fin 5) (y : E2) : E3 := y 0 • lam2 v + y 1 • lam3 v

/-- The cusp coordinate `x = uσ_v + y₂λ₂ + y₃λ₃` (`u` is the perimeter parameter; the σ-circle is
the meridian). -/
def cuspX (v : Fin 5) (u : ℝ) (y : E2) : E3 := u • slope v + cuspY v y

/-- The unit vector along the slope: `σ̂_v`. -/
def frame1 (v : Fin 5) : E3 := (‖slope v‖)⁻¹ • slope v

/-- `κ_{v,2}` projected to the plane orthogonal to `σ_v` (this is the `w₁` direction, in the
`κ₁κ₂`-plane). -/
def frame2aux (v : Fin 5) : E3 := lam2 v - ((⟪lam2 v, slope v⟫_ℝ / ‖slope v‖ ^ 2) • slope v)

/-- The second vector of the orthonormal frame `(σ̂_v, frame2, frame3)`: the unit vector along
`κ_{v,2} − proj_{σ}κ_{v,2}` (the `w₁` direction; `σ ⊥ κ_{v,3}` here). -/
def frame2 (v : Fin 5) : E3 := (‖frame2aux v‖)⁻¹ • frame2aux v

/-- The third vector of the orthonormal frame: `κ̂_{v,3}` (the `w₂` direction, orthogonal to
`σ_v`). -/
def frame3 (v : Fin 5) : E3 := (‖lam3 v‖)⁻¹ • lam3 v

/-- The coefficient of `κ_{v,i}` of `x` in the orthogonal basis `(κ_{v,1},κ_{v,2},κ_{v,3})`:
`⟪x,κ⟩/‖κ‖²`. -/
def kappaCoord (v : Fin 5) (i : Fin 3) (x : E3) : ℝ := ⟪x, kv v i⟫_ℝ / ‖kv v i‖ ^ 2

/-- `u` as a function of a cusp coordinate `x`: the `κ_{v,1}`-coordinate of `x`. -/
def outerU (v : Fin 5) (x : E3) : ℝ := kappaCoord v 0 x

/-- `y₂` as a function of a cusp coordinate `x`: the `κ_{v,2}`-coordinate minus `b_v u`. -/
def outerY (v : Fin 5) (x : E3) : E2 :=
  !₂[kappaCoord v 1 x - (slopeB v : ℝ) * outerU v x, kappaCoord v 2 x]

/-! ### The chart maps (blueprint §1) -/

/-- The height of the collar at layer parameter `t = ‖p‖∞` and ceiling `b = β(x)`:
`s = β^{2t−1} s_J^{2−2t}`, written with `exp`/`log` (equal to the power form for `b > 0`). -/
def collarHeight (t b : ℝ) : ℝ := Real.exp ((2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ)

/-- The UHS height of the collar at `(p,y)`: `s = β(x)^{2‖p‖∞−1} s_J^{2−2‖p‖∞}`, i.e. the height
coordinate of `ThetaOuter`. -/
def collarS (v : Fin 5) (p y : E2) : ℝ :=
  collarHeight (nrm p) (beta (cuspX v (u p) y))

/-- **The metric radial coordinate `r` of the filling.**  In the inner region (`‖p‖∞ ≤ 1/2`) the
warped metric is `dr² + f(r)²dθ² + h(r)²|dw|²` with `r = 2 r_J ‖p‖∞ ∈ [0, r_J]`; in the collar the
metric is hyperbolic, `s = e^{R₀−r}`, so `r = R₀ − log s` with `s` the UHS height `collarS`.  The two
branches agree at `‖p‖∞ = 1/2`, where both are `r_J = 3` (the junction `s_J = e^{R₀−r_J}`). -/
def radial (v : Fin 5) (p y : E2) : ℝ :=
  if nrm p ≤ 1/2 then 2 * rJ * nrm p else R0 - Real.log (collarS v p y)

/-- **`Θ_v`, outer part** (blueprint §1), in UHS coordinates `(x,s)`:
`x = u(p)σ_v + y` and `s = β(x)^{2‖p‖∞−1} s_J^{2−2‖p‖∞}`.  At `‖p‖∞ = 1` this is `(x, β(x))`, the
point `τ_v(x)` of the truncation torus; at `‖p‖∞ = ½` it is the junction `s = s_J`. -/
def ThetaOuter (v : Fin 5) (p y : E2) : E4 :=
  let x := cuspX v (u p) y
  !₂[x 0, x 1, x 2, collarS v p y]

/-- The angle coordinate of the inner charts:
`θ = 2πu(p) + 2π⟪y,σ_v⟫/‖σ_v‖²`. -/
def thetaAng (v : Fin 5) (p y : E2) : ℝ :=
  2 * π * u p + 2 * π * (⟪cuspY v y, slope v⟫_ℝ / ‖slope v‖ ^ 2)

/-- The `w`-coordinates `(⟪y, frame2⟫, ⟪y, frame3⟫)` of the `y`-part `y₂λ₂ + y₃λ₃` of a cusp
coordinate, in the orthonormal frame `(frame2, frame3)` of `σ^⊥`; this is the linear isomorphism
`invY` of `Basic`. -/
def wOf (v : Fin 5) (y : E2) : E2 :=
  !₂[⟪cuspY v y, frame2 v⟫_ℝ, ⟪cuspY v y, frame3 v⟫_ℝ]

/-- **`Θ_v`, inner part, polar coordinates** `(r,θ,w₁,w₂)` with `r = 2 r_J ‖p‖∞` and
`w = proj_{σ^⊥}(y₂λ₂+y₃λ₃)` in the orthonormal frame `(frame2, frame3)`. -/
def ThetaPolar (v : Fin 5) (p y : E2) : E4 :=
  !₂[radial v p y, thetaAng v p y, wOf v y 0, wOf v y 1]

/-- **`Θ_v`, inner part, Cartesian coordinates** `(a,b,w₁,w₂)` with `(a,b) = r(cos θ, sin θ)`: the
core chart, in which the metric is flat (`f = r`, `h = h₀` for `r ≤ 1/2`). -/
def ThetaCore (v : Fin 5) (p y : E2) : E4 :=
  let r := radial v p y
  let θ := thetaAng v p y
  !₂[r * Real.cos θ, r * Real.sin θ, wOf v y 0, wOf v y 1]

/-! ### The polar ↔ UHS coordinate change -/

/-- **The polar ↔ UHS isometry.**  `(r,θ,w₁,w₂) ↦ (x,s)` with
`x = (‖σ_v‖/2π) θ · σ̂_v + w₁ · frame2 + w₂ · frame3` and `s = e^{R₀−r}`.  It turns the warped
metric `dr² + f(r)²dθ² + h(r)²|dw|²` with `f = Ce^r`, `h = De^r`, `C = ‖σ‖e^{−R₀}/2π`,
`D = e^{−R₀}` into the UHS metric `(|dx|²+ds²)/s²`. -/
def polarToUHS (v : Fin 5) (q : E4) : E4 :=
  let x := (‖slope v‖ / (2 * π) * q 1) • frame1 v + q 2 • frame2 v + q 3 • frame3 v
  !₂[x 0, x 1, x 2, Real.exp (R0 - q 0)]

/-! ### The explicit inverses -/

/-- Recover `y` from `w = (⟪y,e₂⟫, ⟪y,e₃⟫)`: the inverse of the `2 × 2` system
`w = G y`, written with the adjugate and determinant of `G = (⟪λ_i, e_j⟫)`. -/
def invY (v : Fin 5) (w : E2) : E2 :=
  let g00 := ⟪lam2 v, frame2 v⟫_ℝ
  let g01 := ⟪lam3 v, frame2 v⟫_ℝ
  let g10 := ⟪lam2 v, frame3 v⟫_ℝ
  let g11 := ⟪lam3 v, frame3 v⟫_ℝ
  ((g00 * g11 - g01 * g10)⁻¹) •
    !₂[g11 * w 0 - g01 * w 1, -(g10 * w 0) + g00 * w 1]

/-- The determinant of the `w`-matrix `G = (⟪λ_i, e_j⟫)`; it is nonzero because `(σ, λ₂, λ₃)` is a
basis of `ℝ³`. -/
def wDet (v : Fin 5) : ℝ :=
  ⟪lam2 v, frame2 v⟫_ℝ * ⟪lam3 v, frame3 v⟫_ℝ
    - ⟪lam3 v, frame2 v⟫_ℝ * ⟪lam2 v, frame3 v⟫_ℝ

/-- **The inverse of the outer chart.**  Given UHS coordinates `q = (x,s)`, recover the layer
parameter `t` from `s = collarHeight t (β x)` and the angle from the `σ`-coordinate of `x`:
`(p,y) = (t • bndOfU(σ-coord of x), y(x))`. -/
def cuspInvOuter (v : Fin 5) (q : E4) : E2 × E2 :=
  let x : E3 := !₂[q 0, q 1, q 2]
  let b := beta x
  let t := 1 + (Real.log (q 3) - Real.log b) / (2 * (Real.log b - Real.log sJ))
  (t • bndOfU (outerU v x), outerY v x)

/-- **The inverse of the inner (polar) charts.**  Given `(r,θ,w₁,w₂)`, recover `y` from `w`, then
`u(p) = (θ − 2π⟪y,σ⟫/‖σ‖²)/2π` (the perimeter coordinate) and finally the layer parameter `t = ‖p‖∞`
from `r`: `t = r/2r_J` in the inner region (`r ≤ r_J`) and from `s = e^{R₀−r} = collarHeight t β(x)`
in the collar (`r ≥ r_J`); then `p = t • bndOfU u`. -/
def cuspInvInner (v : Fin 5) (q : E4) : E2 × E2 :=
  let y := invY v !₂[q 2, q 3]
  let uu := (q 1 - 2 * π * (⟪cuspY v y, slope v⟫_ℝ / ‖slope v‖ ^ 2)) / (2 * π)
  let b := beta (cuspX v uu y)
  let t := if q 0 ≤ rJ then q 0 / (2 * rJ)
    else 1 + (R0 - q 0 - Real.log b) / (2 * (Real.log b - Real.log sJ))
  (t • bndOfU uu, y)

/-- The argument of `(x,y) ∈ ℝ²`, i.e. `atan2 y x`, as the argument of the complex number
`x + iy`; we use it to invert the polar-to-Cartesian map `(r,θ) ↦ (r cos θ, r sin θ)` of the core
chart. -/
def argOf (y x : ℝ) : ℝ := Complex.arg ⟨x, y⟩

/-- **The inverse of the core chart** (Cartesian `(a,b,w₁,w₂)`): same as `cuspInvInner` with
`r = √(a²+b²)` and `θ = atan2 b a = argOf b a`. -/
def cuspInvCore (v : Fin 5) (q : E4) : E2 × E2 :=
  let r := Real.sqrt (q 0 ^ 2 + q 1 ^ 2)
  let θ := argOf (q 1) (q 0)
  cuspInvInner v !₂[r, θ, q 2, q 3]

/-! ### The layer strata of the filling piece -/

/-- The core stratum `r ≤ 1/2`, i.e. `‖p‖∞ ≤ 1/12`. -/
def coreStratum : Set E2 := {p | nrm p < 1/12}

/-- The polar stratum `r > 1/4`, i.e. `1/24 < ‖p‖∞ ≤ 1`: the source of the polar chart (the box
`1/4 < r < r_J + 1` covers the whole filling piece, since in the collar `r ∈ [r_J, R₀ − log β]`). -/
def polarStratum : Set E2 := {p | 1/24 < nrm p ∧ nrm p ≤ 1}

/-- The collar stratum `r_J < r`, i.e. `1/2 < ‖p‖∞ ≤ 1`: the part of the filling piece on which the
cusp chart is the (open) inverse of the UHS coordinates.  (The layer `r = r_J`, i.e. `‖p‖∞ = 1/2`,
is covered by `polarStratum`.) -/
def cuspStratum : Set E2 := {p | 1/2 < nrm p ∧ nrm p ≤ 1}

/-- The filling piece `W_v = [-1,1]² × (ℝ/ℤ)²`: the square of layer parameters and the two torus
coordinates `(y₂,y₃)`. -/
abbrev W := {p : E2 // p ∈ Sq} × (Fin 2 → AddCircle (1 : ℝ))

/-! ### The cusp torus `ℝ³/Λ_v` and `τ_v` -/

/-- The cusp lattice `Λ_v ⊂ ℝ³`, generated (over `ℝ`, i.e. as a subgroup) by the orthogonal basis
`κ_{v,1}, κ_{v,2}, κ_{v,3}`. -/
def lattice (v : Fin 5) : AddSubgroup E3 := AddSubgroup.closure (Set.range (kv v))

/-- The cusp torus `T³_v = ℝ³/Λ_v` (the underlying space of the truncation torus `T_v ⊂ M̄`), in
UHS cube coordinates. -/
abbrev CuspTorus (v : Fin 5) : Type := E3 ⧸ lattice v

/-- The point of the truncation torus with cusp coordinate `x`: in UHS coordinates it is
`(x, β x)`.  Blueprint §1: `τ_v(x) = x_a^{-1}(x)`. -/
def tauCoord (v : Fin 5) (x : E3) : E3 × ℝ := (x, beta x)

/-! ### The lifted maps on the phase torus `(ℝ/ℤ)²` -/

/-- The outer chart with the torus coordinates `(y₂,y₃) ∈ (ℝ/ℤ)²` (the phase variables of `W_v`).
It is the lift of `ThetaOuter v p` along `ℝ² → (ℝ/ℤ)²` (which changes the point by a lattice
translation, see `ThetaOuter_add_int`). -/
def ThetaOuterT (v : Fin 5) (p : E2) (y : Fin 2 → AddCircle (1 : ℝ)) : E4 :=
  AddCircle.liftIco 1 0
    (fun y₀ => AddCircle.liftIco 1 0 (fun y₁ => ThetaOuter v p !₂[y₀, y₁]) (y 1)) (y 0)

/-- The polar chart with torus coordinates. -/
def ThetaPolarT (v : Fin 5) (p : E2) (y : Fin 2 → AddCircle (1 : ℝ)) : E4 :=
  AddCircle.liftIco 1 0
    (fun y₀ => AddCircle.liftIco 1 0 (fun y₁ => ThetaPolar v p !₂[y₀, y₁]) (y 1)) (y 0)

/-- The core chart with torus coordinates. -/
def ThetaCoreT (v : Fin 5) (p : E2) (y : Fin 2 → AddCircle (1 : ℝ)) : E4 :=
  AddCircle.liftIco 1 0
    (fun y₀ => AddCircle.liftIco 1 0 (fun y₁ => ThetaCore v p !₂[y₀, y₁]) (y 1)) (y 0)

end Work.Cusp

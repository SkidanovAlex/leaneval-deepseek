import Mathlib
import Submission.ConjEnergy
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.gp_ode_compare
import Submission.GExpRayVelocity
import Submission.HopfRinow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.GlobalExp Submission.Geodesic

/-!
## STATUS / NOTE for the next session (agent on `Work.Diff.C.dip_model_through`)

PROVED in this file (sorry-free):

* `ode_compare_value_aux` — the scalar Sturm comparison for the *values*: if `φ` is twice
  differentiable on `[0,s]` with `|φ'' + φ| ≤ ε` then
  `|φ s - (φ 0 cos s + φ' 0 sin s)| ≤ ε s` (copied from `Diff/C/ray_cos_compare`, which cannot be
  imported here: see the TRAP below);
* `ode_compare_deriv_aux` — the companion estimate for the *derivatives*:
  `|φ' s - (φ' 0 cos s - φ 0 sin s)| ≤ ε s`;
* `value_off_cap` — **the target's value conjunct in the region where the ray from `p` stays out of
  the antipodal cap of `q`** (`∀ σ ∈ [0,s], fcos q (γ σ) > -1+c`): proved from the already-ported
  ray comparison `Work.Diff.C.gp_ode_compare` (`Diff/C/gp_ode_compare`);
* `gp_ode_compare_deriv` — the *derivative* companion of `gp_ode_compare` (ported here, sorry-free):
  for a smooth `f`, a unit `u` and `|rhess f + f·g| ≤ ε` along the ray,
  `|⟪∇f(x), γ'(s)⟫ - (⟪∇f(q),u⟫ cos s - f(q) sin s)| ≤ ε s`; the velocity identification uses
  `Submission.GExpRayVelocity.curveVelocity_GExp_eq_of_isGeodesicAt`;
* `deriv_off_cap` — **the target's derivative conjunct off the cap**, from `gp_ode_compare_deriv`
  and `InitData`.

* `sin_model_lipschitz` — `σ ↦ β sin σ` is 1-Lipschitz for `|β| ≤ 1`;
* `dip_interval_bound` — **the arithmetic bridge**: `|F s - M s| ≤ (1 + sin δ)|s-a| + ε` from the
  model comparison at the first dip time `a`, the `sin δ`-Lipschitz bound for `F` on the dip, and the
  1-Lipschitz bound for `M`;
* `value_dip_case` — **the target's value conjunct in the dip case**, with the *location* of the dip
  (`halow : a ≥ π/2-δ` elementary, `haK`, `hsK` from `Work.Diff.C.dip_exit_time`) and the two bridge
  inputs (`hcmp` at `a`, `hlip` on `[a,s]`) as hypotheses.  Everything else (the numerics, `δ ≤ α`,
  `|β| ≤ 1`) is discharged inside.

**The crux is now reachable**: `Submission/Work/Diff/C/dip_far_ball.lean` (in flight; its imports
`far_ball_excess`/`far_sphere_size` each still carry one `sorry`) proves the far-ball diameter bound
`rdist z z' ≤ 256(√c + ε₁π)` for `z,z'` with `rdist q z, rdist q z' ≥ π-δ`.  That is the
cap-diameter input, and combined with the *elementary* entry bound (`a ≥ π/2-δ`, triangle
inequality) and the ray-length identity it gives the location bound `σ ≤ a + 256(√c+ε₁π)`;
`dip_far_ball` cannot be imported from this file (`dip_far_ball` → `ray_cos_compare` and `init_data`
both declare `Work.Diff.C.inner_rgrad_mvfderiv'`), so the wiring must happen in a module that does
not import `init_data` (e.g. `dip_cap_exit.lean`, which imports only `Setup`).

So of the target, what remains is exactly the *dip*: the value and the derivative conjuncts on
`[0,s]` in the case where some `σ` has `fcos q (γ σ) ≤ -1+c`, i.e. `Work.Diff.C.dip_exit_time`.  The
bridge from `dip_exit_time` to the target is the crude interval argument (below), which is
elementary: if `a` is the first dip time then `F a = -1+c`, `|F σ - F a| ≤ sin δ · |σ-a|`,
`|M a - M σ| ≤ |σ - a|` with `M σ = β sin σ`, and `|M a - (-1+c)| ≤ ε₁ a`.

These two, together with `hHess` (the Hessian bound `|Hess (fcos q) + fcos q · g| ≤ ε₁ g` on the
region `fcos q > -1+c`) and `hsmC` (smoothness there), give the model comparison for
`F σ := fFam … (Fin.succ k) (GExp p (σ • u))` along the ray `γ σ = GExp p (σ • u)` **as long as the
ray stays in the good region** `fcos q (γ σ) > -1+c` on `[0,s]`: then
`|F s - β sin s| ≤ ε₁ s` and `|F' s - β cos s| ≤ ε₁ s` (`F' s = ⟪∇fcos q (γ s), γ'(s)⟫`).
Note `γ` is minimising on `[0,s]` (`hray`), so `rdist p (γ σ) = σ` there, and `fcos p ∘ γ = cos`.

WHAT IS MISSING (the crux — do not lose time rediscovering it): the *dip*.  Write
`L σ := rdist q (γ σ)`, so `F σ = cos (L σ)`.  On the good region the ODE gives `F'' = -F + E`,
`|E| ≤ ε₁`; but the hypothesis `hHess` for the centre `q` is only available where `L σ < π-δ`,
`δ = arccos (1-c)`.  In the "dip" `F σ ≤ -1+c` (i.e. `L σ ≥ π-δ`) one has, from the prefix comparison
at the first dip time `a`: `|β| sin a = 1-c+O(ε₁)`, hence `|β| ≥ 1-c-O(ε₁)` and
`a ∈ [π/2-δ-O(ε₁), π/2+δ+O(ε₁)]`, and the elementary triangle inequality gives the *lower* bound
`σ ≥ π/2 - δ` for every dip time.  What is needed is the matching **upper** bound
`σ ≤ π/2 + O(√c + ε₁π + α)`, i.e. that the ray from `p` leaves the antipodal cap of `q`
(`{y : d(q,y) ≥ π-δ}`) by time `π/2 + O(√c)`.  Equivalently: the cap `{y : d(q,y) ≥ π-δ}` has
diameter `≤ 2δ + O(ε₁)` — a *boundary* case of Toponogov's hinge comparison in the configuration
`d(p,q) = π/2`, `d(p,γσ) = σ ≈ π/2`, `β ≤ -cos α`.

The documented ROUTE inside the target's docstring ("the set `{h ≤ -1+c}` is at most an isolated set
of tangency points") is **false**: for the model `β sin σ` (with `β ≤ -cos α`) the dip is the
*interval* `{σ : |β| sin σ ≥ 1-c}` of length `2δ > 0`, and along the round sphere the same is true for
the function itself.  So the dip cannot be crossed by "integrating through tangency points".

TOOLS in the workspace (all sorry-free): `Submission/HingeCompare.lean`
(`hinge_of_cos_second_deriv`, `hinge_comparison_dist`, `hinge_of_cot_bound`: Toponogov's hinge
comparison *reduced to a Hessian bound on `cos ∘ ρ`*) — this is the right interface to feed `hHess`;
`Submission/HingePiece.lean` (`gcompHolds_pi_apply`, needs `QuarterPinched`), `Submission/GSBall`,
`GSConcave`, `GSConcaveSeg`, `GSCritical` (the Grove–Shihama machinery, all for the *other* pinching
direction `K ≤ 1`); `Submission/Work/Diff/C/ray_cos_compare.lean`'s `ode_compare` (copied here as
`ode_compare_value_aux`).  Everything in the library that does the *concave/thin* side of the
comparison (`sec ≥ 1`, "third side ≤ model") is only available *under* a pinching hypothesis, and the
strict inequality `l₁ + l₂ < π` of the classical hinge theorem fails in this configuration
(legs `π/2` and `s ≈ π/2`).  Deriving the pinching `sec ≈ 1` from `hHess` (which is what would make
the library tools applicable) is the remaining "missing chapter": `hHess` does determine the shape
operator of the geodesic spheres of radius `π/2` around every centre with error `ε₁`, hence the
sectional curvature at scale `1` with error `O(ε₁)`.

TRAP: `Submission/Work/Diff/C/ray_cos_compare.lean` and `Submission/Work/Diff/C/init_data.lean` both
declare `Work.Diff.C.inner_rgrad_mvfderiv'`; consequently **no module may import both** (Lean:
"already been declared").

More precisely (checked): this file's import closure contains `ray_cos_compare` (via
`gp_ode_compare`/`FarKit`) but **must never contain `init_data`**, because the colleague's proved
module `far_ball_excess` imports *both* this file and `far_sphere_size` (⟹ `ray_cos_compare`); if
one made this file import `init_data`, `far_ball_excess` would stop compiling.  So any lemma of
`rgrad_fcos_eikonal.lean` (`eik_abs_cos_sub_cos_le`, `eik_abs_mvfderiv_fcos_le`, …) must be **copied**
here rather than imported; that is what `dmAux_abs_cos_sub_cos_le` / `dm_abs_mvfderiv_fcos_le` below
do.  (Also: `open`/`open scoped` at the top of the file are scoped to the first `namespace … end`
block, so the new lemmas carry explicit `open … in` prefixes.)

---

## STATUS (session N+3): the target is reduced to ONE geometric input

PROVED in this file (sorry-free): everything listed above plus

* `dmAux_abs_cos_sub_cos_le` — copy of `eik_abs_cos_sub_cos_le` (see TRAP);
* `dm_abs_mvfderiv_fcos_le` — **the `MDifferentiableAt` version of `eik_abs_mvfderiv_fcos_le`**:
  `|mvfderiv I (fcos q) x v| ≤ |sin (rdist q x)|·‖v‖` for **all** `x, v`, with no smoothness
  hypothesis at `x` (the junk case `¬ MDifferentiableAt` gives `mvfderiv = 0`).  This bounds the
  *derivative* conjunct at a dip point.

### The reduction

Write `F σ := fFam … (Fin.succ k) (GExp p (σ • u)) = fcos q (γ σ)`, `β := ⟪e k, u⟫`, `q` the `qpt`,
`γ σ = GExp p (σ • u)`, `x = γ s`, `L := rdist q x`.

* **Case A (no dip: `∀σ∈[0,s], F σ > -1+c`)**: `value_off_cap` + `deriv_off_cap` give both conjuncts
  with error `ε₁ s ≤ ε₁ π`.  DONE.
* **Case B (some dip)**: with `a` the first dip time (`dip_first_compare`), `F a = -1+c`,
  `|F a - β sin a| ≤ ε₁ a`, hence `|β| sin a ≥ 1-c-ε₁π`, `|a - π/2| ≤ arccos(1-c-ε₁π) + O(ε₁) =: w`,
  `w ≤ 2δ + 3ε₁π` (uses `|β| ≤ 1`, `hnum1`).  Two sub-cases:
  * **B1 (`F s ≤ -1+c`)**: the tip is in the dip, `L ∈ [π-δ, π+δ]` (`dipAux_lip`'s `hmem`) and
    `s ≥ L - π/2 ≥ π/2 - δ` (triangle).
    - *value*: `cos L - β sin s ≤ (-1+c) + |β| sin s ≤ c` (trivial upper bound); the lower bound
      needs `sin s ≥ 1 - O(C)`, i.e. `s ≤ π/2 + O(√C)`.
    - *derivative*: `|⟪rgrad (fcos q) x, γ'(s)⟫| ≤ sin δ ≤ √(2c)` (`dm_abs_mvfderiv_fcos_le`, from
      `L ∈ [π-δ,π+δ]`) and `|β cos s| ≤ |cos s|` — so the *derivative* conjunct follows from the
      *value* statement `|cos s| ≤ O(√c)`.
  * **B2 (`F s > -1+c`, a dip earlier)**: the ray leaves the dip at `b < s` (`F b = -1+c`,
    `F > -1+c` on `(b,s]`); restarting the model comparison at `b` gives both conjuncts **provided**
    the data at `b` are known: `|F b - β sin b| ≤ C₁`, `|F'(b) - β cos b| ≤ C₂`.  Both reduce to the
    *dip length* `|b - a| ≤ η`: `C₁ ≤ ε₁π + (1+√(2c))η`, `C₂ ≤ √(2c) + η + w`
    (`|F'(b)| ≤ sin δ` by `dm_abs_mvfderiv_fcos_le` since `F b = -1+c` makes `fcos q` smooth at
    `γ b`, and `|cos b| ≤ |b - π/2| ≤ η + w`).
  * Hence **BOTH dip sub-cases reduce to** `dip_loc : σ ≤ π/2 + η` for every dip time `σ`, with
    `2η + ε₁π ≤ 100(n+2)(ε₁π+α+√c)`: then `dip_interval_bound` (restated with the location
    hypothesis) finishes B1 and the restart finishes B2.  Any `η ≲ 20√c + 20ε₁π` works.

### The routes to `dip_loc` and their blockers (all checked)

1. **Cap diameter** (the previous session's route): `dip_first_compare` at `a` plus
   `|s - a| ≤ diam{rdist q · ≥ π-δ}`, the latter being `2δ + 2arcsin(2ε₁) + (sphere size)` with the
   sphere size `π(π-δ)sin(π-δ) + Cε₁π ≈ 14√c + Cε₁π` (`Work.Diff.C.far_sphere_size`).
   **Blocker**: `far_sphere_size` is unproved (one `sorry`, the fleet's file), and its intended
   Jacobi/modulus route (`Work.Diff.C.jld_modulus_le_sin`, PROVED) needs the bridge
   `⟪∇_{γ'}Z, Z⟫ = rhess (rdist q)(γ t)(Z, Z)` for the variation field `Z`, available only under
   `hminW : ∀ w, ∀ᶠ σ, edist q (GExp q ((d•u) + σ•w)) = ofReal ‖…‖` ("the nearby rays are
   minimising").  `hminW` is the cut-locus statement "`rdist q` smooth at `x` `⟹` `x` is not a cut
   point of `q`"; its classical proof splits into (a) *two minimising geodesics* (elementary
   "shortcut": points just beyond `x` along one of them are closer to `q`, so the directional
   derivative of `d_q` jumps) and (b) *a conjugate point* (`mfderiv (GExp q) (ρu)` singular), where
   one must show that `d_q` fails to be `C¹` at `x` — e.g. "`d_q` smooth near `x` ⟹ flow lines of
   `∇d_q` are geodesics (eikonal + symmetry of the Hessian) ⟹ `GExp q` is a local diffeo at `ρu`".
   Available tools: `Submission.CutStep3.exists_two_minimising_or_not_locallyInjective`,
   `Work.Diff.C.eik_v2_localInverse_GExp`, `Work.Diff.C.eik_v2_rdist_eq_norm` (which needs
   `InjAtLeast hmet q ρ` with `ρ > rdist q x` — equivalent to the missing input),
   `Work.Diff.C.rgrad_rdist_eikonal`, `Work.Diff.C.dmRadialBridge`, `Work.Diff.C.dmRadialOrthogonal`.
2. **Hinge comparison at `p`** (`Submission.HingeCompare.hinge_of_cos_second_deriv`) yields the law
   of cosines at `p`, i.e. exactly the value conjunct, once the one-sided Hessian bound
   `(cos ρ)'' + cos ρ ≥ -ε` holds along the ray (`ρ = rdist q ∘ γ`).  On the good region that is
   `hHess`; in the dip it reads `-sin(ρ)ρ'' ≥ -ε` with
   `ρ'' = (1-(ρ')²)II_{S(q,ρ)}(w,w)`, hence holds as soon as `II ≤ 0` for `ρ ∈ [π-δ,π)`, which would
   follow from the Riccati comparison `II ≤ cot ρ` (the same missing chapter).  An exhaustion
   argument (apply the comparison up to the first time `ρ = π`; at that time the conclusion forces
   `|β| = 1` and `T = π/2`) shows the hinge comparison is valid on all of `[0,s]` **unless** `ρ`
   exceeds `π`, where the branch `ρ > π` needs a *lower* bound on the shape operator (unavailable
   from `sec ≥ 1`).  `Work.Diff.C.hinge_slack` (delegated) is the ε-slack version needed here.
3. **H-ODE at the tip** (the docstring's route): `h t := fcos p (η t)` along a minimising geodesic
   from `q` to `x`; `h'' = -h + E` wherever `h > -1+c`.  The bad region `{t : d_p(η t) ≥ π-δ}` obeys
   the *crude* inclusion `bad ⊆ [π/2-δ, s+L-π+δ]` (from `d_p(ηt) ≤ d_p q + t` and `≤ d_p x + (L-t)`),
   so it is empty iff `s + L < 3π/2 - 2δ`; in the model `s + L = 3π/2` and the bad region is empty,
   and bounding `s + L ≲ 3π/2` *is* the perimeter bound (classical for `sec ≥ 1`, not formalised in
   this workspace).  The Lipschitz-jump argument across the bad interval loses the phase
   (`H(t₂)`, `H'(t₂)` are only bounded by `O(1)`), so it cannot replace the input.  Note that in the
   `H`-bad region `hHess` **does** give the one-sided bound in the branch `ρ ≤ π`, since
   `d_p ≤ π` (`hdiam`) there and the requirement reduces to `II ≤ ε/sin ρ` with `cot ρ ≤ 0`.

### Numerical bookkeeping (`hnum1` is what makes the constants work)

`3c ≤ 1 - cos α` gives `α ≥ √(6c)`, so `C := 100(n+2)(ε₁π + α + √c) ≥ 1034√c`; hence `C ≥ 1` as soon
as `√c ≥ 1/1034`, and then the lower bound of case B1 (`cos L - β sin s ≥ -1 + cos α sin s ≥ -C`) is
automatic.  In the remaining tiny-`c` regime only `|s - π/2| ≤ O(√C) = O(c^{1/4})` is needed.
Moreover `sin δ ≤ √(2c)`, `δ ≤ 2√c`, `ε₁π < c/4 ≤ √c/4`, so all error terms of size `η`, `√c`, `ε₁π`
fit.  Consequently the **sharp** cap diameter (`η ≈ 20√c`) suffices, while the coarse constant of
`Work.Diff.C.cap_diameter` (`η = 100(n+2)(ε₁π+√c)`) does **not**, because `dip_interval_bound`
multiplies `η` by `1 + sin δ ≈ 2`.

---

## STATUS (session N+6): the location bound is *proved* in the workspace — only the far-ball
## diameter (a.k.a. the Rauch sphere size) is missing

Reconnaissance of the workspace (all statements verified to exist):

* **`Work.Diff.C.dip_loc_per`** (`Diff/C/dip_loc_per.lean`, **PROVED, sorry-free**): the dip location
  bound `|σ - π/2| ≤ arccos (1 - 2c') + 20 (√c' + ε₁π)` (for the dip condition `fcos q ≤ -1 + 2c'`)
  from the *perimeter bound* `∀ x y z, d(x,y)+d(y,z)+d(z,x) ≤ 2π + 20(√c' + ε₁π)` alone — the
  Hessian/eikonal inputs are not used.  Applied with `c' = c/2` this gives exactly the input this
  file needs: `|σ - π/2| ≤ δ + 20(√(c/2) + ε₁π) ≤ π/2 + 16√c + 20ε₁π` for every dip time `σ`
  (`δ = arccos (1-c)`), hence ≤ `260 (√c + ε₁π)`.  **So the whole location-bound problem reduces to
  the perimeter bound for the triples `(p, ·, q)`** (`d(p,y) + d(q,y) ≤ 3π/2 + K`, `K` up to ~250).
* The fleet's `geoCrux` development organises the perimeter bound as
  `PerimeterBoundProp ← SphereSizeProp + HingeCosProp` (`geoCrux/Defs.lean`, `FarDefs.lean`), with
  `SphereSizeProp ← RauchSphereMapProp ← CutInjectProp + RadialModulusProp` (`RauchDefs.lean`) and
  `HingeCosProp ← hinge_cos_free + HingeCosHardProp`, the latter reduced (in `hinge_cos_hard.lean`,
  all auxiliary lemmas **PROVED**) to `FarBallDiameterProp` (`≤ (73/10)√(c+ε₁π)`), which is the
  sharp far-ball diameter, i.e. `SphereSizeProp` again.
* **CLOSED THIS SESSION**: `Submission/Work/Diff/C/geoCrux/rauch_num.lean` (module
  `Submission.Work.Diff.C.geoCrux.rauch_num`, all PROVED and axiom-clean) — three purely numerical
  steps of the Rauch/Riccati-comparison chain:
  * `Work.Diff.C.geoCrux.rauch_num_small_rho`: `3 (ε₁ (1 + log (2/ρ)²) + ρ²) ρ ≤ 40 (√c + ε₁π)` for
    `0 < ρ ≤ √(c/4)` — the numerical step of the small-`ρ` case of `rauch_sphere_map_core`
    (`geoCrux/rauch_sphere_map.lean` line ~671);
  * `Work.Diff.C.geoCrux.rauch_B_large_alt` and `rauch_B_tiny_alt`: the two `B`-constant estimates of
    `geoCrux/rauch_B_large.lean` / `geoCrux/rauch_B_tiny.lean` (same hypotheses and conclusions,
    `_alt` names so that no module importing both copies clashes).  These two are exactly what
    `geoCrux/rauch_arith.lean` calls (lines 33 and 56), and `rauch_arith` is precisely the `harith`
    hypothesis of `rauch_sphere_map_core`; so **wiring `rauch_B_large_alt`/`rauch_B_tiny_alt` into
    `rauch_arith.lean` makes `rauch_arith` genuinely sorry-free**, and the `harith` input of
    `rauch_sphere_map_core` is available.  The other gap of `rauch_sphere_map_core` (line ~748) is a
    one-line call to the **PROVED** `Work.Diff.C.geoCrux.tan_ratio_bounds`
    (`geoCrux/tan_ratio_bounds.lean`).
  * **WIRING DONE**: `geoCrux/rauch_B_tiny.lean` now *proves* `Work.Diff.C.geoCrux.rauch_B_tiny`
    by `Work.Diff.C.geoCrux.rauch_B_tiny_alt` (statement unchanged), and its `#print axioms` is
    `[propext, Classical.choice, Quot.sound]`.  Consequently **`Work.Diff.C.geoCrux.rauch_arith`
    is now axiom-clean** (verified), i.e. the `harith` input of the Rauch assembly is sorry-free
    without any further work.  In `geoCrux/rauch_sphere_map.lean` the `harith` argument was
    switched to `Work.Diff.C.geoCrux.rauch_arith_alt` as well (identical type; that file cannot be
    *built* at the moment only because the colleague's `geoCrux/radial_modulus.lean` is mid-edit and
    does not compile yet).
  * `Work.Diff.C.geoCrux.rauch_arith_alt` — the **whole statement of `Work.Diff.C.geoCrux.rauch_arith`**
    (i.e. the `harith` hypothesis of `rauch_sphere_map_core`), proved here from
    `rauch_B_large_alt` / `rauch_B_mid` (proved) / `rauch_B_tiny_alt` / the `rauch_exp_*` estimates.
    Its `#print axioms` is `[propext, Classical.choice, Quot.sound]`, so the `harith` input of
    `rauch_sphere_map` is available **now** (the one-line wiring in `geoCrux/rauch_sphere_map.lean`
    is `(harith := fun hA hR hR1 hs0 hs1 => Work.Diff.C.geoCrux.rauch_arith_alt hc hc1 hε₁ hnum2
    hs0 hs1 hA hR hR1)`).  With that, the only remaining inputs of `RauchSphereMapProp` are
    `CutInjectProp` and `RadialModulusProp`.
* **ALSO CLOSED THIS SESSION**: `Work.Diff.C.geoCrux.far_ball_arith`
  (`geoCrux/far_ball_arith.lean`, statement unchanged, **sorry-free, axiom-clean**): the numerical
  endgame of the far-ball diameter, by splitting it into the two delegated-and-proved pieces
  `Work.Diff.C.geoCrux.far_ball_trig` (the binding `ε₁ = 0` bound `2 arccos(1-c) + π sin(arccos(1-c))
  ≤ (73/10)√c`) and `Work.Diff.C.geoCrux.far_ball_log` (the `ε₁`/logarithm budget spent against the
  slack of the first piece).  Also landed: `Work.Diff.C.dip_numeric` (`Diff/C/dip_numeric.lean`),
  the pure-arithmetic endgame of the dip case of this file (estimates (A), (B) with the input
  `|x| ≤ sin(4δ + 100(n+2)(ε₁π+√c))`), plus `arccos(1-c) ≤ 2√c` and `(12/5)√c ≤ α`.
* Remaining unproved links of the chain (each a single `sorry`, in the fleet's files): `cut_inject`
  (`CutInjectProp`), `radial_modulus` (`RadialModulusProp`), `rauch_sphere_map` (the assembly
  `RauchSphereMapProp` from `rauch_sphere_map_core` + the two inputs), `perimeter_bound`,
  `far_ball_diam`/`far_ball_diameter` (`FarBallDiameterProp`), `hinge_cos_hard` (assembly only).
* **Constants for THIS file's two conjuncts** (`C = 100(n+2)(ε₁π+α+√c) ≥ 300√c ≥ 735√c`):
  in the "tip in the cap" case (B1) the *coarse* location bound `|s - π/2| ≤ 260(√c+ε₁π)` already
  suffices: `1 - sin s ≤ min((s-π/2)²/2, 2)` is ≤ `33800c` (for `c ≤ 4.6e-4`) resp. `2 ≤ 300√c`
  (for `c ≥ 4.6e-4`), and the derivative conjunct needs `sin δ + |cos s| ≤ 1.42√c + 260√c ≤ 300√c`.
  In the "tip good, dip earlier" case (B2) the anchor at the *last* dip time `b` needs the **sharp**
  dip length (`|b - a| ≈ 16√c`): the coarse `260√c` gives anchor errors `≈ 1256√c` which exceed `C`.
* Traps (unchanged, re-verified): this file must not import `Diff/C/init_data` (clash on
  `Work.Diff.C.inner_rgrad_mvfderiv'` with `ray_cos_compare`); `fb_stubs.lean`, `far_sphere_size.lean`,
  `far_ball_excess.lean`(via `fb_stubs`), `cap_near.lean`, `far_sphere_diameter.lean`,
  `dip_far_sharp.lean`, `dip_model_sharp.lean` all still contain `sorry` (do not import them for an
  axiom-clean proof); `Submission/Work/Diff/C/geoCrux/*` is largely sorry-free and is the live effort.
-/

theorem ode_compare_value_aux {φ φ' φ'' : ℝ → ℝ} {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 ≤ s)
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt φ (φ' t) t)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt φ' (φ'' t) t)
    (h3 : ∀ t ∈ Set.Icc (0 : ℝ) s, |φ'' t + φ t| ≤ ε) :
    |φ s - (φ 0 * Real.cos s + φ' 0 * Real.sin s)| ≤ ε * s := by
  set z : ℝ → ℝ := fun t => φ t - (φ 0 * Real.cos t + φ' 0 * Real.sin t) with hzdef
  set z' : ℝ → ℝ := fun t => φ' t + (φ 0 * Real.sin t - φ' 0 * Real.cos t) with hz'def
  set hh : ℝ → ℝ := fun t => φ'' t + φ t with hhdef
  have hz0 : z 0 = 0 := by simp [hzdef]
  have hz'0 : z' 0 = 0 := by simp [hz'def]
  have hdz : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt z (z' t) t := by
    intro t ht
    have hc : HasDerivAt (fun u : ℝ => φ 0 * Real.cos u + φ' 0 * Real.sin u)
        (φ 0 * (-Real.sin t) + φ' 0 * Real.cos t) t :=
      ((Real.hasDerivAt_cos t).const_mul (φ 0)).add ((Real.hasDerivAt_sin t).const_mul (φ' 0))
    have h := (h1 t ht).sub hc
    have heq : φ' t - (φ 0 * (-Real.sin t) + φ' 0 * Real.cos t) = z' t := by
      rw [hz'def]; ring
    rw [heq] at h
    exact h
  have hdz' : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt z' (hh t - z t) t := by
    intro t ht
    have hc : HasDerivAt (fun u : ℝ => φ 0 * Real.sin u - φ' 0 * Real.cos u)
        (φ 0 * Real.cos t - φ' 0 * (-Real.sin t)) t :=
      ((Real.hasDerivAt_sin t).const_mul (φ 0)).sub ((Real.hasDerivAt_cos t).const_mul (φ' 0))
    have h := (h2 t ht).add hc
    have heq : φ'' t + (φ 0 * Real.cos t - φ' 0 * (-Real.sin t)) = hh t - z t := by
      rw [hhdef, hzdef]; ring
    rw [heq] at h
    exact h
  set ζ : ℝ → ℂ := fun t => (z' t : ℂ) + Complex.I * (z t : ℂ) with hζdef
  set ξ : ℝ → ℂ := fun t => Complex.exp (-(t : ℂ) * Complex.I) * ζ t with hξdef
  have hdζ : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt ζ (Complex.I * ζ t + (hh t : ℂ)) t := by
    intro t ht
    have ha : HasDerivAt (fun u : ℝ => (z' u : ℂ)) ((hh t - z t : ℝ) : ℂ) t :=
      (hdz' t ht).ofReal_comp
    have hb : HasDerivAt (fun u : ℝ => (z u : ℂ)) ((z' t : ℝ) : ℂ) t := (hdz t ht).ofReal_comp
    have h := ha.add (hb.const_mul Complex.I)
    have heq : ((hh t - z t : ℝ) : ℂ) + Complex.I * ((z' t : ℝ) : ℂ)
        = Complex.I * ζ t + (hh t : ℂ) := by
      rw [hζdef]
      push_cast
      rw [mul_add, ← mul_assoc, Complex.I_mul_I]
      ring
    rw [heq] at h
    exact h
  have hdξ : ∀ t ∈ Set.Icc (0 : ℝ) s,
      HasDerivAt ξ (Complex.exp (-(t : ℂ) * Complex.I) * (hh t : ℂ)) t := by
    intro t ht
    have hu : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have hlin : HasDerivAt (fun u : ℝ => -(u : ℂ) * Complex.I) (-Complex.I) t := by
      have h := (hu.neg).mul_const Complex.I
      simpa using h
    have hexp : HasDerivAt (fun u : ℝ => Complex.exp (-(u : ℂ) * Complex.I))
        (Complex.exp (-(t : ℂ) * Complex.I) * (-Complex.I)) t := hlin.cexp
    have h := hexp.mul (hdζ t ht)
    have heq : Complex.exp (-(t : ℂ) * Complex.I) * (-Complex.I) * ζ t
        + Complex.exp (-(t : ℂ) * Complex.I) * (Complex.I * ζ t + (hh t : ℂ))
        = Complex.exp (-(t : ℂ) * Complex.I) * (hh t : ℂ) := by
      ring
    rw [heq] at h
    exact h
  have hξ0 : ξ 0 = 0 := by
    simp [hξdef, hζdef, hz0, hz'0]
  have hbnd : ∀ t ∈ Set.Ico (0 : ℝ) s,
      ‖Complex.exp (-(t : ℂ) * Complex.I) * (hh t : ℂ)‖ ≤ ε := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) s := ⟨ht.1, le_of_lt ht.2⟩
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(t : ℂ) * Complex.I).re = 0 := by simp
    rw [hre, Real.exp_zero, one_mul]
    have h5 : ‖((hh t : ℝ) : ℂ)‖ = |hh t| := by simp
    rw [h5]
    exact h3 t ht'
  have hMVT : ‖ξ s - ξ 0‖ ≤ ε * (s - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (f := ξ)
      (f' := fun t => Complex.exp (-(t : ℂ) * Complex.I) * (hh t : ℂ))
      (fun t ht => (hdξ t ht).hasDerivWithinAt) hbnd s ⟨hs, le_rfl⟩
  rw [hξ0, sub_zero, sub_zero] at hMVT
  have hn1 : ‖ξ s‖ = ‖ζ s‖ := by
    rw [hξdef, norm_mul]
    have hn : ‖Complex.exp (-(s : ℂ) * Complex.I)‖ = 1 := by
      have hcast : (-(s : ℂ) * Complex.I) = ((-s : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hcast, Complex.norm_exp_ofReal_mul_I]
    rw [hn, one_mul]
  have hn2 : ‖(z s : ℂ)‖ ≤ ‖ζ s‖ := by
    have him : (ζ s).im = z s := by simp [hζdef]
    calc ‖(z s : ℂ)‖ = |z s| := by simp
      _ = |(ζ s).im| := by rw [him]
      _ ≤ ‖ζ s‖ := Complex.abs_im_le_norm _
  have hfin : |z s| ≤ ε * s := by
    rw [show |z s| = ‖(z s : ℂ)‖ by simp]
    linarith [hn2, hn1, hMVT]
  have hzval : z s = φ s - (φ 0 * Real.cos s + φ' 0 * Real.sin s) := rfl
  rwa [hzval] at hfin


theorem ode_compare_deriv_aux {φ φ' φ'' : ℝ → ℝ} {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 ≤ s)
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt φ (φ' t) t)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt φ' (φ'' t) t)
    (h3 : ∀ t ∈ Set.Icc (0 : ℝ) s, |φ'' t + φ t| ≤ ε) :
    |φ' s - (φ' 0 * Real.cos s - φ 0 * Real.sin s)| ≤ ε * s := by
  set z : ℝ → ℝ := fun t => φ t - (φ 0 * Real.cos t + φ' 0 * Real.sin t) with hzdef
  set z' : ℝ → ℝ := fun t => φ' t + (φ 0 * Real.sin t - φ' 0 * Real.cos t) with hz'def
  set hh : ℝ → ℝ := fun t => φ'' t + φ t with hhdef
  have hz0 : z 0 = 0 := by simp [hzdef]
  have hz'0 : z' 0 = 0 := by simp [hz'def]
  have hdz : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt z (z' t) t := by
    intro t ht
    have hc : HasDerivAt (fun u : ℝ => φ 0 * Real.cos u + φ' 0 * Real.sin u)
        (φ 0 * (-Real.sin t) + φ' 0 * Real.cos t) t :=
      ((Real.hasDerivAt_cos t).const_mul (φ 0)).add ((Real.hasDerivAt_sin t).const_mul (φ' 0))
    have h := (h1 t ht).sub hc
    have heq : φ' t - (φ 0 * (-Real.sin t) + φ' 0 * Real.cos t) = z' t := by
      rw [hz'def]; ring
    rw [heq] at h
    exact h
  have hdz' : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt z' (hh t - z t) t := by
    intro t ht
    have hc : HasDerivAt (fun u : ℝ => φ 0 * Real.sin u - φ' 0 * Real.cos u)
        (φ 0 * Real.cos t - φ' 0 * (-Real.sin t)) t :=
      ((Real.hasDerivAt_sin t).const_mul (φ 0)).sub ((Real.hasDerivAt_cos t).const_mul (φ' 0))
    have h := (h2 t ht).add hc
    have heq : φ'' t + (φ 0 * Real.cos t - φ' 0 * (-Real.sin t)) = hh t - z t := by
      rw [hhdef, hzdef]; ring
    rw [heq] at h
    exact h
  set ζ : ℝ → ℂ := fun t => (z' t : ℂ) + Complex.I * (z t : ℂ) with hζdef
  set ξ : ℝ → ℂ := fun t => Complex.exp (-(t : ℂ) * Complex.I) * ζ t with hξdef
  have hdζ : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt ζ (Complex.I * ζ t + (hh t : ℂ)) t := by
    intro t ht
    have ha : HasDerivAt (fun u : ℝ => (z' u : ℂ)) ((hh t - z t : ℝ) : ℂ) t :=
      (hdz' t ht).ofReal_comp
    have hb : HasDerivAt (fun u : ℝ => (z u : ℂ)) ((z' t : ℝ) : ℂ) t := (hdz t ht).ofReal_comp
    have h := ha.add (hb.const_mul Complex.I)
    have heq : ((hh t - z t : ℝ) : ℂ) + Complex.I * ((z' t : ℝ) : ℂ)
        = Complex.I * ζ t + (hh t : ℂ) := by
      rw [hζdef]
      push_cast
      rw [mul_add, ← mul_assoc, Complex.I_mul_I]
      ring
    rw [heq] at h
    exact h
  have hdξ : ∀ t ∈ Set.Icc (0 : ℝ) s,
      HasDerivAt ξ (Complex.exp (-(t : ℂ) * Complex.I) * (hh t : ℂ)) t := by
    intro t ht
    have hu : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have hlin : HasDerivAt (fun u : ℝ => -(u : ℂ) * Complex.I) (-Complex.I) t := by
      have h := (hu.neg).mul_const Complex.I
      simpa using h
    have hexp : HasDerivAt (fun u : ℝ => Complex.exp (-(u : ℂ) * Complex.I))
        (Complex.exp (-(t : ℂ) * Complex.I) * (-Complex.I)) t := hlin.cexp
    have h := hexp.mul (hdζ t ht)
    have heq : Complex.exp (-(t : ℂ) * Complex.I) * (-Complex.I) * ζ t
        + Complex.exp (-(t : ℂ) * Complex.I) * (Complex.I * ζ t + (hh t : ℂ))
        = Complex.exp (-(t : ℂ) * Complex.I) * (hh t : ℂ) := by
      ring
    rw [heq] at h
    exact h
  have hξ0 : ξ 0 = 0 := by
    simp [hξdef, hζdef, hz0, hz'0]
  have hbnd : ∀ t ∈ Set.Ico (0 : ℝ) s,
      ‖Complex.exp (-(t : ℂ) * Complex.I) * (hh t : ℂ)‖ ≤ ε := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) s := ⟨ht.1, le_of_lt ht.2⟩
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(t : ℂ) * Complex.I).re = 0 := by simp
    rw [hre, Real.exp_zero, one_mul]
    have h5 : ‖((hh t : ℝ) : ℂ)‖ = |hh t| := by simp
    rw [h5]
    exact h3 t ht'
  have hMVT : ‖ξ s - ξ 0‖ ≤ ε * (s - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (f := ξ)
      (f' := fun t => Complex.exp (-(t : ℂ) * Complex.I) * (hh t : ℂ))
      (fun t ht => (hdξ t ht).hasDerivWithinAt) hbnd s ⟨hs, le_rfl⟩
  rw [hξ0, sub_zero, sub_zero] at hMVT
  have hn1 : ‖ξ s‖ = ‖ζ s‖ := by
    rw [hξdef, norm_mul]
    have hn : ‖Complex.exp (-(s : ℂ) * Complex.I)‖ = 1 := by
      have hcast : (-(s : ℂ) * Complex.I) = ((-s : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hcast, Complex.norm_exp_ofReal_mul_I]
    rw [hn, one_mul]
  have hn2 : ‖(z' s : ℂ)‖ ≤ ‖ζ s‖ := by
    have hre : (ζ s).re = z' s := by simp [hζdef]
    calc ‖(z' s : ℂ)‖ = |z' s| := by simp
      _ = |(ζ s).re| := by rw [hre]
      _ ≤ ‖ζ s‖ := Complex.abs_re_le_norm _
  have hfin : |z' s| ≤ ε * s := by
    rw [show |z' s| = ‖(z' s : ℂ)‖ by simp]
    linarith [hn2, hn1, hMVT]
  have hzval : z' s = φ' s - (φ' 0 * Real.cos s - φ 0 * Real.sin s) := by
    rw [hz'def]; ring
  rwa [hzval] at hfin


end Work.Diff.C

namespace Work.Diff.C


open Bundle in
/-- **The arithmetic bridge of the dip case.**  Pure real analysis: if the model comparison
`|F a - M a| ≤ ε` holds at the first dip time `a`, while `F` is `sin δ`-Lipschitz on the dip and the
model `M` is 1-Lipschitz, then the deviation of `F` from `M` at the endpoint `s` is at most
`(1 + sin δ) |s - a| + ε`.  This is the inequality that turns the *location* of the dip
(`Work.Diff.C.dip_exit_time`, or its length bound from `Work.Diff.C.cap_diameter`) into the value
conjunct of `Work.Diff.C.dip_model_through`. -/
theorem dip_interval_bound {F M : ℝ → ℝ} {a s ε δ : ℝ} (hε : 0 ≤ ε)
    (hcmp : |F a - M a| ≤ ε)
    (hF : |F s - F a| ≤ Real.sin δ * |s - a|)
    (hM : |M s - M a| ≤ |s - a|) :
    |F s - M s| ≤ (1 + Real.sin δ) * |s - a| + ε := by
  have h1 : |F s - M s| ≤ |F s - F a| + |F a - M a| + |M a - M s| := by
    have h0 : F s - M s = (F s - F a) + (F a - M a) + (M a - M s) := by ring
    rw [h0]
    exact abs_add_three _ _ _
  have h2 : |M a - M s| = |M s - M a| := abs_sub_comm _ _
  rw [h2] at h1
  have h3 : |F s - F a| + |F a - M a| + |M s - M a|
      ≤ Real.sin δ * |s - a| + ε + |s - a| := by linarith
  have h4 : Real.sin δ * |s - a| + ε + |s - a|
      = (1 + Real.sin δ) * |s - a| + ε := by ring
  linarith [h1, h3, h4]


open Bundle in
/-- **The model comparison off the antipodal cap of `q` (values).**  In the setting of
`Work.Diff.C.dip_model_through`, if the ray `γ σ = GExp p (σ • u)` stays in the good region
`fcos q (γ σ) > -1 + c` on all of `[0,s]`, then the value conjunct of the target holds with error
`ε₁ s`:
`|fFam … (Fin.succ k) (GExp p (s • u)) - ⟪e k, u⟫ * sin s| ≤ ε₁ s`.
Proof: the ported ray comparison `Work.Diff.C.gp_ode_compare` (module `Diff/C/gp_ode_compare`),
whose hypotheses are exactly `hsmC` and `hHess` on the good region, with the initial data
`fFam … (Fin.succ k) (p) = 0`, `∇ (fFam … (Fin.succ k)) (p) = e k` from `InitData`. -/
theorem value_off_cap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hε₁ : 0 ≤ ε₁)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    {u : TangentSpace I p} (hu : Inner.inner ℝ u u = 1) {s : ℝ} (hs0 : 0 ≤ s)
    {k : Fin (Module.finrank ℝ E)}
    (hgood : ∀ σ ∈ Set.Icc (0 : ℝ) s,
      -1 + c < fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) :
    |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))
      - Inner.inner ℝ (e k) u * Real.sin s| ≤ ε₁ * s := by
  obtain ⟨-, -, hfi⟩ := hinit
  have hp0 : fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k) p = 0 := (hfi k).1
  have hgp : rgrad (I := I) (M := M) (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) p
      = e k := (hfi k).2
  have h := gp_ode_compare (I := I) (M := M) (cov := cov) hmet htor
    (q := p) (f := fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
    (ε := ε₁) hε₁ hu hs0 ?_ ?_
  · rw [hp0, hgp] at h
    simpa using h
  · intro t ht
    exact hsmC (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) _
      (le_of_lt (hgood t ht))
  · intro t ht V
    have hb := hHess (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) V V (hgood t ht)
    have hb' : |rhess (I := I) (M := M) cov
          (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
          (Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) V V
        + fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) * Inner.inner ℝ V V|
        ≤ ε₁ * ‖V‖ * ‖V‖ := hb
    rw [real_inner_self_eq_norm_sq] at hb' ⊢
    have h2 : ε₁ * ‖V‖ * ‖V‖ = ε₁ * ‖V‖ ^ 2 := by ring
    rw [h2] at hb'
    exact hb'



open Bundle in
open Submission.GlobalExp Submission.Geodesic in
theorem gp_ode_compare_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} {f : M → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    {u : TangentSpace I q} (hu : Inner.inner ℝ u u = 1)
    {s : ℝ} (hs0 : 0 ≤ s)
    (hsm : ∀ t ∈ Set.Icc (0 : ℝ) s,
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) f (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)))
    (hHess : ∀ t ∈ Set.Icc (0 : ℝ) s,
      ∀ V : TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)),
        |rhess cov f (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) V V
          + f (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))
            * Inner.inner ℝ V V| ≤ ε * Inner.inner ℝ V V) :
    |Inner.inner ℝ (rgrad (I := I) (M := M) f (Submission.GlobalExp.GExp (cov := cov) hmet q (s • u)))
        (curveVelocity (I := I) (fun σ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (σ • u)) s)
      - (Inner.inner ℝ (rgrad (I := I) (M := M) f q) u * Real.cos s - f q * Real.sin s)|
      ≤ ε * s := by
  have hu_ne : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  have hunorm : ‖u‖ = 1 := by
    have h : ‖u‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq u]; exact hu
    nlinarith [norm_nonneg u]
  have huξ : unitOf (I := I) u hu_ne = u := by
    rw [unitOf, hunorm]; simp
  set T : ℝ := max 1 s + 1 with hTdef
  have hT0 : 0 ≤ T := by rw [hTdef]; linarith [le_max_left (1:ℝ) s]
  have hsT : s ≤ T := by rw [hTdef]; linarith [le_max_right (1:ℝ) s]
  have hsT' : s + 1 / 2 ≤ T := by rw [hTdef]; linarith [le_max_right (1:ℝ) s]
  set γ : ℝ → M := geodCurve (cov := cov) hmet T hT0 q (unitOf u hu_ne)
    (unitOf_norm u hu_ne) with hγdef
  obtain ⟨hγ0, hγv0, hγsm, hγgeo, hγsp⟩ :=
    geodCurve_spec (cov := cov) hmet T hT0 q (unitOf u hu_ne) (unitOf_norm u hu_ne)
  set dl : ℝ := geodDelta (cov := cov) hmet with hdldef
  have hdlpos : 0 < dl := geodDelta_pos hmet
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) s, t ∈ Set.Ioo (-dl) (T + dl) := by
    intro t ht
    exact Set.mem_Ioo.mpr ⟨by linarith [hdlpos, ht.1], by linarith [ht.2, hsT, hdlpos]⟩
  have hGExp : ∀ t ∈ Set.Icc (0 : ℝ) T, GExp (cov := cov) hmet q (t • u) = γ t := by
    intro t ht
    have hmul : t * ‖u‖ = t := by rw [hunorm, mul_one]
    have hl : (0 : ℝ) ≤ max ‖u‖ (t * ‖u‖) := le_trans (norm_nonneg u) (le_max_left _ _)
    have hle : max ‖u‖ (t * ‖u‖) ≤ T := by
      refine max_le ?_ ?_
      · rw [hunorm, hTdef]; linarith [le_max_left (1:ℝ) s]
      · rw [hunorm, mul_one]; exact ht.2
    have hmemt : t * ‖u‖ ∈ Set.Ioo (-dl) (max ‖u‖ (t * ‖u‖) + dl) := by
      refine Set.mem_Ioo.mpr ⟨?_, ?_⟩
      · rw [hunorm, mul_one]; linarith [hdlpos, ht.1]
      · have h2 := le_max_right ‖u‖ (t * ‖u‖); linarith [hdlpos, h2]
    have hagree := geodCurve_agree (cov := cov) hmet hl hT0 hle q
      (unitOf u hu_ne) (unitOf_norm u hu_ne)
    have h2 : (geodCurve (cov := cov) hmet (max ‖u‖ (t * ‖u‖)) hl q
        (unitOf u hu_ne) (unitOf_norm u hu_ne)) (t * ‖u‖) = γ t := by
      rw [show (geodCurve (cov := cov) hmet (max ‖u‖ (t * ‖u‖)) hl q
            (unitOf u hu_ne) (unitOf_norm u hu_ne)) (t * ‖u‖)
          = (geodCurve (cov := cov) hmet T hT0 q (unitOf u hu_ne) (unitOf_norm u hu_ne))
              (t * ‖u‖) from hagree hmemt]
      rw [hmul]
    rw [GExp_smul (cov := cov) hmet q hu_ne ht.1]
    exact h2
  have hft : ∀ t ∈ Set.Icc (0 : ℝ) s,
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) f (γ t) := by
    intro t ht
    have h := hsm t ht
    rwa [hGExp t ⟨ht.1, le_trans ht.2 hsT⟩] at h
  have hγmd : ∀ t ∈ Set.Icc (0 : ℝ) s, MDifferentiableAt (modelWithCornersSelf ℝ ℝ) I γ t := fun t ht =>
    (hγsm.contMDiffAt (isOpen_Ioo.mem_nhds (hmem t ht))).mdifferentiableAt (by simp)
  set φ : ℝ → ℝ := fun τ => f (γ τ) with hφdef
  set φ' : ℝ → ℝ := fun τ => mvfderiv I f (γ τ) (curveVelocity (I := I) γ τ) with hφ'def
  set φ'' : ℝ → ℝ := fun τ =>
    rhess cov f (γ τ) (curveVelocity (I := I) γ τ) (curveVelocity (I := I) γ τ) with hφ''def
  have h1 : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt φ (φ' t) t := by
    intro t ht
    have hfmd : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f (γ t) := (hft t ht).mdifferentiableAt (by simp)
    have hcomp := hfmd.hasMFDerivAt.comp t (hγmd t ht).hasMFDerivAt
    have hkey := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := f)
      (γ := γ) (t := t) hfmd (hγmd t ht)
    have hval : φ' t = deriv (f ∘ γ) t := by
      change mvfderiv I f (γ t) (curveVelocity (I := I) γ t) = deriv (f ∘ γ) t
      exact hkey
    rw [hval]
    exact hcomp.hasFDerivAt.differentiableAt.hasDerivAt
  have h2 : ∀ t ∈ Set.Icc (0 : ℝ) s, HasDerivAt φ' (φ'' t) t := by
    intro t ht
    have hne : curveVelocity (I := I) γ t ≠ 0 := by
      intro h0
      have h := hγsp t (hmem t ht)
      rw [h0, norm_zero] at h
      norm_num at h
    exact gpOde_hasDerivAt_secondDeriv_along_geodesic (cov := cov) hmet isOpen_Ioo (hmem t ht) hγsm
      (fun τ hτ => hγgeo τ hτ) hne
      ((gpOde_grad_smoothAt (I := I) (F := f) (x := γ t) (hft t ht)).mdifferentiableAt (by simp))
  have h3 : ∀ t ∈ Set.Icc (0 : ℝ) s, |φ'' t + φ t| ≤ ε := by
    intro t ht
    have hV : Inner.inner ℝ (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) = 1 := by
      rw [real_inner_self_eq_norm_sq, hγsp t (hmem t ht)]
      norm_num
    have hh := hHess t ht
    rw [hGExp t ⟨ht.1, le_trans ht.2 hsT⟩] at hh
    have hres := hh (curveVelocity (I := I) γ t)
    simp only [hV, mul_one] at hres
    change |rhess cov f (γ t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
      + f (γ t)| ≤ ε
    exact hres
  have hfin := ode_compare_deriv_aux (φ := φ) (φ' := φ') (φ'' := φ'') hε hs0 h1 h2 h3
  have hvel' : curveVelocity (I := I) γ s
      = curveVelocity (I := I)
          (fun σ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (σ • unitOf u hu_ne)) s :=
    (Submission.GExpRayVelocity.curveVelocity_GExp_eq_of_isGeodesicAt (cov := cov) hmet
      (by
        intro h0
        have h := unitOf_norm u hu_ne
        rw [h0, norm_zero] at h
        norm_num at h)
      (V := unitOf u hu_ne)
      (a := -dl) (b := T + dl) (T := s) (by linarith [hdlpos]) hs0 (by linarith [hdlpos])
      hγsm (fun t ht => hγgeo t ht)
      (fun t ht => by
        intro h0
        have h := hγsp t ht
        rw [h0, norm_zero] at h
        norm_num at h)
      hγ0 hγv0 s ⟨hs0, le_rfl⟩).symm
  have hvel : curveVelocity (I := I) γ s
      = curveVelocity (I := I) (fun σ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (σ • u)) s := by
    rw [hvel']
    congr 1
    funext σ
    rw [huξ]
  have hγs : γ s = Submission.GlobalExp.GExp (cov := cov) hmet q (s • u) :=
    (hGExp s ⟨hs0, le_trans le_rfl hsT⟩).symm
  have hφ's : φ' s = Inner.inner ℝ
      (rgrad (I := I) (M := M) f (Submission.GlobalExp.GExp (cov := cov) hmet q (s • u)))
      (curveVelocity (I := I) (fun σ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (σ • u)) s) := by
    change mvfderiv I f (γ s) (curveVelocity (I := I) γ s) = Inner.inner ℝ
      (rgrad (I := I) (M := M) f (Submission.GlobalExp.GExp (cov := cov) hmet q (s • u)))
      (curveVelocity (I := I) (fun σ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (σ • u)) s)
    rw [hvel, hγs]
    exact (gpOde_inner_rgrad_mvfderiv' (I := I) f
      (Submission.GlobalExp.GExp (cov := cov) hmet q (s • u))
      (curveVelocity (I := I) (fun σ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (σ • u)) s)).symm
  have hφ0 : φ 0 = f q := by
    change f (γ 0) = f q
    rw [hγdef, hγ0]
  have hφ'0 : φ' 0 = Inner.inner ℝ (rgrad (I := I) (M := M) f q) u := by
    change mvfderiv I f (γ 0) (curveVelocity (I := I) γ 0)
      = Inner.inner ℝ (rgrad (I := I) (M := M) f q) u
    rw [hγdef, hγ0, hγv0, huξ]
    exact (gpOde_inner_rgrad_mvfderiv' (I := I) f q u).symm
  rw [hφ's, hφ0, hφ'0] at hfin
  exact hfin





open Bundle in
/-- **The model comparison off the antipodal cap of `q` (radial derivative).**  Companion of
`value_off_cap`: in the setting of `Work.Diff.C.dip_model_through`, if the ray from `p` stays in the
good region `fcos q (γ σ) > -1 + c` on `[0,s]`, then the *derivative* conjunct of the target holds
with error `ε₁ s`.  Proof: the ported derivative ray comparison `gp_ode_compare_deriv` in this file
(the derivative companion of `Diff/C/gp_ode_compare`), whose hypotheses are `hsmC` and `hHess` on the
good region, with the initial data from `InitData`. -/
theorem deriv_off_cap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hε₁ : 0 ≤ ε₁)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    {u : TangentSpace I p} (hu : Inner.inner ℝ u u = 1) {s : ℝ} (hs0 : 0 ≤ s)
    {k : Fin (Module.finrank ℝ E)}
    (hgood : ∀ σ ∈ Set.Icc (0 : ℝ) s,
      -1 + c < fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) :
    |Inner.inner ℝ
        (rgrad (I := I) (M := M)
          (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
          (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)))
        (Submission.Geodesic.curveVelocity
          (fun σ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) s)
      - Inner.inner ℝ (e k) u * Real.cos s| ≤ ε₁ * s := by
  obtain ⟨-, -, hfi⟩ := hinit
  have hp0 : fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k) p = 0 := (hfi k).1
  have hgp : rgrad (I := I) (M := M) (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) p
      = e k := (hfi k).2
  have h := gp_ode_compare_deriv (I := I) (M := M) (cov := cov) hmet htor
    (q := p) (f := fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
    (ε := ε₁) hε₁ hu hs0 ?_ ?_
  · rw [hp0, hgp] at h
    simpa using h
  · intro t ht
    exact hsmC (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) _
      (le_of_lt (hgood t ht))
  · intro t ht V
    have hb := hHess (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) V V (hgood t ht)
    have hb' : |rhess (I := I) (M := M) cov
          (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
          (Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) V V
        + fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (t • u)) * Inner.inner ℝ V V|
        ≤ ε₁ * ‖V‖ * ‖V‖ := hb
    rw [real_inner_self_eq_norm_sq] at hb' ⊢
    have h2 : ε₁ * ‖V‖ * ‖V‖ = ε₁ * ‖V‖ ^ 2 := by ring
    rw [h2] at hb'
    exact hb'


open Bundle in
/-- **Trigonometric model Lipschitz bound.**  For `|β| ≤ 1` the model `σ ↦ β sin σ` is
1-Lipschitz. -/
theorem sin_model_lipschitz {β s a : ℝ} (hβ : |β| ≤ 1) :
    |β * Real.sin s - β * Real.sin a| ≤ |s - a| := by
  rw [← mul_sub, abs_mul]
  calc |β| * |Real.sin s - Real.sin a| ≤ 1 * |s - a| :=
        mul_le_mul hβ (Real.abs_sin_sub_sin_le s a) (abs_nonneg _) zero_le_one
    _ = |s - a| := one_mul _

open Bundle in
/-- **The value conjunct of the target in the dip case**, fed by the *location* of the dip (the
content of `Work.Diff.C.dip_exit_time` / `Work.Diff.C.dip_near_equator`) and by the two inputs of
the bridge `dip_interval_bound`: the model comparison at the first dip time `a` (from the ray
comparison on the good prefix) and the `sin δ`-Lipschitz bound for `cos ∘ rdist q` inside the dip.

`a` is the first dip time, so `a ∈ [π/2-δ, π/2+K]` (`halow` is the elementary half, `haK` the crux),
and the endpoint `s` satisfies `s ≤ π/2+K` (`hsK`).  The conclusion is literally the value conjunct
of `Work.Diff.C.dip_model_through`. -/
theorem value_dip_case
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {α c ε₁ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hε₁ : 0 ≤ ε₁) (hnum1 : 3 * c ≤ 1 - Real.cos α) (hnum2 : 4 * ε₁ * Real.pi < c)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    {u : TangentSpace I p} (hu : Inner.inner ℝ u u = 1) {s : ℝ} (hs0 : 0 ≤ s) (hsπ : s ≤ Real.pi)
    {k : Fin (Module.finrank ℝ E)}
    {a : ℝ} (ha0 : 0 ≤ a) (has : a ≤ s)
    (halow : Real.pi / 2 - Real.arccos (1 - c) ≤ a)
    (haK : a ≤ Real.pi / 2
      + 10 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c))
    (hsK : s ≤ Real.pi / 2
      + 10 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c))
    (hcmp : |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))
        - Inner.inner ℝ (e k) u * Real.sin a| ≤ ε₁ * a)
    (hlip : |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))
          - fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))|
        ≤ Real.sin (Real.arccos (1 - c)) * |s - a|) :
    |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))
      - Inner.inner ℝ (e k) u * Real.sin s|
      ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c) := by
  -- `|⟪e k, u⟫| ≤ 1`
  have hnek : Inner.inner ℝ (e k) (e k) = 1 := by simpa using hON k k
  have hnk : ‖e k‖ = 1 := by
    have h : ‖e k‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hnek
    nlinarith [norm_nonneg (e k)]
  have hnu : ‖u‖ = 1 := by
    have h : ‖u‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq u]; exact hu
    nlinarith [norm_nonneg u]
  have hβ : |Inner.inner ℝ (e k) u| ≤ 1 := by
    have h := abs_real_inner_le_norm (e k) u
    rw [hnk, hnu, mul_one] at h
    exact h
  -- the model is 1-Lipschitz
  have hM : |Inner.inner ℝ (e k) u * Real.sin s - Inner.inner ℝ (e k) u * Real.sin a| ≤ |s - a| :=
    sin_model_lipschitz hβ
  -- the bridge
  have h1 : |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))
      - Inner.inner ℝ (e k) u * Real.sin s|
      ≤ (1 + Real.sin (Real.arccos (1 - c))) * |s - a| + ε₁ * a :=
    dip_interval_bound
      (F := fun τ : ℝ => fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)))
      (M := fun τ : ℝ => Inner.inner ℝ (e k) u * Real.sin τ)
      (a := a) (s := s) (ε := ε₁ * a) (δ := Real.arccos (1 - c))
      (mul_nonneg hε₁ ha0) hcmp hlip hM
  -- numerics: `δ := arccos (1-c)`, `δ ≤ α`
  have hδπ : Real.arccos (1 - c) ≤ Real.pi := Real.arccos_le_pi _
  have hδ0 : 0 ≤ Real.arccos (1 - c) := Real.arccos_nonneg _
  have hcosδ : Real.cos (Real.arccos (1 - c)) = 1 - c :=
    Real.cos_arccos (by linarith) (by linarith)
  have hδα : Real.arccos (1 - c) ≤ α := by
    by_contra hcon
    push_neg at hcon
    have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi (x := α) (y := Real.arccos (1 - c))
      hα.le hδπ hcon
    rw [hcosδ] at hlt
    have hcosα : Real.cos α ≤ Real.cos (Real.arccos (1 - c)) := by
      rw [hcosδ]
      have : c ≤ (1 - Real.cos α) / 3 := by linarith
      linarith
    linarith
  have hsin1 : Real.sin (Real.arccos (1 - c)) ≤ 1 := Real.sin_le_one _
  have habs : |s - a| ≤ 10 * ((Module.finrank ℝ E : ℝ) + 2)
      * (ε₁ * Real.pi + α + Real.sqrt c) + Real.arccos (1 - c) := by
    have hsa : |s - a| = s - a := abs_of_nonneg (by linarith)
    rw [hsa]
    linarith
  have haπ : a ≤ Real.pi := by linarith
  have hα0 : 0 ≤ α := hα.le
  have hπε : 0 ≤ ε₁ * Real.pi := mul_nonneg hε₁ Real.pi_pos.le
  have hsc : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
  have hn3 : (3 : ℝ) ≤ (Module.finrank ℝ E : ℝ) + 2 := by
    have h1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
    linarith
  have hδK : |s - a| ≤ 10 * ((Module.finrank ℝ E : ℝ) + 2)
      * (ε₁ * Real.pi + α + Real.sqrt c) + α := by linarith [habs, hδα]
  have hs1 : (1 + Real.sin (Real.arccos (1 - c))) * |s - a| ≤ 2 * |s - a| := by
    have h2 : 0 ≤ |s - a| := abs_nonneg _
    nlinarith [hsin1, h2]
  have he : ε₁ * a ≤ ε₁ * Real.pi := by nlinarith [hε₁, haπ]
  have hfin : 2 * |s - a| + ε₁ * Real.pi
      ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c) := by
    have h0 : 0 ≤ ε₁ * Real.pi + α + Real.sqrt c := by linarith
    nlinarith [hδK, hn3, h0, hπε, hα0, hsc]
  have h2 : (1 + Real.sin (Real.arccos (1 - c))) * |s - a| + ε₁ * a
      ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c) := by
    linarith [hs1, he, hfin]
  linarith [h1, h2]

open Bundle in
/-- Triangle inequality for `rdist` (ported from `Work.Diff.C.rdist_triangle_le_aux`). -/
theorem dipAux_triangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    (x y z : M) :
    rdist (I := I) (M := M) x z ≤ rdist (I := I) (M := M) x y + rdist (I := I) (M := M) y z := by
  have htri := Manifold.riemannianEDist_triangle (I := I) (x := x) (y := y) (z := z)
  have h1 : Manifold.riemannianEDist I x y ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) hmet htor x y).ne
  have h2 : Manifold.riemannianEDist I y z ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) hmet htor y z).ne
  have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h1, h2⟩) htri
  rw [ENNReal.toReal_add h1 h2] at h3
  simpa only [rdist] using h3

open Bundle in
/-- Symmetry of `rdist` (ported from `Work.Diff.C.rdist_comm_aux`). -/
theorem dipAux_comm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (x y : M) :
    rdist (I := I) (M := M) x y = rdist (I := I) (M := M) y x := by
  rw [rdist, rdist, Manifold.riemannianEDist_comm]

open Bundle in
/-- Along a ray of `GExp`, distances are at most the parameter difference. -/
theorem dipAux_ray_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (x : M)
    {η : TangentSpace I x} (hη : ‖η‖ = 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    rdist (I := I) (M := M) (Submission.GlobalExp.GExp (cov := cov) hmet x (a • η))
      (Submission.GlobalExp.GExp (cov := cov) hmet x (b • η)) ≤ b - a := by
  have h := Submission.HopfRinow.riemannianEDist_GExp_ray_le hmet x hη ha hab
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (by linarith)] at h2

open Bundle in
/-- `rdist x (GExp x (t • v)) ≤ t ‖v‖`. -/
theorem dipAux_ray_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (x : M)
    (v : TangentSpace I x) {t : ℝ} (ht : 0 ≤ t) :
    rdist (I := I) (M := M) x (Submission.GlobalExp.GExp (cov := cov) hmet x (t • v))
      ≤ t * ‖v‖ := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv
    rw [smul_zero, Submission.GlobalExp.GExp_zero, norm_zero, mul_zero, rdist,
      Manifold.riemannianEDist_self, ENNReal.toReal_zero]
  · have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hη : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v),
        inv_mul_cancel₀ hnv]
    have hsm : t • v = (t * ‖v‖) • (‖v‖⁻¹ • v) := by
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ hnv, mul_one]
    rw [hsm]
    have h := dipAux_ray_sub (I := I) (M := M) (cov := cov) hmet x hη (a := 0)
      (b := t * ‖v‖) le_rfl (by positivity)
    rw [zero_smul, Submission.GlobalExp.GExp_zero, sub_zero] at h
    exact h

open Bundle in
/-- **Ray minimising identities**: if the ray from `p` in direction `u` realises the distance to its
endpoint `s`, then it is minimising on `[0,s]` (pointwise and on sub-arcs). -/
theorem dipAux_ray_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {u : TangentSpace I p} (hu : Inner.inner ℝ u u = 1)
    {s : ℝ} (hs0 : 0 ≤ s)
    (hray : rdist (I := I) (M := M) p
      (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) = s) :
    (∀ σ ∈ Set.Icc (0 : ℝ) s,
      rdist (I := I) (M := M) p (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) = σ) ∧
    (∀ σ ∈ Set.Icc (0 : ℝ) s, ∀ τ ∈ Set.Icc (0 : ℝ) s, σ ≤ τ →
      rdist (I := I) (M := M) (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) = τ - σ) := by
  have hu' : ‖u‖ = 1 := by
    have h : ‖u‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq u]; exact hu
    nlinarith [norm_nonneg u]
  have hpt : ∀ σ ∈ Set.Icc (0 : ℝ) s,
      rdist (I := I) (M := M) p (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) = σ := by
    intro σ hσ
    have hle : rdist (I := I) (M := M) p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) ≤ σ * ‖u‖ :=
      dipAux_ray_smul (I := I) (M := M) (cov := cov) hmet p u hσ.1
    rw [hu', mul_one] at hle
    have hsub : rdist (I := I) (M := M)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) ≤ s - σ :=
      dipAux_ray_sub (I := I) (M := M) (cov := cov) hmet p hu' hσ.1 hσ.2
    have htri := dipAux_triangle (I := I) (M := M) (cov := cov) hmet htor p
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))
    rw [hray] at htri
    linarith
  refine ⟨hpt, ?_⟩
  intro σ hσ τ hτ hστ
  have hle : rdist (I := I) (M := M) (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) ≤ τ - σ :=
    dipAux_ray_sub (I := I) (M := M) (cov := cov) hmet p hu' hσ.1 hστ
  have hge : τ - σ ≤ rdist (I := I) (M := M)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) := by
    have htri1 := dipAux_triangle (I := I) (M := M) (cov := cov) hmet htor p
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))
    rw [hpt σ hσ, hpt τ hτ] at htri1
    linarith
  linarith

open Bundle in
/-- The distance to any point along the minimising ray is 1-Lipschitz in the parameter. -/
theorem dipAux_ray_lip
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p q : M} {u : TangentSpace I p} (hu : Inner.inner ℝ u u = 1)
    {s : ℝ} (hs0 : 0 ≤ s)
    (hray : rdist (I := I) (M := M) p
      (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) = s)
    {σ τ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) s) (hτ : τ ∈ Set.Icc (0 : ℝ) s) :
    |rdist (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      - rdist (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))|
      ≤ |σ - τ| := by
  have hsub := (dipAux_ray_eq (I := I) (M := M) (cov := cov) hmet htor hu hs0 hray).2
  have habs : |rdist (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      - rdist (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))|
      ≤ rdist (I := I) (M := M) (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) := by
    refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
    · have h := dipAux_triangle (I := I) (M := M) (cov := cov) hmet htor q
        (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      rw [dipAux_comm (I := I) (M := M)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))] at h
      linarith [h]
    · have h := dipAux_triangle (I := I) (M := M) (cov := cov) hmet htor q
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))
      linarith [h]
  have hdist : rdist (I := I) (M := M) (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) = |σ - τ| := by
    rcases le_total σ τ with hle | hle
    · rw [hsub σ hσ τ hτ hle, abs_sub_comm,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ τ - σ)]
    · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ - τ)]
      calc rdist (I := I) (M := M) (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
            (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))
          = rdist (I := I) (M := M) (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))
              (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) :=
            dipAux_comm (I := I) (M := M) _ _
        _ = σ - τ := hsub τ hτ σ hσ hle
  rwa [hdist] at habs

open Bundle in
/-- **`rdist q p = π/2` for `q = qpt hmet p e (Fin.succ k)`** (port of `Work.Diff.C.rdist_qpt_p`
from `Diff/C/dip_cap_exit.lean`, kept here so that this module and the far-ball chapter can use it
without an import cycle).  `fcos q p = 0` (`InitData`) and `rdist q p ≤ π` (`hdiam`). -/
theorem dipAux_qpt_p
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    (hdiam : ∀ y : M, rdist (I := I) (M := M) p y ≤ Real.pi)
    {k : Fin (Module.finrank ℝ E)} :
    rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) p
      = Real.pi / 2 := by
  set q : M := qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k) with hq
  have hcqp : Real.cos (rdist (I := I) (M := M) q p) = 0 := (hinit.2.2 k).1
  have hle : rdist (I := I) (M := M) q p ≤ Real.pi := by
    have h := hdiam q
    rw [dipAux_comm (I := I) (M := M) q p]
    exact h
  have h0 : 0 ≤ rdist (I := I) (M := M) q p := ENNReal.toReal_nonneg
  obtain ⟨m, hm⟩ := Real.cos_eq_zero_iff.mp hcqp
  have h1 : (0 : ℝ) ≤ 2 * (m : ℝ) + 1 := by nlinarith [hm, h0, Real.pi_pos]
  have h2 : 2 * (m : ℝ) + 1 ≤ 2 := by nlinarith [hm, hle, Real.pi_pos]
  have h1' : (0 : ℤ) ≤ 2 * m + 1 := by exact_mod_cast h1
  have h2' : 2 * m + 1 ≤ 2 := by exact_mod_cast h2
  have h3 : 2 * m + 1 = 1 := by omega
  have h4 : (m : ℝ) = 0 := by
    have hc := congrArg (fun z : ℤ => (z : ℝ)) h3
    push_cast at hc
    linarith
  rw [h4] at hm
  linarith [hm]

open Bundle in
/-- **The dip is `√(2c)`-Lipschitz.**  If `σ, σ' ∈ [0,s]` are dip times for the centre `q` (i.e.
`fcos q (GExp p (σ•u)) ≤ -1+c`) and `rdist q p = π/2`, then
`|fcos q (GExp p (σ•u)) - fcos q (GExp p (σ'•u))| ≤ √(2c) |σ - σ'|`.

For a dip time `τ` the distance `L := rdist q ∘ ray` lies in `[π-δ, π+δ]` (`δ = arccos (1-c)`; the
lower bound from the monotonicity of `cos` on `[0,π]`, the upper from `cos t = -cos (t-π)` and
`L ≤ 3π/2` obtained from the triangle inequality), so `hcoslip` applies; and
`|L σ - L σ'| ≤ |σ - σ'|` because the ray is minimising (`dipAux_ray_lip`). -/
theorem dipAux_lip
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    {p q : M} {u : TangentSpace I p} (hu : Inner.inner ℝ u u = 1) {s : ℝ} (hs0 : 0 ≤ s)
    (hsπ : s ≤ Real.pi)
    (hray : rdist (I := I) (M := M) p
      (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) = s)
    (hqp : rdist (I := I) (M := M) q p = Real.pi / 2)
    (hcoslip : ∀ A B : ℝ, A ∈ Set.Icc (Real.pi - Real.arccos (1 - c)) (Real.pi + Real.arccos (1 - c)) →
      B ∈ Set.Icc (Real.pi - Real.arccos (1 - c)) (Real.pi + Real.arccos (1 - c)) →
      |Real.cos A - Real.cos B| ≤ Real.sqrt (2 * c) * |A - B|)
    {σ σ' : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) s) (hσ' : σ' ∈ Set.Icc (0 : ℝ) s)
    (hd : fcos (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) ≤ -1 + c)
    (hd' : fcos (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet p (σ' • u)) ≤ -1 + c) :
    |fcos (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      - fcos (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet p (σ' • u))|
      ≤ Real.sqrt (2 * c) * |σ - σ'| := by
  set δ : ℝ := Real.arccos (1 - c) with hδdef
  have hδ0 : 0 ≤ δ := by rw [hδdef]; exact Real.arccos_nonneg _
  have hδπ : δ ≤ Real.pi := by rw [hδdef]; exact Real.arccos_le_pi _
  have hcosδ : Real.cos (Real.pi - δ) = -1 + c := by
    have h1 : Real.cos (Real.pi - δ) = -Real.cos δ := by
      rw [Real.cos_sub, Real.cos_pi, Real.sin_pi]; ring
    rw [h1, hδdef, Real.cos_arccos (by linarith) (by linarith)]
    ring
  have hcosplit : ∀ t : ℝ, Real.cos t = -Real.cos (t - Real.pi) := by
    intro t
    have h := Real.cos_sub t Real.pi
    rw [Real.cos_pi, Real.sin_pi] at h
    linarith [h]
  set L : ℝ → ℝ := fun τ => rdist (I := I) (M := M) q
    (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) with hLdef
  have hLnn : ∀ τ : ℝ, 0 ≤ L τ := fun τ => ENNReal.toReal_nonneg
  have hφeq : ∀ τ : ℝ, fcos (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))
      = Real.cos (L τ) := fun τ => rfl
  have hraypt : ∀ τ ∈ Set.Icc (0 : ℝ) s,
      rdist (I := I) (M := M) p (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) = τ :=
    (dipAux_ray_eq (I := I) (M := M) (cov := cov) hmet htor hu hs0 hray).1
  have hmem : ∀ {τ : ℝ}, τ ∈ Set.Icc (0 : ℝ) s →
      fcos (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) ≤ -1 + c →
      L τ ∈ Set.Icc (Real.pi - δ) (Real.pi + δ) := by
    intro τ hτ hdip
    have hcosτ : Real.cos (L τ) ≤ -1 + c := by rw [← hφeq τ]; exact hdip
    have hle3 : L τ ≤ 3 * Real.pi / 2 := by
      have htri := dipAux_triangle (I := I) (M := M) (cov := cov) hmet htor q p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))
      rw [hqp, hraypt τ hτ] at htri
      have h2 : L τ ≤ Real.pi / 2 + τ := by simpa only [hLdef] using htri
      linarith [hτ.2, hsπ]
    constructor
    · by_contra hcon
      push Not at hcon
      have h1 : Real.pi - δ ≤ Real.pi := by linarith
      have h2 := Real.cos_lt_cos_of_nonneg_of_le_pi (x := L τ) (y := Real.pi - δ)
        (hLnn τ) h1 hcon
      rw [hcosδ] at h2
      linarith
    · by_contra hcon
      push Not at hcon
      have hδπ2 : δ ≤ Real.pi / 2 := by
        rw [hδdef]
        exact Real.arccos_le_pi_div_two.mpr (by linarith)
      have h1 : L τ - Real.pi ≤ Real.pi := by linarith
      have hcon' : δ < L τ - Real.pi := by linarith
      have h2 := Real.cos_lt_cos_of_nonneg_of_le_pi (x := δ) (y := L τ - Real.pi)
        hδ0 h1 hcon'
      rw [hδdef, Real.cos_arccos (by linarith) (by linarith)] at h2
      rw [hcosplit (L τ)] at hcosτ
      linarith
  have hLdiff : |L σ - L σ'| ≤ |σ - σ'| := by
    have := dipAux_ray_lip (I := I) (M := M) (cov := cov) hmet htor (p := p) (q := q) hu hs0 hray hσ hσ'
    simpa only [hLdef] using this
  rw [hφeq σ, hφeq σ']
  calc |Real.cos (L σ) - Real.cos (L σ')|
      ≤ Real.sqrt (2 * c) * |L σ - L σ'| :=
        hcoslip (L σ) (L σ') (hmem hσ hd) (hmem hσ' hd')
    _ ≤ Real.sqrt (2 * c) * |σ - σ'| := mul_le_mul_of_nonneg_left hLdiff (Real.sqrt_nonneg _)


open Bundle in
/-- **The model comparison at the *first* dip time.**  Set `F σ := fFam … (Fin.succ k) (GExp p (σ • u))`.
If some `σ ∈ [0,s]` has `F σ ≤ -1 + c` (the ray dips into the antipodal cap of `q`), there is a least
such time `a`, and at `a` the model comparison of `Work.Diff.C.value_off_cap` still holds (with the
same error `ε₁ a`): the comparison is available on every prefix `[0, a - ε]` (where the ray is good),
and passing to the limit `ε → 0⁺` uses only the continuity of `F`.

The two non-obvious points are `a > 0` (because `F 0 = 0 > -1 + c`) and `F a = -1 + c` (otherwise the
continuity of `F` at `a` would produce a dip time `< a`). -/
theorem dip_first_compare
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    {u : TangentSpace I p} (hu : Inner.inner ℝ u u = 1) {s : ℝ} (hs0 : 0 ≤ s)
    {k : Fin (Module.finrank ℝ E)}
    (hdip : ∃ σ ∈ Set.Icc (0 : ℝ) s,
      fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) ≤ -1 + c) :
    ∃ a : ℝ, a ∈ Set.Icc (0 : ℝ) s
      ∧ fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u)) = -1 + c
      ∧ (∀ τ ∈ Set.Ioo (0 : ℝ) a,
          -1 + c < fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)))
      ∧ |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))
          - Inner.inner ℝ (e k) u * Real.sin a| ≤ ε₁ * a := by
  classical
  have hu_ne : u ≠ 0 := by
    intro h
    rw [h] at hu
    simp at hu
  -- the ray is continuous, hence so is `F`
  have hGsm : ContMDiff (modelWithCornersSelf ℝ ℝ) I ((⊤ : ENat) : WithTop ENat)
      (fun σ : ℝ ↦ Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hu_ne
  have hFcont : Continuous (fun σ : ℝ ↦ fFam (I := I) (M := M) (cov := cov) hmet p e
      (Fin.succ k) (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) :=
    (hcont (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))).comp hGsm.continuous
  have hFp0 : fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k) p = 0 := (hinit.2.2 k).1
  -- the set of dip times of the ray
  set Dip : Set ℝ := {σ : ℝ | σ ∈ Set.Icc (0 : ℝ) s ∧
    fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) ≤ -1 + c} with hDip
  have hDclosed : IsClosed Dip := by
    rw [hDip]
    exact isClosed_Icc.inter (isClosed_Iic.preimage hFcont)
  have hDsub : Dip ⊆ Set.Icc (0 : ℝ) s := fun σ hσ ↦ hσ.1
  have hDne : Dip.Nonempty := hdip
  obtain ⟨a, hamin⟩ := (isCompact_Icc.of_isClosed_subset hDclosed hDsub).exists_isLeast hDne
  have haIcc : a ∈ Set.Icc (0 : ℝ) s := hamin.1.1
  have haF : fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u)) ≤ -1 + c := hamin.1.2
  have hamin' : ∀ y : ℝ, y ∈ Dip → a ≤ y := fun y hy ↦ hamin.2 hy
  -- `a > 0` because `F 0 = 0 > -1 + c`
  have ha0 : 0 < a := by
    rcases haIcc.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have h0F : fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (0 : TangentSpace I p)) = 0 := by
        simpa using hFp0
      have h0le : (0 : ℝ) ≤ -1 + c := by
        rw [← h, zero_smul] at haF
        rw [h0F] at haF
        exact haF
      have h1 : (1 : ℝ) ≤ c := by linarith [h0le]
      linarith [hc1]
  -- `F a = -1 + c`
  have haeq : fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u)) = -1 + c := by
    refine le_antisymm haF ?_
    by_contra hcon
    push_neg at hcon
    have hev : ∀ᶠ σ in nhds a, fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) < -1 + c :=
      hFcont.continuousAt.eventually_lt_const hcon
    obtain ⟨η, hη, hηlt⟩ := Metric.eventually_nhds_iff.mp hev
    have hminpos : 0 < min (η / 2) (a / 2) :=
      lt_min (by linarith [hη]) (by linarith [ha0])
    have hσlt : a - min (η / 2) (a / 2) < a := sub_lt_self a hminpos
    have hσgt : 0 < a - min (η / 2) (a / 2) :=
      sub_pos.mpr (lt_of_le_of_lt (min_le_right _ _) (by linarith [ha0]))
    have hσmem : a - min (η / 2) (a / 2) ∈ Set.Icc (0 : ℝ) s :=
      ⟨hσgt.le, by linarith [hσlt, haIcc.2]⟩
    have hdist : dist (a - min (η / 2) (a / 2)) a < η := by
      rw [Real.dist_eq, abs_of_neg (by linarith [min_le_right (η / 2) (a / 2)] :
        a - min (η / 2) (a / 2) - a < 0)]
      linarith [min_le_left (η / 2) (a / 2)]
    exact absurd (hamin' (a - min (η / 2) (a / 2)) ⟨hσmem, (hηlt hdist).le⟩)
      (not_le.mpr hσlt)
  -- the good-prefix comparison
  have hcmp_eps : ∀ ε : ℝ, 0 < ε → ε < a →
      |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
            (Submission.GlobalExp.GExp (cov := cov) hmet p ((a - ε) • u))
          - Inner.inner ℝ (e k) u * Real.sin (a - ε)| ≤ ε₁ * (a - ε) := by
    intro ε hε hεa
    have hgood : ∀ σ ∈ Set.Icc (0 : ℝ) (a - ε),
        -1 + c < fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) := by
      intro σ hσ
      by_contra hcon
      push_neg at hcon
      have hσmem : σ ∈ Set.Icc (0 : ℝ) s := ⟨hσ.1, by linarith [hσ.2, hεa.le, haIcc.2]⟩
      have := hamin' σ ⟨hσmem, hcon⟩
      linarith [hσ.2]
    exact value_off_cap (I := I) (M := M) (cov := cov) hmet htor hε₁ hsmC hHess hinit hu
      (by linarith [hε.le, hεa.le]) hgood
  refine ⟨a, haIcc, haeq, ?_, ?_⟩
  · -- every earlier time is good
    intro τ hτ
    by_contra hcon
    push_neg at hcon
    have hτmem : τ ∈ Set.Icc (0 : ℝ) s := ⟨hτ.1.le, by linarith [hτ.2, haIcc.2]⟩
    have := hamin' τ ⟨hτmem, hcon⟩
    linarith [hτ.2]
  · -- the model comparison at `a`, by continuity
    have hgcont : Continuous (fun σ : ℝ ↦
        |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
          - Inner.inner ℝ (e k) u * Real.sin σ| - ε₁ * σ) :=
      ((hFcont.sub (continuous_const.mul Real.continuous_sin)).abs).sub
        (continuous_const.mul continuous_id)
    have hgle : ∀ σ ∈ Set.Ioo (0 : ℝ) a,
        |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
          - Inner.inner ℝ (e k) u * Real.sin σ| - ε₁ * σ ≤ 0 := by
      intro σ hσ
      have h := hcmp_eps (a - σ) (by linarith [hσ.2]) (by linarith [hσ.1])
      have hσeq : a - (a - σ) = σ := by ring
      rw [hσeq] at h
      linarith
    by_contra hcon
    push_neg at hcon
    have hpos : 0 < |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))
        - Inner.inner ℝ (e k) u * Real.sin a| - ε₁ * a := by linarith
    have hev : ∀ᶠ σ in nhds a, 0 < |fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
        - Inner.inner ℝ (e k) u * Real.sin σ| - ε₁ * σ :=
      hgcont.continuousAt.tendsto.eventually (isOpen_Ioi.mem_nhds hpos)
    obtain ⟨η, hη, hηlt⟩ := Metric.eventually_nhds_iff.mp hev
    have hminpos : 0 < min (η / 2) (a / 2) :=
      lt_min (by linarith [hη]) (by linarith [ha0])
    have hσlt : a - min (η / 2) (a / 2) < a := sub_lt_self a hminpos
    have hσgt : 0 < a - min (η / 2) (a / 2) :=
      sub_pos.mpr (lt_of_le_of_lt (min_le_right _ _) (by linarith [ha0]))
    have hdist : dist (a - min (η / 2) (a / 2)) a < η := by
      rw [Real.dist_eq, abs_of_neg (by linarith [min_le_right (η / 2) (a / 2)] :
        a - min (η / 2) (a / 2) - a < 0)]
      linarith [min_le_left (η / 2) (a / 2)]
    have h1 := hηlt hdist
    have h2 := hgle (a - min (η / 2) (a / 2)) ⟨hσgt, hσlt⟩
    linarith

open Bundle in
/-- **Elementary trigonometric inequality** (copy of `Work.Diff.C.eik_abs_cos_sub_cos_le`, which
cannot be imported here because its module also declares `inner_rgrad_mvfderiv'`): one-sided
second-order Taylor bound for `cos`,
`|cos s - cos t| ≤ (|sin t| + |s - t|)·|s - t|`. -/
lemma dmAux_abs_cos_sub_cos_le (s t : ℝ) :
    |Real.cos s - Real.cos t| ≤ (|Real.sin t| + |s - t|) * |s - t| := by
  have hsplit : |(s + t) / 2 - t| = |s - t| / 2 := by
    rw [show (s + t) / 2 - t = (s - t) / 2 by ring, abs_div]
    norm_num
  have hA : |Real.sin ((s + t) / 2)| ≤ |Real.sin t| + |s - t| / 2 := by
    have h1 : Real.sin ((s + t) / 2) = Real.sin t + (Real.sin ((s + t) / 2) - Real.sin t) := by ring
    have h2 : |Real.sin ((s + t) / 2) - Real.sin t| ≤ |s - t| / 2 := by
      have := Real.abs_sin_sub_sin_le ((s + t) / 2) t
      rwa [hsplit] at this
    rw [h1]
    exact le_trans (abs_add_le _ _) (add_le_add le_rfl h2)
  have hB : |Real.sin ((s - t) / 2)| ≤ |s - t| / 2 := by
    have h := Real.abs_sin_le_abs (x := (s - t) / 2)
    rwa [show |(s - t) / 2| = |s - t| / 2 by rw [abs_div]; norm_num] at h
  have hA0 : 0 ≤ |Real.sin t| + |s - t| / 2 := by positivity
  have hAB : |Real.sin ((s + t) / 2)| * |Real.sin ((s - t) / 2)|
      ≤ (|Real.sin t| + |s - t| / 2) * (|s - t| / 2) :=
    mul_le_mul hA hB (abs_nonneg _) hA0
  have h2 : (2 : ℝ) * |Real.sin ((s + t) / 2)| * |Real.sin ((s - t) / 2)|
      ≤ 2 * (|Real.sin t| + |s - t| / 2) * (|s - t| / 2) := by nlinarith [hAB]
  calc |Real.cos s - Real.cos t|
      = |(-2 : ℝ) * Real.sin ((s + t) / 2) * Real.sin ((s - t) / 2)| := by
        rw [Real.cos_sub_cos]
    _ = 2 * |Real.sin ((s + t) / 2)| * |Real.sin ((s - t) / 2)| := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * (|Real.sin t| + |s - t| / 2) * (|s - t| / 2) := h2
    _ = (|Real.sin t| + |s - t| / 2) * |s - t| := by ring
    _ ≤ (|Real.sin t| + |s - t|) * |s - t| := by
        have h : |Real.sin t| + |s - t| / 2 ≤ |Real.sin t| + |s - t| := by
          linarith [abs_nonneg (s - t)]
        exact mul_le_mul_of_nonneg_right h (abs_nonneg _)

open Bundle in
open Submission.GlobalExp Submission.Geodesic in
/-- **The differential of `fcos q` is bounded by `|sin (rdist q x)|·‖v‖`, with NO smoothness
hypothesis at `x`.**  If `fcos q` is not mdifferentiable at `x` its `mvfderiv` is `0` (junk value);
otherwise the bound follows from the Lipschitz property of `rdist q ·` along the rays of the
exponential map and `dmAux_abs_cos_sub_cos_le`.

This is the `MDifferentiableAt` version of `Work.Diff.C.eik_abs_mvfderiv_fcos_le`, needed because in
the dip the smoothness of `fcos q` at the tip is not available. -/
theorem dm_abs_mvfderiv_fcos_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q x : M} (v : TangentSpace I x) :
    |mvfderiv I (fcos (I := I) (M := M) q) x v|
      ≤ |Real.sin (rdist (I := I) (M := M) q x)| * ‖v‖ := by
  by_cases hd : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (fcos (I := I) (M := M) q) x
  · rcases eq_or_ne v 0 with hv | hv
    · subst hv
      rw [mvfderiv, ContinuousLinearMap.map_zero, norm_zero, mul_zero, abs_zero]
    · set γ : ℝ → M := fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (t • v) with hγdef
      have hγ0 : γ 0 = x := by
        rw [hγdef]
        simp only [zero_smul]
        exact Submission.GlobalExp.GExp_zero hmet x
      set w : TangentSpace I x := ‖v‖⁻¹ • v with hwdef
      have hwnorm : ‖w‖ = 1 := by
        rw [hwdef, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hv)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
      have hwne : w ≠ 0 := by
        rw [← norm_pos_iff, hwnorm]; norm_num
      have hγsm : ContMDiff (modelWithCornersSelf ℝ ℝ) I ((⊤ : ENat) : WithTop ENat) γ := by
        have h1 : ContMDiff (modelWithCornersSelf ℝ ℝ) I ((⊤ : ENat) : WithTop ENat)
            (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x (s • w)) :=
          Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet x hwne
        have h2 : γ = (fun s : ℝ =>
              Submission.GlobalExp.GExp (cov := cov) hmet x (s • w))
            ∘ (fun s : ℝ => s * ‖v‖) := by
          funext s
          rw [hγdef]
          simp only [Function.comp_apply]
          have hsm : s • v = (s * ‖v‖) • w := by
            rw [hwdef, smul_smul, mul_assoc,
              mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), mul_one]
          rw [hsm]
        rw [h2]
        exact h1.comp (contMDiff_id.mul contMDiff_const)
      have hγmd : MDifferentiableAt (modelWithCornersSelf ℝ ℝ) I γ 0 :=
        (hγsm 0).mdifferentiableAt (by simp)
      have hvel : mfderiv (modelWithCornersSelf ℝ ℝ) I γ 0 (1 : ℝ) = v := by
        rw [← curveVelocity_apply]
        exact Submission.GExpVelocity.curveVelocity_GExp_smul_zero hmet x hv
      have hfmd : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
          (fcos (I := I) (M := M) q) x := hd
      have hFmd : MDifferentiableAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
          ((fcos (I := I) (M := M) q) ∘ γ) 0 := (hγ0 ▸ hfmd).comp 0 hγmd
      have hchain : mvfderiv I (fcos (I := I) (M := M) q) x v
          = deriv ((fcos (I := I) (M := M) q) ∘ γ) 0 := by
        have h := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
          (g := fcos (I := I) (M := M) q) (γ := γ) (t := 0) (hγ0 ▸ hfmd) hγmd
        have h2 : (mvfderiv I (fcos (I := I) (M := M) q) (γ 0))
            ((mfderiv (modelWithCornersSelf ℝ ℝ) I γ 0) (1 : ℝ))
              = (mvfderiv I (fcos (I := I) (M := M) q) x) v := by
          rw [hγ0]
          exact congrArg (fun w => (mvfderiv I (fcos (I := I) (M := M) q) x) w) hvel
        exact h2.symm.trans h
      have hD : HasDerivAt ((fcos (I := I) (M := M) q) ∘ γ)
          (deriv ((fcos (I := I) (M := M) q) ∘ γ) 0) 0 :=
        (mdifferentiableAt_iff_differentiableAt.mp hFmd).hasDerivAt
      have hlip : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          |rdist (I := I) (M := M) q (γ t) - rdist (I := I) (M := M) q x| ≤ t * ‖v‖ := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht0 : 0 ≤ t := le_of_lt ht
        have h3 : rdist (I := I) (M := M) x (γ t) ≤ t * ‖v‖ := by
          show rdist (I := I) (M := M) x
            (Submission.GlobalExp.GExp (cov := cov) hmet x (t • v)) ≤ t * ‖v‖
          exact dipAux_ray_smul (I := I) (M := M) (cov := cov) hmet x v ht0
        have h1 : rdist (I := I) (M := M) q (γ t) - rdist (I := I) (M := M) q x
            ≤ rdist (I := I) (M := M) x (γ t) := by
          have h := dipAux_triangle (I := I) (M := M) (cov := cov) hmet htor q x (γ t)
          linarith
        have h2 : rdist (I := I) (M := M) q x - rdist (I := I) (M := M) q (γ t)
            ≤ rdist (I := I) (M := M) x (γ t) := by
          have h := dipAux_triangle (I := I) (M := M) (cov := cov) hmet htor q (γ t) x
          rw [dipAux_comm (I := I) (M := M) (γ t) x] at h
          linarith
        rw [abs_sub_le_iff]
        exact ⟨h1.trans h3, by linarith⟩
      have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          |((fcos (I := I) (M := M) q) ∘ γ) (0 + t) - ((fcos (I := I) (M := M) q) ∘ γ) 0|
            ≤ (|Real.sin (rdist (I := I) (M := M) q x)| + t * ‖v‖) * (t * ‖v‖) := by
        filter_upwards [hlip, self_mem_nhdsWithin] with t ht htg
        have ht0 : 0 ≤ t := le_of_lt htg
        have htrig := dmAux_abs_cos_sub_cos_le (rdist (I := I) (M := M) q (γ t))
          (rdist (I := I) (M := M) q x)
        have hconv : ((fcos (I := I) (M := M) q) ∘ γ) (0 + t)
            - ((fcos (I := I) (M := M) q) ∘ γ) 0
            = Real.cos (rdist (I := I) (M := M) q (γ t))
              - Real.cos (rdist (I := I) (M := M) q x) := by
          simp only [Function.comp_apply, fcos, zero_add, hγ0]
        rw [hconv]
        refine htrig.trans ?_
        exact mul_le_mul
          (by linarith [abs_nonneg (rdist (I := I) (M := M) q (γ t)
            - rdist (I := I) (M := M) q x)])
          ht (abs_nonneg _)
          (add_nonneg (abs_nonneg _) (mul_nonneg ht0 (norm_nonneg v)))
      have hlim1 : Filter.Tendsto
          (fun t : ℝ =>
            |t⁻¹ • (((fcos (I := I) (M := M) q) ∘ γ) (0 + t)
              - ((fcos (I := I) (M := M) q) ∘ γ) 0)|)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds |deriv ((fcos (I := I) (M := M) q) ∘ γ) 0|) :=
        (continuous_abs.tendsto _).comp (by simpa using hD.tendsto_slope_zero_right)
      have hlim2 : Filter.Tendsto
          (fun t : ℝ => (|Real.sin (rdist (I := I) (M := M) q x)| + t * ‖v‖) * ‖v‖)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (|Real.sin (rdist (I := I) (M := M) q x)| * ‖v‖)) := by
        have ht : Filter.Tendsto (fun t : ℝ => t) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) :=
          Filter.tendsto_id.mono_left nhdsWithin_le_nhds
        have h1 : Filter.Tendsto
            (fun t : ℝ => |Real.sin (rdist (I := I) (M := M) q x)| + t * ‖v‖)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (|Real.sin (rdist (I := I) (M := M) q x)| + 0 * ‖v‖)) :=
          tendsto_const_nhds.add (ht.mul_const ‖v‖)
        simpa using h1.mul_const ‖v‖
      have hbound : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          |t⁻¹ • (((fcos (I := I) (M := M) q) ∘ γ) (0 + t)
              - ((fcos (I := I) (M := M) q) ∘ γ) 0)|
            ≤ (|Real.sin (rdist (I := I) (M := M) q x)| + t * ‖v‖) * ‖v‖ := by
        filter_upwards [hev, self_mem_nhdsWithin] with t ht htg
        have htpos : 0 < t := htg
        have htne : t ≠ 0 := ne_of_gt htpos
        rw [zero_add] at ht
        have h1 : |t⁻¹ • (((fcos (I := I) (M := M) q) ∘ γ) (0 + t)
              - ((fcos (I := I) (M := M) q) ∘ γ) 0)|
            = t⁻¹ * |((fcos (I := I) (M := M) q) ∘ γ) t
                - ((fcos (I := I) (M := M) q) ∘ γ) 0| := by
          rw [smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr htpos), zero_add]
        rw [h1]
        calc t⁻¹ * |((fcos (I := I) (M := M) q) ∘ γ) t
              - ((fcos (I := I) (M := M) q) ∘ γ) 0|
            ≤ t⁻¹ * ((|Real.sin (rdist (I := I) (M := M) q x)| + t * ‖v‖) * (t * ‖v‖)) :=
              mul_le_mul_of_nonneg_left ht (by positivity)
          _ = (|Real.sin (rdist (I := I) (M := M) q x)| + t * ‖v‖) * ‖v‖ := by
              field_simp
      have hmain := le_of_tendsto_of_tendsto hlim1 hlim2 hbound
      rw [hchain]
      exact hmain
  · have h0 : mvfderiv I (fcos (I := I) (M := M) q) x v = 0 := by
      rw [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hd, ContinuousLinearMap.comp_zero]
      rfl
    rw [h0, abs_zero]
    positivity

/-!
## STATUS (session N+5): the target is reduced to TWO geometric inputs

Write `F σ := fFam … (Fin.succ k) (GExp p (σ • u)) = fcos q (γ σ)` with `γ σ := GExp p (σ • u)`,
`β := ⟪e k, u⟫`, `C := 100 (finrank ℝ E + 2)(ε₁π + α + √c)`, `δ := arccos (1-c)`.

**Proved in this file (sorry-free).**  The algebraic kernels of the reduction:

* `value_from_anchor` / `deriv_from_anchor` — *anchor form*: if the ODE comparison holds on `[b,s]`
  and the anchor state matches the model (`F b ≈ β sin b`, `F' b ≈ β cos b`), then both conjuncts
  hold at `s`.  (`b = 0` has an *exact* anchor state: `F 0 = 0`, `F' 0 = β`.)
* `value_dip_of_loc` — *the tip inside the antipodal cap* (`F s ≤ -1+c` implies
  `cos (rdist q x) ∈ [-1,-1+c]`, and with `β ≤ -cos α`, `|β| ≤ 1` alone:
  `|cos L - β sin s| ≤ c + (1-cos α) + (1-sin s)`).  **No geometric input is needed here** beyond
  the bound `s ≤ π/2 + T` on the *location*.
* `dip_arith` — the numerical endgame: `|s - π/2| ≤ 300 (√c + ε₁π)` gives
  `c + (1-cos α) + (1-sin s) ≤ 100 N (ε₁π + α + √c)` (for `3 ≤ N`).

**The two remaining inputs.**  Everything else is mechanical (`Work.Diff.C.value_off_cap`,
`Work.Diff.C.deriv_off_cap` for the no-dip case; `Work.Diff.C.dip_first_compare` for the comparison
at the *first* dip time; `Work.Diff.C.dm_abs_mvfderiv_fcos_le` for the derivative conjunct at a dip
point):

* **(GI-1) `dip_loc` — the location of the dip.**  Every `σ ∈ [0,s]` with `F σ ≤ -1+c` satisfies
  `σ ≤ π/2 + 128 (√c + ε₁π)` (equivalently `|σ - π/2| ≤ 300 (√c + ε₁π)`).  This is the *far-ball
  diameter* chapter: `Work.Diff.C.dip_far_ball` (`diam{z : π-δ ≤ rdist q z} ≤ 256(√c + ε₁π)`,
  proved modulo the sphere-size bound `Work.Diff.C.far_sphere_size`) combined with the elementary
  entry bound `π/2 - δ ≤ σ` (triangle inequality) and `rdist (γ σ) (γ σ') = |σ - σ'|`.
  *This input alone settles the case `F s ≤ -1+c`* (via `value_dip_of_loc` + `dip_arith`), and also
  the *value* part of the anchor state at the last dip time (Lipschitz transport from the first dip
  time, where the comparison is known).
* **(GI-2) `dip_anchor` — the state at the last dip time.**  If `F s > -1+c` and `b` is the last dip
  time (`F b = -1+c`, `F > -1+c` on `(b,s]`), then the restart comparison on `[b,s]` holds
  (`|F s - (F b cos(s-b) + F' b sin(s-b))| ≤ ε₁(s-b)` and the derivative version — provable from
  `hHess`/`hsmC` by `Work.Diff.C.ode_compare_halfopen` once the ray is translated to the base point
  `γ b`), **and** the anchor state matches the model:
  `|F b - β sin b| ≤ C/8` (implied by (GI-1)) and `|F' b - β cos b| ≤ C/8`.
  The missing half is the *radiality of the exit*: `F' b = -sin δ · λ` with `λ = (d/dσ) rdist q (γ σ)|_b`
  the cosine of the angle between the ray and the radial direction, and one needs `|λ| ≥ 1 - O(C)`,
  i.e. the ray leaves the far ball perpendicularly to it (true in the model, where the ray passes
  through the antipode of `q`).

**Why the sphere-size bound is reachable without the cut-locus input `hminW`** (recorded for the
next session): on the good region `{fcos q > -1+c}` the level sets of `f := fcos q` are smooth
(`hsmC`) with `|∇f|² = 1-f²` (`hgrad`, by continuity on the closed region), so the normalised
gradient `ν = ∇f/|∇f|` satisfies `∇_ν ν = 0` (a pure computation from the two identities):
its flow lines are unit-speed geodesics, they are precisely the rays from `q`, and the variation
field `Z` of the flow satisfies `Z' = II(Z)` with `II = -Hess f/|∇f|` **restricted to the level
sets** — which is `cot t · id + O(ε₁/sin t)` directly from `hHess`, with no smoothness of
`rdist q` and no cut-locus input.  Feeding that shape-operator bound into the Sturm comparison
`Work.Diff.C.jld_modulus_le_sin` (proved, hypotheses `hbridge`/`horth`/`hshape`) yields the
sphere-size bound `far_sphere_size` needs.
-/

set_option maxHeartbeats 800000

open Bundle in
/-- **Anchor form of the value conjunct.**  If the restart comparison at the anchor `b` holds and
the anchor state matches the model, then the value conjunct holds at `s`. -/
theorem value_from_anchor {F Fb Fb' β b s ε C1 C2 C : ℝ}
    (hcmp : |F - (Fb * Real.cos (s - b) + Fb' * Real.sin (s - b))| ≤ ε)
    (hA : |Fb - β * Real.sin b| ≤ C1) (hB : |Fb' - β * Real.cos b| ≤ C2)
    (hsum : ε + C1 + C2 ≤ C) :
    |F - β * Real.sin s| ≤ C := by
  have h1 : |(Fb - β * Real.sin b) * Real.cos (s - b)| ≤ C1 := by
    rw [abs_mul]
    calc |Fb - β * Real.sin b| * |Real.cos (s - b)| ≤ |Fb - β * Real.sin b| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |Fb - β * Real.sin b| := mul_one _
      _ ≤ C1 := hA
  have h2 : |(Fb' - β * Real.cos b) * Real.sin (s - b)| ≤ C2 := by
    rw [abs_mul]
    calc |Fb' - β * Real.cos b| * |Real.sin (s - b)| ≤ |Fb' - β * Real.cos b| * 1 :=
          mul_le_mul_of_nonneg_left (by
            rw [abs_le]; exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩) (abs_nonneg _)
      _ = |Fb' - β * Real.cos b| := mul_one _
      _ ≤ C2 := hB
  have hid : F - β * Real.sin s
      = (F - (Fb * Real.cos (s - b) + Fb' * Real.sin (s - b)))
        + (Fb - β * Real.sin b) * Real.cos (s - b)
        + (Fb' - β * Real.cos b) * Real.sin (s - b) := by
    rw [show Real.sin s = Real.sin (b + (s - b)) by ring_nf, Real.sin_add]; ring
  calc |F - β * Real.sin s|
      = |(F - (Fb * Real.cos (s - b) + Fb' * Real.sin (s - b)))
        + (Fb - β * Real.sin b) * Real.cos (s - b)
        + (Fb' - β * Real.cos b) * Real.sin (s - b)| := by rw [hid]
    _ ≤ |F - (Fb * Real.cos (s - b) + Fb' * Real.sin (s - b))|
        + |(Fb - β * Real.sin b) * Real.cos (s - b)|
        + |(Fb' - β * Real.cos b) * Real.sin (s - b)| := abs_add_three _ _ _
    _ ≤ ε + C1 + C2 := by linarith
    _ ≤ C := hsum

open Bundle in
/-- **Anchor form of the derivative conjunct.**  Same as `value_from_anchor`, for the radial
derivative `F'` of the ray. -/
theorem deriv_from_anchor {Fd Fb Fb' β b s ε C1 C2 C : ℝ}
    (hcmp : |Fd - (-(Fb * Real.sin (s - b)) + Fb' * Real.cos (s - b))| ≤ ε)
    (hA : |Fb - β * Real.sin b| ≤ C1) (hB : |Fb' - β * Real.cos b| ≤ C2)
    (hsum : ε + C1 + C2 ≤ C) :
    |Fd - β * Real.cos s| ≤ C := by
  have h1 : |(Fb - β * Real.sin b) * Real.sin (s - b)| ≤ C1 := by
    rw [abs_mul]
    calc |Fb - β * Real.sin b| * |Real.sin (s - b)| ≤ |Fb - β * Real.sin b| * 1 :=
          mul_le_mul_of_nonneg_left (by
            rw [abs_le]; exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩) (abs_nonneg _)
      _ = |Fb - β * Real.sin b| := mul_one _
      _ ≤ C1 := hA
  have h2 : |(Fb' - β * Real.cos b) * Real.cos (s - b)| ≤ C2 := by
    rw [abs_mul]
    calc |Fb' - β * Real.cos b| * |Real.cos (s - b)| ≤ |Fb' - β * Real.cos b| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |Fb' - β * Real.cos b| := mul_one _
      _ ≤ C2 := hB
  have hid : Fd - β * Real.cos s
      = (Fd - (-(Fb * Real.sin (s - b)) + Fb' * Real.cos (s - b)))
        + (-(Fb - β * Real.sin b)) * Real.sin (s - b)
        + (Fb' - β * Real.cos b) * Real.cos (s - b) := by
    rw [show Real.cos s = Real.cos (b + (s - b)) by ring_nf, Real.cos_add]; ring
  calc |Fd - β * Real.cos s|
      = |(Fd - (-(Fb * Real.sin (s - b)) + Fb' * Real.cos (s - b)))
        + (-(Fb - β * Real.sin b)) * Real.sin (s - b)
        + (Fb' - β * Real.cos b) * Real.cos (s - b)| := by rw [hid]
    _ ≤ |Fd - (-(Fb * Real.sin (s - b)) + Fb' * Real.cos (s - b))|
        + |-((Fb - β * Real.sin b)) * Real.sin (s - b)|
        + |(Fb' - β * Real.cos b) * Real.cos (s - b)| := abs_add_three _ _ _
    _ ≤ ε + C1 + C2 := by
        have h3 : |-(Fb - β * Real.sin b) * Real.sin (s - b)| ≤ C1 := by
          rw [show -(Fb - β * Real.sin b) * Real.sin (s - b)
            = -((Fb - β * Real.sin b) * Real.sin (s - b)) by ring, abs_neg]
          exact h1
        linarith [hcmp, h3, h2]
    _ ≤ C := hsum



open Bundle in
/-- **The tip inside the antipodal cap.**  If `cos L ≤ -1 + c` (the tip is in the cap) and
`β ≤ -cos α` with `|β| ≤ 1`, then `|cos L - β sin s| ≤ c + (1-cos α) + (1-sin s)`. -/
theorem value_dip_of_loc {L s β α c C : ℝ}
    (hcos_le : Real.cos L ≤ -1 + c) (hcos_ge : -1 ≤ Real.cos L)
    (hβ0 : β ≤ 0) (hβ1 : -1 ≤ β) (hβcos : Real.cos α ≤ -β) (hcosα0 : 0 ≤ Real.cos α)
    (hsin0 : 0 ≤ Real.sin s)
    (hmain : c + (1 - Real.cos α) + (1 - Real.sin s) ≤ C) :
    |Real.cos L - β * Real.sin s| ≤ C := by
  have hb : |β| = -β := abs_of_nonpos hβ0
  have h1 : |Real.cos L + 1| ≤ c := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |1 + β * Real.sin s| ≤ (1 - Real.sin s) + (1 - Real.cos α) := by
    have hs1 : Real.sin s ≤ 1 := Real.sin_le_one s
    have hb1 : -β ≤ 1 := by linarith
    have h0 : 0 ≤ 1 + β * Real.sin s := by nlinarith
    rw [abs_of_nonneg h0]
    have h3 : Real.cos α * Real.sin s ≤ (-β) * Real.sin s :=
      mul_le_mul_of_nonneg_right hβcos hsin0
    nlinarith
  have hid : Real.cos L - β * Real.sin s
      = (Real.cos L + 1) + (-(1 + β * Real.sin s)) := by ring
  have h5 : |(Real.cos L + 1) + (-(1 + β * Real.sin s))|
      ≤ |Real.cos L + 1| + |1 + β * Real.sin s| := by
    have h := abs_add_le (Real.cos L + 1) (-(1 + β * Real.sin s))
    rwa [abs_neg] at h
  calc |Real.cos L - β * Real.sin s|
      = |(Real.cos L + 1) + (-(1 + β * Real.sin s))| := by rw [hid]
    _ ≤ |Real.cos L + 1| + |1 + β * Real.sin s| := h5
    _ ≤ c + ((1 - Real.sin s) + (1 - Real.cos α)) := add_le_add h1 h2
    _ = c + (1 - Real.cos α) + (1 - Real.sin s) := by ring
    _ ≤ C := hmain

open Bundle in
/-- **The numerical endgame of the cap case.**  If `|s - π/2| ≤ 300 (√c + ε₁π)`, then
`c + (1-cos α) + (1-sin s) ≤ 100 N (ε₁π + α + √c)` for `3 ≤ N` (in the application
`N = (finrank ℝ E : ℝ) + 2`). -/
theorem dip_arith {N c ε₁ α s : ℝ} (hN : 3 ≤ N) (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hε₁ : 0 ≤ ε₁) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hnum1 : 3 * c ≤ 1 - Real.cos α) (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsT : s ≤ Real.pi / 2 + 300 * (Real.sqrt c + ε₁ * Real.pi))
    (hsT' : Real.pi / 2 - 300 * (Real.sqrt c + ε₁ * Real.pi) ≤ s) :
    c + (1 - Real.cos α) + (1 - Real.sin s)
      ≤ 100 * N * (ε₁ * Real.pi + α + Real.sqrt c) := by
  have hc0 : 0 ≤ c := le_of_lt hc
  have hsc : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
  have hscc : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0
  have hπε : 0 ≤ ε₁ * Real.pi := mul_nonneg hε₁ Real.pi_pos.le
  have hπεc : ε₁ * Real.pi < c / 4 := by linarith [hnum2]
  have hsc1 : Real.sqrt c ≤ 1 / 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 2)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hπε' : ε₁ * Real.pi ≤ Real.sqrt c / 8 := by
    have h1 : c / 4 ≤ Real.sqrt c / 8 := by
      have h3 : Real.sqrt c / 4 ≤ (1:ℝ) / 8 := by linarith
      have h5 : Real.sqrt c * (Real.sqrt c / 4) ≤ Real.sqrt c * ((1:ℝ)/8) :=
        mul_le_mul_of_nonneg_left h3 hsc
      have h6 : Real.sqrt c * (Real.sqrt c / 4) = c / 4 := by nlinarith [hscc]
      have h7 : Real.sqrt c * ((1:ℝ)/8) = Real.sqrt c / 8 := by ring
      linarith [h5, h6, h7]
    linarith [hπεc, h1]
  have hA2 : 1 - Real.cos α ≤ α ^ 2 / 2 := by
    have h := Real.one_sub_sq_div_two_le_cos (x := α)
    linarith
  have h3c : 3 * c ≤ α ^ 2 / 2 := by linarith [hnum1, hA2]
  have hα0 : 0 ≤ α := le_of_lt hα
  have hα6 : Real.sqrt (6 * c) ≤ α := by
    have h6 : Real.sqrt (6 * c) ^ 2 = 6 * c := Real.sq_sqrt (by linarith)
    have h7 : 6 * c ≤ α ^ 2 := by linarith [h3c]
    nlinarith [h6, hα0, h7, Real.sqrt_nonneg (6 * c)]
  have hs6 : 2.44 ≤ Real.sqrt 6 := by
    have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    nlinarith [h6, Real.sqrt_nonneg (6:ℝ)]
  have hsq6c : Real.sqrt (6 * c) = Real.sqrt 6 * Real.sqrt c :=
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 6) c
  set C : ℝ := 100 * N * (ε₁ * Real.pi + α + Real.sqrt c) with hCdef
  have hN0 : 0 ≤ N := by linarith
  have hkey : 344 * N * Real.sqrt c ≤ C := by
    have h6 : (3.44 : ℝ) * Real.sqrt c ≤ Real.sqrt 6 * Real.sqrt c + Real.sqrt c := by
      have h7 : (3.44 : ℝ) ≤ Real.sqrt 6 + 1 := by linarith
      nlinarith [hsc, h7]
    have h7 : Real.sqrt 6 * Real.sqrt c ≤ α := by rw [← hsq6c]; exact hα6
    have h8 : (3.44 : ℝ) * Real.sqrt c ≤ ε₁ * Real.pi + α + Real.sqrt c := by linarith
    have h9 : 0 ≤ 100 * N := by linarith
    have h10 : (344:ℝ) * N * Real.sqrt c = 100 * N * ((3.44 : ℝ) * Real.sqrt c) := by ring
    rw [hCdef, h10]
    exact mul_le_mul_of_nonneg_left h8 h9
  have hCN' : 1032 * Real.sqrt c ≤ C := by
    have h1 : 344 * N * Real.sqrt c ≥ 344 * 3 * Real.sqrt c := by nlinarith [hN, hsc]
    linarith [hkey, h1]
  have hp1 : c ≤ C / 3 := by
    have h1 : 3 * c ≤ 1032 * Real.sqrt c := by nlinarith [hscc, hsc, hc1]
    linarith [hCN', h1]
  have hp2 : 1 - Real.cos α ≤ C / 3 := by
    have h3 : α ^ 2 / 2 ≤ 100 * N * α / 3 := by nlinarith [hα1, hN, hα0]
    have h4 : 100 * N * α / 3 ≤ C / 3 := by
      rw [hCdef]; nlinarith [hπε, hsc, hN0]
    linarith [hA2, h3, h4]
  have hp3 : 1 - Real.sin s ≤ C / 3 := by
    have h3 : 1 - Real.sin s ≤ (s - Real.pi / 2) ^ 2 / 2 := by
      have h1 : 1 - (s - Real.pi / 2) ^ 2 / 2 ≤ Real.cos (s - Real.pi / 2) :=
        Real.one_sub_sq_div_two_le_cos
      rw [Real.cos_sub_pi_div_two] at h1
      linarith
    have h4 : 1 - Real.sin s ≤ 2 := by
      have := Real.neg_one_le_sin s
      linarith
    by_cases hcase : (s - Real.pi / 2) ^ 2 / 2 ≤ C / 3
    · linarith
    · have hcase' : C / 3 < (s - Real.pi / 2) ^ 2 / 2 := lt_of_not_ge hcase
      have h5 : (s - Real.pi / 2) ^ 2 ≤ (300 * (Real.sqrt c + ε₁ * Real.pi)) ^ 2 := by
        have habs : |s - Real.pi / 2| ≤ 300 * (Real.sqrt c + ε₁ * Real.pi) := by
          rw [abs_le]; exact ⟨by linarith, by linarith⟩
        have h := mul_self_le_mul_self (abs_nonneg (s - Real.pi / 2)) habs
        rw [abs_mul_abs_self] at h
        simpa [pow_two] using h
      have h7 : (300 * (Real.sqrt c + ε₁ * Real.pi)) ^ 2 ≤ 113907 * c := by
        have h1 : 300 * (Real.sqrt c + ε₁ * Real.pi) ≤ (675 / 2) * Real.sqrt c := by
          linarith [hπε', hsc]
        have h2 : (300 * (Real.sqrt c + ε₁ * Real.pi)) * (300 * (Real.sqrt c + ε₁ * Real.pi))
            ≤ ((675 / 2) * Real.sqrt c) * ((675 / 2) * Real.sqrt c) :=
          mul_le_mul h1 h1 (by linarith) (by linarith)
        have h3 : ((675 / 2) * Real.sqrt c) * ((675 / 2) * Real.sqrt c) = (455625 / 4) * c := by
          nlinarith [hscc]
        have h4 : (300 * (Real.sqrt c + ε₁ * Real.pi)) ^ 2
            = (300 * (Real.sqrt c + ε₁ * Real.pi)) * (300 * (Real.sqrt c + ε₁ * Real.pi)) := by
          ring
        rw [h4]
        linarith [h2, h3]
      have h9 : C / 3 < 56954 * c := by linarith [hcase', h5, h7]
      have h12 : 1032 * Real.sqrt c < 170862 * c := by linarith [hCN', h9]
      have h13 : 0 < Real.sqrt c := Real.sqrt_pos_of_pos hc
      have h14 : c = Real.sqrt c * Real.sqrt c := by nlinarith [hscc]
      have h15 : 1032 < 170862 * Real.sqrt c := by
        have hfac : 170862 * c - 1032 * Real.sqrt c
            = Real.sqrt c * (170862 * Real.sqrt c - 1032) := by nlinarith [hscc]
        have hpos : 0 < 170862 * c - 1032 * Real.sqrt c := by linarith [h12]
        rw [hfac] at hpos
        have := pos_of_mul_pos_right hpos hsc
        linarith
      have h16 : 0.0181 < N * Real.sqrt c := by nlinarith [h15, hN, hsc]
      have h17 : 6 ≤ C := by nlinarith [h16, hkey]
      linarith [h4, h17]
  linarith [hp1, hp2, hp3]

open Bundle in
/-- ROUTE.  `q := qpt hmet p e (Fin.succ k)`, `x := GExp p (s • u)`; `d(p,q) = π/2` (`InitData`), so the
model of `F σ := fcos q (GExp p (σ • u))` at `σ = 0` is `F 0 = 0`, `F' 0 = ⟪e k, u⟫ =: β`, i.e. the model
of `F` is `σ ↦ β sin σ`.  The claim is that this model holds at `σ = s` (value and radial derivative)
even when `fcos q x ≤ -1+c`, i.e. when `F` dips below the level `-1+c` where `hHess`/`hsmC` for the
centre `q` stop applying.

This is the *strengthened* form of `Work.Diff.C.dip_equator_crux` (which only bounds `|Real.cos s|` in
the dip case): prove this one and the crux follows.

Same route as described there: pass to a minimising geodesic `η` from `q` to `x` (length
`L = d(q,x) ∈ [π-δ,π+δ]`, `δ = arccos(1-c)`) and the function `h t := fcos p (η t) = cos (rdist p (η t))`:
`h 0 = 0`, `h L = Real.cos s`, and `h'' = -h + E`, `|E| ≤ ε₁`, `|h'| ≤ 1` wherever `h > -1+c`, so `h` is
an approximate sinusoid with amplitude `≤ 1` and the model comparison integrates to
`Real.cos s = A cos L + B sin L + O(ε₁)` with `A = 0`, `B = h'(0)`; `|B| ≤ 1`.  Hence the value conjunct
reduces to the *geometry* of the diagram `p — q — x` (the relative position of the tip `x` at distance
`L ≈ π` from `q` and `s` from `p`), which is where the hypothesis `hbad` (`β ≤ -cos α`, i.e. the ray from
`p` points almost antipodally to `q`) is used: the tip is `q`-antipodal, so it is `p`-equatorial.
The derivative conjunct uses the same integration for `h'` together with the chain rule
`h' t = ⟪∇ fcos p (η t), η'(t)⟫` and the direction of `η'(0)` (the geodesic from `p` through `q` in
direction `e k`).

Any constant below `100 (n+2) (ε₁π + α + √c)` is acceptable.

⚠️ ROUTE CORRECTION (see also the STATUS note below the imports).  The sentence "the set
`{h ≤ -1+c}` is at most an isolated set of tangency points" (in the ROUTE of
`Work.Diff.C.dip_equator_crux`, reused here) is **false**: for the model `β sin σ` with
`β ≤ -cos α` the dip is the *interval* `{σ : |β| sin σ ≥ 1-c}`, of length `2δ > 0` with
`δ = arccos (1-c)`, and along the round sphere the same holds for the function `h` itself.  The dip
therefore can *not* be crossed by "integrating through tangency points"; the model comparison in the
dip case needs the *boundary* case of Toponogov's hinge comparison for `sec ≥ 1` (equivalently: the
antipodal cap `{y : d(q,y) ≥ π-δ}` has diameter `≤ 2δ + O(ε₁)`), which is not available in the
workspace.  This is isolated as `Work.Diff.C.dip_exit_time` and `Work.Diff.C.cap_diameter` in
`Submission/Work/Diff/C/dip_cap_exit.lean`. -/
theorem dip_model_through
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {α c ε₁ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hε₁ : 0 ≤ ε₁) (hnum1 : 3 * c ≤ 1 - Real.cos α) (hnum2 : 4 * ε₁ * Real.pi < c)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    (hdiam : ∀ y : M, rdist (I := I) (M := M) p y ≤ Real.pi)
    {u : TangentSpace I p} (hu : Inner.inner ℝ u u = 1) {s : ℝ} (hs0 : 0 ≤ s)
    (hsπ : s ≤ Real.pi)
    (hray : rdist (I := I) (M := M) p
        (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)) = s)
    {k : Fin (Module.finrank ℝ E)} (hbad : Inner.inner ℝ (e k) u ≤ -Real.cos α)
    :
    (|fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u))
        - Inner.inner ℝ (e k) u * Real.sin s|
      ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c))
    ∧
    (|Inner.inner ℝ
        (rgrad (I := I) (M := M)
          (fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k))
          (Submission.GlobalExp.GExp (cov := cov) hmet p (s • u)))
        (Submission.Geodesic.curveVelocity
          (fun σ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) s)
        - Inner.inner ℝ (e k) u * Real.cos s|
      ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c)) := by
  sorry

end Work.Diff.C

import Mathlib
import Submission.Work.SimplyConnected.ABS.RegularPieceDefs
import Submission.Work.SimplyConnected.ABS.exists_finite_family_covering_interiors
import Submission.Work.SimplyConnected.ABS.exists_regularPiece_of_greenOn_modulus
import Submission.Work.SimplyConnected.ABS.exists_isModulusOn_of_isGreenOn
import Submission.Work.SimplyConnected.ABS.exists_biholomorphicOn_of_greenOn_modulus
import Submission.Work.SimplyConnected.ABS.exists_isGreenOn_of_barriers
import Submission.Commons.Topology.Surface.exists_locallyFinite_disk_tiling
import Submission.Work.SimplyConnected.ABS.linear_negative_of_no_opposite_pair
import Submission.Work.SimplyConnected.ABS.closedBall_innerHalfPlane
import Submission.Work.SimplyConnected.ABS.exists_sector_subset_of_open_convexCone
import Submission.Work.SimplyConnected.ABS.chartBall_transport
import Submission.Work.SimplyConnected.ABS.exists_chart_with_room_locallyBiholomorphic
import Submission.Work.Modulus.Main
import Submission.Work.Parabolic.All

/-
## Where this lemma sits in the fleet's plan (session reconnaissance, update)

**FINAL STATE OF THIS MODULE (end of the session).**  `regularPiece_core` now *has a complete
proof* in this file:

    regularPiece_core hX K hK
      = regularPiece_core_of_chart_with_room hX
          (Work.SimplyConnected.ABS.exists_chart_with_room_locallyBiholomorphic hX K hK)

i.e. the target is reduced, with no remaining formalisation gap in this file, to the single
statement proved in the companion module
`Submission/Work/SimplyConnected/ABS/exists_chart_with_room_locallyBiholomorphic.lean`:
*every compact `K` lies in a compatible chart `φ` with room* (`K ⊆ φ.source`,
`φ '' K ⊆ ball c ρ`, `closedBall c ρ ⊆ φ.target`) *whose chart representatives
`φ ∘ (chartAt ℂ p).symm` are analytic with non-vanishing derivative*.  In that module the
**hyperbolic case** (a unit-pole Green function on `X`) is proved outright, and the only `remaining
`sorry` is the **parabolic case** (no Green function), which is the ABS/Mori input (Anghel--Bruin--
Stan Theorem 1: a simply connected non-compact Riemann surface embeds biholomorphically into `ℂ`).
Consequently `#print axioms Work.SimplyConnected.ABS.regularPiece_core` =
`[propext, sorryAx, Classical.choice, Quot.sound]`, the `sorryAx` coming from exactly that one
place: proving the parabolic case closes this lemma, `exists_isRegularPiece_superset` and the whole
ABS chain at once.

The endgame used here is `exists_regularPiece_of_chart_with_room` (below), which generalises the
older `exists_regularPiece_of_atlasChartBall` by dropping atlas membership in favour of the
local-biholomorphism clause, and which derives the sector condition at a frontier point by
transporting round geometry from `φ`'s chart to the atlas chart at the point through the quadratic
Taylor remainder (`sectorComplement_of_quadraticRemainder`).  The clause is *necessary*: a plain
chart with room does not give the cone condition (see item 3 below).


This file's target `regularPiece_core` is the *designated geometric core* of the workspace's
regional route to uniformization.  The exact dependency structure, as read off the tree:

* `Submission/Work/SimplyConnected/ABS/exists_isRegularPiece_superset.lean` proves, **from
  `regularPiece_core` together with the (proved) `barrier_of_sector`**, that every compact `K`
  lies in a *regular piece* (`RegPiece`: open, `≅` the open unit disc, compact closure, connected
  frontier of the closure, and a barrier at every frontier point);
* `Submission/Work/SimplyConnected/ABS/exists_injective_holomorphic_of_isSimplyConnected_noncompact.lean`
  (ABS Theorem 1, the "planarity" input of the parabolic branch) is proved from the regular pieces
  via `exists_isGreenOn_of_barriers` ⟹ `exists_isModulusOn_of_isGreenOn` ⟹
  `exists_biholomorphicOn_of_greenOn_modulus` (disc exhaustion) plus the normal-family extraction
  `Work.SimplyConnected.Parabolic.exists_injective_holomorphic_of_univalent_family`;
* conversely the hyperbolic branch is complete here (`regularPiece_core_of_unitGreenFunction`), and
  `regularPiece_core_of_dichotomy` turns the uniformization disjunction `X ≅ ℂ ∨ X ≅ ℍ` into the
  target — but `regularPiece_core ⟹` (fleet's chain) `⟹ X ≅ ℂ ∨ X ≅ ℍ`, so the three are
  *equivalent*: this lemma **is** the topological crux in this workspace's formulation.

### Traps found this session (do not repeat)

1. **`Submission.HasGreenFunctionWeak` is unsatisfiable** (`E : X → ℝ` is total, so the superlevel
   sets `{ε ≤ E}` cannot be compact around the pole; the corpus's own docstring says so, and
   `Work.Parabolic.not_exists_hasGreenFunctionWeak_of_not_compact` proves it).  Consequently
   `Work.SC.uniformization_of_hyperbolic` (which takes a weak Green function) is *vacuous*, and so
   is `region_with_sector_boundary_of_weakGreen`.  The satisfiable notions are
   `Work.Parabolic.IsGreenFunctionAt` and `Work.UnitGreen.IsUnitGreenFunctionAt`; the branches
   quoted in this file use those.
2. `Work.SimplyConnected.ABS.exists_isGreenOn_of_barriers` (colleague's file) contains one
   `sorry`: exactly the statement of
   `Work.SimplyConnected.ABS.exists_superharmonic_majorant_chartLogClamp`.  The wrapper
   `greenOn_of_barriers_closed.lean` cannot compile because that file calls two identifiers that do
   not exist (`dirichletSphereEnvelope_facts_stub`, `dirichletSphereEnvelope_outerGap_stub`); the
   real theorems are `dirichletSphereEnvelope_facts` (proved) and
   `dirichletSphereEnvelope_outerGap` (one `sorry`, `limEnvelope_lt_one_of_localBarrier`).  Note
   that the in-tree `limEnvelope_lt_one_of_localBarrier` imports the *deleted and refuted*
   `pointwiseMVIMinPrinciple`; the classical statement is nevertheless true and needs the
   harmonic-measure comparison.  So the analytic input of the regional route is
   `limEnvelope_lt_one_of_localBarrier` (delegated, path `Topology/Surface/…`).
3. `Work.SimplyConnected.ABS.planarity_around_compact` (one `sorry`) produces an *arbitrary*
   `OpenPartialHomeomorph` with room, whereas the sector condition needs its chart representatives
   to be *analytic with non-vanishing derivative*.  The endgame
   `exists_regularPiece_of_chart_with_room` in this file is the exact form needed; it generalises
   `exists_regularPiece_of_atlasChartBall` (atlas membership dropped).  Any proof of the crux which
   wants to feed this file must track that local-biholomorphism property (the proof of the crux in
   `planarity_around_compact` *does* use a diffeomorphism composed with the disc inclusion, so the
   property is available, but it is not recorded in the statement).
4. The "grow a union of chart balls greedily" route needs two things which are *not* free: (a) the
   *accumulated* intersection `(⋃ i < k, B i) ∩ B k` must be path-connected (this is the hypothesis
   of `simplyConnectedSpace_biUnion_list`), which fails exactly when the growth closes a loop (the
   annulus case: this is where the crux hides — a union of beads can be contractible *only* if the
   compact set does not wind around a hole); (b) the frontier must avoid *cusps*, i.e. no two pieces
   may be externally tangent at a common frontier point.  The general-position statement in the note
   `NOTES_sector_general_position_DONE.md` (workspace root of this directory) records the
   cross-chart obstruction: in the star cover the pieces are round only in *their own* charts.
-/

/-!
# The geometric core of the regular piece

The target is `Work.SimplyConnected.ABS.regularPiece_core`: every compact subset `K` of a simply
connected non-compact Riemann surface `X` lies in a relatively compact open `U`, homeomorphic to the
open unit disc, with connected frontier of the closure, and satisfying the sector (cone) condition
`HasSectorBoundary U p` at every frontier point of `U`.

## The route used here (analytic, after Anghel--Bruin--Stan)

The topological construction of the piece (proper smooth function, Sard's lemma, filling the
relatively compact complementary components, retraction argument -- the ABS Theorem 12 route) is
replaced by the analytic route, which needs no planarity theorem:

1. cover `K` by finitely many members of the *star cover* of `X` (`Commons.exists_star_cover`): a
   locally finite cover by closed coordinate balls `r i = (e i).symm '' closedBall c ρ` such that
   intersecting members lie in a common chart;
2. let `s` be a finite family with `K ⊆ ⋃ i ∈ s, interior (r i)` and `⋃ i ∈ s, r i` preconnected
   (`exists_finite_family_covering_interiors`), and put `W := interior (⋃ i ∈ s, r i)`;
3. `W` is open, `K ⊆ W`, `closure W` is compact, `W ≠ univ`, `W` is connected, and `W` is simply
   connected (a chain of balls and van Kampen, `simplyConnectedSpace_biUnion_list`);
4. the sector condition at `∂W` gives barriers at the frontier points of `W` (the plane sector
   barrier `plane_sector_barrier` and `barrier_of_sector`);
5. barriers give the Green function of `W` (`exists_isGreenOn_of_barriers`), and the holomorphic
   modulus exists because `W` is simply connected (`exists_isModulusOn_of_isGreenOn`);
6. the endgame `exists_biholomorphicOn_of_greenOn_modulus` makes `W` biholomorphic to a round ball;
   `U := W ∩ χ ⁻¹' ball 0 ρ` for a suitable radius `ρ` then has all the required properties
   (`exists_regularPiece_of_greenOn_modulus`, proved in its own module).

Steps 1--2, 5 and 6 are available in the workspace; step 3 is `simplyConnectedSpace_biUnion_list`.
The single remaining geometric input is step 4: the **sector condition on the frontier of a finite
union of star-cover pieces**.

### The pinch obstruction of step 4

For `W = interior (⋃ i ∈ s, r i)` and `q ∈ frontier W`, write `T q = {i ∈ s : q ∈ r i}`.  In the
chart of any `i₀ ∈ T q` (all members of `T q` lie in a common chart, because they all contain `q`),
a cone through `q` inside the complement of `W` exists **iff** `⋂ i ∈ T q {L i > 0} ≠ ∅`, where
`L i` is the outward normal functional of `r i` at `q`.  If `T q = {i, j}` and the two members are
*externally tangent* at `q` (their interiors locally disjoint, e.g. two balls touching at a point),
then `L j = -L i` and the intersection is a line, not a cone: the region has a cusp at `q` and the
sector condition **fails** there.  Such a configuration must therefore be excluded by the choice of
the family `s`:

* it is *not* enough to take `s` = the members meeting an open neighbourhood of `K`;
* it *would* be excluded if `s` were *saturated* (every member of the cover meeting
  `closure (⋃ i ∈ s, r i)` lies in `s`), because then every member covering a cusp of `q` lies in `s`
  and `q` is an interior point, a contradiction;
* however, a finite saturated family need not exist (the saturation process grows outward and need
  not terminate), which is exactly the difficulty.

Alternative ways to close step 4: (a) prove that mutually tangent members cannot occur for the
*star cover* constructed in `Commons.Topology.Surface.exists_star_cover` (the construction's metric
estimates give `r a ⊆ Metric.closedBall (x a) (ρ (x a) / 12)` and
`dist (x a) (x b) ≤ ρ (x a) / 12 + ρ (x b) / 12` for intersecting members, but they do not obviously
exclude tangency); (b) enlarge the members by a factor chosen to kill all tangencies (needs a
genericity argument for the finitely many tangency equations); (c) replace the round members by
members of the *disk tiling* `Commons.Topology.Surface.exists_locallyFinite_disk_tiling`, whose tiles
have disjoint interiors -- but then any two members meeting at a frontier point are externally
tangent, so the failure is generic unless the frontier avoids all junction points of the tiling.
-/


/-
## The precise state after the chart-level analysis (session notes)

The plan of this file is: produce a finite family of *round balls in charts* covering `K`, whose
union `W` has (a) `K ⊆ W`, (b) compact closure, (c) `W` connected and simply connected, (d) the
**sector (cone) condition** at every frontier point of `W`; then barriers (`barrier_of_sector`), the
Green function (`exists_isGreenOn_of_barriers`), its holomorphic modulus
(`exists_isModulusOn_of_isGreenOn`), the endgame (`exists_biholomorphicOn_of_greenOn_modulus`) and
finally `exists_regularPiece_of_greenOn_modulus` (all proved in the workspace) finish the job.

The chart-level theory of (d) is now *completely settled* below.  Write, at a point `q` which lies on
the boundary of each of finitely many closed balls `closedBall (c i) (r i)` (so `‖q - c i‖ = r i`),
`u i := (r i)⁻¹ • (q - c i)` for the outward unit normal and

  `H i := {w | 0 < ⟪u i, w⟫}`   (the *outer* half-plane of the `i`-th ball at `q`).

Then:

* `sectorComplement_of_escapingDirection` — if the `H i` have a common point `v` (`0 < ⟪u i, v⟫` for
  all `i`), the union of the balls avoids a *sector* with apex `q`.  (Each ball lies in the closed
  half-plane `⟪u i, · - q⟫ ≤ 0`, so the open half-planes are complements; their intersection is an
  open convex cone, and `exists_sector_subset_of_open_convexCone` extracts a sector.)
* `exists_escapingDirection_of_not_interior` — at a point `q ∉ interior (⋃ i, closedBall (c i) (r i))`
  the outward half-planes always have a common *closed* point: `∃ v ≠ 0, ∀ i, 0 ≤ ⟪v, q - c i⟫`.
  (Otherwise the minimisation of `v ↦ max i ⟪v, c i - q⟫` over the unit circle produces `δ > 0` with
  `closedBall q (2δ) ⊆ ⋃ i, closedBall (c i) (r i)`.)
* `sectorComplement_of_not_interior_noTangent` — combining the previous two with the linear-algebra
  lemma `linear_negative_of_no_opposite_pair`, the *open* common point exists as soon as no two of the
  balls are **externally tangent** at `q`, i.e. as long as `c j - q ≠ -t • (c i - q)` for `i ≠ j`,
  `t > 0`.  Hence, for a union of round balls in a common chart, the sector condition at a frontier
  point holds whenever no two of the balls passing through that point are externally tangent there.

### The state: `regularPiece_core` reduces to one geometric input

The *conclusion* of `regularPiece_core` is now proved from the single input "(∗) for an **atlas**
chart with room",

  `∃ φ ∈ atlas ℂ X, ∃ c ρ, 0 < ρ ∧ K ⊆ φ.source ∧ φ '' K ⊆ ball c ρ ∧ closedBall c ρ ⊆ φ.target`,

by `regularPiece_core_of_atlasChartBall` (and `exists_regularPiece_of_atlasChartBall`), which is
sorry-free: `U := φ.symm '' ball c ρ` is open, homeomorphic to the unit disc, has compact closure
with connected frontier `φ.symm '' sphere c ρ`, contains `K`, and satisfies the sector condition —
in the chart `φ` itself `U` *is* the round ball `ball c ρ`, whose complement contains the outer
half-plane at every boundary point (`sectorComplement_of_single_ball`).  (∗) with a merely
`OpenPartialHomeomorph` chart also suffices provided one adds the local geometry of the inverse of
`chartAt ℂ p ∘ φ.symm` at a frontier point: that is exactly the content of the sibling lemma
`sectorComplement_of_quadraticRemainder` (a quadratic Taylor remainder at a non-critical point).

So the *only* missing ingredient of `regularPiece_core` is (∗): `K` lies in one chart ball with room,
i.e. the planarity of a neighbourhood of `K` — the same input the whole ABS route of this corpus
needs (`chartBall_with_room_of_compact`, `planarity_around_compact`).

### The alternative route (no planarity input), and what it needs

If instead one wants to build `W` as a finite union of round balls in *several* charts (which is
possible for a compact `K` by elementary local compactness, with no planarity input), the sector
condition is available through the chart-level lemmas above as soon as:

* at each frontier point `q` of `W = interior (⋃ i, B i)`, **no two of the balls passing through `q`
  are externally tangent at `q`** (the hypothesis of `sectorComplement_of_not_interior_noTangent`),

which for balls round in a *single* chart is elementary to arrange: any finite family of equal-radius
balls with all pairwise centre distances different from twice the radius is tangency-free, and a
suitable lattice of such balls covers a prescribed compact set.  What remains for this route is the
bookkeeping that the pieces coming from *different* charts meet only transversally (the star cover's
pieces are round in different charts, so this is not immediate), plus the (proved-elsewhere) Green
function, modulus and endgame for `W`.
-/



/-
## Session status and the precise plan (for the next session)

### What is proved (sorry-free) in this file

* the whole **chart-level theory of the sector condition** (`sectorComplement_of_escapingDirection`,
  `exists_escapingDirection_of_not_interior`, `sectorComplement_of_not_interior_noTangent`,
  `sectorComplement_of_single_ball`);
* **`sectorComplement_of_hasFDerivAt`** (new): for a *real-valued* `C¹` function `F` on `ℂ` with
  `F w₀ = 0` and `fderiv F w₀ ≠ 0`, the sublevel set `{F < 0}` avoids a sector at `w₀`.  The proof
  uses the *Pythagorean identity* `‖v‖ ^ 2 * ((L 1) ^ 2 + (L I) ^ 2) = (L v) ^ 2 + (N v) ^ 2` for
  `N = conjFunctional L` (`N v = L (I * v)`), whence on the sector `{L₁ > 0, L₂ > 0}` with
  `L₁ = L - N`, `L₂ = L + N` one has `L v ≥ sqrt (P/2) * ‖v‖`; the `o (‖v‖)` remainder of
  `HasFDerivAt` is then beaten.  This is the *only* analytic input needed for the sector condition
  at a smooth boundary point, and it is valid for a mere `C¹` boundary (no second-order control).
* the **endgame**: `exists_regularPiece_of_atlasChartBall` (from a chart ball with room) and
  `regularPiece_core_of_atlasChartBall`.

### The shape of the proof of `regularPiece_core`

Case split on `h : ∃ z₀ E, Work.UnitGreen.IsUnitGreenFunctionAt z₀ E`.

* **Hyperbolic case** (`h` holds): both ingredients are *sorry-free* in the workspace:
  `Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction_of_simplyConnected` gives the
  modulus `Φ`, and `Work.Parabolic.uniformization_of_greenFunctionAt` gives a `Diffeomorph X ℂ` or
  `Diffeomorph X UpperHalfPlane`.  From such a diffeomorphism `e` one gets the required `U` as
  `e ⁻¹' (a round ball with room around `e '' K`)`: open, homeomorphic to the unit disc, compact
  closure, connected frontier (a sphere), and the sector condition at every frontier point by
  `sectorComplement_of_hasFDerivAt` applied to
  `F := (supporting functional of the ball at e p) ∘ (e ∘ (chartAt ℂ p).symm)` in the chart
  `chartAt ℂ p` — the derivative of that chart representative is non-zero because `e` is a
  diffeomorphism (chain rule; the chart representative of `e` is `C ^ ∞` with invertible
  derivative).
* **Parabolic case** (`h` fails): **the remaining gap.**  It is a genuine piece of mathematics, not
  a formalisation difficulty: it is the ABS Theorem 12 engulfing in the parabolic case, equivalently
  Mori's normal form theorem (see `Submission/Work/SimplyConnected/ABS/planarity_around_compact.lean`
  and `Submission/Work/Mori/README.md` for the two classical routes, both of which are named inputs
  in this workspace).  Nothing in the corpus proves it yet.

### The plane-level input (done)

`exists_openBall_superset_of_isCompact`, `exists_planeRegularPiece_of_isCompact` (its
`HasSectorBoundary` form for `X = ℂ`) and `exists_openBall_superset_with_halfSpace` (a round ball
lies in the open half-space cut out by the outer normal at any of its boundary points), together
with the ball-topology helpers `interior_closedBall_eq_ball`, `frontier_closedBall_eq_sphere`,
`frontier_ball_eq_sphere`.

### The transport lemmas (statements in place, proofs missing)

`exists_regularPiece_of_diffeomorph_plane` (`X ≅ ℂ`) and `exists_regularPiece_of_diffeomorph_disc`
(`X ≅ 𝔻`, hence `X ≅ ℍ` via the Cayley diffeomorphism).  Their docstrings contain the full proof
plan, whose only non-trivial input is that the chart representative of a diffeomorphism has
invertible derivative (Mathlib's `writtenInExtChartAt`/`HasMFDerivAt` API; cf.
`HasMFDerivAt.hasFDerivAt_writtenInExtChartAt` in `Mathlib/Geometry/Manifold/MFDeriv/Basic.lean`
and the use of `deriv_ne_zero_of_injective_analytic` in `Work/SimplyConnected/Plane.lean`).

### (Superseded plan, kept for reference) The plane-level input

`exists_openBall_superset_of_isCompact` (proved below): for `K ⊆ ℂ` compact, `U := Metric.ball 0 R`
with `K ⊆ Metric.ball 0 R` satisfies `Nonempty (Metric.ball 0 1 ≃ₜ ↥U)`, `IsCompact (closure U)`,
`IsConnected (frontier (closure U))` and the sector condition (in the model coordinates `z - p`) at
every frontier point.  Ingredients:

* `hK.isBounded.subset_ball 0` for `R`; `closure_ball` and the helper lemmas
  `interior_closedBall_eq_ball`, `frontier_closedBall_eq_sphere`, `frontier_ball_eq_sphere` (all
  proved below) for the topology of the round ball;
* `exists_homeomorph_image_interior_closure_frontier_eq_unitBall`
  (`Mathlib.Analysis.Convex.GaugeRescale`) applied to the closed ball, combined with
  `Homeomorph.image`, `Homeomorph.setCongr` and `.symm` for the homeomorphism with the unit disc;
* `isConnected_sphere` (`Mathlib.Analysis.Normed.Module.Connected`) for the frontier;
* `sectorComplement_of_single_ball` (proved above) for the sector condition.

### Remaining concrete work

1. the `HasSectorBoundary` form of the plane-level input for `X = ℂ` (the identity chart
   `chartAt ℂ p` agrees with the identity, so `c x - c p = x - p`);
2. the transport along a `Diffeomorph X ℂ` resp. `Diffeomorph X UpperHalfPlane`
   (`HasSectorBoundary` is stated w.r.t. the *atlas* charts, so the chart representative of `e`
   enters; `sectorComplement_of_hasFDerivAt` applies with
   `F := M ∘ (e ∘ (chartAt ℂ p).symm)` for a supporting functional `M` of the ball at `e p`; the
   derivative of the chart representative of `e` at `p` is non-zero because `e` is a
   diffeomorphism — see `Mathlib/Geometry/Manifold/MFDeriv/Basic.lean` for
   `HasMFDerivAt.hasFDerivAt_writtenInExtChartAt` and `Work/SimplyConnected/Plane.lean` for the same
   computation in this workspace);
3. the case split (hyperbolic case above) with the parabolic case as the gap.  For the `𝔻` (and
   hence `ℍ`) case one can either use the `ℂ ≅ 𝔻` Cayley diffeomorphism
   (`Commons.Analysis.Complex.UpperHalfPlane.halfPlane_disc_diffeomorph`) or repeat the plane-level
   argument with a ball of radius `< 1` inside `𝔻`.
-/

namespace Work.SimplyConnected.ABS

open Set
open scoped Topology Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [SimplyConnectedSpace X]


section ChartLevel

variable {ι : Type*}

/-- **The sector condition at a boundary point of a finite union of round balls, from an escaping
direction.**  Let `q` lie on the boundary of each of the closed balls `closedBall (c i) (r i)`
(so `‖q - c i‖ = r i`), and suppose the outer half-planes of the balls at `q` have a common point
`v` (`0 < ⟪v, q - c i⟫` for all `i`).  Then the union of the balls avoids a *sector* with apex `q`:
there are non-zero real-linear functionals `L₁ L₂` spanning a non-empty sector, disjoint from the
union after translation by `q`.

Each ball lies in the closed half-plane `⟪u i, · - q⟫ ≤ 0` (`u i` the outward unit normal, this is
`closedBall_innerHalfPlane`), so the *outer* open half-planes are complements of the balls; their
intersection is a non-empty open convex cone (it contains `v`), and
`exists_sector_subset_of_open_convexCone` extracts a sector inside it. -/
theorem sectorComplement_of_escapingDirection [Fintype ι] (c : ι → ℂ) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) {q v : ℂ} (hq : ∀ i, ‖q - c i‖ = r i)
    (hv : ∀ i, 0 < inner ℝ v (q - c i)) :
    ∃ L₁ L₂ : ℂ →L[ℝ] ℝ, L₁ ≠ 0 ∧ L₂ ≠ 0 ∧ (∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w) ∧
      ∀ z ∈ ⋃ i, Metric.closedBall (c i) (r i), ¬ (0 < L₁ (z - q) ∧ 0 < L₂ (z - q)) := by
  let u : ι → ℂ := fun i => ((r i)⁻¹ : ℝ) • (q - c i)
  have hu : ∀ i, u i = (((r i)⁻¹ : ℝ) : ℂ) * (q - c i) := fun i => (Complex.real_smul ..).symm
  set C : Set ℂ := ⋂ i, {w : ℂ | 0 < inner ℝ (u i) w} with hC
  have hCopen : IsOpen C := by
    rw [hC]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_const.inner continuous_id)
  have hCmem : ∀ w : ℂ, w ∈ C ↔ ∀ i, 0 < inner ℝ (u i) w := by
    intro w; rw [hC]; simp
  have hCconv : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    rw [hCmem] at hx hy ⊢
    intro i
    have h1 := hx i
    have h2 := hy i
    have h3 : 0 < a * inner ℝ (u i) x + b * inner ℝ (u i) y := by
      rcases eq_or_lt_of_le ha with h | h
      · have hb1 : b = 1 := by linarith
        rw [← h, hb1, zero_mul, zero_add, one_mul]
        exact h2
      · have h4 : 0 < a * inner ℝ (u i) x := mul_pos h h1
        have h5 : 0 ≤ b * inner ℝ (u i) y := mul_nonneg hb (le_of_lt h2)
        linarith
    calc 0 < a * inner ℝ (u i) x + b * inner ℝ (u i) y := h3
      _ = inner ℝ (u i) (a • x + b • y) := by
          rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have hCcone : ∀ w ∈ C, ∀ t : ℝ, 0 < t → t • w ∈ C := by
    intro w hw t ht
    rw [hCmem] at hw ⊢
    intro i
    rw [real_inner_smul_right]
    exact mul_pos ht (hw i)
  have hCne : C.Nonempty := by
    refine ⟨v, ?_⟩
    rw [hCmem]
    intro i
    have h1 : inner ℝ (u i) v = (r i)⁻¹ * inner ℝ v (q - c i) := by
      rw [hu i, ← Complex.real_smul, real_inner_smul_left, real_inner_comm]
    rw [h1]
    exact mul_pos (inv_pos.mpr (hr i)) (hv i)
  obtain ⟨L₁, L₂, h1, h2, h3, hsub⟩ :=
    exists_sector_subset_of_open_convexCone C hCopen hCconv hCcone hCne
  refine ⟨L₁, L₂, h1, h2, h3, ?_⟩
  intro z hz hsec
  obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
  have hle : inner ℝ (u i) (z - q) ≤ 0 := by
    have h := (closedBall_innerHalfPlane (c i) (hr i) (hq i)).2 z hzi
    rw [hu i]; rw [← Complex.real_smul]; exact h
  have hpos : 0 < inner ℝ (u i) (z - q) := (hCmem (z - q)).mp (hsub (z - q) hsec.1 hsec.2) i
  linarith

/-- **An escaping direction exists at any non-interior point of a finite union of round balls.**
If `q` is in the boundary of the union `⋃ i, closedBall (c i) (r i)` (more precisely, not an interior
point), then some non-zero `v` has `0 ≤ ⟪v, q - c i⟫` for all `i`: the outward half-planes have a
common closed point.

Proof (contrapositive): if for every non-zero `v` some `i` had `⟪v, q - c i⟫ < 0`, then the
continuous function `v ↦ max i ⟪v, c i - q⟫` would be strictly positive on the unit circle, hence
bounded below by `δ > 0` there, and every `z` with `‖z - q‖ ≤ 2δ` would lie in
`closedBall (c i) (r i)` for a suitable `i` (namely one attaining the maximum in the direction of
`z - q`), so that `closedBall q (2δ) ⊆ ⋃ i, closedBall (c i) (r i)`. -/
theorem exists_escapingDirection_of_not_interior [Fintype ι] [Nonempty ι] (c : ι → ℂ) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) {q : ℂ} (hq : ∀ i, ‖q - c i‖ = r i)
    (hnot : q ∉ interior (⋃ i, Metric.closedBall (c i) (r i))) :
    ∃ v : ℂ, v ≠ 0 ∧ ∀ i, 0 ≤ inner ℝ v (q - c i) := by
  by_contra hcon
  push_neg at hcon
  let M : ℂ → ℝ := fun v =>
    (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i => inner ℝ v (c i - q))
  have hMcont : Continuous M := by
    have hMfun : M = (Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i => fun v => inner ℝ v (c i - q)) := by
      funext v
      exact (Finset.sup'_apply Finset.univ_nonempty (fun i => fun v => inner ℝ v (c i - q)) v).symm
    rw [hMfun]
    exact Continuous.finset_sup' (L := ℝ) (X := ℂ) (s := (Finset.univ : Finset ι))
      (f := fun i => fun v => inner ℝ v (c i - q)) Finset.univ_nonempty (fun i _ =>
        continuous_id.inner (continuous_const : Continuous (fun _ : ℂ => c i - q)))
  have hne : (Metric.sphere (0 : ℂ) 1).Nonempty := ⟨1, by simp [Metric.mem_sphere]⟩
  obtain ⟨v₀, hv₀mem, hv₀min⟩ :=
    (isCompact_sphere (0 : ℂ) 1).exists_isMinOn hne hMcont.continuousOn
  have hv₀norm : ‖v₀‖ = 1 := by
    have h := hv₀mem
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    exact h
  have hv₀ne : v₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hv₀norm; norm_num at hv₀norm
  have hMpos : 0 < M v₀ := by
    obtain ⟨i, hi⟩ := hcon v₀ hv₀ne
    have hpos : 0 < inner ℝ v₀ (c i - q) := by
      rw [show c i - q = -(q - c i) from by ring, inner_neg_right]
      linarith
    exact lt_of_lt_of_le hpos (Finset.le_sup' (s := (Finset.univ : Finset ι))
      (fun i => inner ℝ v₀ (c i - q)) (Finset.mem_univ i))
  refine hnot (mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (Metric.ball_mem_nhds q hMpos) ?_))
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  rcases eq_or_ne z q with h | h
  · subst h
    exact mem_iUnion.mpr ⟨Classical.arbitrary ι, by
      rw [Metric.mem_closedBall, dist_eq_norm]; exact le_of_eq (hq _)⟩
  · have ht : 0 < ‖z - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
    have hvt : ‖((‖z - q‖)⁻¹ : ℝ) • (z - q)‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht), inv_mul_cancel₀ ht.ne']
    have hmemsph : ((‖z - q‖)⁻¹ : ℝ) • (z - q) ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hvt
    have hle : M v₀ ≤ M (((‖z - q‖)⁻¹ : ℝ) • (z - q)) := hv₀min hmemsph
    have hlt : ‖z - q‖ < M (((‖z - q‖)⁻¹ : ℝ) • (z - q)) := lt_of_lt_of_le hz hle
    obtain ⟨i, -, hi⟩ :=
      (Finset.lt_sup'_iff (s := (Finset.univ : Finset ι)) Finset.univ_nonempty).mp hlt
    refine mem_iUnion.mpr ⟨i, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hzci : z - c i = (z - q) + (q - c i) := by ring
    have hsq : ‖z - c i‖ ^ 2 < r i ^ 2 := by
      rw [hzci, norm_add_sq_real, hq i]
      have hzv : (‖z - q‖) • (((‖z - q‖)⁻¹ : ℝ) • (z - q)) = z - q := by
        rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
      have hinner1 : inner ℝ (z - q) (q - c i)
          = ‖z - q‖ * inner ℝ (((‖z - q‖)⁻¹ : ℝ) • (z - q)) (q - c i) := by
        conv_lhs => rw [← hzv]
        rw [real_inner_smul_left]
      have hinner2 : inner ℝ (((‖z - q‖)⁻¹ : ℝ) • (z - q)) (q - c i)
          = - inner ℝ (((‖z - q‖)⁻¹ : ℝ) • (z - q)) (c i - q) := by
        rw [show q - c i = -(c i - q) from by ring, inner_neg_right]
      rw [hinner1, hinner2]
      nlinarith [ht, hi]
    have h2 := sq_lt_sq.mp hsq
    rw [abs_of_nonneg (norm_nonneg _), abs_of_pos (hr i)] at h2
    exact le_of_lt h2

/-- **The sector condition at a boundary point of a finite union of round balls, when no two of the
balls are externally tangent there.**  `c j - q ≠ -t • (c i - q)` for `i ≠ j`, `t > 0` is exactly the
statement that the balls `i` and `j` (both passing through `q`) are not externally tangent at `q`;
under that hypothesis the union of the balls avoids a sector with apex `q`. -/
theorem sectorComplement_of_not_interior_noTangent [Fintype ι] [Nonempty ι] (c : ι → ℂ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) {q : ℂ} (hq : ∀ i, ‖q - c i‖ = r i)
    (hnot : q ∉ interior (⋃ i, Metric.closedBall (c i) (r i)))
    (hnotan : ∀ i j, i ≠ j → ∀ t : ℝ, 0 < t → c j - q ≠ -t • (c i - q)) :
    ∃ L₁ L₂ : ℂ →L[ℝ] ℝ, L₁ ≠ 0 ∧ L₂ ≠ 0 ∧ (∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w) ∧
      ∀ z ∈ ⋃ i, Metric.closedBall (c i) (r i), ¬ (0 < L₁ (z - q) ∧ 0 < L₂ (z - q)) := by
  obtain ⟨v, hvne, hv⟩ := exists_escapingDirection_of_not_interior c r hr hq hnot
  -- the master linear-algebra step, applied to `n i := c i - q`
  have hne : ∀ i, c i - q ≠ 0 := by
    intro i h
    have h0 : ‖c i - q‖ = 0 := by rw [h, norm_zero]
    have h1 : ‖q - c i‖ = ‖c i - q‖ := norm_sub_rev q (c i)
    rw [← h1, hq i] at h0
    exact absurd h0 (ne_of_gt (hr i))
  have ha : ∃ v : ℂ, v ≠ 0 ∧ ∀ i, inner ℝ v (c i - q) ≤ 0 := by
    refine ⟨v, hvne, fun i => ?_⟩
    have h := hv i
    rw [show c i - q = -(q - c i) from by ring, inner_neg_right]
    linarith
  obtain ⟨w, hw⟩ := linear_negative_of_no_opposite_pair (fun i => c i - q) hne ha hnotan
  refine sectorComplement_of_escapingDirection (v := w) c r hr hq (fun i => ?_)
  have h := hw i
  rw [show c i - q = -(q - c i) from by ring, inner_neg_right, neg_lt_zero] at h
  exact h

/-- **The sector condition at a boundary point of a single round ball** (no tangency hypothesis is
needed: with one ball the escaping direction is the outward normal). -/
theorem sectorComplement_of_single_ball (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {q : ℂ}
    (hq : ‖q - c‖ = ρ) :
    ∃ L₁ L₂ : ℂ →L[ℝ] ℝ, L₁ ≠ 0 ∧ L₂ ≠ 0 ∧ (∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w) ∧
      ∀ z ∈ Metric.closedBall c ρ, ¬ (0 < L₁ (z - q) ∧ 0 < L₂ (z - q)) := by
  have hv : 0 < inner ℝ (q - c) (q - c) := by
    rw [real_inner_self_eq_norm_sq, hq]; positivity
  have hmain := sectorComplement_of_escapingDirection (ι := Unit) (fun _ => c) (fun _ => ρ)
    (fun _ => hρ) (fun _ => hq) (fun _ => hv)
  simpa using hmain

end ChartLevel

section SectorFromDerivative

/-- A non-zero real-linear functional on `ℂ` is positive somewhere. -/
theorem exists_pos_of_ne_zero (L : ℂ →L[ℝ] ℝ) (hL : L ≠ 0) : ∃ u : ℂ, 0 < L u := by
  by_contra h
  push_neg at h
  refine hL (ContinuousLinearMap.ext fun x => ?_)
  have h1 : L x ≤ 0 := h x
  have h2 : 0 ≤ L x := by
    have h3 := h (-x)
    rw [map_neg] at h3
    linarith
  exact le_antisymm h1 h2

/-- The conjugate functional `N v = L (I * v)` of a real-linear functional `L` on `ℂ`. -/
noncomputable def conjFunctional (L : ℂ →L[ℝ] ℝ) : ℂ →L[ℝ] ℝ :=
  L.comp (ContinuousLinearMap.mul ℝ ℂ Complex.I)

theorem conjFunctional_apply (L : ℂ →L[ℝ] ℝ) (v : ℂ) :
    conjFunctional L v = L (Complex.I * v) := rfl

/-- Decomposition of a real-linear functional on `ℂ` in the real basis `(1, I)`. -/
theorem linearMap_apply_eq (L : ℂ →L[ℝ] ℝ) (v : ℂ) :
    L v = v.re * L 1 + v.im * L Complex.I := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hv, map_add, map_smul, map_smul]
  simp [smul_eq_mul]

/-- The conjugate functional in the real basis `(1, I)`. -/
theorem conjFunctional_apply_eq (L : ℂ →L[ℝ] ℝ) (v : ℂ) :
    conjFunctional L v = -(v.im * L 1) + v.re * L Complex.I := by
  have hv : Complex.I * v = (-(v.im)) • (1 : ℂ) + (v.re) • Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [conjFunctional_apply, hv, map_add, map_smul, map_smul]
  simp [smul_eq_mul]

/-- **The Pythagorean identity**: `‖v‖ ^ 2 * (L 1 ^ 2 + (L I) ^ 2) = (L v) ^ 2 + (N v) ^ 2`. -/
theorem normSq_mul_eq (L : ℂ →L[ℝ] ℝ) (v : ℂ) :
    ‖v‖ ^ 2 * ((L 1) ^ 2 + (L Complex.I) ^ 2) = (L v) ^ 2 + (conjFunctional L v) ^ 2 := by
  rw [linearMap_apply_eq L v, conjFunctional_apply_eq L v, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The constant `(L 1) ^ 2 + (L I) ^ 2` is positive when `L ≠ 0`. -/
theorem sq_add_sq_pos_of_ne_zero {L : ℂ →L[ℝ] ℝ} (hL : L ≠ 0) :
    0 < (L 1) ^ 2 + (L Complex.I) ^ 2 := by
  rcases lt_trichotomy ((L 1) ^ 2 + (L Complex.I) ^ 2) 0 with h | h | h
  · nlinarith [sq_nonneg (L 1), sq_nonneg (L Complex.I)]
  · exfalso
    have h1 : L 1 = 0 := by nlinarith [sq_nonneg (L 1), sq_nonneg (L Complex.I)]
    have h2 : L Complex.I = 0 := by nlinarith [sq_nonneg (L 1), sq_nonneg (L Complex.I)]
    exact hL (ContinuousLinearMap.ext fun v => by rw [linearMap_apply_eq, h1, h2]; simp)
  · exact h

/-- **A sector in the complement of `{F < 0}`, from a non-vanishing derivative.**

If `F : ℂ → ℝ` is real-differentiable at `w₀` with `F w₀ = 0` and derivative `L ≠ 0`, then the
sublevel set `{F < 0}` avoids a sector with apex `w₀`. -/
theorem sectorComplement_of_hasFDerivAt {F : ℂ → ℝ} {w₀ : ℂ} {L : ℂ →L[ℝ] ℝ}
    (hF : HasFDerivAt F L w₀) (hF0 : F w₀ = 0) (hL : L ≠ 0) :
    ∃ L₁ L₂ : ℂ →L[ℝ] ℝ, L₁ ≠ 0 ∧ L₂ ≠ 0 ∧ (∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ v : ℂ, ‖v‖ < δ → F (w₀ + v) < 0 → ¬ (0 < L₁ v ∧ 0 < L₂ v) := by
  obtain ⟨u, hu⟩ := exists_pos_of_ne_zero L hL
  set N : ℂ →L[ℝ] ℝ := conjFunctional L with hNdef
  set L₁ : ℂ →L[ℝ] ℝ := L - N with hL₁def
  set L₂ : ℂ →L[ℝ] ℝ := L + N with hL₂def
  have hPpos : 0 < (L 1) ^ 2 + (L Complex.I) ^ 2 := sq_add_sq_pos_of_ne_zero hL
  -- non-emptiness of the sector
  have hLIu : L (Complex.I * u) = N u := (conjFunctional_apply L u).symm
  have hII : Complex.I * (Complex.I * u) = -u := by
    rw [← mul_assoc, Complex.I_mul_I]; simp
  have hNIu : N (Complex.I * u) = -L u := by
    rw [hNdef, conjFunctional_apply, hII, map_neg]
  have hNw : N (u + ((N u) / (L u)) • (Complex.I * u)) = 0 := by
    rw [map_add, map_smul, smul_eq_mul, hNIu]
    have hLu : L u ≠ 0 := ne_of_gt hu
    field_simp
    ring
  have hLw : L (u + ((N u) / (L u)) • (Complex.I * u)) = L u + (N u) ^ 2 / L u := by
    rw [map_add, map_smul, smul_eq_mul, hLIu]
    field_simp
  have hLwpos : 0 < L (u + ((N u) / (L u)) • (Complex.I * u)) := by
    rw [hLw]
    have h1 : 0 ≤ (N u) ^ 2 / L u := div_nonneg (sq_nonneg _) hu.le
    linarith
  have hw : ∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w := by
    refine ⟨u + ((N u) / (L u)) • (Complex.I * u), ?_, ?_⟩
    · simp only [hL₁def, ContinuousLinearMap.sub_apply]
      rw [hNw]
      linarith
    · simp only [hL₂def, ContinuousLinearMap.add_apply]
      rw [hNw]
      linarith
  -- the functionals are non-zero
  have hL₁ne : L₁ ≠ 0 := by
    intro hcon
    have hLN : L = N := by
      have : L - N = 0 := hcon
      exact sub_eq_zero.mp this
    -- L = N implies (L 1) ^ 2 + (L I) ^ 2 = 0
    have h1 : N 1 = L Complex.I := by rw [hNdef, conjFunctional_apply]; simp
    have h2 : N Complex.I = -L 1 := by
      rw [hNdef, conjFunctional_apply, Complex.I_mul_I, map_neg]
    have hN : N = L := hLN.symm
    have hp : L 1 = L Complex.I := by
      have h := h1; rw [hN] at h; exact h
    have hq : L Complex.I = -L 1 := by
      have h := h2; rw [hN] at h; exact h
    have hp0 : L 1 = 0 := by linarith
    have hq0 : L Complex.I = 0 := by rw [hp0] at hq; simpa using hq
    rw [hp0, hq0] at hPpos
    norm_num at hPpos
  have hL₂ne : L₂ ≠ 0 := by
    intro hcon
    have hLN : L = -N := by
      have : L + N = 0 := hcon
      exact eq_neg_of_add_eq_zero_left this
    have h1 : N 1 = L Complex.I := by rw [hNdef, conjFunctional_apply]; simp
    have h2 : N Complex.I = -L 1 := by
      rw [hNdef, conjFunctional_apply, Complex.I_mul_I, map_neg]
    have hN : N = -L := by rw [hLN, neg_neg]
    have hp : L 1 = -L Complex.I := by
      have h := h1; rw [hN, neg_apply] at h; linarith
    have hq : L Complex.I = L 1 := by
      have h := h2; rw [hN, neg_apply] at h; linarith
    have hp0 : L 1 = 0 := by linarith
    have hq0 : L Complex.I = 0 := by rw [hq, hp0]
    rw [hp0, hq0] at hPpos
    norm_num at hPpos
  -- the sector bound: `L v ≥ sqrt (P/2) * ‖v‖` on the sector
  have hbound : ∀ v : ℂ, (0 < L₁ v ∧ 0 < L₂ v) → Real.sqrt (((L 1) ^ 2 + (L Complex.I) ^ 2) / 2) * ‖v‖ < L v := by
    intro v hv
    have h1 : 0 < L v - N v := by
      have := hv.1
      simpa only [hL₁def, ContinuousLinearMap.sub_apply] using this
    have h2 : 0 < L v + N v := by
      have := hv.2
      simpa only [hL₂def, ContinuousLinearMap.add_apply] using this
    have hNlt : |N v| < L v := by
      rw [abs_lt]
      constructor <;> linarith
    have hLvpos : 0 < L v := by linarith [abs_nonneg (N v)]
    have hpyth := normSq_mul_eq L v
    have hnormsq : ‖v‖ ^ 2 * ((L 1) ^ 2 + (L Complex.I) ^ 2) < 2 * (L v) ^ 2 := by
      rw [hpyth]
      nlinarith [hNlt, hLvpos]
    have hsq : (Real.sqrt (((L 1) ^ 2 + (L Complex.I) ^ 2) / 2) * ‖v‖) ^ 2 < (L v) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ ((L 1) ^ 2 + (L Complex.I) ^ 2) / 2)]
      nlinarith [hnormsq]
    have hnn : 0 ≤ Real.sqrt (((L 1) ^ 2 + (L Complex.I) ^ 2) / 2) * ‖v‖ := by positivity
    nlinarith [hsq, hnn, hLvpos]
  -- the differentiability bound
  have hlittle : (fun v : ℂ => F (w₀ + v) - F w₀ - L v) =o[𝓝 (0 : ℂ)] (fun v : ℂ => v) := by
    have h := hF.isLittleO
    have hφ : Filter.Tendsto (fun v : ℂ => w₀ + v) (𝓝 (0 : ℂ)) (𝓝 w₀) := by
      have h1 : Filter.Tendsto (fun _ : ℂ => w₀) (𝓝 (0 : ℂ)) (𝓝 w₀) := tendsto_const_nhds
      have h2 : Filter.Tendsto (fun v : ℂ => v) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := Filter.tendsto_id
      simpa using h1.add h2
    have hcomp := h.comp_tendsto hφ
    have key : ((fun x' : ℂ => F x' - F w₀ - L (x' - w₀)) ∘ (fun v : ℂ => w₀ + v))
        = fun v : ℂ => F (w₀ + v) - F w₀ - L v := by
      funext v
      simp [add_sub_cancel_left]
    have key2 : ((fun x' : ℂ => x' - w₀) ∘ (fun v : ℂ => w₀ + v)) = fun v : ℂ => v := by
      funext v
      simp [add_sub_cancel_left]
    rw [key, key2] at hcomp
    simpa using hcomp
  have hc2 : 0 < Real.sqrt (((L 1) ^ 2 + (L Complex.I) ^ 2) / 2) / 2 := by positivity
  have hev := (Asymptotics.isLittleO_iff.mp hlittle) hc2
  simp only [hF0, sub_zero] at hev
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨L₁, L₂, hL₁ne, hL₂ne, hw, δ, hδpos, ?_⟩
  intro v hvnorm hFv hvsec
  have hb := hbound v hvsec
  have hd := hδ (y := v) (by simpa [dist_eq_norm] using hvnorm)
  have hcpos : 0 < Real.sqrt (((L 1) ^ 2 + (L Complex.I) ^ 2) / 2) := by positivity
  -- `‖F (w₀+v) - L v‖ ≤ c/2 * ‖v‖` with `F w₀ = 0`
  have hFv' : F (w₀ + v) - L v = F (w₀ + v) - F w₀ - L v := by rw [hF0]; ring
  rw [hFv'] at hd
  have hle : Real.sqrt (((L 1) ^ 2 + (L Complex.I) ^ 2) / 2) / 2 * ‖v‖ ≤ F (w₀ + v) := by
    have := abs_le.mp hd
    nlinarith [this.1, hb, hcpos, norm_nonneg v]
  have h0 : 0 ≤ Real.sqrt (((L 1) ^ 2 + (L Complex.I) ^ 2) / 2) / 2 * ‖v‖ := by positivity
  linarith

end SectorFromDerivative

section PlanePiece

/-- The interior of a closed ball of positive radius in `ℂ` is the open ball. -/
theorem interior_closedBall_eq_ball {R : ℝ} (hR : 0 < R) :
    interior (Metric.closedBall (0 : ℂ) R) = Metric.ball (0 : ℂ) R := by
  refine Subset.antisymm ?_ Metric.ball_subset_interior_closedBall
  intro x hx
  by_contra hcon
  rw [Metric.mem_ball, not_lt] at hcon
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
  set t : ℝ := δ / (2 * (‖x‖ + 1)) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have hmem : x + t • x ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : x + t • x - x = t • x := by module
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (‖x‖ + 1))]
    nlinarith [norm_nonneg x]
  have hxmem : x + t • x ∈ Metric.closedBall (0 : ℂ) R := interior_subset (hδsub hmem)
  have hnorm : ‖x + t • x‖ = (1 + t) * ‖x‖ := by
    have h1 : x + t • x = (1 + t) • x := by module
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hxmem
  have hgt : R < (1 + t) * ‖x‖ := by
    have h2 : R ≤ ‖x‖ := by
      have hh := hcon; rwa [dist_zero_right] at hh
    nlinarith [h2, norm_nonneg x, htpos]
  exact absurd hxmem (not_le.mpr hgt)

/-- The frontier of a closed ball of positive radius in `ℂ` is the sphere. -/
theorem frontier_closedBall_eq_sphere {R : ℝ} (hR : 0 < R) :
    frontier (Metric.closedBall (0 : ℂ) R) = Metric.sphere (0 : ℂ) R := by
  rw [Metric.isClosed_closedBall.frontier_eq, interior_closedBall_eq_ball hR]
  ext z
  rw [Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, Metric.mem_sphere,
    not_lt, dist_zero_right]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

/-- The frontier of an open ball of positive radius in `ℂ` is the sphere. -/
theorem frontier_ball_eq_sphere {R : ℝ} (hR : 0 < R) :
    frontier (Metric.ball (0 : ℂ) R) = Metric.sphere (0 : ℂ) R := by
  rw [Metric.isOpen_ball.frontier_eq, closure_ball (0 : ℂ) hR.ne']
  ext z
  rw [Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, Metric.mem_sphere,
    not_lt, dist_zero_right]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

/-- **The plane case.**  Every compact subset `K` of `ℂ` is contained in a round ball, and the
round ball satisfies the sector condition (in the model coordinates `z - p`) at every frontier
point. -/
theorem exists_openBall_superset_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    ∃ U : Set ℂ, IsOpen U ∧ Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥U) ∧
      IsCompact (closure U) ∧ IsConnected (frontier (closure U)) ∧ K ⊆ U ∧
      ∀ p ∈ frontier U, ∃ L₁ L₂ : ℂ →L[ℝ] ℝ, L₁ ≠ 0 ∧ L₂ ≠ 0 ∧
        (∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w) ∧
        ∀ z ∈ U, ¬ (0 < L₁ (z - p) ∧ 0 < L₂ (z - p)) := by
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_ball (0 : ℂ)
  set R : ℝ := |R₀| + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hsub : Metric.ball (0 : ℂ) R₀ ⊆ Metric.ball (0 : ℂ) R :=
    Metric.ball_subset_ball (by rw [hRdef]; linarith [le_abs_self R₀])
  refine ⟨Metric.ball (0 : ℂ) R, Metric.isOpen_ball, ?_, ?_, ?_, hR₀.trans hsub, ?_⟩
  · -- the homeomorphism with the unit ball
    have hconv : Convex ℝ (Metric.closedBall (0 : ℂ) R) := convex_closedBall (0 : ℂ) R
    have hne : (interior (Metric.closedBall (0 : ℂ) R)).Nonempty := by
      rw [interior_closedBall_eq_ball hRpos]
      exact ⟨0, by simp [hRpos]⟩
    have hbdd : Bornology.IsBounded (Metric.closedBall (0 : ℂ) R) :=
      (isCompact_closedBall (x := (0 : ℂ)) (r := R)).isBounded
    obtain ⟨h, h1, h2, h3⟩ :=
      exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hne hbdd
    rw [interior_closedBall_eq_ball hRpos] at h1
    exact ⟨((h.image (Metric.ball (0 : ℂ) R)).trans (Homeomorph.setCongr h1)).symm⟩
  · -- compact closure
    exact (isCompact_closedBall (x := (0 : ℂ)) (r := R)).of_isClosed_subset
      isClosed_closure (closure_minimal Metric.ball_subset_closedBall
        Metric.isClosed_closedBall)
  · -- connected frontier
    rw [closure_ball (0 : ℂ) hRpos.ne', frontier_closedBall_eq_sphere hRpos]
    have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
    exact isConnected_sphere hrank 0 hRpos.le
  · -- the sector condition
    intro p hp
    have hpnorm : ‖p - 0‖ = R := by
      rw [frontier_ball_eq_sphere hRpos] at hp
      simpa using hp
    obtain ⟨L₁, L₂, h1, h2, h3, havoid⟩ :=
      sectorComplement_of_single_ball (0 : ℂ) hRpos hpnorm
    exact ⟨L₁, L₂, h1, h2, h3, fun z hz => havoid z (Metric.ball_subset_closedBall hz)⟩


/-- **The plane case, in the form of the target statement for `X = ℂ`.** -/
theorem exists_planeRegularPiece_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    ∃ U : Set ℂ, IsOpen U ∧ Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥U) ∧
      IsCompact (closure U) ∧ IsConnected (frontier (closure U)) ∧ K ⊆ U ∧
      ∀ p ∈ frontier U, HasSectorBoundary U p := by
  obtain ⟨U, h1, h2, h3, h4, h5, h6⟩ := exists_openBall_superset_of_isCompact hK
  refine ⟨U, h1, h2, h3, h4, h5, fun p hp => ?_⟩
  obtain ⟨L₁, L₂, hL₁, hL₂, hsec, havoid⟩ := h6 p hp
  have hsrc : (chartAt ℂ p).source = Set.univ := by
    rw [chartAt_self_eq]; rfl
  have happ : ∀ x : ℂ, (chartAt ℂ p) x = x := by
    intro x; rw [chartAt_self_eq]; rfl
  exact ⟨chartAt ℂ p, Set.univ, L₁, L₂, chart_mem_atlas ℂ p, isOpen_univ, Set.mem_univ p,
    hsrc.le, by rw [hsrc]; exact Set.mem_univ p, hL₁, hL₂, hsec, fun x hx => by
      obtain ⟨hxU, -⟩ := hx
      rw [happ x, happ p]
      exact havoid x hxU⟩


/-- **A round ball lies in the half-space cut out by the outer normal at any boundary point.**
This is the form of the plane-level input needed to transport the sector condition along a
diffeomorphism `X ≅ ℂ`: it says that for `p` on the sphere the ball is contained in the open
half-space `{z | inner ℝ p z < inner ℝ p p}`. -/
theorem exists_openBall_superset_with_halfSpace {K : Set ℂ} (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.ball (0 : ℂ) R ∧
      ∀ p ∈ Metric.sphere (0 : ℂ) R, ∀ z ∈ Metric.ball (0 : ℂ) R,
        inner ℝ p z < inner ℝ p p := by
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_ball (0 : ℂ)
  set R : ℝ := |R₀| + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hsub : Metric.ball (0 : ℂ) R₀ ⊆ Metric.ball (0 : ℂ) R :=
    Metric.ball_subset_ball (by rw [hRdef]; linarith [le_abs_self R₀])
  refine ⟨R, hRpos, hR₀.trans hsub, fun p hp z hz => ?_⟩
  have hpnorm : ‖p - 0‖ = R := by
    rw [Metric.mem_sphere, dist_eq_norm] at hp; simpa using hp
  have hznorm : ‖z - 0‖ < R := by
    rw [Metric.mem_ball, dist_eq_norm] at hz; simpa using hz
  have hself : inner ℝ p p = R ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
    have h2 : ‖p‖ = R := by simpa using hpnorm
    rw [h2]
  have hle : inner ℝ p z ≤ R * ‖z‖ := by
    have h1 : inner ℝ p z ≤ ‖p‖ * ‖z‖ := real_inner_le_norm p z
    have h2 : ‖p‖ = R := by simpa using hpnorm
    rwa [h2] at h1
  have hlt : R * ‖z‖ < R * R := by
    have h2 : ‖z‖ = ‖z - 0‖ := by rw [sub_zero]
    nlinarith [hRpos, hznorm]
  rw [hself]
  nlinarith [hle, hlt]

/-- **The full plane-level certificate**: the round ball containing `K`, its disc homeomorphism, and
the half-space property at every boundary point. -/
theorem exists_openBall_superset_all {K : Set ℂ} (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ K ⊆ Metric.ball (0 : ℂ) R ∧
      Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥(Metric.ball (0 : ℂ) R)) ∧
      ∀ p ∈ Metric.sphere (0 : ℂ) R, ∀ z ∈ Metric.ball (0 : ℂ) R,
        inner ℝ p z < inner ℝ p p := by
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_ball (0 : ℂ)
  set R : ℝ := |R₀| + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hsub : Metric.ball (0 : ℂ) R₀ ⊆ Metric.ball (0 : ℂ) R :=
    Metric.ball_subset_ball (by rw [hRdef]; linarith [le_abs_self R₀])
  -- the homeomorphism with the unit disc
  have hhomeo : Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥(Metric.ball (0 : ℂ) R)) := by
    have hconv : Convex ℝ (Metric.closedBall (0 : ℂ) R) := convex_closedBall (0 : ℂ) R
    have hne : (interior (Metric.closedBall (0 : ℂ) R)).Nonempty := by
      rw [interior_closedBall_eq_ball hRpos]
      exact ⟨0, by simp [hRpos]⟩
    have hbdd : Bornology.IsBounded (Metric.closedBall (0 : ℂ) R) :=
      (isCompact_closedBall (x := (0 : ℂ)) (r := R)).isBounded
    obtain ⟨h, h1, -, -⟩ :=
      exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hne hbdd
    rw [interior_closedBall_eq_ball hRpos] at h1
    exact ⟨((h.image (Metric.ball (0 : ℂ) R)).trans (Homeomorph.setCongr h1)).symm⟩
  refine ⟨R, hRpos, hR₀.trans hsub, hhomeo, ?_⟩
  intro p hp z hz
  have hpnorm : ‖p - 0‖ = R := by
    rw [Metric.mem_sphere, dist_eq_norm] at hp; simpa using hp
  have hznorm : ‖z - 0‖ < R := by
    rw [Metric.mem_ball, dist_eq_norm] at hz; simpa using hz
  have hself : inner ℝ p p = R ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
    have h2 : ‖p‖ = R := by simpa using hpnorm
    rw [h2]
  have hle : inner ℝ p z ≤ R * ‖z‖ := by
    have h1 : inner ℝ p z ≤ ‖p‖ * ‖z‖ := real_inner_le_norm p z
    have h2 : ‖p‖ = R := by simpa using hpnorm
    rwa [h2] at h1
  have hlt : R * ‖z‖ < R * R := by
    have h2 : ‖z‖ = ‖z - 0‖ := by rw [sub_zero]
    nlinarith [hRpos, hznorm]
  rw [hself]
  nlinarith [hle, hlt]

end PlanePiece

/-- **The conclusion of `regularPiece_core` from a single atlas chart ball with room.**

This is the *endgame* of the single-chart route to `regularPiece_core`: if `K` is contained in the
source of a member `φ` of the atlas, with `φ '' K` inside a round ball `ball c ρ` whose closed ball
sits in `φ.target`, then `U := φ.symm '' ball c ρ` is the required piece: it is open, homeomorphic to
the unit disc (hence connected and simply connected), has compact closure, connected frontier
`φ.symm '' sphere c ρ`, contains `K`, and satisfies the sector condition at every frontier point —
because in the chart `φ` itself, `U` is the round ball `ball c ρ`, whose complement contains the
outer half-plane at every boundary point (`sectorComplement_of_single_ball`). -/
theorem exists_regularPiece_of_atlasChartBall {φ : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ atlas ℂ X) {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {K : Set X} (hKsrc : K ⊆ φ.source)
    (himg : φ '' K ⊆ Metric.ball c ρ) (hsub : Metric.closedBall c ρ ⊆ φ.target) :
    ∃ U : Set X, IsOpen U ∧ Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥U) ∧ IsCompact (closure U) ∧
      IsConnected (frontier (closure U)) ∧ K ⊆ U ∧
      ∀ p ∈ frontier U, HasSectorBoundary U p := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := chartBall_transport (X := X) φ hρ hsub
  refine ⟨φ.symm '' Metric.ball c ρ, h1, h6, ?_, ?_, ?_, ?_⟩
  · rw [h2]; exact h4
  · rw [h2]; exact h5
  · intro x hx
    exact ⟨φ x, himg ⟨x, hx, rfl⟩, φ.left_inv (hKsrc hx)⟩
  · intro p hp
    have hballT : Metric.ball c ρ ⊆ φ.target := Metric.ball_subset_closedBall.trans hsub
    have hsphereT : Metric.sphere c ρ ⊆ φ.target := Metric.sphere_subset_closedBall.trans hsub
    have hsymm_inj : ∀ y ∈ φ.target, ∀ z ∈ φ.target, φ.symm y = φ.symm z → y = z := by
      intro y hy z hz hyz
      rw [← φ.right_inv hy, ← φ.right_inv hz, hyz]
    -- identify the frontier of the ball with the image of the sphere
    have hfron : frontier (φ.symm '' Metric.ball c ρ) = φ.symm '' Metric.sphere c ρ := by
      ext x
      constructor
      · intro hx
        have hxcl : x ∈ φ.symm '' Metric.closedBall c ρ := by
          rw [← h2]; exact frontier_subset_closure hx
        have hxU : x ∉ φ.symm '' Metric.ball c ρ := by
          have hh := hx
          rw [IsOpen.frontier_eq h1] at hh
          exact hh.2
        obtain ⟨z, hz, hzx⟩ := hxcl
        have hzle : dist z c ≤ ρ := Metric.mem_closedBall.mp hz
        have hznlt : ¬ dist z c < ρ := by
          intro h
          exact hxU ⟨z, by rwa [Metric.mem_ball], hzx⟩
        exact ⟨z, Metric.mem_sphere.mpr (le_antisymm hzle (not_lt.mp hznlt)), hzx⟩
      · rintro ⟨z, hz, hzx⟩
        rw [IsOpen.frontier_eq h1]
        refine ⟨?_, ?_⟩
        · rw [h2]; exact ⟨z, Metric.sphere_subset_closedBall hz, hzx⟩
        · rintro ⟨z', hz', hz'x⟩
          have hzz : z' = z := hsymm_inj z' (hballT hz') z (hsphereT hz) (by rw [hz'x, hzx])
          have h1' : dist z' c < ρ := Metric.mem_ball.mp hz'
          have h2' : dist z c = ρ := Metric.mem_sphere.mp hz
          rw [hzz, h2'] at h1'
          exact lt_irrefl _ h1'
    rw [hfron] at hp
    obtain ⟨w, hwmem, hwp⟩ := hp
    have hwt : w ∈ φ.target := hsphereT hwmem
    have hqm : ‖w - c‖ = ρ := by
      have h := hwmem
      rw [Metric.mem_sphere, dist_eq_norm] at h
      exact h
    have hpsrc : p ∈ φ.source := by
      rw [← hwp]
      exact (φ.symm).map_source hwt
    have hpval : φ p = w := by
      rw [← hwp]
      exact φ.right_inv hwt
    obtain ⟨L₁, L₂, hL₁, hL₂, hsec, havoid⟩ := sectorComplement_of_single_ball c hρ hqm
    refine ⟨φ, φ.source, L₁, L₂, hφ, φ.open_source, hpsrc, subset_rfl, hpsrc, hL₁, hL₂, hsec, ?_⟩
    intro x hx
    obtain ⟨hxU, -⟩ := hx
    have hxball : φ x ∈ Metric.ball c ρ := by
      obtain ⟨z, hz, hzx⟩ := hxU
      rw [← hzx, φ.right_inv (hballT hz)]
      exact hz
    rw [hpval]
    exact havoid (φ x) (Metric.ball_subset_closedBall hxball)

/-- **`regularPiece_core` follows from the "planarity" input `(∗)` for an atlas chart.** -/
theorem regularPiece_core_of_atlasChartBall (hX : ¬ CompactSpace X) {K : Set X}
    (h : ∃ (φ : OpenPartialHomeomorph X ℂ) (c : ℂ) (ρ : ℝ), φ ∈ atlas ℂ X ∧ 0 < ρ ∧
      K ⊆ φ.source ∧ φ '' K ⊆ Metric.ball c ρ ∧ Metric.closedBall c ρ ⊆ φ.target) :
    ∃ U : Set X, IsOpen U ∧ Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥U) ∧
      IsCompact (closure U) ∧ IsConnected (frontier (closure U)) ∧ K ⊆ U ∧
      ∀ p ∈ frontier U, Work.SimplyConnected.ABS.HasSectorBoundary U p := by
  obtain ⟨φ, c, ρ, hφ, hρ, hKsrc, himg, hsub⟩ := h
  exact exists_regularPiece_of_atlasChartBall hφ hρ hKsrc himg hsub

-- (The former placeholder `sectorCondition_of_saturated_family` was replaced by the proved
-- base case in `Submission.Work.SimplyConnected.ABS.sectorCondition_of_chart_balls`
-- (`hasSectorBoundary_or_hasRayBoundary_iUnion_chartBall`), and by the delegated lemma
-- `Work.SimplyConnected.ABS.hasRayBoundary_interior_ballUnion`, which removes the common-chart
-- hypothesis from that statement.)


/-- **The `ℂ` case of the target.**  Given a diffeomorphism `e : X ≅ ℂ`, every compact `K ⊆ X` is
contained in a piece satisfying the whole conclusion of `regularPiece_core`.

Take the round ball `B := Metric.ball 0 R ⊇ e '' K` of `exists_openBall_superset_all` and put
`U := e ⁻¹' B`.  Openness, the disc homeomorphism (via `e`), compactness of the closure,
connectedness of the frontier and `K ⊆ U` are immediate from `e` being a homeomorphism.  For the
sector condition at `p ∈ frontier U`, take the chart `c := chartAt ℂ p` and the function
`F := fun w => inner ℝ (e p) (e (c.symm w)) - inner ℝ (e p) (e p)`: then `F (c p) = 0`, and for
`x ∈ U` one has `F (c x) = inner ℝ (e p) (e x) - inner ℝ (e p) (e p) < 0` by the half-space
property of the ball; moreover `HasFDerivAt F L (c p)` with `L ≠ 0`, because the chart
representation `e ∘ c.symm` of `e` is analytic (`Work.Parabolic.analyticAt_chart_representation_infty`)
and its derivative does not vanish (`Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic`).
Then `sectorComplement_of_hasFDerivAt` produces the two functionals of `HasSectorBoundary`. -/
theorem exists_regularPiece_of_diffeomorph_plane {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (e : X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)
    {K : Set X} (hK : IsCompact K) :
    ∃ U : Set X, IsOpen U ∧ Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥U) ∧
      IsCompact (closure U) ∧ IsConnected (frontier (closure U)) ∧ K ⊆ U ∧
      ∀ p ∈ frontier U, HasSectorBoundary U p := by
  classical
  obtain ⟨R, hRpos, hKR, hhomeo, hhalf⟩ := exists_openBall_superset_all (hK.image e.continuous)
  set B : Set ℂ := Metric.ball (0 : ℂ) R with hB
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hsurj : Function.Surjective (e.toHomeomorph : X → ℂ) := e.toHomeomorph.surjective
  refine ⟨e.toHomeomorph ⁻¹' B, hBopen.preimage e.toHomeomorph.continuous, ?_, ?_, ?_, ?_, ?_⟩
  · -- the disc homeomorphism
    obtain ⟨hball⟩ := hhomeo
    have himg : e.toHomeomorph '' (e.toHomeomorph ⁻¹' B) = B :=
      Set.image_preimage_eq _ hsurj
    have h1 : ↥(e.toHomeomorph ⁻¹' B) ≃ₜ ↥B :=
      (e.toHomeomorph.image (e.toHomeomorph ⁻¹' B)).trans (Homeomorph.setCongr himg)
    exact ⟨hball.trans h1.symm⟩
  · -- compact closure
    have hcl : closure (e.toHomeomorph ⁻¹' B) ⊆ e.toHomeomorph ⁻¹' Metric.closedBall (0 : ℂ) R := by
      rw [← Homeomorph.preimage_closure (h := e.toHomeomorph) (s := Metric.ball (0 : ℂ) R),
        closure_ball (0 : ℂ) hRpos.ne']
    exact ((e.toHomeomorph.isCompact_preimage).mpr
      (isCompact_closedBall (x := (0 : ℂ)) (r := R))).of_isClosed_subset isClosed_closure hcl
  · -- connected frontier
    have hfr : frontier (closure (e.toHomeomorph ⁻¹' B)) = e.toHomeomorph ⁻¹' Metric.sphere (0 : ℂ) R := by
      rw [← Homeomorph.preimage_closure (h := e.toHomeomorph) (s := Metric.ball (0 : ℂ) R),
        ← Homeomorph.preimage_frontier, closure_ball (0 : ℂ) hRpos.ne',
        frontier_closedBall_eq_sphere hRpos]
    rw [hfr]
    have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
    exact (e.toHomeomorph.isConnected_preimage).mpr (isConnected_sphere hrank 0 hRpos.le)
  · -- containment
    intro x hx
    exact hKR ⟨x, hx, rfl⟩
  · -- the sector condition
    intro p hp
    have hp_sphere : e p ∈ Metric.sphere (0 : ℂ) R := by
      have h2 : e p ∈ frontier B := by
        have h3 : frontier (e.toHomeomorph ⁻¹' B) = e.toHomeomorph ⁻¹' frontier B := by
          rw [← Homeomorph.preimage_frontier]
        rw [h3] at hp
        exact hp
      rw [hB, frontier_ball_eq_sphere hRpos] at h2
      exact h2
    set c : OpenPartialHomeomorph X ℂ := chartAt ℂ p with hc
    have hpsrc : p ∈ c.source := mem_chart_source ℂ p
    have hcp : c p = (chartAt ℂ p) p := rfl
    set G : ℂ → ℂ := fun z => e (c.symm z) with hG
    have hGcp : G (c p) = e p := by
      simp only [hG, hc]
      rw [OpenPartialHomeomorph.left_inv (chartAt ℂ p) (mem_chart_source ℂ p)]
    have hGan : AnalyticAt ℂ G (c p) := by
      have h := Work.Parabolic.analyticAt_chart_representation_infty (X := X) (Y := ℂ)
        (Φ := (e : X → ℂ)) e.contMDiff p
      have h' : (fun z => (chartAt ℂ (e p)) (e ((chartAt ℂ p).symm z))) = G := by
        funext z
        simp only [hG, hc, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq]
      rwa [h'] at h
    have hderiv : deriv G (c p) ≠ 0 := by
      have h := Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic (X := X)
        (Φ := (e : X → ℂ)) e.injective (fun y => by
          have h2 := Work.Parabolic.analyticAt_chart_representation_infty (X := X) (Y := ℂ)
            (Φ := (e : X → ℂ)) e.contMDiff y
          have h3 : (fun z => (chartAt ℂ (e y)) (e ((chartAt ℂ y).symm z)))
              = fun z => e ((chartAt ℂ y).symm z) := by
            funext z
            simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq]
          rwa [h3] at h2)
        (Submission.exists_ne_of_chartedSpace p)
      rw [show (⇑e ∘ ⇑(chartAt ℂ p).symm) = G from by
        funext z; simp only [Function.comp_apply, hG, hc]] at h
      exact h
    have hGder : HasFDerivAt G (ContinuousLinearMap.toSpanSingleton ℂ (deriv G (c p))) (c p) :=
      (hGan.differentiableAt.hasDerivAt).hasFDerivAt
    set D : ℂ →L[ℝ] ℂ :=
      (ContinuousLinearMap.toSpanSingleton ℂ (deriv G (c p))).restrictScalars ℝ with hD
    have hGderR : HasFDerivAt G D (c p) := by
      rw [hD]
      exact hGder.restrictScalars ℝ
    set M : ℂ →L[ℝ] ℝ := innerSL ℝ (e p) with hM
    have hep_ne : e p ≠ 0 := by
      intro h
      have h2 := hp_sphere
      rw [Metric.mem_sphere, h, dist_zero_right, norm_zero] at h2
      linarith [hRpos]
    have hMpos : 0 < M (e p) := by
      simp only [hM, innerSL_apply_apply]
      exact real_inner_self_pos.mpr hep_ne
    have hMne : M ≠ 0 := by
      intro h0
      have h1 : M (e p) = 0 := by rw [h0]; rfl
      linarith [hMpos]
    have hDval : ∀ v : ℂ, D v = deriv G (c p) • v := by
      intro v
      rw [hD, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply]
      simp [mul_comm]
    have hLne : M.comp D ≠ 0 := by
      intro h0
      have h1 : ∀ v : ℂ, M (D v) = 0 := fun v => by
        have h2 := congrArg (fun (L : ℂ →L[ℝ] ℝ) => L v) h0
        simpa using h2
      have h3 : M (D ((deriv G (c p))⁻¹ * e p)) = 0 := h1 _
      rw [hDval] at h3
      have h4 : deriv G (c p) • ((deriv G (c p))⁻¹ * e p) = e p := by
        rw [smul_eq_mul]
        field_simp
      rw [h4] at h3
      linarith [hMpos]
    have hFder : HasFDerivAt (fun w => M (G w) - M (G (c p)))
        (M.comp D) (c p) := by
      have h1 : HasFDerivAt (fun w => M (G w)) (M.comp D) (c p) :=
        (M.hasFDerivAt).comp (c p) hGderR
      simpa using h1.sub_const (M (G (c p)))
    have hFcp : (fun w => M (G w) - M (G (c p))) (c p) = 0 := by simp
    obtain ⟨L₁, L₂, hL₁, hL₂, hsec, δ, hδpos, havoid⟩ :=
      sectorComplement_of_hasFDerivAt hFder hFcp hLne
    have hFneg : ∀ x ∈ e.toHomeomorph ⁻¹' B, x ∈ c.source →
        (fun w => M (G w) - M (G (c p))) (c x) < 0 := by
      intro x hx hxsrc
      have hx' : e x ∈ B := hx
      have h1 : inner ℝ (e p) (e x) < inner ℝ (e p) (e p) := hhalf (e p) hp_sphere (e x) hx'
      have hGx : G (c x) = e x := by
        simp only [hG]
        rw [c.left_inv hxsrc]
      simp only [hGx, hGcp, hM, innerSL_apply_apply]
      linarith [h1]
    have hVopen : IsOpen (c.source ∩ c ⁻¹' {w : ℂ | ‖w - c p‖ < δ}) :=
      c.continuousOn.isOpen_inter_preimage c.open_source
        (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
    have hpV : p ∈ c.source ∩ c ⁻¹' {w : ℂ | ‖w - c p‖ < δ} := by
      refine ⟨hpsrc, ?_⟩
      show ‖c p - c p‖ < δ
      rw [sub_self, norm_zero]
      exact hδpos
    refine ⟨c, c.source ∩ c ⁻¹' {w : ℂ | ‖w - c p‖ < δ}, L₁, L₂, chart_mem_atlas ℂ p,
      hVopen, hpV, Set.inter_subset_left, hpsrc, hL₁, hL₂, hsec, ?_⟩
    intro x hx
    obtain ⟨hxU, hxV⟩ := hx
    have hxnorm : ‖c x - c p‖ < δ := hxV.2
    have hneg : (fun w => M (G w) - M (G (c p))) (c p + (c x - c p)) < 0 := by
      rw [show c p + (c x - c p) = c x from by ring]
      exact hFneg x hxU hxV.1
    exact havoid (c x - c p) hxnorm hneg

/-- For `R > 0` the round ball of radius `R` and the unit disc are homeomorphic. -/
lemma ballHomeo_of_pos {R : ℝ} (hR : 0 < R) :
    Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥(Metric.ball (0 : ℂ) R)) := by
  have hconv : Convex ℝ (Metric.closedBall (0 : ℂ) R) := convex_closedBall (0 : ℂ) R
  have hne : (interior (Metric.closedBall (0 : ℂ) R)).Nonempty := by
    rw [interior_closedBall_eq_ball hR]
    exact ⟨0, by simp [hR]⟩
  have hbdd : Bornology.IsBounded (Metric.closedBall (0 : ℂ) R) :=
    (isCompact_closedBall (x := (0 : ℂ)) (r := R)).isBounded
  obtain ⟨h, h1, -, -⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hne hbdd
  rw [interior_closedBall_eq_ball hR] at h1
  exact ⟨((h.image (Metric.ball (0 : ℂ) R)).trans (Homeomorph.setCongr h1)).symm⟩

/-- The inner-product half-space property of a round ball at its boundary points. -/
lemma inner_lt_self_of_mem_sphere {R : ℝ} (hR : 0 < R) {p z : ℂ}
    (hp : p ∈ Metric.sphere (0 : ℂ) R) (hz : z ∈ Metric.ball (0 : ℂ) R) :
    inner ℝ p z < inner ℝ p p := by
  have hpnorm : ‖p‖ = R := by simpa [dist_eq_norm] using hp
  have hznorm : ‖z‖ < R := by simpa [dist_eq_norm] using hz
  have hself : inner ℝ p p = R ^ 2 := by rw [real_inner_self_eq_norm_sq, hpnorm]
  have hle : inner ℝ p z ≤ R * ‖z‖ := by
    have h1 : inner ℝ p z ≤ ‖p‖ * ‖z‖ := real_inner_le_norm p z
    rwa [hpnorm] at h1
  have hlt : R * ‖z‖ < R * R := by nlinarith [hR, hznorm]
  rw [hself]; nlinarith [hle, hlt]

/-- A compact subset of a round ball is contained in a strictly smaller round ball. -/
lemma exists_ball_of_isCompact_subset_ball {K : Set ℂ} (hK : IsCompact K) {R₁ : ℝ}
    (hR₁ : 0 < R₁) (hK₁ : K ⊆ Metric.ball (0 : ℂ) R₁) :
    ∃ R : ℝ, 0 < R ∧ R < R₁ ∧ K ⊆ Metric.ball (0 : ℂ) R := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨R₁ / 2, by linarith, by linarith, by simp⟩
  · obtain ⟨z₀, hz₀K, hz₀max⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
    have hz₀lt : ‖z₀‖ < R₁ := by
      have h := hK₁ hz₀K
      simpa [dist_eq_norm] using h
    refine ⟨(‖z₀‖ + R₁) / 2, by linarith [norm_nonneg z₀], by linarith, fun z hz => ?_⟩
    have h1 : ‖z‖ ≤ ‖z₀‖ := hz₀max hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    linarith

/-- A general "coercion" homeomorphism: for `S ⊆ B`, the subtype of points of `↥B` lying in `S` is
homeomorphic to `↥S`. -/
lemma homeomorph_subtype_coe {B S : Set ℂ} (hSB : S ⊆ B) :
    Nonempty (↥{z : ↥B | (z : ℂ) ∈ S} ≃ₜ ↥S) := by
  let f : ↥{z : ↥B | (z : ℂ) ∈ S} → ↥S := fun z => ⟨(z.1 : ℂ), z.2⟩
  let g : ↥S → ↥{z : ↥B | (z : ℂ) ∈ S} := fun w => ⟨⟨(w : ℂ), hSB w.2⟩, w.2⟩
  have hfg : Function.LeftInverse g f := fun z => Subtype.ext (Subtype.ext rfl)
  have hgf : Function.RightInverse g f := fun w => Subtype.ext rfl
  have hf : Continuous f :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun z => z.2)
  have hg : Continuous g :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val (fun w => hSB w.2))
      (fun w => w.2)
  let e : ↥{z : ↥B | (z : ℂ) ∈ S} ≃ ↥S :=
    { toFun := f, invFun := g, left_inv := hfg, right_inv := hgf }
  exact ⟨{ toEquiv := e, continuous_toFun := hf, continuous_invFun := hg }⟩

/-- The subtype of a subtype: `{z : ↥B | (z : ℂ) ∈ ball R}` is homeomorphic to `↥(ball R)`. -/
lemma homeomorph_subtype_coe_ball {B : Set ℂ} {R : ℝ}
    (hRB : Metric.ball (0 : ℂ) R ⊆ B) :
    Nonempty (↥{z : ↥B | (z : ℂ) ∈ Metric.ball (0 : ℂ) R} ≃ₜ ↥(Metric.ball (0 : ℂ) R)) :=
  homeomorph_subtype_coe hRB

/-- The subtype points of the unit disc lying in a smaller closed ball form a compact set. -/
lemma isCompact_subtype_mem_closedBall {R : ℝ} (hR : R < 1) :
    IsCompact {z : ↥(Metric.ball (0 : ℂ) 1) | (z : ℂ) ∈ Metric.closedBall (0 : ℂ) R} := by
  have hmem : ∀ w : ℂ, w ∈ Metric.closedBall (0 : ℂ) R → w ∈ Metric.ball (0 : ℂ) 1 := by
    intro w hw
    have h2 : ‖w‖ ≤ R := by simpa [dist_eq_norm] using hw
    simpa [Metric.mem_ball, dist_eq_norm] using lt_of_le_of_lt h2 hR
  have himg : {z : ↥(Metric.ball (0 : ℂ) 1) | (z : ℂ) ∈ Metric.closedBall (0 : ℂ) R} =
      (fun w : ↥(Metric.closedBall (0 : ℂ) R) =>
        (⟨(w : ℂ), hmem w w.2⟩ : ↥(Metric.ball (0 : ℂ) 1))) '' Set.univ := by
    ext z
    constructor
    · intro hz
      exact ⟨⟨(z : ℂ), hz⟩, trivial, Subtype.ext rfl⟩
    · rintro ⟨w, -, hwz⟩
      rw [← hwz]
      simp only [Set.mem_setOf_eq]
      exact w.2
  rw [himg]
  exact isCompact_univ.image (Continuous.subtype_mk continuous_subtype_val (fun w => hmem w w.2))

/-- **The sector condition at a frontier point of the preimage of a round ball.**

If `Φ : X → ℂ` is an injective `C^∞` map (a local biholomorphism, e.g. the chart representative of a
diffeomorphism), `R > 0` and `Φ p` lies on the sphere of radius `R`, then the set
`Φ ⁻¹' Metric.ball (0 : ℂ) R` satisfies the sector condition at `p`.  The argument is the one of the
plane-level endgame: `F := inner ℝ (Φ p) ∘ Φ - inner ℝ (Φ p) (Φ p)` vanishes at `p`, is negative on
`Φ ⁻¹' ball (0,R)`, and has non-zero derivative at `p`. -/
lemma hasSectorBoundary_preimage_ball {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Φ : X → ℂ} (hΦcd : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ Φ)
    (hΦinj : Function.Injective Φ) {R : ℝ} (hR : 0 < R)
    (hhalf : ∀ p ∈ Metric.sphere (0 : ℂ) R, ∀ z ∈ Metric.ball (0 : ℂ) R,
      inner ℝ p z < inner ℝ p p)
    {p : X} (hp : Φ p ∈ Metric.sphere (0 : ℂ) R) :
    HasSectorBoundary (Φ ⁻¹' Metric.ball (0 : ℂ) R) p := by
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ p with hc
  have hpsrc : p ∈ c.source := mem_chart_source ℂ p
  set G : ℂ → ℂ := fun z => Φ (c.symm z) with hG
  have hGcp : G (c p) = Φ p := by
    simp only [hG, hc]
    rw [OpenPartialHomeomorph.left_inv (chartAt ℂ p) (mem_chart_source ℂ p)]
  have hGan : AnalyticAt ℂ G (c p) := by
    have h := Work.Parabolic.analyticAt_chart_representation_infty (X := X) (Y := ℂ)
      (Φ := Φ) hΦcd p
    have h' : (fun z => (chartAt ℂ (Φ p)) (Φ ((chartAt ℂ p).symm z))) = G := by
      funext z
      simp only [hG, hc, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq]
    rwa [h'] at h
  have hderiv : deriv G (c p) ≠ 0 := by
    have h := Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic (X := X)
      (Φ := Φ) hΦinj (fun y => by
        have h2 := Work.Parabolic.analyticAt_chart_representation_infty (X := X) (Y := ℂ)
          (Φ := Φ) hΦcd y
        have h3 : (fun z => (chartAt ℂ (Φ y)) (Φ ((chartAt ℂ y).symm z)))
            = fun z => Φ ((chartAt ℂ y).symm z) := by
          funext z
          simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq]
        rwa [h3] at h2)
      (Submission.exists_ne_of_chartedSpace p)
    rw [show (Φ ∘ ⇑(chartAt ℂ p).symm) = G from by
      funext z; simp only [Function.comp_apply, hG, hc]] at h
    exact h
  have hGder : HasFDerivAt G (ContinuousLinearMap.toSpanSingleton ℂ (deriv G (c p))) (c p) :=
    (hGan.differentiableAt.hasDerivAt).hasFDerivAt
  set D : ℂ →L[ℝ] ℂ :=
    (ContinuousLinearMap.toSpanSingleton ℂ (deriv G (c p))).restrictScalars ℝ with hD
  have hGderR : HasFDerivAt G D (c p) := by
    rw [hD]
    exact hGder.restrictScalars ℝ
  set M : ℂ →L[ℝ] ℝ := innerSL ℝ (Φ p) with hM
  have hp_ne : Φ p ≠ 0 := by
    intro h
    have h2 := hp
    rw [Metric.mem_sphere, h, dist_zero_right, norm_zero] at h2
    linarith [hR]
  have hMpos : 0 < M (Φ p) := by
    simp only [hM, innerSL_apply_apply]
    exact real_inner_self_pos.mpr hp_ne
  have hMne : M ≠ 0 := by
    intro h0
    have h1 : M (Φ p) = 0 := by rw [h0]; rfl
    linarith [hMpos]
  have hDval : ∀ v : ℂ, D v = deriv G (c p) • v := by
    intro v
    rw [hD, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply]
    simp [mul_comm]
  have hLne : M.comp D ≠ 0 := by
    intro h0
    have h1 : ∀ v : ℂ, M (D v) = 0 := fun v => by
      have h2 := congrArg (fun (L : ℂ →L[ℝ] ℝ) => L v) h0
      simpa using h2
    have h3 : M (D ((deriv G (c p))⁻¹ * Φ p)) = 0 := h1 _
    rw [hDval] at h3
    have h4 : deriv G (c p) • ((deriv G (c p))⁻¹ * Φ p) = Φ p := by
      rw [smul_eq_mul]
      field_simp
    rw [h4] at h3
    linarith [hMpos]
  have hFder : HasFDerivAt (fun w => M (G w) - M (G (c p))) (M.comp D) (c p) := by
    have h1 : HasFDerivAt (fun w => M (G w)) (M.comp D) (c p) :=
      (M.hasFDerivAt).comp (c p) hGderR
    simpa using h1.sub_const (M (G (c p)))
  have hFcp : (fun w => M (G w) - M (G (c p))) (c p) = 0 := by simp
  obtain ⟨L₁, L₂, hL₁, hL₂, hsec, δ, hδpos, havoid⟩ :=
    sectorComplement_of_hasFDerivAt hFder hFcp hLne
  have hFneg : ∀ x ∈ Φ ⁻¹' Metric.ball (0 : ℂ) R, x ∈ c.source →
      (fun w => M (G w) - M (G (c p))) (c x) < 0 := by
    intro x hx hxsrc
    have hx' : Φ x ∈ Metric.ball (0 : ℂ) R := hx
    have h1 : inner ℝ (Φ p) (Φ x) < inner ℝ (Φ p) (Φ p) := hhalf (Φ p) hp (Φ x) hx'
    have hGx : G (c x) = Φ x := by
      simp only [hG]
      rw [c.left_inv hxsrc]
    simp only [hGx, hGcp, hM, innerSL_apply_apply]
    linarith [h1]
  have hVopen : IsOpen (c.source ∩ c ⁻¹' {w : ℂ | ‖w - c p‖ < δ}) :=
    c.continuousOn.isOpen_inter_preimage c.open_source
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
  have hpV : p ∈ c.source ∩ c ⁻¹' {w : ℂ | ‖w - c p‖ < δ} := by
    refine ⟨hpsrc, ?_⟩
    show ‖c p - c p‖ < δ
    rw [sub_self, norm_zero]
    exact hδpos
  refine ⟨c, c.source ∩ c ⁻¹' {w : ℂ | ‖w - c p‖ < δ}, L₁, L₂, chart_mem_atlas ℂ p,
    hVopen, hpV, Set.inter_subset_left, hpsrc, hL₁, hL₂, hsec, ?_⟩
  intro x hx
  obtain ⟨hxU, hxV⟩ := hx
  have hxnorm : ‖c x - c p‖ < δ := hxV.2
  have hneg : (fun w => M (G w) - M (G (c p))) (c p + (c x - c p)) < 0 := by
    rw [show c p + (c x - c p) = c x from by ring]
    exact hFneg x hxU hxV.1
  exact havoid (c x - c p) hxnorm hneg

/-- A point of the closed ball of radius `R` shrunk by `t ∈ (0,1)` lies in the open ball. -/
lemma smul_mem_ball_of_mem_closedBall {t R : ℝ} (h0 : 0 < t) (h1 : t < 1) (hR : 0 < R)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R) : t • z ∈ Metric.ball (0 : ℂ) R := by
  have hzn : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul, Real.norm_of_nonneg h0.le]
  nlinarith

/-- **The disc case of the target.**  Same as `exists_regularPiece_of_diffeomorph_plane` with `ℂ`
replaced by the open unit disc, where the round ball of the construction must be chosen inside the
disc (which is possible because a compact subset of the disc is bounded away from the boundary).
The half-plane case follows by composing with the Cayley diffeomorphism `ℍ ≅ 𝔻`
(`Commons.Analysis.Complex.UpperHalfPlane.halfPlane_disc_diffeomorph`). -/
theorem exists_regularPiece_of_diffeomorph_disc {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (e : X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ Submission.Helpers.DiscOpen)
    {K : Set X} (hK : IsCompact K) :
    ∃ U : Set X, IsOpen U ∧ Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥U) ∧
      IsCompact (closure U) ∧ IsConnected (frontier (closure U)) ∧ K ⊆ U ∧
      ∀ p ∈ frontier U, HasSectorBoundary U p := by
  classical
  set E : X → ℂ := fun x => (e x : ℂ) with hEdef
  have hEcont : Continuous E := continuous_subtype_val.comp e.continuous
  have hEopen : IsOpenMap E :=
    Metric.isOpen_ball.isOpenMap_subtype_val.comp e.toHomeomorph.isOpenMap
  have hEcd : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ E :=
    contMDiff_subtype_val.comp e.contMDiff
  have hEinj : Function.Injective E := fun x y hxy => e.injective (Subtype.ext hxy)
  have hE1 : ∀ x : X, E x ∈ Metric.ball (0 : ℂ) 1 := fun x => (e x).2
  have hKeq : E '' K ⊆ Metric.ball (0 : ℂ) 1 := by rintro z ⟨x, -, rfl⟩; exact hE1 x
  obtain ⟨R, hRpos, hRlt, hKR⟩ :=
    exists_ball_of_isCompact_subset_ball (hK.image hEcont) (by norm_num) hKeq
  set U : Set X := E ⁻¹' Metric.ball (0 : ℂ) R with hUdef
  have hhalf : ∀ p ∈ Metric.sphere (0 : ℂ) R, ∀ z ∈ Metric.ball (0 : ℂ) R,
      inner ℝ p z < inner ℝ p p := fun p hp z hz => inner_lt_self_of_mem_sphere hRpos hp hz
  -- the closure and the frontier
  have hcl : closure U = E ⁻¹' Metric.closedBall (0 : ℂ) R := by
    rw [hUdef, ← hEopen.preimage_closure_eq_closure_preimage hEcont (Metric.ball (0 : ℂ) R),
      closure_ball (0 : ℂ) hRpos.ne']
  have hfr : frontier (closure U) = E ⁻¹' Metric.sphere (0 : ℂ) R := by
    rw [hcl, ← hEopen.preimage_frontier_eq_frontier_preimage hEcont (Metric.closedBall (0 : ℂ) R),
      frontier_closedBall_eq_sphere hRpos]
  have hfrU : frontier U = E ⁻¹' Metric.sphere (0 : ℂ) R := by
    rw [hUdef, ← hEopen.preimage_frontier_eq_frontier_preimage hEcont (Metric.ball (0 : ℂ) R),
      frontier_ball_eq_sphere hRpos]
  refine ⟨U, Metric.isOpen_ball.preimage hEcont, ?_, ?_, ?_, ?_, ?_⟩
  · -- the disc homeomorphism
    obtain ⟨hball⟩ := ballHomeo_of_pos (R := R) hRpos
    have h1 : ↥U ≃ₜ ↥{z : ↥(Metric.ball (0 : ℂ) 1) | (z : ℂ) ∈ Metric.ball (0 : ℂ) R} :=
      Homeomorph.subtype e.toHomeomorph (fun x => by
        simp only [hEdef, hUdef, Set.mem_preimage, Diffeomorph.coe_toHomeomorph, Set.mem_ofPred_eq,
          Metric.mem_ball, dist_eq_norm, sub_zero])
    obtain ⟨h2⟩ := homeomorph_subtype_coe_ball (B := Metric.ball (0 : ℂ) 1) (R := R)
      (Metric.ball_subset_ball hRlt.le)
    exact ⟨hball.trans (h1.trans h2).symm⟩
  · -- compact closure
    rw [hcl]
    have heq : E ⁻¹' Metric.closedBall (0 : ℂ) R =
        e.toHomeomorph ⁻¹'
          {z : ↥(Metric.ball (0 : ℂ) 1) | (z : ℂ) ∈ Metric.closedBall (0 : ℂ) R} := by
      rw [show E = (Subtype.val : ↥(Metric.ball (0 : ℂ) 1) → ℂ) ∘ (⇑e.toHomeomorph) from by
        funext x; exact (Diffeomorph.coe_toHomeomorph e).symm ▸ rfl, Set.preimage_comp]
      rfl
    rw [heq]
    exact (e.toHomeomorph.isCompact_preimage).mpr (isCompact_subtype_mem_closedBall hRlt)
  · -- connected frontier
    rw [hfr]
    have h3 : E ⁻¹' Metric.sphere (0 : ℂ) R =
        e.toHomeomorph ⁻¹'
          {z : ↥(Metric.ball (0 : ℂ) 1) | (z : ℂ) ∈ Metric.sphere (0 : ℂ) R} := by
      rw [show E = (Subtype.val : ↥(Metric.ball (0 : ℂ) 1) → ℂ) ∘ (⇑e.toHomeomorph) from by
        funext x; exact (Diffeomorph.coe_toHomeomorph e).symm ▸ rfl, Set.preimage_comp]
      rfl
    rw [h3]
    have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
    haveI : ConnectedSpace ↥(Metric.sphere (0 : ℂ) R) :=
      isConnected_iff_connectedSpace.mp (isConnected_sphere hrank 0 hRpos.le)
    refine (e.toHomeomorph.isConnected_preimage).mpr ?_
    obtain ⟨hS⟩ := homeomorph_subtype_coe (B := Metric.ball (0 : ℂ) 1)
      (S := Metric.sphere (0 : ℂ) R)
      (Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_ball hRlt))
    exact isConnected_iff_connectedSpace.mpr (hS.connectedSpace_iff.mpr inferInstance)
  · -- containment
    intro x hx
    exact hKR ⟨x, hx, rfl⟩
  · -- the sector condition
    intro p hp
    have hp' : E p ∈ Metric.sphere (0 : ℂ) R := by
      have hmem : p ∈ E ⁻¹' Metric.sphere (0 : ℂ) R := by
        rw [← hfrU]
        exact hp
      exact hmem
    exact hasSectorBoundary_preimage_ball hEcd hEinj hRpos hhalf hp'

/-- **The target from the uniformization dichotomy `X ≅ ℂ ∨ X ≅ ℍ`.**  In the first case apply the
`ℂ`-case of the diffeomorphism transport, in the second compose with the Cayley diffeomorphism
`ℍ ≅ 𝔻` and apply the disc case. -/
theorem regularPiece_core_of_dichotomy (hX : ¬ CompactSpace X)
    (h : Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane))
    {K : Set X} (hK : IsCompact K) :
    ∃ U : Set X, IsOpen U ∧ Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥U) ∧
      IsCompact (closure U) ∧ IsConnected (frontier (closure U)) ∧ K ⊆ U ∧
      ∀ p ∈ frontier U, HasSectorBoundary U p := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    exact exists_regularPiece_of_diffeomorph_plane e hK
  · obtain ⟨e⟩ := h
    obtain ⟨d⟩ := Commons.Analysis.Complex.UpperHalfPlane.halfPlane_disc_diffeomorph
    exact exists_regularPiece_of_diffeomorph_disc (e.trans d) hK

/-- **The target in the hyperbolic case**, from a unit-pole Green function on `X`: the workspace's
sorry-free hyperbolic branch of uniformization
(`Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction_of_simplyConnected` fed into
`Work.Parabolic.uniformization_of_greenFunctionAt`) gives the dichotomy, and
`regularPiece_core_of_dichotomy` concludes. -/
theorem regularPiece_core_of_unitGreenFunction (hX : ¬ CompactSpace X)
    (h : ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    {K : Set X} (hK : IsCompact K) :
    ∃ U : Set X, IsOpen U ∧ Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥U) ∧
      IsCompact (closure U) ∧ IsConnected (frontier (closure U)) ∧ K ⊆ U ∧
      ∀ p ∈ frontier U, HasSectorBoundary U p := by
  obtain ⟨z₀, E, hE⟩ := h
  obtain ⟨Φ, hhol, hpole, hmod⟩ :=
    Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction_of_simplyConnected (X := X)
      (z₀ := z₀) hE
  exact regularPiece_core_of_dichotomy hX
    (Work.Parabolic.uniformization_of_greenFunctionAt (X := X) hX hE.isGreenFunctionAt
      hhol hmod hpole) hK


/-! ## The endgame for an arbitrary *locally biholomorphic* chart with room

The reduction `regularPiece_core_of_atlasChartBall` above consumes a chart *of the atlas* with room.
The fleet's planarity statement (`Work.SimplyConnected.ABS.planarity_around_compact`) produces
instead an arbitrary open partial homeomorphism `φ : X → ℂ` with room; in the proof of that
statement (from the uniformization disjunction) `φ` is the composite of a diffeomorphism with the
inclusion of the unit disc, hence **locally biholomorphic**: its chart representatives are analytic
with non-vanishing derivative.  The theorem below is the endgame for that form: no atlas
membership is assumed, and the sector condition at a frontier point `p` is derived by transporting
the round geometry of `φ`'s own chart to the atlas chart `chartAt ℂ p` through the analytic chart
representative `φ ∘ (chartAt ℂ p).symm` (the quadratic Taylor remainder of
`sectorComplement_of_quadraticRemainder`).
-/

/-- **The endgame for an arbitrary locally biholomorphic chart with room.**  If `φ` is an open
partial homeomorphism of `X` into `ℂ` whose chart representatives are analytic with non-vanishing
derivative, and `K` is a compact subset of `φ.source` whose image under `φ` lies in a ball
`ball c ρ` whose closed companion lies in `φ.target`, then the conclusion of `regularPiece_core`
holds for `K`. -/
theorem exists_regularPiece_of_chart_with_room {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {φ : OpenPartialHomeomorph X ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {K : Set X}
    (hKsrc : K ⊆ φ.source) (himg : φ '' K ⊆ Metric.ball c ρ)
    (hsub : Metric.closedBall c ρ ⊆ φ.target)
    (hφan : ∀ p ∈ φ.source, AnalyticAt ℂ (fun w => φ ((chartAt ℂ p).symm w))
      ((chartAt ℂ p) p))
    (hφderiv : ∀ p ∈ φ.source,
      deriv (fun w => φ ((chartAt ℂ p).symm w)) ((chartAt ℂ p) p) ≠ 0) :
    ∃ U : Set X, IsOpen U ∧ Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥U) ∧
      IsCompact (closure U) ∧ IsConnected (frontier (closure U)) ∧ K ⊆ U ∧
      ∀ p ∈ frontier U, HasSectorBoundary U p := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := chartBall_transport (X := X) φ hρ hsub
  have hballT : Metric.ball c ρ ⊆ φ.target := Metric.ball_subset_closedBall.trans hsub
  have hsphereT : Metric.sphere c ρ ⊆ φ.target := Metric.sphere_subset_closedBall.trans hsub
  have hsymm_inj : ∀ y ∈ φ.target, ∀ z ∈ φ.target, φ.symm y = φ.symm z → y = z := by
    intro y hy z hz hyz
    rw [← φ.right_inv hy, ← φ.right_inv hz, hyz]
  have hfron : frontier (φ.symm '' Metric.ball c ρ) = φ.symm '' Metric.sphere c ρ := by
    ext x
    constructor
    · intro hx
      have hxcl : x ∈ φ.symm '' Metric.closedBall c ρ := by
        rw [← h2]; exact frontier_subset_closure hx
      have hxU : x ∉ φ.symm '' Metric.ball c ρ := by
        have hh := hx
        rw [IsOpen.frontier_eq h1] at hh
        exact hh.2
      obtain ⟨z, hz, hzx⟩ := hxcl
      have hzle : dist z c ≤ ρ := Metric.mem_closedBall.mp hz
      have hznlt : ¬ dist z c < ρ := by
        intro h
        exact hxU ⟨z, by rwa [Metric.mem_ball], hzx⟩
      exact ⟨z, Metric.mem_sphere.mpr (le_antisymm hzle (not_lt.mp hznlt)), hzx⟩
    · rintro ⟨z, hz, hzx⟩
      rw [IsOpen.frontier_eq h1]
      refine ⟨?_, ?_⟩
      · rw [h2]; exact ⟨z, Metric.sphere_subset_closedBall hz, hzx⟩
      · rintro ⟨z', hz', hz'x⟩
        have hzz : z' = z := hsymm_inj z' (hballT hz') z (hsphereT hz) (by rw [hz'x, hzx])
        have h1' : dist z' c < ρ := Metric.mem_ball.mp hz'
        have h2' : dist z c = ρ := Metric.mem_sphere.mp hz
        rw [hzz, h2'] at h1'
        exact lt_irrefl _ h1'
  refine ⟨φ.symm '' Metric.ball c ρ, h1, h6, ?_, ?_, ?_, ?_⟩
  · rw [h2]; exact h4
  · rw [h2]; exact h5
  · intro x hx
    exact ⟨φ x, himg ⟨x, hx, rfl⟩, φ.left_inv (hKsrc hx)⟩
  · intro p hp
    rw [hfron] at hp
    obtain ⟨w, hwmem, hwp⟩ := hp
    have hwt : w ∈ φ.target := hsphereT hwmem
    have hqm : ‖w - c‖ = ρ := by
      have h := hwmem
      rw [Metric.mem_sphere, dist_eq_norm] at h
      exact h
    have hpsrc : p ∈ φ.source := by
      rw [← hwp]; exact (φ.symm).map_source hwt
    have hpval : φ p = w := by
      rw [← hwp]; exact φ.right_inv hwt
    set c₀ : OpenPartialHomeomorph X ℂ := chartAt ℂ p with hc₀
    have hpc₀ : p ∈ c₀.source := mem_chart_source ℂ p
    set G : ℂ → ℂ := fun z => φ (c₀.symm z) with hG
    have hGan : AnalyticAt ℂ G (c₀ p) := by
      simpa only [hG, hc₀] using hφan p hpsrc
    have hGderiv : deriv G (c₀ p) ≠ 0 := by
      simpa only [hG, hc₀] using hφderiv p hpsrc
    have hGcp : G (c₀ p) = w := by
      simp only [hG, hc₀, OpenPartialHomeomorph.left_inv _ (mem_chart_source ℂ p), hpval]
    have hFderiv : deriv (fun z => G z - c) (c₀ p) ≠ 0 := by
      rw [deriv_sub_const]; exact hGderiv
    have hne : (fun z => G z - c) (c₀ p) ≠ 0 := by
      intro h
      have hz : w - c = 0 := by rw [← hGcp]; exact h
      rw [hz, norm_zero] at hqm
      linarith
    obtain ⟨C, hC⟩ := quadraticRemainder_of_analyticAt (g := G) (w₀ := c₀ p) hGan
    have hrem : ∃ C : ℝ, ∀ᶠ v in 𝓝 (0 : ℂ),
        ‖(fun z => G z - c) (c₀ p + v) - (fun z => G z - c) (c₀ p)
            - deriv (fun z => G z - c) (c₀ p) * v‖ ≤ C * ‖v‖ ^ 2 := by
      refine ⟨C, ?_⟩
      filter_upwards [hC] with v hv
      have hd : deriv (fun z => G z - c) (c₀ p) = deriv G (c₀ p) := deriv_sub_const c
      rw [hd]
      have heq : (G (c₀ p + v) - c) - (G (c₀ p) - c) - deriv G (c₀ p) * v
          = G (c₀ p + v) - G (c₀ p) - deriv G (c₀ p) * v := by ring
      rw [heq]
      exact hv
    obtain ⟨L₁, L₂, δ, hL₁, hL₂, hδpos, hsectne, hsect⟩ :=
      sectorComplement_of_quadraticRemainder (g := fun z => G z - c) (w₀ := c₀ p)
        (d := deriv (fun z => G z - c) (c₀ p)) hne hFderiv hrem
    refine ⟨c₀, c₀.source ∩ c₀ ⁻¹' Metric.ball (c₀ p) δ, L₁, L₂, chart_mem_atlas ℂ p,
      ?_, ?_, ?_, hpc₀, hL₁, hL₂, hsectne, ?_⟩
    · rw [isOpen_iff_mem_nhds]
      intro x hx
      exact Filter.inter_mem (c₀.open_source.mem_nhds hx.1)
        ((c₀.continuousAt hx.1).preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hx.2))
    · exact ⟨hpc₀, Metric.mem_ball_self hδpos⟩
    · exact Set.inter_subset_left
    · intro x hx
      obtain ⟨hxU, hxV⟩ := hx
      obtain ⟨hxc₀, hxcball⟩ := hxV
      obtain ⟨y, hyball, hyx⟩ := hxU
      have hxφ : φ x = y := by
        rw [← hyx]
        exact φ.right_inv (hballT hyball)
      have hxlt : ‖φ x - c‖ < ρ := by
        rw [hxφ]
        simpa [Metric.mem_ball, dist_eq_norm] using hyball
      have hdist : ‖c₀ x - c₀ p‖ < δ := by
        have h := hxcball
        rwa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at h
      have hFx : (fun z => G z - c) (c₀ x) = φ x - c := by
        simp only [hG, hc₀]
        rw [OpenPartialHomeomorph.left_inv _ hxc₀]
      have hlt : ‖(fun z => G z - c) (c₀ p + (c₀ x - c₀ p))‖
          < ‖(fun z => G z - c) (c₀ p)‖ := by
        rw [show c₀ p + (c₀ x - c₀ p) = c₀ x from by ring, hFx]
        rw [show (fun z => G z - c) (c₀ p) = w - c from by simp only [hGcp]]
        rw [hqm]
        exact hxlt
      exact hsect (c₀ x - c₀ p) hdist hlt

/-- **`regularPiece_core` from a locally biholomorphic chart with room** (existential form). -/
theorem regularPiece_core_of_chart_with_room (hX : ¬ CompactSpace X) {K : Set X}
    (h : ∃ (φ : OpenPartialHomeomorph X ℂ) (c : ℂ) (ρ : ℝ), 0 < ρ ∧ K ⊆ φ.source ∧
      φ '' K ⊆ Metric.ball c ρ ∧ Metric.closedBall c ρ ⊆ φ.target ∧
      (∀ p ∈ φ.source, AnalyticAt ℂ (fun w => φ ((chartAt ℂ p).symm w)) ((chartAt ℂ p) p)) ∧
      (∀ p ∈ φ.source,
        deriv (fun w => φ ((chartAt ℂ p).symm w)) ((chartAt ℂ p) p) ≠ 0)) :
    ∃ U : Set X, IsOpen U ∧ Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥U) ∧
      IsCompact (closure U) ∧ IsConnected (frontier (closure U)) ∧ K ⊆ U ∧
      ∀ p ∈ frontier U, Work.SimplyConnected.ABS.HasSectorBoundary U p := by
  obtain ⟨φ, c, ρ, hρ, hKsrc, himg, hsub, han, hder⟩ := h
  exact exists_regularPiece_of_chart_with_room hρ hKsrc himg hsub han hder

-- (the target `regularPiece_core` is proved at the end of this file, using the endgame for an
-- arbitrary locally biholomorphic chart with room and the delegated planarity input)

/-- **The geometric core of the regular piece.**  Every compact subset `K` of a simply connected non-compact Riemann surface `X` is contained in a relatively compact open set `U`, homeomorphic to the open unit disc, whose closure has connected frontier, and which satisfies the sector (cone) condition `HasSectorBoundary U p` at every frontier point. -/
theorem regularPiece_core (hX : ¬ CompactSpace X) (K : Set X) (hK : IsCompact K) :
    ∃ U : Set X, IsOpen U ∧ Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥U) ∧
      IsCompact (closure U) ∧ IsConnected (frontier (closure U)) ∧ K ⊆ U ∧
      ∀ p ∈ frontier U, Work.SimplyConnected.ABS.HasSectorBoundary U p := by
  -- The whole content is now the geometric input
  -- `Work.SimplyConnected.ABS.exists_chart_with_room_locallyBiholomorphic` (a compatible chart
  -- with room around `K` whose chart representatives are analytic with non-zero derivative); its
  -- *parabolic* case is the single remaining classical input of the project (ABS Theorem 1 /
  -- Mori's normal form: a simply connected non-compact Riemann surface embeds into `ℂ`).
  exact regularPiece_core_of_chart_with_room hX
    (Work.SimplyConnected.ABS.exists_chart_with_room_locallyBiholomorphic hX K hK)
end Work.SimplyConnected.ABS

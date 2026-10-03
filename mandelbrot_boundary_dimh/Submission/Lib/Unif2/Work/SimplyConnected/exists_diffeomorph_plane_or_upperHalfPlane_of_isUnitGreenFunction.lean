import Mathlib
import Submission.Lib.Unif2.Work.UnitGreen.Defs
import Submission.Lib.Unif2.Work.Modulus.Main
import Submission.Lib.Unif2.Work.Parabolic.uniformization_of_greenFunctionAt
import Submission.Lib.Unif2.Work.Modulus.hasTrivialModulusMonodromy_of_periods
import Submission.Lib.Unif2.Work.Modulus.PeriodSetup
import Submission.Lib.Unif2.Work.SimplyConnected.fundamentalGroup_map_surjective_of_punctured
import Submission.Lib.Unif2.Work.Modulus.Unconditional
import Submission.Lib.Unif2.Work.Spine.Main
import Submission.Lib.Unif2.Work.Mori.noNontrivialHomToCircle
import Submission.Lib.Unif2.Work.Mori.torsionFree_abelianization_riemannSurface
import Submission.Lib.Unif2.Work.Mori.torsionFree_abelianization_of_exhaustion
import Submission.Lib.Unif2.Work.Mori.exhaustionUnitGreen
import Submission.Lib.Unif2.Work.Topology.Surface.spine_reduction_library
import Submission.Lib.Unif2.Work.Spine.Surface.isFreeGroup_fundamentalGroup_of_noncompact
import Submission.Lib.Unif2.ExtremalInj
import Submission.Lib.Unif2.Work.Analysis.RiemannSurface.single_simple_zero_at
import Submission.Lib.Unif2.Work.Analysis.RiemannSurface.runge_meromorphic
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.modulus_of_single_zero
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.windingHom

/-!
# A unit-pole Green function on a non-compact surface with `H¹(X,ℝ) = 0` is `ℂ` or `ℍ`

This module is the delegated lemma
`Work.SimplyConnected.exists_diffeomorph_plane_or_upperHalfPlane_of_isUnitGreenFunction`.

## What is proved here (axiom-clean)

* `pathConnectedSpace_of_chartedSpace_complex` — a connected complex one-manifold is path connected;
* `subsingleton_hom_toReal_of_path` — the challenge hypothesis `Hom(π₁(X,x),ℝ) = 0` is a property of
  the space and not of the base point;
* `subsingleton_mulHom_of_subsingleton_addHom` — the same vanishing in the multiplicative language
  `G →* Multiplicative ℝ`;
* `exists_chartBall_not_mem` — given `u ≠ z₀`, some chart ball around `z₀` misses `u` (the first
  ingredient of the surjectivity input: it selects the simply connected chart ball `W` used by the
  loop-dependent push-off argument, so that `W` misses the base point of the loop);
* `periods_two_pi_zmultiples_of_windingMatching` — **the crux**: the periods of the conjugate
  differential `⋆dE` of a unit-pole Green function are multiples of `2π`, given (i) the *winding
  matching* `P γ = 2π W γ` for loops `γ` that are null-homotopic in `X` and an integer-valued
  homomorphism `W`, and (ii) the surjectivity of `π₁(X∖{z₀}) → π₁(X)`.  Proof: `P − 2πW` kills the
  kernel of `j: π₁(X∖{z₀}) → π₁(X)`, hence descends along the surjection `j` to a homomorphism
  `π₁(X) → ℝ`, which vanishes by the hypothesis; so `P = 2πW` and all periods are multiples of
  `2π`;
* `exists_diffeomorph_plane_or_upperHalfPlane_of_windingMatching` — the target conclusion from the
  same two inputs, via the (sorry-free) modulus chapter `Work.Modulus` and the hyperbolic endgame
  `Work.Parabolic.uniformization_of_greenFunctionAt`.

## SESSION NOTE (the (D3) whisker brick, and the monodromy route)

Two new, *verified* ingredients for this file's closure are recorded in
`Submission/Work/Mori/NOTES_session_attach_arc_and_monodromy.md`:

* `Submission/Work/Mori/attach_arc_at_point.lean` (sorry-free, axiom-clean):
  `Work.Mori.isMulTorsionFree_abelianization_union_attach_arc_at_point` — attaching an arc at one of
  its endpoints preserves torsion-freeness of `H₁` (a strong deformation retraction).  This is the
  "whisker" half of the `(D3)` tile induction;
* `Submission/Work/Mori/attach_arc_retraction.lean` (sorry-free): the retraction collapsing an arc
  attached at *both* endpoints along an arbitrary path of `M`, which makes `i_* : H₁ M → H₁ (M ∪ γ)`
  injective — the first ingredient of the critical `(D3)` brick
  `Work.Mori.isMulTorsionFree_abelianization_union_attach_arc` (the only remaining gap there is the
  *generation* `H₁ (M ∪ γ) = i_* H₁ M + ℤ [ℓ]`).

A third, *analytic* finding: with `E` as in the hypotheses of this file, the periods of `⋆dE` on a
small meridian are exactly `-2π`, so the monodromy of the multivalued `exp (-F)` descends to a
subgroup of `U(1)`, which is finite cyclic, infinite cyclic or dense; the infinite cyclic case
contradicts `H : Subsingleton (π₁(X,x₀) →+ ℝ)`.  Hence the *analytic* obstruction to producing the
holomorphic modulus `Φ` with `‖Φ‖ = exp (-E)` is only the finite case `m ≥ 2` (and `m = 2` really
occurs, e.g. for the symmetric annulus).  So a *strictly weaker* topological input would close this
file: "`π₁ X` has no non-trivial finite cyclic quotient".  (The dense case is open.)

## STATUS (session: the three routes, and which one is now the critical path)

**The target's proof now consumes the DIVISOR THEOREM, not the spine** (see the section
"THE DIVISOR ROUTE (spine-free)" below and `Work.SimplyConnected.…_of_singleSimpleZero`): the only
`sorry` in its axiom closure is `Work.Analysis.RiemannSurface.single_simple_zero_at`, a statement
with *no topological hypothesis on `X`* (Behnke--Stein: a non-compact Riemann surface is Stein, so
the divisor `1·z₀` is principal).  A second, independent spine-free interface is
`Work.SimplyConnected.…_of_integerValuedPeriods` (see "THE WINDING (INTEGER-PERIOD) ROUTE" below),
whose obligation is the existence of the winding homomorphism, i.e. the *primitivity of the meridian
in `H₁ (X ∖ {z₀})`*.

The *topological* (spine / abelian) routes are recorded for reference and remain valuable for the
other consumers of the tree; they are no longer on the critical path of this file:

* the *spine* route (`Work.Spine.simplyConnectedSpace_of_subsingleton_hom_toReal`, still a `sorry`
  upstream) — this is what the target's proof currently consumes, so its axiom closure contains
  `sorryAx`;
* the *abelian* route, which is strictly weaker and is now **spine-free up to one statement**:

  - `Work.Mori.isMulTorsionFree_abelianization_of_exhaustion` (proved, axiom-clean): torsion-freeness
    of `H₁` passes from the members of an exhaustion to the whole space;
  - `Work.Mori.torsionFree_abelianization_planeDomain` (proved, axiom-clean): the planar case
    (`U ⊆ ℂ` open connected has torsion-free `H₁`), obtained from the polyomino exhaustion;
  - `exists_diffeomorph_plane_or_upperHalfPlane_of_abelianization_torsionFree` and
    `exists_diffeomorph_plane_or_upperHalfPlane_of_torsionFreeExhaustion` (proved, axiom-clean):
    the target from the torsion-freeness of `H₁`, resp. from an exhaustion with torsion-free pieces;

  so the target follows from the single remaining statement
  `Work.Mori.exists_torsionFreeExhaustion_of_noncompact_riemannSurface` (reviewed 2/2;
  `Mori/exists_torsionFreeExhaustion_of_noncompact_riemannSurface`), and the switch is the one line

  ```
  exact exists_diffeomorph_plane_or_upperHalfPlane_of_torsionFreeExhaustion hX x₀ hE hexh
  ```

  See `Submission/Work/Mori/NOTES_session_exhaustion_architecture.md` for the plan for that
  statement (tile clusters of `Commons.Topology.Surface.exists_locallyFinite_disk_tiling`), the
  fold/attachment bricks it needs, and the elaboration trap (`FundamentalGroup` is a `@[reducible]`
  alias for `CategoryTheory.End`) that makes `let`-bound group families `H : ℕ → Type*` unusable in
  the colimit statements.

## SESSION NOTE (the `(D3)` route, sharpened)

The piece-level statement `(D3)` ("every finite union of tiles of the disc tiling has torsion-free
`H₁`") *is* reachable by a tile-by-tile induction even though the tile-by-tile *fold* induction of
`Submission/Work/Mori/NOTES_session_fold_induction.md` is blocked: fold each new tile onto a
*caterpillar tree inside the tile* (for `c = 1` the fold is the semicircle fold; in general the disc
is cut along `c - 1` drawn arcs into `c` discs, each retracting onto all but one of its boundary
sides) and then attach the `c - 1` missing edges as 1-cells.  The four pieces this needs, and their
status, are recorded in `Submission/Work/Mori/NOTES_session_D3_via_attach_arc.md`, with the two
reviewed-2/2 statements in compilable form in
`Submission/Work/Mori/REQUESTS_d3_attach_and_tameness.lean`
(`Work.Surface.exists_locallyFinite_disk_tiling_arc_interfaces` = tameness of the global tiling, and
`Work.Mori.isMulTorsionFree_abelianization_union_attach_arc` = the attach-a-1-cell step).

## The exact remaining gap

`Work.SimplyConnected.exists_diffeomorph_plane_or_upperHalfPlane_of_isUnitGreenFunction` is the
above with the two inputs discharged *from the hypotheses*:

* **the winding matching** (the only remaining input) — for a unit-pole Green function `E` at `z₀`
  and every base point `u₀` of `X∖{z₀}`, there is a homomorphism `W : π₁(X∖{z₀},u₀) →+ ℤ` with
  `P γ = 2π·W γ` for every loop `γ` that is null-homotopic in `X`.  Equivalently: the period of the conjugate of `E` around such a
  loop is `2π` times the winding number of `γ` about the pole (a `2πi·Res = −2π` flux computation,
  cf. `Work.Modulus.greenPeriodHom_two_pi_zmultiples`, which gives only the weaker statement
  `P γ ∈ 2πℤ`).  Its formalisation needs the meridian of `z₀` to be *primitive* in
  `H₁(X∖{z₀};ℤ)`, a surface-topology fact which is not in the workspace (the same wall as the
  spine theorem `Work.Spine.exists_homotopyEquiv_oneDimCWComplex_of_noncompact`, in a cheaper
  form: it says nothing about `π₁(X)` beyond its finite quotients);

* **the surjectivity** of `π₁(X∖{z₀}) → π₁(X)` ("a loop can be pushed off a point"), which is
  elementary topology (general position in a chart ball) but not yet in the workspace.
  Note on *how* it has to be proved: a *global* push — a continuous `ρ : X → X∖{z₀}` with
  `ρ u = u` and `ρ` homotopic to the identity rel `u` — is impossible: it would make a meridian
  about `z₀` null-homotopic in `X∖{z₀}`, contradicting `P μ = ±2π`.  Likewise every explicit
  formula (radial or translational push inside a chart ball, with a cutoff so that the boundary is
  fixed) fails: a push of the *point* `z₀` by a map that fixes the boundary of the ball is
  obstructed (no retraction of the disc onto the punctured disc), and any translation whose
  magnitude dominates the distance `‖c z₀ − c(γ s)‖` must be supported on all of the ball while any
  cutoff must vanish near its boundary.  So the push must be **loop-dependent**: decompose
  `γ⁻¹(W)` (an open subset of `I`) into its connected components (open intervals), replace the
  excursion of `γ` on each component by a path inside the *simply connected* chart ball `W` that
  avoids `z₀` (the endpoints of the closure of a component lie outside `W`, hence are `≠ z₀`), and
  glue the homotopies; the case of a component containing `0`/`1` (where `γ` starts inside `W`) is
  handled by choosing `W` not to contain the base point `u`.  Equivalently: `π₁(X)` is generated by
  `π₁(X∖{z₀})` and the trivial group, via the open cover `{W, X∖{z₀}}` (a van Kampen argument;
  Mathlib has no van Kampen, so this must be done by hand).  Ingredient status: the chart ball
  (Lemma `exists_chartBall_not_mem` above) is proved; still to do are "a chart ball inside the chart
  target is simply connected" (transport of `IsSimplyConnected` along the chart homeomorphism to a
  metric ball, together with `isSimplyConnected_ball` from the workspace) and the excursion
  bookkeeping itself (components of `γ⁻¹(W)` are intervals; the punctured chart ball is
  path-connected; glue the finitely/countably many local homotopies with `Path.Homotopic.hcomp`).

Both statements were reviewed and approved as stated.

**The winding matching splits into three independently useful statements** (all formalised, with
the definitions `inclMap`, `toPunctured`, `inclSub` below):

* **(A)** `Work.SimplyConnected.ker_inclMap_eq_normalClosure` — the van Kampen kernel statement:
  for an open simply connected disc `D ∋ z₀` with `D∖{z₀}` path connected and `q ∈ D∖{z₀}`,
  `ker(π₁(X∖{z₀}) → π₁(X)) = normalClosure (image of π₁(D∖{z₀}))`.  *Reviewed and approved*
  (both reviewers; the extra `IsPathConnected (D∖{z₀})` hypothesis was added on their advice, and
  is supplied for chart balls by `exists_chartBall_punctured`).
* **(B)** `Work.SimplyConnected.exists_windingHom_meridian` — the residue computation: the period
  of the conjugate of the unit-pole Green function around the loops of `D∖{z₀}` is `2π` times a
  **surjective** integer-valued homomorphism.  *Reviewed and approved* (the surjectivity is the
  substantive content: it needs the local `2πi·Res = −2π` computation at a unit pole, which the
  existing `greenPeriodHom_two_pi_zmultiples` does not extract).
* **(C)** `Work.SimplyConnected.exists_int_hom_extends_meridian` — pure surface topology: that
  integer-valued homomorphism extends to a `ℤ`-valued homomorphism of `π₁(X∖{z₀})` (equivalently:
  the meridian is primitive in `H₁(X∖{z₀};ℤ)`).  Not yet reviewed; this is the hard half.

`(A) + (B) + (C) ⇒ the winding matching` (agreement on the image of `π₁(D∖{z₀})` plus the normal
closure); the remaining bookkeeping is the pure group-theoretic descent.

**Status.**  The *surjectivity* input is now **proved**:
`Work.SimplyConnected.fundamentalGroup_map_surjective_of_punctured`
(`Submission/Work/SimplyConnected/fundamentalGroup_map_surjective_of_punctured.lean`, with the
van-Kampen-style ingredient `Work.SimplyConnected.exists_path_homotopic_mem_of_open_cover` in
`PushOff.lean`), and it is used by the winding-matching assembly below.  (The *target* theorem no
longer depends on the winding matching: see the "FINDINGS / STATUS" section below — it is now the
two-line reduction to Hubbard Theorem 1.1.2.)

## SESSION UPDATE (this session): the sharp interface

Two new *proved* (axiom-clean) lemmas isolate the exact group-theoretic content, and they show that
the target needs strictly less than Hubbard 1.1.2:

* `Work.SimplyConnected.periods_two_pi_zmultiples_of_subsingleton_hom_addCircle` — **the sharp
  reduction**: if *every* character `π₁(X,y) →+ ℝ/2πℤ` vanishes, then every period of the conjugate
  differential of the unit-pole Green function is a multiple of `2π`.  Together with the (proved)
  `Work.Modulus.greenPeriodHom_two_pi_zmultiples` (periods of loops null-homotopic in `X`) and the
  (proved) surjectivity `Work.SimplyConnected.fundamentalGroup_map_surjective_of_punctured`, this
  descends the period homomorphism to a circle-valued character of `π₁(X)` and kills it.
* `Work.SimplyConnected.subsingleton_addHom_of_torsionFree` — the *abelian half* of Hubbard 1.1.2
  suffices for the circle-valued vanishing: if `π₁(X,x)^{ab} = H₁(X;ℤ)` is **torsion-free** and has
  no non-trivial real character, then it is trivial, so every character into an abelian group
  (in particular into the circle) is trivial.

Hence the target follows from the torsion-freeness of `H₁` alone
(`Work.SimplyConnected.exists_diffeomorph_plane_or_upperHalfPlane_of_torsionFree`) — no freeness of
`π₁(X)` is needed.  Freeness implies torsion-freeness and not conversely, and *freeness is what the
spine subproject `Work.Spine` is about*; the abelian statement is the "limit of free groups need not
be free, but is torsion-free" phenomenon, so it is the cheaper of the two
(`Submission/Work/Mori/torsionFree_abelianization_riemannSurface.lean`, Route 2, and
`Submission/Work/Mori/NOTES_session3_analysis.md` §3; the delegated target
`Work.Mori.noNontrivialHomToCircle` was reviewed 2/2 and is the same statement).

In the *plane* case the abelian half is **provable without the spine**: see
`Submission/Work/Mori/torsionFree_abelianization_planeDomain.lean`, where
`Work.Mori.isFreeGroup_fundamentalGroup_polyK` (a polyomino strongly deformation retracts onto a
one-dimensional CW spine, so its `π₁` is free) and
`Work.Mori.isMulTorsionFree_abelianization_polyK` are proved.  Extending this to a general
(non-planar) Riemann surface is exactly the remaining gap.

## FINDINGS / STATUS (session 9, updated) — read before planning

**UPDATE (this file is now a complete *interface* to the topological chapter).**  Three *direct
consumers*, each `#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorry-free), take the
three shapes of the missing topological input and produce the target:

| consumer below | input |
|---|---|
| `exists_diffeomorph_plane_or_upperHalfPlane_of_hasCutSystemCore` | `Commons.Topology.Surface.HasCutSystemCore X` |
| `exists_diffeomorph_plane_or_upperHalfPlane_of_spineDatum` | `D : Work.Spine.Surface.SpineDatum X` + `X ≃ₕ ↥D.carrier` |
| `exists_diffeomorph_plane_or_upperHalfPlane_of_torsionFreeExhaustion` | exhaustion of `X` by compact sets with torsion-free `H₁` |

So whoever lands *any* one of the three inputs closes this file by one application (no change to the
statement of the target is needed).  See `Submission/Work/Mori/NOTES_interfaces_for_uniformization.md`
for the state of the fleet on those inputs and for the traps of the supporting bricks (windows).

**The lemma is true, it is NOT vacuous, and it is *equivalent* (given the machinery already in this
workspace) to the topological step of Hubbard Theorem 1.1.2:**

* downstream of the period/Green-function input everything is *sorry-free*: the modulus chapter
  `Work.Modulus` and the hyperbolic endgame `Work.Parabolic.uniformization_of_greenFunctionAt`;
  the target below is therefore now written as the *two-line* reduction
  `Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction` (whose topological input `hSpine`
  is exactly `Work.Spine.simplyConnectedSpace_of_subsingleton_hom_toReal`) followed by the endgame;
* the *only* missing input of this file is therefore `Work.Spine` (Johansson/Stallings: `π₁` of a
  connected non-compact surface is free, hence trivial here), which is the central open subproject.
  `Work.Spine.simplyConnectedSpace_of_subsingleton_hom_toReal` is imported and used below, so this
  file becomes axiom-clean automatically as soon as the spine subproject lands.

**Negative findings (do not re-derive; these kill the shortcuts):**

1. *The integrality of the periods is **false** without the hypothesis
   `Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)`*, so it cannot be proved from the Green
   function alone: for `X` the annulus `{1 < |z| < 2}` (or a compact Riemann surface of genus `≥ 1`
   minus a point) the conjugate differential of the Green function has non-integral periods.  Proof
   of the failure for the compact-minus-a-point case: a single-valued `Φ` with `‖Φ‖ = exp (-E)`
   would be bounded and holomorphic on the compact surface minus a point, extend holomorphically
   across the puncture (removable) and have a single simple zero, which is impossible on a compact
   surface.  For the annulus the flux through the two ideal boundary circles sums to `±2π` and is
   not a multiple of `2π` in general.
2. The "winding-matching" route of this file ((A) van Kampen kernel + (B) the residue computation
   `P μ = ±2π` + (C) `∃ W : π₁(X∖{z₀}) →+ ℤ, W μ = ±1`) *is* a valid route to the conclusion (the
   assembly, using the proved surjectivity of input 2 and the hypothesis, is
   `periods_two_pi_zmultiples_of_windingMatching` + `..._of_windingMatching` above, all proved),
   but it is **not a shortcut**: (A) and (B) are provable but (C) is *as hard as the conclusion*
   (with (A)+(B)+the hypothesis it implies the integrality, hence `X ≅ ℂ` or `ℍ`, hence
   `π₁(X) = 1`), and (C) is not a consequence of the hypothesis alone: in the group-theoretic model
   `G = ℤ = π₁(X∖{z₀})`, `μ = aⁿ`, `Q = ℤ/n` one has `Hom(Q,ℝ) = 0` while no `W` with `W(aⁿ) = 1`
   exists.  Geometrically (C) is the statement that *the meridian around a planar end of an
   orientable surface is primitive in `H₁`* — true, but it needs the same surface topology.
3. Since `Hom(A,ℝ) = 0 ⟺ A` is a torsion group for abelian `A` (choice), the hypothesis is
   equivalent to "`π₁(X)^{ab}` is a torsion group"; for a *free* group this forces triviality, which
   is precisely how `Work.Spine` uses it.  For non-free groups it does not (e.g. the infinite
   dihedral group, or any torsion-free perfect group), which is why freeness (or an equivalent
   surface-theoretic input) is unavoidable.
4. The *unit* normalisation of the pole is essential for the route of item 2 (a pole of order `n`
   gives periods in `2πnℤ`), and it is exactly what `Work.UnitGreen.IsUnitGreenFunctionAt` records.

**Proved in this file (axiom-clean, independent of `Work.Spine`):**
`pathConnectedSpace_of_chartedSpace_complex`, `subsingleton_hom_toReal_of_path`,
`subsingleton_mulHom_of_subsingleton_addHom`, `exists_chartBall_not_mem`,
`periods_two_pi_zmultiples_of_windingMatching` (the crux of the winding-matching descent) and
`exists_diffeomorph_plane_or_upperHalfPlane_of_windingMatching` (the full assembly from the two
inputs (wind. matching, surjectivity)).


## Session 22 (routes)

`Submission/Work/Mori/NOTES_session22_routes_and_boundary.md` records the structural finding that
decides between the two spine-free routes of this file: the compact-bordered crux is *currently*
routed (by `Submission/Work/Spine/CompactBordered/interior_of_compact_bordered_surface.lean`) through
the **non-compact spine theorem** — the same `sorry` that the direct spine route of this file needs —
so the *only* root-free route to this lemma is the **abelian route through the disc tiling**:

`target ⟸ IsMulTorsionFree (H₁ X) ⟸ the exhaustion from
Commons.Topology.Surface.exists_locallyFinite_disk_tiling ⟸ (D3)`,

where (D3) ("every finite union of tiles has torsion-free `H₁`") is the single remaining input and all
of its engines (fold transfer, disc and annulus model folds) are proved.  (D3) still needs the
tameness of the tiling, a homeomorphism of a *ring* of tiles with a standard annulus, and the peeling
induction.  That note also records the state of the bordered structure on the superlevel pieces
(`Submission/Work/Mori/boundaryChartInstance.lean`: the straightening with a globally continuous `g`
is landed; the boundary chart is designed and parked).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Work.SimplyConnected

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

def inclMap (z₀ : X) (u₀ : Work.Modulus.puncturedOpens z₀) :
    FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀ →* FundamentalGroup X u₀.1 :=
  FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ u₀

theorem pathConnectedSpace_of_chartedSpace_complex : PathConnectedSpace X := by
  have h : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace (H := ℂ) (M := X)
  exact PathConnectedSpace.of_locallyPathConnectedSpace

theorem subsingleton_hom_toReal_of_path {x y : X} (γ : Path x y)
    (h : Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)) :
    Subsingleton (Additive (FundamentalGroup X y) →+ ℝ) := by
  have e : Additive (FundamentalGroup X x) ≃+ Additive (FundamentalGroup X y) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toAdditive
  refine ⟨fun f g => ?_⟩
  have h' : f.comp e.toAddMonoidHom = g.comp e.toAddMonoidHom := Subsingleton.elim _ _
  refine AddMonoidHom.ext (fun y' => ?_)
  obtain ⟨x', rfl⟩ := e.surjective y'
  exact congrFun (congrArg DFunLike.coe h') x'

/-- A point of a set `D ∖ {z₀}` viewed as a point of the punctured surface `X ∖ {z₀}`. -/
def toPunctured (z₀ : X) (q : X) (h : q ∉ ({z₀} : Set X)) : ↥(Work.Modulus.puncturedOpens z₀) :=
  ⟨q, h⟩

/-- The inclusion map `D ∖ {z₀} ↪ X ∖ {z₀}`, as a continuous map (used to state the van Kampen
kernel statement for the cover `{X∖{z₀}, D}`). -/
def inclSub (z₀ : X) (D : Set X) : C(↥(D \ {z₀}), ↥(Work.Modulus.puncturedOpens z₀)) :=
  ⟨fun x => toPunctured z₀ x.1 (by simpa using x.2.2), by
    apply Continuous.subtype_mk
    exact continuous_subtype_val⟩

/-- **First ingredient of the surjectivity input.**  Given `u ≠ z₀`, some chart ball around `z₀`
misses `u`.  This is what lets the loop-dependent argument choose the simply connected chart ball
`W` so that it does not contain the base point of the loop (so that the homotopy can keep the base
point fixed). -/
theorem exists_chartBall_not_mem {z₀ u : X} (h : u ≠ z₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ u ∉ Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ := by
  by_contra hcon
  push_neg at hcon
  have hmem1 : u ∈ Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) 1 := hcon 1 one_pos
  have hsrc : u ∈ (chartAt ℂ z₀).source := (Submission.mem_chartBall.mp hmem1).1
  have hc : (chartAt ℂ z₀) u = (chartAt ℂ z₀) z₀ := by
    by_contra hne
    have hpos : 0 < dist ((chartAt ℂ z₀) u) ((chartAt ℂ z₀) z₀) := dist_pos.mpr hne
    have hlt := (Submission.mem_chartBall.mp
      (hcon (dist ((chartAt ℂ z₀) u) ((chartAt ℂ z₀) z₀)) hpos)).2
    rw [Metric.mem_ball] at hlt
    exact absurd hlt (lt_irrefl _)
  exact h ((chartAt ℂ z₀).injOn hsrc (mem_chart_source ℂ z₀) hc)

theorem subsingleton_mulHom_of_subsingleton_addHom (G : Type*) [Group G]
    (h : Subsingleton (Additive G →+ ℝ)) : Subsingleton (G →* Multiplicative ℝ) := by
  refine ⟨fun f g => ?_⟩
  have lift : ∀ u : G →* Multiplicative ℝ, ∃ φ : Additive G →+ ℝ,
      ∀ x : G, φ (Additive.ofMul x) = Multiplicative.toAdd (u x) := by
    intro u
    let φ : Additive G →+ ℝ :=
      { toFun := fun a => Multiplicative.toAdd (u (Additive.toMul a))
        map_zero' := by simp
        map_add' := fun a b => by
          show Multiplicative.toAdd (u (Additive.toMul (a + b)))
              = Multiplicative.toAdd (u (Additive.toMul a))
                + Multiplicative.toAdd (u (Additive.toMul b))
          rw [show Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b from rfl, map_mul]
          rfl }
    exact ⟨φ, fun x => rfl⟩
  obtain ⟨φ, hφ⟩ := lift f
  obtain ⟨ψ, hψ⟩ := lift g
  have hfg : φ = ψ := Subsingleton.elim _ _
  refine MonoidHom.ext (fun x => ?_)
  exact Multiplicative.toAdd.injective (by rw [← hφ x, ← hψ x, hfg])

theorem periods_two_pi_zmultiples_of_windingMatching {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hmatch : ∀ u₀ : Work.Modulus.puncturedOpens z₀,
      ∃ W : Additive (FundamentalGroup ↥(Work.Modulus.puncturedOpens z₀) u₀) →+ ℤ,
        ∀ γ : FundamentalGroup ↥(Work.Modulus.puncturedOpens z₀) u₀, inclMap z₀ u₀ γ = 1 →
          Work.Modulus.greenPeriodHom hE u₀ (Additive.ofMul γ)
            = (W (Additive.ofMul γ) : ℝ) * (2 * Real.pi))
    (hsurj : ∀ u₀ : Work.Modulus.puncturedOpens z₀, Function.Surjective (inclMap z₀ u₀))
    (hsub : ∀ y : X, Subsingleton (Additive (FundamentalGroup X y) →+ ℝ))
    (u₀ : Work.Modulus.puncturedOpens z₀)
    (γ : FundamentalGroup ↥(Work.Modulus.puncturedOpens z₀) u₀) :
    ∃ k : ℤ, Work.Modulus.greenPeriodHom hE u₀ (Additive.ofMul γ) = k * (2 * Real.pi) := by
  classical
  obtain ⟨W, hW⟩ := hmatch u₀
  let φ : FundamentalGroup ↥(Work.Modulus.puncturedOpens z₀) u₀ →* Multiplicative ℝ :=
    { toFun := fun a => Multiplicative.ofAdd (Work.Modulus.greenPeriodHom hE u₀ (Additive.ofMul a)
        - (W (Additive.ofMul a) : ℝ) * (2 * Real.pi))
      map_one' := by
        rw [show Additive.ofMul (1 : FundamentalGroup ↥(Work.Modulus.puncturedOpens z₀) u₀) = 0
          from rfl, map_zero, map_zero W, Int.cast_zero, zero_mul, sub_zero]
        rfl
      map_mul' := fun a b => by
        rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from rfl,
          map_add, map_add W, Int.cast_add]
        have harg : (Work.Modulus.greenPeriodHom hE u₀) (Additive.ofMul a)
              + (Work.Modulus.greenPeriodHom hE u₀) (Additive.ofMul b)
              - ((W (Additive.ofMul a) : ℝ) + (W (Additive.ofMul b) : ℝ)) * (2 * Real.pi)
            = ((Work.Modulus.greenPeriodHom hE u₀) (Additive.ofMul a)
                - (W (Additive.ofMul a) : ℝ) * (2 * Real.pi))
              + ((Work.Modulus.greenPeriodHom hE u₀) (Additive.ofMul b)
                - (W (Additive.ofMul b) : ℝ) * (2 * Real.pi)) := by ring
        rw [harg]
        rfl }
  have hker : (inclMap z₀ u₀).ker ≤ φ.ker := by
    intro a ha
    have h1 : inclMap z₀ u₀ a = 1 := ha
    show φ a = 1
    show Multiplicative.ofAdd (Work.Modulus.greenPeriodHom hE u₀ (Additive.ofMul a)
      - (W (Additive.ofMul a) : ℝ) * (2 * Real.pi)) = 1
    rw [hW a h1, sub_self]
    rfl
  let f_inv : FundamentalGroup X u₀.1 → FundamentalGroup ↥(Work.Modulus.puncturedOpens z₀) u₀ :=
    fun h => Classical.choose (hsurj u₀ h)
  have hf : Function.RightInverse f_inv (inclMap z₀ u₀) :=
    fun h => Classical.choose_spec (hsurj u₀ h)
  haveI : Subsingleton (FundamentalGroup X u₀.1 →* Multiplicative ℝ) :=
    subsingleton_mulHom_of_subsingleton_addHom _ (hsub u₀.1)
  let Ψ : FundamentalGroup X u₀.1 →* Multiplicative ℝ :=
    (MonoidHom.liftOfRightInverse (inclMap z₀ u₀) f_inv hf) ⟨φ, hker⟩
  have hΨ : Ψ = 1 := Subsingleton.elim _ _
  have hφ : φ = 1 := by
    refine MonoidHom.ext (fun a => ?_)
    have hcomp := MonoidHom.liftOfRightInverse_comp_apply (inclMap z₀ u₀) f_inv hf ⟨φ, hker⟩ a
    show φ a = 1
    rw [← hcomp]
    show (((inclMap z₀ u₀).liftOfRightInverse f_inv hf) ⟨φ, hker⟩) ((inclMap z₀ u₀) a) = 1
    rw [show (((inclMap z₀ u₀).liftOfRightInverse f_inv hf) ⟨φ, hker⟩) = Ψ from rfl, hΨ]
    rfl
  refine ⟨W (Additive.ofMul γ), ?_⟩
  have h1 : φ γ = 1 := by
    have := congrFun (congrArg DFunLike.coe hφ) γ
    simpa using this
  have h2 : Multiplicative.toAdd (φ γ) = 0 := by rw [h1]; rfl
  have h3 : (Work.Modulus.greenPeriodHom hE u₀) (Additive.ofMul γ)
      - (W (Additive.ofMul γ) : ℝ) * (2 * Real.pi) = 0 := by
    simpa [φ] using h2
  rwa [sub_eq_zero] at h3

/-- **The uniformization conclusion from the winding matching and the surjectivity.**  This is the
assembly: the matching identifies the periods of the conjugate with `2π` times an integer-valued
winding homomorphism on the loops that are null-homotopic in `X`; the surjectivity of
`π₁(X∖{z₀}) → π₁(X)` turns that into the statement that *all* periods of the conjugate
differential are multiples of `2π`; the existing (sorry-free) modulus chapter then produces the
holomorphic modulus of `E` and the hyperbolic endgame concludes. -/
theorem exists_diffeomorph_plane_or_upperHalfPlane_of_windingMatching
    (hX : ¬ CompactSpace X) {x₀ : X} [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hmatch : ∀ u₀ : Work.Modulus.puncturedOpens z₀,
      ∃ W : Additive (FundamentalGroup ↥(Work.Modulus.puncturedOpens z₀) u₀) →+ ℤ,
        ∀ γ : FundamentalGroup ↥(Work.Modulus.puncturedOpens z₀) u₀, inclMap z₀ u₀ γ = 1 →
          Work.Modulus.greenPeriodHom hE u₀ (Additive.ofMul γ)
            = (W (Additive.ofMul γ) : ℝ) * (2 * Real.pi))
    (hsurj : ∀ u₀ : Work.Modulus.puncturedOpens z₀, Function.Surjective (inclMap z₀ u₀)) :
    Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X ℂ
        ((⊤ : ℕ∞) : WithTop ℕ∞)) ∨
      Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X UpperHalfPlane
        ((⊤ : ℕ∞) : WithTop ℕ∞)) := by
  haveI : PathConnectedSpace X := pathConnectedSpace_of_chartedSpace_complex
  have hsub : ∀ y : X, Subsingleton (Additive (FundamentalGroup X y) →+ ℝ) := fun y =>
    subsingleton_hom_toReal_of_path (PathConnectedSpace.somePath x₀ y) (inferInstance)
  obtain ⟨Φ, hhol, hne, hmod⟩ := Work.Modulus.hasTrivialModulusMonodromy_of_periods hE
    (fun u₀ γ => periods_two_pi_zmultiples_of_windingMatching hE hmatch hsurj hsub u₀ γ)
  have hpole : Submission.HasLogPoleAt z₀ Φ :=
    Work.Modulus.poleOrderModulus_of_unitGreen hE hhol hne hmod
  exact Work.Parabolic.uniformization_of_greenFunctionAt hX hE.1 hhol hmod hpole


/-! ## THE DIVISOR ROUTE (spine-free): the target from the Weierstrass/Cousin divisor theorem

Everything above reduces the target to surface topology (freeness of `π₁`, or torsion-freeness of
`H₁`).  There is a second, **spine-free** reduction, recorded here: the classical *divisor theorem*
of Behnke--Stein (`Work.Analysis.RiemannSurface.single_simple_zero_at`: every connected non-compact
Riemann surface carries a holomorphic function whose zero set is exactly one prescribed point,
simply) — a theorem that is **unconditional** in the topology of `X` — together with the challenge
hypothesis `H¹(X,ℝ) = 0` produces the holomorphic modulus of the Green function outright.

The mathematics (all of it machine-checked by the two ingredients consumed below):

* Let `g` have a simple zero exactly at `z₀`.  Then `log ‖g‖ + E` is harmonic on `X ∖ {z₀}` — the
  logarithmic pole of `E` is *exactly cancelled* by the simple zero of `g` — and bounded near `z₀`,
  so it extends to a harmonic function `K` on all of `X`
  (`Work.Potential.removable_singularity_of_bounded_near`);
* the hypothesis says that the conjugate period homomorphism `π₁(X,x₀) → ℝ` vanishes, so `K` is the
  real part of a global holomorphic function `F`
  (`Work.SimplyConnected.ABS.exists_holomorphic_conjugate_of_subsingleton`);
* hence `Φ := g · exp (-F)` is holomorphic on `X`, has a simple zero at `z₀`, and
  `‖Φ x‖ = ‖g x‖ · exp (-K x) = exp (-E x)` off `z₀` (`‖g‖` cancels against the `log ‖g‖` in `K`);

then the hyperbolic endgame `Work.Parabolic.uniformization_of_greenFunctionAt` concludes.  The whole
chain is `Work.SimplyConnected.ABS.exists_modulus_of_singleSimpleZero`, which is sorry-free and
axiom-clean.

**Also the challenge target itself can be made spine-free**: see
`Submission/Work/SimplyConnected/uniformization_via_divisor.lean`
(`Submission.uniformization_via_divisor`), which assembles `Submission.uniformization`'s statement
from the *same* divisor theorem plus the parabolic gap `Submission.plane_of_no_greenFunction`; the
split is "`X` carries a Green function ? divisor route : Mori", and the spine is not used at all.

**Status.**  `Work.Analysis.RiemannSurface.single_simple_zero_at` is a `sorry` at the time of
writing: its proof is being built in `Submission/Work/Analysis/RiemannSurface/` (the
Behnke--Stein/Runge/`∂̄` chapter), where it is reduced to the single approximation-theoretic input
`Work.Analysis.RiemannSurface.MeromorphicRunge`.  Unlike the spine statement, this input makes **no
topological assumption** on `X`, so it is *strictly* the easier obligation.
-/

/-- **A unit-pole Green function satisfies the ABS unit-log-pole predicate** (`HasLogPoleOn` is
`IsUnitGreenFunctionAt.2` with the harmonicity domain passed as an extra parameter). -/
theorem hasLogPoleOn_of_isUnitGreenFunctionAt {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E) :
    Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E := by
  obtain ⟨C, V, hV, hb⟩ := hE.2
  exact ⟨C, V, hV, fun x hx _ hxne => hb x hx hxne⟩

/-- **The target from the divisor theorem, as an explicit hypothesis.**  `hdiv` is
`Work.Analysis.RiemannSurface.single_simple_zero_at` (the Weierstrass/Cousin theorem of
Behnke--Stein for a single point), which is *unconditional* in the topology of `X`.  This statement
is axiom-clean; the target below instantiates `hdiv`. -/
theorem exists_diffeomorph_plane_or_upperHalfPlane_of_singleSimpleZero {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x₀ : X) [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hdiv : ∀ z : X, ¬ CompactSpace X → ∃ g : X → ℂ,
      Submission.HolomorphicOnX g Set.univ ∧ (∀ w : X, w ≠ z → g w ≠ 0) ∧
        Submission.HasLogPoleAt z g) :
    Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X ℂ
        ((⊤ : ℕ∞) : WithTop ℕ∞)) ∨
      Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X UpperHalfPlane
        ((⊤ : ℕ∞) : WithTop ℕ∞)) := by
  haveI : PathConnectedSpace X := pathConnectedSpace_of_chartedSpace_complex
  haveI : Subsingleton (Additive (FundamentalGroup X z₀) →+ ℝ) :=
    subsingleton_hom_toReal_of_path (PathConnectedSpace.somePath x₀ z₀) inferInstance
  obtain ⟨g, hghol, hgne, hgsimple⟩ := hdiv z₀ hX
  obtain ⟨Φ, hΦhol, -, hΦmod, hΦpole⟩ :=
    Work.SimplyConnected.ABS.exists_modulus_of_singleSimpleZero (x₀ := z₀)
      hE.1.harmonic (hasLogPoleOn_of_isUnitGreenFunctionAt hE) hghol hgne hgsimple
  exact Work.Parabolic.uniformization_of_greenFunctionAt hX hE.1 hΦhol hΦmod hΦpole


/-! ## THE WINDING (INTEGER-PERIOD) ROUTE: the target from an integer-valued period homomorphism

The second spine-free interface: `Work.SimplyConnected.ABS.unitGreen_modulus_of_integerValuedPeriods`
(proved, axiom-clean) produces the holomorphic modulus of `E` as soon as the period homomorphism
`Work.Modulus.greenPeriodHom hE u` is `2π` times an *integer-valued* homomorphism, at every base
point `u` of the punctured surface `X ∖ {z₀}`.  The remaining obligation of that route is the
existence of that integer-valued homomorphism (the "winding"/linking homomorphism about `z₀`),
isolated in `Work.SimplyConnected.ABS.exists_integerValued_greenPeriodHom`; the mathematical content
is the *primitivity of the meridian in `H₁ (X ∖ {z₀})`* (an embedded two-sided circle in an
orientable surface), together with the local `2π i Res = −2π` matching on loops that are
null-homotopic in `X`.

The consumer below is the exact interface between that obligation and the challenge conclusion, and
is axiom-clean: it uses no topological hypothesis on `X` beyond `hW`. -/

/-- **The target from an integer-valued period homomorphism of the Green function.** -/
theorem exists_diffeomorph_plane_or_upperHalfPlane_of_integerValuedPeriods {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) {z₀ : X} {E : X → ℝ}
    (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hW : ∀ u : Work.Modulus.puncturedOpens z₀,
      ∃ W : Additive (FundamentalGroup (Work.Modulus.puncturedOpens z₀) u) →+ ℤ,
        ∀ γ : Additive (FundamentalGroup (Work.Modulus.puncturedOpens z₀) u),
          Work.Modulus.greenPeriodHom hE u γ = (W γ : ℝ) * (2 * Real.pi)) :
    Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X ℂ
        ((⊤ : ℕ∞) : WithTop ℕ∞)) ∨
      Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X UpperHalfPlane
        ((⊤ : ℕ∞) : WithTop ℕ∞)) := by
  obtain ⟨Φ, hhol, hpole, hmod⟩ :=
    Work.SimplyConnected.ABS.unitGreen_modulus_of_integerValuedPeriods (x₀ := z₀) hE hW
  exact Work.Parabolic.uniformization_of_greenFunctionAt hX hE.1 hhol hmod hpole


/-- **The target from the named input of the divisor chapter** (`MeromorphicRunge`, the Behnke--Stein
meromorphic Runge approximation statement of `Submission/Work/Analysis/RiemannSurface/`).  This is
the same reduction as `…_of_singleSimpleZero`, but it consumes the *named* obligation directly
(via `Work.Analysis.RiemannSurface.exists_singleZero_of_meromorphicRunge`, which is sorry-free), so
that the target closes as soon as that input lands, without waiting for the wrapper
`Work.Analysis.RiemannSurface.single_simple_zero_at`. -/
theorem exists_diffeomorph_plane_or_upperHalfPlane_of_meromorphicRunge {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x₀ : X) [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (h : Work.Analysis.RiemannSurface.MeromorphicRunge (X := X) z₀) :
    Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X ℂ
        ((⊤ : ℕ∞) : WithTop ℕ∞)) ∨
      Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X UpperHalfPlane
        ((⊤ : ℕ∞) : WithTop ℕ∞)) := by
  obtain ⟨g, hghol, hgne, hgsimple⟩ :=
    Work.Analysis.RiemannSurface.exists_singleZero_of_meromorphicRunge z₀ hX h
  haveI : PathConnectedSpace X := pathConnectedSpace_of_chartedSpace_complex
  haveI : Subsingleton (Additive (FundamentalGroup X z₀) →+ ℝ) :=
    subsingleton_hom_toReal_of_path (PathConnectedSpace.somePath x₀ z₀) inferInstance
  obtain ⟨Φ, hΦhol, -, hΦmod, hΦpole⟩ :=
    Work.SimplyConnected.ABS.exists_modulus_of_singleSimpleZero (x₀ := z₀)
      hE.1.harmonic (hasLogPoleOn_of_isUnitGreenFunctionAt hE) hghol hgne hgsimple
  exact Work.Parabolic.uniformization_of_greenFunctionAt hX hE.1 hΦhol hΦmod hΦpole


/-- **The target lemma.**  It is exactly the two-line reduction to Hubbard Theorem 1.1.2 recorded
in the module docstring: the (sorry-free) modulus chapter of the Green function followed by the
hyperbolic endgame, with its topological input
`Work.Spine.simplyConnectedSpace_of_subsingleton_hom_toReal` supplied by the `Work.Spine`
subproject. -/
theorem exists_diffeomorph_plane_or_upperHalfPlane_of_hubbard112 {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x₀ : X) [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hSpine : (¬ CompactSpace X) → (x : X) →
      Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) → SimplyConnectedSpace X) :
    Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X ℂ
        ((⊤ : ℕ∞) : WithTop ℕ∞)) ∨
      Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X UpperHalfPlane
        ((⊤ : ℕ∞) : WithTop ℕ∞)) := by
  obtain ⟨Φ, hhol, hpole, hmod⟩ :=
    Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction (z₀ := z₀) (x₀ := x₀) hE hSpine
  exact Work.Parabolic.uniformization_of_greenFunctionAt hX hE.1 hhol hmod hpole


/-- **Base-point independence of the vanishing of `A`-valued characters.**

If every additive character `π₁(X,x) →+ A` vanishes (for `A` an additive commutative group), then
the same holds at every other base point: conjugation along a path identifies the two fundamental
groups and the corresponding character groups. -/
theorem subsingleton_hom_of_path {A : Type*} [AddCommGroup A] {x y : X} (γ : Path x y)
    (h : Subsingleton (Additive (FundamentalGroup X x) →+ A)) :
    Subsingleton (Additive (FundamentalGroup X y) →+ A) := by
  have e : Additive (FundamentalGroup X x) ≃+ Additive (FundamentalGroup X y) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toAdditive
  refine ⟨fun f g => ?_⟩
  have h' : f.comp e.toAddMonoidHom = g.comp e.toAddMonoidHom := Subsingleton.elim _ _
  refine AddMonoidHom.ext (fun y' => ?_)
  obtain ⟨x', rfl⟩ := e.surjective y'
  exact congrFun (congrArg DFunLike.coe h') x'

/-- **The periods of the conjugate differential are multiples of `2π` from the vanishing of the
circle-valued characters.**

Let `E` be a unit-pole Green function at `z₀` on `X`, `U = X ∖ {z₀}` the punctured surface and
`P : π₁(U,u₀) →+ ℝ` the period homomorphism of the conjugate of `E`.  Assume

* `hsub : ∀ y, Subsingleton (π₁(X,y) →+ ℝ/2πℤ)`

(the *circle-valued* form of the challenge hypothesis).  Then `P γ ∈ 2πℤ` for **every**
`γ ∈ π₁(U,u₀)`.

This is the sharp interface between the analysis of the modulus and the topology of `X`, and it is
strictly weaker than the spine (Hubbard 1.1.2): the only surface-theoretic input it needs is that
`H₁` of an open orientable surface is torsion-free.  Proof: the periods of the loops that are
null-homotopic *in* `X` are already known to be multiples of `2π`
(`Work.Modulus.greenPeriodHom_two_pi_zmultiples`), so `P` descends along the surjection
`π₁(U,u₀) → π₁(X,u₀)` (`Work.SimplyConnected.fundamentalGroup_map_surjective_of_punctured`) to a
circle-valued character of `π₁(X,u₀)`, which vanishes by `hsub`; hence `P` itself takes values in
`2πℤ`. -/
theorem periods_two_pi_zmultiples_of_subsingleton_hom_addCircle
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hsub : ∀ y : X, Subsingleton (Additive (FundamentalGroup X y) →+
      (ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi))))
    (u₀ : Work.Modulus.puncturedOpens z₀)
    (γ : FundamentalGroup ↥(Work.Modulus.puncturedOpens z₀) u₀) :
    ∃ k : ℤ, Work.Modulus.greenPeriodHom hE u₀ (Additive.ofMul γ) = k * (2 * Real.pi) := by
  classical
  let Q := ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi)
  let q : ℝ →+ Q := QuotientAddGroup.mk' (AddSubgroup.zmultiples (2 * Real.pi))
  let φ : Additive (FundamentalGroup ↥(Work.Modulus.puncturedOpens z₀) u₀) →+ Q :=
    { toFun := fun a => q (Work.Modulus.greenPeriodHom hE u₀ a)
      map_zero' := by simp
      map_add' := fun a b => by simp [map_add] }
  have hker : (inclMap z₀ u₀).toAdditive.ker ≤ φ.ker := by
    intro a ha
    have ha' : inclMap z₀ u₀ (Additive.toMul a) = 1 := by
      have h1 := congrArg Additive.toMul ha
      simpa using h1
    obtain ⟨k, hk⟩ := Work.Modulus.greenPeriodHom_two_pi_zmultiples (z₀ := z₀) hE u₀
      (Additive.toMul a) ha'
    show φ a = 0
    show q (Work.Modulus.greenPeriodHom hE u₀ (Additive.ofMul (Additive.toMul a))) = 0
    rw [hk]
    have hmem : (↑k * (2 * Real.pi) : ℝ) ∈ AddSubgroup.zmultiples (2 * Real.pi) := by
      rw [show (↑k * (2 * Real.pi) : ℝ) = k • (2 * Real.pi) by rw [zsmul_eq_mul]]
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, rfl⟩
    exact QuotientAddGroup.eq_zero_iff _ |>.mpr hmem
  have hsurj : Function.Surjective (inclMap z₀ u₀) :=
    fundamentalGroup_map_surjective_of_punctured u₀
  let f_inv : FundamentalGroup X u₀.1 → FundamentalGroup ↥(Work.Modulus.puncturedOpens z₀) u₀ :=
    fun h => Classical.choose (hsurj h)
  have hf : Function.RightInverse f_inv (inclMap z₀ u₀) :=
    fun h => Classical.choose_spec (hsurj h)
  have hfA : Function.RightInverse (fun h => Additive.ofMul (f_inv (Additive.toMul h)))
      (inclMap z₀ u₀).toAdditive := by
    intro a
    show Additive.ofMul (inclMap z₀ u₀ (f_inv (Additive.toMul a))) = a
    rw [hf (Additive.toMul a)]
    rfl
  set Ψ : Additive (FundamentalGroup X u₀.1) →+ Q :=
    (AddMonoidHom.liftOfRightInverse (inclMap z₀ u₀).toAdditive
      (fun h => Additive.ofMul (f_inv (Additive.toMul h))) hfA) ⟨φ, hker⟩ with hΨdef
  have hΨ : Ψ = 0 := Subsingleton.elim _ _
  have hφ0 : φ = 0 := by
    refine AddMonoidHom.ext (fun a => ?_)
    have hcomp := AddMonoidHom.liftOfRightInverse_comp_apply (inclMap z₀ u₀).toAdditive
      (fun h => Additive.ofMul (f_inv (Additive.toMul h))) hfA ⟨φ, hker⟩ a
    show φ a = 0
    rw [← hcomp, ← hΨdef, hΨ]
    rfl
  have h1 : φ (Additive.ofMul γ) = 0 := by rw [hφ0]; rfl
  have h2 : q (Work.Modulus.greenPeriodHom hE u₀ (Additive.ofMul γ)) = 0 := h1
  rw [show (0 : Q) = q 0 by simp] at h2
  have h3 : Work.Modulus.greenPeriodHom hE u₀ (Additive.ofMul γ)
      ∈ AddSubgroup.zmultiples (2 * Real.pi) := QuotientAddGroup.eq_zero_iff _ |>.mp h2
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h3
  exact ⟨k, by rw [← hk, zsmul_eq_mul]⟩

/-- **The uniformization conclusion from the circle-valued form of the hypothesis.**

This is the assembly of the two-step reduction that avoids Hubbard 1.1.2: if every character
`π₁(X,y) →+ ℝ/2πℤ` vanishes, then the modulus of the unit-pole Green function is single-valued, and
the hyperbolic endgame concludes. -/
theorem exists_diffeomorph_plane_or_upperHalfPlane_of_subsingleton_hom_addCircle {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x₀ : X)
    (hsub : ∀ y : X, Subsingleton (Additive (FundamentalGroup X y) →+
      (ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi))))
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E) :
    Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X ℂ
        ((⊤ : ℕ∞) : WithTop ℕ∞)) ∨
      Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X UpperHalfPlane
        ((⊤ : ℕ∞) : WithTop ℕ∞)) := by
  haveI : PathConnectedSpace X := pathConnectedSpace_of_chartedSpace_complex
  obtain ⟨Φ, hhol, hne, hmod⟩ := Work.Modulus.hasTrivialModulusMonodromy_of_periods hE
    (fun u₀ γ => periods_two_pi_zmultiples_of_subsingleton_hom_addCircle hE hsub u₀ γ)
  have hpole : Submission.HasLogPoleAt z₀ Φ :=
    Work.Modulus.poleOrderModulus_of_unitGreen hE hhol hne hmod
  exact Work.Parabolic.uniformization_of_greenFunctionAt hX hE.1 hhol hmod hpole


/-- **The additive and multiplicative formulations of the vanishing of the real characters agree.** -/
theorem subsingleton_addHom_iff_mulHom (H : Type*) [Group H] :
    Subsingleton (Additive H →+ ℝ) ↔ Subsingleton (H →* Multiplicative ℝ) := by
  constructor
  · intro h
    exact subsingleton_mulHom_of_subsingleton_addHom H h
  · intro h
    refine ⟨fun f g => ?_⟩
    have key : ∀ φ : Additive H →+ ℝ, ∃ ψ : H →* Multiplicative ℝ,
        ∀ x, ψ x = Multiplicative.ofAdd (φ (Additive.ofMul x)) := fun φ =>
      ⟨{ toFun := fun x => Multiplicative.ofAdd (φ (Additive.ofMul x))
         map_one' := by simp
         map_mul' := fun x y => by
           show Multiplicative.ofAdd (φ (Additive.ofMul (x * y))) =
             Multiplicative.ofAdd (φ (Additive.ofMul x)) * Multiplicative.ofAdd (φ (Additive.ofMul y))
           rw [show Additive.ofMul (x * y) = Additive.ofMul x + Additive.ofMul y from rfl,
             map_add]
           rfl }, fun _ => rfl⟩
    obtain ⟨ψf, hf⟩ := key f
    obtain ⟨ψg, hg⟩ := key g
    have hψ : ψf = ψg := Subsingleton.elim _ _
    refine AddMonoidHom.ext (fun a => ?_)
    have h1 := congrFun (congrArg DFunLike.coe hψ) (Additive.toMul a)
    rw [hf, hg] at h1
    exact Multiplicative.ofAdd.injective h1

/-- **A torsion-free abelianisation with no real characters kills every character into an abelian
group.**  This is the group-theoretic step that turns the *abelian half* of Hubbard's Theorem 1.1.2
(torsion-freeness of `H₁(X;ℤ) = π₁(X)^{ab}`) into the vanishing of the *circle-valued* characters of
`π₁(X)`, which is the form in which the modulus chapter consumes the topology of `X`. -/
theorem subsingleton_addHom_of_torsionFree {G : Type*} [Group G] {Q : Type*} [AddCommGroup Q]
    (hsub : Subsingleton (Additive G →+ ℝ))
    (htf : IsMulTorsionFree (Abelianization G)) :
    Subsingleton (Additive G →+ Q) := by
  -- the abelianisation has no non-trivial real character either
  have hAGmul : Subsingleton (Abelianization G →* Multiplicative ℝ) :=
    (Equiv.subsingleton_congr Abelianization.lift).mp ((subsingleton_addHom_iff_mulHom G).mp hsub)
  have hAGadd : Subsingleton (Additive (Abelianization G) →+ ℝ) :=
    (subsingleton_addHom_iff_mulHom (Abelianization G)).mpr hAGmul
  -- so the abelianisation is trivial, by torsion-freeness
  have hA : Subsingleton (Abelianization G) :=
    Work.Mori.subsingleton_of_subsingleton_hom_real (A := Additive (Abelianization G))
      (fun a n hn ha => by
        have h1 : (Additive.toMul a) ^ n = 1 := by
          have h := congrArg Additive.toMul ha
          simpa using h
        have h2 : (Additive.toMul a) ^ n = (1 : Abelianization G) ^ n := by rw [one_pow, h1]
        exact Additive.toMul.injective
          (IsMulTorsionFree.pow_left_injective (M := Abelianization G) hn h2)) hAGadd
  -- hence every character into an abelian group is trivial
  refine ⟨fun f g => ?_⟩
  have key : ∀ φ : Additive G →+ Q, φ = 0 := by
    intro φ
    let F : G →* Multiplicative Q :=
      { toFun := fun x => Multiplicative.ofAdd (φ (Additive.ofMul x))
        map_one' := by simp
        map_mul' := fun x y => by
          show Multiplicative.ofAdd (φ (Additive.ofMul (x * y))) =
            Multiplicative.ofAdd (φ (Additive.ofMul x))
              * Multiplicative.ofAdd (φ (Additive.ofMul y))
          rw [show Additive.ofMul (x * y) = Additive.ofMul x + Additive.ofMul y from rfl,
            map_add]
          rfl }
    have hF : F = 1 := by
      have h1 : Abelianization.lift F = 1 := Subsingleton.elim _ _
      ext x
      have h2 := congrFun (congrArg DFunLike.coe h1) (Abelianization.of x)
      rw [Abelianization.lift_apply_of] at h2
      simpa using h2
    refine AddMonoidHom.ext (fun a => ?_)
    have h3 : F (Additive.toMul a) = 1 := by rw [hF]; rfl
    have h4 := congrArg Multiplicative.toAdd h3
    simpa [F] using h4
  rw [key f, key g]

/-- **The circle-valued form of the challenge hypothesis, from torsion-freeness of `H₁`.**

If `π₁(X,x)^{ab}` is torsion-free and has no non-trivial real character, then it is trivial, so
every character of `π₁(X,x)` into an abelian group -- in particular into the circle `ℝ/2πℤ` -- is
trivial. -/
theorem subsingleton_hom_addCircle_of_torsionFree {X : Type*} [TopologicalSpace X]
    (x : X) (hsub : Subsingleton (Additive (FundamentalGroup X x) →+ ℝ))
    (htf : IsMulTorsionFree (Abelianization (FundamentalGroup X x))) :
    Subsingleton (Additive (FundamentalGroup X x) →+
      (ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi))) :=
  subsingleton_addHom_of_torsionFree hsub htf

/-- **The target from the torsion-freeness of `H₁(X;ℤ) = π₁(X)^{ab}`.**  This is the *sharp*
form of the topological input: it is strictly weaker than freeness of `π₁(X)` and is all that the
modulus chapter needs.

The proof transports the hypothesis to every base point `y` (using
`subsingleton_hom_toReal_of_path` for the vanishing hypothesis and path connectedness of `X`), then
applies `subsingleton_hom_addCircle_of_torsionFree`: a torsion-free abelian group with no non-trivial
homomorphism to `ℝ` is trivial. -/
theorem exists_diffeomorph_plane_or_upperHalfPlane_of_abelianization_torsionFree {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x₀ : X) [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (htf₀ : IsMulTorsionFree (Abelianization (FundamentalGroup X x₀))) :
    Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X ℂ
        ((⊤ : ℕ∞) : WithTop ℕ∞)) ∨
      Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X UpperHalfPlane
        ((⊤ : ℕ∞) : WithTop ℕ∞)) := by
  haveI : PathConnectedSpace X := pathConnectedSpace_of_chartedSpace_complex
  refine exists_diffeomorph_plane_or_upperHalfPlane_of_subsingleton_hom_addCircle (X := X) hX x₀
    (fun y => ?_) hE
  have hsub : Subsingleton (Additive (FundamentalGroup X y) →+ ℝ) :=
    subsingleton_hom_toReal_of_path (PathConnectedSpace.somePath x₀ y) (inferInstance)
  -- transport the torsion-freeness from `x₀` to `y` along the path
  haveI : IsMulTorsionFree (Abelianization (FundamentalGroup X y)) :=
    Work.Mori.isMulTorsionFree_of_mulEquiv
      (FundamentalGroup.fundamentalGroupMulEquivOfPath (PathConnectedSpace.somePath x₀ y)).abelianizationCongr
      htf₀
  exact subsingleton_hom_addCircle_of_torsionFree y hsub inferInstance

/-- **The target from an exhaustion of `X` by pieces with torsion-free `H₁`.**

This is the form in which the abelian half of Hubbard 1.1.2 is consumed: the geometric input is the
*existence* of the exhaustion (`Work.Mori.exists_torsionFreeExhaustion_of_noncompact_riemannSurface`,
stated for a connected non-compact Riemann surface), and the passage from the pieces to `X` is the
proved bookkeeping lemma `Work.Mori.isMulTorsionFree_abelianization_of_exhaustion`. -/
theorem exists_diffeomorph_plane_or_upperHalfPlane_of_torsionFreeExhaustion {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x₀ : X) [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hexh : ∃ (K : ℕ → Set X) (hxK : ∀ n, x₀ ∈ K n),
      Monotone K ∧ (⋃ n, interior (K n)) = Set.univ ∧ (∀ n, IsCompact (K n)) ∧
      ∀ n, IsMulTorsionFree (Abelianization (FundamentalGroup ↥(K n) ⟨x₀, hxK n⟩))) :
    Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X ℂ
        ((⊤ : ℕ∞) : WithTop ℕ∞)) ∨
      Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X UpperHalfPlane
        ((⊤ : ℕ∞) : WithTop ℕ∞)) := by
  obtain ⟨K, hxK, hmono, hint, _hcomp, htf⟩ := hexh
  exact exists_diffeomorph_plane_or_upperHalfPlane_of_abelianization_torsionFree (X := X) hX x₀ hE
    (Work.Mori.isMulTorsionFree_abelianization_of_exhaustion x₀ K hmono hint hxK htf)

/-- **The target from torsion-freeness of `H₁` of the superlevel pieces of the Green function.**

This is the *spine-free* route at its sharpest interface.  The superlevel sets
`{x | ε ≤ E x} ∪ {z₀}` of the unit-pole Green function at *regular* levels `ε` are compact surfaces
(their boundary is the level set `{E = ε}`, the pole is an interior point), they exhaust `X` in a
nested way (with the pole inside every piece, which is why the pieces are the union with `{z₀}`),
and torsion-freeness of `H₁` passes from the pieces to `X`
(`Work.Mori.isMulTorsionFree_abelianization_of_isUnitGreenFunction`, whose input is the piece-level
hypothesis `hpiece` below; regular levels exist by
`Work.Mori.exists_regularLevel_of_isUnitGreenFunction`).  The hypothesis `H¹(X,ℝ) = 0` then kills
every circle-valued character of `π₁(X)`
(`exists_diffeomorph_plane_or_upperHalfPlane_of_abelianization_torsionFree`).

`hpiece` is exactly what the compact-bordered-surface spine theorem
(`Work.Spine.fundamentalGroup_isFreeGroup_of_compact_bordered_surface`) supplies — freeness of the
`π₁` of each piece implies torsion-freeness of its abelianization — but it is stated without assuming
any surface structure on the pieces, so a proof of torsion-freeness by another route (for instance
one that only needs the regular level set to be a `C¹` graph, which
`Work.CriticalSet.levelSet_isLocalGraph` provides) also suffices. -/
theorem exists_diffeomorph_plane_or_upperHalfPlane_of_superlevel_torsionFree {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x₀ : X) [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hpiece : ∀ ε : ℝ, 0 < ε →
      Work.CriticalSet.IsRegularValueOn E (Work.CriticalSet.punctured z₀) ε →
      ∀ p : ↥({x : X | ε ≤ E x} ∪ {z₀}),
        IsMulTorsionFree (Abelianization (FundamentalGroup ↥({x : X | ε ≤ E x} ∪ {z₀}) p))) :
    Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X ℂ
        ((⊤ : ℕ∞) : WithTop ℕ∞)) ∨
      Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X UpperHalfPlane
        ((⊤ : ℕ∞) : WithTop ℕ∞)) :=
  exists_diffeomorph_plane_or_upperHalfPlane_of_abelianization_torsionFree (X := X) hX x₀ hE
    (Work.Mori.isMulTorsionFree_abelianization_of_isUnitGreenFunction (X := X) (z₀ := z₀) hX hE
      hpiece)

/-! ## The purely analytic interface: the injective extremal family

The *second* route to the target of this file is available in the workspace and is **entirely
analytic** (no CW complexes, no spines): `Submission.uniformization_of_injective_into_disc` (in
`Submission/ExtremalInj.lean`, proved and axiom-clean) produces the conclusion from the challenge
hypothesis plus a single *univalent* (injective) holomorphic `f : X → 𝔻` with `f x₀ = 0`
(a member of `Submission.injFamily x₀`).

That input is the remaining content of the ABS (Anghel–Bruin–Stan) route; the machinery of the
route is already in the workspace (`Submission/Extremal*`, `Submission/DiagLimit`,
`Submission/AbsEndgame`, `Submission/UnivalentCompactness`, all sorry-free).  The consumer below
records the interface, with no `sorryAx`: whoever produces a member of `injFamily x₀` closes this
file through it, independently of `Work.Spine` and of `Work.Mori`. -/

/-- **The target from a member of the injective extremal family** (the ABS interface). -/
theorem exists_diffeomorph_plane_or_upperHalfPlane_of_injFamily {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (x₀ : X) [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    (h : (Submission.injFamily x₀).Nonempty) :
    Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X ℂ
        ((⊤ : ℕ∞) : WithTop ℕ∞)) ∨
      Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X UpperHalfPlane
        ((⊤ : ℕ∞) : WithTop ℕ∞)) :=
  Submission.uniformization_of_injective_into_disc (x₀ := x₀) h

/-- **The target from a cut system** (`Commons.Topology.Surface.HasCutSystemCore X`, the geometric
input of the spine construction in the surface-topology chapter): this is the *direct* consumer of a
completed `HasCutSystemCore X`.  The cut system yields a one-dimensional CW model of `X`
(`Commons.Topology.Surface.spine_of_noncompact_surface_of_core`), hence freeness of `π₁(X)`, hence
(by Hypothesis, i.e. the vanishing of the real characters) triviality of `π₁(X)`, and the modulus
chapter plus the hyperbolic endgame conclude. -/
theorem exists_diffeomorph_plane_or_upperHalfPlane_of_hasCutSystemCore {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x₀ : X) [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hcore : Commons.Topology.Surface.HasCutSystemCore X) :
    Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X ℂ
        ((⊤ : ℕ∞) : WithTop ℕ∞)) ∨
      Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X UpperHalfPlane
        ((⊤ : ℕ∞) : WithTop ℕ∞)) := by
  refine exists_diffeomorph_plane_or_upperHalfPlane_of_hubbard112 (X := X) hX x₀ hE
    (fun hXc x _ => ?_)
  haveI : PathConnectedSpace X := Work.Spine.pathConnectedSpace_of_chartedSpace_complex
  obtain ⟨G, hC, -, hdim, he⟩ :=
    Commons.Topology.Surface.spine_of_noncompact_surface_of_core (X := X) hXc hcore
  haveI : IsFreeGroup (FundamentalGroup X x) :=
    Work.Spine.isFreeGroup_fundamentalGroup_of_oneDimCWComplex x hC hdim he
  haveI : Subsingleton (FundamentalGroup X x) :=
    Work.Spine.subsingleton_of_isFreeGroup_of_subsingleton_hom_toReal
  exact Work.Spine.simplyConnectedSpace_of_subsingleton_fundamentalGroup x


/-- **The target from a wild-graph spine** (`Work.Spine.Surface.SpineDatum X`, the geometric input
of the second branch of the spine programme): a locally finite family of arcs meeting pairwise in
common endpoints whose carrier is homotopy equivalent to `X`.  This is the *direct* consumer of a
completed `Work.Spine.Surface.exists_spineDatum_homotopyEquiv_of_noncompact`. -/
theorem exists_diffeomorph_plane_or_upperHalfPlane_of_spineDatum {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x₀ : X) [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (D : Work.Spine.Surface.SpineDatum X)
    (he : Nonempty (ContinuousMap.HomotopyEquiv X ↥D.carrier)) :
    Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X ℂ
        ((⊤ : ℕ∞) : WithTop ℕ∞)) ∨
      Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X UpperHalfPlane
        ((⊤ : ℕ∞) : WithTop ℕ∞)) := by
  refine exists_diffeomorph_plane_or_upperHalfPlane_of_hubbard112 (X := X) hX x₀ hE
    (fun _ x _ => ?_)
  haveI : PathConnectedSpace X := Work.Spine.pathConnectedSpace_of_chartedSpace_complex
  haveI : IsFreeGroup (FundamentalGroup X x) :=
    Work.Spine.Surface.isFreeGroup_fundamentalGroup_of_spineDatum D he x
  haveI : Subsingleton (FundamentalGroup X x) :=
    Work.Spine.subsingleton_of_isFreeGroup_of_subsingleton_hom_toReal
  exact Work.Spine.simplyConnectedSpace_of_subsingleton_fundamentalGroup x


/-- **The target from a one-dimensional CW model** — the *sharpest and most general* interface: it
takes exactly the conclusion of the central geometric input
`Work.Spine.exists_homotopyEquiv_oneDimCWComplex_of_noncompact` (and of
`Commons.Topology.Homotopy.spine_geometric_input_of_chamber_data`, and of every other statement in
the project that produces a one-dimensional CW model of `X`). -/
theorem exists_diffeomorph_plane_or_upperHalfPlane_of_oneDimCWModel {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x₀ : X) [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hmodel : ∃ (Y : Type*) (tY : TopologicalSpace Y), @T2Space Y tY ∧
      ∃ (hC : @Topology.CWComplex Y tY Set.univ),
        (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell Y tY Set.univ hC n)) ∧
        Nonempty (@ContinuousMap.HomotopyEquiv X Y _ tY)) :
    Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X ℂ
        ((⊤ : ℕ∞) : WithTop ℕ∞)) ∨
      Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X UpperHalfPlane
        ((⊤ : ℕ∞) : WithTop ℕ∞)) := by
  refine exists_diffeomorph_plane_or_upperHalfPlane_of_hubbard112 (X := X) hX x₀ hE
    (fun _ x _ => ?_)
  haveI : PathConnectedSpace X := Work.Spine.pathConnectedSpace_of_chartedSpace_complex
  obtain ⟨Y, tY, hT2, hC, hdim, he⟩ := hmodel
  haveI := hT2
  haveI : IsFreeGroup (FundamentalGroup X x) :=
    Work.Spine.isFreeGroup_fundamentalGroup_of_oneDimCWComplex (X := X) (Y := Y) x hC hdim he
  haveI : Subsingleton (FundamentalGroup X x) :=
    Work.Spine.subsingleton_of_isFreeGroup_of_subsingleton_hom_toReal
  exact Work.Spine.simplyConnectedSpace_of_subsingleton_fundamentalGroup x


end Work.SimplyConnected

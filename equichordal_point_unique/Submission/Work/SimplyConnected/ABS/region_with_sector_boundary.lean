import Mathlib
import Submission.Work.SimplyConnected.ABS.RegularPieceDefs
import Submission.Work.SimplyConnected.ABS.regularPiece_core
import Submission.Work.SimplyConnected.ABS.ballChain
import Submission.Work.SimplyConnected.Final
import Submission.Work.SimplyConnected.AbsData
import Submission.UnifHelpers
import Submission.Work.Parabolic.Main
import Submission.Work.UnitGreen.Defs
import Submission.Work.Modulus.Main
import Submission.Work.Mori.Main
import Submission.Work.SimplyConnected.ABS.sectorCondition_of_chart_balls
import Submission.Work.Topology.Surface.sectorCondition_chartBallUnion_generalPosition
import Submission.Work.Topology.Surface.sectorCondition_chartBallUnion_multiChart
import Submission.Work.SimplyConnected.ABS.simplyConnectedSpace_biUnion_list
import Submission.Work.SimplyConnected.ABS.chartBall_transport
import Submission.Work.SimplyConnected.ABS.exists_ballPiece_of_closedDisc
import Submission.Work.SimplyConnected.ABS.exists_regularPiece_of_greenOn_modulus
import Submission.Work.SimplyConnected.ABS.isGreenOn_of_sectorRegion
import Submission.Work.SimplyConnected.ABS.green_reduction.sard_lite_manifold
import Submission.Work.SimplyConnected.ABS.green_reduction.level_component_supset
import Submission.Work.SimplyConnected.ABS.OneEnded.exists_contMDiff_sublevel_compact

/-!
# A relatively compact simply connected region with sector boundary

The target is `Work.SimplyConnected.ABS.region_with_sector_boundary`: every compact subset `K` of a
simply connected non-compact Riemann surface `X` is contained in an open `W` with compact closure,
`W ≠ univ`, `W` simply connected, and satisfying the *sector* (cone) condition
`Work.SimplyConnected.ABS.HasSectorBoundary W p` at every frontier point of `W`.

## What is proved here (verified, no `sorry`)

* `ne_univ_of_isCompact_closure`, `simplyConnectedSpace_of_homeomorph_ball` — elementary.
* `region_with_sector_boundary_of_plane` / `_of_disc` / `_of_upperHalfPlane` /
  `_of_dichotomy`: the conclusion for a surface biholomorphic to `ℂ`, to the open unit disc, or to
  the upper half plane.  These use only the *verified* plane-level theorems
  `Work.SimplyConnected.ABS.exists_regularPiece_of_diffeomorph_plane` and
  `..._of_diffeomorph_disc` (which produce, for every compact `K`, an open `U ⊇ K` homeomorphic to
  the unit disc, with compact closure and the sector condition at every frontier point);
  `U ≠ X` follows from non-compactness.
* `region_with_sector_boundary_of_weakGreen`: **the hyperbolic case**, where `X` carries a weak Green
  function: the dichotomy holds by the fully verified hyperbolic branch
  (`Work.SC.uniformization_of_hyperbolic`, whose proof uses no `sorryAx`).
* `subsingleton_characters_of_simplyConnected`, `region_with_sector_boundary_of_parabolic_of_injective`:
  the parabolic case *given* the ABS embedding input (an injective holomorphic `X → ℂ`), via
  `Work.Parabolic.plane_of_no_greenFunction`.

## The sector half is complete, in the multi-chart form (verified)

Three interfaces proved in this file and in the two modules
`Submission.Work.Topology.Surface.sectorCondition_chartBallUnion_multiChart` /
`hasSectorBoundary_union_of_two_sublevel` discharge the *sector* condition for every shape of region
the ABS engulfing produces:

* `region_with_sector_boundary_of_multiChartBallUnion_genPos` — `V` is a finite union of chart balls
  taken in **different** atlas charts, in general position (at most two closed balls through each
  frontier point, and no external tangency there, expressed through the transition's derivative);
* `region_with_sector_boundary_of_filling_multiChartBallUnion` — `Ω` is a *filling* / a component of
  the interior of such a union (the shape the tile-based engulfing produces), with
  `frontier Ω ⊆ frontier (⋃ balls)` and `Ω` locally inside the closure of the union;
* `hasSectorBoundary_of_subset_closure_of_nhds` — the local transfer lemma behind the second.

In each case the residual hypothesis is only the *simple connectivity* of the region (the crux, see
below).  The single-chart forms (`region_with_sector_boundary_of_chartBallUnion_genPos`,
`hasSectorBoundary_filling_of_chartBallUnion`) remain available but are strictly stronger inputs.

## Status and wiring (measured 2026-09-23, see NOTES §BT.1–§BT.9)

The *live* closure of `Submission.lean` (the file the comparator reads) is 170 local modules and does
**not** contain this module: the main theorem is `uniformization_via_spine`
(`Submission/Assembly.lean`), whose two inputs are the two `sorry`s of `Submission/Gaps.lean`, namely
the **spine** theorem (`Work.Spine.*`) and the **simply connected case**
`uniformization_of_simplyConnected` — the latter being reduced in the corpus to the ABS input
`∃ φ : X → ℂ` holomorphic injective.  This file is the *alternative* route to that gap: its target
plus the landed `planarity_around_compact` gives a chart with room around every compact set, hence
disc pieces, hence the simply connected case.

The residual obligation of the target below is therefore exactly one of:

* the ABS input (an injective holomorphic `X → ℂ`) — the route the file's own `sorry` names, or
* planarity / (SURF): "a precompact open region of a simply connected non-compact surface whose
  complementary components all have non-compact closure is simply connected" — which closes the target
  through the *(FILL)* interfaces below, since the sector half is free for the filling of a
  multi-chart ball union in general position.

Everything else in this file (the hyperbolic branch, the sector half in its multi-chart form, the
beading-chain interface, the level-set interfaces) is proved.

## The sharpest interface: a single chart with room around `K` (verified)

`region_with_sector_boundary_of_chart_with_room` (proved below, axiom-clean) shows that the target
follows from the *single* statement

> **(CHART WITH ROOM)** for every compact `K` there is an atlas chart `φ`, a centre `a : ℂ` and a
> radius `ρ > 0` with `K ⊆ φ.source`, `φ '' K ⊆ Metric.ball a ρ` and
> `Metric.closedBall a ρ ⊆ φ.target`.

The witness is the single chart ball `chartBall φ a ρ`; nothing weaker can suffice, because the
remaining ingredients (openness, compact closure, simple connectivity, and the sector condition at
every frontier point) are *free* for a chart ball.  (CHART WITH ROOM) is the conclusion of
`Work.SimplyConnected.ABS.planarity_around_compact` and the hypothesis of
`Work.SimplyConnected.ABS.exists_discPiece_of_chart_with_room`; it is equivalent to the
uniformization theorem in this workspace, so the single `sorry` below *is* the project's crux, in
its most usable form.

## Two further verified interfaces: the sector condition is now *free*

The sector half of the target no longer needs (CHART WITH ROOM):

* **`hasSectorBoundary_filling_of_chartBallUnion`** — for a finite union `V` of chart balls in one
  atlas chart, in general position (at most two closed balls through any point, no external tangency
  at frontier points), the *filling* `W = filling V` satisfies the sector condition at *every*
  frontier point, provided only that `W` is open.  (The avoided sector is the explicit wedge of
  `exists_wedge_functionals_chartBallUnion`; the key point is that the component of `p` in `Vᶜ` is
  non-compact, hence disjoint from `W`.)
* **`hasSectorBoundary_of_isRegularLevel_sublevel` / `..._superlevel`** — at a point where a
  non-critical level of a *harmonic* function bounds the region, the sector condition holds, with
  the avoided sector on the side where the function decreases.  These are built from the elementary
  wedge construction `exists_wedge_functionals_of_ne_zero_coeffs` and the two analytic wedges
  `exists_wedge_of_hasFDerivAt` / `exists_wedge_of_hasFDerivAt_lt`, and cover exactly the boundary
  shape of the ABS filling (a regular level of a region Green function).

Consequently the target follows from the ABS engulfing data in either of two forms:
`region_with_sector_boundary_of_filling_chartBallUnion` (a general-position union of chart balls in
one chart whose filling is open, precompact and simply connected) and
`region_with_sector_boundary_of_levelSet_engulfing` (an abstract open connected precompact `Omega`,
simply connected, whose frontier points carry harmonic regular-level data).  In both, the residual
obligation is the shared crux: the existence of the engulfing region `(FILL)` and its simple
connectivity `(SURF)`.

## The remaining gap, precisely

`region_with_sector_boundary` splits on whether `X` carries a weak Green function.  The hyperbolic
case is discharged above.  The parabolic case (`Work.Parabolic.IsParabolic X`) needs the single
classical input

  *a simply connected non-compact Riemann surface admits an injective holomorphic function into
  `ℂ`*  (Anghel--Bruin--Stan, Theorem 1; equivalently, in the parabolic case, Mori's normal form),

i.e. `Work.Mori.HasHolomorphicEmbedding X` / `Work.Mori.ABSTheorem X`.  With it,
`region_with_sector_boundary_of_parabolic_of_injective` finishes the proof.

In this workspace that input is *exactly* the ABS engulfing (Theorem 12) together with the disc
lemma (Theorem 10); the engulfing is the statement of `Work.SimplyConnected.ABS.regularPiece_core`
(this file's target with the frontier-connectivity clause), and every route to it in the library
currently passes through an unresolved `sorry` (`regularPiece_core`, `exists_isGreenOn_of_barriers`,
`exists_hasDiscExhaustion`, `Work.Spine.exists_homotopyEquiv_oneDimCWComplex_of_noncompact` — the
last is vacuous as stated, see its docstring).  In particular no theorem of the library proves the
parabolic case without that input, and none can: the input is the topological/analytic content of
the non-compact case of uniformization.

Note also that the *hyperbolic* case cannot be used to deduce the parabolic one by applying the
hyperbolic branch to a subregion: that branch requires the subregion to be simply connected, which is
exactly what has to be proved.

-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology ComplexConjugate
open Set Metric

set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [SimplyConnectedSpace X]

/-- **A subset with compact closure is never all of a non-compact space.** -/
theorem ne_univ_of_isCompact_closure (hX : ¬ CompactSpace X) {U : Set X}
    (h : IsCompact (closure U)) : U ≠ Set.univ := by
  intro hU
  rw [hU, closure_univ] at h
  exact hX (isCompact_univ_iff.mp h)


/-- **A set homeomorphic to the open unit disc is simply connected.** -/
theorem simplyConnectedSpace_of_homeomorph_ball {U : Set X}
    (h : Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥U)) : SimplyConnectedSpace ↥U := by
  obtain ⟨φ⟩ := h
  haveI : ContractibleSpace ↥(Metric.ball (0 : ℂ) 1) :=
    Convex.contractibleSpace (convex_ball (0 : ℂ) 1) ⟨0, by simp [Metric.mem_ball]⟩
  exact (φ.symm.toHomotopyEquiv).simplyConnectedSpace

 /-- **The target from a relatively compact *disc piece* with cone boundary.**

This is the sharpest form of the remaining gap: if every compact set `K` of `X` lies in an open `U`
with `U` homeomorphic to the open unit disc, `closure U` compact and the cone condition at every
frontier point of `U` (the geometric core of ABS Theorem 12, i.e.
`Work.SimplyConnected.ABS.exists_isRegularPiece_core` with the frontier-connectedness clause
dropped), then the target follows: `U != X` because `closure U` is compact and `X` is non-compact,
and `↥U` is simply connected because it is homeomorphic to the disc. -/
theorem region_with_sector_boundary_of_discPiece (hX : ¬ CompactSpace X) {K : Set X}
    (h : ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ IsCompact (closure U) ∧
      Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥U) ∧
      ∀ p ∈ frontier U, Work.SimplyConnected.ABS.HasSectorBoundary U p) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  obtain ⟨U, hUo, hKU, hUcomp, hUball, hsect⟩ := h
  exact ⟨U, hUo, hKU, hUcomp, ne_univ_of_isCompact_closure hX hUcomp,
    simplyConnectedSpace_of_homeomorph_ball hUball, hsect⟩

/-- **The sector condition at a point where two one-sided regions meet, in one chart.**

Let c be an atlas chart at p and let W1, W2 be sets which, near p, lie respectively in the
half-planes {L1 <= 0} and {L2 <= 0} cut out in the chart c by two non-zero functionals whose
positive sides meet.  Then the union of W1 and W2 satisfies the cone condition at p, with the wedge
{0 < L1} intersected with {0 < L2} as the avoided sector.

This is the two-ball step of the cluster analysis in the form that does NOT require the two balls to
be round in the same chart: it is enough that each is one-sided with respect to its own transported
conormal.  The chart-transition bookkeeping (producing the functional and the one-sidedness for a
round chart ball read in another chart) is the only remaining input; the aggregation itself is here.
-/
theorem hasSectorBoundary_union_of_two_oneSided {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {W₁ W₂ : Set X} {p : X} {c : OpenPartialHomeomorph X ℂ}
    (hc : c ∈ atlas ℂ X) (hps : p ∈ c.source) {L₁ L₂ : ℂ →L[ℝ] ℝ}
    (hL₁ : L₁ ≠ 0) (hL₂ : L₂ ≠ 0) (hwit : ∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w)
    (h₁ : ∀ᶠ x in 𝓝 p, x ∈ W₁ → L₁ (c x - c p) ≤ 0)
    (h₂ : ∀ᶠ x in 𝓝 p, x ∈ W₂ → L₂ (c x - c p) ≤ 0) :
    Work.SimplyConnected.ABS.HasSectorBoundary (W₁ ∪ W₂) p := by
  classical
  obtain ⟨w, hw₁, hw₂⟩ := hwit
  rcases Filter.eventually_iff_exists_mem.mp h₁ with ⟨V₁, hV₁mem, hV₁⟩
  rcases Filter.eventually_iff_exists_mem.mp h₂ with ⟨V₂, hV₂mem, hV₂⟩
  refine ⟨c, interior (V₁ ∩ V₂) ∩ c.source, L₁, L₂, hc, ?_, ?_, ?_, hps, hL₁, hL₂,
    ⟨w, hw₁, hw₂⟩, ?_⟩
  · exact isOpen_interior.inter c.open_source
  · exact ⟨mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hV₁mem hV₂mem), hps⟩
  · exact fun _ hx => hx.2
  · intro x hx
    rintro ⟨hx₁, hx₂⟩
    have hxV : x ∈ V₁ ∩ V₂ := interior_subset hx.2.1
    rcases hx.1 with hx | hx
    · exact absurd (hV₁ x hxV.1 hx) (not_le.mpr hx₁)
    · exact absurd (hV₂ x hxV.2 hx) (not_le.mpr hx₂)

/-- **The conclusion for a surface biholomorphic to the plane.** -/
theorem region_with_sector_boundary_of_plane (hX : ¬ CompactSpace X)
    (e : X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)
    (K : Set X) (hK : IsCompact K) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  obtain ⟨W, hWo, hhomeo, hcomp, -, hKW, hsector⟩ :=
    exists_regularPiece_of_diffeomorph_plane (X := X) e hK
  exact ⟨W, hWo, hKW, hcomp, ne_univ_of_isCompact_closure hX hcomp,
    simplyConnectedSpace_of_homeomorph_ball hhomeo, hsector⟩

/-- **The conclusion for a surface biholomorphic to the open unit disc.** -/
theorem region_with_sector_boundary_of_disc (hX : ¬ CompactSpace X)
    (e : X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ Submission.Helpers.DiscOpen)
    (K : Set X) (hK : IsCompact K) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  obtain ⟨W, hWo, hhomeo, hcomp, -, hKW, hsector⟩ :=
    exists_regularPiece_of_diffeomorph_disc (X := X) e hK
  exact ⟨W, hWo, hKW, hcomp, ne_univ_of_isCompact_closure hX hcomp,
    simplyConnectedSpace_of_homeomorph_ball hhomeo, hsector⟩

/-- **The conclusion for a surface biholomorphic to the upper half plane.** -/
theorem region_with_sector_boundary_of_upperHalfPlane (hX : ¬ CompactSpace X)
    (e : X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane)
    (K : Set X) (hK : IsCompact K) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  obtain ⟨d⟩ := Commons.Analysis.Complex.UpperHalfPlane.halfPlane_disc_diffeomorph
  exact region_with_sector_boundary_of_disc (X := X) hX (e.trans d) K hK

/-- **The conclusion from the uniformization dichotomy.** -/
theorem region_with_sector_boundary_of_dichotomy (hX : ¬ CompactSpace X)
    (h : Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane))
    (K : Set X) (hK : IsCompact K) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  cases h with
  | inl h1 =>
    obtain ⟨e⟩ := h1
    exact region_with_sector_boundary_of_plane (X := X) hX e K hK
  | inr h2 =>
    obtain ⟨e⟩ := h2
    exact region_with_sector_boundary_of_upperHalfPlane (X := X) hX e K hK

/-- **The hyperbolic case.**  If `X` carries a weak Green function then the uniformization
dichotomy holds (`Work.SC.uniformization_of_hyperbolic`, fully verified), whence the conclusion. -/
theorem region_with_sector_boundary_of_weakGreen (hX : ¬ CompactSpace X)
    {z₀ : X} {E : X → ℝ} (hE : Submission.HasGreenFunctionWeak z₀ E) (K : Set X)
    (hK : IsCompact K) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p :=
  region_with_sector_boundary_of_dichotomy (X := X) hX
    (Work.SC.uniformization_of_hyperbolic (X := X) hX hE) K hK

section ChartBallMonotoneUnion

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- **The monotone-union identity (§BG.3, Route 2 engine).**  A chart ball is the union of the chart
balls of strictly smaller radius, over all positive decrements.  Equivalently: every compact subset
of `chartBall c a ρ` already lies in `chartBall c a (ρ - δ)` for some `δ > 0`. -/
theorem chartBall_eq_iUnion_sub {c : OpenPartialHomeomorph Y ℂ} {a : ℂ} {ρ : ℝ} :
    Submission.chartBall c a ρ = ⋃ δ ∈ {δ : ℝ | 0 < δ}, Submission.chartBall c a (ρ - δ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxsrc, hxb⟩ := Submission.mem_chartBall.mp hx
    have hd : ‖c x - a‖ < ρ := by
      rw [Metric.mem_ball, dist_eq_norm] at hxb
      exact hxb
    have hδ : 0 < (ρ - ‖c x - a‖) / 2 := div_pos (sub_pos.mpr hd) two_pos
    refine Set.mem_iUnion₂.mpr ⟨(ρ - ‖c x - a‖) / 2, hδ, ?_⟩
    refine Submission.mem_chartBall.mpr ⟨hxsrc, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have hstep : (‖c x - a‖ + ‖c x - a‖) / 2 < (ρ + ‖c x - a‖) / 2 :=
      div_lt_div_of_pos_right (add_lt_add_left hd (‖c x - a‖)) two_pos
    have hid : (‖c x - a‖ + ‖c x - a‖) / 2 = ‖c x - a‖ := by ring
    rw [hid] at hstep
    have hval : ρ - (ρ - ‖c x - a‖) / 2 = (ρ + ‖c x - a‖) / 2 := by ring
    rwa [hval]
  · intro hx
    obtain ⟨δ, hδ, hxb⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hxsrc, hxb'⟩ := Submission.mem_chartBall.mp hxb
    have h : ‖c x - a‖ < ρ - δ := by
      rw [Metric.mem_ball, dist_eq_norm] at hxb'
      exact hxb'
    refine Submission.mem_chartBall.mpr ⟨hxsrc, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le h (sub_le_self ρ hδ.le)

end ChartBallMonotoneUnion

section ChartBallCompactShrink

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- Monotonicity of chart balls in the radius (in the `ρ`-direction, for a fixed chart and centre). -/
theorem chartBall_subset_chartBall_of_le {c : OpenPartialHomeomorph Y ℂ} {a : ℂ} {ρ ρ' : ℝ}
    (h : ρ ≤ ρ') : Submission.chartBall c a ρ ⊆ Submission.chartBall c a ρ' := by
  intro x hx
  obtain ⟨hxsrc, hxb⟩ := Submission.mem_chartBall.mp hx
  exact Submission.mem_chartBall.mpr ⟨hxsrc, Metric.ball_subset_ball h hxb⟩

/-- **Route 2's per-piece shrink.**  Every compact subset of a chart ball is already inside a chart
ball of strictly smaller radius.  This is the step that lets the shrink lemma (§BG.3) source its
`δ`'s from a single chart: apply it to each compact piece of a finite subcover. -/
theorem exists_sub_radius_of_isCompact_subset_chartBall {c : OpenPartialHomeomorph Y ℂ} {a : ℂ}
    {ρ : ℝ} {S : Set Y} (hS : IsCompact S) (hsub : S ⊆ Submission.chartBall c a ρ) :
    ∃ δ : ℝ, 0 < δ ∧ S ⊆ Submission.chartBall c a (ρ - δ) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · exact ⟨1, one_pos, by simp⟩
  have hchoice : ∀ x : S, ∃ δ : ℝ, 0 < δ ∧ (x : Y) ∈ Submission.chartBall c a (ρ - δ) := by
    intro x
    have hx : (x : Y) ∈ ⋃ δ ∈ {δ : ℝ | 0 < δ}, Submission.chartBall c a (ρ - δ) := by
      rw [← Work.SimplyConnected.ABS.chartBall_eq_iUnion_sub]
      exact hsub x.2
    obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨e, he, hxe⟩
  choose d hd hxd using hchoice
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun x : S => Submission.chartBall c a (ρ - d x))
    (fun x => Submission.chartBall_isOpen c a (ρ - d x))
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxd ⟨x, hx⟩⟩)
  obtain ⟨y₀, hy₀⟩ := hSne
  obtain ⟨a₀, ha₀t, -⟩ := Set.mem_iUnion₂.mp (ht hy₀)
  have htne : t.Nonempty := ⟨a₀, ha₀t⟩
  refine ⟨t.inf' htne d, (Finset.lt_inf'_iff htne).mpr (fun b _ => hd b), ?_⟩
  intro x hx
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact chartBall_subset_chartBall_of_le (ρ := ρ - d y) (ρ' := ρ - t.inf' htne d)
    (sub_le_sub_left (Finset.inf'_le d hyt) ρ) hxy

end ChartBallCompactShrink

section ShrinkAssembly

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- **§BG.3, Route 2 completed (metric-free).**  Any finite chart-ball cover of a compact set can be
uniformly shrunk, keeping the cover: a single global decrement of all radii suffices. -/
theorem exists_shrunk_chartBall_cover_of {K : Set Y} (hK : IsCompact K) (x₀ : Y) {n : ℕ}
    (hn : 0 < n) (z : Fin n → Y) (r : Fin n → ℝ) (hz : Function.Injective z)
    (hr : ∀ i, 0 < r i)
    (hroom : ∀ i, Metric.closedBall ((chartAt ℂ (z i)) (z i)) (r i) ⊆ (chartAt ℂ (z i)).target)
    (hcov : K ∪ {x₀} ⊆ ⋃ i, Submission.chartBall (chartAt ℂ (z i))
      ((chartAt ℂ (z i)) (z i)) (r i)) :
    ∃ r' : Fin n → ℝ, (∀ i, 0 < r' i) ∧ (∀ i, r' i ≤ r i) ∧
      (∀ i, Metric.closedBall ((chartAt ℂ (z i)) (z i)) (r' i) ⊆ (chartAt ℂ (z i)).target) ∧
      K ∪ {x₀} ⊆ ⋃ i, Submission.chartBall (chartAt ℂ (z i))
        ((chartAt ℂ (z i)) (z i)) (r' i) := by
  classical
  have hKc : IsCompact (K ∪ {x₀}) := hK.union isCompact_singleton
  have hstep : ∀ y : ↥(K ∪ {x₀}), ∃ (i : Fin n) (δ : ℝ), 0 < δ ∧
      (y : Y) ∈ Submission.chartBall (chartAt ℂ (z i)) ((chartAt ℂ (z i)) (z i)) (r i - δ) := by
    intro y
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov y.2)
    have hy : (y : Y) ∈ ⋃ δ ∈ {δ : ℝ | 0 < δ}, Submission.chartBall (chartAt ℂ (z i))
        ((chartAt ℂ (z i)) (z i)) (r i - δ) := by
      rw [← Work.SimplyConnected.ABS.chartBall_eq_iUnion_sub]
      exact hi
    obtain ⟨δ, hδ, hyδ⟩ := Set.mem_iUnion₂.mp hy
    exact ⟨i, δ, hδ, hyδ⟩
  choose iF dF hdF hmemF using hstep
  obtain ⟨s, hs⟩ := hKc.elim_finite_subcover
    (fun y : ↥(K ∪ {x₀}) => Submission.chartBall (chartAt ℂ (z (iF y)))
      ((chartAt ℂ (z (iF y))) (z (iF y))) (r (iF y) - dF y))
    (fun y => Submission.chartBall_isOpen _ _ _) (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hmemF ⟨y, hy⟩⟩)
  have hsne : s.Nonempty := by
    obtain ⟨y, hy⟩ : (K ∪ {x₀}).Nonempty := ⟨x₀, Or.inr rfl⟩
    obtain ⟨y', hy's, -⟩ := Set.mem_iUnion₂.mp (hs hy)
    exact ⟨y', hy's⟩
  have hune : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  let δ : ℝ := min (s.inf' hsne dF) (((Finset.univ : Finset (Fin n)).inf' hune r) / 2)
  have hδpos : 0 < δ := lt_min ((Finset.lt_inf'_iff hsne).mpr (fun b _ => hdF b))
    (div_pos ((Finset.lt_inf'_iff hune).mpr (fun b _ => hr b)) two_pos)
  refine ⟨fun i => r i - δ, ?_, ?_, ?_, ?_⟩
  · intro i
    have h1 : δ ≤ r i / 2 := le_trans (min_le_right _ _)
      (div_le_div_of_nonneg_right (Finset.inf'_le r (Finset.mem_univ i)) two_pos.le)
    exact sub_pos.mpr (lt_of_le_of_lt h1 (half_lt_self (hr i)))
  · intro i
    exact sub_le_self _ hδpos.le
  · intro i
    exact (Metric.closedBall_subset_closedBall (sub_le_self _ hδpos.le)).trans (hroom i)
  · intro y hy
    obtain ⟨y', hy's, hy'y⟩ := Set.mem_iUnion₂.mp (hs hy)
    refine Set.mem_iUnion.mpr ⟨iF y', ?_⟩
    have hle : r (iF y') - dF y' ≤ r (iF y') - δ :=
      sub_le_sub_left (le_trans (min_le_left _ _) (Finset.inf'_le dF hy's)) _
    exact Work.SimplyConnected.ABS.chartBall_subset_chartBall_of_le hle hy'y

end ShrinkAssembly



/-! ### The path-chaining lemma (§BF.9 of the status notes)

`exists_chain_class` is the combinatorial core of the general-position construction: an open cover of
the image of a path has a *meeting-closed class* of members covering the image.  It is what lets the
beading walk from one dedicated chart ball to another: the class covers the path, and can be
enumerated as a finite list by induction along `Relation.ReflTransGen`, so the construction can
attach balls one at a time along it.

Nothing here uses charts, the tiling, or the engulfing: it is `Path`, `Relation.ReflTransGen`, and
the classical clopen argument. -/
section PathChaining

/-- **The path-chaining lemma.**  If `U : ι → Set X` is an open cover of the image of a path
`γ : Path y y'` and `γ 0 ∈ U i`, then there is a set `R` of indices containing `i`, covering the
image of `γ`, and closed under meeting: `a ∈ R` and `(U a ∩ U b).Nonempty` imply `b ∈ R`.

`A := ⋃ k ∈ R, U k` is open, and `T := γ ⁻¹' A` is also closed — a point of the path outside `A`
has an open neighbourhood `U j` disjoint from `A`, so `j ∉ R` and `U j ⊆ Aᶜ` — hence `T` is clopen
and non-empty in the connected `unitInterval`. -/
theorem exists_chain_class {X ι : Type*} [TopologicalSpace X] {y y' : X} (γ : Path y y')
    {U : ι → Set X} (hUo : ∀ k, IsOpen (U k)) (hcov : ∀ t, ∃ k, γ t ∈ U k) {i : ι}
    (hi : γ 0 ∈ U i) :
    ∃ R : Set ι, i ∈ R ∧ (∀ t, ∃ k ∈ R, γ t ∈ U k) ∧
      (∀ a ∈ R, ∀ b, (U a ∩ U b).Nonempty → b ∈ R) := by
  classical
  set rel : ι → ι → Prop := fun a b => (U a ∩ U b).Nonempty with hrel
  refine ⟨{b | Relation.ReflTransGen rel i b}, Relation.ReflTransGen.refl, ?_, ?_⟩
  · intro t
    set R : Set ι := {b | Relation.ReflTransGen rel i b} with hR
    set A : Set X := ⋃ k ∈ R, U k with hA
    have hAopen : IsOpen A := by rw [hA]; exact isOpen_biUnion fun k _ => hUo k
    have hA0 : γ 0 ∈ A := by
      rw [hA]
      exact Set.mem_iUnion₂.mpr ⟨i, Relation.ReflTransGen.refl, hi⟩
    have hTopen : IsOpen (γ ⁻¹' A) := hAopen.preimage γ.continuous
    have hTcl : IsClosed (γ ⁻¹' A) := by
      rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro s hs
      obtain ⟨j, hj⟩ := hcov s
      have hdisj : U j ∩ A = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨hxj, hxA⟩
        obtain ⟨k, hkR, hxk⟩ := Set.mem_iUnion₂.mp hxA
        have hkj : rel k j := ⟨x, hxk, hxj⟩
        exact hs (by rw [hA]; exact Set.mem_iUnion₂.mpr ⟨j, hkR.tail hkj, hj⟩)
      refine Filter.mem_of_superset (((hUo j).preimage γ.continuous).mem_nhds hj) ?_
      intro x hx hxA
      have hmem : γ x ∈ U j ∩ A := ⟨hx, hxA⟩
      rw [hdisj] at hmem
      simpa using hmem
    have hTuniv : γ ⁻¹' A = Set.univ :=
      IsClopen.eq_univ ⟨hTcl, hTopen⟩ ⟨0, hA0⟩
    have htA : γ t ∈ A := by
      have h : t ∈ γ ⁻¹' A := by rw [hTuniv]; trivial
      exact h
    obtain ⟨k, hkR, hk⟩ := Set.mem_iUnion₂.mp htA
    exact ⟨k, hkR, hk⟩
  · intro a ha b hb
    exact ha.tail (by rw [hrel]; exact hb)

end PathChaining

/-! ### A finite chart-ball cover of a compact set (first brick of the general position)

`exists_finite_chartBall_cover` produces, for a compact `K` and a point `x₀`, a finite family of
chart balls with room covering `K ∪ {x₀}`; its members are centred at the points of the cover, so
each point of `K ∪ {x₀}` lies in the *interior* of one of them
(`chartBall_subset_interior_chartClosedBall`).  This is step one of the general-position construction
of `NOTES_region_with_sector_boundary_STATUS.md` §BF.6, on which the sector condition at the frontier
of the engulfing region rests. -/
section FiniteChartBallCover

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- **A chart ball with room around any point.** -/
theorem exists_radius_chartAt (x : Y) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target := by
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp
    ((chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))
  exact ⟨ρ / 2, half_pos hρ, (Metric.closedBall_subset_ball (by linarith)).trans hsub⟩

/-- A chart ball lies in the interior of the corresponding closed chart ball. -/
theorem chartBall_subset_interior_chartClosedBall (c : OpenPartialHomeomorph Y ℂ) (a : ℂ) (ρ : ℝ) :
    Submission.chartBall c a ρ ⊆ interior (Submission.chartClosedBall c a ρ) :=
  interior_maximal (fun _ hy => by
    obtain ⟨hysrc, hyb⟩ := Submission.mem_chartBall.mp hy
    exact Submission.mem_chartClosedBall.mpr ⟨hysrc, Metric.ball_subset_closedBall hyb⟩)
    (Submission.chartBall_isOpen c a ρ)

/-- **A finite family of chart balls with room covering `K ∪ {x₀}`.** -/
theorem exists_finite_chartBall_cover {K : Set Y} (hK : IsCompact K) (x₀ : Y) :
    ∃ (ρ : Y → ℝ) (t : Finset ↥(K ∪ {x₀})),
      (∀ x, 0 < ρ x) ∧ (∀ x, Metric.closedBall ((chartAt ℂ x) x) (ρ x) ⊆ (chartAt ℂ x).target) ∧
      K ∪ {x₀} ⊆ ⋃ y ∈ t, Submission.chartBall (chartAt ℂ (y : Y)) ((chartAt ℂ (y : Y)) (y : Y))
        (ρ (y : Y)) := by
  classical
  choose ρ hρ hsub using exists_radius_chartAt (Y := Y)
  have hKc : IsCompact (K ∪ {x₀}) := hK.union isCompact_singleton
  have hcov : K ∪ {x₀} ⊆ ⋃ (y : ↥(K ∪ {x₀})),
      Submission.chartBall (chartAt ℂ (y : Y)) ((chartAt ℂ (y : Y)) (y : Y)) (ρ (y : Y)) := by
    rintro z hz
    refine mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
    refine Submission.mem_chartBall.mpr ⟨mem_chart_source ℂ z, ?_⟩
    simp only [Metric.mem_ball, dist_self]
    exact hρ z
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover
    (fun y : ↥(K ∪ {x₀}) =>
      Submission.chartBall (chartAt ℂ (y : Y)) ((chartAt ℂ (y : Y)) (y : Y)) (ρ (y : Y)))
    (fun y => Submission.chartBall_isOpen _ _ _) hcov
  exact ⟨ρ, t, hρ, hsub, fun z hz => by
    obtain ⟨y, hyt, hyz⟩ := Set.mem_iUnion₂.mp (ht hz)
    exact Set.mem_iUnion₂.mpr ⟨y, hyt, hyz⟩⟩

/-- **A finite family of chart balls with room covering `K ∪ {x₀}`, indexed by `Fin n`.**

This is the `Fin`-indexed form of `exists_finite_chartBall_cover`, obtained through
`Finset.equivFin`; it is the shape consumed by the general-position statement (step two of §BF.6). -/
theorem exists_finite_chartBall_cover_fin {K : Set Y} (hK : IsCompact K) (x₀ : Y) :
    ∃ (n : ℕ) (_ : 0 < n) (cc : Fin n → OpenPartialHomeomorph Y ℂ) (a : Fin n → ℂ)
      (r : Fin n → ℝ),
      (∀ i, cc i ∈ atlas ℂ Y) ∧ (∀ i, 0 < r i) ∧
      (∀ i, Metric.closedBall (a i) (r i) ⊆ (cc i).target) ∧
      K ∪ {x₀} ⊆ ⋃ i, Submission.chartBall (cc i) (a i) (r i) := by
  classical
  obtain ⟨ρ, t, hρ, hsub, hcov⟩ := exists_finite_chartBall_cover (Y := Y) hK x₀
  have htne : t.Nonempty := by
    obtain ⟨z, hz⟩ : (K ∪ {x₀}).Nonempty := ⟨x₀, Or.inr rfl⟩
    obtain ⟨y, hy't, -⟩ := Set.mem_iUnion₂.mp (hcov hz)
    exact ⟨y, hy't⟩
  let pt : Fin t.card → ↥(K ∪ {x₀}) := fun i => ((t.equivFin.symm i : t) : ↥(K ∪ {x₀}))
  refine ⟨t.card, Finset.card_pos.mpr htne, fun i => chartAt ℂ (pt i : Y),
    fun i => (chartAt ℂ (pt i : Y)) (pt i : Y), fun i => ρ (pt i : Y), ?_, ?_, ?_, ?_⟩
  · exact fun i => chart_mem_atlas ℂ (pt i : Y)
  · exact fun i => hρ (pt i : Y)
  · exact fun i => hsub (pt i : Y)
  · intro z hz
    obtain ⟨y, hy't, hyz⟩ := Set.mem_iUnion₂.mp (hcov hz)
    refine Set.mem_iUnion.mpr ⟨t.equivFin ⟨y, hy't⟩, ?_⟩
    simpa only [pt, Equiv.symm_apply_apply] using hyz

end FiniteChartBallCover

/-- **The target: every compact subset of a simply connected non-compact Riemann surface lies in a
relatively compact, simply connected region with sector boundary.**

The proof splits on whether `X` carries a weak Green function.  In the *hyperbolic* case the
uniformization dichotomy holds by the verified hyperbolic branch
(`region_with_sector_boundary_of_weakGreen`).  In the *parabolic* case, the classical input needed is
that `X` is biholomorphic to `ℂ` (equivalently: that every non-compact simply connected Riemann
surface embeds holomorphically into `ℂ`, the ABS/Anghel--Bruin--Stan embedding theorem, whose
parabolic case is Mori's normal-form theorem); with it, `region_with_sector_boundary_of_plane`
concludes.  That input is the single remaining gap of this file. -/
theorem region_with_sector_boundary {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [SimplyConnectedSpace X]
    (hX : ¬ CompactSpace X) (K : Set X) (hK : IsCompact K) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  by_cases h : ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt z₀ E
  · -- hyperbolic case: the holomorphic modulus of the Green function gives the dichotomy
    obtain ⟨z₀, E, hE⟩ := h
    obtain ⟨Φ, hΦ, hpole, hmod⟩ :=
      Work.Modulus.exists_holomorphic_modulus_of_unitGreenFunction_of_simplyConnected
        (X := X) (z₀ := z₀) hE
    exact region_with_sector_boundary_of_dichotomy (X := X) hX
      (Work.Parabolic.uniformization_of_greenFunctionAt (X := X) hX hE.1 hΦ hmod hpole) K hK
  · -- The parabolic case.  The remaining classical input is the ABS embedding theorem: a
    -- simply connected non-compact Riemann surface admits an injective holomorphic function into
    -- `ℂ`; with it `Work.Parabolic.plane_of_no_greenFunction` gives `X ≅ ℂ` and the plane case
    -- concludes (see `region_with_sector_boundary_of_parabolic_of_injective`).
    -- Delegated: `Work.SimplyConnected.ABS.region_with_sector_boundary_parabolic`.
    sorry

/-- **Additive characters of a simply connected space vanish.** -/
theorem subsingleton_characters_of_simplyConnected {Y : Type*} [TopologicalSpace Y]
    [SimplyConnectedSpace Y] (y : Y) :
    Subsingleton (Additive (FundamentalGroup Y y) →+ ℝ) :=
  ⟨fun f g => AddMonoidHom.ext fun a => by
    have h : a = 0 := Subsingleton.elim a 0
    rw [h, map_zero f, map_zero g]⟩

/-- **The parabolic case, from the ABS input.**  If `X` is parabolic and admits an injective
holomorphic function into `ℂ` (the ABS / Anghel--Bruin--Stan embedding input), then `X` is
biholomorphic to `ℂ` (`Work.Parabolic.plane_of_no_greenFunction`), whence the conclusion by the
plane case. -/
theorem region_with_sector_boundary_of_parabolic_of_injective (hX : ¬ CompactSpace X)
    (hpar : Work.Parabolic.IsParabolic X)
    {φ : X → ℂ} (hφ : Submission.HolomorphicOnX φ Set.univ) (hinj : Function.Injective φ)
    (K : Set X) (hK : IsCompact K) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  obtain ⟨x⟩ : Nonempty X := ConnectedSpace.toNonempty
  haveI : Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) :=
    subsingleton_characters_of_simplyConnected x
  obtain ⟨e⟩ := Work.Parabolic.plane_of_no_greenFunction (X := X) hX x hpar hφ hinj
  exact region_with_sector_boundary_of_plane (X := X) hX e K hK

/-- **The conclusion from the ABS disc-exhaustion data.**  If `X` admits an exhaustion by discs in
the normalised sense of `Work.SC.HasDiscExhaustion` (ABS Theorems 12 and 10) and the normal-family
bound `Work.SC.UniformBoundAt`, then the uniformization dichotomy holds
(`Work.SC.uniformization_of_simplyConnected_of_discExhaustion`, verified), whence the conclusion.

This records the exact interface: the conclusion of this file follows from the ABS data, and
`Work.SC.HasDiscExhaustion` is what the engulfing (`regularPiece_core`) plus the disc lemma produce.
-/
theorem region_with_sector_boundary_of_hasDiscExhaustion [SimplyConnectedSpace X]
    (hX : ¬ CompactSpace X) {x₀ : X} (hU : Work.SC.UniformBoundAt (X := X) x₀)
    (h : Work.SC.HasDiscExhaustion (X := X) x₀) (K : Set X) (hK : IsCompact K) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p :=
  region_with_sector_boundary_of_dichotomy (X := X) hX
    (Work.SC.uniformization_of_simplyConnected_of_discExhaustion (X := X) hX hU h) K hK


/-! ## The sharp reduction: the target from a Green function with a holomorphic modulus

The ABS disc lemma (Hubbard, *Teichmüller theory* Vol. 1, Chapter 1, the "disc" theorem `olomxn`;
Anghel--Bruin--Stan, arXiv:2008.12189 item (10)) says: a relatively compact domain `W` of a Riemann
surface, carrying a Green function `E` with pole `x₀` together with a *holomorphic modulus* `Φ` of `E`
(so that `W` is biholomorphic to a round disc via `Φ`), contains for every compact `K ⊆ W` a *regular
piece* `U`: open, homeomorphic to the open unit disc (hence simply connected), with compact closure
and the cone (sector) condition at every frontier point.

That statement is landed, axiom-clean, in
`Work.SimplyConnected.ABS.exists_regularPiece_of_greenOn_modulus`, so the target reduces to producing
the analytic datum `(W, x₀, E, Φ)`.  This section records that reduction, and the further reduction of
the datum to a region with the *cone condition* plus the modulus obligation. -/

/-- **The target from a Green function with a holomorphic modulus on a region containing `K`.**

If `W` is open, `≠ univ`, with compact closure, `x₀ ∈ W`, `E` is the Green function of `W` with pole
`x₀`, `Φ` is a holomorphic modulus of `E` on `W`, and `K ⊆ W` is compact, then `K` lies in a regular
piece `U ⊆ W`: `U` is open, homeomorphic to the open unit disc, has compact closure, is `≠ univ`, and
satisfies the sector condition at every frontier point.

The two remaining obligations of the parabolic case are therefore exactly (a) the *existence* of such
a region `W ⊇ K` (with a Green function, i.e. a regular enough boundary: the cone condition suffices,
`Work.SimplyConnected.ABS.isGreenOn_of_sectorRegion`) and (b) the *modulus* `Φ`
(`Work.SimplyConnected.ABS.IsModulusOn`). -/
theorem region_with_sector_boundary_of_greenOn_modulus (hX : ¬ CompactSpace X) {K : Set X}
    {W : Set X} {x₀ : X} {E : X → ℝ} {Φ : X → ℂ}
    (hWo : IsOpen W) (hWne : W ≠ Set.univ) (hcomp : IsCompact (closure W)) (hx₀ : x₀ ∈ W)
    (hE : Work.SimplyConnected.ABS.IsGreenOn W x₀ E)
    (hΦ : Work.SimplyConnected.ABS.IsModulusOn W x₀ E Φ)
    (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  obtain ⟨U, hUo, hhomeo, hUcomp, -, hKU, hsect⟩ :=
    Work.SimplyConnected.ABS.exists_regularPiece_of_greenOn_modulus (X := X) hX hWo hWne hcomp
      hx₀ hE hΦ hK hKW
  exact ⟨U, hUo, hKU, hUcomp, ne_univ_of_isCompact_closure hX hUcomp,
    simplyConnectedSpace_of_homeomorph_ball hhomeo, hsect⟩

/-- **The target from a *simply connected* relatively compact region with the cone condition.**

This is the sharpest form of the reduction reached: a single geometric input — an open, connected,
relatively compact `W ⊇ K` with `W ≠ univ` and the cone (sector) condition at every frontier point,
which is moreover *simply connected* — closes the target, using only axiom-clean material:

* `Work.SimplyConnected.ABS.isGreenOn_of_sectorRegion` (Perron/balayage: the cone condition gives
  the Green function of `W`, pole any `x₀ ∈ W`);
* `Work.SimplyConnected.ABS.exists_isModulusOn_of_isGreenOn` (the monodromy argument: on a *simply
  connected* domain the Green function has a holomorphic modulus — the conjugate periods are
  automatically trivial);
* `Work.SimplyConnected.ABS.exists_regularPiece_of_greenOn_modulus` (the ABS disc lemma: a Green
  function with a modulus on `W` produces a sub-region `U ⊆ W`, homeomorphic to the open unit disc,
  with compact closure and the sector condition on its frontier).

The *simplicity* of `W` is essential and cannot be replaced by the simple connectivity of the
ambient `X`: an annulus in `ℂ` is an open subset of a simply connected surface carrying a Green
function, but no holomorphic modulus (a modulus would make it biholomorphic to a disc, and moreover
the conjugate period around the hole is not a multiple of `2π`).  So the geometric input above is
exactly the residual obligation, and it is *independent of the Green-function/parabolic analysis*. -/
theorem region_with_sector_boundary_of_sectorRegion [SimplyConnectedSpace X]
    (hX : ¬ CompactSpace X) (K : Set X) (hK : IsCompact K)
    (h : ∃ (W : Set X) (x₀ : X), IsOpen W ∧ IsConnected W ∧ W ≠ Set.univ ∧
      IsCompact (closure W) ∧ x₀ ∈ W ∧ K ⊆ W ∧ SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  obtain ⟨W, x₀, hWo, hWc, hWne, hcomp, hx₀, hKW, hWsc, hsect⟩ := h
  obtain ⟨E, hE⟩ :=
    Work.SimplyConnected.ABS.isGreenOn_of_sectorRegion (X := X) hWo hWc hWne hcomp hx₀ hsect
  obtain ⟨Φ, hΦ⟩ :=
    Work.SimplyConnected.ABS.exists_isModulusOn_of_isGreenOn (X := X) (Ω := W) hWo hWsc hx₀ hE
  exact region_with_sector_boundary_of_greenOn_modulus (X := X) hX hWo hWne hcomp hx₀ hE hΦ hK hKW

/-- **The target from a region with the cone condition, given the modulus obligation.**

A relatively compact connected non-total open region `W ⊇ K` with the cone condition at every frontier
point automatically carries a Green function with any prescribed pole `x₀ ∈ W`
(`Work.SimplyConnected.ABS.isGreenOn_of_sectorRegion`, proved from the ABS balayage/Perron
construction — axiom-clean); it remains to produce the holomorphic modulus of that Green function.
The hypothesis `hmod` is *exactly* the modulus obligation. -/
theorem region_with_sector_boundary_of_sectorRegion_and_modulus (hX : ¬ CompactSpace X) (K : Set X)
    (hK : IsCompact K)
    (h : ∃ (W : Set X) (x₀ : X), IsOpen W ∧ IsConnected W ∧ W ≠ Set.univ ∧
      IsCompact (closure W) ∧ x₀ ∈ W ∧ K ⊆ W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p)
    (hmod : ∀ (W : Set X) (x₀ : X) (E : X → ℝ), IsOpen W → x₀ ∈ W →
      Work.SimplyConnected.ABS.IsGreenOn W x₀ E →
      ∃ Φ : X → ℂ, Work.SimplyConnected.ABS.IsModulusOn W x₀ E Φ) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  obtain ⟨W, x₀, hWo, hWc, hWne, hcomp, hx₀, hKW, hsect⟩ := h
  obtain ⟨E, hE⟩ :=
    Work.SimplyConnected.ABS.isGreenOn_of_sectorRegion (X := X) hWo hWc hWne hcomp hx₀ hsect
  obtain ⟨Φ, hΦ⟩ := hmod W x₀ E hWo hx₀ hE
  exact region_with_sector_boundary_of_greenOn_modulus (X := X) hX hWo hWne hcomp hx₀ hE hΦ hK hKW

/-! ## A verified step of the "filling" construction

The parabolic case of the target is proved (in the complete argument) by taking a finite union `V`
of chart balls containing `K`, and putting `W := V ∪ {relatively compact components of `X \ V`}`.
The lemma below is the elementary half of that construction: the sector condition is inherited by any
set contained in the closure of a region satisfying it, because the *avoided* sector is open. -/

section Filling

/-- **The sector condition is inherited by subsets of the closure.**  If `V` satisfies
`HasSectorBoundary` at `p` and `W ⊆ closure V`, then so does `W`.  The avoided sector is an open set
disjoint from `V`, hence disjoint from `closure V ⊇ W`. -/
theorem hasSectorBoundary_of_subset_closure {W V : Set X} {p : X}
    (hWV : W ⊆ closure V) (h : Work.SimplyConnected.ABS.HasSectorBoundary V p) :
    Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  obtain ⟨c, V₀, L₁, L₂, hc, hV₀o, hpV₀, hV₀c, hpsrc, hL₁, hL₂, hw, havoid⟩ := h
  refine ⟨c, V₀, L₁, L₂, hc, hV₀o, hpV₀, hV₀c, hpsrc, hL₁, hL₂, hw, ?_⟩
  intro x hx
  rintro ⟨h1, h2⟩
  have hxsrc : x ∈ c.source := hV₀c hx.2
  -- the sector (two strict inequalities in the chart) is open inside the chart source
  have h1c : ContinuousOn (fun y : X => L₁ (c y - c p)) c.source := by
    have h' : ContinuousOn (fun y : X => L₁ (c y)) c.source :=
      L₁.continuous.comp_continuousOn c.continuousOn_toFun
    have h'' : ContinuousOn (fun y : X => L₁ (c y) - L₁ (c p)) c.source :=
      h'.sub continuousOn_const
    simpa only [map_sub] using h''
  have h2c : ContinuousOn (fun y : X => L₂ (c y - c p)) c.source := by
    have h' : ContinuousOn (fun y : X => L₂ (c y)) c.source :=
      L₂.continuous.comp_continuousOn c.continuousOn_toFun
    have h'' : ContinuousOn (fun y : X => L₂ (c y) - L₂ (c p)) c.source :=
      h'.sub continuousOn_const
    simpa only [map_sub] using h''
  have hpre1 : IsOpen (c.source ∩ (fun y : X => L₁ (c y - c p)) ⁻¹' Set.Ioi (0 : ℝ)) :=
    h1c.isOpen_inter_preimage c.open_source isOpen_Ioi
  have hpre2 : IsOpen (c.source ∩ (fun y : X => L₂ (c y - c p)) ⁻¹' Set.Ioi (0 : ℝ)) :=
    h2c.isOpen_inter_preimage c.open_source isOpen_Ioi
  have hsplit : c.source ∩ {y : X | 0 < L₁ (c y - c p) ∧ 0 < L₂ (c y - c p)}
      = (c.source ∩ (fun y : X => L₁ (c y - c p)) ⁻¹' Set.Ioi (0 : ℝ))
        ∩ (c.source ∩ (fun y : X => L₂ (c y - c p)) ⁻¹' Set.Ioi (0 : ℝ)) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq]
    tauto
  have hAopen : IsOpen (V₀ ∩ (c.source ∩
      {y : X | 0 < L₁ (c y - c p) ∧ 0 < L₂ (c y - c p)})) := by
    rw [hsplit]
    exact hV₀o.inter (hpre1.inter hpre2)
  have hxmem : x ∈ V₀ ∩ (c.source ∩
      {y : X | 0 < L₁ (c y - c p) ∧ 0 < L₂ (c y - c p)}) :=
    ⟨hx.2, hxsrc, h1, h2⟩
  -- that neighbourhood is disjoint from `V`
  have hdisj : ∀ y ∈ V₀ ∩ (c.source ∩
      {y : X | 0 < L₁ (c y - c p) ∧ 0 < L₂ (c y - c p)}), y ∉ V := by
    intro y hy hyV
    exact havoid y ⟨hyV, hy.1⟩ ⟨hy.2.2.1, hy.2.2.2⟩
  have hsub : V ⊆ (V₀ ∩ (c.source ∩
      {y : X | 0 < L₁ (c y - c p) ∧ 0 < L₂ (c y - c p)}))ᶜ :=
    fun y hy hyS => hdisj y hyS hy
  have hcl : closure V ⊆ (V₀ ∩ (c.source ∩
      {y : X | 0 < L₁ (c y - c p) ∧ 0 < L₂ (c y - c p)}))ᶜ :=
    (isClosed_compl_iff.mpr hAopen).closure_subset_iff.mpr hsub
  exact hcl (hWV hx.1) hxmem

/-- **The sector condition is inherited by subsets of the closure, locally.**

If `W` agrees, near `p`, with a subset of `closure V`, and `V` satisfies the sector condition at `p`,
then so does `W`.  This is the local form of `hasSectorBoundary_of_subset_closure` and it is the shape
the ABS *filling* construction needs: the region is a component (or the filling) of the interior of a
union of chart balls, and at a frontier point `p` it is contained in the closure of the union near
`p`, while the union itself carries the sector condition (for a multi-chart family of chart balls:
`Work.Topology.Surface.sectorCondition_chartBallUnion_multiChart`). -/
theorem hasSectorBoundary_of_subset_closure_of_nhds {W V V₀ : Set X} {p : X}
    (hV₀o : IsOpen V₀) (hpV₀ : p ∈ V₀) (hWV : W ∩ V₀ ⊆ closure V)
    (h : Work.SimplyConnected.ABS.HasSectorBoundary V p) :
    Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  set W' : Set X := (W ∩ V₀) ∪ (closure V ∩ V₀ᶜ) with hW'
  have hW'sub : W' ⊆ closure V := by
    rw [hW']
    rintro x (hx | hx)
    · exact hWV hx
    · exact hx.1
  have h1 : Work.SimplyConnected.ABS.HasSectorBoundary W' p :=
    hasSectorBoundary_of_subset_closure hW'sub h
  have heq : W ∩ V₀ = W' ∩ V₀ := by
    rw [hW']
    ext x
    constructor
    · intro hx
      exact ⟨Or.inl hx, hx.2⟩
    · rintro ⟨hx | hx, hxV₀⟩
      · exact hx
      · exact absurd hxV₀ hx.2
  exact hasSectorBoundary_of_inter_eq hV₀o hpV₀ heq h1

/-- The **filling** of an open set `V` with respect to a topological space `X`: `V` together with
all points whose component in `X \ V` has compact closure. -/
def filling (V : Set X) : Set X :=
  V ∪ {x : X | IsCompact (closure (connectedComponentIn Vᶜ x))}

/-- **The filling is the complement of the union of the non-relatively-compact components.** -/
theorem compl_filling {V : Set X} :
    (filling V)ᶜ = {x : X | ¬ IsCompact (closure (connectedComponentIn Vᶜ x))} := by
  ext x
  rw [Set.mem_compl_iff, filling, Set.mem_union, not_or]
  constructor
  · rintro ⟨-, hx⟩
    exact hx
  · intro hx
    refine ⟨fun hxV => ?_, hx⟩
    have hxV' : x ∉ Vᶜ := by simpa using hxV
    refine hx ?_
    rw [connectedComponentIn_eq_empty hxV', closure_empty]
    exact isCompact_empty

/-- **The filling of an open set is open as soon as the union of the non-relatively-compact
components of its complement is closed.**

This is the elementary half of the ABS "filling" step: filling `V` by the relatively compact
components of its complement preserves openness whenever the *other* components do not accumulate
onto the filled set — for instance when there is just one such component
(`filling_eq_self_of_isPreconnected` below). -/
theorem isOpen_filling {V : Set X} (hV : IsOpen V)
    (hclosed : IsClosed {x : X | ¬ IsCompact (closure (connectedComponentIn Vᶜ x))}) :
    IsOpen (filling V) := by
  have h := hclosed.isOpen_compl
  have heq : filling V = ({x : X | ¬ IsCompact (closure (connectedComponentIn Vᶜ x))})ᶜ := by
    rw [← compl_compl (filling V), compl_filling]
  rw [heq]
  exact h

/-- If the complement of `V` is preconnected and not compact, then it has a single component and the
filling of `V` is `V` itself. -/
theorem filling_eq_self_of_isPreconnected {V : Set X} (hV : IsOpen V)
    (hconn : IsPreconnected Vᶜ) (hne : ¬ IsCompact Vᶜ) : filling V = V := by
  have hcomp : ∀ x, x ∈ Vᶜ → connectedComponentIn Vᶜ x = Vᶜ := fun x hx =>
    Set.Subset.antisymm (connectedComponentIn_subset _ _)
      (hconn.subset_connectedComponentIn hx subset_rfl)
  have hset : {x : X | IsCompact (closure (connectedComponentIn Vᶜ x))} = V := by
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hy
      by_contra hyV
      have hyV' : y ∈ Vᶜ := by simpa using hyV
      rw [show connectedComponentIn Vᶜ y = Vᶜ from hcomp y hyV'] at hy
      refine hne (by rwa [hV.isClosed_compl.closure_eq] at hy)
    · intro hyV
      have hyV' : y ∉ Vᶜ := by simpa using hyV
      rw [connectedComponentIn_eq_empty hyV', closure_empty]
      exact isCompact_empty
  rw [filling, hset, Set.union_self]

/-- **The target from an engulfing region that is a union of chart balls.**  This is the interface
through which the ABS engulfing (this file's `regularPiece_core` target; the fleet's
`Work.SimplyConnected.ABS.exists_simplyConnected_region_of_isCompact_of_parabolic`) discharges the
target: it suffices to produce a precompact simply connected region `V ⊇ K`, equal to a finite union
of chart balls in a single *atlas* chart, such that every frontier point of `V` lies in exactly one
of the corresponding closed balls.  The sector condition is then
`Work.SimplyConnected.ABS.hasSectorBoundary_iUnion_chartBall_of_unique` (verified), and all the other
requirements are hypotheses. -/
theorem region_with_sector_boundary_of_chartBallUnion {K V : Set X}
    (hVo : IsOpen V) (hKV : K ⊆ V) (hcomp : IsCompact (closure V)) (hVne : V ≠ Set.univ)
    (hsc : SimplyConnectedSpace ↥V)
    {c : OpenPartialHomeomorph X ℂ} (hc : c ∈ atlas ℂ X) {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℂ) (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hsub : ∀ i, Metric.closedBall (a i) (ρ i) ⊆ c.target)
    (hV : V = ⋃ i, Submission.chartBall c (a i) (ρ i))
    (huniq : ∀ p ∈ frontier V, ∃ i₀, c p ∈ Metric.closedBall (a i₀) (ρ i₀) ∧
      ∀ i, i ≠ i₀ → c p ∉ Metric.closedBall (a i) (ρ i)) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  refine ⟨V, hVo, hKV, hcomp, hVne, hsc, fun p hp => ?_⟩
  obtain ⟨i₀, hmem, haway⟩ := huniq p hp
  have h := hasSectorBoundary_iUnion_chartBall_of_unique (X := X) hc a ρ hρ hsub
    (i₀ := i₀) (by rw [← hV]; exact hp) hmem haway
  rwa [← hV] at h


/-! ## An ingredient of the two-chart-ball sector analysis

The sector condition at a frontier point of a union of chart balls is proved in
`Submission.Work.SimplyConnected.ABS.sectorCondition_of_chart_balls` in the case where the point lies in
exactly one closed ball, and, in the general-position case (at most two closed balls through each
point of `ℂ`), the alternative "sector *or* ray" is proved in
`Submission.Work.SimplyConnected.ABS.hasSectorBoundary_or_hasRayBoundary_of_two_chartBall`; the ray
case occurs exactly at an *external tangency* of two boundary circles, while a *transversal* crossing
gives the sector.  The lemma below is the elementary half-plane estimate behind that analysis: a disc
through the point `x₀` lies in the open half plane determined by the outward normal `x₀ - c`.  It is
stated separately so that the transversal-crossing refinement of
`region_with_sector_boundary_of_chartBallUnion` can reuse it. -/

open scoped ComplexConjugate in
/-- **A disc through `x₀` lies in an open half plane.**  If `x₀` is on the boundary circle of the
disc `ball c ρ`, then every point of the disc satisfies `Re (conj (x₀ - c) * (z - x₀)) < 0`, i.e. it
lies strictly on the side of `x₀` opposite to the outward normal `x₀ - c`. -/
theorem disc_re_neg {c x₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hd : dist x₀ c = ρ) :
    ∀ z, ‖z - c‖ < ρ → (conj (x₀ - c) * (z - x₀)).re < 0 := by
  intro z hz
  have hnorm : ‖x₀ - c‖ = ρ := by rwa [dist_eq_norm] at hd
  have hsq : conj (x₀ - c) * (x₀ - c) = ((ρ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul', hnorm]; push_cast; ring
  have hsplit : conj (x₀ - c) * (z - x₀)
      = conj (x₀ - c) * (z - c) - conj (x₀ - c) * (x₀ - c) := by ring
  rw [hsplit, hsq, Complex.sub_re, Complex.ofReal_re]
  have hb : |(conj (x₀ - c) * (z - c)).re| ≤ ρ * ‖z - c‖ := by
    have h1 := Complex.abs_re_le_norm (conj (x₀ - c) * (z - c))
    rwa [norm_mul, Complex.norm_conj, hnorm] at h1
  have h2 : (conj (x₀ - c) * (z - c)).re ≤ ρ * ‖z - c‖ := le_trans (le_abs_self _) hb
  have h3 : ρ * ‖z - c‖ < ρ ^ 2 := by
    have h4 := mul_lt_mul_of_pos_left hz hρ
    rwa [pow_two]
  linarith

open scoped ComplexConjugate in
/-- **The real part of `conj u * v` is symmetric in `u, v`** (the two are conjugate complex numbers,
which have the same real part). -/
theorem conj_mul_re_comm (u v : ℂ) : (conj u * v).re = (conj v * u).re := by
  have h3 : conj (conj u * v) = conj v * u := by rw [map_mul, Complex.conj_conj, mul_comm]
  rw [← Complex.conj_re (conj u * v), h3]

open scoped ComplexConjugate in
/-- **Two distinct half planes through the origin have a common open wedge.**  If `u` and `v` are
unit vectors with `u ≠ -v`, then there is `w` with `0 < Re (conj u * w)` and `0 < Re (conj v * w)`;
`w = u + v` works.  This is the *witness* in the definition of `HasSectorBoundary`, in the
transversal-crossing case of the two-chart-ball analysis. -/
theorem exists_wedge_witness_of_ne_neg {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : u ≠ -v) :
    ∃ w : ℂ, 0 < (conj u * w).re ∧ 0 < (conj v * w).re := by
  have hne : u + v ≠ 0 := by
    intro h
    apply huv
    have h' : u + v - v = 0 - v := by rw [h]
    simpa using h'
  have hkey : (conj u * u).re = 1 := by rw [Complex.conj_mul', hu]; norm_num
  have hkey' : (conj v * v).re = 1 := by rw [Complex.conj_mul', hv]; norm_num
  have hns : Complex.normSq (u + v) = 2 + 2 * (conj u * v).re := by
    rw [Complex.normSq_add u v, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hu, hv,
      Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.conj_re,
      Complex.conj_im]
    ring
  have hpos : 0 < Complex.normSq (u + v) := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hne) 2
  refine ⟨u + v, ?_, ?_⟩
  · have h1 : (conj u * (u + v)).re = 1 + (conj u * v).re := by
      rw [mul_add, Complex.add_re, hkey]
    rw [h1]; nlinarith [hpos, hns]
  · have h1 : (conj v * (u + v)).re = (conj v * u).re + 1 := by
      rw [mul_add, Complex.add_re, hkey']
    rw [h1, conj_mul_re_comm v u]
    nlinarith [hpos, hns]

/-! ## The general-position form of the interface

The hypothesis of `region_with_sector_boundary_of_chartBallUnion` above (each frontier point lies in
*exactly one* closed ball) is stronger than what the sector condition needs.  The following version
uses the honest general-position hypothesis — at most two closed balls through each point of `ℂ`, and
no external tangency at a frontier point — which is what a finite family of coordinate discs produced
by the ABS engulfing construction satisfies after an arbitrarily small perturbation.  It consumes the
verified `Work.Topology.Surface.sectorCondition_chartBallUnion_generalPosition`. -/

/-- **The target from an engulfing region that is a general-position union of chart balls.** -/
theorem region_with_sector_boundary_of_chartBallUnion_genPos {K V : Set X}
    (hVo : IsOpen V) (hKV : K ⊆ V) (hcomp : IsCompact (closure V)) (hVne : V ≠ Set.univ)
    (hsc : SimplyConnectedSpace ↥V)
    {c : OpenPartialHomeomorph X ℂ} (hc : c ∈ atlas ℂ X) {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℂ) (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hsub : ∀ i, Metric.closedBall (a i) (ρ i) ⊆ c.target)
    (hV : V = ⋃ i, Submission.chartBall c (a i) (ρ i))
    (htwo : ∀ z : ℂ, ({i | z ∈ Metric.closedBall (a i) (ρ i)} : Set ι).ncard ≤ 2)
    (hgood : ∀ p ∈ frontier V, ∀ i j, i ≠ j → c p ∈ Metric.closedBall (a i) (ρ i) →
      c p ∈ Metric.closedBall (a j) (ρ j) → (c p - a i) / ρ i ≠ -((c p - a j) / ρ j)) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  refine ⟨V, hVo, hKV, hcomp, hVne, hsc, fun p hp => ?_⟩
  have hgood' : ∀ q ∈ frontier (⋃ i, Submission.chartBall c (a i) (ρ i)), ∀ i j, i ≠ j →
      c q ∈ Metric.closedBall (a i) (ρ i) → c q ∈ Metric.closedBall (a j) (ρ j) →
      (c q - a i) / ρ i ≠ -((c q - a j) / ρ j) := by
    intro q hq i j hij hi hj
    have hqV : q ∈ frontier V := by rw [hV]; exact hq
    exact hgood q hqV i j hij hi hj
  have hpU : p ∈ frontier (⋃ i, Submission.chartBall c (a i) (ρ i)) := by simpa [hV] using hp
  have h := Work.Topology.Surface.sectorCondition_chartBallUnion_generalPosition
    (X := X) hc a ρ hρ hsub htwo hgood' p hpU
  rw [hV]
  exact h

/-- **The target from a *multi-chart* union of chart balls.**

This is the multi-chart form of `region_with_sector_boundary_of_chartBallUnion_genPos` above: the
region `V` is presented as a finite union of chart balls taken in *different* atlas charts `c i`,
which is the geometry that the ABS tiling and the fleet's engulfing construction actually produce
(`Work.Topology.Engulf.exists_finset_tiles_engulfing`, `Commons.Topology.Surface.exists_star_cover`).
The single-chart version forces the whole region into one chart, which is *equivalent* to planarity of
`X` (`NOTES_region_with_sector_boundary_STATUS.md`, §BQ.4 item 1); this version does not.

The two general-position hypotheses are the multi-chart ones:

* `htwo`: at most two *closed* chart balls contain each frontier point of `V`;
* `hgood`: no external tangency, expressed through the derivative `b` of the transition
  `c j ∘ (c i)⁻¹` at `(c i) p`: the two outward conormals -- the second transported by `b`, i.e.
  `w ↦ inner ℝ ((c j) p - a j) (b w)` -- are not opposite.

The sector half of the conclusion is the verified
`Work.Topology.Surface.sectorCondition_chartBallUnion_multiChart`; everything else is a hypothesis. -/
theorem region_with_sector_boundary_of_multiChartBallUnion_genPos {K V : Set X}
    (hVo : IsOpen V) (hKV : K ⊆ V) (hcomp : IsCompact (closure V)) (hVne : V ≠ Set.univ)
    (hsc : SimplyConnectedSpace ↥V)
    {ι : Type*} [Fintype ι] [Nonempty ι] (c : ι → OpenPartialHomeomorph X ℂ)
    (hc : ∀ i, c i ∈ atlas ℂ X) (a : ι → ℂ) (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hsub : ∀ i, Metric.closedBall (a i) (ρ i) ⊆ (c i).target)
    (hV : V = ⋃ i, Submission.chartBall (c i) (a i) (ρ i))
    (htwo : ∀ p ∈ frontier V,
      ({i | p ∈ Submission.chartClosedBall (c i) (a i) (ρ i)} : Set ι).ncard ≤ 2)
    (hgood : ∀ p ∈ frontier V, ∀ i j, i ≠ j →
      p ∈ Submission.chartClosedBall (c i) (a i) (ρ i) →
      p ∈ Submission.chartClosedBall (c j) (a j) (ρ j) →
      ∃ (b : ℂ →L[ℂ] ℂ), b ≠ 0 ∧
        HasFDerivAt (fun ζ : ℂ => c j ((c i).symm ζ)) b ((c i) p) ∧
        ∃ w : ℂ, 0 < inner ℝ ((c i) p - a i) w ∧ 0 < inner ℝ ((c j) p - a j) (b w)) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  have htwo' : ∀ q ∈ frontier (⋃ i, Submission.chartBall (c i) (a i) (ρ i)),
      ({i | q ∈ Submission.chartClosedBall (c i) (a i) (ρ i)} : Set ι).ncard ≤ 2 := by
    intro q hq
    exact htwo q (by rw [hV]; exact hq)
  have hgood' : ∀ q ∈ frontier (⋃ i, Submission.chartBall (c i) (a i) (ρ i)), ∀ i j, i ≠ j →
      q ∈ Submission.chartClosedBall (c i) (a i) (ρ i) →
      q ∈ Submission.chartClosedBall (c j) (a j) (ρ j) →
      ∃ (b : ℂ →L[ℂ] ℂ), b ≠ 0 ∧
        HasFDerivAt (fun ζ : ℂ => c j ((c i).symm ζ)) b ((c i) q) ∧
        ∃ w : ℂ, 0 < inner ℝ ((c i) q - a i) w ∧ 0 < inner ℝ ((c j) q - a j) (b w) := by
    intro q hq
    exact hgood q (by rw [hV]; exact hq)
  refine ⟨V, hVo, hKV, hcomp, hVne, hsc, fun p hp => ?_⟩
  rw [hV]
  exact Work.Topology.Surface.sectorCondition_chartBallUnion_multiChart c hc a ρ hρ hsub
    htwo' hgood' p (by rw [← hV]; exact hp)

/-- **The target from a region that is a *filling* of a multi-chart union of chart balls.**

This is the interface for the ABS filling construction (the fleet's tile-based engulfing,
`Work.Topology.Engulf.exists_finset_tiles_engulfing` plus the filling `filling` defined below): the
region `Ω` is *not* a union of chart balls -- it is a component of the interior of such a union, or
the filling of one -- so the sector condition cannot be read off from the union directly.  What is
needed, and what this theorem takes as hypotheses, is

* `hfront`: `frontier Ω` sits inside the frontier of the union (true for fillings and for components
  of the interior of a tiling), so that the sector condition of the *union*
  (`Work.Topology.Surface.sectorCondition_chartBallUnion_multiChart`, applied here) is available at
  every frontier point of `Ω`;
* `hlocal`: near each frontier point `p` the region is contained in the closure of the union, so that
  `hasSectorBoundary_of_subset_closure_of_nhds` transfers the sector condition from the union to `Ω`.

The simple connectivity of `Ω` remains a hypothesis (it is the crux of the parabolic branch). -/
theorem region_with_sector_boundary_of_filling_multiChartBallUnion {K Ω : Set X}
    (hΩo : IsOpen Ω) (hKΩ : K ⊆ Ω) (hΩcomp : IsCompact (closure Ω)) (hΩne : Ω ≠ Set.univ)
    (hΩsc : SimplyConnectedSpace ↥Ω)
    {ι : Type*} [Fintype ι] [Nonempty ι] (c : ι → OpenPartialHomeomorph X ℂ)
    (hc : ∀ i, c i ∈ atlas ℂ X) (a : ι → ℂ) (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hsub : ∀ i, Metric.closedBall (a i) (ρ i) ⊆ (c i).target)
    (htwo : ∀ p ∈ frontier (⋃ i, Submission.chartBall (c i) (a i) (ρ i)),
      ({i | p ∈ Submission.chartClosedBall (c i) (a i) (ρ i)} : Set ι).ncard ≤ 2)
    (hgood : ∀ p ∈ frontier (⋃ i, Submission.chartBall (c i) (a i) (ρ i)), ∀ i j, i ≠ j →
      p ∈ Submission.chartClosedBall (c i) (a i) (ρ i) →
      p ∈ Submission.chartClosedBall (c j) (a j) (ρ j) →
      ∃ (b : ℂ →L[ℂ] ℂ), b ≠ 0 ∧
        HasFDerivAt (fun ζ : ℂ => c j ((c i).symm ζ)) b ((c i) p) ∧
        ∃ w : ℂ, 0 < inner ℝ ((c i) p - a i) w ∧ 0 < inner ℝ ((c j) p - a j) (b w))
    (hfront : frontier Ω ⊆ frontier (⋃ i, Submission.chartBall (c i) (a i) (ρ i)))
    (hlocal : ∀ p ∈ frontier Ω, ∃ V₀ : Set X, IsOpen V₀ ∧ p ∈ V₀ ∧
      Ω ∩ V₀ ⊆ closure (⋃ i, Submission.chartBall (c i) (a i) (ρ i))) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  refine ⟨Ω, hΩo, hKΩ, hΩcomp, hΩne, hΩsc, fun p hp => ?_⟩
  obtain ⟨V₀, hV₀o, hpV₀, hV₀sub⟩ := hlocal p hp
  exact hasSectorBoundary_of_subset_closure_of_nhds hV₀o hpV₀ hV₀sub
    (Work.Topology.Surface.sectorCondition_chartBallUnion_multiChart c hc a ρ hρ hsub
      htwo hgood p (hfront hp))

/-! ### A local `omega` refinement (needed by the statement of the chain interface)

The chain interface below is stated with the *accumulated* union `⋃ i ∈ Finset.range (k + 1),
chartBall (c (L.get ⟨i, _⟩)) …`, and the natural proof that the index is `< L.length` is `omega`,
using the hypothesis `i ∈ Finset.range (k + 1)` introduced by the binder together with
`hk : k + 1 < L.length`.  `omega` does not preprocess `Finset`-membership hypotheses, so the
refinement below (the same device as in
`Work.SimplyConnected.ABS.simplyConnectedSpace_biUnion_list`) first rewrites them into `Nat`
comparisons.  The override is `local` and conservative: it tries the builtin `omega` first. -/
section OmegaRangeMembership

open Lean Elab Tactic in
/-- The builtin `omega` tactic, callable from inside a `macro_rules` override. -/
elab "omegaBuiltinRange" : tactic => do
  Lean.Elab.Tactic.Omega.evalOmega (← `(tactic| omega))

/-- `omega`, first rewriting `Finset`-membership hypotheses into `Nat` comparisons. -/
macro "omegaFinsetRange" : tactic =>
  `(tactic| first
      | omegaBuiltinRange
      | (simp only [Finset.mem_range, Finset.mem_singleton, Set.mem_Iio, Set.mem_Ici,
            Set.mem_Icc] at *
         omegaBuiltinRange))

local macro_rules | `(tactic| omega) => `(tactic| omegaFinsetRange)

/-- **The target from a *beading chain* of chart balls.**

The ABS engulfing construction (and the fleet's "beading" walk, `exists_chartBall_attach_of_inter_nonempty`
and `exists_chartBall_attach_avoiding` in this file) produces the region by *attaching* chart balls one
at a time along a connected piece.  This interface takes exactly that structure: a finite family of
chart balls in possibly different charts, an ordering `L` of its indices (the walk order,
`L.Nodup`, `∀ i, i ∈ L`), and the hypothesis that each ball meets the *accumulated* union of its
predecessors in a **path-connected** set.  The clause `SimplyConnectedSpace ↥V` is then *derived*
(from the landed `Work.SimplyConnected.ABS.simplyConnectedSpace_biUnion_list`), and the sector
condition comes from `Work.Topology.Surface.sectorCondition_chartBallUnion_multiChart`; so the
residual obligation here is purely the geometric one of *building* such a walk with the general
position conditions. -/
theorem region_with_sector_boundary_of_chartBallChain {K : Set X} {ι : Type*} [Fintype ι]
    [Nonempty ι] [DecidableEq ι] (hX : ¬ CompactSpace X)
    (c : ι → OpenPartialHomeomorph X ℂ) (hc : ∀ i, c i ∈ atlas ℂ X)
    (a : ι → ℂ) (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hsub : ∀ i, Metric.closedBall (a i) (ρ i) ⊆ (c i).target)
    (L : List ι) (hLnodup : L.Nodup) (hLall : ∀ i, i ∈ L)
    (hchain : ∀ (k : ℕ) (hk : k + 1 < L.length),
      PathConnectedSpace ↥((⋃ i ∈ Finset.range (k + 1),
          Submission.chartBall (c (L.get ⟨i, by omega⟩)) (a (L.get ⟨i, by omega⟩))
            (ρ (L.get ⟨i, by omega⟩))) ∩
        Submission.chartBall (c (L.get ⟨k + 1, hk⟩)) (a (L.get ⟨k + 1, hk⟩))
          (ρ (L.get ⟨k + 1, hk⟩))))
    (hK : K ⊆ ⋃ i, Submission.chartBall (c i) (a i) (ρ i))
    (hcomp : IsCompact (closure (⋃ i, Submission.chartBall (c i) (a i) (ρ i))))
    (htwo : ∀ p ∈ frontier (⋃ i, Submission.chartBall (c i) (a i) (ρ i)),
      ({i | p ∈ Submission.chartClosedBall (c i) (a i) (ρ i)} : Set ι).ncard ≤ 2)
    (hgood : ∀ p ∈ frontier (⋃ i, Submission.chartBall (c i) (a i) (ρ i)), ∀ i j, i ≠ j →
      p ∈ Submission.chartClosedBall (c i) (a i) (ρ i) →
      p ∈ Submission.chartClosedBall (c j) (a j) (ρ j) →
      ∃ (b : ℂ →L[ℂ] ℂ), b ≠ 0 ∧
        HasFDerivAt (fun ζ : ℂ => c j ((c i).symm ζ)) b ((c i) p) ∧
        ∃ w : ℂ, 0 < inner ℝ ((c i) p - a i) w ∧ 0 < inner ℝ ((c j) p - a j) (b w)) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  classical
  let B : ι → Set X := fun i => Submission.chartBall (c i) (a i) (ρ i)
  have hsc : SimplyConnectedSpace ↥(⋃ i, B i) := by
    have hBmem : ∀ i : ι, B i ∈ L.map B := fun i => List.mem_map.mpr ⟨i, hLall i, rfl⟩
    have hne : L.map B ≠ [] := by
      intro h
      obtain ⟨i⟩ := ‹Nonempty ι›
      exact List.not_mem_nil (h ▸ hBmem i)
    have h := Work.SimplyConnected.ABS.simplyConnectedSpace_biUnion_list (l := L.map B) hne
      (fun B' hB' => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hB'
        exact Submission.chartBall_isOpen (c i) (a i) (ρ i))
      (fun B' hB' => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hB'
        show SimplyConnectedSpace ↥(Submission.chartBall (c i) (a i) (ρ i))
        rw [Work.SimplyConnected.ABS.chartBall_eq_image (hsub i)]
        exact (Work.SimplyConnected.ABS.chartBall_transport (c i) (hρ i) (hsub i)).2.2.2.2.2.2)
      (fun k hk => by
        have hk' : k + 1 < L.length := by
          simpa [List.length_map] using hk
        have hU : (⋃ i ∈ Finset.range (k + 1), (L.map B).get ⟨i, by omega⟩)
            = ⋃ i ∈ Finset.range (k + 1), B (L.get ⟨i, by omega⟩) :=
          Set.iUnion₂_congr fun i _ => by
            rw [List.get_eq_getElem, List.getElem_map]
            rfl
        have hV : (L.map B).get ⟨k + 1, by omega⟩ = B (L.get ⟨k + 1, hk'⟩) := by
          rw [List.get_eq_getElem, List.getElem_map]
          rfl
        rw [hU, hV]
        exact hchain k hk')
    have hunion : (⋃ B' ∈ L.map B, B') = ⋃ i, B i := by
      ext x
      constructor
      · intro hx
        obtain ⟨B', hx1⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hB', hxB'⟩ := Set.mem_iUnion.mp hx1
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hB'
        exact Set.mem_iUnion.mpr ⟨i, hxB'⟩
      · intro hx
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨B i, Set.mem_iUnion.mpr ⟨hBmem i, hxi⟩⟩
    rwa [hunion] at h
  exact region_with_sector_boundary_of_multiChartBallUnion_genPos (K := K)
    (isOpen_iUnion fun i => Submission.chartBall_isOpen (c i) (a i) (ρ i)) hK hcomp
    (ne_univ_of_isCompact_closure hX hcomp) (by simpa only [B] using hsc) (c := c) hc a ρ hρ hsub
    rfl htwo hgood

end OmegaRangeMembership

/-! ## The sharpest interface: a single chart with room around `K`

The hypothesis of `region_with_sector_boundary_of_chartBallUnion_genPos` above is one *sufficient*
input, but there is a strictly weaker one, and it is the form in which the rest of the project
attacks the engulfing (`Work.SimplyConnected.ABS.exists_chart_with_room_locallyBiholomorphic`,
`Work.SimplyConnected.ABS.planarity_around_compact`):

> (`chart with room`) there is an atlas chart `φ`, a centre `a : ℂ` and a radius `ρ > 0` with
> `K ⊆ φ.source`, `φ '' K ⊆ Metric.ball a ρ` and `Metric.closedBall a ρ ⊆ φ.target`.

The corresponding region is simply the *single* chart ball `W := chartBall φ a ρ`: it is open, its
closure is compact (it is contained in the closed chart ball), it is homeomorphic to the Euclidean
ball (hence simply connected), and the sector condition at every frontier point is
`hasSectorBoundary_chartBall`.  In particular the whole content of the target below is the existence
of such a chart — the *planarity* of a neighbourhood of `K` — which is the shared crux of the
project (equivalently, by the uniformization theorem, `X ≃ ℂ` or `X ≃ ℍ`). -/

/-- **The target from a chart with room around `K`.**

Given an atlas chart `φ` whose image of `K` sits in a Euclidean ball `a, ρ` whose *closed* ball is
still inside `φ.target`, the chart ball `chartBall φ a ρ` is a witness for the target: it is open
(`chartBall_isOpen`), contains `K`, has compact closure (`closure_chartBall_subset_chartClosedBall`
inside the compact `chartClosedBall`), is not all of `X` (`ne_univ_of_isCompact_closure`),
is simply connected (homeomorphic to the Euclidean ball, `chartBall_transport`) and satisfies the
sector condition at every frontier point (`hasSectorBoundary_chartBall`). -/
theorem region_with_sector_boundary_of_chart_with_room (hX : ¬ CompactSpace X) {K : Set X}
    {c : OpenPartialHomeomorph X ℂ} (hc : c ∈ atlas ℂ X) {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hKsrc : K ⊆ c.source) (himg : c '' K ⊆ Metric.ball a ρ)
    (hroom : Metric.closedBall a ρ ⊆ c.target) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  refine ⟨Submission.chartBall c a ρ, Submission.chartBall_isOpen c a ρ, ?_, ?_, ?_, ?_,
    hasSectorBoundary_chartBall hc hρ hroom⟩
  · intro x hx
    exact Submission.mem_chartBall.mpr ⟨hKsrc hx, himg ⟨x, hx, rfl⟩⟩
  · exact (Submission.isCompact_chartClosedBall hroom).of_isClosed_subset isClosed_closure
      (Submission.closure_chartBall_subset_chartClosedBall hroom)
  · exact ne_univ_of_isCompact_closure hX
      ((Submission.isCompact_chartClosedBall hroom).of_isClosed_subset isClosed_closure
        (Submission.closure_chartBall_subset_chartClosedBall hroom))
  · rw [chartBall_eq_image hroom]
    exact (chartBall_transport c hρ hroom).2.2.2.2.2.2

/-! ## The sector condition at a frontier point of the *filling* of a union of chart balls

The lemmas of this final section reduce the target to the ABS engulfing construction in the exact
form the filling produces: for a finite union `V` of chart balls in one atlas chart, in general
position, the *filling* `W = filling V` automatically satisfies the sector condition at every
frontier point.  What remains for the engulfing is then only `IsOpen W`, `IsCompact (closure W)`,
`K ⊆ W` and `SimplyConnectedSpace ↥W`.
-/

set_option linter.unusedSectionVars false

/-- The real-linear functional `z ↦ Re (conj u * z)`. -/
def reConjCLM (u : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ (conj u))

@[simp] theorem reConjCLM_apply (u z : ℂ) : reConjCLM u z = (conj u * z).re := rfl

theorem reConjCLM_mul_self_re (u : ℂ) : (conj u * u).re = ‖u‖ ^ 2 := by
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem reConjCLM_ne_zero {u : ℂ} (hu : u ≠ 0) : reConjCLM u ≠ 0 := by
  intro h
  have h2 : reConjCLM u u = 0 := by rw [h]; rfl
  have h3 : reConjCLM u u = ‖u‖ ^ 2 := reConjCLM_mul_self_re u
  have hpos : (0:ℝ) < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu) 2
  rw [← h3, h2] at hpos
  exact lt_irrefl 0 hpos

/-- The real-linear functional of the exterior half-plane of a ball through `x₀`. -/
theorem disc_reConjCLM_neg {a x₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hd : dist x₀ a = ρ) :
    ∀ z ∈ Metric.ball a ρ, (conj (x₀ - a) * (z - x₀)).re < 0 := by
  intro z hz
  exact disc_re_neg hρ hd z (by rwa [Metric.mem_ball, Complex.dist_eq] at hz)


/-! ## The sector condition at a frontier point of the *filling* of a union of chart balls -/

section FillingSector

variable {c : OpenPartialHomeomorph X ℂ} {ι : Type*} [Fintype ι] [Nonempty ι]
  {a : ι → ℂ} {ρ : ι → ℝ}

/-- **The sector functionals at a frontier point of a general-position union of chart balls.**

Let `p` be a frontier point of `V = ⋃ i, chartBall c (a i) (ρ i)`, where at most two of the closed
balls `closedBall (a i) (ρ i)` contain `c p`, and no two of those that do are externally tangent.
Then there are non-zero real-linear functionals `L₁`, `L₂` spanning a non-degenerate sector which
*the whole of `V` avoids*: no point of any closed ball through `c p` satisfies both inequalities. -/
theorem exists_wedge_functionals_chartBallUnion
    (hc : c ∈ atlas ℂ X) {p : X} (hp : p ∈ frontier (⋃ i, Submission.chartBall c (a i) (ρ i)))
    (hρ : ∀ i, 0 < ρ i) (hsub : ∀ i, Metric.closedBall (a i) (ρ i) ⊆ c.target)
    (htwo : ∀ z : ℂ, ({i | z ∈ Metric.closedBall (a i) (ρ i)} : Set ι).ncard ≤ 2)
    (hgood : ∀ i j, i ≠ j → c p ∈ Metric.closedBall (a i) (ρ i) →
      c p ∈ Metric.closedBall (a j) (ρ j) → (c p - a i) / ρ i ≠ -((c p - a j) / ρ j)) :
    ∃ (L₁ L₂ : ℂ →L[ℝ] ℝ), L₁ ≠ 0 ∧ L₂ ≠ 0 ∧ (∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w) ∧
      ∀ i, c p ∈ Metric.closedBall (a i) (ρ i) → ∀ z ∈ Metric.ball (a i) (ρ i),
        ¬ (0 < L₁ (z - c p) ∧ 0 < L₂ (z - c p)) := by
  classical
  have hVopen : IsOpen (⋃ i, Submission.chartBall c (a i) (ρ i)) :=
    isOpen_iUnion fun i => Submission.chartBall_isOpen c (a i) (ρ i)
  have hpU : p ∉ (⋃ i, Submission.chartBall c (a i) (ρ i)) := by
    have h := hp
    rw [frontier, Set.mem_sdiff, IsOpen.interior_eq hVopen] at h
    exact h.2
  have hpcl : p ∈ ⋃ i, Submission.chartClosedBall c (a i) (ρ i) := by
    refine closure_minimal ?_ (isClosed_iUnion_of_finite fun i =>
      Submission.isClosed_chartClosedBall (hsub i)) hp.1
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i, Submission.chartBall_subset_chartClosedBall c (a i) (ρ i) hxi⟩
  have hpsrc : p ∈ c.source := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpcl
    exact Submission.chartClosedBall_subset_source c (a i) (ρ i) hi
  set T : Set ι := {i | c p ∈ Metric.closedBall (a i) (ρ i)} with hT
  have hTne : T.Nonempty := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpcl
    exact ⟨i, (Submission.mem_chartClosedBall.mp hi).2⟩
  have hTcard : T.ncard ≤ 2 := htwo (c p)
  have hcases : T.ncard = 1 ∨ T.ncard = 2 := by
    have hfin : T.Finite := Set.finite_univ.subset (Set.subset_univ T)
    have hpos : 0 < T.ncard := (Set.ncard_pos hfin).mpr hTne
    omega
  -- `c p` lies on the boundary circle of each closed ball through it
  have hsphere : ∀ i, i ∈ T → dist (c p) (a i) = ρ i := by
    intro i hiT
    refine le_antisymm (Metric.mem_closedBall.mp hiT) ?_
    by_contra hlt
    have : p ∈ (⋃ j, Submission.chartBall c (a j) (ρ j)) := by
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      exact Submission.mem_chartBall.mpr ⟨hpsrc, Metric.mem_ball.mpr (lt_of_not_ge hlt)⟩
    exact hpU this
  rcases hcases with h1 | h2
  · -- exactly one closed ball through `c p`
    obtain ⟨i₀, hi₀⟩ := Set.ncard_eq_one.mp h1
    have hmem₀ : c p ∈ Metric.closedBall (a i₀) (ρ i₀) := by
      have : i₀ ∈ T := by rw [hi₀]; exact Set.mem_singleton i₀
      exact this
    have hsp₀ : dist (c p) (a i₀) = ρ i₀ := hsphere i₀ hmem₀
    have hne₀ : c p - a i₀ ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rw [h, dist_self] at hsp₀
      exact (ne_of_gt (hρ i₀)) hsp₀.symm
    refine ⟨reConjCLM (c p - a i₀), reConjCLM (c p - a i₀), ?_, ?_, ?_, ?_⟩
    · exact reConjCLM_ne_zero hne₀
    · exact reConjCLM_ne_zero hne₀
    · refine ⟨c p - a i₀, ?_, ?_⟩
      · rw [reConjCLM_apply, reConjCLM_mul_self_re]; exact pow_pos (norm_pos_iff.mpr hne₀) 2
      · rw [reConjCLM_apply, reConjCLM_mul_self_re]; exact pow_pos (norm_pos_iff.mpr hne₀) 2
    · intro i hiT z hz hcon
      have hi : i = i₀ := by
        have : i ∈ T := hiT
        rw [hi₀, Set.mem_singleton_iff] at this
        exact this
      have hz' : z ∈ Metric.ball (a i₀) (ρ i₀) := by rw [hi] at hz; exact hz
      have hneg : (conj (c p - a i₀) * (z - c p)).re < 0 :=
        disc_reConjCLM_neg (hρ i₀) hsp₀ z hz'
      rw [reConjCLM_apply] at hcon
      linarith [hcon.1, hneg]
  · -- exactly two closed balls through `c p`
    obtain ⟨i₀, i₁, hne, hTeq⟩ := Set.ncard_eq_two.mp h2
    have hmem₀ : c p ∈ Metric.closedBall (a i₀) (ρ i₀) := by
      have : i₀ ∈ T := by rw [hTeq]; exact Set.mem_insert i₀ {i₁}
      exact this
    have hmem₁ : c p ∈ Metric.closedBall (a i₁) (ρ i₁) := by
      have : i₁ ∈ T := by
        rw [hTeq]; exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton i₁))
      exact this
    have hsp₀ : dist (c p) (a i₀) = ρ i₀ := hsphere i₀ hmem₀
    have hsp₁ : dist (c p) (a i₁) = ρ i₁ := hsphere i₁ hmem₁
    have hne₀ : c p - a i₀ ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rw [h, dist_self] at hsp₀
      exact (ne_of_gt (hρ i₀)) hsp₀.symm
    have hne₁ : c p - a i₁ ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rw [h, dist_self] at hsp₁
      exact (ne_of_gt (hρ i₁)) hsp₁.symm
    have hnorm₀ : ‖c p - a i₀‖ = ρ i₀ := by rw [← Complex.dist_eq]; exact hsp₀
    have hnorm₁ : ‖c p - a i₁‖ = ρ i₁ := by rw [← Complex.dist_eq]; exact hsp₁
    have hu : ‖(c p - a i₀) / ρ i₀‖ = 1 := by
      rw [div_eq_mul_inv, norm_mul, norm_inv, hnorm₀]
      have hρc : ‖((ρ i₀ : ℝ) : ℂ)‖ = ρ i₀ := by simp [abs_of_pos (hρ i₀)]
      rw [hρc, mul_inv_cancel₀ (ne_of_gt (hρ i₀))]
    have hv : ‖(c p - a i₁) / ρ i₁‖ = 1 := by
      rw [div_eq_mul_inv, norm_mul, norm_inv, hnorm₁]
      have hρc : ‖((ρ i₁ : ℝ) : ℂ)‖ = ρ i₁ := by simp [abs_of_pos (hρ i₁)]
      rw [hρc, mul_inv_cancel₀ (ne_of_gt (hρ i₁))]
    have hgood' : (c p - a i₀) / ρ i₀ ≠ -((c p - a i₁) / ρ i₁) :=
      hgood i₀ i₁ hne hmem₀ hmem₁
    obtain ⟨w, hw₁, hw₂⟩ := exists_wedge_witness_of_ne_neg hu hv hgood'
    have hρc₀ : ((ρ i₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hρ i₀)
    have hscal₀ : ((ρ i₀ : ℂ)) * ((c p - a i₀) / ρ i₀) = c p - a i₀ := by
      rw [div_eq_mul_inv, mul_comm (c p - a i₀) (↑(ρ i₀))⁻¹, ← mul_assoc, mul_inv_cancel₀ hρc₀,
        one_mul]
    have hconj₀ : conj (c p - a i₀) = ((ρ i₀ : ℝ) : ℂ) * conj ((c p - a i₀) / ρ i₀) := by
      conv_lhs => rw [← hscal₀]
      rw [map_mul, Complex.conj_ofReal]
    have hρc₁ : ((ρ i₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hρ i₁)
    have hscal₁ : ((ρ i₁ : ℂ)) * ((c p - a i₁) / ρ i₁) = c p - a i₁ := by
      rw [div_eq_mul_inv, mul_comm (c p - a i₁) (↑(ρ i₁))⁻¹, ← mul_assoc, mul_inv_cancel₀ hρc₁,
        one_mul]
    have hconj₁ : conj (c p - a i₁) = ((ρ i₁ : ℝ) : ℂ) * conj ((c p - a i₁) / ρ i₁) := by
      conv_lhs => rw [← hscal₁]
      rw [map_mul, Complex.conj_ofReal]
    refine ⟨reConjCLM (c p - a i₀), reConjCLM (c p - a i₁), ?_, ?_, ?_, ?_⟩
    · exact reConjCLM_ne_zero hne₀
    · exact reConjCLM_ne_zero hne₁
    · refine ⟨w, ?_, ?_⟩
      · rw [reConjCLM_apply, hconj₀, mul_assoc, Complex.re_ofReal_mul]
        exact mul_pos (hρ i₀) hw₁
      · rw [reConjCLM_apply, hconj₁, mul_assoc, Complex.re_ofReal_mul]
        exact mul_pos (hρ i₁) hw₂
    · intro i hiT z hz hcon
      have hi : i = i₀ ∨ i = i₁ := by
        have : i ∈ T := hiT
        rw [hTeq, Set.mem_insert_iff, Set.mem_singleton_iff] at this
        exact this
      rcases hi with h | h
      · have hz' : z ∈ Metric.ball (a i₀) (ρ i₀) := by rw [h] at hz; exact hz
        have hneg : (conj (c p - a i₀) * (z - c p)).re < 0 :=
          disc_reConjCLM_neg (hρ i₀) hsp₀ z hz'
        simp only [reConjCLM_apply] at hcon
        linarith [hcon.1, hneg]
      · have hz' : z ∈ Metric.ball (a i₁) (ρ i₁) := by rw [h] at hz; exact hz
        have hneg : (conj (c p - a i₁) * (z - c p)).re < 0 :=
          disc_reConjCLM_neg (hρ i₁) hsp₁ z hz'
        simp only [reConjCLM_apply] at hcon
        linarith [hcon.2, hneg]

end FillingSector



/-! ## The sector condition at a frontier point of the *filling* of a union of chart balls -/

set_option linter.unusedSectionVars false

section FillingSector

variable {c : OpenPartialHomeomorph X ℂ} {ι : Type*} [Fintype ι] [Nonempty ι]
  {a : ι → ℂ} {ρ : ι → ℝ}

/-- **The target's sector condition at a frontier point of the filling of a union of chart balls.**

Let `V = ⋃ i, chartBall c (a i) (ρ i)` be a finite union of chart balls in a single atlas chart,
at most two of whose closed balls contain any given point of `ℂ`, with no two of them externally
tangent at a frontier point of `V`.  Then the *filling* `W = filling V` satisfies the sector
condition at every one of its frontier points.

The point is that the filling only adds the relatively compact components of `Vᶜ`; at a frontier point
`p` of the filling, the component of `Vᶜ` containing `p` is therefore non-compact, hence entirely
inside `Wᶜ`, and the wedge of `exists_wedge_functionals_chartBallUnion` — which `V` avoids — is
contained in that component. -/
theorem hasSectorBoundary_filling_of_chartBallUnion
    (hc : c ∈ atlas ℂ X) (hρ : ∀ i, 0 < ρ i)
    (hsub : ∀ i, Metric.closedBall (a i) (ρ i) ⊆ c.target)
    (htwo : ∀ z : ℂ, ({i | z ∈ Metric.closedBall (a i) (ρ i)} : Set ι).ncard ≤ 2)
    (hgood : ∀ p ∈ frontier (⋃ i, Submission.chartBall c (a i) (ρ i)), ∀ i j, i ≠ j →
      c p ∈ Metric.closedBall (a i) (ρ i) → c p ∈ Metric.closedBall (a j) (ρ j) →
      (c p - a i) / ρ i ≠ -((c p - a j) / ρ j))
    (hWo : IsOpen (filling (⋃ i, Submission.chartBall c (a i) (ρ i)))) :
    ∀ p ∈ frontier (filling (⋃ i, Submission.chartBall c (a i) (ρ i))),
      HasSectorBoundary (filling (⋃ i, Submission.chartBall c (a i) (ρ i))) p := by
  classical
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  intro p hp
  set V : Set X := ⋃ i, Submission.chartBall c (a i) (ρ i) with hV
  have hVopen : IsOpen V := isOpen_iUnion fun i => Submission.chartBall_isOpen c (a i) (ρ i)
  have hpW : p ∉ filling V := by
    have h := hp
    rw [frontier, Set.mem_sdiff, IsOpen.interior_eq hWo] at h
    exact h.2
  have hpclW : p ∈ closure (filling V) := hp.1
  have hpVc : p ∉ V := fun h => hpW (by rw [filling]; exact Or.inl h)
  set Z : Set X := connectedComponentIn Vᶜ p with hZ
  have hpZ : p ∈ Z := mem_connectedComponentIn (by simpa using hpVc)
  have hZnc : ¬ IsCompact (closure Z) := by
    intro hcZ
    have hmem : p ∈ {x : X | IsCompact (closure (connectedComponentIn Vᶜ x))} := by
      show IsCompact (closure (connectedComponentIn Vᶜ p))
      rw [← hZ]
      exact hcZ
    exact hpW (by rw [filling]; exact Or.inr hmem)
  have hZW : Z ∩ filling V = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    intro x hx
    have hxV : x ∉ V := fun hxV =>
      (connectedComponentIn_subset Vᶜ p) hx.1 (by simpa using hxV)
    have hcomp : connectedComponentIn Vᶜ x = Z := by
      rw [← connectedComponentIn_eq (F := Vᶜ) hx.1, hZ]
    have hxm : x ∉ filling V := by
      rw [filling]
      rintro (h | h)
      · exact hxV h
      · have h2 : IsCompact (closure (connectedComponentIn Vᶜ x)) := h
        exact hZnc (by rwa [hcomp] at h2)
    exact hxm hx.2
  have hpclV : p ∈ closure V := by
    by_contra hcon
    have hcon' : p ∈ (closure V)ᶜ := by simpa using hcon
    set B : Set X := connectedComponentIn ((closure V)ᶜ) p with hB
    have hBopen : IsOpen B := isClosed_closure.isOpen_compl.connectedComponentIn
    have hpB : p ∈ B := mem_connectedComponentIn hcon'
    have hBpre : IsPreconnected B := (isConnected_connectedComponentIn_iff.mpr hcon').2
    have hBsub : B ⊆ (closure V)ᶜ := connectedComponentIn_subset _ _
    have hBVc : B ⊆ Vᶜ := fun x hx hxv => hBsub hx (subset_closure hxv)
    have hBZ : B ⊆ Z := IsPreconnected.subset_connectedComponentIn hBpre hpB hBVc
    obtain ⟨x, hx⟩ := (mem_closure_iff.mp hpclW B hBopen hpB)
    obtain ⟨hxB, hxW'⟩ := hx
    have hxV : x ∉ V := fun hxv => hBVc hxB hxv
    have hxZ : x ∈ Z := hBZ hxB
    have hxmem : x ∈ V ∨ IsCompact (closure (connectedComponentIn Vᶜ x)) := by
      have := hxW'; rw [filling] at this; exact this
    rcases hxmem with h | h
    · exact hxV h
    · refine hZnc ?_
      have h3 : connectedComponentIn Vᶜ x = Z := by
        rw [(connectedComponentIn_eq (F := Vᶜ) (x := p) (y := x)
          (by simpa [hZ] using hxZ)).symm]
      rwa [h3] at h
  have hpfV : p ∈ frontier V := by
    rw [frontier, IsOpen.interior_eq hVopen]
    exact ⟨hpclV, hpVc⟩
  have hpclClosed : p ∈ ⋃ i, Submission.chartClosedBall c (a i) (ρ i) :=
    closure_minimal (fun x hx => by
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨i, Submission.chartBall_subset_chartClosedBall c (a i) (ρ i) hxi⟩)
      (isClosed_iUnion_of_finite fun i => Submission.isClosed_chartClosedBall (hsub i)) hpclV
  have hpsrc : p ∈ c.source := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpclClosed
    exact Submission.chartClosedBall_subset_source c (a i) (ρ i) hi
  -- the sector functionals
  obtain ⟨L₁, L₂, hL₁, hL₂, ⟨w, hw₁, hw₂⟩, hsecT⟩ :=
    exists_wedge_functionals_chartBallUnion (X := X) (c := c) (a := a) (ρ := ρ) hc hpfV hρ hsub htwo
      (hgood p hpfV)
  -- the small chart ball around `p`, away from the closed balls not through `c p`
  obtain ⟨ε, hε, hεtgt, hεfar⟩ :
      ∃ ε : ℝ, 0 < ε ∧ Metric.ball (c p) ε ⊆ c.target ∧
        ∀ i : ι, c p ∉ Metric.closedBall (a i) (ρ i) → ∀ z : ℂ,
          z ∈ Metric.ball (c p) ε → z ∉ Metric.ball (a i) (ρ i) := by
    obtain ⟨ε₀, hε₀, hε₀sub⟩ :=
      Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source hpsrc))
    have hfin : ({i : ι | c p ∉ Metric.closedBall (a i) (ρ i)} : Set ι).Finite :=
      Set.finite_univ.subset (Set.subset_univ _)
    have hδ : ∀ i ∈ hfin.toFinset, 0 < dist (c p) (a i) - ρ i := by
      intro i hi
      have hi' : i ∈ ({i : ι | c p ∉ Metric.closedBall (a i) (ρ i)} : Set ι) :=
        hfin.mem_toFinset.mp hi
      have : ρ i < dist (c p) (a i) :=
        not_le.mp (fun h => hi' (Metric.mem_closedBall.mpr h))
      linarith
    set m : ℝ := if h : hfin.toFinset.Nonempty then
        hfin.toFinset.inf' h (fun i => dist (c p) (a i) - ρ i) else 1 with hm
    have hmpos : 0 < m := by
      by_cases h : hfin.toFinset.Nonempty
      · rw [hm, dif_pos h]
        exact (Finset.lt_inf'_iff h).mpr (fun i hi => hδ i hi)
      · rw [hm, dif_neg h]; norm_num
    have hmle : ∀ i ∈ hfin.toFinset, m ≤ dist (c p) (a i) - ρ i := by
      intro i hi
      by_cases h : hfin.toFinset.Nonempty
      · rw [hm, dif_pos h]; exact Finset.inf'_le _ hi
      · exact absurd ⟨i, hi⟩ h
    have hminpos : 0 < min m ε₀ := lt_min hmpos hε₀
    refine ⟨min m ε₀ / 2, by positivity, ?_, ?_⟩
    · rintro z hz
      refine hε₀sub (Metric.mem_ball.mpr ?_)
      have h1 : dist z (c p) < min m ε₀ / 2 := Metric.mem_ball.mp hz
      have h2 : min m ε₀ / 2 ≤ ε₀ := by linarith [min_le_right m ε₀]
      linarith
    · intro i hi z hzB hzb
      have his : i ∈ hfin.toFinset := hfin.mem_toFinset.mpr hi
      have hdle : m ≤ dist (c p) (a i) - ρ i := hmle i his
      have hzn : dist z (c p) < min m ε₀ / 2 := Metric.mem_ball.mp hzB
      have hltm : dist z (c p) < m := by
        have h2 : min m ε₀ / 2 ≤ m := by linarith [min_le_left m ε₀]
        linarith
      have hzai : dist z (a i) < ρ i := Metric.mem_ball.mp hzb
      have htri : dist (c p) (a i) ≤ dist (c p) z + dist z (a i) :=
        dist_triangle (c p) z (a i)
      have hltm' : dist (c p) z < m := by rwa [dist_comm] at hltm
      linarith
  -- the neighbourhood and the avoidance
  set B : Set X := Submission.chartBall c (c p) ε with hBdef
  refine ⟨c, B, L₁, L₂, hc, Submission.chartBall_isOpen c (c p) ε,
    Submission.mem_chartBall.mpr ⟨hpsrc, Metric.mem_ball_self hε⟩,
    Submission.chartBall_subset_source c (c p) ε, hpsrc, hL₁, hL₂, ⟨w, hw₁, hw₂⟩, ?_⟩
  rintro x ⟨hxfill, hxB⟩ hcon
  have hxsrc : x ∈ c.source := Submission.chartBall_subset_source c (c p) ε hxB
  have hxtgt : c x ∈ c.target := c.map_source hxsrc
  have hxball : ‖c x - c p‖ < ε := by
    have := Metric.mem_ball.mp ((Submission.mem_chartBall.mp hxB).2)
    rwa [Complex.dist_eq] at this
  have hxVc : x ∉ V := by
    intro hxV
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV ▸ hxV)
    have hcy : c x ∈ Metric.ball (a i) (ρ i) := (Submission.mem_chartBall.mp hi).2
    have hcyB : c x ∈ Metric.ball (c p) ε := (Submission.mem_chartBall.mp hxB).2
    have hiT : c p ∈ Metric.closedBall (a i) (ρ i) := by
      by_contra hiT
      exact hεfar i hiT (c x) hcyB hcy
    exact hsecT i hiT (c x) hcy hcon
  -- the radial path from `x` to `p` stays in `Vᶜ`
  set γ : ℝ → X := fun t => c.symm (c p + t • (c x - c p)) with hγ
  have hγmem : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ Vᶜ := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · have hpt : γ t = p := by
        subst h0
        rw [hγ]
        simp only [zero_smul, add_zero]
        exact c.left_inv hpsrc
      rw [hpt]
      simpa using hpVc
    · have hnorm : dist (c p + t • (c x - c p)) (c p) < ε := by
        rw [dist_eq_norm, add_sub_cancel_left]
        calc ‖t • (c x - c p)‖ = t * ‖c x - c p‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
          _ ≤ ‖c x - c p‖ := mul_le_of_le_one_left (norm_nonneg _) ht.2
          _ < ε := hxball
      have hmemtgt : c p + t • (c x - c p) ∈ c.target := hεtgt (Metric.mem_ball.mpr hnorm)
      have hγB : γ t ∈ B := by
        refine Submission.mem_chartBall.mpr ⟨c.map_target hmemtgt, ?_⟩
        rw [hγ]
        rw [c.right_inv hmemtgt]
        exact Metric.mem_ball.mpr hnorm
      have h1' : 0 < L₁ (c (γ t) - c p) := by
        have hv : c (γ t) - c p = t • (c x - c p) := by
          rw [hγ, c.right_inv hmemtgt, add_sub_cancel_left]
        rw [hv, map_smul, smul_eq_mul]
        exact mul_pos hpos hcon.1
      have h2' : 0 < L₂ (c (γ t) - c p) := by
        have hv : c (γ t) - c p = t • (c x - c p) := by
          rw [hγ, c.right_inv hmemtgt, add_sub_cancel_left]
        rw [hv, map_smul, smul_eq_mul]
        exact mul_pos hpos hcon.2
      have hyV : γ t ∉ V := by
        intro hyV
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV ▸ hyV)
        have hcy : c (γ t) ∈ Metric.ball (a i) (ρ i) := (Submission.mem_chartBall.mp hi).2
        have hcyB : c (γ t) ∈ Metric.ball (c p) ε := (Submission.mem_chartBall.mp hγB).2
        have hiT : c p ∈ Metric.closedBall (a i) (ρ i) := by
          by_contra hiT
          exact hεfar i hiT (c (γ t)) hcyB hcy
        exact hsecT i hiT (c (γ t)) hcy ⟨h1', h2'⟩
      simpa using hyV
  have hcont : ContinuousOn γ (Set.Icc (0:ℝ) 1) := by
    refine ContinuousOn.comp c.continuousOn_symm ?_ ?_
    · fun_prop
    · intro t ht
      rcases eq_or_lt_of_le ht.1 with h0 | hpos
      · subst h0
        simp only [zero_smul, add_zero]
        exact c.map_source hpsrc
      · refine hεtgt (Metric.mem_ball.mpr ?_)
        rw [dist_eq_norm, add_sub_cancel_left]
        calc ‖t • (c x - c p)‖ = t * ‖c x - c p‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
          _ ≤ ‖c x - c p‖ := mul_le_of_le_one_left (norm_nonneg _) ht.2
          _ < ε := hxball
  have hpre : IsPreconnected (γ '' Set.Icc (0:ℝ) 1) :=
    IsPreconnected.image isPreconnected_Icc γ hcont
  have hpmem : p ∈ γ '' Set.Icc (0:ℝ) 1 :=
    ⟨0, ⟨le_refl 0, zero_le_one⟩, by
      rw [hγ]; simp only [zero_smul, add_zero]; exact c.left_inv hpsrc⟩
  have hZsub : γ '' Set.Icc (0:ℝ) 1 ⊆ Z := by
    refine IsPreconnected.subset_connectedComponentIn hpre hpmem ?_
    rintro y ⟨t, ht, rfl⟩
    exact hγmem t ht
  have hxZ : x ∈ Z := hZsub ⟨1, ⟨zero_le_one, le_refl 1⟩, by
    rw [hγ]
    simp only [one_smul]
    rw [show c p + (c x - c p) = c x by ring, c.left_inv hxsrc]⟩
  have : x ∈ Z ∩ filling V := ⟨hxZ, hxfill⟩
  rw [hZW] at this
  exact this

/-! ## The sector condition is inherited by the filling

The *filling* of an open set `V` adds the relatively compact components of `Vᶜ`.  Hence the sector
condition at the frontier of `V` transfers to the frontier of the filling, whatever the shape of `V`:
at a frontier point `p` of the filling, the component of `Vᶜ` through `p` has non-compact closure,
so it is disjoint from the filling, and the sector of the condition at `p` — an open set disjoint
from `V` — lies in that component.  This is the multi-chart-compatible form of the transport
performed inside `hasSectorBoundary_filling_of_chartBallUnion`, and it is what lets the sector
condition be read off from a union of chart balls living in *different* atlas charts (the situation
produced by the disk tiling). -/

/-- **The sector condition is inherited by the filling.**

If `V` is open, its filling is open, and `V` satisfies the sector condition at each of its frontier
points, then the filling satisfies the sector condition at each of the frontier points of the
filling. -/
theorem hasSectorBoundary_filling_of_sectorCondition {V : Set X} (hV : IsOpen V)
    (hWo : IsOpen (filling V))
    (hsect : ∀ p ∈ frontier V, Work.SimplyConnected.ABS.HasSectorBoundary V p) :
    ∀ p ∈ frontier (filling V),
      Work.SimplyConnected.ABS.HasSectorBoundary (filling V) p := by
  classical
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  intro p hp
  have hWV : V ⊆ filling V := fun x hx => by rw [filling]; exact Or.inl hx
  have hpfill : p ∉ filling V := by
    have h := hp
    rw [frontier, Set.mem_sdiff, hWo.interior_eq] at h
    exact h.2
  have hpclW : p ∈ closure (filling V) := hp.1
  have hpVc : p ∉ V := fun h => hpfill (hWV h)
  set Z : Set X := connectedComponentIn Vᶜ p with hZ
  have hpZ : p ∈ Z := mem_connectedComponentIn (by simpa using hpVc)
  have hZnc : ¬ IsCompact (closure Z) := by
    intro hcZ
    have hmem : IsCompact (closure (connectedComponentIn Vᶜ p)) := by rw [← hZ]; exact hcZ
    exact hpfill (by rw [filling]; exact Or.inr hmem)
  have hZW : Z ∩ filling V = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    intro x hx
    have hxV : x ∉ V := fun hxV => (connectedComponentIn_subset Vᶜ p) hx.1 (by simpa using hxV)
    have hcomp : connectedComponentIn Vᶜ x = Z := by
      rw [← connectedComponentIn_eq (F := Vᶜ) hx.1, hZ]
    have hxm : x ∉ filling V := by
      rw [filling]
      rintro (h | h)
      · exact hxV h
      · have h' : IsCompact (closure (connectedComponentIn Vᶜ x)) := h
        exact hZnc (by rwa [hcomp] at h')
    exact hxm hx.2
  have hpclV : p ∈ closure V := by
    by_contra hcon
    have hcon' : p ∈ (closure V)ᶜ := by simpa using hcon
    set B : Set X := connectedComponentIn ((closure V)ᶜ) p with hB
    have hBopen : IsOpen B := isClosed_closure.isOpen_compl.connectedComponentIn
    have hpB : p ∈ B := mem_connectedComponentIn hcon'
    have hBpre : IsPreconnected B := (isConnected_connectedComponentIn_iff.mpr hcon').2
    have hBsub : B ⊆ (closure V)ᶜ := connectedComponentIn_subset _ _
    have hBVc : B ⊆ Vᶜ := fun x hx hxv => hBsub hx (subset_closure hxv)
    have hBZ : B ⊆ Z := IsPreconnected.subset_connectedComponentIn hBpre hpB hBVc
    obtain ⟨x, hx⟩ := (mem_closure_iff.mp hpclW B hBopen hpB)
    obtain ⟨hxB, hxW'⟩ := hx
    have hxV : x ∉ V := fun hxv => hBVc hxB hxv
    have hxZ : x ∈ Z := hBZ hxB
    have hxmem : x ∈ V ∨ IsCompact (closure (connectedComponentIn Vᶜ x)) := by
      have := hxW'; rw [filling] at this; exact this
    rcases hxmem with h | h
    · exact hxV h
    · refine hZnc ?_
      have h3 : connectedComponentIn Vᶜ x = Z := by
        rw [(connectedComponentIn_eq (F := Vᶜ) (x := p) (y := x)
          (by simpa [hZ] using hxZ)).symm]
      rwa [h3] at h
  have hpfV : p ∈ frontier V := by
    rw [frontier, hV.interior_eq]
    exact ⟨hpclV, hpVc⟩
  obtain ⟨c, V₀, L₁, L₂, hc, hV₀o, hpV₀, hV₀sub, hpsrc, hL₁, hL₂, hdir, havoid⟩ :=
    hsect p hpfV
  obtain ⟨w₀, hw₀₁, hw₀₂⟩ := hdir
  -- a radius such that the round ball in the chart stays inside `c.target` and maps into `V₀`
  have hcont : ContinuousAt c.symm (c p) :=
    c.continuousOn_symm.continuousAt (c.open_target.mem_nhds (c.map_source hpsrc))
  obtain ⟨δ, hδpos, hδtgt, hδV₀⟩ : ∃ δ : ℝ, 0 < δ ∧ Metric.ball (c p) δ ⊆ c.target ∧
      Metric.ball (c p) δ ⊆ c.symm ⁻¹' V₀ := by
    have h1 : c.symm ⁻¹' V₀ ∈ 𝓝 (c p) :=
      hcont.preimage_mem_nhds (by rw [c.left_inv hpsrc]; exact hV₀o.mem_nhds hpV₀)
    have h2 : c.target ∈ 𝓝 (c p) := c.open_target.mem_nhds (c.map_source hpsrc)
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem h1 h2)
    exact ⟨δ, hδ, fun z hz => (hsub hz).2, fun z hz => (hsub hz).1⟩
  -- the sectorial ball of the chart
  set S : Set ℂ := Metric.ball (c p) δ ∩ {z : ℂ | 0 < L₁ (z - c p) ∧ 0 < L₂ (z - c p)} with hS
  have hSconv : Convex ℝ S := by
    refine (convex_ball (c p) δ).inter ?_
    intro x hx y hy a b ha hb hab
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    have hsplit : a • (x - c p) + b • (y - c p) = a • x + b • y - c p := by
      have hkey : a • (x - c p) + b • (y - c p) = (a • x + b • y) - (a + b) • c p := by
        rw [smul_sub, smul_sub, add_smul]
        abel
      rw [hkey, hab, one_smul]
    constructor
    · have key : L₁ ((a • x + b • y) - c p) = a * L₁ (x - c p) + b * L₁ (y - c p) := by
        rw [← hsplit, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      rw [key]
      rcases eq_or_lt_of_le ha with h0 | h0
      · rw [← h0, zero_mul, zero_add]
        have hb1 : b = 1 := by linarith
        rw [hb1, one_mul]
        exact hy1
      · exact add_pos_of_pos_of_nonneg (mul_pos h0 hx1) (mul_nonneg hb hy1.le)
    · have key : L₂ ((a • x + b • y) - c p) = a * L₂ (x - c p) + b * L₂ (y - c p) := by
        rw [← hsplit, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      rw [key]
      rcases eq_or_lt_of_le ha with h0 | h0
      · rw [← h0, zero_mul, zero_add]
        have hb1 : b = 1 := by linarith
        rw [hb1, one_mul]
        exact hy2
      · exact add_pos_of_pos_of_nonneg (mul_pos h0 hx2) (mul_nonneg hb hy2.le)
  have hSpre : IsPreconnected S := hSconv.isPreconnected
  have hApre : IsPreconnected (c.symm '' S) :=
    hSpre.image c.symm (c.continuousOn_symm.mono (fun z hz => hδtgt hz.1))
  have hAne : (c.symm '' S).Nonempty := by
    have hpos : 0 < δ / (2 * (‖w₀‖ + 1)) := by positivity
    have hnorm : ‖w₀‖ / (2 * (‖w₀‖ + 1)) < 1 := by
      have := norm_nonneg w₀
      rw [div_lt_one (by positivity)]
      linarith
    have hmem : c p + (δ / (2 * (‖w₀‖ + 1))) • w₀ ∈ S := by
      refine ⟨?_, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg hpos.le]
        calc δ / (2 * (‖w₀‖ + 1)) * ‖w₀‖
            = δ * (‖w₀‖ / (2 * (‖w₀‖ + 1))) := by ring
        _ < δ * 1 := mul_lt_mul_of_pos_left hnorm hδpos
        _ = δ := by ring
      · have hkey : L₁ (c p + (δ / (2 * (‖w₀‖ + 1))) • w₀ - c p)
            = (δ / (2 * (‖w₀‖ + 1))) * L₁ w₀ := by
          rw [show c p + (δ / (2 * (‖w₀‖ + 1))) • w₀ - c p
              = (δ / (2 * (‖w₀‖ + 1))) • w₀ by ring, map_smul, smul_eq_mul]
        rw [hkey]; positivity
      · have hkey : L₂ (c p + (δ / (2 * (‖w₀‖ + 1))) • w₀ - c p)
            = (δ / (2 * (‖w₀‖ + 1))) * L₂ w₀ := by
          rw [show c p + (δ / (2 * (‖w₀‖ + 1))) • w₀ - c p
              = (δ / (2 * (‖w₀‖ + 1))) • w₀ by ring, map_smul, smul_eq_mul]
        rw [hkey]; positivity
    exact ⟨c.symm _, ⟨_, hmem, rfl⟩⟩
  have hpclA : p ∈ closure (c.symm '' S) := by
    rw [mem_closure_iff_nhds]
    intro U hU
    have hU' : U ∈ 𝓝 (c.symm (c p)) := by rw [c.left_inv hpsrc]; exact hU
    have hpre : c.symm ⁻¹' U ∈ 𝓝 (c p) := hcont.preimage_mem_nhds hU'
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
    have hnorm : ‖w₀‖ / (2 * (‖w₀‖ + 1)) < 1 := by
      have := norm_nonneg w₀
      rw [div_lt_one (by positivity)]
      linarith
    obtain ⟨t, htpos, htsmall, htε⟩ : ∃ t : ℝ, 0 < t ∧ t * ‖w₀‖ < δ ∧ t * ‖w₀‖ < ε := by
      refine ⟨min δ ε / (2 * (‖w₀‖ + 1)), by positivity, ?_, ?_⟩
      · calc min δ ε / (2 * (‖w₀‖ + 1)) * ‖w₀‖
            = min δ ε * (‖w₀‖ / (2 * (‖w₀‖ + 1))) := by ring
        _ < min δ ε * 1 := mul_lt_mul_of_pos_left hnorm (lt_min hδpos hε)
        _ = min δ ε := by ring
        _ ≤ δ := min_le_left _ _
      · calc min δ ε / (2 * (‖w₀‖ + 1)) * ‖w₀‖
            = min δ ε * (‖w₀‖ / (2 * (‖w₀‖ + 1))) := by ring
        _ < min δ ε * 1 := mul_lt_mul_of_pos_left hnorm (lt_min hδpos hε)
        _ = min δ ε := by ring
        _ ≤ ε := min_le_right _ _
    have htS : c p + t • w₀ ∈ S := by
      refine ⟨?_, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg htpos.le]
        exact htsmall
      · have hkey : L₁ (c p + t • w₀ - c p) = t * L₁ w₀ := by
          rw [show c p + t • w₀ - c p = t • w₀ by ring, map_smul, smul_eq_mul]
        rw [hkey]; positivity
      · have hkey : L₂ (c p + t • w₀ - c p) = t * L₂ w₀ := by
          rw [show c p + t • w₀ - c p = t • w₀ by ring, map_smul, smul_eq_mul]
        rw [hkey]; positivity
    have htU : c p + t • w₀ ∈ c.symm ⁻¹' U := hεsub (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg htpos.le]
      exact htε)
    exact ⟨c.symm (c p + t • w₀), htU, ⟨c p + t • w₀, htS, rfl⟩⟩
  -- the sectorial set avoids `V`, hence lies in the component `Z`
  have hAVc : c.symm '' S ⊆ Vᶜ := by
    rintro x ⟨z, hz, rfl⟩ hxV
    have hzV₀ : c.symm z ∈ V₀ := hδV₀ hz.1
    have hbad := havoid (c.symm z) ⟨hxV, hzV₀⟩
    have hz2 : 0 < L₁ (z - c p) ∧ 0 < L₂ (z - c p) := hz.2
    have hz' : 0 < L₁ (c (c.symm z) - c p) ∧ 0 < L₂ (c (c.symm z) - c p) := by
      rwa [c.right_inv (hδtgt hz.1)]
    exact hbad hz'
  have hAZ : c.symm '' S ⊆ Z := by
    have hsub : closure (c.symm '' S) ⊆ Z :=
      hApre.closure.subset_connectedComponentIn hpclA
        (closure_minimal hAVc hV.isClosed_compl)
    exact fun x hx => hsub (subset_closure hx)
  refine ⟨c, V₀ ∩ (c.source ∩ c ⁻¹' Metric.ball (c p) δ), L₁, L₂, hc, ?_, ?_, ?_, hpsrc,
    hL₁, hL₂, ⟨w₀, hw₀₁, hw₀₂⟩, ?_⟩
  · exact hV₀o.inter (c.continuousOn.isOpen_inter_preimage c.open_source Metric.isOpen_ball)
  · exact ⟨hpV₀, hpsrc, Metric.mem_ball_self hδpos⟩
  · intro y hy
    exact hy.2.1
  · rintro x ⟨hxfill, hxV₀'⟩ ⟨hx1, hx2⟩
    have hxsrc : x ∈ c.source := hxV₀'.2.1
    have hxball : c x ∈ Metric.ball (c p) δ := hxV₀'.2.2
    have hxS : c x ∈ S := ⟨hxball, hx1, hx2⟩
    have hxmem : x ∈ c.symm '' S := ⟨c x, hxS, c.left_inv hxsrc⟩
    have hxZ : x ∈ Z := hAZ hxmem
    have hxint : x ∈ Z ∩ filling V := ⟨hxZ, hxfill⟩
    rw [hZW] at hxint
    exact hxint

/-- **The target from the filling of a general-position union of chart balls.**

This is the interface through which the ABS engulfing construction (`FILL` + `SURF`) discharges the
target: the engulfing produces exactly a finite union `V` of chart balls (in a single atlas chart)
whose *filling* is open, precompact, not all of `X`, and simply connected.  The sector condition —
the remaining requirement — is then free, by `hasSectorBoundary_filling_of_chartBallUnion`. -/
theorem region_with_sector_boundary_of_filling_chartBallUnion
    (hX : ¬ CompactSpace X) {K : Set X} {c : OpenPartialHomeomorph X ℂ}
    {ι : Type*} [Fintype ι] [Nonempty ι] {a : ι → ℂ} {ρ : ι → ℝ}
    (hc : c ∈ atlas ℂ X) (hρ : ∀ i, 0 < ρ i)
    (hsub : ∀ i, Metric.closedBall (a i) (ρ i) ⊆ c.target)
    (htwo : ∀ z : ℂ, ({i | z ∈ Metric.closedBall (a i) (ρ i)} : Set ι).ncard ≤ 2)
    (hgood : ∀ p ∈ frontier (⋃ i, Submission.chartBall c (a i) (ρ i)), ∀ i j, i ≠ j →
      c p ∈ Metric.closedBall (a i) (ρ i) → c p ∈ Metric.closedBall (a j) (ρ j) →
      (c p - a i) / ρ i ≠ -((c p - a j) / ρ j))
    (hKV : K ⊆ filling (⋃ i, Submission.chartBall c (a i) (ρ i)))
    (hWo : IsOpen (filling (⋃ i, Submission.chartBall c (a i) (ρ i))))
    (hcomp : IsCompact (closure (filling (⋃ i, Submission.chartBall c (a i) (ρ i)))))
    (hsc : SimplyConnectedSpace ↥(filling (⋃ i, Submission.chartBall c (a i) (ρ i)))) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, HasSectorBoundary W p :=
  ⟨filling (⋃ i, Submission.chartBall c (a i) (ρ i)), hWo, hKV, hcomp,
    ne_univ_of_isCompact_closure hX hcomp, hsc,
    hasSectorBoundary_filling_of_chartBallUnion (X := X) (c := c) (a := a) (ρ := ρ)
      hc hρ hsub htwo hgood hWo⟩

end FillingSector

/-! ## The sector condition from a locally regular level set

The lemmas of this section free the sector condition from any chart-ball structure: at a frontier
point where the boundary is locally a *regular level set* of a differentiable function (with `W` on
one side), the sector condition holds.  This is the form needed by the ABS filling construction,
whose boundaries are regular level sets of the Green function of a region (`Work.CriticalSet`).
-/

set_option linter.unusedSectionVars false

/-- The real-linear functional `z ↦ -β Re z + α Im z`. -/
def rotCLM (α β : ℝ) : ℂ →L[ℝ] ℝ := (-β) • Complex.reCLM + α • Complex.imCLM

@[simp] theorem rotCLM_apply (α β : ℝ) (z : ℂ) : rotCLM α β z = -β * z.re + α * z.im := by
  simp [rotCLM, mul_comm]

theorem coordCLM_apply (α β : ℝ) (z : ℂ) :
    ((α • Complex.reCLM + β • Complex.imCLM : ℂ →L[ℝ] ℝ)) z = α * z.re + β * z.im := by
  simp

/-- **The elementary wedge construction.**  For non-zero coefficients `(α, β)` there are two non-zero
functionals spanning a sector on which the functional `z ↦ α Re z + β Im z` is bounded below by
`δ‖z‖`. -/
theorem exists_wedge_functionals_of_ne_zero_coeffs {α β : ℝ} (hne : α ≠ 0 ∨ β ≠ 0) :
    ∃ (L₁ L₂ : ℂ →L[ℝ] ℝ) (δ : ℝ), 0 < δ ∧ L₁ ≠ 0 ∧ L₂ ≠ 0 ∧
      (∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w) ∧
      ∀ h : ℂ, 0 < L₁ h → 0 < L₂ h → δ * ‖h‖ ≤ α * h.re + β * h.im := by
  classical
  have hs : 0 < α ^ 2 + β ^ 2 := by
    rcases hne with h | h
    · nlinarith [sq_pos_of_ne_zero h]
    · nlinarith [sq_pos_of_ne_zero h]
  have hpos : 0 < |α| + |β| := by
    rcases hne with h | h
    · exact add_pos_of_pos_of_nonneg (abs_pos.mpr h) (abs_nonneg β)
    · exact add_pos_of_nonneg_of_pos (abs_nonneg α) (abs_pos.mpr h)
  set δ : ℝ := (α ^ 2 + β ^ 2) / (2 * (|α| + |β|)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  set L₁ : ℂ →L[ℝ] ℝ := (α • Complex.reCLM + β • Complex.imCLM) + rotCLM α β with hL₁
  set L₂ : ℂ →L[ℝ] ℝ := (α • Complex.reCLM + β • Complex.imCLM) - rotCLM α β with hL₂
  have hL₁_apply : ∀ z, L₁ z = (α - β) * z.re + (β + α) * z.im := by
    intro z
    rw [hL₁, add_apply, coordCLM_apply, rotCLM_apply]
    ring
  have hL₂_apply : ∀ z, L₂ z = (α + β) * z.re + (β - α) * z.im := by
    intro z
    rw [hL₂, sub_apply, coordCLM_apply, rotCLM_apply]
    ring
  have hwitness : ∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w := by
    have hre : (((α : ℂ) + (β : ℂ) * Complex.I)).re = α := by simp
    have him : (((α : ℂ) + (β : ℂ) * Complex.I)).im = β := by simp
    refine ⟨(α : ℂ) + (β : ℂ) * Complex.I, ?_, ?_⟩
    · rw [hL₁_apply, hre, him]; nlinarith [hs]
    · rw [hL₂_apply, hre, him]; nlinarith [hs]
  refine ⟨L₁, L₂, δ, hδpos, ?_, ?_, hwitness, ?_⟩
  · intro h
    obtain ⟨w, hw, -⟩ := hwitness
    rw [h] at hw; simp at hw
  · intro h
    obtain ⟨w, -, hw⟩ := hwitness
    rw [h] at hw; simp at hw
  · intro h h1 h2
    have hA : α * h.re + β * h.im = (L₁ h + L₂ h) / 2 := by
      rw [hL₁_apply, hL₂_apply]; ring
    have hB : rotCLM α β h = (L₁ h - L₂ h) / 2 := by
      rw [hL₁, hL₂, add_apply, sub_apply]; ring
    have hAh : 0 < α * h.re + β * h.im := by rw [hA]; linarith
    have hBh : |rotCLM α β h| ≤ α * h.re + β * h.im := by
      rw [hB, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2),
        div_le_iff₀ (by norm_num : (0:ℝ) < 2), abs_le]
      constructor <;> linarith
    have hx : (α ^ 2 + β ^ 2) * h.re = α * (α * h.re + β * h.im) - β * rotCLM α β h := by
      rw [rotCLM_apply]; ring
    have hy : (α ^ 2 + β ^ 2) * h.im = β * (α * h.re + β * h.im) + α * rotCLM α β h := by
      rw [rotCLM_apply]; ring
    have hxabs : (α ^ 2 + β ^ 2) * |h.re| ≤ (|α| + |β|) * (α * h.re + β * h.im) := by
      have h1' : |(α ^ 2 + β ^ 2) * h.re| ≤ (|α| + |β|) * (α * h.re + β * h.im) := by
        rw [hx]
        calc |α * (α * h.re + β * h.im) - β * rotCLM α β h|
            = |α * (α * h.re + β * h.im) + -(β * rotCLM α β h)| := by ring_nf
          _ ≤ |α * (α * h.re + β * h.im)| + |-(β * rotCLM α β h)| := abs_add_le _ _
          _ = |α| * (α * h.re + β * h.im) + |β| * |rotCLM α β h| := by
                rw [abs_mul, abs_neg, abs_mul, abs_of_pos hAh]
          _ ≤ |α| * (α * h.re + β * h.im) + |β| * (α * h.re + β * h.im) :=
                add_le_add le_rfl (mul_le_mul_of_nonneg_left hBh (abs_nonneg β))
          _ = (|α| + |β|) * (α * h.re + β * h.im) := by ring
      rw [abs_mul, abs_of_pos hs] at h1'
      exact h1'
    have hyabs : (α ^ 2 + β ^ 2) * |h.im| ≤ (|α| + |β|) * (α * h.re + β * h.im) := by
      have h1' : |(α ^ 2 + β ^ 2) * h.im| ≤ (|α| + |β|) * (α * h.re + β * h.im) := by
        rw [hy]
        calc |β * (α * h.re + β * h.im) + α * rotCLM α β h|
            ≤ |β * (α * h.re + β * h.im)| + |α * rotCLM α β h| := abs_add_le _ _
          _ = |β| * (α * h.re + β * h.im) + |α| * |rotCLM α β h| := by
                rw [abs_mul, abs_mul, abs_of_pos hAh]
          _ ≤ |β| * (α * h.re + β * h.im) + |α| * (α * h.re + β * h.im) :=
                add_le_add le_rfl (mul_le_mul_of_nonneg_left hBh (abs_nonneg α))
          _ = (|α| + |β|) * (α * h.re + β * h.im) := by ring
      rw [abs_mul, abs_of_pos hs] at h1'
      exact h1'
    have hnorm : ‖h‖ ≤ |h.re| + |h.im| := Complex.norm_le_abs_re_add_abs_im h
    have hkey : ‖h‖ * (α ^ 2 + β ^ 2) ≤ 2 * (|α| + |β|) * (α * h.re + β * h.im) := by
      have h2 : (|h.re| + |h.im|) * (α ^ 2 + β ^ 2) ≤
          2 * (|α| + |β|) * (α * h.re + β * h.im) := by
        nlinarith [hxabs, hyabs]
      nlinarith [hnorm, mul_nonneg (sub_nonneg.mpr hnorm) (le_of_lt hs)]
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 2 * (|α| + |β|))]
    linarith


end Filling


/-! ## The sector condition from a locally regular level set

The lemmas of this section free the sector condition from any chart-ball structure: at a frontier
point where the boundary is locally a *regular level set* of a differentiable function (with `W` on
one side), the sector condition holds.  This is the form needed by the ABS filling construction,
whose boundaries are regular level sets of the Green function of a region (`Work.CriticalSet`).
-/

set_option linter.unusedSectionVars false

theorem complex_re_smul_one_add_im_smul_I (z : Complex) :
    (z.re) • (1:Complex) + (z.im) • Complex.I = z := by
  rw [Complex.real_smul (x := z.re) (z := (1:Complex)),
    Complex.real_smul (x := z.im) (z := Complex.I), mul_one]
  exact Complex.re_add_im z

/-- **A wedge on the side where the function increases.** -/
theorem exists_wedge_of_hasFDerivAt {phi : Complex → Real} {L : Complex →L[Real] Real}
    (hL : L ≠ 0) {z0 : Complex} (hphi : HasFDerivAt phi L z0) :
    ∃ (L1 L2 : Complex →L[Real] Real), L1 ≠ 0 ∧ L2 ≠ 0 ∧ (∃ w : Complex, 0 < L1 w ∧ 0 < L2 w) ∧
      ∃ r > 0, ∀ z, dist z z0 < r → (0 < L1 (z - z0) ∧ 0 < L2 (z - z0)) → phi z0 < phi z := by
  classical
  set alpha : Real := L 1 with halpha
  set beta : Real := L Complex.I with hbeta
  have hL_apply : ∀ z : Complex, L z = alpha * z.re + beta * z.im := by
    intro z
    conv_lhs => rw [← complex_re_smul_one_add_im_smul_I z]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← halpha, ← hbeta]
    ring
  have hne : alpha ≠ 0 ∨ beta ≠ 0 := by
    by_contra h
    push Not at h
    refine hL (ContinuousLinearMap.ext fun z => ?_)
    rw [hL_apply, h.1, h.2]
    simp
  obtain ⟨L1, L2, delta, hdelta, hL1, hL2, hwit, hquant⟩ :=
    exists_wedge_functionals_of_ne_zero_coeffs hne
  have hlittle : (fun z => phi z - phi z0 - L (z - z0)) =o[nhds z0]
      (fun z : Complex => z - z0) := hphi.isLittleO
  have heps : 0 < delta / 2 := by linarith
  have hev : ∀ᶠ z in nhds z0, ‖phi z - phi z0 - L (z - z0)‖ ≤ (delta / 2) * ‖z - z0‖ :=
    Asymptotics.isLittleO_iff.mp hlittle heps
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨r, hr, hball⟩ := hev
  refine ⟨L1, L2, hL1, hL2, hwit, r, hr, fun z hz hsec => ?_⟩
  have h1 := hball hz
  have hlow : delta * ‖z - z0‖ ≤ L (z - z0) := by
    rw [hL_apply]
    exact hquant (z - z0) hsec.1 hsec.2
  have hzne : z ≠ z0 := by
    rintro rfl
    simp at hsec
  have hzk : 0 < ‖z - z0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzne)
  have h3 : |L (z - z0) - (phi z - phi z0)| ≤ (delta / 2) * ‖z - z0‖ := by
    have heq : L (z - z0) - (phi z - phi z0) = -(phi z - phi z0 - L (z - z0)) := by ring
    rw [heq, abs_neg]
    exact h1
  have h4 : L (z - z0) - (phi z - phi z0) ≤ (delta / 2) * ‖z - z0‖ := (abs_le.mp h3).2
  have h5 : 0 < (delta / 2) * ‖z - z0‖ := by positivity
  linarith

/-- **A wedge on the side where the function decreases.** -/
theorem exists_wedge_of_hasFDerivAt_lt {phi : Complex → Real} {L : Complex →L[Real] Real}
    (hL : L ≠ 0) {z0 : Complex} (hphi : HasFDerivAt phi L z0) :
    ∃ (L1 L2 : Complex →L[Real] Real), L1 ≠ 0 ∧ L2 ≠ 0 ∧ (∃ w : Complex, 0 < L1 w ∧ 0 < L2 w) ∧
      ∃ r > 0, ∀ z, dist z z0 < r → (0 < L1 (z - z0) ∧ 0 < L2 (z - z0)) → phi z < phi z0 := by
  classical
  set alpha : Real := L 1 with halpha
  set beta : Real := L Complex.I with hbeta
  have hL_apply : ∀ z : Complex, L z = alpha * z.re + beta * z.im := by
    intro z
    conv_lhs => rw [← complex_re_smul_one_add_im_smul_I z]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← halpha, ← hbeta]
    ring
  have hne : -alpha ≠ 0 ∨ -beta ≠ 0 := by
    by_contra h
    push Not at h
    refine hL (ContinuousLinearMap.ext fun z => ?_)
    rw [hL_apply]
    have h1 : alpha = 0 := by simpa using h.1
    have h2 : beta = 0 := by simpa using h.2
    rw [h1, h2]
    simp
  obtain ⟨L1, L2, delta, hdelta, hL1, hL2, hwit, hquant⟩ :=
    exists_wedge_functionals_of_ne_zero_coeffs hne
  have hlittle : (fun z => phi z - phi z0 - L (z - z0)) =o[nhds z0]
      (fun z : Complex => z - z0) := hphi.isLittleO
  have heps : 0 < delta / 2 := by linarith
  have hev : ∀ᶠ z in nhds z0, ‖phi z - phi z0 - L (z - z0)‖ ≤ (delta / 2) * ‖z - z0‖ :=
    Asymptotics.isLittleO_iff.mp hlittle heps
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨r, hr, hball⟩ := hev
  refine ⟨L1, L2, hL1, hL2, hwit, r, hr, fun z hz hsec => ?_⟩
  have h1 := hball hz
  have hlow : delta * ‖z - z0‖ ≤ -(L (z - z0)) := by
    have h := hquant (z - z0) hsec.1 hsec.2
    have h2 : L (z - z0) = alpha * (z - z0).re + beta * (z - z0).im := hL_apply (z - z0)
    linarith
  have hzne : z ≠ z0 := by
    rintro rfl
    simp at hsec
  have hzk : 0 < ‖z - z0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzne)
  have h3 : |L (z - z0) - (phi z - phi z0)| ≤ (delta / 2) * ‖z - z0‖ := by
    have heq : L (z - z0) - (phi z - phi z0) = -(phi z - phi z0 - L (z - z0)) := by ring
    rw [heq, abs_neg]
    exact h1
  have h4 : -(delta / 2) * ‖z - z0‖ ≤ L (z - z0) - (phi z - phi z0) := by
    have := (abs_le.mp h3).1
    linarith
  have h5 : 0 < (delta / 2) * ‖z - z0‖ := by positivity
  linarith


/-! ## The sector condition at a point of a one-sided local level set -/

/-- **The sector condition from a local one-sided sub-level description.** -/
theorem hasSectorBoundary_of_local_sublevel {W : Set X} {p : X} {u : X → Real}
    {L : Complex →L[Real] Real}
    (hderiv : HasFDerivAt (fun z : Complex => u ((chartAt Complex p).symm z)) L
      ((chartAt Complex p) p))
    (hL : L ≠ 0)
    (hside : ∀ᶠ y in nhds p, y ∈ W → ¬ (u p < u y)) :
    Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  classical
  obtain ⟨L1, L2, hL1, hL2, hwit, r, hr, hwedge⟩ :=
    exists_wedge_of_hasFDerivAt (phi := fun z : Complex => u ((chartAt Complex p).symm z)) hL
      hderiv
  rcases Filter.eventually_iff_exists_mem.mp hside with ⟨V, hVmem, hVside⟩
  set V0 : Set X := (interior V ∩ (chartAt Complex p).source) ∩
      ((chartAt Complex p).source ∩ (chartAt Complex p) ⁻¹' Metric.ball ((chartAt Complex p) p) r)
    with hV0
  have hV0open : IsOpen V0 := by
    rw [hV0]
    exact (isOpen_interior.inter (chartAt Complex p).open_source).inter
      (ContinuousOn.isOpen_inter_preimage (chartAt Complex p).continuousOn_toFun
        (chartAt Complex p).open_source Metric.isOpen_ball)
  have hpV0 : p ∈ V0 := by
    rw [hV0]
    exact ⟨⟨mem_interior_iff_mem_nhds.mpr hVmem, mem_chart_source Complex p⟩,
      mem_chart_source Complex p, Metric.mem_ball_self hr⟩
  have hV0sub : V0 ⊆ (chartAt Complex p).source := by
    rw [hV0]; exact fun x hx => hx.1.2
  refine ⟨chartAt Complex p, V0, L1, L2, chart_mem_atlas Complex p, hV0open, hpV0, hV0sub,
    mem_chart_source Complex p, hL1, hL2, hwit, ?_⟩
  rintro x ⟨hxW, hxV⟩ ⟨h1, h2⟩
  have hxsrc : x ∈ (chartAt Complex p).source := hxV.1.2
  have hxball : (chartAt Complex p) x ∈ Metric.ball ((chartAt Complex p) p) r := hxV.2.2
  have hdist : dist ((chartAt Complex p) x) ((chartAt Complex p) p) < r := hxball
  have hlt : u ((chartAt Complex p).symm ((chartAt Complex p) p))
      < u ((chartAt Complex p).symm ((chartAt Complex p) x)) :=
    hwedge ((chartAt Complex p) x) hdist ⟨h1, h2⟩
  rw [(chartAt Complex p).left_inv (mem_chart_source Complex p),
    (chartAt Complex p).left_inv hxsrc] at hlt
  have := hVside x (interior_subset hxV.1.1) hxW
  linarith

/-- **The sector condition from a local one-sided super-level description.** -/
theorem hasSectorBoundary_of_local_superlevel {W : Set X} {p : X} {u : X → Real}
    {L : Complex →L[Real] Real}
    (hderiv : HasFDerivAt (fun z : Complex => u ((chartAt Complex p).symm z)) L
      ((chartAt Complex p) p))
    (hL : L ≠ 0)
    (hside : ∀ᶠ y in nhds p, y ∈ W → ¬ (u y < u p)) :
    Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  classical
  obtain ⟨L1, L2, hL1, hL2, hwit, r, hr, hwedge⟩ :=
    exists_wedge_of_hasFDerivAt_lt (phi := fun z : Complex => u ((chartAt Complex p).symm z)) hL
      hderiv
  rcases Filter.eventually_iff_exists_mem.mp hside with ⟨V, hVmem, hVside⟩
  set V0 : Set X := (interior V ∩ (chartAt Complex p).source) ∩
      ((chartAt Complex p).source ∩ (chartAt Complex p) ⁻¹' Metric.ball ((chartAt Complex p) p) r)
    with hV0
  have hV0open : IsOpen V0 := by
    rw [hV0]
    exact (isOpen_interior.inter (chartAt Complex p).open_source).inter
      (ContinuousOn.isOpen_inter_preimage (chartAt Complex p).continuousOn_toFun
        (chartAt Complex p).open_source Metric.isOpen_ball)
  have hpV0 : p ∈ V0 := by
    rw [hV0]
    exact ⟨⟨mem_interior_iff_mem_nhds.mpr hVmem, mem_chart_source Complex p⟩,
      mem_chart_source Complex p, Metric.mem_ball_self hr⟩
  have hV0sub : V0 ⊆ (chartAt Complex p).source := by
    rw [hV0]; exact fun x hx => hx.1.2
  refine ⟨chartAt Complex p, V0, L1, L2, chart_mem_atlas Complex p, hV0open, hpV0, hV0sub,
    mem_chart_source Complex p, hL1, hL2, hwit, ?_⟩
  rintro x ⟨hxW, hxV⟩ ⟨h1, h2⟩
  have hxsrc : x ∈ (chartAt Complex p).source := hxV.1.2
  have hxball : (chartAt Complex p) x ∈ Metric.ball ((chartAt Complex p) p) r := hxV.2.2
  have hdist : dist ((chartAt Complex p) x) ((chartAt Complex p) p) < r := hxball
  have hlt : u ((chartAt Complex p).symm ((chartAt Complex p) x))
      < u ((chartAt Complex p).symm ((chartAt Complex p) p)) :=
    hwedge ((chartAt Complex p) x) hdist ⟨h1, h2⟩
  rw [(chartAt Complex p).left_inv (mem_chart_source Complex p),
    (chartAt Complex p).left_inv hxsrc] at hlt
  have := hVside x (interior_subset hxV.1.1) hxW
  linarith

/-! ## Regular level sets of a harmonic function -/

/-- **The closed sub-level set of a harmonic function, at a non-critical boundary point.** -/
theorem hasSectorBoundary_of_isRegularLevel_sublevel {E : X → Real} {c : Real} {p : X}
    (hE : Submission.HarmonicOnXAt E p)
    (hreg : fderiv Real (fun z : Complex => E ((chartAt Complex p).symm z))
      ((chartAt Complex p) p) ≠ 0)
    (hcp : E p = c) :
    Work.SimplyConnected.ABS.HasSectorBoundary {x : X | E x ≤ c} p := by
  refine hasSectorBoundary_of_local_sublevel (W := {x : X | E x ≤ c}) (u := E) ?_ hreg ?_
  · have hcd : ContDiffAt Real 1 (fun z : Complex => E ((chartAt Complex p).symm z))
        ((chartAt Complex p) p) := hE.1.of_le (by norm_num)
    exact (hcd.differentiableAt (by norm_num)).hasFDerivAt
  · filter_upwards with y hy
    have hyc : E y ≤ c := hy
    rw [hcp]
    exact fun h => absurd h (not_lt.mpr hyc)

/-- **The closed super-level set of a harmonic function, at a non-critical boundary point.** -/
theorem hasSectorBoundary_of_isRegularLevel_superlevel {E : X → Real} {c : Real} {p : X}
    (hE : Submission.HarmonicOnXAt E p)
    (hreg : fderiv Real (fun z : Complex => E ((chartAt Complex p).symm z))
      ((chartAt Complex p) p) ≠ 0)
    (hcp : E p = c) :
    Work.SimplyConnected.ABS.HasSectorBoundary {x : X | c ≤ E x} p := by
  refine hasSectorBoundary_of_local_superlevel (W := {x : X | c ≤ E x}) (u := E) ?_ hreg ?_
  · have hcd : ContDiffAt Real 1 (fun z : Complex => E ((chartAt Complex p).symm z))
        ((chartAt Complex p) p) := hE.1.of_le (by norm_num)
    exact (hcd.differentiableAt (by norm_num)).hasFDerivAt
  · filter_upwards with y hy
    have hyc : c ≤ E y := hy
    rw [hcp]
    exact fun h => absurd h (not_lt.mpr hyc)

/-- **The closed sub-level set of a `C¹` function, at a regular boundary point.**

The same statement as `hasSectorBoundary_of_isRegularLevel_sublevel`, with the harmonicity of `E`
replaced by `C¹`-regularity at `p`.  This is the form needed by the ABS filling construction, where
the function realising the boundary is an arbitrary proper `C¹` function (a partition-of-unity sum,
or a regularised distance), not a harmonic one. -/
theorem hasSectorBoundary_of_isRegularLevel_sublevel_of_contDiff {E : X → Real} {c : Real}
    {p : X}
    (hcd : ContDiffAt Real 1 (fun z : Complex => E ((chartAt Complex p).symm z))
      ((chartAt Complex p) p))
    (hreg : fderiv Real (fun z : Complex => E ((chartAt Complex p).symm z))
      ((chartAt Complex p) p) ≠ 0)
    (hcp : E p = c) :
    Work.SimplyConnected.ABS.HasSectorBoundary {x : X | E x ≤ c} p := by
  refine hasSectorBoundary_of_local_sublevel (W := {x : X | E x ≤ c}) (u := E) ?_ hreg ?_
  · exact (hcd.differentiableAt (by norm_num)).hasFDerivAt
  · filter_upwards with y hy
    have hyc : E y ≤ c := hy
    rw [hcp]
    exact fun h => absurd h (not_lt.mpr hyc)

/-- **The closed super-level set of a `C¹` function, at a regular boundary point.** -/
theorem hasSectorBoundary_of_isRegularLevel_superlevel_of_contDiff {E : X → Real} {c : Real}
    {p : X}
    (hcd : ContDiffAt Real 1 (fun z : Complex => E ((chartAt Complex p).symm z))
      ((chartAt Complex p) p))
    (hreg : fderiv Real (fun z : Complex => E ((chartAt Complex p).symm z))
      ((chartAt Complex p) p) ≠ 0)
    (hcp : E p = c) :
    Work.SimplyConnected.ABS.HasSectorBoundary {x : X | c ≤ E x} p := by
  refine hasSectorBoundary_of_local_superlevel (W := {x : X | c ≤ E x}) (u := E) ?_ hreg ?_
  · exact (hcd.differentiableAt (by norm_num)).hasFDerivAt
  · filter_upwards with y hy
    have hyc : c ≤ E y := hy
    rw [hcp]
    exact fun h => absurd h (not_lt.mpr hyc)

/-- **The target from the ABS engulfing with a `C¹`-regular-level boundary.**

The `C¹` counterpart of `region_with_sector_boundary_of_levelSet_engulfing`.  This is the shape in
which the ABS filling construction (Anghel--Bruin--Stan, Theorem 12) delivers its piece when the
boundary is a regular level set of an arbitrary proper `C¹` function `E` — a partition-of-unity sum
or a regularised distance from a compact set, neither of which is harmonic, so that the harmonic
form of the interface does not apply.  The sector condition is again free, from the two lemmas
above. -/
theorem region_with_sector_boundary_of_contDiffLevel_engulfing (hX : ¬ CompactSpace X) {K : Set X}
    (h : ∃ Omega : Set X, IsOpen Omega ∧ IsConnected Omega ∧ IsCompact (closure Omega) ∧
      K ⊆ Omega ∧ SimplyConnectedSpace ↥Omega ∧
      ∀ p ∈ frontier Omega,
        (∃ (E : X → ℝ) (c : ℝ),
          ContDiffAt ℝ 1 (fun z : ℂ => E ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) ∧
          fderiv ℝ (fun z : ℂ => E ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) ≠ 0 ∧ E p = c ∧
          (∀ᶠ y in 𝓝 p, y ∈ Omega → ¬ (E p < E y))) ∨
        (∃ (E : X → ℝ) (c : ℝ),
          ContDiffAt ℝ 1 (fun z : ℂ => E ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) ∧
          fderiv ℝ (fun z : ℂ => E ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) ≠ 0 ∧ E p = c ∧
          (∀ᶠ y in 𝓝 p, y ∈ Omega → ¬ (E y < E p)))) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  obtain ⟨Omega, hOo, hOc, hOk, hKO, hsc, hfront⟩ := h
  refine ⟨Omega, hOo, hKO, hOk, ne_univ_of_isCompact_closure hX hOk, hsc, fun p hp => ?_⟩
  rcases hfront p hp with ⟨E, c, hcd, hreg, hcp, hside⟩ | ⟨E, c, hcd, hreg, hcp, hside⟩
  · exact hasSectorBoundary_of_local_sublevel (W := Omega) (u := E)
      ((hcd.differentiableAt (by norm_num)).hasFDerivAt) hreg hside
  · exact hasSectorBoundary_of_local_superlevel (W := Omega) (u := E)
      ((hcd.differentiableAt (by norm_num)).hasFDerivAt) hreg hside

/-- **The target from the ABS engulfing with a regular-level boundary.**

This records precisely what the ABS filling construction must deliver: an open, connected,
precompact `Omega` containing `K`, simply connected, each of whose frontier points is a
non-critical point of a harmonic function `E` (locally `Omega` being a sub- or super-level set of
`E`).  The sector condition is then free, by the lemmas of this section. -/
theorem region_with_sector_boundary_of_levelSet_engulfing (hX : ¬ CompactSpace X) {K : Set X}
    (h : ∃ Omega : Set X, IsOpen Omega ∧ IsConnected Omega ∧ IsCompact (closure Omega) ∧
      K ⊆ Omega ∧ SimplyConnectedSpace ↥Omega ∧
      ∀ p ∈ frontier Omega,
        (∃ (E : X → ℝ) (c : ℝ), Submission.HarmonicOnXAt E p ∧
          fderiv ℝ (fun z : ℂ => E ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) ≠ 0 ∧ E p = c ∧
          (∀ᶠ y in 𝓝 p, y ∈ Omega → ¬ (E p < E y))) ∨
        (∃ (E : X → ℝ) (c : ℝ), Submission.HarmonicOnXAt E p ∧
          fderiv ℝ (fun z : ℂ => E ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) ≠ 0 ∧ E p = c ∧
          (∀ᶠ y in 𝓝 p, y ∈ Omega → ¬ (E y < E p)))) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ W ≠ Set.univ ∧
      SimplyConnectedSpace ↥W ∧
      ∀ p ∈ frontier W, Work.SimplyConnected.ABS.HasSectorBoundary W p := by
  obtain ⟨Omega, hOo, hOc, hOk, hKO, hsc, hfront⟩ := h
  refine ⟨Omega, hOo, hKO, hOk, ne_univ_of_isCompact_closure hX hOk, hsc, fun p hp => ?_⟩
  rcases hfront p hp with ⟨E, c, hE, hreg, hcp, hside⟩ | ⟨E, c, hE, hreg, hcp, hside⟩
  · have hcd : ContDiffAt ℝ 1 (fun z : ℂ => E ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) :=
      hE.1.of_le (by norm_num)
    exact hasSectorBoundary_of_local_sublevel (W := Omega) (u := E)
      ((hcd.differentiableAt (by norm_num)).hasFDerivAt) hreg hside
  · have hcd : ContDiffAt ℝ 1 (fun z : ℂ => E ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) :=
      hE.1.of_le (by norm_num)
    exact hasSectorBoundary_of_local_superlevel (W := Omega) (u := E)
      ((hcd.differentiableAt (by norm_num)).hasFDerivAt) hreg hside

/-! ## Filled regions admit no escaping disc

The point-set heart of one-endedness.  A region `W` is *filled* when every connected component of
its complement has non-compact closure (the output of "filling the relatively compact complementary
components").  Such a region swallows every embedded closed disc whose frontier lies in it: an
escaping disc `D` (with `frontier D ⊆ W` but `D ⊄ W`) would trap a component `Z` of `Wᶜ` in the
closed disc `D`, because `Z` cannot cross `frontier D ⊆ W`; `closure Z ⊆ D` would then be compact,
contradicting filledness.

This is a genuine new brick of the ABS/Hubbard engulfing argument: it is the reason why a *filled*
region cannot fail to be simply connected "through a hole", and it reduces that failure entirely to
the existence of an escaping disc, i.e. to the handle/level-set structure of the region. -/

/-- **A filled region contains every embedded closed disc whose frontier lies in it.** -/
theorem subset_of_filled_of_isDisc_frontier_subset {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] {W D : Set X}
    (hfilled : ∀ x ∈ Wᶜ, ¬ IsCompact (closure (connectedComponentIn Wᶜ x)))
    (hD : Nonempty (Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D))
    (hfr : frontier D ⊆ W) : D ⊆ W := by
  obtain ⟨e⟩ := hD
  have hDc : IsCompact D := isCompact_discDisc e
  have hclint : closure (interior D) = D := by
    rw [(disc_interior_invariance e).1]
    exact closure_discMap_image_ball e
  have hfre : frontier D = D \ interior D := by
    rw [← closure_sdiff_interior, hDc.isClosed.closure_eq]
  intro x hxD
  by_contra hxW
  -- the component `Z` of `Wᶜ` through `x`
  have hxZ : x ∈ connectedComponentIn Wᶜ x := mem_connectedComponentIn hxW
  have hZp : IsPreconnected (connectedComponentIn Wᶜ x) := isPreconnected_connectedComponentIn
  have hZsub : connectedComponentIn Wᶜ x ⊆ Wᶜ := connectedComponentIn_subset Wᶜ x
  -- `x` is an interior point of `D`
  have hxint : x ∈ interior D := by
    by_contra hcon
    exact (fun h => hxW (hfr h)) (by rw [hfre]; exact ⟨hxD, hcon⟩)
  -- `Z` cannot meet the frontier of `D`, which is contained in `W`
  have hZsub2 : connectedComponentIn Wᶜ x ⊆ interior D ∪ Dᶜ := by
    intro y hy
    by_cases hyint : y ∈ interior D
    · exact Or.inl hyint
    · by_cases hyD : y ∈ D
      · exact absurd (hfr (by rw [hfre]; exact ⟨hyD, hyint⟩)) (hZsub hy)
      · exact Or.inr hyD
  have hZint : connectedComponentIn Wᶜ x ⊆ interior D :=
    hZp.subset_left_of_subset_union isOpen_interior hDc.isClosed.isOpen_compl
      ((disjoint_compl_right : Disjoint D Dᶜ).mono_left interior_subset) hZsub2
      ⟨x, hxZ, hxint⟩
  -- hence the closure of `Z` is compact, contradicting filledness
  have hclZ : closure (connectedComponentIn Wᶜ x) ⊆ D := by
    rw [← hclint]
    exact closure_mono hZint
  exact hfilled x hxW (hDc.of_isClosed_subset isClosed_closure hclZ)

section InjectivCentre

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- **§BG.2's enumeration condition.**  The finite chart-ball cover of a compact set can be indexed by
a family with **injective** centre map — equivalently, the same points of `K ∪ {x₀}` are not listed
twice.  This is what keeps three *coincident* balls from going through one boundary point downstream. -/
theorem exists_finite_chartBall_cover_injective {K : Set Y} (hK : IsCompact K) (x₀ : Y) :
    ∃ (n : ℕ) (hn : 0 < n) (z : Fin n → Y) (r : Fin n → ℝ),
      Function.Injective z ∧ (∀ i, 0 < r i) ∧
      (∀ i, Metric.closedBall ((chartAt ℂ (z i)) (z i)) (r i) ⊆ (chartAt ℂ (z i)).target) ∧
      K ∪ {x₀} ⊆ ⋃ i, Submission.chartBall (chartAt ℂ (z i)) ((chartAt ℂ (z i)) (z i)) (r i) := by
  classical
  obtain ⟨ρ, t, hρ, hsub, hcov⟩ := exists_finite_chartBall_cover
    (Y := Y) hK x₀
  have htne : t.Nonempty := by
    obtain ⟨z, hz⟩ : (K ∪ {x₀}).Nonempty := ⟨x₀, Or.inr rfl⟩
    obtain ⟨y, hy't, -⟩ := Set.mem_iUnion₂.mp (hcov hz)
    exact ⟨y, hy't⟩
  let t' : Finset Y := t.image (fun y : ↥(K ∪ {x₀}) => (y : Y))
  let e : ↥t' ≃ Fin t'.card := t'.equivFin
  refine ⟨t'.card, Finset.card_pos.mpr (htne.image _), fun i => ((e.symm i : ↥t') : Y),
    fun i => ρ ((e.symm i : ↥t') : Y), ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have h1 : ((e.symm i : ↥t') : Y) = ((e.symm j : ↥t') : Y) := hij
    have h2 : (e.symm i : ↥t') = (e.symm j : ↥t') := Subtype.ext h1
    have h3 : e.symm i = e.symm j := h2
    exact e.symm.injective h3
  · exact fun i => hρ _
  · exact fun i => hsub _
  · intro z hz
    obtain ⟨y, hy't, hyz⟩ := Set.mem_iUnion₂.mp (hcov hz)
    have hymem : (y : Y) ∈ t' := Finset.mem_image.mpr ⟨y, hy't, rfl⟩
    refine Set.mem_iUnion.mpr ⟨e ⟨(y : Y), hymem⟩, ?_⟩
    have hsymm : ((e.symm (e ⟨(y : Y), hymem⟩) : ↥t') : Y) = (y : Y) := by
      rw [Equiv.symm_apply_apply]
    simp only [hsymm]
    exact hyz

end InjectivCentre

section BeadingStep

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- **The atomic beading step.**  Every point of an open set lies in a chart ball *with room* that is
contained in that open set.  This is the placement used at every step of the beading walk: given the
next source `V` and a point `p` of it (typically a point of the previous ball, chosen in the
intersection), put the new ball inside `V` around `p`. -/
theorem exists_chartBall_subset_of_mem {V : Set Y} (hV : IsOpen V) {p : Y} (hp : p ∈ V) :
    ∃ (c : OpenPartialHomeomorph Y ℂ) (a : ℂ) (ρ : ℝ), c ∈ atlas ℂ Y ∧ 0 < ρ ∧
      Metric.closedBall a ρ ⊆ c.target ∧ p ∈ Submission.chartBall c a ρ ∧
      Submission.chartBall c a ρ ⊆ V := by
  classical
  obtain ⟨ρ₁, hρ₁, hroom⟩ := Work.SimplyConnected.ABS.exists_radius_chartAt (Y := Y) p
  have hV' : V ∩ (chartAt ℂ p).source ∈ nhds p :=
    (hV.inter (chartAt ℂ p).open_source).mem_nhds ⟨hp, mem_chart_source ℂ p⟩
  obtain ⟨ρ₂, hρ₂, hsub⟩ := Metric.mem_nhds_iff.mp
    ((chartAt ℂ p).image_mem_nhds (mem_chart_source ℂ p) hV')
  set ρ : ℝ := min ρ₁ ρ₂ / 2 with hρdef
  have hρpos : 0 < ρ := half_pos (lt_min hρ₁ hρ₂)
  have hρle₁ : ρ ≤ ρ₁ :=
    (div_le_self (le_of_lt (lt_min hρ₁ hρ₂)) (by norm_num : (1:ℝ) ≤ 2)).trans (min_le_left _ _)
  have hρlt₂ : ρ < ρ₂ := by
    rw [hρdef, div_lt_iff₀ two_pos]
    linarith [min_le_right ρ₁ ρ₂, hρ₂]
  refine ⟨chartAt ℂ p, (chartAt ℂ p) p, ρ, chart_mem_atlas ℂ p, hρpos,
    (Metric.closedBall_subset_closedBall hρle₁).trans hroom, ?_, ?_⟩
  · exact Submission.mem_chartBall.mpr ⟨mem_chart_source ℂ p, by
      rw [Metric.mem_ball, dist_self]
      exact hρpos⟩
  · rintro x hx
    obtain ⟨hxsrc, hxb⟩ := Submission.mem_chartBall.mp hx
    have hxb' : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) ρ₂ :=
      Metric.ball_subset_ball hρlt₂.le hxb
    obtain ⟨v, ⟨hvV, hvsrc⟩, hvx⟩ := hsub hxb'
    have : v = x := (chartAt ℂ p).injOn hvsrc hxsrc hvx
    exact this ▸ hvV

/-- **The beading attachment.**  An open set `V` (the next source of the walk) meeting a set `B` (the
previous ball) contains a chart ball *with room* that meets `B`.  This is the step iterated along the
`ReflTransGen` enumeration of section BG.8 of the status notes: the ball is placed at the chosen point
of `B ∩ V`, so it is both inside `V` and meets `B`. -/
theorem exists_chartBall_attach_of_inter_nonempty {B V : Set Y} (hV : IsOpen V)
    (h : (B ∩ V).Nonempty) :
    ∃ (c : OpenPartialHomeomorph Y ℂ) (a : ℂ) (ρ : ℝ), c ∈ atlas ℂ Y ∧ 0 < ρ ∧
      Metric.closedBall a ρ ⊆ c.target ∧ Submission.chartBall c a ρ ⊆ V ∧
      (Submission.chartBall c a ρ ∩ B).Nonempty := by
  obtain ⟨p, hpB, hpV⟩ := h
  obtain ⟨c, a, ρ, hc, hρ, hroom, hpmem, hsub⟩ :=
    exists_chartBall_subset_of_mem (Y := Y) hV hpV
  exact ⟨c, a, ρ, hc, hρ, hroom, hsub, ⟨p, hpmem, hpB⟩⟩

end BeadingStep

section BeadingSuccessor

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- **The successor step of the beading walk.**  Let `q` be a point of `B` inside the next source `V`
(the point chosen on the sphere of the previous ball), and let `S` be the finitely many *closed* sets
(the closures of the other balls of the family) that avoid `q`.  Then there is a chart ball with room,
inside `V`, containing `q`, meeting `B`, and **disjoint from every member of `S`** — so the new ball
meets no earlier ball except its parent, which is exactly the invariant the walk maintains. -/
theorem exists_chartBall_attach_avoiding {B V : Set Y} (hV : IsOpen V) {q : Y} (hqB : q ∈ B)
    (hqV : q ∈ V) (S : Finset (Set Y)) (hS : ∀ F ∈ S, IsClosed F ∧ q ∉ F) :
    ∃ (c : OpenPartialHomeomorph Y ℂ) (a : ℂ) (ρ : ℝ), c ∈ atlas ℂ Y ∧ 0 < ρ ∧
      Metric.closedBall a ρ ⊆ c.target ∧ Submission.chartBall c a ρ ⊆ V ∧
      q ∈ Submission.chartBall c a ρ ∧ (Submission.chartBall c a ρ ∩ B).Nonempty ∧
      (∀ F ∈ S, Disjoint (Submission.chartBall c a ρ) F) := by
  classical
  have hSopen : IsOpen (V ∩ ⋂ F ∈ S, Fᶜ) :=
    hV.inter (isOpen_biInter_finset fun F hF => (hS F hF).1.isOpen_compl)
  have hq : q ∈ V ∩ ⋂ F ∈ S, Fᶜ :=
    ⟨hqV, Set.mem_iInter₂.mpr fun F hF => (hS F hF).2⟩
  obtain ⟨c, a, ρ, hc, hρ, hroom, hqmem, hsub⟩ :=
    exists_chartBall_subset_of_mem (Y := Y) hSopen hq
  refine ⟨c, a, ρ, hc, hρ, hroom, fun x hx => (hsub hx).1, hqmem, ⟨q, hqmem, hqB⟩, ?_⟩
  intro F hF
  rw [Set.disjoint_left]
  intro x hxball hxF
  exact (Set.mem_iInter₂.mp (hsub hxball).2 F hF) hxF

end BeadingSuccessor

/-! ## The canonical relatively compact region with the sector condition

Every compact `K` of a non-compact `ℂ`-charted surface lies in an open, connected, relatively compact
`Ω ≠ univ` with the *sector* (cone) condition at every frontier point, constructed from the smooth
exhaustion function of the ABS proof:

* `g` is the `C^∞` proper exhaustion function (`OneEnded.exists_contMDiff_sublevel_compact`, the
  partition-of-unity sum `∑ χ n · (lvl n + 1)` of Anghel--Bruin--Stan Theorem 12);
* `C₀` is a level with `K ∪ {x₀} ⊆ connectedComponentIn {g < C₀} x₀`
  (`green_reduction.exists_component_sublevel_supset`);
* `C > C₀` is a *regular* level on `{g ≤ C₀ + 1}`
  (`green_reduction.exists_regular_level_of_contMDiff`, Sard-lite for a `C^∞` function on a surface);
* `Ω := connectedComponentIn {g < C} x₀`.

`Ω` is open and preconnected, its closure is compact (it is contained in the compact sub-level set
`{g ≤ C}`), `Ω ≠ univ` since `X` is non-compact, `K ⊆ Ω` by monotonicity in `C`, and the *sector
condition* holds at every frontier point: such a frontier point realises the level (`g p = C`), the
chart pull-back of `g` there is differentiable with non-zero derivative (`C` is a regular level), and
the component is locally contained in the sub-level set, so `hasSectorBoundary_of_local_sublevel`
applies.

The only thing this construction does **not** give is the simple connectivity of `Ω`: that is the
residual obligation of the parabolic case (see `region_with_sector_boundary_of_sectorRegion` above,
which closes the target as soon as the region produced here — or any other such region — is simply
connected). -/

/-- **A point of an open set lying in the closure of a connected component lies in it.** -/
theorem mem_connectedComponentIn_of_mem_closure_of_sublevel [LocallyConnectedSpace X] {U : Set X} (hUo : IsOpen U)
    {x₀ y : X} (hx₀U : x₀ ∈ U) (hyU : y ∈ U) (hy : y ∈ closure (connectedComponentIn U x₀)) :
    y ∈ connectedComponentIn U x₀ := by
  obtain ⟨V, ⟨hVopen, hyV, hVconn⟩, hVsub⟩ :=
    (LocallyConnectedSpace.open_connected_basis y).mem_iff.mp (hUo.mem_nhds hyU)
  obtain ⟨z, hzV, hzA⟩ := mem_closure_iff.mp hy V hVopen hyV
  have hpre : IsPreconnected (V ∪ connectedComponentIn U x₀) :=
    IsPreconnected.union' ⟨z, hzV, hzA⟩ hVconn.isPreconnected
      isPreconnected_connectedComponentIn
  have hsub : V ∪ connectedComponentIn U x₀ ⊆ U := by
    rintro w (hw | hw)
    · exact hVsub hw
    · exact connectedComponentIn_subset U x₀ hw
  exact hpre.subset_connectedComponentIn (Or.inr (mem_connectedComponentIn hx₀U)) hsub
    (Or.inl hyV)

/-- **A frontier point of a component of an open sub-level set realises the level.** -/
theorem eq_of_mem_frontier_connectedComponentIn_sublevel [LocallyConnectedSpace X] {g : X → ℝ}
    (hgcont : Continuous g) {C : ℝ} {x₀ p : X}
    (hx₀ : x₀ ∈ connectedComponentIn {x : X | g x < C} x₀)
    (hp : p ∈ frontier (connectedComponentIn {x : X | g x < C} x₀)) : g p = C := by
  have hUo : IsOpen {x : X | g x < C} := isOpen_lt hgcont continuous_const
  have hAle : closure (connectedComponentIn {x : X | g x < C} x₀) ⊆ {x : X | g x ≤ C} :=
    closure_minimal
      (fun y hy => show g y ≤ C from
        le_of_lt (connectedComponentIn_subset {x : X | g x < C} x₀ hy))
      (isClosed_le hgcont continuous_const)
  refine le_antisymm (hAle hp.1) ?_
  by_contra hcon
  rw [not_le] at hcon
  have hAopen : IsOpen (connectedComponentIn {x : X | g x < C} x₀) := hUo.connectedComponentIn
  have hpA : p ∉ connectedComponentIn {x : X | g x < C} x₀ := by
    have h := hp
    rw [hAopen.frontier_eq] at h
    exact h.2
  have hx₀U : x₀ ∈ {x : X | g x < C} := connectedComponentIn_subset {x : X | g x < C} x₀ hx₀
  exact hpA (mem_connectedComponentIn_of_mem_closure_of_sublevel hUo hx₀U hcon hp.1)

/-- **The sector condition at a regular level of a sub-level component.** -/
theorem hasSectorBoundary_of_local_sublevel_component [LocallyConnectedSpace X] {g : X → ℝ} {C : ℝ}
    {x₀ : X} (hx₀ : x₀ ∈ connectedComponentIn {x : X | g x < C} x₀) (hcont : Continuous g)
    (hreg : ∀ p : X, g p = C →
      DifferentiableAt ℝ (fun z : ℂ => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) ∧
      fderiv ℝ (fun z : ℂ => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) ≠ 0) :
    ∀ p ∈ frontier (connectedComponentIn {x : X | g x < C} x₀),
      Work.SimplyConnected.ABS.HasSectorBoundary (connectedComponentIn {x : X | g x < C} x₀) p := by
  intro p hp
  have hgp : g p = C := eq_of_mem_frontier_connectedComponentIn_sublevel hcont hx₀ hp
  obtain ⟨hdiff, hfd⟩ := hreg p hgp
  refine hasSectorBoundary_of_local_sublevel
    (W := connectedComponentIn {x : X | g x < C} x₀) (u := g)
    (L := fderiv ℝ (fun z : ℂ => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p))
    hdiff.hasFDerivAt hfd ?_
  refine Filter.Eventually.of_forall fun y hy => ?_
  rw [hgp]
  exact not_lt.mpr (le_of_lt (connectedComponentIn_subset {x : X | g x < C} x₀ hy))

/-- **A relatively compact region with the cone condition, containing every compact set.**

This is the *unconditional* geometric half of the target: the only missing ingredient for
`region_with_sector_boundary` in the parabolic case is the simple connectivity of the region
produced here. -/
theorem exists_precompact_sectorRegion (hX : ¬ CompactSpace X) (K : Set X) (hK : IsCompact K) :
    ∃ Ω : Set X, IsOpen Ω ∧ IsConnected Ω ∧ Ω ≠ Set.univ ∧ IsCompact (closure Ω) ∧ K ⊆ Ω ∧
      ∀ p ∈ frontier Ω, Work.SimplyConnected.ABS.HasSectorBoundary Ω p := by
  classical
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  obtain ⟨g, hgsm, -, hgsub⟩ :=
    Work.SimplyConnected.ABS.OneEnded.exists_contMDiff_sublevel_compact (X := X) hX
  have hgcont : Continuous g := hgsm.continuous
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨C₀, hC₀⟩ :=
    Work.SimplyConnected.ABS.green_reduction.exists_component_sublevel_supset (X := X) hgcont hK x₀
  obtain ⟨C, hC₁, hC₂, hreg⟩ :=
    Work.SimplyConnected.ABS.green_reduction.exists_regular_level_of_contMDiff (X := X) hgsm
      (hgsub (C₀ + 1)) x₀ (C₀ := C₀)
  have hmono : connectedComponentIn {x : X | g x < C₀} x₀ ⊆
      connectedComponentIn {x : X | g x < C} x₀ :=
    connectedComponentIn_mono x₀ fun y hy => lt_of_lt_of_le hy (le_of_lt hC₁)
  have hx₀C : x₀ ∈ connectedComponentIn {x : X | g x < C} x₀ := hmono (hC₀ (Or.inr rfl))
  have hKC : K ⊆ connectedComponentIn {x : X | g x < C} x₀ := fun y hy => hmono (hC₀ (Or.inl hy))
  have hcl : IsCompact (closure (connectedComponentIn {x : X | g x < C} x₀)) :=
    (hgsub C).of_isClosed_subset isClosed_closure
      (closure_minimal
        (fun y hy => show g y ≤ C from
          le_of_lt (connectedComponentIn_subset {x : X | g x < C} x₀ hy))
        (isClosed_le hgcont continuous_const))
  refine ⟨connectedComponentIn {x : X | g x < C} x₀, ?_, ⟨⟨x₀, hx₀C⟩,
    isPreconnected_connectedComponentIn⟩, ne_univ_of_isCompact_closure hX hcl, hcl, hKC, ?_⟩
  · exact (isOpen_lt hgcont continuous_const).connectedComponentIn
  · refine hasSectorBoundary_of_local_sublevel_component hx₀C hgcont fun p hp => ?_
    exact hreg p (by rw [Set.mem_ofPred_eq]; exact le_trans (le_of_eq hp) hC₂) hp

end Work.SimplyConnected.ABS

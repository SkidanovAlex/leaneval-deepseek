import Mathlib
import Submission.Work.SimplyConnected.ABS.regBouligand
import Submission.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Work.SimplyConnected.ABS.clampedBarrierDefs
import Submission.Work.SimplyConnected.ABS.regionSweepBarrier
import Submission.Work.SimplyConnected.ABS.barrierMemberRegion
import Submission.Work.Modulus.BranchCovering.coveringAux
import Submission.Work.SimplyConnected.ABS.globalizedBarrier_dev
import Submission.Work.SimplyConnected.ABS.globalBarrierOfClampedCollar
import Submission.Work.SimplyConnected.ABS.limEnvelopeLeSmulOfBarrierRegion
import Submission.Commons.Analysis.Complex.Harmonic.dirichlet_circle_boundary
import Submission.Work.SimplyConnected.Perron.globalizedBarrier

/-!
# A global barrier from a local barrier (regularity form)

The target theorem `globalBarrierOfLocalBarrierReg` is the classical statement that a *local
barrier* at a boundary point `p` of an open set `Ω` in a Riemann surface forces a *global*
barrier: a superharmonic `w > 0` on `Ω`, bounded by `1`, with `w → 0` at `p` along `Ω`
(equivalently: `p` is a Dirichlet-regular boundary point).

## The classical proof (Ivrii, "Perron's Method", Bouligand's Lemma 2; Tolsa, *Harmonic
measure*, Theorem 5.37)

Write `c := chartAt ℂ p`, `a := c p`, and shrink `V` to a chart ball `Δ = chartBall c a ρ` with
`chartClosedBall c a ρ ⊆ V` (so that `u` is defined and continuous on the sphere `∂Δ`).

1. *The bad set.*  For `m > 0` put `L_m := {ξ ∈ Ω ∩ ∂Δ : u ξ < m}`.  Since `u > 0` on `Ω ∩ ∂Δ`
   and `u` is continuous there, `L_m ↓ ∅` as `m ↓ 0`; `L_m` is relatively open in the sphere,
   hence measurable, so its arc length `|L_m| → 0`.

2. *The datum.*  Choose `m, δ > 0` with `(|L_m| + 2δ)/(2π) < η` and let `g` be a continuous
   function on the sphere with `0 ≤ g ≤ 1`, `g = 1` on `L_m` and `g = 0` off the
   `δ`-neighbourhood of `L_m` (a "tent" over `L_m`).  Then the *mean* of `g` is
   `≤ (|L_m| + 2δ)/(2π) < η`.

3. *The harmonic function.*  Let `h` be the Poisson extension of `g` to `Δ` (the workspace has
   the Poisson integral and the Dirichlet solution on a circle,
   `Commons.Analysis.Complex.Harmonic.dirichlet_circle_boundary`).  Then `h` is harmonic on `Δ`,
   continuous on the closed ball, equal to `g` on the sphere, and — the key point — its value at
   the centre `p` equals the circle average of `g` (the Poisson kernel is constant there), so
   `h p ≤ η`.

4. *Gluing.*  `b₁ := -u/m - C h` (with `C ≥ 1`) is subharmonic on `Ω ∩ Δ`; on the collar
   `Ω ∩ ∂Δ` one has `b₁ ≤ -1` (where `u < m` because `h = g = 1` there, and where `u ≥ m`
   because `-u/m ≤ -1`).  Hence `b := max b₁ (-1)` on `Ω ∩ Δ`, extended by `-1` outside `Δ`,
   is subharmonic on `Ω`, with `-1 ≤ b < 0` and `limsup_{z→p} b z ≤ η` (since `b ≤ -u/m` and
   `u → 0` at `p`).

5. *Conclusion.*  `w := min (-b) 1` is superharmonic on `Ω` (negation, then the clamp lemma),
   `0 < w ≤ 1`, and `w → 0` at `p`.  This last step is the lemma
   `globalBarrier_of_subharmonicDecay` below.

## Obstruction to the elementary routes (recorded for the record)

The naive route — compare a member `v` of the Perron family with `ε + C·u` on `Ω ∩ B` and apply
the maximum principle — needs `C·u ≥ M` on `Ω ∩ ∂B`, i.e. `u` bounded below on the collar.  This
**fails in general**: for the slit plane (`X = ℂ`, `Ω = ℂ ∖ (-∞,0]`, `p = 0`, `u = Re √z`) the
infimum of `u` over `Ω ∩ ∂B` is `0` for every ball `B` around `p`.  Likewise the clamped barrier
`min (u ·) c` glued to the constant `c` outside `V` is not superharmonic at `Ω ∩ ∂V` when `u` is
small there.  The harmonic-measure argument of step 3 is what repairs both failures: the "bad
set" is the part of the *collar* (where `u > 0`), not the part of the *boundary* (where `u` may
vanish), so its measure shrinks to `0`.

Nothing of mathematical substance lives in this file's imports.
-/

open Filter Set
open Classical
open scoped Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The final assembly.**  A *subharmonic* function `b` on `Ω` with `-1 ≤ b < 0`, vanishing at
`p`, yields the target global barrier `w := min (-b) 1`: `-b` is superharmonic, positive and
vanishes at `p`, and the clamp with `1` preserves all of that. -/
theorem globalBarrier_of_subharmonicDecay {Ω : Set X} {p : X} {b : X → ℝ}
    (hb : Submission.SubharmonicOnX b Ω) (hneg : ∀ x ∈ Ω, b x < 0)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ nhds p ∧ ∀ x ∈ Ω ∩ N, -ε < b x) :
    ∃ w : X → ℝ, Submission.SuperharmonicOnX w Ω ∧ (∀ x ∈ Ω, 0 < w x) ∧
      (∀ x ∈ Ω, w x ≤ 1) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ nhds p ∧ ∀ x ∈ Ω ∩ N, w x < ε) := by
  have hsup : Submission.SuperharmonicOnX (fun x => -b x) Ω := hb.neg
  have hmin : Submission.SuperharmonicOnX (fun x => min (-b x) 1) Ω :=
    Work.SimplyConnected.ABS.SuperharmonicOnX.inf_const_dev hsup 1
  refine ⟨fun x => min (-b x) 1, hmin, ?_, ?_, ?_⟩
  · intro x hx
    exact lt_min (neg_pos.mpr (hneg x hx)) one_pos
  · intro x hx
    exact min_le_right (-b x) 1
  · intro ε hε
    by_cases h1 : ε ≤ 1
    · obtain ⟨N, hN, hNsub⟩ := hdecay ε hε
      refine ⟨N, hN, fun x hx => ?_⟩
      have : -b x < ε := by linarith [hNsub x hx]
      exact lt_of_le_of_lt (min_le_left (-b x) 1) this
    · push_neg at h1
      refine ⟨Set.univ, Filter.univ_mem, fun x _ => ?_⟩
      exact lt_of_le_of_lt (min_le_right (-b x) 1) h1

/-! ## The chart-and-radii setup for the Perron/hitting-probability route

The construction of the global barrier from a local barrier needs a chart disc around `p` that is
small enough that (i) its closed chart disc sits in the target of the chart and (ii) it is contained
in the barrier neighbourhood `V`.  This is pure bookkeeping, isolated here. -/

/-- **Chart data at a point of an open set.**  If `V` is an open neighbourhood of `p` then there is
`ρ₂ > 0` such that the closed Euclidean ball of radius `ρ₂` around `(chartAt ℂ p) p` lies in the
chart target and the corresponding closed *chart* disc lies in `V`. -/
theorem exists_chartClosedBall_subset_nhds {V : Set X} (hVo : IsOpen V) {p : X} (hpV : p ∈ V) :
    ∃ ρ₂ : ℝ, 0 < ρ₂ ∧
      Metric.closedBall ((chartAt ℂ p) p) ρ₂ ⊆ (chartAt ℂ p).target ∧
      Submission.chartClosedBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ₂ ⊆ V := by
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let a : ℂ := c p
  have hxsrc : p ∈ c.source := mem_chart_source ℂ p
  -- a Euclidean ball around `a` inside the chart target
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ :=
    Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source hxsrc))
  -- a Euclidean ball around `a` mapping into `V` under `c.symm`
  have hpV' : V ∈ nhds (c.symm a) := by
    rw [c.left_inv hxsrc]
    exact hVo.mem_nhds hpV
  obtain ⟨ρ₂', hρ₂', hρ₂'sub⟩ :=
    Metric.mem_nhds_iff.mp
      ((c.continuousAt_symm (c.map_source hxsrc)).preimage_mem_nhds hpV')
  refine ⟨min ρ₁ ρ₂' / 2, half_pos (lt_min hρ₁ hρ₂'), ?_, ?_⟩
  · intro z hz
    refine hρ₁sub ?_
    have hz' : ‖z - a‖ ≤ min ρ₁ ρ₂' / 2 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    rw [Metric.mem_ball, dist_eq_norm]
    have : min ρ₁ ρ₂' / 2 < ρ₁ := by
      have := min_le_left ρ₁ ρ₂'
      linarith
    linarith
  · intro x hx
    obtain ⟨hxsrc, hxcl⟩ := Submission.mem_chartClosedBall.mp hx
    have hx' : ‖c x - a‖ ≤ min ρ₁ ρ₂' / 2 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxcl
    have hmem : c x ∈ Metric.ball a ρ₂' := by
      rw [Metric.mem_ball, dist_eq_norm]
      have : min ρ₁ ρ₂' / 2 < ρ₂' := by
        have := min_le_right ρ₁ ρ₂'
        linarith
      linarith
    have := hρ₂'sub hmem
    rw [Set.mem_preimage] at this
    rwa [c.left_inv hxsrc] at this

/-- **The decay brick: the Perron envelope is dominated by the local barrier on a region.**

Let `U` be a preconnected relatively compact open set on which the local barrier `u` is
superharmonic and nonnegative, let `h` be the hitting probability of a chart ball around `p`
(abstracted here to: `h = 1` on `chartClosedBall c a ρ`) and `f := 1 - h`.  If the part of the
frontier of `U` where `u` can be small (`K`) is decomposed from the rest, and on that rest the
frontier lies in the chart ball where `h = 1`, then the Perron envelope of `f` over `U` is bounded
by `(1/m) · u`, where `m > 0` bounds `u` below on `K`.

This is the comparison step that converts `u → 0` at `p` into `ω → 0` at `p`; the frontier split is
exactly the one packaged in `limEnvelopeLeSmulOfBarrierRegion`. -/
theorem limEnvelope_one_sub_hitting_le_smul {Ω U : Set X} (hUo : IsOpen U) (hUpc : IsPreconnected U)
    (hcomp : IsCompact (closure U)) (hne : (frontier U).Nonempty)
    {h : X → ℝ} (hsub : Submission.SubharmonicOnX (fun x => 1 - h x) U)
    (hneF : (Submission.limFamily U (fun x => 1 - h x) 1).Nonempty)
    {u : X → ℝ} (hβ : Submission.SuperharmonicOnX u U) (hβ0 : ∀ x ∈ U, 0 ≤ u x)
    {K : Set X} (hKfr : K ⊆ frontier U) (hKcont : ∀ ζ ∈ K, ContinuousAt u ζ)
    {m : ℝ} (hm : 0 < m) (hmβ : ∀ ζ ∈ K, m ≤ u ζ)
    {ρ : ℝ} {p : X}
    (hfr : ∀ ζ ∈ frontier U, ζ ∉ K →
      ζ ∈ Submission.chartClosedBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ)
    (hh1 : ∀ ζ ∈ Submission.chartClosedBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ, h ζ = 1) :
    ∀ x ∈ U, Submission.limEnvelope U (fun x => 1 - h x) 1 x ≤ (1 / m) * u x := by
  refine limEnvelopeLeSmulOfBarrierRegion (U := U) hUo hUpc hcomp hne
    (M := 1) (f := fun x => 1 - h x) zero_le_one hneF hβ hβ0 hKfr hKcont hm hmβ ?_
  intro ζ hζfr hζnotK
  rw [hh1 ζ (hfr ζ hζfr hζnotK)]
  norm_num

/-- **A compact piece of the barrier collar carries a positive lower bound.**  If `K` is compact,
lies in `Ω ∩ V`, `u` is continuous on `V` and strictly positive on `Ω ∩ V`, then `u` is bounded
below by some `m > 0` on `K`.  This is the `m` of the frontier split in the decay brick
(`limEnvelope_one_sub_hitting_le_smul`): the caller produces a compact `K ⊆ frontier U ∩ Ω ∩ V`
(typically the part of the inner collar away from `p`). -/
theorem exists_pos_inf_of_compact_subset {Ω V K : Set X} {u : X → ℝ} (hKcomp : IsCompact K)
    (hKV : K ⊆ V) (hKΩ : K ⊆ Ω) (hcont : ContinuousOn u V)
    (hpos : ∀ x ∈ Ω ∩ V, 0 < u x) :
    ∃ m : ℝ, 0 < m ∧ ∀ ζ ∈ K, m ≤ u ζ := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, fun ζ hζ => absurd hζ (Set.notMem_empty ζ)⟩
  · obtain ⟨ζ₀, hζ₀K, hmin⟩ := hKcomp.exists_isMinOn hKne (hcont.mono hKV)
    exact ⟨u ζ₀, hpos ζ₀ ⟨hKΩ hζ₀K, hKV hζ₀K⟩, fun ζ hζ => hmin hζ⟩

/-! ## The compact collar piece `K`

The barrier comparison `limEnvelope_one_sub_hitting_le_smul` needs a compact set `K` on which the
local barrier `u` is bounded below by some `m > 0`, while its complement in the frontier is covered
by the chart ball where the hitting probability equals `1` (so that the Perron datum vanishes
there).  Both requirements are met by a single definition: take the part of the frontier at chart
radius at least `ρ_h` (away from the chart ball of `h`) which is also at distance at least `δ > 0`
from the complement of `Ω` (hence inside `Ω`, and away from both `p` and `frontier Ω`). -/

/-- **The compact collar piece.**  For a chart centre `p`, a radius `ρ_h` and a set `C` (the
caller supplies a *closed* `C ⊆ Ω` away from `p` and from `frontier Ω`, e.g. the complement of an
open neighbourhood of `frontier Ω`): the points of the frontier of `U` at chart distance at least
`ρ_h` from `(chartAt ℂ p) p` which lie in `C`. -/
noncomputable def collarPiece (Ω U C : Set X) (p : X) (ρ_h : ℝ) : Set X :=
  frontier U ∩ {x : X | ρ_h ≤ ‖(chartAt ℂ p) x - (chartAt ℂ p) p‖} ∩ C

theorem collarPiece_subset_frontier {Ω U C : Set X} {p : X} {ρ_h : ℝ} :
    collarPiece Ω U C p ρ_h ⊆ frontier U := fun _ hx => hx.1.1

theorem collarPiece_subset_closure {Ω U C : Set X} {p : X} {ρ_h : ℝ} :
    collarPiece Ω U C p ρ_h ⊆ closure U :=
  fun _ hx => frontier_subset_closure hx.1.1

/-- **`K` lies in `V`** as soon as the closure of `U` does. -/
theorem collarPiece_subset_of_closure_subset {Ω U C V : Set X} {p : X} {ρ_h : ℝ}
    (hUV : closure U ⊆ V) : collarPiece Ω U C p ρ_h ⊆ V :=
  fun x hx => hUV (frontier_subset_closure hx.1.1)

/-- **`K` lies in `Ω`** as soon as `C` does. -/
theorem collarPiece_subset_of_subset {Ω U C : Set X} {p : X} {ρ_h : ℝ} (hCΩ : C ⊆ Ω) :
    collarPiece Ω U C p ρ_h ⊆ Ω := fun _ hx => hCΩ hx.2

/-- **`p ∉ K`** — a consequence of the caller's choice of `C`, not of the geometry: if `C` avoids
`p` then so does the collar piece. -/
theorem not_mem_collarPiece_of_notMem {Ω U C : Set X} {p : X} {ρ_h : ℝ} (hp : p ∉ C) :
    p ∉ collarPiece Ω U C p ρ_h := fun h => hp h.2

/-- **`K` is disjoint from the frontier of `Ω`** — again a consequence of `C`: if `C ⊆ Ω` (and `Ω`
is open, so `Ω = interior Ω`), then no point of `K` can lie in `frontier Ω = closure Ω \ interior Ω`. -/
theorem disjoint_collarPiece_frontier {Ω U C : Set X} (hΩo : IsOpen Ω) {p : X} {ρ_h : ℝ}
    (hCΩ : C ⊆ Ω) : Disjoint (collarPiece Ω U C p ρ_h) (frontier Ω) := by
  rw [Set.disjoint_left]
  intro x hxK hxfr
  exact hxfr.2 (by rw [hΩo.interior_eq]; exact hCΩ hxK.2)

/-! ## Trap 2, first brick: the positive local clamp `min (u ·) 1`

The Perron envelope `ω` provides the decay at `p` but not the strict positivity (for `X = ℂ` it can
be identically `0`).  Positivity must come from the local barrier itself: the clamp `min (u ·) 1` is
superharmonic on `Ω ∩ V`, strictly positive there, bounded by `1`, and tends to `0` at `p`. -/

/-- **The clamped local barrier on `Ω ∩ V`.**  The pointwise minimum of the local barrier with `1`
inherits superharmonicity (`SuperharmonicOnX.inf_const_dev`), is strictly positive on `Ω ∩ V`,
bounded by `1`, and decays at `p` along `Ω`. -/
theorem localClamp_facts {Ω V : Set X} {u : X → ℝ} {p : X} (hVo : IsOpen V) (hpV : p ∈ V)
    (hsup : Submission.SuperharmonicOnX u (Ω ∩ V))
    (hpos : ∀ x ∈ Ω ∩ V, 0 < u x) (hcont : ContinuousOn u V) (hup : u p = 0) :
    Submission.SuperharmonicOnX (fun x => min (u x) 1) (Ω ∩ V) ∧
      (∀ x ∈ Ω ∩ V, 0 < min (u x) 1) ∧
      (∀ x ∈ Ω ∩ V, min (u x) 1 ≤ 1) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ nhds p ∧ ∀ x ∈ Ω ∩ V ∩ N, min (u x) 1 < ε) := by
  refine ⟨SuperharmonicOnX.inf_const_dev hsup 1, ?_, ?_, ?_⟩
  · intro x hx
    exact lt_min (hpos x hx) one_pos
  · intro x _
    exact min_le_right _ _
  · intro ε hε
    by_cases hε1 : ε ≤ 1
    · have hev : ∀ᶠ x in 𝓝 p, u x < ε :=
        (hcont.continuousAt (hVo.mem_nhds hpV)).eventually
          (isOpen_Iio.mem_nhds (by rw [hup]; exact hε))
      obtain ⟨N, hN, hNsub⟩ := Filter.eventually_iff_exists_mem.mp hev
      exact ⟨N, hN, fun x hx => lt_of_le_of_lt (min_le_left _ _) (hNsub x hx.2)⟩
    · push_neg at hε1
      exact ⟨Set.univ, Filter.univ_mem, fun x _ => lt_of_le_of_lt (min_le_right _ _) hε1⟩

/-! ## Trap 2, third brick: continuity of the clamp across the level set

The assembly glues along a level set of the local barrier `u`: on the side where `u ≤ c` one takes
the clamp `min (u ·) c`, on the other side the constant `c`, and the two agree exactly on
`{u = c}` — so the glued function is just `min (u ·) c`, which is continuous wherever `u` is.  The
two elementary facts behind that are isolated here. -/

/-- **Continuity of the clamp at a level point.**  If `u` is continuous at `ξ`, so is
`min (u ·) c`; on the level set `{u = c}` this is what makes the gluing of `min (u ·) c` with the
constant `c` continuous. -/
theorem continuousAt_min_const {u : X → ℝ} {ξ : X} (hu : ContinuousAt u ξ) (c : ℝ) :
    ContinuousAt (fun x : X => min (u x) c) ξ :=
  hu.min continuousAt_const

/-- **The clamp is the constant on the level set and beyond.**  For `x` with `c ≤ u x` the clamp
equals `c`, so the glued function and the outside constant agree there. -/
theorem min_const_eq_right_of_le {u : X → ℝ} {c : ℝ} {x : X} (h : c ≤ u x) :
    min (u x) c = c := min_eq_right h

/-- **The clamp equals `u` below the level.**  For `x` with `u x ≤ c` the clamp is `u x`, so on the
side where the barrier is small the glued function is the barrier itself (hence superharmonic
there). -/
theorem min_const_eq_left_of_le {u : X → ℝ} {c : ℝ} {x : X} (h : u x ≤ c) :
    min (u x) c = u x := min_eq_left h

/-! ## Trap 2, fourth brick: sums of superharmonic functions

Superharmonicity is closed under addition (the circle MVI is reversed, so `Real.circleAverage_add`
applies with the inequalities in the same direction over a common sum).  Rather than redo the chart
bookkeeping, this is deduced from the *proven* `SubharmonicOnX.add` by negation. -/

/-- **Sums of superharmonic functions are superharmonic.** -/
theorem SuperharmonicOnX.add' {u v : X → ℝ} {U : Set X} (hu : Submission.SuperharmonicOnX u U)
    (hv : Submission.SuperharmonicOnX v U) :
    Submission.SuperharmonicOnX (fun x => u x + v x) U := by
  have h := (hu.neg).add (hv.neg)
  convert h.neg using 1
  funext x
  ring

/-- **Scaling a superharmonic function by a nonnegative constant.**  (The library
`Submission.SuperharmonicOnX.const_mul` carries a spurious `[PreconnectedSpace X]`; this is the
direct proof.) -/
theorem SuperharmonicOnX.const_mul' {u : X → ℝ} {U : Set X} {k : ℝ} (hk : 0 ≤ k)
    (hu : Submission.SuperharmonicOnX u U) :
    Submission.SuperharmonicOnX (fun x => k * u x) U := by
  refine ⟨hu.1.const_mul k, fun x hx => ?_⟩
  obtain ⟨hxsrc, ρh, hρh, htgt, hch, hmvh⟩ := hu.2 x hx
  have hfun : (fun y : X => k * u y) ∘ (chartAt ℂ x).symm
      = fun w => k * ((u ∘ (chartAt ℂ x).symm) w) := rfl
  refine ⟨hxsrc, ρh, hρh, htgt, ?_, ?_⟩
  · rw [hfun]
    exact hch.const_mul k
  · intro p hp r hr hpr
    have hca : Real.circleAverage (fun w : ℂ => k * ((u ∘ (chartAt ℂ x).symm) w)) p r
        = k * Real.circleAverage ((u ∘ (chartAt ℂ x).symm)) p r := by
      simpa using Real.circleAverage_fun_smul
        (f := (u ∘ (chartAt ℂ x).symm)) (a := k) (c := p) (R := r)
    rw [hfun, hca]
    exact mul_le_mul_of_nonneg_left (hmvh p hp r hr hpr) hk

/-- **Obligation 1 of the assembly.**  The merged function
`W := min (ω + ε · min (u ·) c, 1)` is superharmonic on `Ω ∩ V` whenever `ω` is superharmonic on
`Ω`, `u` is superharmonic on `Ω ∩ V`, and `0 ≤ ε`, `0 ≤ c`: the clamp `min (u ·) c` is
superharmonic by `inf_const_dev`, scaled by `const_mul'`, added to `ω` by `add'`, and clamped at
`1` again by `inf_const_dev`. -/
theorem assembly_clamp_superharmonic {Ω V : Set X} {u ω : X → ℝ} {c ε : ℝ}
    (hsup : Submission.SuperharmonicOnX u (Ω ∩ V))
    (hω : Submission.SuperharmonicOnX ω Ω) (hc : 0 ≤ c) (hε : 0 ≤ ε) :
    Submission.SuperharmonicOnX (fun x => min (ω x + ε * min (u x) c) 1) (Ω ∩ V) := by
  have hmono : Submission.SuperharmonicOnX ω (Ω ∩ V) :=
    ⟨hω.1.mono Set.inter_subset_left, fun x hx => hω.2 x hx.1⟩
  have h1 : Submission.SuperharmonicOnX (fun x => min (u x) c) (Ω ∩ V) :=
    SuperharmonicOnX.inf_const_dev hsup c
  have h2 : Submission.SuperharmonicOnX (fun x => ε * min (u x) c) (Ω ∩ V) :=
    SuperharmonicOnX.const_mul' hε h1
  have h3 : Submission.SuperharmonicOnX (fun x => ω x + ε * min (u x) c) (Ω ∩ V) :=
    SuperharmonicOnX.add' hmono h2
  exact SuperharmonicOnX.inf_const_dev h3 1

/-! ## Trap 2, obligation 2: the collar identification

At a collar point the Perron envelope vanishes (`h = 1` there, and `ω ≤ (1/m)·u → 0`), so the merged
function `W := min (ω + ε·min (u ·) c, 1)` reduces to the clamped barrier alone; and where moreover
`u ≥ c` it is the *constant* `min (ε·c) 1`, matching the outside piece.  These two identifications
are the interface of the gluing. -/

/-- **The envelope drops out where it vanishes.** -/
theorem assembly_clamp_of_envelope_zero {u ω : X → ℝ} {c ε : ℝ} {x : X} (hωx : ω x = 0) :
    min (ω x + ε * min (u x) c) 1 = min (ε * min (u x) c) 1 := by
  rw [hωx, zero_add]

/-- **The merged function is the outside constant on the far side of the level set.** -/
theorem assembly_clamp_of_envelope_zero_of_le {u ω : X → ℝ} {c ε : ℝ} {x : X} (hωx : ω x = 0)
    (hux : c ≤ u x) :
    min (ω x + ε * min (u x) c) 1 = min (ε * c) 1 := by
  rw [assembly_clamp_of_envelope_zero hωx, min_const_eq_right_of_le hux]

/-! ## Trap 2, obligation 3: the two gluing pieces

The global barrier is glued from `Ω ∩ V` (where the clamped barrier gives positivity and the
superharmonicity of obligation 1) and `Ω \ N` for a neighbourhood `N ∋ p` with `N ⊆ V` (where `p`
is absent, so the constant `c` does the job).  The cover and the openness are the only set-theoretic
inputs. -/

/-- **The two pieces cover `Ω`.** -/
theorem subset_union_inter_sdiff {Ω V N : Set X} (hNV : N ⊆ V) :
    Ω ⊆ (Ω ∩ V) ∪ (Ω \ N) := by
  intro x hx
  by_cases hxN : x ∈ N
  · exact Or.inl ⟨hx, hNV hxN⟩
  · exact Or.inr ⟨hx, hxN⟩


/-- **The away-from-`p` piece is open.**  Subtracting a *closed* set keeps openness: the piece away
from `p` is taken to be `Ω \ closure N`, which is open because `closure N` is closed. -/
theorem isOpen_sdiff_closure {N Ω : Set X} (hΩ : IsOpen Ω) : IsOpen (Ω \ closure N) :=
  hΩ.sdiff isClosed_closure

/-- **The two pieces cover `Ω`** (open form, with the closed piece `closure N`). -/
theorem subset_union_inter_sdiff_closure {Ω V N : Set X} (hNV : closure N ⊆ V) :
    Ω ⊆ (Ω ∩ V) ∪ (Ω \ closure N) := by
  intro x hx
  by_cases hxN : x ∈ closure N
  · exact Or.inl ⟨hx, hNV hxN⟩
  · exact Or.inr ⟨hx, hxN⟩

/-- **The constant piece.**  On the away-from-`p` piece `Ω \ closure N` the constant `c` is
superharmonic (constants are superharmonic on any set), positive for `c > 0`, and `≤ 1` for `c ≤ 1`;
no decay is asked for there since `N` is a neighbourhood of `p`. -/
theorem const_superharmonic_on_sdiff (N Ω : Set X) (c : ℝ) :
    Submission.SuperharmonicOnX (fun _ : X => c) (Ω \ closure N) :=
  superharmonicOnX_const_dev c _

/-! ## Obligation 3(ii): gluing superharmonicity from two open pieces

Rather than re-prove the two fields of `Submission.SuperharmonicOnX` by hand (the binder shape of
`ContinuousOn` inside the `def`-to-`And` is opaque), this is a pure instantiation of the workspace's
proven locality lemma `superharmonicOnX_of_isOpen_cover_dev` with the two-element index `Bool`. -/

/-- **Gluing superharmonicity from two open pieces.** -/
theorem superharmonicOnX_of_union {Ω Ω₁ Ω₂ : Set X} (h₁ : IsOpen Ω₁) (h₂ : IsOpen Ω₂)
    (hcov : Ω ⊆ Ω₁ ∪ Ω₂) {w : X → ℝ}
    (hw₁ : Submission.SuperharmonicOnX w Ω₁) (hw₂ : Submission.SuperharmonicOnX w Ω₂) :
    Submission.SuperharmonicOnX w Ω := by
  refine superharmonicOnX_of_isOpen_cover_dev (ι := Bool) (V := fun b : Bool => cond b Ω₁ Ω₂)
    ?_ ?_ ?_
  · intro b
    cases b
    · exact h₂
    · exact h₁
  · intro x hx
    rcases hcov hx with h | h
    · exact Set.mem_iUnion.mpr ⟨true, h⟩
    · exact Set.mem_iUnion.mpr ⟨false, h⟩
  · intro b
    cases b
    · exact hw₂
    · exact hw₁

/-! ## The assembled barrier

`w := if x ∈ Ω ∩ V then min (ω x + ε * min (u x) c, c) else c`.  On `Ω ∩ V` it is the merged clamp
(clamped at `c` rather than `1`, so that it agrees with the outside constant on the overlap *by
definition*), and off `Ω ∩ V` it is the constant `c`.  Superharmonicity on each of the two gluing
pieces comes from the lemmas already proved. -/

/-- **The assembled barrier.** -/
noncomputable def assembledBarrier (Ω V : Set X) (u ω : X → ℝ) (c ε : ℝ) : X → ℝ :=
  fun x => if x ∈ Ω ∩ V then (ω x + ε * min (u x) c) ⊓ c else c

theorem assembledBarrier_of_mem {Ω V : Set X} {u ω : X → ℝ} {c ε : ℝ} {x : X}
    (hx : x ∈ Ω ∩ V) :
    assembledBarrier Ω V u ω c ε x = (ω x + ε * min (u x) c) ⊓ c := if_pos hx

theorem assembledBarrier_of_not_mem {Ω V : Set X} {u ω : X → ℝ} {c ε : ℝ} {x : X}
    (hx : x ∉ Ω ∩ V) : assembledBarrier Ω V u ω c ε x = c := if_neg hx


/-! ## The final clamp, and the reduction of the target to the Bouligand (Bouligand/Poisson)
globalization of a local barrier

The construction of `Work.SimplyConnected.ABS.bouligandCoherentBarrier` (Bouligand's Lemma 2, via
the Poisson integral of a "tent" datum over the bad set on a chart sphere — see
`NOTES_globalBarrier_reg_perron_route.md` and the recipe module `bouligandRecipe.lean`) produces a
*coherent subharmonic barrier* `b` on `Ω`: subharmonic, negative, tending to `0` at `p`.  The two
lemmas below turn such a `b` into the target: `min (-b) 1` is superharmonic on `Ω`, positive,
`≤ 1`, and tends to `0` at `p`. -/

/-- **The final clamp.**  A positive superharmonic function on `Ω` whose values tend to `0` at `p`
yields the target of `globalBarrierOfLocalBarrierReg`. -/
theorem globalBarrierOf_pos_superharmonic_local {Ω : Set X} {p : X} {v : X → ℝ}
    (hv : Submission.SuperharmonicOnX v Ω) (hpos : ∀ x ∈ Ω, 0 < v x)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ nhds p ∧ ∀ x ∈ Ω ∩ N, v x < ε) :
    ∃ w : X → ℝ, Submission.SuperharmonicOnX w Ω ∧ (∀ x ∈ Ω, 0 < w x) ∧
      (∀ x ∈ Ω, w x ≤ 1) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ nhds p ∧ ∀ x ∈ Ω ∩ N, w x < ε) :=
  ⟨fun x => min (v x) 1, SuperharmonicOnX.inf_const_dev hv 1,
   fun x hx => lt_min (hpos x hx) one_pos, fun x _ => min_le_right _ _, fun ε hε => by
     obtain ⟨N, hN, hNlt⟩ := hdec ε hε
     exact ⟨N, hN, fun x hx => lt_of_le_of_lt (min_le_left _ _) (hNlt x hx)⟩⟩

/-- **The target from a coherent subharmonic barrier.**  If `b` is subharmonic on `Ω`, negative
there, and tends to `0` at `p` along `Ω`, then `min (-b) 1` is the required global barrier. -/
theorem globalBarrier_of_coherentSubharmonicBarrier {Ω : Set X} (hΩo : IsOpen Ω) {p : X}
    (hp : p ∈ frontier Ω)
    (hb : ∃ b : X → ℝ, Submission.SubharmonicOnX b Ω ∧ (∀ x ∈ Ω, b x < 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ nhds p ∧ ∀ x ∈ Ω ∩ N, -ε < b x)) :
    ∃ w : X → ℝ, Submission.SuperharmonicOnX w Ω ∧ (∀ x ∈ Ω, 0 < w x) ∧
      (∀ x ∈ Ω, w x ≤ 1) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ nhds p ∧ ∀ x ∈ Ω ∩ N, w x < ε) := by
  obtain ⟨b, hbsub, hbneg, hbdec⟩ := hb
  refine globalBarrierOf_pos_superharmonic_local (v := fun x => min (-(b x)) 1)
    (SuperharmonicOnX.inf_const_dev hbsub.neg 1) ?_ ?_
  · intro x hx
    exact lt_min (neg_pos.mpr (hbneg x hx)) one_pos
  · intro ε hε
    obtain ⟨N, hN, hNsub⟩ := hbdec (min ε 1) (lt_min hε one_pos)
    refine ⟨N, hN, fun x hx => ?_⟩
    have h0 : -(b x) < min ε 1 := by linarith [hNsub x hx]
    have h1 : -(b x) < ε := lt_of_lt_of_le h0 (min_le_left ε 1)
    exact lt_of_le_of_lt (min_le_left (-(b x)) 1) h1

theorem globalBarrierOfLocalBarrierReg {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) {p : X} (hp : p ∈ frontier Ω)
    (hb : ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0) :
    ∃ w : X → ℝ, Submission.SuperharmonicOnX w Ω ∧ (∀ x ∈ Ω, 0 < w x) ∧
      (∀ x ∈ Ω, w x ≤ 1) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ nhds p ∧ ∀ x ∈ Ω ∩ N, w x < ε) := by
  obtain ⟨u, V, hVo, hpV, hsup, hpos, hcont, hup⟩ := hb
  exact globalBarrier_of_coherentSubharmonicBarrier hΩo hp
    (RegBouligand.coherentSubharmonicBarrier hΩo hp hVo hpV hsup hpos hcont hup)

end Work.SimplyConnected.ABS

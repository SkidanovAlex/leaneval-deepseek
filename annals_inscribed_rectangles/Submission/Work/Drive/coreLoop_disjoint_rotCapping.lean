import Mathlib
import Submission.Work.Configuration
import Submission.Work.Drive.OrderBase
import Submission.Work.Drive.sideCountDefs
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.omegaChainInterface
import Submission.Work.Drive.coreLoopCapDisjoint
import Submission.Work.Drive.coreLoopStripDisjoint
import Submission.Work.Drive.chartLevelData
import Submission.Work.Drive.isOpen_Zc

/-!
# The core loop misses the rotated plane: the *loop-vs-disk* form of the germ route's `hdisj`

`Work.Drive.sideGerm_spec` and `Work.Drive.sideGerm_parity_eq_of_close` carry the hypothesis

    hdisj : Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q)      -- **disk vs disk**

for **all** `w ∈ Zc γ`.  That is much stronger than what `Zc γ` gives, and the `cap ∩ w·cap` piece of it
is a statement about two `2`-dimensional caps, which is *not* a consequence of `w ∈ Zc γ` (see the note
in `HANDOFF.md`).  What the parity argument actually consumes is the **loop-vs-disk** statement

    Disjoint (range (coreLoop Q)) (rotCapping w '' chartDisk Q),

because it is the *loop* `coreLoop Q` (the projective line of the chart, `Q` on `‖z‖ = 1`) which is
swept and must miss the *rotated plane*.  This file states and assembles that form.

## The mathematics

`Zc γ = (GoodC γ)ᶜ` is, by `Work.Drive.mem_Zc_iff` below, *exactly* the statement that the
configuration strip of `γ` (the set of `muOrd`-values of pairs of **distinct** points) is disjoint from
its rotation by `u`: `u ∈ Zc γ ↔ Disjoint (stripConfig γ) (actC u '' stripConfig γ)`.  That is the
"`∂M ∩ w·M ⊆ M ∩ w·M = ∅`" step: the loop is a set of configuration points of `chartDisk Q`, so
rotating a *strip* point by `w` and landing on a *loop* point would produce a meet of the strip with
its own rotation, i.e. a point of `GoodC γ`.

The remaining piece is the **side dichotomy** of `capSideLift.lean`/`capSide_capPiece.lean`: the capping
space is divided by the Clifford torus `{‖c₁‖ = ‖c₂‖}` into the *configuration* side and the *cap*
side; the loop is configuration side (`stripChart`-values are `confProjVecOf u d` with `‖d‖ < 1`,
`Work.Drive.isCapVec_confProjVecOf`), while the rotated cap disk is cap side
(`CapPiece`-values are `capProjVecOf w d` with `‖d‖ < 1`, `Work.Drive.isCapVec_capProjVecOf`), and
`rotCapping w` preserves `‖c₁‖` and `‖c₂‖` (it multiplies the two complex coordinates by unit complex
numbers).  Hence the loop cannot meet a rotated cap point either.

The two halves are isolated as `coreLoop_disjoint_rotCapping_stripPart` (the `Zc γ` half, which is where
the chart's strip clause and the dictionary `stripChart ↔ muConfPiece` are used) and
`coreLoop_disjoint_rotCapping_capPart` (the side half, which does **not** use `w ∈ Zc γ` at all); the
assembly is proved below.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

section Zc

open Submission.Configuration

/-- The **configuration strip** of `γ`: the set of `muOrd`-values of pairs of *distinct* points of the
circle.  (`muOrd γ (x, x)` is the degenerate chord at `γ x`, which is *not* in the strip; that boundary
is exactly where `GoodC γ`'s "`x ≠ y`" hypotheses are needed.) -/
def stripConfig (γ : Circle → ℝ × ℝ) : Set ((ℝ × ℝ) × UnitAddCircle × ℝ) :=
  {q | ∃ x y : Circle, x ≠ y ∧ q = muOrd γ (x, y)}

/-- **`Zc γ` is "the configuration strip misses its rotation"** — the geometric form of the complement
of `GoodC γ`, obtained by unfolding the definition of `GoodC`.  This is the hypothesis the chart lane
consumes: it is a statement about the *configuration* space, without any reference to a chart. -/
theorem mem_Zc_iff {γ : Circle → ℝ × ℝ} {u : UnitAddCircle} :
    u ∈ Zc γ ↔ Disjoint (stripConfig γ) (actC u '' stripConfig γ) := by
  constructor
  · intro hu
    rw [Set.disjoint_left]
    rintro q ⟨x, y, hxy, hq⟩ ⟨q', hq'mem, hqq'⟩
    obtain ⟨x', y', hx'y', hq'⟩ := hq'mem
    refine hu ⟨x, y, x', y', hxy, hx'y', ?_⟩
    rw [hq', hq] at hqq'
    exact hqq'.symm
  · intro h
    rintro ⟨x, y, x', y', hxy, hx'y', heq⟩
    have h1 : muOrd γ (x, y) ∈ stripConfig γ := ⟨x, y, hxy, rfl⟩
    have h2 : muOrd γ (x, y) ∈ actC u '' stripConfig γ :=
      ⟨muOrd γ (x', y'), ⟨x', y', hx'y', rfl⟩, heq.symm⟩
    exact Set.disjoint_left.mp h h1 h2

end Zc

/-- **The `Zc γ` half of the loop-vs-disk disjointness**: a loop point (a `stripChart`-value of the
chart, `‖z‖ = 1`) is never the rotation by `w ∈ Zc γ` of a *strip*-part point of the chart
(`1/2 ≤ ‖z'‖ ≤ 1`).

**The hypothesis `Function.Injective γ` is genuinely needed** (the review gate refuted the version
without it: for constant `γ ≡ p ≠ 0` the constant chart satisfies every clause of `IsPlaneChart` and
`Q 1 = rotCapping 0 (Q 0)`).  Injectivity is what makes the *maximal* chord `Q z` (`‖z‖ = 1`, chord
parameters `arg z ± π/2`, separation `π`) non-degenerate, hence strictly configuration side; it is
supplied in the application by `IsSmoothEmbedding`.

Proof plan.  By the strip clause of `IsPlaneChart`, both `Q z` and `Q z'` are `stripChart γ hγne 0 _`
values, i.e. the capping-space images of explicit configuration points of `stripConfig γ` (the chords
of `γ`); `rotCapping w` of a strip point is `actC w` of the corresponding configuration.  If
`Q z = rotCapping w (Q z')` then, reading the chart in the capping coordinates and using
`Work.Drive.mem_Zc_iff`, the configuration strip meets its rotation by `w`, i.e. `w ∈ GoodC γ`,
contradicting `hw`.  The boundary case `‖z'‖ = 1/2` is *not* covered by the strip clause (which is
strict) — there `Q z'` is pinned only by continuity to the *degenerate* chord at `γ (arg z')`, whose
disk coordinate is `‖d‖ = 1` (**not** a vanishing length: the capping radius is `√(|mid|² + len²)`,
which stays `|γ x| > 0`), while `Q z` has `‖d‖ < 1` exactly because the maximal chord is
non-degenerate (injectivity of `γ`).  So that case is settled by the disk coordinate `‖d‖`, i.e. it is
the same statement as the cap half below. -/
theorem coreLoop_disjoint_rotCapping_stripPart {γ : Circle → ℝ × ℝ}
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ) {Q : ℂ → CappingSpace}
    (hQ : IsPlaneChart γ hγne Q) {w : UnitAddCircle} (hw : w ∈ Zc γ) ⦃z z' : ℂ⦄
    (hz : ‖z‖ = 1) (hz'₁ : 1 / 2 ≤ ‖z'‖) (hz'₂ : ‖z'‖ ≤ 1) :
    Q z ≠ rotCapping w (Q z') :=
  coreLoopStripDisjoint hγne hγinj hQ hw hz hz'₁ hz'₂

/-- **The side half of the loop-vs-disk disjointness**: a loop point is never the rotation by any `w`
of a *cap*-part point of the chart (`‖z'‖ < 1/2`).  No hypothesis on `w` is needed.

**The hypothesis `Function.Injective γ` is genuinely needed** (the review gate gave the counterexample
`γ ≡ p ≠ 0` with `Q` constant: `Q 1 = rotCapping 0 (Q 0)`, and every clause of `IsPlaneChart` is
satisfied because the clauses only pin `‖d‖ ≤ 1`, never `‖d‖ < 1`).  In the application it comes from
`IsSmoothEmbedding`.

Proof plan.  By the cap clause of `IsPlaneChart`, `Q z' = Quotient.mk'' (Sum.inr c)` for a `CapPiece`
`c`; a `CapPiece` of *non-degenerate* chord data is strictly cap side (`IsCapVec`, i.e.
`‖c₁‖ < ‖c₂‖`, `Work.Drive.isCapVec_capProjVecOf`), while the boundary `‖d‖ = 1` of the cap piece is
identified by `cappingRel` with the boundary of the configuration piece.  The loop point `Q z`
(`‖z‖ = 1`) is a `stripChart`-value whose disk coordinate is `‖d‖ = ‖midpoint‖/R < 1` — strict
because the maximal chord is non-degenerate, i.e. `γ (exp (i (arg z + π/2))) ≠
γ (exp (i (arg z - π/2)))`, which injectivity of `γ` supplies — so `¬IsCapVec`.  `rotCapping w`
multiplies both complex coordinates of the lift by unit complex numbers, hence preserves `‖c₁‖` and
`‖c₂‖` and therefore the side.  Since `IsCapVec` and its complement are complementary, the points
differ. -/
theorem coreLoop_disjoint_rotCapping_capPart {γ : Circle → ℝ × ℝ}
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ) {Q : ℂ → CappingSpace}
    (hQ : IsPlaneChart γ hγne Q) ⦃w : UnitAddCircle⦄ ⦃z z' : ℂ⦄
    (hz : ‖z‖ = 1) (hz' : ‖z'‖ < 1 / 2) :
    Q z ≠ rotCapping w (Q z') :=
  coreLoopCapDisjoint hγne hγinj hQ hz hz' 

/-- **The loop-vs-disk disjointness**: for `w ∈ Zc γ`, the core loop of the chart misses the rotated
chart disk.  This is the form of the germ route's `hdisj` that the parity argument consumes, and it is
the only form derivable from `w ∈ Zc γ` (the `disk`-vs-`disk` form is not).

The proof is the immediate assembly of the two halves above: a point of `chartDisk Q` is `Q z'` with
`‖z'‖ ≤ 1`, and a point of `range (coreLoop Q)` is `Q z` with `‖z‖ = 1`; split `‖z'‖ < 1/2` /
`1/2 ≤ ‖z'‖`.  `Function.Injective γ` is carried because both halves need it (see their docstrings);
in the application it is supplied by `IsSmoothEmbedding`. -/
theorem disjoint_range_coreLoop_rotCapping_chartDisk {γ : Circle → ℝ × ℝ}
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ) {Q : ℂ → CappingSpace}
    (hQ : IsPlaneChart γ hγne Q) {w : UnitAddCircle} (hw : w ∈ Zc γ) :
    Disjoint (Set.range (coreLoop Q)) (rotCapping w '' chartDisk Q) := by
  rw [Set.disjoint_left]
  rintro q ⟨t, htq⟩ ⟨p, hp_mem, hp_eq⟩
  obtain ⟨z', hz'1, rfl⟩ := hp_mem
  have hnorm : ‖Complex.exp (Real.pi * (t : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  have hz'le : ‖z'‖ ≤ 1 := by simpa [dist_eq_norm] using hz'1
  have hgoal : Q (Complex.exp (Real.pi * (t : ℂ) * Complex.I)) = rotCapping w (Q z') :=
    (show coreLoop Q t = rotCapping w (Q z') from htq.trans hp_eq.symm)
  rcases lt_or_ge (‖z'‖) (1 / 2) with h | h
  · exact coreLoop_disjoint_rotCapping_capPart hγne hγinj hQ hnorm h hgoal
  · exact coreLoop_disjoint_rotCapping_stripPart hγne hγinj hQ hw hnorm h hz'le hgoal

section Separation

attribute [local instance] Work.Drive.t2Space_cappingSpace

/-- **The separation form of the loop-vs-disk disjointness** — the shape the germ route needs, so that
the property survives the chart perturbation `Ξ t` and the limit `w' → w`: two **disjoint open**
supersets, one of the (compact image of the) core loop and one of the rotated chart disk.

* `Continuous (coreLoop Q)` comes from `Work.Drive.continuous_of_isPlaneChart`
  (`chartLevelData.lean`) and the smoothness of `z ↦ exp (π z i)`;
* `IsCompact (coreLoop Q '' Icc 0 1) := isCompact_Icc.image hloop` and
  `IsCompact (rotCapping w '' chartDisk Q) := (chartDisk_compact hQcont).image (continuous_rotCapping w)`;
* the two are disjoint by `disjoint_range_coreLoop_rotCapping_chartDisk` (restricted to `Icc 0 1`,
  which by the seam clause is the whole range of the loop);
* `SeparatedNhds.of_isCompact_isCompact_isClosed` (in the `R₁` topology of `CappingSpace`, here
  `Work.Drive.t2Space_cappingSpace`) then returns exactly the two disjoint open sets.

There is deliberately **no** `dist` bound: `CappingSpace` carries only a `PseudoMetricSpace` (its
zero-distance pairs are the antipodal lifts in the capping chart), so the metric form of the separation
lemma is not applicable — and openness is all the perturbation argument consumes.)-/
theorem exists_isOpen_separation_coreLoop_rotCapping_chartDisk {γ : Circle → ℝ × ℝ}
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ) {Q : ℂ → CappingSpace}
    (hQ : IsPlaneChart γ hγne Q) {w : UnitAddCircle} (hw : w ∈ Zc γ) :
    ∃ U V : Set CappingSpace, IsOpen U ∧ IsOpen V ∧
      coreLoop Q '' Set.Icc (0 : ℝ) 1 ⊆ U ∧ rotCapping w '' chartDisk Q ⊆ V ∧
      Disjoint U V := by
  classical
  have hQcont : Continuous Q := continuous_of_isPlaneChart γ hγne Q hQ
  have hloop : Continuous (coreLoop Q) := by
    unfold coreLoop
    exact hQcont.comp (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const))
  have hK : IsCompact (coreLoop Q '' Set.Icc (0 : ℝ) 1) := isCompact_Icc.image hloop
  have hL : IsCompact (rotCapping w '' chartDisk Q) :=
    (chartDisk_compact hQcont).image (continuous_rotCapping w)
  have hd : Disjoint (coreLoop Q '' Set.Icc (0 : ℝ) 1) (rotCapping w '' chartDisk Q) :=
    (disjoint_range_coreLoop_rotCapping_chartDisk hγne hγinj hQ hw).mono_left
      (Set.image_subset_range _ _)
  exact SeparatedNhds.of_isCompact_isCompact_isClosed hK hL hL.isClosed hd

/-- **The angle-locality form of the separation.**  Because `Zc γ` is *open* (`Work.Drive.isOpen_Zc`),
the loop-vs-disk separation holds for every `w'` in a neighbourhood of `w` — the second role that the
germ route asked `hdisj` to play ("`w' → w`").  The chart and its hypotheses are independent of the
angle, so this is `isOpen_Zc` + the separation lemma, nothing else. -/
theorem eventually_disjoint_range_coreLoop_rotCapping {γ : Circle → ℝ × ℝ}
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ)
    (hγinj : Function.Injective γ) {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    {w : UnitAddCircle} (hw : w ∈ Zc γ) :
    ∀ᶠ w' in 𝓝 w,
      Disjoint (coreLoop Q '' Set.Icc (0 : ℝ) 1) (rotCapping w' '' chartDisk Q) := by
  filter_upwards [(isOpen_Zc γ hγ).mem_nhds hw] with w' hw'
  exact (disjoint_range_coreLoop_rotCapping_chartDisk hγne hγinj hQ hw').mono_left
    (Set.image_subset_range _ _)

end Separation

end

end Work.Drive

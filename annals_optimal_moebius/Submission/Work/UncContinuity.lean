import Submission.Work.ChordSqueeze
import Submission.Work.SequentialContinuityDegenerate
import Submission.Work.FrontierFine
import Submission.Work.UncDiagonal
import Submission.Work.HeightSlope
import Submission.Work.DegenerateLeafValue
import Submission.Work.UHeightSlope
import Submission.Work.Main0U
import Submission.Work.UMatchDirection
import Submission.Work.HeightStructure
import Submission.Work.ComponentLeaves
import Submission.Work.FlatLeafBendData
import Submission.Work.BandSpliceFI

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Uncovered-height leaf-slope continuity — COMPLETE (zero sorry)

The mathematical plan is recorded in full in `session_status117.lean`.
This file implements — all GREEN, `lake build Submission.Work.UncContinuity`
rc=0, zero sorry:

1. The pure 2-D `chord_crossing` and the chord wiring (`frCompData_centre`,
   `graph_mem_stripChord`, `stripChord_dN_zero_of_frCompData`,
   `ubend_graph_dN_ne_zero`, `cov_graph_dN_zero`, blend-leaf wiring
   `bendGraph_eq_affine`/`genP_affine`/`compLeaf_graph_eq_blendP`/
   `blend_graph_dN_zero`).
2. **`leafSlope_tendsto_cov_at_unc`** — covered heights → an uncovered
   degenerate height: slopes → degenerate slope (CROSSING CONTRADICTION of
   the frontier chord vs a U-bend).
3. **`leafSlope_tendsto_fi_at_unc`** — flat-interior heights → uncovered
   degenerate height (crossing of the flat BLEND leaf vs a U-bend).
4. The classwise assembly at uncovered heights:
   `leafSlope_converges_uHeight_unc`/`_fi_unc`/`_cov_unc`/`_unc_unc` and
   **`leafSlope_tendsto_at_uncovered`** (sequential continuity of
   `leafSlope` at every uncovered degenerate flat height).
5. **Layer-3 completion**: `continuousAt_leafSlope_of_uncovered`,
   `continuousAt_spliceA1/B1_of_uncovered`, and the TOTAL continuity
   `continuous_spliceA1` / `continuous_spliceB1` on all of ℝ (via
   `continuous_iff_continuousAt` + `height_case`) — the `cont_left` /
   `cont_right` ingredients of the `BandFoliation` instance.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- **Two strip chords cross in the open strip**: if the centre heights
`c`, `w` are closer than half the slope difference, the chords
`chordLine c M` and `chordLine w m` meet at some `x0 ∈ (0,1)`. -/
lemma chord_crossing {c w M m : ℝ} (h : |c - w| < |M - m| / 2) :
    ∃ x : ℝ, x ∈ Set.Ioo 0 1 ∧ chordLine c M x = chordLine w m x := by
  have hMm : M ≠ m := by
    intro hz
    have : |c - w| < 0 := by simpa [hz] using h
    exact (not_lt_of_ge (abs_nonneg (c - w))) this
  let t : ℝ := (w - c) / (M - m)
  have htlin : c + M * t = w + m * t := by
    have htw : (M - m) * t = w - c := by
      dsimp [t]
      field_simp [sub_ne_zero.mpr hMm]
    nlinarith
  refine ⟨1 / 2 + t, ?_, ?_⟩
  · rw [Set.mem_Ioo]
    have hMm0 : |M - m| > 0 := abs_pos.mpr (sub_ne_zero.mpr hMm)
    have hwd : |w - c| / |M - m| < 1 / 2 := by
      have hh : |w - c| < |M - m| / 2 := by simpa [abs_sub_comm] using h
      rw [div_lt_iff₀ hMm0]
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
    have hstep : |t| < 1 / 2 := by
      dsimp [t]
      rw [abs_div]
      exact hwd
    have hstep' : |(1 / 2 + t) - 1 / 2| < 1 / 2 := by
      have hred : (1 / 2 + t) - 1 / 2 = t := by ring
      rwa [hred]
    rw [abs_lt] at hstep'
    constructor <;> linarith
  · dsimp [chordLine]
    have hx : (1 / 2 + t) - 1 / 2 = t := by ring
    calc
      c + M * ((1 / 2 + t) - 1 / 2) = c + M * t := by rw [hx]
      _ = w + m * t := htlin
      _ = w + m * ((1 / 2 + t) - 1 / 2) := by rw [hx]

/-- The centre height of the frontier chord at a slice height is the
slice height itself: `sideH₁ α β (1/2) = h`. -/
lemma frCompData_centre {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h : ℝ} (hh : h ∈ frHeights f p) :
    sideH₁ (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 (1 / 2) = h := by
  have hslice : frSlicePoint f p h ∈
      stripChord (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 := by
    have h1 := frCompAt_slice hf ha hp hh
    rw [← frCompData_spec hf ha p hp hh]
    exact h1
  have hc := (mem_stripChord_coords.mp hslice).2.2
  have hc0 : (frSlicePoint f p h) 0 = 1 / 2 := by simp [frSlicePoint]
  have hc1 : (frSlicePoint f p h) 1 = h := by simp [frSlicePoint]
  calc
    sideH₁ (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 (1 / 2)
        = sideH₁ (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2
            ((frSlicePoint f p h) 0) := by rw [hc0]
    _ = (frSlicePoint f p h) 1 := hc.symm
    _ = h := hc1

/-- The graph point `(x, chordLine c M x)` lies on the chord
`stripChord α β` whenever the centre height and slope match. -/
lemma graph_mem_stripChord {α β c M x : ℝ} (hcentre : sideH₁ α β (1 / 2) = c)
    (hslope : M = β - α) (hx : x ∈ Set.Ioo 0 1) :
    (!₂[x, chordLine c M x] : ℝ²) ∈ stripChord α β := by
  rw [mem_stripChord_coords]
  rcases (Set.mem_Ioo.mp hx) with ⟨hx0, hx1⟩
  constructor
  · exact hx0
  constructor
  · exact hx1
  · -- chordLine c M x = sideH₁ α β x
    have hid : chordLine c M x = sideH₁ α β x := by
      dsimp [chordLine, sideH₁]
      rw [hslope]
      have hc : c = α + (β - α) * (1 / 2) := hcentre.symm
      rw [hc]
      ring
    calc
      (!₂[x, chordLine c M x] : ℝ²) 1 = chordLine c M x := by simp
      _ = sideH₁ α β x := hid

/-- Points of the frontier chord at a slice height of a flat component
are flat: `dN = 0`. -/
lemma stripChord_dN_zero_of_frCompData {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h : ℝ} (hh : h ∈ frHeights f p) :
    ∀ z : ℝ², z ∈ stripChord (frCompData hf ha p hp h hh).1 (frCompData hf ha p hp h hh).2 →
      dN f z = 0 := by
  intro z hz
  have hzS : z ∈ stripInterior := stripChord_subset_stripInterior hz
  have hcomp : z ∈ frCompAt f p h := by
    rw [frCompData_spec hf ha p hp hh]
    exact hz
  have hF : z ∈ frontier (flatComponent f p) := frCompAt_subset_frontier hcomp
  have hflat : z ∈ FlatSet f := flatComponent_frontier_subset_FlatSet hf hzS hF
  exact (mem_FlatSet.mp hflat).2

/-- The points of the graph of a `U`-bend over `x0 ∈ (0,1)` are `U`-points
(`dN ≠ 0`). -/
lemma ubend_graph_dN_ne_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hyU : y ∈ UHeight a f) {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    dN f (!₂[x, chordLine y (slopeAtHeight hf ha hyU) x] : ℝ²) ≠ 0 := by
  let q : ℝ² := centrePoint y
  let hqS : q ∈ stripInterior := centrePoint_mem_stripInterior y
  let hqU : dN f q ≠ 0 := (mem_UHeight (a := a) (f := f)).mp hyU
  let s : ℝ := (x - 1 / 2) / (uBendDirPos hf ha hqS hqU) 0
  have hw0 : (uBendDirPos hf ha hqS hqU) 0 ≠ 0 := uBendDirPos_coord_ne_zero hf ha hqS hqU
  have hcoord0 : (q + s • uBendDirPos hf ha hqS hqU) 0 = x := by
    have hc : (q + s • uBendDirPos hf ha hqS hqU) 0 = q 0 + s * (uBendDirPos hf ha hqS hqU) 0 := by simp
    rw [hc]
    have hq0 : q 0 = 1 / 2 := by dsimp [q, centrePoint]
    rw [hq0]
    dsimp [s]
    change 1 / 2 + (x - 1 / 2) / (uBendDirPos hf ha hqS hqU) 0 * (uBendDirPos hf ha hqS hqU) 0 = x
    field_simp [hw0]
    ring
  have hcoord1 : (q + s • uBendDirPos hf ha hqS hqU) 1 =
      chordLine y (slopeAtHeight hf ha hyU) x := by
    have hc : (q + s • uBendDirPos hf ha hqS hqU) 1 =
        q 1 + s * (uBendDirPos hf ha hqS hqU) 1 := by simp
    rw [hc]
    have hq1 : q 1 = y := by dsimp [q, centrePoint]
    rw [hq1]
    dsimp [s, slopeAtHeight, uBendSlope, chordLine]
    change y + (x - 1 / 2) / (uBendDirPos hf ha hqS hqU) 0 * (uBendDirPos hf ha hqS hqU) 1 =
      y + (uBendDirPos hf ha hqS hqU) 1 / (uBendDirPos hf ha hqS hqU) 0 * (x - 1 / 2)
    field_simp [hw0]
  have hPstrip : q + s • uBendDirPos hf ha hqS hqU ∈ stripInterior := by
    have hx0' : (q + s • uBendDirPos hf ha hqS hqU) 0 = x := hcoord0
    simpa [stripInterior, hx0'] using hx
  have hSin : s ∈ Set.Ioo (leftParam q (uBendDirPos hf ha hqS hqU))
      (rightParam q (uBendDirPos hf ha hqS hqU)) := by
    exact (param_stripInterior_iff (x := q) (w := uBendDirPos hf ha hqS hqU)
      (uBendDirPos_spec hf ha hqS hqU).2.2 s).mpr hPstrip
  have hmem : q + s • uBendDirPos hf ha hqS hqU ∈ uBendSet hf ha hqS hqU := by
    rw [uBendSet_eq_param hf ha hqS hqU]
    exact ⟨s, hSin, rfl⟩
  have hdN : dN f (q + s • uBendDirPos hf ha hqS hqU) ≠ 0 :=
    (uBendSet_subset_U_and_kernel hf ha hqS hqU).1 (q + s • uBendDirPos hf ha hqS hqU) hmem
  have hEq : q + s • uBendDirPos hf ha hqS hqU =
      (!₂[x, chordLine y (slopeAtHeight hf ha hyU) x] : ℝ²) := by
    ext i <;> fin_cases i <;> simp [hcoord0, hcoord1]
  rwa [← hEq]

/-- At a COVERED height the frontier chord over `x0 ∈ (0,1)` is flat: the
graph points of `chordLine y (leafSlope y)` have `dN = 0`. -/
lemma cov_graph_dN_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hc : CoveredHeight (f := f) y) {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    dN f (!₂[x, chordLine y (leafSlope hf ha y) x] : ℝ²) = 0 := by
  let p : ℝ² := covPoint y hc
  let hp : p ∈ interior (FlatSet f) := covPoint_hp hc
  let hh : y ∈ frHeights f p := covPoint_hh hc
  let α : ℝ := (frCompData hf ha p hp y hh).1
  let β : ℝ := (frCompData hf ha p hp y hh).2
  have hcentre : sideH₁ α β (1 / 2) = y := by
    dsimp [α, β]
    exact frCompData_centre hf ha hp hh
  have hslope : leafSlope hf ha y = β - α := by
    dsimp [α, β]
    have h1 := leafSlope_eq_covFrontSlope hf ha hc
    simpa [covFrontSlope, p, hp, hh] using h1
  have hgm : (!₂[x, chordLine y (leafSlope hf ha y) x] : ℝ²) ∈ stripChord α β := by
    exact graph_mem_stripChord hcentre hslope hx
  have hz : (!₂[x, chordLine y (leafSlope hf ha y) x] : ℝ²) ∈
      stripChord (frCompData hf ha p hp y hh).1 (frCompData hf ha p hp y hh).2 := by
    simpa [α, β] using hgm
  exact stripChord_dN_zero_of_frCompData hf ha hp hh _ hz





/-- **cov→unc**: a sequence of COVERED heights converging to an
UNCOVERED degenerate flat height has leaf slopes converging to the
degenerate slope.  Proof by CROSSING CONTRADICTION: a covered frontier
chord whose slope stayed ε-away from the U-limit slope `M₀` would cross
a nearby U-bend inside the open strip — but frontier chords are flat
(`dN = 0`, `cov_graph_dN_zero`) while U-bends are `U` (`dN ≠ 0`). -/
theorem leafSlope_tendsto_cov_at_unc {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f)
    (hni₀ : ¬ IsFlatInterior f (centrePoint y₀)) (hunc₀ : ¬ CoveredHeight (f := f) y₀)
    {c : ℕ → ℝ} (hcCov : ∀ n : ℕ, CoveredHeight (f := f) (c n))
    (hct : Tendsto c atTop (𝓝 y₀)) :
    Tendsto (fun n : ℕ => leafSlope hf ha (c n)) atTop
      (𝓝 (degenerateSlope hf ha hy₀F hni₀ hunc₀)) := by
  classical
  by_contra hnot
  rcases exists_bad_subseq_of_not_tendsto hnot with ⟨ε, hε, φ, hφmono, hbad⟩
  -- hbad : ∀ n, ε ≤ |leafSlope hf ha (c (φ n)) − degenerateSlope ...|
  let M₀ : ℝ := degenerateSlope hf ha hy₀F hni₀ hunc₀
  let w : ℕ → ℝ := fun n => uHeightBelowSeq hf ha hy₀F hni₀ hunc₀ n
  let hyW : ∀ n : ℕ, w n ∈ UHeight a f := fun n => uHeightBelowSeq_mem hf ha hy₀F hni₀ hunc₀ n
  let m : ℕ → ℝ := fun n => slopeAtHeight hf ha (hyW n)
  have hw : Tendsto w atTop (𝓝 y₀) := by
    dsimp [w]
    exact uHeightBelowSeq_tendsto hf ha hy₀F hni₀ hunc₀
  have hm : Tendsto m atTop (𝓝 M₀) := by
    dsimp [m, M₀]
    simpa [w, hyW] using degenerateSlope_tendsto hf ha hy₀F hni₀ hunc₀
  have hwU : ∀ n : ℕ, w n ∈ UHeight a f := by
    intro n
    exact hyW n
  -- |c(φ n) − w n| → 0 (both converge to y₀)
  have hcφ : Tendsto (fun n : ℕ => c (φ n)) atTop (𝓝 y₀) := hct.comp hφmono.tendsto_atTop
  have hsmall : ∀ᶠ n in atTop, |c (φ n) - w n| < ε / 4 := by
    have hc₁ : ∀ᶠ n in atTop, |c (φ n) - y₀| < ε / 8 := by
      rcases (Metric.tendsto_atTop.mp hcφ) (ε / 8) (by positivity) with ⟨N, hN⟩
      refine Filter.eventually_atTop.2 ⟨N, ?_⟩
      intro n hn
      have hd := hN n hn
      simpa [Real.dist_eq] using hd
    have hc₂ : ∀ᶠ n in atTop, |w n - y₀| < ε / 8 := by
      rcases (Metric.tendsto_atTop.mp hw) (ε / 8) (by positivity) with ⟨N, hN⟩
      refine Filter.eventually_atTop.2 ⟨N, ?_⟩
      intro n hn
      have hd := hN n hn
      simpa [Real.dist_eq] using hd
    rcases Filter.eventually_atTop.mp (hc₁.and hc₂) with ⟨N, hN⟩
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have h1 := (hN n hn).1
    have h2 := (hN n hn).2
    have htri : |c (φ n) - w n| ≤ |c (φ n) - y₀| + |w n - y₀| := by
      have h := abs_add_le (c (φ n) - y₀) (y₀ - w n)
      have hsum : (c (φ n) - y₀) + (y₀ - w n) = c (φ n) - w n := by ring
      have h' : |y₀ - w n| = |w n - y₀| := abs_sub_comm y₀ (w n)
      rwa [hsum, h'] at h
    linarith
  have hmid : ∀ᶠ n in atTop, |m n - M₀| < ε / 4 := by
    rcases (Metric.tendsto_atTop.mp hm) (ε / 4) (by positivity) with ⟨N, hN⟩
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hd := hN n hn
    simpa [Real.dist_eq] using hd
  have hboth : ∀ᶠ n in atTop, |c (φ n) - w n| < ε / 4 ∧ |m n - M₀| < ε / 4 := hsmall.and hmid
  rcases Filter.eventually_atTop.mp hboth with ⟨N₀, hN₀⟩
  have hcwN : |c (φ N₀) - w N₀| < ε / 4 := (hN₀ N₀ le_rfl).1
  have hmN : |m N₀ - M₀| < ε / 4 := (hN₀ N₀ le_rfl).2
  -- ε ≤ |leafSlope(c(φ N₀)) − M₀|
  have hbadN : ε ≤ |leafSlope hf ha (c (φ N₀)) - M₀| := by
    simpa [M₀] using hbad N₀
  -- |m N₀ − leafSlope(c(φN₀))| ≥ 3ε/4 via the triangle inequality
  have htri : |leafSlope hf ha (c (φ N₀)) - M₀| ≤
      |leafSlope hf ha (c (φ N₀)) - m N₀| + |m N₀ - M₀| := by
    have h := abs_add_le (leafSlope hf ha (c (φ N₀)) - m N₀) (m N₀ - M₀)
    have hsum : (leafSlope hf ha (c (φ N₀)) - m N₀) + (m N₀ - M₀) =
        leafSlope hf ha (c (φ N₀)) - M₀ := by ring
    rwa [hsum] at h
  have hMmN : 3 * ε / 4 ≤ |leafSlope hf ha (c (φ N₀)) - m N₀| := by
    nlinarith
  have hcrossIneq : |c (φ N₀) - w N₀| < |leafSlope hf ha (c (φ N₀)) - m N₀| / 2 := by
    have h₂ : |leafSlope hf ha (c (φ N₀)) - m N₀| / 2 ≥ 3 * ε / 8 := by nlinarith
    nlinarith
  rcases chord_crossing (c := c (φ N₀)) (M := leafSlope hf ha (c (φ N₀)))
      (w := w N₀) (m := m N₀) hcrossIneq with ⟨xstar, hxstar, hcrossline⟩
  -- the two graph points coincide; one is flat (cov), the other is U
  have hB₀ : dN f (!₂[xstar, chordLine (w N₀) (slopeAtHeight hf ha (hyW N₀)) xstar] : ℝ²) ≠ 0 :=
    ubend_graph_dN_ne_zero hf ha (hyW N₀) hxstar
  have hlin : chordLine (w N₀) (slopeAtHeight hf ha (hyW N₀)) xstar =
      chordLine (c (φ N₀)) (leafSlope hf ha (c (φ N₀))) xstar := by
    -- hcrossline : chordLine c Mleaf xstar = chordLine w m xstar; m = slopeAtHeight
    have hmm : slopeAtHeight hf ha (hyW N₀) = m N₀ := rfl
    rw [hmm]
    exact hcrossline.symm
  have hB : dN f (!₂[xstar, chordLine (c (φ N₀)) (leafSlope hf ha (c (φ N₀))) xstar] : ℝ²) ≠ 0 := by
    have hP : (!₂[xstar, chordLine (w N₀) (slopeAtHeight hf ha (hyW N₀)) xstar] : ℝ²) =
        !₂[xstar, chordLine (c (φ N₀)) (leafSlope hf ha (c (φ N₀))) xstar] := by
      ext i <;> fin_cases i <;> simp [hlin]
    rw [← hP]
    exact hB₀
  have hA : dN f (!₂[xstar, chordLine (c (φ N₀)) (leafSlope hf ha (c (φ N₀))) xstar] : ℝ²) = 0 :=
    cov_graph_dN_zero hf ha (hcCov (φ N₀)) hxstar
  exact hB hA

/-- **The graph point of a bend lies on its segment**: for a `BendData`
with centre height `z` and slope `D.slope`, the graph point over `x0 = x`
is the affine combination `(1−x)•A + x•B`. -/
lemma bendGraph_eq_affine (D : BendData) {z : ℝ} (hcen : D.centreHeight = z)
    (x : ℝ) :
    (!₂[x, chordLine z (BendData.slope D) x] : ℝ²) = (1 - x) • D.A + x • D.B := by
  ext i <;> fin_cases i
  · simp [D.left_coord, D.right_coord]
  · simp [BendData.slope, chordLine]
    have hz : z = (D.A 1 + D.B 1) / 2 := by
      dsimp [BendData.centreHeight] at hcen
      exact hcen.symm
    rw [hz]
    ring

/-- `genP` is affine in its segment parameter: the point at `u = x` equals
the affine combination of the `u = 0` and `u = 1` points. -/
lemma genP_affine (α₁ β₁ α₂ β₂ t x : ℝ) :
    (1 - x) • genP α₁ β₁ α₂ β₂ t 0 + x • genP α₁ β₁ α₂ β₂ t 1 =
      genP α₁ β₁ α₂ β₂ t x := by
  ext i <;> fin_cases i
  · simp [genP]
  · simp [genP, sideH₁, sideH₂]
    ring

/-- The graph point of the component leaf at centre height `z` over
`x0 = x` equals the blended chord point `blendP d₁ d₂ z x`. -/
lemma compLeaf_graph_eq_blendP {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) (z x : ℝ) :
    (!₂[x, chordLine z ((compLeaf hf ha hp z).slope) x] : ℝ²) =
      blendP (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).1
             (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).2
             (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).1
             (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).2 z x := by
  let D : BendData := compLeaf hf ha hp z
  let d₁ : ℝ × ℝ := frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)
  let d₂ : ℝ × ℝ := frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)
  have hcen : D.centreHeight = z := by
    dsimp [D, compLeaf]
    exact flatCompBend_centre hf ha p hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp) (bwlt hf ha hp)
  have h1 := bendGraph_eq_affine D hcen x
  have hgb : (!₂[x, chordLine z (D.slope) x] : ℝ²) = genP d₁.1 d₁.2 d₂.1 d₂.2 (blendT d₁.1 d₁.2 d₂.1 d₂.2 z) x := by
    -- D = blendBend d₁ d₂ z; A = genA d t etc.
    have hD : D = blendBend d₁.1 d₁.2 d₂.1 d₂.2 z := by
      dsimp [D, d₁, d₂, compLeaf]
      exact compLeaf_eq_blendBend hf ha hp z
    have hA : D.A = genP d₁.1 d₁.2 d₂.1 d₂.2 (blendT d₁.1 d₁.2 d₂.1 d₂.2 z) 0 := by
      have hb := blendBend_A_eq d₁.1 d₁.2 d₂.1 d₂.2 z
      dsimp [genA] at hb
      rw [hD]
      exact hb
    have hB : D.B = genP d₁.1 d₁.2 d₂.1 d₂.2 (blendT d₁.1 d₁.2 d₂.1 d₂.2 z) 1 := by
      have hb := blendBend_B_eq d₁.1 d₁.2 d₂.1 d₂.2 z
      dsimp [genB] at hb
      rw [hD]
      exact hb
    calc
      (!₂[x, chordLine z (D.slope) x] : ℝ²) = (1 - x) • D.A + x • D.B := by simpa using h1
      _ = (1 - x) • genP d₁.1 d₁.2 d₂.1 d₂.2 (blendT d₁.1 d₁.2 d₂.1 d₂.2 z) 0 +
          x • genP d₁.1 d₁.2 d₂.1 d₂.2 (blendT d₁.1 d₁.2 d₂.1 d₂.2 z) 1 := by rw [hA, hB]
      _ = genP d₁.1 d₁.2 d₂.1 d₂.2 (blendT d₁.1 d₁.2 d₂.1 d₂.2 z) x := genP_affine d₁.1 d₁.2 d₂.1 d₂.2 _ x
  have hfin : genP d₁.1 d₁.2 d₂.1 d₂.2 (blendT d₁.1 d₁.2 d₂.1 d₂.2 z) x =
      blendP d₁.1 d₁.2 d₂.1 d₂.2 z x := by
    dsimp [blendP, blendT]
  simpa [D, d₁, d₂] using hgb.trans hfin


/-- The graph of the spliced leaf over a FLAT-INTERIOR height `z` is flat:
`dN = 0` on `!₂[x, chordLine z (leafSlope z) x]` for `x ∈ (0,1)`. -/
lemma blend_graph_dN_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {z : ℝ} (hfi : IsFlatInterior f (centrePoint z)) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 1) :
    dN f (!₂[x, chordLine z (leafSlope hf ha z) x] : ℝ²) = 0 := by
  let p : ℝ² := centrePoint z
  have hps : p ∈ stripInterior := by dsimp [p]; exact centrePoint_mem_stripInterior z
  have hp : p ∈ interior (FlatSet f) := (IsFlatInterior_iff_mem_interior_FlatSet hps).mp hfi
  have hzC : centrePoint z ∈ flatComponent f p := by dsimp [p]; exact mem_flatComponent hp
  have hzI : z ∈ Set.Ioo (bw₁ hf ha hp) (bw₂ hf ha hp) :=
    (mem_centreInterval_iff hf ha hp z).mp hzC
  have hleaf : leafSlope hf ha z = (compLeaf hf ha hp z).slope := by
    unfold leafSlope
    congr 1
    exact spliceChord_eq_compLeaf_of_centre_mem hf ha hp hzC
  let d₁ : ℝ × ℝ := frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)
  let d₂ : ℝ × ℝ := frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)
  have hgp : (!₂[x, chordLine z (leafSlope hf ha z) x] : ℝ²) =
      blendP d₁.1 d₁.2 d₂.1 d₂.2 z x := by
    have h1 := compLeaf_graph_eq_blendP hf ha hp z x
    rwa [← hleaf] at h1
  have hord : ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
      sideH₁ d₁.1 d₁.2 u < sideH₁ d₂.1 d₂.2 u := by
    intro u hu
    dsimp [d₁, d₂]
    exact sideH₁_lt_of_heights hf ha p hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp) (bwlt hf ha hp) u hu
  have hy : z ∈ Set.Ioo (sideH₁ d₁.1 d₁.2 (1 / 2)) (sideH₂ d₂.1 d₂.2 (1 / 2)) := by
    dsimp [d₁, d₂]
    rw [Set.mem_Ioo] at hzI ⊢
    rw [sideH₁_data_half hf ha p hp (bwhh₁ hf ha hp)]
    rw [sideH₂_eq_sideH₁, sideH₁_data_half hf ha p hp (bwhh₂ hf ha hp)]
    exact hzI
  have hin : blendP d₁.1 d₁.2 d₂.1 d₂.2 z x ∈
      betweenChord d₁.1 d₁.2 d₂.1 d₂.2 := blend_inside (hord := hord) hy hx
  have hinC : blendP d₁.1 d₁.2 d₂.1 d₂.2 z x ∈ flatComponent f p := by
    dsimp [d₁, d₂] at hin
    rwa [← bwC hf ha hp] at hin
  have hflat : dN f (blendP d₁.1 d₁.2 d₂.1 d₂.2 z x) = 0 := by
    have hptI : blendP d₁.1 d₁.2 d₂.1 d₂.2 z x ∈ interior (FlatSet f) :=
      flatComponent_subset_flatInterior f p hinC
    have hptF : blendP d₁.1 d₁.2 d₂.1 d₂.2 z x ∈ FlatSet f := interior_subset hptI
    exact (mem_FlatSet.mp hptF).2
  rw [hgp]
  exact hflat

/-- **fi→unc**: a sequence of FLAT-INTERIOR heights converging to an
UNCOVERED degenerate flat height has leaf slopes converging to the
degenerate slope.  Proof by CROSSING CONTRADICTION (as cov→unc): the
blend leaf over a flat-interior height is flat (`dN = 0`,
`blend_graph_dN_zero`) and passes through `(1/2, zₙ)` with slope
`leafSlope zₙ`; a bad subsequence would cross a nearby U-bend. -/
theorem leafSlope_tendsto_fi_at_unc {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f)
    (hni₀ : ¬ IsFlatInterior f (centrePoint y₀)) (hunc₀ : ¬ CoveredHeight (f := f) y₀)
    {z : ℕ → ℝ} (hzfi : ∀ n : ℕ, IsFlatInterior f (centrePoint (z n)))
    (hzt : Tendsto z atTop (𝓝 y₀)) :
    Tendsto (fun n : ℕ => leafSlope hf ha (z n)) atTop
      (𝓝 (degenerateSlope hf ha hy₀F hni₀ hunc₀)) := by
  classical
  by_contra hnot
  rcases exists_bad_subseq_of_not_tendsto hnot with ⟨ε, hε, φ, hφmono, hbad⟩
  -- hbad : ∀ n, ε ≤ |leafSlope hf ha (z (φ n)) − degenerateSlope ...|
  let M₀ : ℝ := degenerateSlope hf ha hy₀F hni₀ hunc₀
  let w : ℕ → ℝ := fun n => uHeightBelowSeq hf ha hy₀F hni₀ hunc₀ n
  let hyW : ∀ n : ℕ, w n ∈ UHeight a f := fun n => uHeightBelowSeq_mem hf ha hy₀F hni₀ hunc₀ n
  let m : ℕ → ℝ := fun n => slopeAtHeight hf ha (hyW n)
  have hw : Tendsto w atTop (𝓝 y₀) := by
    dsimp [w]
    exact uHeightBelowSeq_tendsto hf ha hy₀F hni₀ hunc₀
  have hm : Tendsto m atTop (𝓝 M₀) := by
    dsimp [m, M₀]
    simpa [w, hyW] using degenerateSlope_tendsto hf ha hy₀F hni₀ hunc₀
  have hwU : ∀ n : ℕ, w n ∈ UHeight a f := by
    intro n
    exact hyW n
  -- |c(φ n) − w n| → 0 (both converge to y₀)
  have hcφ : Tendsto (fun n : ℕ => z (φ n)) atTop (𝓝 y₀) := hzt.comp hφmono.tendsto_atTop
  have hsmall : ∀ᶠ n in atTop, |z (φ n) - w n| < ε / 4 := by
    have hc₁ : ∀ᶠ n in atTop, |z (φ n) - y₀| < ε / 8 := by
      rcases (Metric.tendsto_atTop.mp hcφ) (ε / 8) (by positivity) with ⟨N, hN⟩
      refine Filter.eventually_atTop.2 ⟨N, ?_⟩
      intro n hn
      have hd := hN n hn
      simpa [Real.dist_eq] using hd
    have hc₂ : ∀ᶠ n in atTop, |w n - y₀| < ε / 8 := by
      rcases (Metric.tendsto_atTop.mp hw) (ε / 8) (by positivity) with ⟨N, hN⟩
      refine Filter.eventually_atTop.2 ⟨N, ?_⟩
      intro n hn
      have hd := hN n hn
      simpa [Real.dist_eq] using hd
    rcases Filter.eventually_atTop.mp (hc₁.and hc₂) with ⟨N, hN⟩
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have h1 := (hN n hn).1
    have h2 := (hN n hn).2
    have htri : |z (φ n) - w n| ≤ |z (φ n) - y₀| + |w n - y₀| := by
      have h := abs_add_le (z (φ n) - y₀) (y₀ - w n)
      have hsum : (z (φ n) - y₀) + (y₀ - w n) = z (φ n) - w n := by ring
      have h' : |y₀ - w n| = |w n - y₀| := abs_sub_comm y₀ (w n)
      rwa [hsum, h'] at h
    linarith
  have hmid : ∀ᶠ n in atTop, |m n - M₀| < ε / 4 := by
    rcases (Metric.tendsto_atTop.mp hm) (ε / 4) (by positivity) with ⟨N, hN⟩
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hd := hN n hn
    simpa [Real.dist_eq] using hd
  have hboth : ∀ᶠ n in atTop, |z (φ n) - w n| < ε / 4 ∧ |m n - M₀| < ε / 4 := hsmall.and hmid
  rcases Filter.eventually_atTop.mp hboth with ⟨N₀, hN₀⟩
  have hcwN : |z (φ N₀) - w N₀| < ε / 4 := (hN₀ N₀ le_rfl).1
  have hmN : |m N₀ - M₀| < ε / 4 := (hN₀ N₀ le_rfl).2
  -- ε ≤ |leafSlope(c(φ N₀)) − M₀|
  have hbadN : ε ≤ |leafSlope hf ha (z (φ N₀)) - M₀| := by
    simpa [M₀] using hbad N₀
  -- |m N₀ − leafSlope(c(φN₀))| ≥ 3ε/4 via the triangle inequality
  have htri : |leafSlope hf ha (z (φ N₀)) - M₀| ≤
      |leafSlope hf ha (z (φ N₀)) - m N₀| + |m N₀ - M₀| := by
    have h := abs_add_le (leafSlope hf ha (z (φ N₀)) - m N₀) (m N₀ - M₀)
    have hsum : (leafSlope hf ha (z (φ N₀)) - m N₀) + (m N₀ - M₀) =
        leafSlope hf ha (z (φ N₀)) - M₀ := by ring
    rwa [hsum] at h
  have hMmN : 3 * ε / 4 ≤ |leafSlope hf ha (z (φ N₀)) - m N₀| := by
    nlinarith
  have hcrossIneq : |z (φ N₀) - w N₀| < |leafSlope hf ha (z (φ N₀)) - m N₀| / 2 := by
    have h₂ : |leafSlope hf ha (z (φ N₀)) - m N₀| / 2 ≥ 3 * ε / 8 := by nlinarith
    nlinarith
  rcases chord_crossing (c := z (φ N₀)) (M := leafSlope hf ha (z (φ N₀)))
      (w := w N₀) (m := m N₀) hcrossIneq with ⟨xstar, hxstar, hcrossline⟩
  -- the two graph points coincide; one is flat (cov), the other is U
  have hB₀ : dN f (!₂[xstar, chordLine (w N₀) (slopeAtHeight hf ha (hyW N₀)) xstar] : ℝ²) ≠ 0 :=
    ubend_graph_dN_ne_zero hf ha (hyW N₀) hxstar
  have hlin : chordLine (w N₀) (slopeAtHeight hf ha (hyW N₀)) xstar =
      chordLine (z (φ N₀)) (leafSlope hf ha (z (φ N₀))) xstar := by
    -- hcrossline : chordLine c Mleaf xstar = chordLine w m xstar; m = slopeAtHeight
    have hmm : slopeAtHeight hf ha (hyW N₀) = m N₀ := rfl
    rw [hmm]
    exact hcrossline.symm
  have hB : dN f (!₂[xstar, chordLine (z (φ N₀)) (leafSlope hf ha (z (φ N₀))) xstar] : ℝ²) ≠ 0 := by
    have hP : (!₂[xstar, chordLine (w N₀) (slopeAtHeight hf ha (hyW N₀)) xstar] : ℝ²) =
        !₂[xstar, chordLine (z (φ N₀)) (leafSlope hf ha (z (φ N₀))) xstar] := by
      ext i <;> fin_cases i <;> simp [hlin]
    rw [← hP]
    exact hB₀
  have hA : dN f (!₂[xstar, chordLine (z (φ N₀)) (leafSlope hf ha (z (φ N₀))) xstar] : ℝ²) = 0 :=
    blend_graph_dN_zero hf ha (hzfi (φ N₀)) hxstar
  exact hB hA


/-- **U-class restricted convergence at an uncovered target**: among
indices whose heights are `U`, leaf slopes converge to the degenerate
slope. -/
theorem leafSlope_converges_uHeight_unc {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f)
    (hni₀ : ¬ IsFlatInterior f (centrePoint y₀)) (hunc₀ : ¬ CoveredHeight (f := f) y₀)
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 y₀)) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (degenerateSlope hf ha hy₀F hni₀ hunc₀) (fun n : ℕ => z n ∈ UHeight a f) := by
  classical
  intro ε hε
  by_contra hnone
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ z n ∈ UHeight a f ∧
      ε ≤ |leafSlope hf ha (z n) - degenerateSlope hf ha hy₀F hni₀ hunc₀| := by
    intro N
    push_neg at hnone
    rcases hnone N with ⟨n, hN, hC, hlt⟩
    exact ⟨n, hN, hC, hlt⟩
  rcases exists_bad_in_class ε hε hbad with ⟨φ, hφ, hφC, hφbad⟩
  have hzφ : Tendsto (fun m : ℕ => z (φ m)) atTop (𝓝 y₀) := hz.comp hφ.tendsto_atTop
  have hlim := leafSlope_tendsto_uHeight_of_uncovered hf ha hy₀F hni₀ hunc₀ hφC hzφ
  have hlim' : Tendsto (fun m : ℕ => leafSlope hf ha (z (φ m))) atTop
      (𝓝 (degenerateSlope hf ha hy₀F hni₀ hunc₀)) := by
    have hval : leafSlope hf ha y₀ = degenerateSlope hf ha hy₀F hni₀ hunc₀ :=
      leafSlope_eq_degenerateSlope hf ha hy₀F hni₀ hunc₀
    simpa [hval] using hlim
  rcases (Metric.tendsto_atTop.mp hlim') ε hε with ⟨N₂, hN₂⟩
  have hc : |leafSlope hf ha (z (φ N₂)) - degenerateSlope hf ha hy₀F hni₀ hunc₀| < ε := by
    simpa [Real.dist_eq] using hN₂ N₂ le_rfl
  have hb : ε ≤ |leafSlope hf ha (z (φ N₂)) - degenerateSlope hf ha hy₀F hni₀ hunc₀| := hφbad N₂
  linarith

/-- **FI-class restricted convergence at an uncovered target**. -/
theorem leafSlope_converges_fi_unc {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f)
    (hni₀ : ¬ IsFlatInterior f (centrePoint y₀)) (hunc₀ : ¬ CoveredHeight (f := f) y₀)
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 y₀)) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (degenerateSlope hf ha hy₀F hni₀ hunc₀)
      (fun n : ℕ => IsFlatInterior f (centrePoint (z n))) := by
  classical
  intro ε hε
  by_contra hnone
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ IsFlatInterior f (centrePoint (z n)) ∧
      ε ≤ |leafSlope hf ha (z n) - degenerateSlope hf ha hy₀F hni₀ hunc₀| := by
    intro N
    push_neg at hnone
    rcases hnone N with ⟨n, hN, hC, hlt⟩
    exact ⟨n, hN, hC, hlt⟩
  rcases exists_bad_in_class ε hε hbad with ⟨φ, hφ, hφC, hφbad⟩
  have hzφ : Tendsto (fun m : ℕ => z (φ m)) atTop (𝓝 y₀) := hz.comp hφ.tendsto_atTop
  have hlim := leafSlope_tendsto_fi_at_unc hf ha hy₀F hni₀ hunc₀ hφC hzφ
  rcases (Metric.tendsto_atTop.mp hlim) ε hε with ⟨N₂, hN₂⟩
  have hc : |leafSlope hf ha (z (φ N₂)) - degenerateSlope hf ha hy₀F hni₀ hunc₀| < ε := by
    simpa [Real.dist_eq] using hN₂ N₂ le_rfl
  have hb : ε ≤ |leafSlope hf ha (z (φ N₂)) - degenerateSlope hf ha hy₀F hni₀ hunc₀| := hφbad N₂
  linarith

/-- **Cov-class restricted convergence at an uncovered target**. -/
theorem leafSlope_converges_cov_unc {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f)
    (hni₀ : ¬ IsFlatInterior f (centrePoint y₀)) (hunc₀ : ¬ CoveredHeight (f := f) y₀)
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 y₀)) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (degenerateSlope hf ha hy₀F hni₀ hunc₀)
      (fun n : ℕ => CoveredDegenerate (a := a) (f := f) (z n)) := by
  classical
  intro ε hε
  by_contra hnone
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ CoveredDegenerate (a := a) (f := f) (z n) ∧
      ε ≤ |leafSlope hf ha (z n) - degenerateSlope hf ha hy₀F hni₀ hunc₀| := by
    intro N
    push_neg at hnone
    rcases hnone N with ⟨n, hN, hC, hlt⟩
    exact ⟨n, hN, hC, hlt⟩
  rcases exists_bad_in_class ε hε hbad with ⟨φ, hφ, hφC, hφbad⟩
  have hzφ : Tendsto (fun m : ℕ => z (φ m)) atTop (𝓝 y₀) := hz.comp hφ.tendsto_atTop
  have hcov : ∀ m : ℕ, CoveredHeight (f := f) (z (φ m)) := fun m => (hφC m).2.2
  have hlim := leafSlope_tendsto_cov_at_unc hf ha hy₀F hni₀ hunc₀ hcov hzφ
  rcases (Metric.tendsto_atTop.mp hlim) ε hε with ⟨N₂, hN₂⟩
  have hc : |leafSlope hf ha (z (φ N₂)) - degenerateSlope hf ha hy₀F hni₀ hunc₀| < ε := by
    simpa [Real.dist_eq] using hN₂ N₂ le_rfl
  have hb : ε ≤ |leafSlope hf ha (z (φ N₂)) - degenerateSlope hf ha hy₀F hni₀ hunc₀| := hφbad N₂
  linarith

/-- **Unc-class restricted convergence at an uncovered target**. -/
theorem leafSlope_converges_unc_unc {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f)
    (hni₀ : ¬ IsFlatInterior f (centrePoint y₀)) (hunc₀ : ¬ CoveredHeight (f := f) y₀)
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 y₀)) :
    ConvergesOnClass (fun n : ℕ => leafSlope hf ha (z n))
      (degenerateSlope hf ha hy₀F hni₀ hunc₀)
      (fun n : ℕ => UncoveredDegenerate (a := a) (f := f) (z n)) := by
  classical
  intro ε hε
  by_contra hnone
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ UncoveredDegenerate (a := a) (f := f) (z n) ∧
      ε ≤ |leafSlope hf ha (z n) - degenerateSlope hf ha hy₀F hni₀ hunc₀| := by
    intro N
    push_neg at hnone
    rcases hnone N with ⟨n, hN, hC, hlt⟩
    exact ⟨n, hN, hC, hlt⟩
  rcases exists_bad_in_class ε hε hbad with ⟨φ, hφ, hφC, hφbad⟩
  have hzφ : Tendsto (fun m : ℕ => z (φ m)) atTop (𝓝 y₀) := hz.comp hφ.tendsto_atTop
  have huF : ∀ m : ℕ, z (φ m) ∈ FlatHeight a f := by
    intro m
    by_contra hnF
    exact (hφC m).1 ((mem_UHeight_iff_not_FlatHeight (a := a) (f := f)).mpr hnF)
  have huni : ∀ m : ℕ, ¬ IsFlatInterior f (centrePoint (z (φ m))) := fun m => (hφC m).2.1
  have huunc : ∀ m : ℕ, ¬ CoveredHeight (f := f) (z (φ m)) := fun m => (hφC m).2.2
  have hlim := leafSlope_tendsto_uncovered_of_uncovered hf ha hy₀F hni₀ hunc₀ huF huni huunc hzφ
  have hlim' : Tendsto (fun m : ℕ => leafSlope hf ha (z (φ m))) atTop
      (𝓝 (degenerateSlope hf ha hy₀F hni₀ hunc₀)) := by
    have hval : leafSlope hf ha y₀ = degenerateSlope hf ha hy₀F hni₀ hunc₀ :=
      leafSlope_eq_degenerateSlope hf ha hy₀F hni₀ hunc₀
    simpa [hval] using hlim
  rcases (Metric.tendsto_atTop.mp hlim') ε hε with ⟨N₂, hN₂⟩
  have hc : |leafSlope hf ha (z (φ N₂)) - degenerateSlope hf ha hy₀F hni₀ hunc₀| < ε := by
    simpa [Real.dist_eq] using hN₂ N₂ le_rfl
  have hb : ε ≤ |leafSlope hf ha (z (φ N₂)) - degenerateSlope hf ha hy₀F hni₀ hunc₀| := hφbad N₂
  linarith

/-- **FULL sequential continuity of `leafSlope` at an UNCOVERED degenerate
flat height**: any height sequence converging to `y₀` has leaf slopes
converging to the degenerate slope. -/
theorem leafSlope_tendsto_at_uncovered {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f)
    (hni₀ : ¬ IsFlatInterior f (centrePoint y₀)) (hunc₀ : ¬ CoveredHeight (f := f) y₀)
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 y₀)) :
    Tendsto (fun n : ℕ => leafSlope hf ha (z n)) atTop
      (𝓝 (degenerateSlope hf ha hy₀F hni₀ hunc₀)) := by
  exact tendsto_of_classwise (u := fun n : ℕ => leafSlope hf ha (z n))
    (L := degenerateSlope hf ha hy₀F hni₀ hunc₀)
    (fun n : ℕ => height_case (a := a) (f := f) (z n))
    (leafSlope_converges_uHeight_unc hf ha hy₀F hni₀ hunc₀ hz)
    (leafSlope_converges_fi_unc hf ha hy₀F hni₀ hunc₀ hz)
    (leafSlope_converges_cov_unc hf ha hy₀F hni₀ hunc₀ hz)
    (leafSlope_converges_unc_unc hf ha hy₀F hni₀ hunc₀ hz)


/-- `leafSlope` is continuous at every UNCOVERED degenerate flat height
(the metric bridge from the sequential theorem). -/
theorem continuousAt_leafSlope_of_uncovered {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f)
    (hni₀ : ¬ IsFlatInterior f (centrePoint y₀)) (hunc₀ : ¬ CoveredHeight (f := f) y₀) :
    ContinuousAt (fun y : ℝ => leafSlope hf ha y) y₀ := by
  refine continuousAt_of_seq_tendsto ?_
  intro z hz
  have hlim := leafSlope_tendsto_at_uncovered hf ha hy₀F hni₀ hunc₀ hz
  have hval : leafSlope hf ha y₀ = degenerateSlope hf ha hy₀F hni₀ hunc₀ :=
    leafSlope_eq_degenerateSlope hf ha hy₀F hni₀ hunc₀
  simpa [hval] using hlim

/-- `spliceA1` is continuous at every UNCOVERED degenerate flat height. -/
theorem continuousAt_spliceA1_of_uncovered {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f)
    (hni₀ : ¬ IsFlatInterior f (centrePoint y₀)) (hunc₀ : ¬ CoveredHeight (f := f) y₀) :
    ContinuousAt (fun y : ℝ => spliceA1 hf ha y) y₀ := by
  have hcont : ContinuousAt (fun y : ℝ => leafSlope hf ha y) y₀ :=
    continuousAt_leafSlope_of_uncovered hf ha hy₀F hni₀ hunc₀
  have hc : ContinuousAt (fun y : ℝ => y - leafSlope hf ha y / 2) y₀ := by
    have hdiv : ContinuousAt (fun y : ℝ => leafSlope hf ha y / 2) y₀ :=
      hcont.div continuousAt_const (by norm_num)
    exact continuousAt_id.sub hdiv
  have hfun : (fun y : ℝ => spliceA1 hf ha y) = fun y : ℝ => y - leafSlope hf ha y / 2 := by
    funext y
    exact spliceA1_eq_sub_half hf ha y
  rwa [hfun]

/-- `spliceB1` is continuous at every UNCOVERED degenerate flat height. -/
theorem continuousAt_spliceB1_of_uncovered {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f)
    (hni₀ : ¬ IsFlatInterior f (centrePoint y₀)) (hunc₀ : ¬ CoveredHeight (f := f) y₀) :
    ContinuousAt (fun y : ℝ => spliceB1 hf ha y) y₀ := by
  have hcont : ContinuousAt (fun y : ℝ => leafSlope hf ha y) y₀ :=
    continuousAt_leafSlope_of_uncovered hf ha hy₀F hni₀ hunc₀
  have hc : ContinuousAt (fun y : ℝ => y + leafSlope hf ha y / 2) y₀ := by
    have hdiv : ContinuousAt (fun y : ℝ => leafSlope hf ha y / 2) y₀ :=
      hcont.div continuousAt_const (by norm_num)
    exact continuousAt_id.add hdiv
  have hfun : (fun y : ℝ => spliceB1 hf ha y) = fun y : ℝ => y + leafSlope hf ha y / 2 := by
    funext y
    exact spliceB1_eq_add_half hf ha y
  rwa [hfun]

/-- **The left endpoint height function is continuous on ALL of ℝ** — the
union of the U / flat-interior / covered / uncovered height cases. -/
theorem continuous_spliceA1 {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) : Continuous (fun y : ℝ => spliceA1 hf ha y) := by
  rw [continuous_iff_continuousAt]
  intro y
  rcases height_case (a := a) (f := f) y with hyU | hfi | hcov | hunc
  · exact continuousAt_spliceA1_uHeight hf ha hyU
  · exact continuousAt_spliceA1_flatInterior hf ha hfi
  · exact continuousAt_spliceA1_of_covered hf ha hcov.2.2
  · refine continuousAt_spliceA1_of_uncovered hf ha ?_ hunc.2.1 hunc.2.2
    by_contra hnf
    exact hunc.1 ((mem_UHeight_iff_not_FlatHeight (a := a) (f := f)).mpr hnf)

/-- **The right endpoint height function is continuous on ALL of ℝ**. -/
theorem continuous_spliceB1 {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) : Continuous (fun y : ℝ => spliceB1 hf ha y) := by
  rw [continuous_iff_continuousAt]
  intro y
  rcases height_case (a := a) (f := f) y with hyU | hfi | hcov | hunc
  · exact continuousAt_spliceB1_uHeight hf ha hyU
  · exact continuousAt_spliceB1_flatInterior hf ha hfi
  · exact continuousAt_spliceB1_of_covered hf ha hcov.2.2
  · refine continuousAt_spliceB1_of_uncovered hf ha ?_ hunc.2.1 hunc.2.2
    by_contra hnf
    exact hunc.1 ((mem_UHeight_iff_not_FlatHeight (a := a) (f := f)).mpr hnf)

end Submission

import Submission.Work.HeightStructure
import Submission.Work.DegenerateLeafValue

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Leaf-slope API of the spliced chord (GREEN layer 1: value identities)

`m̃(y) := leafSlope hf ha y := (spliceChord hf ha y).slope = B1 − A1` is
the single function whose continuity (together with
`spliceChord_centre`) implies the continuity of the endpoint heights
`spliceA1`/`spliceB1` (the `BandFoliation.cont_left/right` fields):
`spliceA1 y = y − m̃ y / 2`, `spliceB1 y = y + m̃ y / 2` (generic
`BendData` identities, proved first).

Value identities per height region (all green-instantiations):
* `leafSlope_eq_slopeAtHeight` — on `UHeight`, `m̃ = slopeAtHeight`
  (the canonical U-leaf slope), via the endpoint formulas
  `uBendA_atHeight_eq`/`uBendB_atHeight_eq`;
* `leafSlope_eq_degenerateSlope` — at an uncovered degenerate height,
  `m̃ = degenerateSlope` (from `degenerateLeaf_A/B`);
* endpoint-height formulas `spliceA1_eq_uHeight` / `spliceB1_eq_uHeight`
  and `spliceA1_eq_degenerate` / `spliceB1_eq_degenerate` used directly
  by the sequential-continuity layer.

Build: `lake build Submission.Work.HeightSlope` rc=0, zero sorry.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- Generic: `A1 = centreHeight − slope/2` for any `BendData`. -/
lemma BendData_A1_eq_centre_sub_slope_half (b : BendData) :
    b.A 1 = b.centreHeight - b.slope / 2 := by
  unfold BendData.slope BendData.centreHeight
  ring

/-- Generic: `B1 = centreHeight + slope/2` for any `BendData`. -/
lemma BendData_B1_eq_centre_add_slope_half (b : BendData) :
    b.B 1 = b.centreHeight + b.slope / 2 := by
  unfold BendData.slope BendData.centreHeight
  ring

/-- The leaf slope of the spliced chord: `m̃(y) = B1(y) − A1(y)`. -/
def leafSlope {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : ℝ) : ℝ :=
  (spliceChord hf ha y).slope

/-- `spliceA1 y = y − m̃(y)/2` (the centre property of every leaf). -/
lemma spliceA1_eq_sub_half {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : ℝ) : spliceA1 hf ha y = y - leafSlope hf ha y / 2 := by
  unfold spliceA1 leafSlope
  rw [BendData_A1_eq_centre_sub_slope_half]
  rw [spliceChord_centre hf ha y]

/-- `spliceB1 y = y + m̃(y)/2` (the centre property of every leaf). -/
lemma spliceB1_eq_add_half {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : ℝ) : spliceB1 hf ha y = y + leafSlope hf ha y / 2 := by
  unfold spliceB1 leafSlope
  rw [BendData_B1_eq_centre_add_slope_half]
  rw [spliceChord_centre hf ha y]

/-! ## U-region identities -/

/-- The slope of the canonical U-leaf at a `U`-height is the leaf slope. -/
lemma uHeightBend_slope_eq_slopeAtHeight {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (y : UHeight a f) :
    (uHeightBend hf ha y).slope = slopeAtHeight hf ha y.2 := by
  unfold BendData.slope
  have hA := uBendA_atHeight_eq hf ha y.2
  have hB := uBendB_atHeight_eq hf ha y.2
  have hA1 : (uHeightBend hf ha y).A 1 = y.1 - slopeAtHeight hf ha y.2 / 2 := by
    unfold uHeightBend uHeightA
    simpa using (congrArg (fun p : ℝ² => p 1) hA)
  have hB1 : (uHeightBend hf ha y).B 1 = y.1 + slopeAtHeight hf ha y.2 / 2 := by
    unfold uHeightBend uHeightB
    simpa using (congrArg (fun p : ℝ² => p 1) hB)
  rw [hA1, hB1]
  ring

/-- On a `U`-height the spliced leaf slope is `slopeAtHeight`. -/
lemma leafSlope_eq_slopeAtHeight {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hyU : y ∈ UHeight a f) :
    leafSlope hf ha y = slopeAtHeight hf ha hyU := by
  unfold leafSlope
  rw [spliceChord_eq_uHeightBend hf ha hyU]
  exact uHeightBend_slope_eq_slopeAtHeight hf ha ⟨y, hyU⟩

/-- The left endpoint height at a `U`-height (endpoint formula). -/
lemma spliceA1_eq_uHeight {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hyU : y ∈ UHeight a f) :
    spliceA1 hf ha y = y - slopeAtHeight hf ha hyU / 2 := by
  rw [spliceA1_eq_sub_half, leafSlope_eq_slopeAtHeight hf ha hyU]

/-- The right endpoint height at a `U`-height (endpoint formula). -/
lemma spliceB1_eq_uHeight {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hyU : y ∈ UHeight a f) :
    spliceB1 hf ha y = y + slopeAtHeight hf ha hyU / 2 := by
  rw [spliceB1_eq_add_half, leafSlope_eq_slopeAtHeight hf ha hyU]

/-! ## Uncovered-degenerate region identities -/

/-- At an uncovered degenerate height the spliced leaf is the degenerate
leaf, whose slope is `degenerateSlope`. -/
lemma degenerateLeaf_slope_eq_degenerateSlope {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y₀ : ℝ}
    (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    (degenerateLeaf hf ha hy₀F hni hunc).slope = degenerateSlope hf ha hy₀F hni hunc := by
  unfold BendData.slope
  have hA := degenerateLeaf_A hf ha hy₀F hni hunc
  have hB := degenerateLeaf_B hf ha hy₀F hni hunc
  have hA1 : (degenerateLeaf hf ha hy₀F hni hunc).A 1 =
      y₀ - degenerateSlope hf ha hy₀F hni hunc / 2 := by
    simpa using (congrArg (fun p : ℝ² => p 1) hA)
  have hB1 : (degenerateLeaf hf ha hy₀F hni hunc).B 1 =
      y₀ + degenerateSlope hf ha hy₀F hni hunc / 2 := by
    simpa using (congrArg (fun p : ℝ² => p 1) hB)
  rw [hA1, hB1]
  ring

/-- At an uncovered degenerate height the spliced leaf slope equals
`degenerateSlope`. -/
lemma leafSlope_eq_degenerateSlope {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hy₀F : y ∈ FlatHeight a f)
    (hni : ¬ IsFlatInterior f (centrePoint y)) (hunc : ¬ CoveredHeight (f := f) y) :
    leafSlope hf ha y = degenerateSlope hf ha hy₀F hni hunc := by
  unfold leafSlope
  have hyU : y ∉ UHeight a f := by
    intro hyU
    exact ((mem_UHeight_iff_not_FlatHeight (a := a) (f := f)).mp hyU) hy₀F
  rw [spliceChord_eq_uncoveredLeaf hf ha hy₀F hyU hni hunc]
  exact degenerateLeaf_slope_eq_degenerateSlope hf ha hy₀F hni hunc

/-- The left endpoint height at an uncovered degenerate height. -/
lemma spliceA1_eq_degenerate {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hy₀F : y ∈ FlatHeight a f)
    (hni : ¬ IsFlatInterior f (centrePoint y)) (hunc : ¬ CoveredHeight (f := f) y) :
    spliceA1 hf ha y = y - degenerateSlope hf ha hy₀F hni hunc / 2 := by
  rw [spliceA1_eq_sub_half, leafSlope_eq_degenerateSlope hf ha hy₀F hni hunc]

/-- The right endpoint height at an uncovered degenerate height. -/
lemma spliceB1_eq_degenerate {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hy₀F : y ∈ FlatHeight a f)
    (hni : ¬ IsFlatInterior f (centrePoint y)) (hunc : ¬ CoveredHeight (f := f) y) :
    spliceB1 hf ha y = y + degenerateSlope hf ha hy₀F hni hunc / 2 := by
  rw [spliceB1_eq_add_half, leafSlope_eq_degenerateSlope hf ha hy₀F hni hunc]


/-! ## Covered (frontier) region identities -/

/-- The slope of the frontier chord of the covering component at a covered
height: `β − α` for the canonical chord data at that height. -/
def covFrontSlope {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hc : CoveredHeight (f := f) y) : ℝ :=
  (frCompData hf ha (covPoint y hc) (covPoint_hp (y := y) hc) y (covPoint_hh (y := y) hc)).2 -
    (frCompData hf ha (covPoint y hc) (covPoint_hp (y := y) hc) y (covPoint_hh (y := y) hc)).1

/-- The component leaf at its UPPER frontier height is the upper frontier
chord, whose slope is `β₂ − α₂`. -/
lemma flatCompBend_slope_at_upper {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂) :
    (flatCompBend hf ha p hp h₁ h₂ h₂ hh₁ hh₂).slope =
      (frCompData hf ha p hp h₂ hh₂).2 - (frCompData hf ha p hp h₂ hh₂).1 := by
  unfold BendData.slope
  have hA := flatCompBend_upper_A hf ha p hp hh₁ hh₂ hlt
  have hB := flatCompBend_upper_B hf ha p hp hh₁ hh₂ hlt
  have hA1 : (flatCompBend hf ha p hp h₁ h₂ h₂ hh₁ hh₂).A 1 =
      (frCompData hf ha p hp h₂ hh₂).1 := by
    simpa using (congrArg (fun q : ℝ² => q 1) hA)
  have hB1 : (flatCompBend hf ha p hp h₁ h₂ h₂ hh₁ hh₂).B 1 =
      (frCompData hf ha p hp h₂ hh₂).2 := by
    simpa using (congrArg (fun q : ℝ² => q 1) hB)
  rw [hA1, hB1]

/-- The component leaf at its LOWER frontier height is the lower frontier
chord, whose slope is `β₁ − α₁`. -/
lemma flatCompBend_slope_at_lower {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (p : ℝ²) (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂) :
    (flatCompBend hf ha p hp h₁ h₂ h₁ hh₁ hh₂).slope =
      (frCompData hf ha p hp h₁ hh₁).2 - (frCompData hf ha p hp h₁ hh₁).1 := by
  unfold BendData.slope
  have hA := flatCompBend_lower_A hf ha p hp hh₁ hh₂ hlt
  have hB := flatCompBend_lower_B hf ha p hp hh₁ hh₂ hlt
  have hA1 : (flatCompBend hf ha p hp h₁ h₂ h₁ hh₁ hh₂).A 1 =
      (frCompData hf ha p hp h₁ hh₁).1 := by
    simpa using (congrArg (fun q : ℝ² => q 1) hA)
  have hB1 : (flatCompBend hf ha p hp h₁ h₂ h₁ hh₁ hh₂).B 1 =
      (frCompData hf ha p hp h₁ hh₁).2 := by
    simpa using (congrArg (fun q : ℝ² => q 1) hB)
  rw [hA1, hB1]

/-- The covering frontier-chord slope equals the slope of the covered
leaf value (`coveredLeaf` = the component leaf at the frontier height). -/
lemma covFrontSlope_eq_slope_coveredLeaf {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hc : CoveredHeight (f := f) y₀) :
    covFrontSlope hf ha hc = (coveredLeaf hf ha hc).slope := by
  let p : ℝ² := covPoint y₀ hc
  let hp : p ∈ interior (FlatSet f) := covPoint_hp (y := y₀) hc
  let hh₀ : y₀ ∈ frHeights f p := covPoint_hh (y := y₀) hc
  unfold covFrontSlope coveredLeaf compLeaf
  rcases covered_eq_bw hf ha hc with hy₁ | hy₂
  · -- y₀ = bw₁ (lower frontier height)
    have hy₁' : y₀ = bw₁ hf ha hp := by simpa [p, hp] using hy₁
    have hd₀ : frCompData hf ha p hp y₀ hh₀ = frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp) := by
      exact frCompData_congr_height hf ha p hp hy₁' hh₀ (bwhh₁ hf ha hp)
    have hsub : (flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) y₀
          (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).slope =
        (flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) (bw₁ hf ha hp)
          (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).slope := by
      exact congrArg (fun yy : ℝ =>
        (flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) yy
          (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).slope) hy₁'
    calc
      (frCompData hf ha p hp y₀ hh₀).2 - (frCompData hf ha p hp y₀ hh₀).1
          = (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).2 -
              (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).1 := by
            rw [hd₀]
      _ = (flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) (bw₁ hf ha hp)
              (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).slope :=
            (flatCompBend_slope_at_lower hf ha p hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)
              (bwlt hf ha hp)).symm
      _ = (flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) y₀
              (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).slope := hsub.symm
  · -- y₀ = bw₂ (upper frontier height)
    have hy₂' : y₀ = bw₂ hf ha hp := by simpa [p, hp] using hy₂
    have hd₀ : frCompData hf ha p hp y₀ hh₀ = frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp) := by
      exact frCompData_congr_height hf ha p hp hy₂' hh₀ (bwhh₂ hf ha hp)
    have hsub : (flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) y₀
          (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).slope =
        (flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) (bw₂ hf ha hp)
          (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).slope := by
      exact congrArg (fun yy : ℝ =>
        (flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) yy
          (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).slope) hy₂'
    calc
      (frCompData hf ha p hp y₀ hh₀).2 - (frCompData hf ha p hp y₀ hh₀).1
          = (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).2 -
              (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).1 := by
            rw [hd₀]
      _ = (flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) (bw₂ hf ha hp)
              (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).slope :=
            (flatCompBend_slope_at_upper hf ha p hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)
              (bwlt hf ha hp)).symm
      _ = (flatCompBend hf ha p hp (bw₁ hf ha hp) (bw₂ hf ha hp) y₀
              (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)).slope := hsub.symm

theorem leafSlope_eq_covFrontSlope {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hc : CoveredHeight (f := f) y₀) :
    leafSlope hf ha y₀ = covFrontSlope hf ha hc := by
  rw [covFrontSlope_eq_slope_coveredLeaf hf ha hc]
  unfold leafSlope
  have hflat : y₀ ∈ FlatHeight a f := covered_mem_FlatHeight hf hc
  have hfi : ¬ IsFlatInterior f (centrePoint y₀) := covered_not_flatInterior hc
  have hyU : y₀ ∉ UHeight a f := by
    intro hyU
    exact ((mem_UHeight_iff_not_FlatHeight (a := a) (f := f)).mp hyU) hflat
  rw [spliceChord_eq_coveredLeaf hf ha hyU hfi hc]


/-! ## U-sequence limits at degenerate heights (uniform-route steps 1-2) -/

/-- The frontier component at a slice height is flat (every point of
`frCompAt f p h` has `dN = 0`): the chord lies in the frontier of the
component, and frontier points of the flat set are flat. -/
lemma frCompAt_flat {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p z : ℝ²} {h : ℝ} (hh : h ∈ frHeights f p) :
    z ∈ frCompAt f p h → dN f z = 0 := by
  intro hz
  have hzFS : z ∈ frontier (flatComponent f p) ∩ stripInterior :=
    connectedComponentIn_subset (frontier (flatComponent f p) ∩ stripInterior)
      (frSlicePoint f p h) hz
  have hzF : z ∈ frontier (flatComponent f p) := hzFS.1
  have hzS : z ∈ stripInterior := hzFS.2
  have hzFlat := flatComponent_frontier_subset_FlatSet hf hzS hzF
  exact (mem_FlatSet.mp hzFlat).2

/-- A `U`-height sequence converging to a COVERED height has leaf slopes
converging to the frontier-chord slope (`= leafSlope y₀`): the `ε`-slope
limit of `uBend_slope_limit` at the (flat) frontier chord. -/
theorem leafSlope_tendsto_uHeight_of_covered {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hc : CoveredHeight (f := f) y₀) {z : ℕ → ℝ}
    (hzU : ∀ n : ℕ, z n ∈ UHeight a f) (hz : Tendsto z atTop (𝓝 y₀)) :
    Tendsto (fun n : ℕ => leafSlope hf ha (z n)) atTop (𝓝 (leafSlope hf ha y₀)) := by
  let p : ℝ² := covPoint y₀ hc
  let hp : p ∈ interior (FlatSet f) := covPoint_hp (y := y₀) hc
  let hh : y₀ ∈ frHeights f p := covPoint_hh (y := y₀) hc
  have hflat : ∀ z : ℝ², z ∈ stripChord
      (frCompData hf ha p hp y₀ hh).1 (frCompData hf ha p hp y₀ hh).2 → dN f z = 0 := by
    intro w hw
    have hspec := frCompData_spec hf ha p hp hh
    rw [← hspec] at hw
    exact frCompAt_flat hf hh hw
  have hzU' : ∀ n : ℕ, dN f (centrePoint (z n)) ≠ 0 := fun n =>
    (mem_UHeight (a := a) (f := f)).mp (hzU n)
  have hside : Tendsto z atTop (𝓝 (sideH₁
      (frCompData hf ha p hp y₀ hh).1 (frCompData hf ha p hp y₀ hh).2 (1 / 2))) := by
    have hs := sideH₁_data_half hf ha p hp hh
    rw [← hs] at hz
    exact hz
  have hlim := uBend_slope_limit hf ha (y := z) hflat hzU' hside
  have ht : Tendsto (fun n : ℕ => slopeAtHeight hf ha (hzU n)) atTop
      (𝓝 ((frCompData hf ha p hp y₀ hh).2 - (frCompData hf ha p hp y₀ hh).1)) := by
    simpa [slopeAtHeight, hzU'] using hlim
  have heqfun : (fun n : ℕ => leafSlope hf ha (z n)) =ᶠ[atTop]
      fun n : ℕ => slopeAtHeight hf ha (hzU n) := by
    filter_upwards with n
    exact leafSlope_eq_slopeAtHeight hf ha (hzU n)
  have hval : leafSlope hf ha y₀ =
      (frCompData hf ha p hp y₀ hh).2 - (frCompData hf ha p hp y₀ hh).1 := by
    rw [leafSlope_eq_covFrontSlope hf ha hc]
    rfl
  rw [hval]
  exact ht.congr' heqfun.symm

/-- A `U`-height sequence converging to an UNCOVERED degenerate height has
leaf slopes converging to `degenerateSlope y₀ = leafSlope y₀` (brick (C)
value agreement). -/
theorem leafSlope_tendsto_uHeight_of_uncovered {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {y₀ : ℝ}
    (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) {z : ℕ → ℝ}
    (hzU : ∀ n : ℕ, z n ∈ UHeight a f) (hz : Tendsto z atTop (𝓝 y₀)) :
    Tendsto (fun n : ℕ => leafSlope hf ha (z n)) atTop (𝓝 (leafSlope hf ha y₀)) := by
  have ht := slopeLimitOfSeq_tendsto hf ha hzU hz
  have heq : slopeLimitOfSeq hf ha hzU hz = degenerateSlope hf ha hy₀F hni hunc :=
    slopeLimit_eq_degenerateSlope hf ha hy₀F hni hunc hzU hz
  have ht' : Tendsto (fun n : ℕ => slopeAtHeight hf ha (hzU n)) atTop
      (𝓝 (degenerateSlope hf ha hy₀F hni hunc)) := by
    rwa [heq] at ht
  have hval : leafSlope hf ha y₀ = degenerateSlope hf ha hy₀F hni hunc :=
    leafSlope_eq_degenerateSlope hf ha hy₀F hni hunc
  have heqfun : (fun n : ℕ => leafSlope hf ha (z n)) =ᶠ[atTop]
      fun n : ℕ => slopeAtHeight hf ha (hzU n) := by
    filter_upwards with n
    exact leafSlope_eq_slopeAtHeight hf ha (hzU n)
  rw [hval]
  exact ht'.congr' heqfun.symm


end Submission

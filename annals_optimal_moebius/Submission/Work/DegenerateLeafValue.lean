import Submission.Work.UHeightSlope
import Submission.Work.UHeightDichotomy
import Submission.Work.Main0Interface
import Submission.Work.BendImage
import Submission.Work.BendArcFacts
import Submission.Work.FlatDeck
import Submission.Work.FrontierDeck

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Brick (D) of the degenerate-flat-height route: the degenerate leaf value

GREEN (first layer): at an UNCOVERED degenerate flat height `y₀` (flat,
not flat-interior, `¬ CoveredHeight f y₀`), the degenerate LEAF VALUE is
the straight chord through the centreline point `(1/2, y₀)` whose slope is
the brick (C) limit of the slopes of the U-leaves approaching from below
(brick (B) supplies the one-sided U-height sequence).

* `chordThrough y₀ m` — the strip chord `A = (0, y₀−m/2)`, `B = (1, y₀+m/2)`
  (slope `m`, centre height `y₀`);
* `uBendA_atHeight` / `uBendB_atHeight` + endpoint height formulas
  (`uBendA_atHeight_eq` / `uBendB_atHeight_eq`): the canonical U-leaf
  through the U-height `z` has endpoints `(0, z − Δ/2)`,
  `(1, z + Δ/2)` with `Δ = slopeAtHeight`;
* `uHeightBelowSeq` (+ mem / below / tendsto): a U-height sequence below
  `y₀` converging to it (classical choice from
  `UHeightDichotomy.uHeight_accumulate_below_of_uncovered_degenerate`);
* `degenerateSlope` (+ tendsto): the brick (C) limit of the slopes over
  that sequence;
* `degenerateLeaf` = `chordThrough y₀ (degenerateSlope …)` with
  `degenerateLeaf_centre` (centre height `y₀`) and the endpoint formulas.

ALSO GREEN below: **`degenerateLeaf_preBend`**
(`‖f B − f A‖ = ‖B − A‖`, i.e. the degenerate leaf is a genuine pre-bend)
— the approaching U-leaves are isometric images
(`BendImage.bend_length_eq`), their image endpoints converge to `f A` /
`f B` (1-Lipschitz `embedding_lipschitz` bounds along the two boundary
lines: `f_leftEdge_param_tendsto`, `f_rightEdge_param_tendsto`), their
preimage chord lengths converge to `‖B − A‖` (real-square-root limit of
`‖Bₙ−Aₙ‖ = √(1+Δₙ²)`), and `tendsto_nhds_unique` identifies the two
limits.  FURTHER GREEN: **one-sided endpoint continuity from BOTH sides**
(`degenerateLeaf_A/_B_endpoint_tendsto_below/_above`, via the
cross-sequence slope-limit uniqueness `slope_limit_of_two_seq_eq` +
`slopeLimit_eq_degenerateSlope` + the parameter continuity lemmas) and
**the deck identities at the degenerate leaf**
(`degenerateSlope_deck` : `degenerateSlope (y₀+a) = −degenerateSlope y₀`,
from the shifted below-sequence + `slopeAtHeight_flip`, and
`degenerateLeaf_deck_A/_B` matching the `BandFoliation.deck` field shape:
`A(y₀+a) = period a (B y₀)`, `B(y₀+a) = period a (A y₀)`; the
certificates at `y₀+a` come from `flatHeight_add` /
`not_flatInterior_add` / `not_covered_add`, built on
`mem_FlatHeight_add_period`, `not_IsFlatInterior_period`,
`CoveredHeight_period_iff`).  Still to come: splicing the U-height,
component, and degenerate leaves into the TOTAL `chord : ℝ → BendData`
(BandFoliation / Prop main0).
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- The straight chord of the strip through the centreline point
`(1/2, y₀)` with slope `m`: `A = (0, y₀ − m/2)`, `B = (1, y₀ + m/2)`. -/
noncomputable def chordThrough (y₀ m : ℝ) : BendData where
  A := !₂[(0 : ℝ), y₀ - m / 2]
  B := !₂[(1 : ℝ), y₀ + m / 2]
  left_coord := by simp
  right_coord := by simp

/-- The slope of the chord through `(1/2,y₀)` of slope `m` is `m`. -/
lemma chordThrough_slope (y₀ m : ℝ) : (chordThrough y₀ m).slope = m := by
  simp [chordThrough, BendData.slope]

/-- The chord through `(1/2,y₀)` meets the centreline at height `y₀`. -/
lemma chordThrough_centreHeight (y₀ m : ℝ) : (chordThrough y₀ m).centreHeight = y₀ := by
  simp [chordThrough, BendData.centreHeight]

/-- The left endpoint of the canonical U-leaf through the U-height `z`:
`A = (0, z − Δ/2)` with `Δ = slopeAtHeight`. -/
lemma uBendA_atHeight_eq {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {z : ℝ} (hz : z ∈ UHeight a f) :
    uBendA hf ha (centrePoint_mem_stripInterior z) ((mem_UHeight (a := a) (f := f)).mp hz) =
      !₂[(0 : ℝ), z - slopeAtHeight hf ha hz / 2] := by
  let x : ℝ² := centrePoint z
  have hx : x ∈ stripInterior := by dsimp [x]; exact centrePoint_mem_stripInterior z
  have hdN : dN f x ≠ 0 := by dsimp [x]; exact (mem_UHeight (a := a) (f := f)).mp hz
  have hA0 : (uBendA hf ha hx hdN) 0 = 0 := by
    have h := uBendA_leftEdge hf ha hx hdN
    unfold leftEdge at h
    simpa using h
  have hA1 : (uBendA hf ha hx hdN) 1 = z - slopeAtHeight hf ha hz / 2 := by
    dsimp [slopeAtHeight, uBendA, leftParam, uBendSlope]
    have hw0 : (uBendDirPos hf ha hx hdN) 0 ≠ 0 := uBendDirPos_coord_ne_zero hf ha hx hdN
    have hx0 : x 0 = 1 / 2 := by dsimp [x, centrePoint]
    have hx1 : x 1 = z := by dsimp [x, centrePoint]
    simp [ray_coord0, hx0, hx1]
    field_simp [hw0]
    ring
  have hA : uBendA hf ha hx hdN = !₂[0, (uBendA hf ha hx hdN) 1] := by
    exact leftEdge_eq_vec hA0
  rw [hA, hA1]

/-- The right endpoint of the canonical U-leaf through the U-height `z`:
`B = (1, z + Δ/2)` with `Δ = slopeAtHeight`. -/
lemma uBendB_atHeight_eq {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {z : ℝ} (hz : z ∈ UHeight a f) :
    uBendB hf ha (centrePoint_mem_stripInterior z) ((mem_UHeight (a := a) (f := f)).mp hz) =
      !₂[(1 : ℝ), z + slopeAtHeight hf ha hz / 2] := by
  let x : ℝ² := centrePoint z
  have hx : x ∈ stripInterior := by dsimp [x]; exact centrePoint_mem_stripInterior z
  have hdN : dN f x ≠ 0 := by dsimp [x]; exact (mem_UHeight (a := a) (f := f)).mp hz
  have hB1 : (uBendB hf ha hx hdN) 0 = 1 := by
    have h := uBendB_rightEdge hf ha hx hdN
    unfold rightEdge at h
    simpa using h
  have hB1v : (uBendB hf ha hx hdN) 1 = z + slopeAtHeight hf ha hz / 2 := by
    dsimp [slopeAtHeight, uBendB, rightParam, uBendSlope]
    have hw0 : (uBendDirPos hf ha hx hdN) 0 ≠ 0 := uBendDirPos_coord_ne_zero hf ha hx hdN
    have hx0 : x 0 = 1 / 2 := by dsimp [x, centrePoint]
    have hx1 : x 1 = z := by dsimp [x, centrePoint]
    simp [ray_coord0, hx0, hx1]
    field_simp [hw0]
    ring
  have hB : uBendB hf ha hx hdN = !₂[1, (uBendB hf ha hx hdN) 1] := by
    exact rightEdge_eq_vec hB1
  rw [hB, hB1v]

/-- A U-height sequence approaching the degenerate flat height `y₀` from
BELOW (exists by brick (B), `uHeight_accumulate_below_of_uncovered_degenerate`);
used to pin the limiting leaf slope `m₀` (brick (C)). -/
noncomputable def uHeightBelowSeq {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) : ℕ → ℝ :=
  fun n => Classical.choose
    (uHeight_accumulate_below_of_uncovered_degenerate hf ha hy₀F hni hunc (1 / (n + 1)) (by positivity))

/-- The below-sequence consists of U-heights. -/
lemma uHeightBelowSeq_mem {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) (n : ℕ) :
    uHeightBelowSeq hf ha hy₀F hni hunc n ∈ UHeight a f := by
  exact (Classical.choose_spec
    (uHeight_accumulate_below_of_uncovered_degenerate hf ha hy₀F hni hunc (1 / (n + 1)) (by positivity))).1

/-- The below-sequence stays strictly below `y₀`. -/
lemma uHeightBelowSeq_below {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) (n : ℕ) :
    uHeightBelowSeq hf ha hy₀F hni hunc n < y₀ := by
  have hspec := Classical.choose_spec
    (uHeight_accumulate_below_of_uncovered_degenerate hf ha hy₀F hni hunc (1 / (n + 1)) (by positivity))
  rcases hspec with ⟨_hU, huI⟩
  rw [Set.mem_Ioo] at huI
  exact huI.2

/-- The below-sequence converges to `y₀`. -/
lemma uHeightBelowSeq_tendsto {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    Tendsto (uHeightBelowSeq hf ha hy₀F hni hunc) atTop (𝓝 y₀) := by
  have hpts : ∀ n : ℕ, dist (uHeightBelowSeq hf ha hy₀F hni hunc n) y₀ < 1 / (n + 1) := by
    intro n
    have hspec := Classical.choose_spec
      (uHeight_accumulate_below_of_uncovered_degenerate hf ha hy₀F hni hunc (1 / (n + 1)) (by positivity))
    rcases hspec with ⟨_hU, huI⟩
    rw [Set.mem_Ioo] at huI
    unfold uHeightBelowSeq
    rw [dist_eq_norm, Real.norm_eq_abs]
    rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt huI.2))]
    nlinarith [huI.1]
  have hg : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hle : ∀ n : ℕ, ‖uHeightBelowSeq hf ha hy₀F hni hunc n - y₀‖ ≤ (1 : ℝ) / (n + 1) := by
    intro n
    exact le_of_lt (by simpa [dist_eq_norm] using hpts n)
  have hs : Tendsto (fun n : ℕ => ‖uHeightBelowSeq hf ha hy₀F hni hunc n - y₀‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg (uHeightBelowSeq hf ha hy₀F hni hunc n - y₀)) hle hg
  exact (tendsto_iff_dist_tendsto_zero (f := uHeightBelowSeq hf ha hy₀F hni hunc) (x := atTop)
    (a := y₀)).2 (by simpa [dist_eq_norm] using hs)



/-- A U-height sequence approaching the degenerate flat height `y₀` from
ABOVE (mirror of `uHeightBelowSeq`, brick (B) `_above` variant). -/
noncomputable def uHeightAboveSeq {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) : ℕ → ℝ :=
  fun n => Classical.choose
    (uHeight_accumulate_above_of_uncovered_degenerate hf ha hy₀F hni hunc (1 / (n + 1)) (by positivity))

/-- The above-sequence consists of U-heights. -/
lemma uHeightAboveSeq_mem {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) (n : ℕ) :
    uHeightAboveSeq hf ha hy₀F hni hunc n ∈ UHeight a f := by
  exact (Classical.choose_spec
    (uHeight_accumulate_above_of_uncovered_degenerate hf ha hy₀F hni hunc (1 / (n + 1)) (by positivity))).1

/-- The above-sequence stays strictly above `y₀`. -/
lemma uHeightAboveSeq_above {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) (n : ℕ) :
    y₀ < uHeightAboveSeq hf ha hy₀F hni hunc n := by
  have hspec := Classical.choose_spec
    (uHeight_accumulate_above_of_uncovered_degenerate hf ha hy₀F hni hunc (1 / (n + 1)) (by positivity))
  rcases hspec with ⟨_hU, huI⟩
  rw [Set.mem_Ioo] at huI
  exact huI.1

/-- The above-sequence converges to `y₀`. -/
lemma uHeightAboveSeq_tendsto {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    Tendsto (uHeightAboveSeq hf ha hy₀F hni hunc) atTop (𝓝 y₀) := by
  have hpts : ∀ n : ℕ, dist (uHeightAboveSeq hf ha hy₀F hni hunc n) y₀ < 1 / (n + 1) := by
    intro n
    have hspec := Classical.choose_spec
      (uHeight_accumulate_above_of_uncovered_degenerate hf ha hy₀F hni hunc (1 / (n + 1)) (by positivity))
    rcases hspec with ⟨_hU, huI⟩
    rw [Set.mem_Ioo] at huI
    unfold uHeightAboveSeq
    rw [dist_eq_norm, Real.norm_eq_abs]
    rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt huI.1))]
    nlinarith [huI.2]
  have hg : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hle : ∀ n : ℕ, ‖uHeightAboveSeq hf ha hy₀F hni hunc n - y₀‖ ≤ (1 : ℝ) / (n + 1) := by
    intro n
    exact le_of_lt (by simpa [dist_eq_norm] using hpts n)
  have hs : Tendsto (fun n : ℕ => ‖uHeightAboveSeq hf ha hy₀F hni hunc n - y₀‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg (uHeightAboveSeq hf ha hy₀F hni hunc n - y₀)) hle hg
  exact (tendsto_iff_dist_tendsto_zero (f := uHeightAboveSeq hf ha hy₀F hni hunc) (x := atTop)
    (a := y₀)).2 (by simpa [dist_eq_norm] using hs)

/-- The limiting leaf slope at an uncovered degenerate flat height: the
brick (C) limit of the slopes of the approaching below-sequence. -/
noncomputable def degenerateSlope {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) : ℝ :=
  Classical.choose (uBendSlope_tendsto_of_height_tendsto hf ha
    (y := uHeightBelowSeq hf ha hy₀F hni hunc)
    (hyU := uHeightBelowSeq_mem hf ha hy₀F hni hunc)
    (hyy₀ := uHeightBelowSeq_tendsto hf ha hy₀F hni hunc))

/-- The slopes of the below-sequence converge to the degenerate slope. -/
lemma degenerateSlope_tendsto {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    Tendsto (fun n : ℕ => slopeAtHeight hf ha (uHeightBelowSeq_mem hf ha hy₀F hni hunc n))
      atTop (𝓝 (degenerateSlope hf ha hy₀F hni hunc)) := by
  exact (Classical.choose_spec (uBendSlope_tendsto_of_height_tendsto hf ha
    (y := uHeightBelowSeq hf ha hy₀F hni hunc)
    (hyU := uHeightBelowSeq_mem hf ha hy₀F hni hunc)
    (hyy₀ := uHeightBelowSeq_tendsto hf ha hy₀F hni hunc)))

/-- **The degenerate leaf VALUE at an uncovered degenerate flat height**:
the chord through `(1/2, y₀)` of slope `m₀` (the limiting slope of the
approaching U-leaves). -/
noncomputable def degenerateLeaf {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) : BendData :=
  chordThrough y₀ (degenerateSlope hf ha hy₀F hni hunc)

/-- The degenerate leaf meets the centreline point `(1/2, y₀)`. -/
lemma degenerateLeaf_centre {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    (degenerateLeaf hf ha hy₀F hni hunc).centreHeight = y₀ := by
  dsimp [degenerateLeaf]
  exact chordThrough_centreHeight y₀ (degenerateSlope hf ha hy₀F hni hunc)

/-- The left endpoint of the degenerate leaf. -/
lemma degenerateLeaf_A {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    (degenerateLeaf hf ha hy₀F hni hunc).A =
      !₂[(0 : ℝ), y₀ - degenerateSlope hf ha hy₀F hni hunc / 2] := by
  rfl

/-- The right endpoint of the degenerate leaf. -/
lemma degenerateLeaf_B {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    (degenerateLeaf hf ha hy₀F hni hunc).B =
      !₂[(1 : ℝ), y₀ + degenerateSlope hf ha hy₀F hni hunc / 2] := by
  rfl
lemma norm_leftEdge_sub (a b : ℝ) :
    ‖(!₂[0, a] : ℝ²) - !₂[0, b]‖ = |a - b| := by
  have hvec : (!₂[0, a] : ℝ²) - !₂[0, b] = !₂[0, a - b] := by
    ext i <;> fin_cases i <;> simp <;> ring
  rw [hvec]
  exact norm_single_second (a - b)

lemma f_leftEdge_param_tendsto {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀)) :
    Tendsto (fun n : ℕ => f (!₂[0, t n] : ℝ²)) atTop (𝓝 (f (!₂[0, t₀] : ℝ²))) := by
  have hnorm0 : Tendsto (fun n : ℕ => |t n - t₀|) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n : ℕ => t n - t₀) atTop (𝓝 0) := by
      simpa using (ht.sub (tendsto_const_nhds (x := t₀)))
    have hn := hsub.norm
    simpa [Real.norm_eq_abs] using hn
  have hle : ∀ n : ℕ, ‖f (!₂[0, t n] : ℝ²) - f (!₂[0, t₀] : ℝ²)‖ ≤ |t n - t₀| := by
    intro n
    have hL := embedding_lipschitz hf (leftEdge_mem_unitStrip t₀) (leftEdge_mem_unitStrip (t n))
    have hdist : ‖(!₂[0, t n] : ℝ²) - !₂[0, t₀]‖ = |t n - t₀| := norm_leftEdge_sub (t n) t₀
    simpa [hdist] using hL
  have hsq : Tendsto (fun n : ℕ => ‖f (!₂[0, t n] : ℝ²) - f (!₂[0, t₀] : ℝ²)‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg (f (!₂[0, t n] : ℝ²) - f (!₂[0, t₀] : ℝ²))) hle hnorm0
  exact tendsto_nhds_of_norm_sub_tendsto_zero (x := fun n => f (!₂[0, t n] : ℝ²))
    (e := f (!₂[0, t₀] : ℝ²)) (by simpa using hsq)

/-- Along the right boundary line, `t ↦ f (1, t)` is continuous. -/
lemma f_rightEdge_param_tendsto {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀)) :
    Tendsto (fun n : ℕ => f (!₂[1, t n] : ℝ²)) atTop (𝓝 (f (!₂[1, t₀] : ℝ²))) := by
  have hnorm0 : Tendsto (fun n : ℕ => |t n - t₀|) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n : ℕ => t n - t₀) atTop (𝓝 0) := by
      simpa using (ht.sub (tendsto_const_nhds (x := t₀)))
    have hn := hsub.norm
    simpa [Real.norm_eq_abs] using hn
  have hle : ∀ n : ℕ, ‖f (!₂[1, t n] : ℝ²) - f (!₂[1, t₀] : ℝ²)‖ ≤ |t n - t₀| := by
    intro n
    have hL := embedding_lipschitz hf (rightEdge_mem_unitStrip t₀) (rightEdge_mem_unitStrip (t n))
    have hdist : ‖(!₂[1, t n] : ℝ²) - !₂[1, t₀]‖ = |t n - t₀| := dist_rightEdge (t n) t₀
    simpa [hdist] using hL
  have hsq : Tendsto (fun n : ℕ => ‖f (!₂[1, t n] : ℝ²) - f (!₂[1, t₀] : ℝ²)‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg (f (!₂[1, t n] : ℝ²) - f (!₂[1, t₀] : ℝ²))) hle hnorm0
  exact tendsto_nhds_of_norm_sub_tendsto_zero (x := fun n => f (!₂[1, t n] : ℝ²))
    (e := f (!₂[1, t₀] : ℝ²)) (by simpa using hsq)

/-- **The degenerate leaf is a genuine pre-bend**: the image of the chord
through `(1/2, y₀)` of slope `m₀` has the preimage length
`‖f B − f A‖ = ‖B − A‖`.  Proof: the approaching U-leaves (at the heights
`uHeightBelowSeq n → y₀`) have isometric images (`bend_length_eq`), their
image endpoints converge to `f A` / `f B` (1-Lipschitz bounds along the
two boundary lines), their preimage chord lengths converge to `‖B − A‖`
(`‖Bₙ − Aₙ‖ = √(1 + Δₙ²) → √(1 + m₀²)`), and `tendsto_nhds_unique`
identifies the two limits. -/
theorem degenerateLeaf_preBend {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    ‖f (degenerateLeaf hf ha hy₀F hni hunc).B - f (degenerateLeaf hf ha hy₀F hni hunc).A‖ =
    ‖(degenerateLeaf hf ha hy₀F hni hunc).B - (degenerateLeaf hf ha hy₀F hni hunc).A‖ := by
  let m₀ : ℝ := degenerateSlope hf ha hy₀F hni hunc
  have hA : (degenerateLeaf hf ha hy₀F hni hunc).A = !₂[(0 : ℝ), y₀ - m₀ / 2] := by
    rw [degenerateLeaf_A]
  have hB : (degenerateLeaf hf ha hy₀F hni hunc).B = !₂[(1 : ℝ), y₀ + m₀ / 2] := by
    rw [degenerateLeaf_B]
  -- RHS length: ‖B − A‖ = √(1+m₀²)
  have hlenR : ‖(degenerateLeaf hf ha hy₀F hni hunc).B - (degenerateLeaf hf ha hy₀F hni hunc).A‖ =
      Real.sqrt (1 + m₀ ^ 2) := by
    rw [hA, hB]
    have hpre := preimage_chord_length (y₀ - m₀ / 2) (y₀ + m₀ / 2)
    have hdiff : (y₀ + m₀ / 2) - (y₀ - m₀ / 2) = m₀ := by ring
    simpa [hdiff] using hpre
  -- LHS: limit over approaching leaves
  let b : ℕ → ℝ := uHeightBelowSeq hf ha hy₀F hni hunc
  have hb : Tendsto b atTop (𝓝 y₀) := by simpa [b] using (uHeightBelowSeq_tendsto hf ha hy₀F hni hunc)
  let s : ℕ → ℝ := fun n => slopeAtHeight hf ha (uHeightBelowSeq_mem hf ha hy₀F hni hunc n)
  have hs : Tendsto s atTop (𝓝 m₀) := by
    dsimp [s, m₀]
    exact degenerateSlope_tendsto hf ha hy₀F hni hunc
  -- endpoint limits along the edges
  have hfAL : Tendsto (fun n : ℕ => f (!₂[0, b n - s n / 2] : ℝ²)) atTop
      (𝓝 (f (!₂[0, y₀ - m₀ / 2] : ℝ²))) := by
    have hshalf : Tendsto (fun n : ℕ => s n / 2) atTop (𝓝 (m₀ / 2)) := by
      have hmul := hs.const_mul ((1 : ℝ) / 2)
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    have ht : Tendsto (fun n : ℕ => b n - s n / 2) atTop (𝓝 (y₀ - m₀ / 2)) := by
      simpa using (hb.sub hshalf)
    exact f_leftEdge_param_tendsto hf (t := fun n => b n - s n / 2) (t₀ := y₀ - m₀ / 2) ht
  have hshalf : Tendsto (fun n : ℕ => s n / 2) atTop (𝓝 (m₀ / 2)) := by
    have hmul := hs.const_mul ((1 : ℝ) / 2)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hfBR : Tendsto (fun n : ℕ => f (!₂[1, b n + s n / 2] : ℝ²)) atTop
      (𝓝 (f (!₂[1, y₀ + m₀ / 2] : ℝ²))) := by
    have ht : Tendsto (fun n : ℕ => b n + s n / 2) atTop (𝓝 (y₀ + m₀ / 2)) := by
      simpa using (hb.add hshalf)
    exact f_rightEdge_param_tendsto hf (t := fun n => b n + s n / 2) (t₀ := y₀ + m₀ / 2) ht
  -- the images of the approaching leaf endpoints converge to f A / f B
  let IA : ℕ → ℝ³ := fun n => f (uBendA hf ha (centrePoint_mem_stripInterior (b n))
    ((mem_UHeight (a := a) (f := f)).mp (uHeightBelowSeq_mem hf ha hy₀F hni hunc n)))
  let IB : ℕ → ℝ³ := fun n => f (uBendB hf ha (centrePoint_mem_stripInterior (b n))
    ((mem_UHeight (a := a) (f := f)).mp (uHeightBelowSeq_mem hf ha hy₀F hni hunc n)))
  have hIAeq : (fun n : ℕ => f (!₂[0, b n - s n / 2] : ℝ²)) =ᶠ[atTop] IA := by
    filter_upwards with n
    congr 1
    have hE := uBendA_atHeight_eq hf ha (uHeightBelowSeq_mem hf ha hy₀F hni hunc n)
    exact hE.symm
  have hIBeq : (fun n : ℕ => f (!₂[1, b n + s n / 2] : ℝ²)) =ᶠ[atTop] IB := by
    filter_upwards with n
    congr 1
    have hE := uBendB_atHeight_eq hf ha (uHeightBelowSeq_mem hf ha hy₀F hni hunc n)
    exact hE.symm
  have hIA : Tendsto IA atTop (𝓝 (f ((degenerateLeaf hf ha hy₀F hni hunc).A))) := by
    have hh := hfAL.congr' hIAeq
    simpa [hA] using hh
  have hIB : Tendsto IB atTop (𝓝 (f ((degenerateLeaf hf ha hy₀F hni hunc).B))) := by
    have hh := hfBR.congr' hIBeq
    simpa [hB] using hh
  -- the norm of the image difference converges to ‖fB − fA‖
  have hdiff_img : Tendsto (fun n : ℕ => IB n - IA n) atTop
      (𝓝 (f ((degenerateLeaf hf ha hy₀F hni hunc).B) -
          f ((degenerateLeaf hf ha hy₀F hni hunc).A))) := by
    dsimp [IA, IB] at hIA hIB
    simpa using (hIB.sub hIA)
  have hLHS_norm : Tendsto (fun n : ℕ => ‖IB n - IA n‖) atTop
      (𝓝 ‖f ((degenerateLeaf hf ha hy₀F hni hunc).B) -
          f ((degenerateLeaf hf ha hy₀F hni hunc).A)‖) := by
    exact hdiff_img.norm
  -- preimage chord lengths of the approaching leaves converge to ‖B − A‖
  have hpre_len : ∀ n : ℕ, ‖uBendB hf ha (centrePoint_mem_stripInterior (b n))
        ((mem_UHeight (a := a) (f := f)).mp (uHeightBelowSeq_mem hf ha hy₀F hni hunc n)) -
        uBendA hf ha (centrePoint_mem_stripInterior (b n))
        ((mem_UHeight (a := a) (f := f)).mp (uHeightBelowSeq_mem hf ha hy₀F hni hunc n))‖ =
      Real.sqrt (1 + (s n) ^ 2) := by
    intro n
    have hAe := uBendA_atHeight_eq hf ha (uHeightBelowSeq_mem hf ha hy₀F hni hunc n)
    have hBe := uBendB_atHeight_eq hf ha (uHeightBelowSeq_mem hf ha hy₀F hni hunc n)
    rw [hAe, hBe]
    have hpre := preimage_chord_length (b n - s n / 2) (b n + s n / 2)
    have hdiff : (b n + s n / 2) - (b n - s n / 2) = s n := by ring
    simpa [hdiff] using hpre
  have hs_sqrt : Tendsto (fun n : ℕ => Real.sqrt (1 + (s n) ^ 2)) atTop (𝓝 (Real.sqrt (1 + m₀ ^ 2))) := by
    have hc : ContinuousAt (fun x : ℝ => Real.sqrt (1 + x ^ 2)) m₀ := by fun_prop
    exact (hc.tendsto.comp hs)
  have hRHS_norm : Tendsto (fun n : ℕ => ‖uBendB hf ha (centrePoint_mem_stripInterior (b n))
        ((mem_UHeight (a := a) (f := f)).mp (uHeightBelowSeq_mem hf ha hy₀F hni hunc n)) -
        uBendA hf ha (centrePoint_mem_stripInterior (b n))
        ((mem_UHeight (a := a) (f := f)).mp (uHeightBelowSeq_mem hf ha hy₀F hni hunc n))‖)
      atTop (𝓝 ‖(degenerateLeaf hf ha hy₀F hni hunc).B - (degenerateLeaf hf ha hy₀F hni hunc).A‖) := by
    have hpt : (fun n : ℕ => ‖uBendB hf ha (centrePoint_mem_stripInterior (b n))
        ((mem_UHeight (a := a) (f := f)).mp (uHeightBelowSeq_mem hf ha hy₀F hni hunc n)) -
        uBendA hf ha (centrePoint_mem_stripInterior (b n))
        ((mem_UHeight (a := a) (f := f)).mp (uHeightBelowSeq_mem hf ha hy₀F hni hunc n))‖) =ᶠ[atTop]
        fun n : ℕ => Real.sqrt (1 + (s n) ^ 2) := by
      filter_upwards with n
      exact hpre_len n
    have htarget : Real.sqrt (1 + m₀ ^ 2) =
        ‖(degenerateLeaf hf ha hy₀F hni hunc).B - (degenerateLeaf hf ha hy₀F hni hunc).A‖ :=
      hlenR.symm
    simpa [htarget] using hs_sqrt.congr' hpt.symm
  -- per-n image isometry carries the limit to the LHS sequence
  have hbend : ∀ n : ℕ, ‖IB n - IA n‖ =
      ‖uBendB hf ha (centrePoint_mem_stripInterior (b n))
        ((mem_UHeight (a := a) (f := f)).mp (uHeightBelowSeq_mem hf ha hy₀F hni hunc n)) -
        uBendA hf ha (centrePoint_mem_stripInterior (b n))
        ((mem_UHeight (a := a) (f := f)).mp (uHeightBelowSeq_mem hf ha hy₀F hni hunc n))‖ := by
    intro n
    dsimp [IA, IB]
    exact bend_length_eq hf ha (centrePoint_mem_stripInterior (b n))
      ((mem_UHeight (a := a) (f := f)).mp (uHeightBelowSeq_mem hf ha hy₀F hni hunc n))
  have hLHS2 : Tendsto (fun n : ℕ => ‖IB n - IA n‖) atTop
      (𝓝 ‖(degenerateLeaf hf ha hy₀F hni hunc).B - (degenerateLeaf hf ha hy₀F hni hunc).A‖) := by
    have hpt : (fun n : ℕ => ‖uBendB hf ha (centrePoint_mem_stripInterior (b n))
        ((mem_UHeight (a := a) (f := f)).mp (uHeightBelowSeq_mem hf ha hy₀F hni hunc n)) -
        uBendA hf ha (centrePoint_mem_stripInterior (b n))
        ((mem_UHeight (a := a) (f := f)).mp (uHeightBelowSeq_mem hf ha hy₀F hni hunc n))‖) =ᶠ[atTop]
        fun n : ℕ => ‖IB n - IA n‖ := by
      filter_upwards with n
      exact (hbend n).symm
    exact (hRHS_norm.congr' hpt)
  exact tendsto_nhds_unique hLHS_norm hLHS2



/-- The brick (C) slope limit of a given U-height sequence converging to
`y₀`. -/
noncomputable def slopeLimitOfSeq {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} {y : ℕ → ℝ}
    (hyU : ∀ n : ℕ, y n ∈ UHeight a f) (hyy₀ : Tendsto y atTop (𝓝 y₀)) : ℝ :=
  Classical.choose (uBendSlope_tendsto_of_height_tendsto hf ha (y := y) hyU hyy₀)

/-- The slopes over the sequence converge to its slope limit. -/
lemma slopeLimitOfSeq_tendsto {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} {y : ℕ → ℝ}
    (hyU : ∀ n : ℕ, y n ∈ UHeight a f) (hyy₀ : Tendsto y atTop (𝓝 y₀)) :
    Tendsto (fun n : ℕ => slopeAtHeight hf ha (hyU n)) atTop
      (𝓝 (slopeLimitOfSeq hf ha hyU hyy₀)) := by
  exact (Classical.choose_spec (uBendSlope_tendsto_of_height_tendsto hf ha (y := y) hyU hyy₀))

/-- The left-edge parametrisation `t ↦ (0, t)` is continuous. -/
lemma leftEdge_param_tendsto {t : ℕ → ℝ} {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀)) :
    Tendsto (fun n : ℕ => (!₂[(0 : ℝ), t n] : ℝ²)) atTop (𝓝 (!₂[(0 : ℝ), t₀] : ℝ²)) := by
  have hnorm0 : Tendsto (fun n : ℕ => |t n - t₀|) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n : ℕ => t n - t₀) atTop (𝓝 0) := by
      simpa using (ht.sub (tendsto_const_nhds (x := t₀)))
    have hn := hsub.norm
    simpa [Real.norm_eq_abs] using hn
  have hle : ∀ n : ℕ, ‖(!₂[(0 : ℝ), t n] : ℝ²) - !₂[(0 : ℝ), t₀]‖ ≤ |t n - t₀| := by
    intro n
    exact le_of_eq (norm_leftEdge_sub (t n) t₀)
  have hsq : Tendsto (fun n : ℕ => ‖(!₂[(0 : ℝ), t n] : ℝ²) - !₂[(0 : ℝ), t₀]‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg ((!₂[(0 : ℝ), t n] : ℝ²) - !₂[(0 : ℝ), t₀])) hle hnorm0
  exact tendsto_nhds_of_norm_sub_tendsto_zero (x := fun n => (!₂[(0 : ℝ), t n] : ℝ²))
    (e := (!₂[(0 : ℝ), t₀] : ℝ²)) (by simpa using hsq)

/-- The right-edge parametrisation `t ↦ (1, t)` is continuous. -/
lemma rightEdge_param_tendsto {t : ℕ → ℝ} {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀)) :
    Tendsto (fun n : ℕ => (!₂[(1 : ℝ), t n] : ℝ²)) atTop (𝓝 (!₂[(1 : ℝ), t₀] : ℝ²)) := by
  have hnorm0 : Tendsto (fun n : ℕ => |t n - t₀|) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n : ℕ => t n - t₀) atTop (𝓝 0) := by
      simpa using (ht.sub (tendsto_const_nhds (x := t₀)))
    have hn := hsub.norm
    simpa [Real.norm_eq_abs] using hn
  have hle : ∀ n : ℕ, ‖(!₂[(1 : ℝ), t n] : ℝ²) - !₂[(1 : ℝ), t₀]‖ ≤ |t n - t₀| := by
    intro n
    exact le_of_eq (dist_rightEdge (t n) t₀)
  have hsq : Tendsto (fun n : ℕ => ‖(!₂[(1 : ℝ), t n] : ℝ²) - !₂[(1 : ℝ), t₀]‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg ((!₂[(1 : ℝ), t n] : ℝ²) - !₂[(1 : ℝ), t₀])) hle hnorm0
  exact tendsto_nhds_of_norm_sub_tendsto_zero (x := fun n => (!₂[(1 : ℝ), t n] : ℝ²))
    (e := (!₂[(1 : ℝ), t₀] : ℝ²)) (by simpa using hsq)

/-- **Endpoint continuity (left), generic**: for a U-height sequence
`yₙ → y₀`, the left endpoints of the U-leaves converge to the left end of
the chord through `(1/2,y₀)` with the slope limit. -/
lemma uBendA_tendsto_of_height {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} {y : ℕ → ℝ}
    (hyU : ∀ n : ℕ, y n ∈ UHeight a f) (hyy₀ : Tendsto y atTop (𝓝 y₀)) :
    Tendsto (fun n : ℕ => uBendA hf ha (centrePoint_mem_stripInterior (y n))
        ((mem_UHeight (a := a) (f := f)).mp (hyU n))) atTop
      (𝓝 (!₂[(0 : ℝ), y₀ - slopeLimitOfSeq hf ha hyU hyy₀ / 2] : ℝ²)) := by
  let s : ℕ → ℝ := fun n => slopeAtHeight hf ha (hyU n)
  have hs : Tendsto s atTop (𝓝 (slopeLimitOfSeq hf ha hyU hyy₀)) := by
    dsimp [s]
    exact slopeLimitOfSeq_tendsto hf ha hyU hyy₀
  have hshalf : Tendsto (fun n : ℕ => s n / 2) atTop (𝓝 (slopeLimitOfSeq hf ha hyU hyy₀ / 2)) := by
    have hmul := hs.const_mul ((1 : ℝ) / 2)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have ht : Tendsto (fun n : ℕ => y n - s n / 2) atTop (𝓝 (y₀ - slopeLimitOfSeq hf ha hyU hyy₀ / 2)) := by
    simpa using (hyy₀.sub hshalf)
  have hv := leftEdge_param_tendsto (t := fun n => y n - s n / 2)
    (t₀ := y₀ - slopeLimitOfSeq hf ha hyU hyy₀ / 2) ht
  have heq : (fun n : ℕ => (!₂[(0 : ℝ), y n - s n / 2] : ℝ²)) =ᶠ[atTop]
      fun n : ℕ => uBendA hf ha (centrePoint_mem_stripInterior (y n))
        ((mem_UHeight (a := a) (f := f)).mp (hyU n)) := by
    filter_upwards with n
    have hE := uBendA_atHeight_eq hf ha (hyU n)
    rw [hE]
  exact hv.congr' heq

/-- **Endpoint continuity (right), generic**. -/
lemma uBendB_tendsto_of_height {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} {y : ℕ → ℝ}
    (hyU : ∀ n : ℕ, y n ∈ UHeight a f) (hyy₀ : Tendsto y atTop (𝓝 y₀)) :
    Tendsto (fun n : ℕ => uBendB hf ha (centrePoint_mem_stripInterior (y n))
        ((mem_UHeight (a := a) (f := f)).mp (hyU n))) atTop
      (𝓝 (!₂[(1 : ℝ), y₀ + slopeLimitOfSeq hf ha hyU hyy₀ / 2] : ℝ²)) := by
  let s : ℕ → ℝ := fun n => slopeAtHeight hf ha (hyU n)
  have hs : Tendsto s atTop (𝓝 (slopeLimitOfSeq hf ha hyU hyy₀)) := by
    dsimp [s]
    exact slopeLimitOfSeq_tendsto hf ha hyU hyy₀
  have hshalf : Tendsto (fun n : ℕ => s n / 2) atTop (𝓝 (slopeLimitOfSeq hf ha hyU hyy₀ / 2)) := by
    have hmul := hs.const_mul ((1 : ℝ) / 2)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have ht : Tendsto (fun n : ℕ => y n + s n / 2) atTop (𝓝 (y₀ + slopeLimitOfSeq hf ha hyU hyy₀ / 2)) := by
    simpa using (hyy₀.add hshalf)
  have hv := rightEdge_param_tendsto (t := fun n => y n + s n / 2)
    (t₀ := y₀ + slopeLimitOfSeq hf ha hyU hyy₀ / 2) ht
  have heq : (fun n : ℕ => (!₂[(1 : ℝ), y n + s n / 2] : ℝ²)) =ᶠ[atTop]
      fun n : ℕ => uBendB hf ha (centrePoint_mem_stripInterior (y n))
        ((mem_UHeight (a := a) (f := f)).mp (hyU n)) := by
    filter_upwards with n
    have hE := uBendB_atHeight_eq hf ha (hyU n)
    rw [hE]
  exact hv.congr' heq
lemma slope_limit_of_two_seq_eq {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ}
    {y₁ : ℕ → ℝ} (hy₁U : ∀ n : ℕ, y₁ n ∈ UHeight a f) (hy₁t : Tendsto y₁ atTop (𝓝 y₀))
    {y₂ : ℕ → ℝ} (hy₂U : ∀ n : ℕ, y₂ n ∈ UHeight a f) (hy₂t : Tendsto y₂ atTop (𝓝 y₀))
    {m₁ m₂ : ℝ}
    (hm₁ : Tendsto (fun n : ℕ => slopeAtHeight hf ha (hy₁U n)) atTop (𝓝 m₁))
    (hm₂ : Tendsto (fun n : ℕ => slopeAtHeight hf ha (hy₂U n)) atTop (𝓝 m₂)) :
    m₁ = m₂ := by
  let e : ℝ² := centrePoint y₀
  let q₁ : ℕ → ℝ² := fun n => centrePoint (y₁ n)
  let q₂ : ℕ → ℝ² := fun n => centrePoint (y₂ n)
  let v₁ : ℕ → ℝ² := fun n => unitDirAtHeight f (y₁ n)
  let v₂ : ℕ → ℝ² := fun n => unitDirAtHeight f (y₂ n)
  let Δ₁ : ℕ → ℝ := fun n => slopeAtHeight hf ha (hy₁U n)
  let Δ₂ : ℕ → ℝ := fun n => slopeAtHeight hf ha (hy₂U n)
  let C : ℝ := (a ^ 2 - 1) / (2 * a)
  have hq₁S : ∀ n : ℕ, q₁ n ∈ stripInterior := by
    intro n; dsimp [q₁]; exact centrePoint_mem_stripInterior (y₁ n)
  have hq₁U : ∀ n : ℕ, dN f (q₁ n) ≠ 0 := by
    intro n; dsimp [q₁]; exact (mem_UHeight (a := a) (f := f)).mp (hy₁U n)
  have hq₁e : Tendsto q₁ atTop (𝓝 e) := by
    dsimp [q₁, e]; exact centrePoint_tendsto hy₁t
  have hq₂S : ∀ n : ℕ, q₂ n ∈ stripInterior := by
    intro n; dsimp [q₂]; exact centrePoint_mem_stripInterior (y₂ n)
  have hq₂U : ∀ n : ℕ, dN f (q₂ n) ≠ 0 := by
    intro n; dsimp [q₂]; exact (mem_UHeight (a := a) (f := f)).mp (hy₂U n)
  have hq₂e : Tendsto q₂ atTop (𝓝 e) := by
    dsimp [q₂, e]; exact centrePoint_tendsto hy₂t
  have heS : e ∈ stripInterior := by
    dsimp [e]; exact centrePoint_mem_stripInterior y₀
  have hv₁def : ∀ n : ℕ, v₁ n = unitKernelDir f (q₁ n) := by
    intro n; dsimp [v₁, q₁, unitDirAtHeight]
  have hv₂def : ∀ n : ℕ, v₂ n = unitKernelDir f (q₂ n) := by
    intro n; dsimp [v₂, q₂, unitDirAtHeight]
  have hΔ₁ratio : ∀ n : ℕ, Δ₁ n = (v₁ n) 1 / (v₁ n) 0 := by
    intro n
    rw [show Δ₁ n = slopeAtHeight hf ha (hy₁U n) by rfl, hv₁def n]
    dsimp [slopeAtHeight]
    exact uBendSlope_eq_unitKernelDir_ratio hf ha (hq₁S n) (hq₁U n)
  have hΔ₂ratio : ∀ n : ℕ, Δ₂ n = (v₂ n) 1 / (v₂ n) 0 := by
    intro n
    rw [show Δ₂ n = slopeAtHeight hf ha (hy₂U n) by rfl, hv₂def n]
    dsimp [slopeAtHeight]
    exact uBendSlope_eq_unitKernelDir_ratio hf ha (hq₂S n) (hq₂U n)
  have hC0 : 0 ≤ C := by
    dsimp [C]; exact uBendDispCoeff_nonneg_UHeight hf ha (hy₁U 0)
  have hv₁unit : ∀ n : ℕ, ‖v₁ n‖ = 1 := by
    intro n; rw [hv₁def n]
    exact norm_unitKernelDir (V2f_ne_zero_at_U hf ha (hq₁S n) (hq₁U n))
  have hv₂unit : ∀ n : ℕ, ‖v₂ n‖ = 1 := by
    intro n; rw [hv₂def n]
    exact norm_unitKernelDir (V2f_ne_zero_at_U hf ha (hq₂S n) (hq₂U n))
  let c₀ : ℝ := 1 / Real.sqrt (1 + C ^ 2)
  have hv₁₀lb : ∀ n : ℕ, c₀ ≤ |(v₁ n) 0| := by
    intro n
    have hlb := unitKernelDir_coord0_lower_UHeight hf ha (hy₁U n)
    dsimp [c₀, C, v₁, unitDirAtHeight, q₁] at hlb ⊢
    exact hlb
  have hv₂₀lb : ∀ n : ℕ, c₀ ≤ |(v₂ n) 0| := by
    intro n
    have hlb := unitKernelDir_coord0_lower_UHeight hf ha (hy₂U n)
    dsimp [c₀, C, v₂, unitDirAtHeight, q₂] at hlb ⊢
    exact hlb
  have hc₀pos : 0 < c₀ := by
    dsimp [c₀]
    have hsq : 0 < Real.sqrt (1 + C ^ 2) := Real.sqrt_pos.2 (by nlinarith [sq_nonneg C])
    exact div_pos (by norm_num) hsq
  have hv₁0nz : ∀ n : ℕ, (v₁ n) 0 ≠ 0 := by
    intro n; exact (abs_pos.mp (lt_of_lt_of_le hc₀pos (hv₁₀lb n)))
  have hv₂0nz : ∀ n : ℕ, (v₂ n) 0 ≠ 0 := by
    intro n; exact (abs_pos.mp (lt_of_lt_of_le hc₀pos (hv₂₀lb n)))
  have hΔ₁ : Tendsto Δ₁ atTop (𝓝 m₁) := by
    dsimp [Δ₁]; exact hm₁
  have hΔ₂ : Tendsto Δ₂ atTop (𝓝 m₂) := by
    dsimp [Δ₂]; exact hm₂
  -- direction sub-subsequences
  have hvb₁ : Bornology.IsBounded (Set.range v₁) := by
    exact isBounded_range_unit (v := v₁) (fun n => hv₁unit n)
  rcases tendsto_subseq_of_bounded hvb₁ (x := v₁) (fun n => Set.mem_range_self n) with
    ⟨w₁, _hw₁cl, ψ₁, hψ₁, hvw₁⟩
  have hvb₂ : Bornology.IsBounded (Set.range v₂) := by
    exact isBounded_range_unit (v := v₂) (fun n => hv₂unit n)
  rcases tendsto_subseq_of_bounded hvb₂ (x := v₂) (fun n => Set.mem_range_self n) with
    ⟨w₂, _hw₂cl, ψ₂, hψ₂, hvw₂⟩
  have hw₁₀lb : c₀ ≤ |w₁ 0| := by
    have hc0 : ContinuousAt (fun z : ℝ² => |z 0|) w₁ := by fun_prop
    have ht : Tendsto (fun n : ℕ => |((v₁ ∘ ψ₁) n) 0|) atTop (𝓝 |w₁ 0|) := (hc0.tendsto.comp hvw₁)
    have hpt : ∀ n : ℕ, c₀ ≤ |((v₁ ∘ ψ₁) n) 0| := by
      intro n; exact hv₁₀lb (ψ₁ n)
    exact ge_of_tendsto ht (Filter.Eventually.of_forall hpt)
  have hw₁₀nz : w₁ 0 ≠ 0 := by
    exact (abs_pos.mp (lt_of_lt_of_le hc₀pos hw₁₀lb))
  have hm₁w : m₁ = w₁ 1 / w₁ 0 := by
    have hΔ₁' : Tendsto (Δ₁ ∘ ψ₁) atTop (𝓝 m₁) := hΔ₁.comp hψ₁.tendsto_atTop
    have heq : (fun n : ℕ => Δ₁ (ψ₁ n)) =ᶠ[atTop]
        fun n : ℕ => (((v₁ ∘ ψ₁) n) 1) / (((v₁ ∘ ψ₁) n) 0) := by
      filter_upwards with n
      exact hΔ₁ratio (ψ₁ n)
    have hΔ₁'' : Tendsto (fun n : ℕ => (((v₁ ∘ ψ₁) n) 1) / (((v₁ ∘ ψ₁) n) 0)) atTop (𝓝 m₁) :=
      hΔ₁'.congr' heq
    have hr₁ : Tendsto (fun n : ℕ => (((v₁ ∘ ψ₁) n) 1) / (((v₁ ∘ ψ₁) n) 0)) atTop
        (𝓝 (w₁ 1 / w₁ 0)) :=
      tendsto_coord_ratio hvw₁ hw₁₀nz (by intro n; exact hv₁0nz (ψ₁ n))
    exact tendsto_nhds_unique hΔ₁'' hr₁
  have hw₂₀lb : c₀ ≤ |w₂ 0| := by
    have hc0 : ContinuousAt (fun z : ℝ² => |z 0|) w₂ := by fun_prop
    have ht : Tendsto (fun n : ℕ => |((v₂ ∘ ψ₂) n) 0|) atTop (𝓝 |w₂ 0|) := (hc0.tendsto.comp hvw₂)
    have hpt : ∀ n : ℕ, c₀ ≤ |((v₂ ∘ ψ₂) n) 0| := by
      intro n; exact hv₂₀lb (ψ₂ n)
    exact ge_of_tendsto ht (Filter.Eventually.of_forall hpt)
  have hw₂₀nz : w₂ 0 ≠ 0 := by
    exact (abs_pos.mp (lt_of_lt_of_le hc₀pos hw₂₀lb))
  have hm₂w : m₂ = w₂ 1 / w₂ 0 := by
    have hΔ₂' : Tendsto (Δ₂ ∘ ψ₂) atTop (𝓝 m₂) := hΔ₂.comp hψ₂.tendsto_atTop
    have heq : (fun n : ℕ => Δ₂ (ψ₂ n)) =ᶠ[atTop]
        fun n : ℕ => (((v₂ ∘ ψ₂) n) 1) / (((v₂ ∘ ψ₂) n) 0) := by
      filter_upwards with n
      exact hΔ₂ratio (ψ₂ n)
    have hΔ₂'' : Tendsto (fun n : ℕ => (((v₂ ∘ ψ₂) n) 1) / (((v₂ ∘ ψ₂) n) 0)) atTop (𝓝 m₂) :=
      hΔ₂'.congr' heq
    have hr₂ : Tendsto (fun n : ℕ => (((v₂ ∘ ψ₂) n) 1) / (((v₂ ∘ ψ₂) n) 0)) atTop
        (𝓝 (w₂ 1 / w₂ 0)) :=
      tendsto_coord_ratio hvw₂ hw₂₀nz (by intro n; exact hv₂0nz (ψ₂ n))
    exact tendsto_nhds_unique hΔ₂'' hr₂
  have hpar : w₁ = w₂ ∨ w₁ = -w₂ := by
    exact rulingCluster_dirs_parallel hf ha heS
      (q₁ := q₁ ∘ ψ₁) (q₂ := q₂ ∘ ψ₂)
      (hq₁S := fun n => hq₁S (ψ₁ n)) (hq₁U := fun n => hq₁U (ψ₁ n))
      (hq₂S := fun n => hq₂S (ψ₂ n)) (hq₂U := fun n => hq₂U (ψ₂ n))
      (hq₁e := hq₁e.comp hψ₁.tendsto_atTop) (hq₂e := hq₂e.comp hψ₂.tendsto_atTop)
      (hd₁ := hvw₁) (hd₂ := hvw₂)
  have hratio_eq : w₁ 1 / w₁ 0 = w₂ 1 / w₂ 0 := by
    rcases hpar with hpar | hpar
    · rw [hpar]
    · have hw : w₁ = -w₂ := hpar
      calc
        w₁ 1 / w₁ 0 = (-w₂) 1 / (-w₂) 0 := by rw [hw]
        _ = w₂ 1 / w₂ 0 := by
          simp
  calc
    m₁ = w₁ 1 / w₁ 0 := hm₁w
    _ = w₂ 1 / w₂ 0 := hratio_eq
    _ = m₂ := hm₂w.symm


/-- `degenerateSlope` is the slope limit of the below-sequence (defeq:
both are the brick (C) choice over the same sequence). -/
lemma degenerateSlope_eq_slopeLimit_belowSeq {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    slopeLimitOfSeq hf ha (uHeightBelowSeq_mem hf ha hy₀F hni hunc)
      (uHeightBelowSeq_tendsto hf ha hy₀F hni hunc) = degenerateSlope hf ha hy₀F hni hunc := by
  rfl

/-- **Two-sided slope agreement**: the slope limit of ANY U-height sequence
converging to `y₀` equals `degenerateSlope` (compare with the below
sequence; the cross-sequence limit lemma). -/
lemma slopeLimit_eq_degenerateSlope {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) {y : ℕ → ℝ}
    (hyU : ∀ n : ℕ, y n ∈ UHeight a f) (hyy₀ : Tendsto y atTop (𝓝 y₀)) :
    slopeLimitOfSeq hf ha hyU hyy₀ = degenerateSlope hf ha hy₀F hni hunc := by
  symm
  exact slope_limit_of_two_seq_eq hf ha
    (y₁ := uHeightBelowSeq hf ha hy₀F hni hunc)
    (hy₁U := uHeightBelowSeq_mem hf ha hy₀F hni hunc)
    (hy₁t := uHeightBelowSeq_tendsto hf ha hy₀F hni hunc)
    (y₂ := y) (hy₂U := hyU) (hy₂t := hyy₀)
    (m₁ := degenerateSlope hf ha hy₀F hni hunc)
    (m₂ := slopeLimitOfSeq hf ha hyU hyy₀)
    (degenerateSlope_tendsto hf ha hy₀F hni hunc)
    (slopeLimitOfSeq_tendsto hf ha hyU hyy₀)

/-- The slope limit of the above-sequence equals the degenerate slope. -/
lemma slopeLimit_aboveSeq_eq_degenerateSlope {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    slopeLimitOfSeq hf ha (uHeightAboveSeq_mem hf ha hy₀F hni hunc)
      (uHeightAboveSeq_tendsto hf ha hy₀F hni hunc) = degenerateSlope hf ha hy₀F hni hunc := by
  exact slopeLimit_eq_degenerateSlope hf ha hy₀F hni hunc
    (uHeightAboveSeq_mem hf ha hy₀F hni hunc) (uHeightAboveSeq_tendsto hf ha hy₀F hni hunc)

/-- **One-sided endpoint continuity (left, from below)**: the left endpoints
of the U-leaves at the below-heights converge to the degenerate leaf's left
endpoint. -/
lemma degenerateLeaf_A_endpoint_tendsto_below {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    Tendsto (fun n : ℕ => uBendA hf ha (centrePoint_mem_stripInterior (uHeightBelowSeq hf ha hy₀F hni hunc n))
        ((mem_UHeight (a := a) (f := f)).mp (uHeightBelowSeq_mem hf ha hy₀F hni hunc n))) atTop
      (𝓝 (degenerateLeaf hf ha hy₀F hni hunc).A) := by
  have hc := uBendA_tendsto_of_height hf ha (uHeightBelowSeq_mem hf ha hy₀F hni hunc)
    (uHeightBelowSeq_tendsto hf ha hy₀F hni hunc)
  -- target limit value: !₂[0, y₀ − degenerateSlope/2] = degenerateLeaf.A
  have hval : (!₂[(0 : ℝ), y₀ - degenerateSlope hf ha hy₀F hni hunc / 2] : ℝ²) =
      (degenerateLeaf hf ha hy₀F hni hunc).A := by
    rw [degenerateLeaf_A]
  simpa [degenerateSlope_eq_slopeLimit_belowSeq hf ha hy₀F hni hunc, hval] using hc

/-- **One-sided endpoint continuity (right, from below)**. -/
lemma degenerateLeaf_B_endpoint_tendsto_below {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    Tendsto (fun n : ℕ => uBendB hf ha (centrePoint_mem_stripInterior (uHeightBelowSeq hf ha hy₀F hni hunc n))
        ((mem_UHeight (a := a) (f := f)).mp (uHeightBelowSeq_mem hf ha hy₀F hni hunc n))) atTop
      (𝓝 (degenerateLeaf hf ha hy₀F hni hunc).B) := by
  have hc := uBendB_tendsto_of_height hf ha (uHeightBelowSeq_mem hf ha hy₀F hni hunc)
    (uHeightBelowSeq_tendsto hf ha hy₀F hni hunc)
  have hval : (!₂[(1 : ℝ), y₀ + degenerateSlope hf ha hy₀F hni hunc / 2] : ℝ²) =
      (degenerateLeaf hf ha hy₀F hni hunc).B := by
    rw [degenerateLeaf_B]
  simpa [degenerateSlope_eq_slopeLimit_belowSeq hf ha hy₀F hni hunc, hval] using hc

/-- **One-sided endpoint continuity (left, from above)**: the U-leaves at
the above-heights converge to the SAME degenerate leaf (two-sided slope
agreement). -/
lemma degenerateLeaf_A_endpoint_tendsto_above {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    Tendsto (fun n : ℕ => uBendA hf ha (centrePoint_mem_stripInterior (uHeightAboveSeq hf ha hy₀F hni hunc n))
        ((mem_UHeight (a := a) (f := f)).mp (uHeightAboveSeq_mem hf ha hy₀F hni hunc n))) atTop
      (𝓝 (degenerateLeaf hf ha hy₀F hni hunc).A) := by
  have hc := uBendA_tendsto_of_height hf ha (uHeightAboveSeq_mem hf ha hy₀F hni hunc)
    (uHeightAboveSeq_tendsto hf ha hy₀F hni hunc)
  have hval : (!₂[(0 : ℝ), y₀ - degenerateSlope hf ha hy₀F hni hunc / 2] : ℝ²) =
      (degenerateLeaf hf ha hy₀F hni hunc).A := by
    rw [degenerateLeaf_A]
  simpa [slopeLimit_aboveSeq_eq_degenerateSlope hf ha hy₀F hni hunc, hval] using hc

/-- **One-sided endpoint continuity (right, from above)**. -/
lemma degenerateLeaf_B_endpoint_tendsto_above {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    Tendsto (fun n : ℕ => uBendB hf ha (centrePoint_mem_stripInterior (uHeightAboveSeq hf ha hy₀F hni hunc n))
        ((mem_UHeight (a := a) (f := f)).mp (uHeightAboveSeq_mem hf ha hy₀F hni hunc n))) atTop
      (𝓝 (degenerateLeaf hf ha hy₀F hni hunc).B) := by
  have hc := uBendB_tendsto_of_height hf ha (uHeightAboveSeq_mem hf ha hy₀F hni hunc)
    (uHeightAboveSeq_tendsto hf ha hy₀F hni hunc)
  have hval : (!₂[(1 : ℝ), y₀ + degenerateSlope hf ha hy₀F hni hunc / 2] : ℝ²) =
      (degenerateLeaf hf ha hy₀F hni hunc).B := by
    rw [degenerateLeaf_B]
  simpa [slopeLimit_aboveSeq_eq_degenerateSlope hf ha hy₀F hni hunc, hval] using hc



/-- **Deck flip of the slope at a U-height**: the canonical U-leaf through
`(1/2, y+a)` has slope `−Δ` (the deck map `period` swaps the endpoints and
shifts by `a`). -/
lemma slopeAtHeight_flip {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {z : ℝ} (hz : z ∈ UHeight a f) :
    slopeAtHeight hf ha (y := z + a) ((mem_UHeight_add_period hf z).2 hz) =
      - slopeAtHeight hf ha hz := by
  let u : UHeight a f := ⟨z, hz⟩
  have hflip : slopeAtHeight hf ha (y := u.1 + a) (uHeightShift hf u).2 =
      - slopeAtHeight hf ha u.2 := by
    have hA1 : (uHeightA hf ha (uHeightShift hf u)) 1 = (period a (uHeightB hf ha u)) 1 := by
      rw [uHeightA_period hf ha u]
    have hB1 : (uHeightB hf ha (uHeightShift hf u)) 1 = (period a (uHeightA hf ha u)) 1 := by
      rw [uHeightB_period hf ha u]
    have hshift : slopeAtHeight hf ha (y := u.1 + a) (uHeightShift hf u).2 =
        (uHeightB hf ha (uHeightShift hf u)) 1 - (uHeightA hf ha (uHeightShift hf u)) 1 := by
      dsimp [slopeAtHeight]
      rw [uBendSlope_eq_disp hf ha (centrePoint_mem_stripInterior (u.1 + a))
        (uHeightShift hf u).2]
      rfl
    have horig : slopeAtHeight hf ha u.2 =
        (uHeightB hf ha u) 1 - (uHeightA hf ha u) 1 := by
      dsimp [slopeAtHeight]
      rw [uBendSlope_eq_disp hf ha (centrePoint_mem_stripInterior u.1) u.2]
      rfl
    rw [hshift, hA1, hB1, horig]
    simp [period]
  dsimp [u] at hflip ⊢
  exact hflip
lemma not_IsFlatInterior_period {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hxS : x ∈ stripInterior) (hni : ¬ IsFlatInterior f x) :
    ¬ IsFlatInterior f (period a x) := by
  intro hper
  have hperS : period a x ∈ stripInterior := by
    rw [stripInterior]
    change (period a x) 0 ∈ Set.Ioo (0 : ℝ) 1
    rw [Set.mem_Ioo]
    constructor
    · have hx1 : x 0 < 1 := by rw [stripInterior] at hxS; exact hxS.2
      simp [period]; linarith
    · have hx0 : 0 < x 0 := by rw [stripInterior] at hxS; exact hxS.1
      simp [period]; linarith
  have hperInt : period a x ∈ interior (FlatSet f) :=
    (IsFlatInterior_iff_mem_interior_FlatSet hperS).1 hper
  have hpinv := mem_interior_FlatSet_periodInv hf (p := period a x) hperInt
  have hxInt : x ∈ interior (FlatSet f) := by
    simpa [periodInv_period] using hpinv
  exact hni ((IsFlatInterior_iff_mem_interior_FlatSet hxS).2 hxInt)

lemma CoveredHeight_period_iff {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (y : ℝ) : CoveredHeight (f := f) (y + a) ↔ CoveredHeight (f := f) y := by
  constructor
  · intro h
    rcases h with ⟨p, hp, hpa⟩
    refine ⟨periodInv a p, mem_interior_FlatSet_periodInv hf hp, ?_⟩
    have hpp : period a (periodInv a p) = p := period_periodInv a p
    have hdeck := frHeights_deck_mem hf (mem_interior_FlatSet_periodInv hf hp) (h := y)
    have hpa' : y + a ∈ frHeights f (period a (periodInv a p)) := by
      rwa [hpp]
    exact hdeck.mp hpa'
  · intro h
    rcases h with ⟨p, hp, hy⟩
    refine ⟨period a p, mem_interior_FlatSet_period hf hp, ?_⟩
    exact (frHeights_deck_mem hf hp (h := y)).mpr hy


lemma flatHeight_add {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) : y₀ + a ∈ FlatHeight a f := by
  exact (mem_FlatHeight_add_period hf y₀).2 hy₀F

lemma not_flatInterior_add {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {y₀ : ℝ} (hni : ¬ IsFlatInterior f (centrePoint y₀)) :
    ¬ IsFlatInterior f (centrePoint (y₀ + a)) := by
  rw [centrePoint_period a y₀]
  exact not_IsFlatInterior_period hf (centrePoint_mem_stripInterior y₀) hni

lemma not_covered_add {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {y₀ : ℝ} (hunc : ¬ CoveredHeight (f := f) y₀) :
    ¬ CoveredHeight (f := f) (y₀ + a) := by
  intro h
  exact hunc ((CoveredHeight_period_iff hf y₀).mp h)

/-- **Deck flip of the degenerate slope**: the degenerate slope at the
deck partner height `y₀+a` is `−degenerateSlope y₀`.  Proof: shift the
below-sequence by `a` — it is a U-height sequence converging to `y₀+a`
(`mem_UHeight_add_period`, `Tendsto.add`); its slope limit is
`degenerateSlope (y₀+a)` (`slopeLimit_eq_degenerateSlope`) and, pointwise
by `slopeAtHeight_flip`, also `−degenerateSlope y₀`. -/
theorem degenerateSlope_deck {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    degenerateSlope hf ha (flatHeight_add hf hy₀F) (not_flatInterior_add hf hni) (not_covered_add hf hunc)
      = - degenerateSlope hf ha hy₀F hni hunc := by
  -- shifted below sequence
  let y : ℕ → ℝ := fun n => uHeightBelowSeq hf ha hy₀F hni hunc n + a
  have hyU : ∀ n : ℕ, y n ∈ UHeight a f := by
    intro n
    dsimp [y]
    exact (mem_UHeight_add_period hf (uHeightBelowSeq hf ha hy₀F hni hunc n)).2
      (uHeightBelowSeq_mem hf ha hy₀F hni hunc n)
  have hyy₀ : Tendsto y atTop (𝓝 (y₀ + a)) := by
    dsimp [y]
    simpa using ((uHeightBelowSeq_tendsto hf ha hy₀F hni hunc).add
      (tendsto_const_nhds (x := a)))
  -- slope limit of the shifted sequence equals degenerateSlope at y₀+a
  have hmain := slopeLimit_eq_degenerateSlope hf ha (flatHeight_add hf hy₀F)
    (not_flatInterior_add hf hni) (not_covered_add hf hunc) hyU hyy₀
  -- ... and equals the negated slope limit of the original below sequence
  have hneg : Tendsto (fun n : ℕ => - slopeAtHeight hf ha (uHeightBelowSeq_mem hf ha hy₀F hni hunc n))
      atTop (𝓝 (- degenerateSlope hf ha hy₀F hni hunc)) := by
    exact (degenerateSlope_tendsto hf ha hy₀F hni hunc).neg
  have hpt : (fun n : ℕ => slopeAtHeight hf ha (hyU n)) =ᶠ[atTop]
      fun n : ℕ => - slopeAtHeight hf ha (uHeightBelowSeq_mem hf ha hy₀F hni hunc n) := by
    filter_upwards with n
    dsimp [y]
    exact slopeAtHeight_flip hf ha (uHeightBelowSeq_mem hf ha hy₀F hni hunc n)
  have hshiftlim : slopeLimitOfSeq hf ha hyU hyy₀ = - degenerateSlope hf ha hy₀F hni hunc := by
    have hc := slopeLimitOfSeq_tendsto hf ha hyU hyy₀
    exact tendsto_nhds_unique (hc.congr' hpt) hneg
  rw [← hmain, hshiftlim]


/-- **Deck flip of the degenerate leaf (left)**: the leaf at `y₀+a`
starts at the period image of the right endpoint of the leaf at `y₀`
(`BandFoliation.deck` field, first conjunct). -/
lemma degenerateLeaf_deck_A {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    (degenerateLeaf hf ha (flatHeight_add hf hy₀F) (not_flatInterior_add hf hni)
        (not_covered_add hf hunc)).A = period a (degenerateLeaf hf ha hy₀F hni hunc).B := by
  have hdeck := degenerateSlope_deck hf ha hy₀F hni hunc
  rw [degenerateLeaf_A, degenerateLeaf_B]
  ext i <;> fin_cases i
  · simp [period]
  · simp [period, hdeck]
    ring

/-- **Deck flip of the degenerate leaf (right)**: the leaf at `y₀+a`
ends at the period image of the left endpoint of the leaf at `y₀`
(`BandFoliation.deck` field, second conjunct). -/
lemma degenerateLeaf_deck_B {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} (hy₀F : y₀ ∈ FlatHeight a f) (hni : ¬ IsFlatInterior f (centrePoint y₀))
    (hunc : ¬ CoveredHeight (f := f) y₀) :
    (degenerateLeaf hf ha (flatHeight_add hf hy₀F) (not_flatInterior_add hf hni)
        (not_covered_add hf hunc)).B = period a (degenerateLeaf hf ha hy₀F hni hunc).A := by
  have hdeck := degenerateSlope_deck hf ha hy₀F hni hunc
  rw [degenerateLeaf_A, degenerateLeaf_B]
  ext i <;> fin_cases i
  · simp [period]
  · simp [period, hdeck]
    ring

end Submission

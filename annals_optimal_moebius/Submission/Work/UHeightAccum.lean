import Submission.Work.DegenerateLeaf
import Submission.Work.FlatComponents
import Submission.Work.FlatHeightFacts

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Brick (B) of the degenerate-flat-height route: U-height accumulation

GREEN so far — the first lemmas of brick (B) (session_status105): at a
degenerate flat centreline point `(1/2, y)` (flat, NOT flat-interior),
U-heights occur arbitrarily close to `y`, and under a no-U-height band
hypothesis the centre points of the band are all flat-INTERIOR.

* `ball_centrePoint_subset_stripInterior` — the ball of radius
  `r < 1/2` around a centreline point lies in `stripInterior`;
* **`exists_uHeight_near_degenerate_flat`** — for `y ∈ FlatHeight a f`
  with `¬ IsFlatInterior f (centrePoint y)`:
  `∀ ρ > 0, ∃ u ∈ UHeight a f, |u − y| < ρ`.  Proof: `U_dense_near_degenerate_frontier`
  gives U-points arbitrarily close to `(1/2,y)`; the stage-1 U-point (at
  radius `1/4`) proves the displacement coefficient `(a²−1)/(2a)` is
  nonnegative (`DegenerateLeaf.uBendDispCoeff_nonneg`), so the radius
  `δ := min (1/4) (ρ/(2(C+1)))` is well-chosen; the stage-2 U-point's
  leaf crosses the centreline at a U-height within `(C+1)·δ ≤ ρ/2` of
  `y` (`DegenerateLeaf.crossHeight_close`).
* **`flatInterior_of_no_uHeight_band`** — if NO U-height occurs in the
  band `(y₀−ε, y₀)` (`hnoU`), then every centre point `(1/2,y)`,
  `y ∈ (y₀−ε/2, y₀)`, is flat-INTERIOR: a flat non-interior one would
  carry a U-height into the band by the near-lemma (choose `ρ` smaller
  than both margins `y − (y₀−ε)` and `(y₀−y)/2`), contradicting `hnoU`.

Remaining for brick (B) (see session_status105 for the full design): the
component-dichotomy — under `hnoU`, `flatInterior_of_no_uHeight_band` says
the whole inner band is covered by flat-interior points, and the component
interval structure (`flatComponent_between_with_data`,
`flatComponent_centreline`, `FlatNeighbour`) then forces `y₀` to be in the
CLOSED centre interval of some flat component ("covered"): so an UNCOVERED
degenerate flat height must have U-heights accumulating below it, and
symmetrically above.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- The ball of radius `r < 1/2` around a centreline point stays in the
strip interior (coordinate `0` stays strictly between 0 and 1). -/
lemma ball_centrePoint_subset_stripInterior (y : ℝ) {r : ℝ} (hr : r < 1 / 2) :
    Metric.ball (centrePoint y) r ⊆ stripInterior := by
  intro z hz
  have hz0 : |z 0 - (centrePoint y) 0| ≤ ‖z - centrePoint y‖ :=
    abs_coord0_le_norm (z - centrePoint y)
  have hz0' : ‖z - centrePoint y‖ < r := by
    simpa [dist_eq_norm] using (Metric.mem_ball.mp hz)
  have hz0'' : ‖z - centrePoint y‖ < 1 / 2 := lt_trans hz0' hr
  have hzc : |z 0 - 1 / 2| < 1 / 2 := by
    have hcp0 : (centrePoint y) 0 = 1 / 2 := by simp [centrePoint]
    rw [hcp0] at hz0
    exact lt_of_le_of_lt hz0 hz0''
  have hzabs := abs_lt.mp hzc
  rw [stripInterior]
  change z 0 ∈ Set.Ioo (0 : ℝ) 1
  rw [Set.mem_Ioo]
  constructor <;> nlinarith

/-- **Brick (B), near-lemma**: at a flat NON-interior centreline point
`(1/2, y)` (a "degenerate flat height"), U-heights occur arbitrarily
close to `y`.  Proof: U-points are dense around `(1/2,y)`
(`U_dense_near_degenerate_frontier`); by brick (A)
(`DegenerateLeaf.crossHeight_close`) the U-leaf through such a point
crosses the centreline at a U-height within `(C+1)·r` of `y`. -/
theorem exists_uHeight_near_degenerate_flat {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hyF : y ∈ FlatHeight a f)
    (hni : ¬ IsFlatInterior f (centrePoint y)) :
    ∀ ρ > 0, ∃ u : ℝ, u ∈ UHeight a f ∧ |u - y| < ρ := by
  intro ρ hρ
  have heS : centrePoint y ∈ stripInterior := centrePoint_mem_stripInterior y
  have heF : centrePoint y ∈ FlatSet f := by
    exact (mem_FlatHeight_iff_FlatSet (a := a) (f := f)).mp hyF
  -- stage 1: a U point at radius 1/4 (to get the displacement coefficient nonnegative)
  rcases (U_dense_near_degenerate_frontier (a := a) heS heF hni (1 / 4) (by norm_num)) with
    ⟨x₁, hx₁b, hx₁U⟩
  have hx₁S : x₁ ∈ stripInterior :=
    ball_centrePoint_subset_stripInterior y (by norm_num : (1 / 4 : ℝ) < 1 / 2) hx₁b
  have hC0 : 0 ≤ (a ^ 2 - 1) / (2 * a) := uBendDispCoeff_nonneg hf ha hx₁S hx₁U
  -- radius δ
  let C : ℝ := (a ^ 2 - 1) / (2 * a)
  have hC0' : 0 ≤ C := by dsimp [C]; exact hC0
  let δ : ℝ := min (1 / 4) (ρ / (2 * (C + 1)))
  have hδ : 0 < δ := by
    dsimp [δ]
    apply lt_min
    · norm_num
    · have hpos : 0 < 2 * (C + 1) := by nlinarith [hC0']
      positivity
  rcases (U_dense_near_degenerate_frontier (a := a) heS heF hni δ hδ) with ⟨x, hxb, hxU⟩
  have hδlt : δ < 1 / 2 := by
    have hδle4 : δ ≤ 1 / 4 := by dsimp [δ]; exact min_le_left _ _
    linarith
  have hxS : x ∈ stripInterior := ball_centrePoint_subset_stripInterior y hδlt hxb
  have hr : 0 ≤ δ := le_of_lt hδ
  have hxr : ‖x - centrePoint y‖ ≤ δ := by
    have hd : dist x (centrePoint y) < δ := Metric.mem_ball.mp hxb
    simpa [dist_eq_norm] using le_of_lt hd
  have hb := crossHeight_close hf ha hxS hxU hr hxr
  let u : ℝ := (uBendCrossPt hf ha hxS hxU) 1
  have huU : u ∈ UHeight a f := by
    dsimp [u]
    exact uBendCrossPt_height_mem_UHeight hf ha hxS hxU
  have hb' : |u - y| ≤ (C + 1) * δ := by
    dsimp [C, u] at hb ⊢
    exact hb
  have hcoeff : 0 < C + 1 := by nlinarith [hC0']
  have hδle : δ ≤ ρ / (2 * (C + 1)) := by
    dsimp [δ]
    exact min_le_right _ _
  have hmul : (C + 1) * δ ≤ ρ / 2 := by
    have hm := mul_le_mul_of_nonneg_left hδle (le_of_lt hcoeff)
    have hred : (C + 1) * (ρ / (2 * (C + 1))) = ρ / 2 := by
      field_simp [show C + 1 ≠ 0 by linarith]
    rw [hred] at hm
    exact hm
  have hlt : |u - y| < ρ := by
    have hle := le_trans hb' hmul
    have hhalf : ρ / 2 < ρ := by linarith
    linarith
  exact ⟨u, huU, hlt⟩

/-- **Brick (B), first lemma of the both-sides accumulation proof**: if no
U-height occurs in the open band `(y₀−ε, y₀)` below the flat height `y₀`,
then every centre point `(1/2, y)` with `y` in the inner band
`(y₀−ε/2, y₀)` is flat-INTERIOR — a flat NON-interior centre point there
would produce (near-lemma) a U-height inside the band, contradicting
`hnoU`. -/
theorem flatInterior_of_no_uHeight_band {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ ε : ℝ} (hε : 0 < ε)
    (hnoU : ∀ u : ℝ, u ∈ Set.Ioo (y₀ - ε) y₀ → u ∉ UHeight a f) :
    ∀ y : ℝ, y ∈ Set.Ioo (y₀ - ε / 2) y₀ → IsFlatInterior f (centrePoint y) := by
  intro y hy
  have hyU : y ∉ UHeight a f := by
    apply hnoU
    rw [Set.mem_Ioo] at hy ⊢
    constructor <;> nlinarith [hy.1, hy.2, hε]
  have hyF : y ∈ FlatHeight a f := by
    by_contra h
    exact hyU ((mem_UHeight_iff_not_FlatHeight (a := a) (f := f)).mpr h)
  by_contra hni
  let ρ : ℝ := min (y - (y₀ - ε)) ((y₀ - y) / 2)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    apply lt_min
    · nlinarith [hε, hy.1]
    · nlinarith [hy.2]
  rcases exists_uHeight_near_degenerate_flat hf ha hyF hni ρ hρ with ⟨u, huU, huρ⟩
  have huI : u ∈ Set.Ioo (y₀ - ε) y₀ := by
    rw [Set.mem_Ioo]
    have huρ' := abs_lt.mp huρ
    constructor
    · have h1 : ρ ≤ y - (y₀ - ε) := by dsimp [ρ]; exact min_le_left _ _
      nlinarith
    · have h2 : ρ ≤ (y₀ - y) / 2 := by dsimp [ρ]; exact min_le_right _ _
      nlinarith
  exact (hnoU u huI) huU

end Submission

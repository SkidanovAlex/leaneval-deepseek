import Submission.Work.Main0U
import Submission.Work.FlatFrontier
import Submission.Work.FlatBetween
import Submission.Work.GeneralChord
import Submission.Work.FlatNeighbour
import Submission.Work.FlatComponents
import Submission.Work.UMatchEngine

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# U-matching direction limit — crossing-impossibility core (step 2)

The U-leaf through a U-point `x` is the straight line in the kernel
direction `w := uBendDirPos x`, and its open part inside the strip is
`uBendSet` (all U-points).  A frontier chord `stripChord α β` of a flat
component consists of flat points.  Two straight full chords that cross
INSIDE the open strip would contain a common point that is both U and
flat — impossible.  Hence, if a U-leaf line (centre height
`x 1 ≠ sideH₁ α β (1/2)`) is NOT parallel to the frontier chord, their
unique crossing has `x0`-coordinate OUTSIDE `(0,1)`:

* `uBendSlope` — the slope of the U-leaf line, `w1/w0` (non-vertical
  since `0 < w 0`);
* `sideH₁_affine_centre` — `sideH₁ α β u = sideH₁ α β (1/2) +
  (β−α)(u − 1/2)`;
* `line_cross_height` — at the crossing coordinate
  `ξ = 1/2 + (c − y)/(m − M)` the leaf-line height equals the chord
  height (pure real algebra);
* **`uBend_chord_no_cross`** / **`uBend_crossing_outside`** — with a
  flat chord and a U-leaf whose slope differs from the chord's, the
  crossing coordinate of the two lines is not in `(0,1)`;
* **`frontier_chord_flat`** — the points of the canonical upper chord of
  a between-represented flat component are flat (`dN = 0`): the chord
  lies in the frontier (Brick (A)) and
  `flatComponent_frontier_subset_FlatSet` applies;
* **`uBend_slope_limit`** — the ε slope-limit: U-centre heights
  approaching the centre height of a flat chord force the leaf slopes to
  converge to the chord slope `β − α` (if `|mₙ − M| ≥ ε` while
  `|c − yₙ| < ε/4`, the crossing coordinate lies in `(0,1)`, contradicting
  `uBend_crossing_outside`);
* `uBendDirPos_unit_first`, `uBendA_eq_leftPoint_slope`,
  `uBendB_eq_rightPoint_slope` — the leaf endpoint equals the
  left/right-intersection with the unit-first-coordinate direction
  `(1, uBendSlope)`;
* **`uBend_left_endpoint_limit`** / **`uBend_right_endpoint_limit`** —
  U-matching: U-centre heights approaching the centre height of a flat
  chord give U-leaf endpoints converging to the chord seam endpoints
  `(0, α)` and `(1, β)` (slope-limit + `tendsto_left/rightPointOfDir` +
  `left/rightPointOfDir_chord_left/right`).

Build: `lake build Submission.Work.UMatchDirection` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- The slope of the canonical U-leaf line through a U-point: the second
coordinate ratio of the (non-vertical) kernel direction. -/
noncomputable def uBendSlope {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) : ℝ :=
  (uBendDirPos hf ha hx hdN) 1 / (uBendDirPos hf ha hx hdN) 0

/-- The kernel direction of a U-leaf is non-vertical with a positive
first coordinate. -/
lemma uBendDirPos_coord_pos {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    0 < (uBendDirPos hf ha hx hdN) 0 := by
  exact (uBendDirPos_spec hf ha hx hdN).2.2

/-- The kernel direction of a U-leaf is non-vertical. -/
lemma uBendDirPos_coord_ne_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    (uBendDirPos hf ha hx hdN) 0 ≠ 0 := by
  exact ne_of_gt (uBendDirPos_coord_pos hf ha hx hdN)

/-- The affine side height through its centre value. -/
lemma sideH₁_affine_centre (α β u : ℝ) :
    sideH₁ α β u = sideH₁ α β (1 / 2) + (β - α) * (u - 1 / 2) := by
  dsimp [sideH₁]
  ring

/-- At the crossing coordinate `ξ` the leaf-line height equals the chord
height: with `M = β − α` and `ξ = 1/2 + (c−y)/(m−M)`, `y + m(ξ−1/2) =
sideH₁ α β ξ`. -/
lemma line_cross_height {α β y m M : ℝ} (hM : M = β - α)
    (hden : m - M ≠ 0) {ξ : ℝ}
    (hξ : ξ = 1 / 2 + (sideH₁ α β (1 / 2) - y) / (m - M)) :
    y + m * (ξ - 1 / 2) = sideH₁ α β ξ := by
  have hd : ξ - 1 / 2 = (sideH₁ α β (1 / 2) - y) / (m - M) := by
    rw [hξ]
    ring_nf
  let q : ℝ := (sideH₁ α β (1 / 2) - y) / (m - M)
  have hq : (m - M) * q = sideH₁ α β (1 / 2) - y := by
    dsimp [q]
    field_simp [hden]
  have hq' : m * q = (sideH₁ α β (1 / 2) - y) + M * q := by
    have hs : m * q - M * q = sideH₁ α β (1 / 2) - y := by
      simpa [sub_mul] using hq
    linarith
  calc
    y + m * (ξ - 1 / 2) = y + m * q := by rw [hd]
    _ = y + ((sideH₁ α β (1 / 2) - y) + M * q) := by rw [hq']
    _ = sideH₁ α β (1 / 2) + M * q := by ring
    _ = sideH₁ α β (1 / 2) + M * (ξ - 1 / 2) := by dsimp [q]; rw [← hd]
    _ = sideH₁ α β ξ := by
      have hmid : sideH₁ α β ξ = sideH₁ α β (1 / 2) + M * (ξ - 1 / 2) := by
        rw [hM]
        exact sideH₁_affine_centre α β ξ
      exact hmid.symm



/-- **A U-leaf line cannot cross a flat full chord inside the open
strip**: with `x` a U-point on the centreline (`x 0 = 1/2`), a flat chord
`stripChord α β` whose centre height differs from `x 1`, and leaf slope
`uBendSlope ≠ β−α`, the crossing coordinate of the two lines is not in
`(0,1)`. -/
theorem uBend_chord_no_cross {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hxS : x ∈ stripInterior) (hdN : dN f x ≠ 0)
    (hx0 : x 0 = 1 / 2) {α β : ℝ}
    (hchordFlat : ∀ z : ℝ², z ∈ stripChord α β → dN f z = 0)
    {ξ : ℝ}
    (hξeq : ξ = 1 / 2 + (sideH₁ α β (1 / 2) - x 1) /
        (uBendSlope hf ha hxS hdN - (β - α)))
    (hslope : uBendSlope hf ha hxS hdN ≠ β - α)
    (hξmem : ξ ∈ Set.Ioo 0 1) :
    False := by
  let w : ℝ² := uBendDirPos hf ha hxS hdN
  have hwpos : 0 < w 0 := by
    rcases uBendDirPos_spec hf ha hxS hdN with ⟨_, _, hwpos⟩
    dsimp [w]
    exact hwpos
  have hw0 : w 0 ≠ 0 := ne_of_gt hwpos
  let m : ℝ := w 1 / w 0
  have hm : m = uBendSlope hf ha hxS hdN := by
    dsimp [m, w, uBendSlope]
  have hden : m - (β - α) ≠ 0 := by
    rw [hm]
    exact sub_ne_zero.mpr hslope
  have hξm : ξ = 1 / 2 + (sideH₁ α β (1 / 2) - x 1) / (m - (β - α)) := by
    rwa [← hm] at hξeq
  let r : ℝ² := !₂[ξ, sideH₁ α β ξ]
  -- r is on the flat chord, hence flat:
  have hrS : r ∈ stripInterior := by
    rw [stripInterior]
    dsimp [r]
    exact (Set.mem_Ioo.mp hξmem)
  have hrchord : r ∈ stripChord α β := by
    rw [mem_stripChord]
    constructor
    · exact hrS
    · dsimp [r]
  have hdNr : dN f r = 0 := hchordFlat r hrchord
  -- r is on the open U-leaf through x, hence a U-point:
  have hlh : x 1 + m * (ξ - 1 / 2) = sideH₁ α β ξ :=
    line_cross_height (hM := rfl) (y := x 1) (m := m) hden hξm
  have hrcoll : ∃ s : ℝ, r = x + s • w := by
    let s : ℝ := (ξ - 1 / 2) / (w 0)
    have hr0 : r 0 = ξ := by dsimp [r]
    have hr1 : r 1 = sideH₁ α β ξ := by dsimp [r]
    have hsum0 : (x + s • w) 0 = x 0 + s * (w 0) := by simp [smul_eq_mul]
    have hsum1 : (x + s • w) 1 = x 1 + s * (w 1) := by simp [smul_eq_mul]
    have hs1 : s * (w 1) = m * (ξ - 1 / 2) := by
      dsimp [s, m]
      field_simp [hw0]
    refine ⟨s, ?_⟩
    ext i <;> fin_cases i
    · simp [hr0, hsum0]
      dsimp [s]
      field_simp [hw0]
      rw [hx0]
      ring
    · simp [hr1, hsum1, hs1]
      simpa using hlh.symm
  have hruB : r ∈ uBendSet hf ha hxS hdN := by
    rw [mem_uBendSet_iff_on_line_interior hf ha hxS hdN]
    constructor
    · exact hrS
    · simpa [w] using hrcoll
  have hdNr' : dN f r ≠ 0 := (uBendSet_subset_U_and_kernel hf ha hxS hdN).1 r hruB
  exact hdNr' hdNr


/-- **Corollary (negation form)**: with a flat chord and non-parallel
leaf, the crossing coordinate of the U-leaf line and the chord line is
NOT in `(0,1)`. -/
theorem uBend_crossing_outside {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hxS : x ∈ stripInterior) (hdN : dN f x ≠ 0)
    (hx0 : x 0 = 1 / 2) {α β : ℝ}
    (hchordFlat : ∀ z : ℝ², z ∈ stripChord α β → dN f z = 0)
    (hslope : uBendSlope hf ha hxS hdN ≠ β - α) :
    ¬ (1 / 2 + (sideH₁ α β (1 / 2) - x 1) /
          (uBendSlope hf ha hxS hdN - (β - α)) ∈ Set.Ioo 0 1) := by
  intro hm
  exact uBend_chord_no_cross hf ha hxS hdN hx0 hchordFlat (hξeq := rfl) hslope hm


/-- **Frontier chords of a flat component are flat**: the points of the
canonical upper chord `stripChord (data h₂)` (which bounds the component
on its upper side) satisfy `dN = 0`.  Proof: Brick (A) puts the chord in
the frontier of the between-represented component, and
`flatComponent_frontier_subset_FlatSet` makes frontier strip points
flat. -/
theorem frontier_chord_flat {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {h₁ h₂ : ℝ}
    (hh₁ : h₁ ∈ frHeights f p) (hh₂ : h₂ ∈ frHeights f p) (hlt : h₁ < h₂)
    (hC : flatComponent f p = betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2) :
    ∀ z : ℝ², z ∈ stripChord (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 →
      dN f z = 0 := by
  intro z hz
  have hzS : z ∈ stripInterior := stripChord_subset_stripInterior
    (α := (frCompData hf ha p hp h₂ hh₂).1) (β := (frCompData hf ha p hp h₂ hh₂).2) hz

  have hord : ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
      sideH₁ (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 u <
      sideH₁ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 u :=
    sideH₁_lt_of_heights hf ha p hp hh₁ hh₂ hlt
  have hEq := frontier_betweenChord (α₁ := (frCompData hf ha p hp h₁ hh₁).1)
    (β₁ := (frCompData hf ha p hp h₁ hh₁).2)
    (α₂ := (frCompData hf ha p hp h₂ hh₂).1)
    (β₂ := (frCompData hf ha p hp h₂ hh₂).2) hord
  have hin : z ∈ frontier (betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2) ∩ stripInterior := by
    rw [hEq]
    right
    exact hz
  have hzB : z ∈ frontier (betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2) := hin.1
  have hzfront : z ∈ frontier (flatComponent f p) := by
    rw [hC]
    exact hzB
  have hzF := flatComponent_frontier_subset_FlatSet hf hzS hzfront
  exact (mem_FlatSet.mp hzF).2


/-- **The slope limit**: if U-centre heights approach the centre height
of a flat chord, the leaf slopes converge to the chord slope `β − α`.
Proof (ε-argument): with `mₙ` the leaf slope and `M := β−α`, if
`|mₙ − M| ≥ ε` while `|c − yₙ| < ε/4`, the crossing coordinate
`ξ = 1/2 + (c−yₙ)/(mₙ−M)` satisfies `|ξ−1/2| < 1/4`, hence lies in
`(0,1)` — contradicting `uBend_crossing_outside`. -/
theorem uBend_slope_limit {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {α β : ℝ}
    (hchordFlat : ∀ z : ℝ², z ∈ stripChord α β → dN f z = 0)
    {y : ℕ → ℝ} (hyU : ∀ n : ℕ, dN f (centrePoint (y n)) ≠ 0)
    (hylim : Tendsto y atTop (𝓝 (sideH₁ α β (1 / 2)))) :
    Tendsto (fun n : ℕ => uBendSlope hf ha (centrePoint_mem_stripInterior (y n)) (hyU n))
      atTop (𝓝 (β - α)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let c : ℝ := sideH₁ α β (1 / 2)
  have hlimε : ∀ ε' > 0, ∃ N : ℕ, ∀ n ≥ N, dist (y n) c < ε' := by
    intro ε' hε'
    simpa [c] using ((Metric.tendsto_atTop.mp hylim) ε' hε')
  rcases hlimε (ε / 4) (by linarith) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  let x : ℝ² := centrePoint (y n)
  have hxS : x ∈ stripInterior := centrePoint_mem_stripInterior (y n)
  have hdNn : dN f x ≠ 0 := hyU n
  have hx0 : x 0 = 1 / 2 := by dsimp [x]; rfl
  let m : ℝ := uBendSlope hf ha hxS hdNn
  let M : ℝ := β - α
  change |m - M| < ε
  by_contra hnot
  have hge' : ε ≤ |m - M| := le_of_not_gt hnot
  have hmd0 : m - M ≠ 0 := by
    intro hz
    have hzero : |m - M| = 0 := by rw [hz]; simp
    linarith
  have hdy : |c - y n| < (1 / 4 : ℝ) * ε := by
    have hd := hN n hn
    have hd' : |y n - c| < ε / 4 := by simpa [Real.dist_eq] using hd
    have hc : |c - y n| < ε / 4 := by rwa [abs_sub_comm] at hd'
    convert hc using 1
    ring
  let ξ : ℝ := 1 / 2 + (c - y n) / (m - M)
  have habsξ : |ξ - 1 / 2| = |c - y n| / |m - M| := by
    dsimp [ξ]
    have hz : |(1 / 2 + (c - y n) / (m - M)) - 1 / 2| = |(c - y n) / (m - M)| := by
      congr 1
      ring
    rw [hz]
    exact abs_div (c - y n) (m - M)
  have hle : |c - y n| / |m - M| ≤ |c - y n| / ε := by
    have hmp : 0 < |m - M| := lt_of_lt_of_le hε hge'
    have hinv : |m - M|⁻¹ ≤ ε⁻¹ := (inv_le_inv₀ hmp hε).mpr hge'
    calc
      |c - y n| / |m - M| = |c - y n| * |m - M|⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ |c - y n| * ε⁻¹ := mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
      _ = |c - y n| / ε := by rw [div_eq_mul_inv]
  have hlt : |c - y n| / ε < 1 / 4 := by
    rw [div_lt_iff₀ hε]
    exact hdy
  have hb1 : |ξ - 1 / 2| < 1 / 4 := by
    rw [habsξ]
    exact lt_of_le_of_lt hle hlt
  have hmem : ξ ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [Set.mem_Ioo]
    have hzlt : -(1 / 4) < ξ - 1 / 2 ∧ ξ - 1 / 2 < 1 / 4 := abs_lt.mp hb1
    rcases hzlt with ⟨hl, hr⟩
    constructor <;> linarith
  have hneSlope : uBendSlope hf ha hxS hdNn ≠ β - α := by
    intro hz
    apply hmd0
    dsimp [M]
    exact sub_eq_zero.mpr hz
  have hneg := uBend_crossing_outside hf ha hxS hdNn hx0 hchordFlat hneSlope
  have hform : (1 / 2 + (sideH₁ α β (1 / 2) - x 1) /
      (uBendSlope hf ha hxS hdNn - (β - α))) = ξ := by
    dsimp [ξ, m, M, c, x]
    rfl
  have hF : (1 / 2 + (sideH₁ α β (1 / 2) - x 1) /
      (uBendSlope hf ha hxS hdNn - (β - α))) ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [hform]
    exact hmem
  exact hneg hF


/-- The canonical leaf direction `uBendDirPos` renormalised to unit first
coordinate is the direction vector `(1, uBendSlope)`. -/
lemma uBendDirPos_unit_first {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hxS : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    ((uBendDirPos hf ha hxS hdN) 0)⁻¹ • uBendDirPos hf ha hxS hdN =
      !₂[(1 : ℝ), uBendSlope hf ha hxS hdN] := by
  have hw0 : (uBendDirPos hf ha hxS hdN) 0 ≠ 0 := uBendDirPos_coord_ne_zero hf ha hxS hdN
  ext i <;> fin_cases i
  · dsimp [uBendSlope]
    field_simp [hw0]
  · dsimp [uBendSlope]
    field_simp [hw0]

/-- **The left endpoint of the canonical U-leaf equals the
left-intersection of its line with the unit-first-coordinate direction**
`(1, uBendSlope)`. -/
lemma uBendA_eq_leftPoint_slope {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hxS : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendA hf ha hxS hdN =
      leftPointOfDir x (!₂[(1 : ℝ), uBendSlope hf ha hxS hdN]) := by
  have hw0 : (uBendDirPos hf ha hxS hdN) 0 ≠ 0 := uBendDirPos_coord_ne_zero hf ha hxS hdN
  have hc : ((uBendDirPos hf ha hxS hdN) 0)⁻¹ ≠ 0 := inv_ne_zero hw0
  have hsm := leftPointOfDir_smul (x := x) (d := uBendDirPos hf ha hxS hdN) (c := ((uBendDirPos hf ha hxS hdN) 0)⁻¹) hc hw0
  calc
    uBendA hf ha hxS hdN = leftPointOfDir x (uBendDirPos hf ha hxS hdN) := by
      exact uBendA_eq_leftPointOfDir hf ha hxS hdN
    _ = leftPointOfDir x (((uBendDirPos hf ha hxS hdN) 0)⁻¹ • uBendDirPos hf ha hxS hdN) := hsm.symm
    _ = leftPointOfDir x (!₂[(1 : ℝ), uBendSlope hf ha hxS hdN]) := by
      rw [uBendDirPos_unit_first hf ha hxS hdN]

/-- **The right endpoint of the canonical U-leaf equals the
right-intersection of its line with the unit-first-coordinate direction**
`(1, uBendSlope)`. -/
lemma uBendB_eq_rightPoint_slope {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hxS : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendB hf ha hxS hdN =
      rightPointOfDir x (!₂[(1 : ℝ), uBendSlope hf ha hxS hdN]) := by
  have hw0 : (uBendDirPos hf ha hxS hdN) 0 ≠ 0 := uBendDirPos_coord_ne_zero hf ha hxS hdN
  have hc : ((uBendDirPos hf ha hxS hdN) 0)⁻¹ ≠ 0 := inv_ne_zero hw0
  have hsm := rightPointOfDir_smul (x := x) (d := uBendDirPos hf ha hxS hdN) (c := ((uBendDirPos hf ha hxS hdN) 0)⁻¹) hc hw0
  calc
    uBendB hf ha hxS hdN = rightPointOfDir x (uBendDirPos hf ha hxS hdN) := by
      exact uBendB_eq_rightPointOfDir hf ha hxS hdN
    _ = rightPointOfDir x (((uBendDirPos hf ha hxS hdN) 0)⁻¹ • uBendDirPos hf ha hxS hdN) := hsm.symm
    _ = rightPointOfDir x (!₂[(1 : ℝ), uBendSlope hf ha hxS hdN]) := by
      rw [uBendDirPos_unit_first hf ha hxS hdN]


/-- **U-matching: left endpoints**.  U-centre heights approaching the
centre height of a flat chord give U-leaf LEFT endpoints converging to
the chord's left seam endpoint `(0, α)`. -/
theorem uBend_left_endpoint_limit {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℕ → ℝ} {α β : ℝ}
    (hyU : ∀ n : ℕ, dN f (centrePoint (y n)) ≠ 0)
    (hylim : Tendsto y atTop (𝓝 (sideH₁ α β (1 / 2))))
    (hchordFlat : ∀ z : ℝ², z ∈ stripChord α β → dN f z = 0) :
    Tendsto (fun n : ℕ => uBendA hf ha (centrePoint_mem_stripInterior (y n)) (hyU n))
      atTop (𝓝 (!₂[(0 : ℝ), α])) := by
  let m : ℕ → ℝ := fun n => uBendSlope hf ha (centrePoint_mem_stripInterior (y n)) (hyU n)
  have hm : Tendsto m atTop (𝓝 (β - α)) := by
    simpa [m] using (uBend_slope_limit hf ha hchordFlat hyU hylim)
  have hu : Tendsto (fun n : ℕ => centrePoint (y n)) atTop
      (𝓝 (centrePoint (sideH₁ α β (1 / 2)))) :=
    (continuousAt_centrePoint (sideH₁ α β (1 / 2))).tendsto.comp hylim
  have hg : Continuous (fun t : ℝ => (!₂[(1 : ℝ), t] : ℝ²)) := by fun_prop
  have hd : Tendsto (fun n : ℕ => (!₂[(1 : ℝ), m n] : ℝ²)) atTop
      (𝓝 (!₂[(1 : ℝ), β - α])) := hg.continuousAt.tendsto.comp hm
  have hd0 : (!₂[(1 : ℝ), β - α] : ℝ²) 0 ≠ 0 := by norm_num
  have ht := tendsto_leftPointOfDir hu hd hd0
  have hval : leftPointOfDir (centrePoint (sideH₁ α β (1 / 2))) (!₂[(1 : ℝ), β - α]) =
      !₂[(0 : ℝ), α] := leftPointOfDir_chord_left α β
  have hnh : (fun p : ℝ² => 𝓝 p) (leftPointOfDir (centrePoint (sideH₁ α β (1 / 2)))
      (!₂[(1 : ℝ), β - α])) = (fun p : ℝ² => 𝓝 p) (!₂[(0 : ℝ), α]) := congrArg (fun p : ℝ² => 𝓝 p) hval
  have htarget : Tendsto (fun n : ℕ => leftPointOfDir (centrePoint (y n)) (!₂[(1 : ℝ), m n]))
      atTop (𝓝 (!₂[(0 : ℝ), α])) := by
    change Tendsto (fun n : ℕ => leftPointOfDir (centrePoint (y n)) (!₂[(1 : ℝ), m n]))
      atTop ((fun p : ℝ² => 𝓝 p) (!₂[(0 : ℝ), α]))
    rw [← hnh]
    exact ht
  have hpeq : (fun n : ℕ => uBendA hf ha (centrePoint_mem_stripInterior (y n)) (hyU n)) =
      fun n : ℕ => leftPointOfDir (centrePoint (y n)) (!₂[(1 : ℝ), m n]) := by
    funext n
    dsimp [m]
    exact uBendA_eq_leftPoint_slope hf ha (centrePoint_mem_stripInterior (y n)) (hyU n)
  rwa [hpeq]

/-- **U-matching: right endpoints**.  U-centre heights approaching the
centre height of a flat chord give U-leaf RIGHT endpoints converging to
the chord's right seam endpoint `(1, β)`. -/
theorem uBend_right_endpoint_limit {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℕ → ℝ} {α β : ℝ}
    (hyU : ∀ n : ℕ, dN f (centrePoint (y n)) ≠ 0)
    (hylim : Tendsto y atTop (𝓝 (sideH₁ α β (1 / 2))))
    (hchordFlat : ∀ z : ℝ², z ∈ stripChord α β → dN f z = 0) :
    Tendsto (fun n : ℕ => uBendB hf ha (centrePoint_mem_stripInterior (y n)) (hyU n))
      atTop (𝓝 (!₂[(1 : ℝ), β])) := by
  let m : ℕ → ℝ := fun n => uBendSlope hf ha (centrePoint_mem_stripInterior (y n)) (hyU n)
  have hm : Tendsto m atTop (𝓝 (β - α)) := by
    simpa [m] using (uBend_slope_limit hf ha hchordFlat hyU hylim)
  have hu : Tendsto (fun n : ℕ => centrePoint (y n)) atTop
      (𝓝 (centrePoint (sideH₁ α β (1 / 2)))) :=
    (continuousAt_centrePoint (sideH₁ α β (1 / 2))).tendsto.comp hylim
  have hg : Continuous (fun t : ℝ => (!₂[(1 : ℝ), t] : ℝ²)) := by fun_prop
  have hd : Tendsto (fun n : ℕ => (!₂[(1 : ℝ), m n] : ℝ²)) atTop
      (𝓝 (!₂[(1 : ℝ), β - α])) := hg.continuousAt.tendsto.comp hm
  have hd0 : (!₂[(1 : ℝ), β - α] : ℝ²) 0 ≠ 0 := by norm_num
  have ht := tendsto_rightPointOfDir hu hd hd0
  have hval : rightPointOfDir (centrePoint (sideH₁ α β (1 / 2))) (!₂[(1 : ℝ), β - α]) =
      !₂[(1 : ℝ), β] := rightPointOfDir_chord_right α β
  have hnh : (fun p : ℝ² => 𝓝 p) (rightPointOfDir (centrePoint (sideH₁ α β (1 / 2)))
      (!₂[(1 : ℝ), β - α])) = (fun p : ℝ² => 𝓝 p) (!₂[(1 : ℝ), β]) := congrArg (fun p : ℝ² => 𝓝 p) hval
  have htarget : Tendsto (fun n : ℕ => rightPointOfDir (centrePoint (y n)) (!₂[(1 : ℝ), m n]))
      atTop (𝓝 (!₂[(1 : ℝ), β])) := by
    change Tendsto (fun n : ℕ => rightPointOfDir (centrePoint (y n)) (!₂[(1 : ℝ), m n]))
      atTop ((fun p : ℝ² => 𝓝 p) (!₂[(1 : ℝ), β]))
    rw [← hnh]
    exact ht
  have hpeq : (fun n : ℕ => uBendB hf ha (centrePoint_mem_stripInterior (y n)) (hyU n)) =
      fun n : ℕ => rightPointOfDir (centrePoint (y n)) (!₂[(1 : ℝ), m n]) := by
    funext n
    dsimp [m]
    exact uBendB_eq_rightPoint_slope hf ha (centrePoint_mem_stripInterior (y n)) (hyU n)
  rwa [hpeq]
end Submission.PaperBand

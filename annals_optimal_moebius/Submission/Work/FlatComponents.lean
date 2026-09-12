import Submission.Work.FlatFrontier

open OptimalMoebius Topology ContDiff
open Filter
open scoped BigOperators Matrix Topology Metric
open InnerProductGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Prop main0 (block C, step 2): flat pieces lie on one side of U-bend lines

Flat-component analysis via `FlatRegions`: every point of a flat piece
(an open set on which the shape operator vanishes) is flat; but every
interior strip point on the line of a maximal U-bend is a `U`-point
(`FlatFrontier.interior_on_line_is_U`).  Hence:

* **flat pieces avoid U-bend lines entirely**
  (`flat_piece_avoids_uBend_line`): no point of the piece lies on the
  chord line of a `U`-point;
* by connectedness, a flat piece lies STRICTLY ON ONE SIDE of every such
  line (`flat_piece_one_side_of_uBend`): the signed line functional
  `signedLineFunc q w z = (z0 − q0)·w1 − (z1 − q1)·w0` never vanishes on
  the piece, and if it took both signs the intermediate-value theorem
  would force a zero.

This is the geometric core of the trapezoid picture of Prop main0: the
frontier of a flat region toward `U` is made of U-bend lines, with the flat
region contained in a half-plane on one side of each such line.
-/

noncomputable section
namespace Submission.PaperBand

/-- The signed affine-linear functional vanishing exactly on the line
through `q` in direction `w`: `(z − q) × w` in the plane. -/
def signedLineFunc (q w z : ℝ²) : ℝ :=
  (z 0 - q 0) * w 1 - (z 1 - q 1) * w 0

/-- The signed line functional is continuous. -/
lemma continuous_signedLineFunc (q w : ℝ²) : Continuous (fun z : ℝ² => signedLineFunc q w z) := by
  unfold signedLineFunc
  fun_prop

/-- A point lies on the affine line through `q` in direction `w` (with
`w 0 ≠ 0`) iff the signed functional vanishes. -/
lemma on_line_iff_signedLineFunc_eq_zero {q w z : ℝ²} (hw0 : w 0 ≠ 0) :
    (∃ s : ℝ, z = q + s • w) ↔ signedLineFunc q w z = 0 := by
  constructor
  · rintro ⟨s, hz⟩
    unfold signedLineFunc
    rw [hz]
    -- (q + s•w - q) = s•w coordinatewise
    have hc0 : (q + s • w) 0 - q 0 = s * w 0 := by
      have : (q + s • w) 0 = q 0 + s * w 0 := by simp
      linarith
    have hc1 : (q + s • w) 1 - q 1 = s * w 1 := by
      have : (q + s • w) 1 = q 1 + s * w 1 := by simp
      linarith
    rw [hc0, hc1]
    ring
  · intro hφ
    let s : ℝ := (z 0 - q 0) / w 0
    refine ⟨s, ?_⟩
    ext i
    fin_cases i
    · -- coordinate 0
      simp [s]
      field_simp [hw0]
      ring
    · -- coordinate 1
      have hφ' : (z 0 - q 0) * w 1 - (z 1 - q 1) * w 0 = 0 := hφ
      have hm : (z 0 - q 0) * w 1 = (z 1 - q 1) * w 0 := by linarith
      have hz1 : ((z 0 - q 0) * w 1) / w 0 = z 1 - q 1 := by
        rw [hm]
        field_simp [hw0]
      calc
        z 1 = q 1 + (z 1 - q 1) := by ring
        _ = q 1 + s * w 1 := by
          rw [← hz1]
          congr 1
          rw [show s * w 1 = ((z 0 - q 0) * w 1) / w 0 by
            simp [s]
            field_simp [hw0]]
        _ = (q + s • w) 1 := by simp

/-- **Flat pieces avoid U-bend lines**: no point of an open set on which the
shape operator vanishes (lying in the strip interior) lies on the line of a
canonical U-bend — such a point would be both flat and a `U`-point. -/
lemma flat_piece_avoids_uBend_line {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {s : Set ℝ²} (hssub : s ⊆ stripInterior)
    (hflat : ∀ x ∈ s, dN f x = 0) {q : ℝ²} (hq : q ∈ stripInterior)
    (hU : dN f q ≠ 0) (z : ℝ²) (hz : z ∈ s) :
    signedLineFunc q (uBendDirPos hf ha hq hU) z ≠ 0 := by
  intro hzero
  rcases uBendDirPos_spec hf ha hq hU with ⟨hker, hwne, hwpos⟩
  have hline : ∃ t : ℝ, z = q + t • (uBendDirPos hf ha hq hU) :=
    (on_line_iff_signedLineFunc_eq_zero (q := q) (w := uBendDirPos hf ha hq hU) (z := z)
      (ne_of_gt hwpos)).2 hzero
  have hzI : z ∈ stripInterior := hssub hz
  have hUz : dN f z ≠ 0 :=
    interior_on_line_is_U hf ha (x := q) (z := z) hq hU hzI hline
  exact hUz (hflat z hz)

/-- **Flat pieces lie strictly on one side of every U-bend line**: for a
preconnected flat piece `s` (an open connected flat region), the signed line
functional of a canonical U-bend line has a constant strict sign on `s` (it
never vanishes, and if it took both signs the intermediate-value theorem
would produce a zero). -/
theorem flat_piece_one_side_of_uBend {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {s : Set ℝ²} (hsconn : IsPreconnected s)
    (hssub : s ⊆ stripInterior) (hflat : ∀ x ∈ s, dN f x = 0)
    {q : ℝ²} (hq : q ∈ stripInterior) (hU : dN f q ≠ 0) :
    (∀ z ∈ s, 0 < signedLineFunc q (uBendDirPos hf ha hq hU) z) ∨
      (∀ z ∈ s, signedLineFunc q (uBendDirPos hf ha hq hU) z < 0) := by
  let w : ℝ² := uBendDirPos hf ha hq hU
  let φ : ℝ² → ℝ := fun z => signedLineFunc q w z
  have hne0 : ∀ z ∈ s, φ z ≠ 0 := by
    intro z hz
    exact flat_piece_avoids_uBend_line hf ha hssub hflat hq hU z hz
  have hφcontOn : ContinuousOn φ s := by
    exact (continuous_signedLineFunc q w).continuousOn
  by_cases hpos : ∃ z ∈ s, 0 < φ z
  · -- some point on the positive side; all others are also positive
    left
    intro z₂ hz₂
    by_contra hnot
    have hz₂le : φ z₂ ≤ 0 := le_of_not_gt hnot
    have hz₂neg : φ z₂ < 0 := lt_of_le_of_ne hz₂le (hne0 z₂ hz₂)
    rcases hpos with ⟨z₁, hz₁, hz₁pos⟩
    -- IVT: 0 is between φ z₂ < 0 and φ z₁ > 0
    have hIVT : Set.Icc (φ z₂) (φ z₁) ⊆ φ '' s :=
      IsPreconnected.intermediate_value hsconn hz₂ hz₁ hφcontOn
    have hzero_mem : (0 : ℝ) ∈ Set.Icc (φ z₂) (φ z₁) := by
      rw [Set.mem_Icc]
      exact ⟨le_of_lt hz₂neg, le_of_lt hz₁pos⟩
    rcases hIVT hzero_mem with ⟨z₀, hz₀, hφz₀⟩
    exact hne0 z₀ hz₀ (by simpa [φ] using hφz₀)
  · -- no positive point: all are non-positive and nonzero, hence negative
    right
    intro z₂ hz₂
    have hz₂le : φ z₂ ≤ 0 := by
      by_contra hgt
      exact hpos ⟨z₂, hz₂, lt_of_not_ge hgt⟩
    exact lt_of_le_of_ne hz₂le (hne0 z₂ hz₂)

/-! ## Connected components of the flat interior -/

/-- The **flat component** of a point `p`: the connected component of `p`
inside the interior of the flat set (`interior (FlatSet f)`).  For a
flat-interior point this is the maximal open flat region containing it. -/
noncomputable def flatComponent (f : ℝ² → ℝ³) (p : ℝ²) : Set ℝ² :=
  connectedComponentIn (interior (FlatSet f)) p

/-- `p` lies in its flat component (for flat-interior `p`). -/
lemma mem_flatComponent {f : ℝ² → ℝ³} {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    p ∈ flatComponent f p := by
  exact mem_connectedComponentIn hp

/-- The flat component lies inside the interior of the flat set. -/
lemma flatComponent_subset_flatInterior (f : ℝ² → ℝ³) (p : ℝ²) :
    flatComponent f p ⊆ interior (FlatSet f) := by
  exact connectedComponentIn_subset (interior (FlatSet f)) p

/-- The flat component is preconnected. -/
lemma isPreconnected_flatComponent (f : ℝ² → ℝ³) (p : ℝ²) :
    IsPreconnected (flatComponent f p) := by
  unfold flatComponent
  exact isPreconnected_connectedComponentIn

/-- The flat component lies inside the strip interior. -/
lemma flatComponent_subset_stripInterior (f : ℝ² → ℝ³) (p : ℝ²) :
    flatComponent f p ⊆ stripInterior := by
  intro z hz
  have hzInt : z ∈ interior (FlatSet f) := (flatComponent_subset_flatInterior f p) hz
  have hzF : z ∈ FlatSet f := interior_subset hzInt
  exact FlatSet_subset_stripInterior f hzF

/-- The shape operator vanishes everywhere on a flat component (it is a
flat piece). -/
lemma flatComponent_flat {f : ℝ² → ℝ³} {p z : ℝ²} (hz : z ∈ flatComponent f p) :
    dN f z = 0 := by
  have hzInt : z ∈ interior (FlatSet f) := (flatComponent_subset_flatInterior f p) hz
  have hzF : z ∈ FlatSet f := interior_subset hzInt
  exact (mem_FlatSet.mp hzF).2

/-- **Every flat component is an open flat piece**: its points are
flat-interior.  (The component is the connected component of the open set
`interior (FlatSet f)`; openness in the plane is not needed to run the
one-sided argument, but recorded here for the foliation picture.) -/
lemma flatComponent_mem_flatInterior {f : ℝ² → ℝ³} {p z : ℝ²} (hz : z ∈ flatComponent f p) :
    IsFlatInterior f z := by
  have hzInt : z ∈ interior (FlatSet f) := (flatComponent_subset_flatInterior f p) hz
  have hzS : z ∈ stripInterior := (FlatSet_subset_stripInterior f (interior_subset hzInt))
  exact (IsFlatInterior_iff_mem_interior_FlatSet (f := f) hzS).2 hzInt

/-- **A flat component lies strictly on one side of every U-bend line**: the
flat component of a flat-interior point `p` is a preconnected flat piece, so
`flat_piece_one_side_of_uBend` applies to it. -/
theorem flatComponent_one_side_of_uBend {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hpS : p ∈ stripInterior) (hfi : IsFlatInterior f p)
    {q : ℝ²} (hq : q ∈ stripInterior) (hU : dN f q ≠ 0) :
    (∀ z ∈ flatComponent f p,
      0 < signedLineFunc q (uBendDirPos hf ha hq hU) z) ∨
      (∀ z ∈ flatComponent f p,
        signedLineFunc q (uBendDirPos hf ha hq hU) z < 0) := by
  exact flat_piece_one_side_of_uBend hf ha (s := flatComponent f p)
    (hsconn := isPreconnected_flatComponent f p)
    (hssub := flatComponent_subset_stripInterior f p)
    (hflat := fun x hx => flatComponent_flat (p := p) hx) hq hU

/-! ## Frontier separation: U-points keep away from flat components -/

/-- Flat components are open (the plane is locally connected, and
`interior (FlatSet f)` is open). -/
lemma isOpen_flatComponent (f : ℝ² → ℝ³) (p : ℝ²) : IsOpen (flatComponent f p) := by
  unfold flatComponent
  exact IsOpen.connectedComponentIn (F := interior (FlatSet f)) isOpen_interior

/-- **No U-point lies in the closure of the flat set**: `dN` is continuous at
the interior point `q` with `dN f q ≠ 0`, so a whole ball around `q` has
`dN ≠ 0` and therefore meets no flat point. -/
theorem no_U_in_closure_FlatSet {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {q : ℝ²} (hq : q ∈ stripInterior) (hU : dN f q ≠ 0) :
    q ∉ closure (FlatSet f) := by
  have hcont : ContinuousAt (fun z : ℝ² => dN f z) q :=
    ContinuousOn.continuousAt (ContDiffOn.continuousOn (contDiffOn_dN hf))
      (IsOpen.mem_nhds stripInterior_isOpen hq)
  have hNev : {z : ℝ² | dN f z ≠ 0} ∈ 𝓝 q := by
    exact hcont.preimage_mem_nhds (isOpen_ne.mem_nhds hU)
  rintro hc
  rcases (Metric.mem_nhds_iff.mp hNev) with ⟨δ, hδ, hball⟩
  rcases Metric.mem_closure_iff.mp hc δ hδ with ⟨z, hzF, hzd⟩
  have hzball : z ∈ Metric.ball q δ := by
    rw [Metric.mem_ball]
    simpa [dist_comm] using hzd
  have hzN : z ∈ {z : ℝ² | dN f z ≠ 0} := hball hzball
  exact hzN (mem_FlatSet.mp hzF).2

/-- **Bends keep a definite margin from flat-interior points**: around a
flat-interior point `p` there is a ball `B(p, ρ)` (inside the strip, fully
flat) that NO open U-leaf meets. -/
theorem uBend_avoids_flat_interior_ball {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hpS : p ∈ stripInterior) (hfi : IsFlatInterior f p) :
    ∃ ρ > 0, ∀ (q : ℝ²) (hq : q ∈ stripInterior) (hU : dN f q ≠ 0),
      uBendSet hf ha hq hU ∩ Metric.ball p ρ = ∅ := by
  rcases hfi with ⟨U0, hU0o, hUp, hU0flat⟩
  rcases (Metric.mem_nhds_iff.mp (hU0o.mem_nhds hUp)) with ⟨ρ1, hρ1, hb1⟩
  rcases (Metric.mem_nhds_iff.mp (stripInterior_isOpen.mem_nhds hpS)) with ⟨ρ2, hρ2, hb2⟩
  let ρ : ℝ := min ρ1 ρ2
  have hρpos : 0 < ρ := lt_min hρ1 hρ2
  refine ⟨ρ, hρpos, ?_⟩
  intro q hq hU
  ext z
  constructor
  · rintro ⟨hzL, hzB⟩
    have hzU0 : z ∈ U0 := hb1 (Metric.ball_subset_ball (min_le_left ρ1 ρ2) hzB)
    have hzS : z ∈ stripInterior := hb2 (Metric.ball_subset_ball (min_le_right ρ1 ρ2) hzB)
    have hzF : z ∈ FlatSet f := (mem_FlatSet.mpr ⟨hzS, hU0flat z hzU0⟩)
    exact (uBendSet_subset_U_and_kernel hf ha hq hU).1 z hzL (mem_FlatSet.mp hzF).2
  · rintro hz
    exact False.elim ((Set.mem_empty_iff_false z).mp hz)

/-! ## Ruling directions: continuity on `U` and adjacency to flat components -/

/-- **The unit kernel direction is continuous at every `U`-point** (ambient,
2-dimensional): the mirror kernel field `V2f` is smooth and nonvanishing on
`U`, so `unitKernelDir = V2f/‖V2f‖` (`KernelUnit`) varies continuously. -/
theorem continuousAt_uBendUnitDir {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hU : dN f x ≠ 0) :
    ContinuousAt (fun q : ℝ² => unitKernelDir f q) x := by
  exact continuousAt_unitKernelDir hf hx (V2f_ne_zero_at_U hf ha hx hU)

/-- **Consequence (adjacency constancy, continuous form)**: two `U`-points
`q₁`, `q₂` close together have nearly parallel bend lines — the bend
direction varies continuously with the point on `U`, by
`continuousAt_uBendUnitDir`.  (Stated as the metric bound that the
continuity supplies.) -/
lemma uBendDir_epsilon_parallel {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hU : dN f x ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ q ∈ stripInterior, dN f q ≠ 0 →
      ‖q - x‖ < δ → ‖unitKernelDir f q - unitKernelDir f x‖ < ε := by
  rcases Metric.continuousAt_iff.mp (continuousAt_uBendUnitDir hf ha hx hU) ε hε with
    ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, ?_⟩
  intro q hq hUq hdist
  -- hball : ∀ y, dist y x < δ → dist (unitKernelDir f y) (unitKernelDir f x) < ε
  have hclose : dist q x < δ := by
    simpa [dist_eq_norm] using hdist
  have hd := hball hclose
  simpa [dist_eq_norm] using hd

/-- **Bend lines avoid every flat component**: no open U-leaf meets the flat
component of a flat-interior point (a flat component is contained in the
flat set, and U-leaves are disjoint from it). -/
theorem uBendSet_disjoint_flatComponent {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p q : ℝ²} (hq : q ∈ stripInterior) (hU : dN f q ≠ 0) :
    uBendSet hf ha hq hU ∩ flatComponent f p = ∅ := by
  ext z
  constructor
  · rintro ⟨hzL, hzC⟩
    have hzF : z ∈ FlatSet f := (flatComponent_subset_flatInterior f p) hzC |> interior_subset
    exact (uBendSet_subset_U_and_kernel hf ha hq hU).1 z hzL (mem_FlatSet.mp hzF).2
  · rintro hz
    exact False.elim ((Set.mem_empty_iff_false z).mp hz)

/-! ## Flat components are planar rigid patches; their chords are pre-bends -/

/-- **Flat components are affine patches**: on the flat component of
`p`, `f` equals the affine map `z ↦ f x₀ + fderiv f x₀ (z − x₀)` (so the
component maps rigidly onto a planar region). -/
theorem flatComponent_affine {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p x₀ : ℝ²} (hx₀ : x₀ ∈ flatComponent f p) :
    ∀ z ∈ flatComponent f p,
      f z = f x₀ + (fderiv ℝ f x₀) (z - x₀) := by
  exact affine_on_flat hf (hs := isOpen_flatComponent f p)
    (hconn := isPreconnected_flatComponent f p)
    (hsub := flatComponent_subset_stripInterior f p)
    (hflat := fun x hx => flatComponent_flat (f := f) hx) hx₀

/-- **The unit normal is constant on a flat component**. -/
theorem flatComponent_unitNormal_const {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} :
    ∃ N₀ : ℝ³, ∀ z ∈ flatComponent f p, unitNormal f z = N₀ := by
  exact unitNormal_const_on hf (hs := isOpen_flatComponent f p)
    (hconn := isPreconnected_flatComponent f p)
    (hsub := flatComponent_subset_stripInterior f p)
    (hflat := fun x hx => flatComponent_flat (f := f) hx)

/-- **The image of a flat component lies in a plane**: there is a unit
`N₀` and a constant `c` with `⟪f z, N₀⟫ = c` for every `z` in the
component. -/
theorem flatComponent_in_plane {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p : ℝ²} :
    ∃ N₀ : ℝ³, ‖N₀‖ = 1 ∧ ∃ c : ℝ, ∀ z ∈ flatComponent f p, inner ℝ (f z) N₀ = c := by
  exact image_in_plane hf (hs := isOpen_flatComponent f p)
    (hconn := isPreconnected_flatComponent f p)
    (hsub := flatComponent_subset_stripInterior f p)
    (hflat := fun x hx => flatComponent_flat (f := f) hx)

/-- **Straight chords of a flat component are pre-bends**: a segment
`{x₀ + t•v | t ∈ [A,B]}` contained in a flat component has the three bend
properties (strip-interior points with `v` a kernel direction, affine image,
constant unit normal) — `FlatBends.flat_chord_is_prebend` instantiated at
the component level. -/
theorem flatComponent_chord_is_prebend {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p x₀ : ℝ²} (hx₀ : x₀ ∈ flatComponent f p) {v : ℝ²} {A B : ℝ}
    (hseg : ∀ t ∈ Set.Icc A B, x₀ + t • v ∈ flatComponent f p) :
    (∀ t ∈ Set.Icc A B,
      x₀ + t • v ∈ stripInterior ∧ dN f (x₀ + t • v) v = 0) ∧
    (∀ t ∈ Set.Icc A B,
      f (x₀ + t • v) = f x₀ + t • (fderiv ℝ f x₀ v)) ∧
    (∀ t ∈ Set.Icc A B, unitNormal f (x₀ + t • v) = unitNormal f x₀) := by
  exact flat_chord_is_prebend hf (hs := isOpen_flatComponent f p)
    (hconn := isPreconnected_flatComponent f p)
    (hsub := flatComponent_subset_stripInterior f p)
    (hflat := fun x hx => flatComponent_flat (f := f) hx) hx₀ hseg

/-! ## Frontier of a flat component: degenerate flat points only -/

/-- A flat component lies inside the flat set. -/
lemma flatComponent_subset_FlatSet (f : ℝ² → ℝ³) (p : ℝ²) :
    flatComponent f p ⊆ FlatSet f := by
  intro z hz
  exact interior_subset (flatComponent_subset_flatInterior f p hz)

/-- **Frontier points of a flat component that lie in the strip interior are
flat** (not `U`-points): they are in the closure of the flat set (the
component is), and no `U`-point lies in the closure of the flat set. -/
theorem flatComponent_frontier_subset_FlatSet {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {p z : ℝ²} (hzS : z ∈ stripInterior) (hz : z ∈ frontier (flatComponent f p)) :
    z ∈ FlatSet f := by
  rw [frontier] at hz
  rw [Set.mem_diff] at hz
  have hzcl : z ∈ closure (flatComponent f p) := hz.1
  have hclF : closure (flatComponent f p) ⊆ closure (FlatSet f) :=
    closure_mono (flatComponent_subset_FlatSet f p)
  have hzclF : z ∈ closure (FlatSet f) := hclF hzcl
  refine (mem_FlatSet.mpr ⟨hzS, ?_⟩)
  by_contra hz0
  exact no_U_in_closure_FlatSet hf hzS hz0 hzclF

/-- **Frontier points of a flat component are not flat-interior**: if a
frontier point `z` of a flat component were flat-interior, a small open
CONNECTED ball around `z` inside the flat interior would meet the component
(`z` is in its closure); being connected, that ball would then lie in the
component (maximality of connected components), so `z` would be an interior
point of the component — contradicting that it is on the frontier. -/
theorem flatComponent_frontier_not_flat_interior {f : ℝ² → ℝ³} {p z : ℝ²}
    (hzS : z ∈ stripInterior) (hz : z ∈ frontier (flatComponent f p)) :
    ¬ IsFlatInterior f z := by
  intro hfi
  let C : Set ℝ² := flatComponent f p
  rw [frontier] at hz
  rw [Set.mem_diff] at hz
  have hzcl : z ∈ closure C := hz.1
  have hzni : z ∉ interior C := hz.2
  have hzF : z ∈ interior (FlatSet f) := (IsFlatInterior_iff_mem_interior_FlatSet (f := f) hzS).1 hfi
  rcases (Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hzF)) with ⟨ρ, hρ, hb1⟩
  -- hb1 : Metric.ball z ρ ⊆ interior (FlatSet f), and the ball is connected
  have hBallPre : IsPreconnected (Metric.ball z ρ) := (convex_ball (a := z) (r := ρ)).isPreconnected
  -- the ball meets C (z is in its closure)
  have hmt : (Metric.ball z ρ ∩ C).Nonempty := by
    rcases Metric.mem_closure_iff.mp hzcl ρ hρ with ⟨w, hwC, hwd⟩
    refine ⟨w, ?_, hwC⟩
    rw [Metric.mem_ball]
    simpa [dist_comm] using hwd
  rcases hmt with ⟨w, hwB, hwC⟩
  -- maximality: the whole ball lies in the component of w, which is C
  have hmax : Metric.ball z ρ ⊆ connectedComponentIn (interior (FlatSet f)) w :=
    IsPreconnected.subset_connectedComponentIn (s := Metric.ball z ρ) (x := w) hBallPre hwB hb1
  have heq : connectedComponentIn (interior (FlatSet f)) p =
      connectedComponentIn (interior (FlatSet f)) w :=
    connectedComponentIn_eq (F := interior (FlatSet f)) (x := p) (y := w)
      (by simpa [C, flatComponent] using hwC)
  have hzC : z ∈ C := by
    have hzcc : z ∈ connectedComponentIn (interior (FlatSet f)) w :=
      hmax (Metric.mem_ball.mpr (by simpa [dist_self] using hρ))
    simpa [C, flatComponent, ← heq] using hzcc
  have hCopen : IsOpen C := by simpa [C] using isOpen_flatComponent f p
  have hzIC : z ∈ interior C := by
    rw [IsOpen.interior_eq hCopen]
    exact hzC
  exact hzni hzIC

/-! ## Flat-frontier transition: the flat side of nearby rulings is stable -/

/-- **A flat point never lies on a U-ruling**: `signedLineFunc q d z₀ ≠ 0`
whenever `z₀` is flat, `q` is a `U`-point and `d` is a nonzero kernel
direction at `q` (`z₀` would then be an interior point of the open leaf of
`q`, hence a `U`-point). -/
lemma flat_point_not_on_uBend_dir {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {z₀ : ℝ²} (hz₀F : z₀ ∈ FlatSet f)
    {q d : ℝ²} (hqS : q ∈ stripInterior) (hU : dN f q ≠ 0)
    (hdker : dN f q d = 0) (hdne : d ≠ 0) (hd0 : d 0 ≠ 0) :
    signedLineFunc q d z₀ ≠ 0 := by
  intro hz
  have hon : ∃ s : ℝ, z₀ = q + s • d :=
    (on_line_iff_signedLineFunc_eq_zero (q := q) (w := d) (z := z₀) hd0).2 hz
  have hz₀U : dN f z₀ ≠ 0 := by
    -- z₀ interior & collinear with q along kernel direction d: parallel to the canonical dir
    rcases uBendDirPos_spec hf ha hqS hU with ⟨hker, hwne, hwpos⟩
    rcases kernel_direction_parallel hf hqS hU hker hdker hwne with ⟨c, hc⟩
    rcases hon with ⟨s, hzEq⟩
    -- z₀ = q + s•d = q + (s*c)•wpos
    apply interior_on_line_is_U hf ha hqS hU ?_ ⟨s * c, ?_⟩
    · have hz₀S : z₀ ∈ stripInterior := (mem_FlatSet.mp hz₀F).1
      exact hz₀S
    · calc
        z₀ = q + s • d := hzEq
        _ = q + s • (c • uBendDirPos hf ha hqS hU) := by rw [hc]
        _ = q + (s * c) • uBendDirPos hf ha hqS hU := by rw [smul_smul]
  have hz₀flat : dN f z₀ = 0 := (mem_FlatSet.mp hz₀F).2
  exact hz₀U hz₀flat

/-- **Rulings keep the flat side locally constant**: near a `U`-point `q₀`
whose ruling has a fixed flat point `z₀` on one side, every nearby `U`-point
has `z₀` strictly on the SAME side of its ruling (the signed line functional
in the continuous unit kernel direction is nonzero at `z₀` and varies
continuously, so it cannot change sign). -/
theorem ruling_flat_side_locally_constant {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {z₀ : ℝ²} (hz₀F : z₀ ∈ FlatSet f)
    {q₀ : ℝ²} (hq₀S : q₀ ∈ stripInterior) (hU₀ : dN f q₀ ≠ 0) :
    ∃ δ > 0, ∀ q ∈ Metric.ball q₀ δ, q ∈ stripInterior → dN f q ≠ 0 →
      (0 < signedLineFunc q (unitKernelDir f q) z₀ ↔
        0 < signedLineFunc q₀ (unitKernelDir f q₀) z₀) := by
  -- the signed functional in the continuous unit kernel direction
  let F : ℝ² → ℝ := fun q => signedLineFunc q (unitKernelDir f q) z₀
  -- F is continuous at q₀
  have hUc : ContinuousAt (fun q : ℝ² => unitKernelDir f q) q₀ :=
    continuousAt_uBendUnitDir hf ha hq₀S hU₀
  have hU0c : ContinuousAt (fun q : ℝ² => (unitKernelDir f q) 0) q₀ := by
    have hc0 : ContinuousAt (fun d : ℝ² => d 0) (unitKernelDir f q₀) := by fun_prop
    exact ContinuousAt.comp (x := q₀) (f := unitKernelDir f) (g := fun d : ℝ² => d 0)
      hc0 hUc
  have hU1c : ContinuousAt (fun q : ℝ² => (unitKernelDir f q) 1) q₀ := by
    have hc1 : ContinuousAt (fun d : ℝ² => d 1) (unitKernelDir f q₀) := by fun_prop
    exact ContinuousAt.comp (x := q₀) (f := unitKernelDir f) (g := fun d : ℝ² => d 1)
      hc1 hUc
  have hterm0 : ContinuousAt (fun q : ℝ² => (z₀ 0 - q 0) * (unitKernelDir f q) 1) q₀ := by
    have hz : ContinuousAt (fun q : ℝ² => z₀ 0 - q 0) q₀ := by fun_prop
    exact ContinuousAt.mul hz hU1c
  have hterm1 : ContinuousAt (fun q : ℝ² => (z₀ 1 - q 1) * (unitKernelDir f q) 0) q₀ := by
    have hz : ContinuousAt (fun q : ℝ² => z₀ 1 - q 1) q₀ := by fun_prop
    exact ContinuousAt.mul hz hU0c
  have hFcont : ContinuousAt F q₀ := by
    have hm := ContinuousAt.sub hterm0 hterm1
    unfold F signedLineFunc
    exact hm
  -- F q₀ ≠ 0 (flat point not on the ruling)
  have hF0ne : F q₀ ≠ 0 := by
    rcases V2f_ne_zero_at_U hf ha hq₀S hU₀ with hV2  -- not needed
    unfold F
    have hd0 : (unitKernelDir f q₀) 0 ≠ 0 := by
      rcases uBendDirPos_spec hf ha hq₀S hU₀ with ⟨hker, hwne, hwpos⟩
      -- unitKernelDir q₀ is a nonzero kernel vector at q₀: apply the kernel-vector lemma
      apply kernel_vector_coord0_ne_zero hf ha hq₀S hU₀ (unitKernelDir_mem_ker hf hq₀S)
      exact unitKernelDir_ne_zero (V2f_ne_zero_at_U hf ha hq₀S hU₀)
    exact flat_point_not_on_uBend_dir hf ha hz₀F hq₀S hU₀
      (unitKernelDir_mem_ker hf hq₀S) (unitKernelDir_ne_zero (V2f_ne_zero_at_U hf ha hq₀S hU₀)) hd0
  -- continuity at q₀ with ε = |F q₀|/2 gives a δ-ball of the same sign
  have hε : 0 < |F q₀| / 2 := half_pos (abs_pos.mpr hF0ne)
  rcases Metric.continuousAt_iff.mp hFcont (|F q₀| / 2) hε with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, ?_⟩
  intro q hqball hqS hUq
  have hclose : dist (F q) (F q₀) < |F q₀| / 2 := hball hqball
  have habs : |F q - F q₀| < |F q₀| / 2 := by
    simpa [Real.dist_eq] using hclose
  by_cases hpos : 0 < F q₀
  · -- F q₀ > 0: nearby values are positive
    rw [abs_of_pos hpos] at habs
    constructor
    · intro hqpos
      exact hpos
    · intro hq0
      have hx := abs_lt.mp habs
      linarith
  · -- F q₀ < 0: nearby values are negative
    have hneg : F q₀ < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hF0ne
    rw [abs_of_neg hneg] at habs
    constructor
    · intro hqpos
      have hx := abs_lt.mp habs
      linarith
    · intro hq0
      exfalso
      linarith

/-! ## Degenerate-frontier analysis: U-points accumulate at every such point -/

/-- **U-points are dense around every degenerate frontier point**: if `e` is
a flat, non-flat-interior point of the strip (a degenerate flat frontier
point), then every ball around `e` contains a `U`-point (`dN ≠ 0`) — the
only way a ball could avoid `U`-points would be for all its points to be
flat, making `e` flat-interior. -/
theorem U_dense_near_degenerate_frontier {a : ℝ} {f : ℝ² → ℝ³}
    {e : ℝ²} (_heS : e ∈ stripInterior) (heF : e ∈ FlatSet f)
    (hni : ¬ IsFlatInterior f e) :
    ∀ δ > 0, ∃ q ∈ Metric.ball e δ, dN f q ≠ 0 := by
  intro δ hδ
  by_contra hnone
  -- no U point in the ball: every point of the ball is flat
  have hballflat : ∀ q ∈ Metric.ball e δ, dN f q = 0 := by
    intro q hq
    by_contra hq0
    exact hnone ⟨q, hq, hq0⟩
  -- ball is an open flat neighbourhood of e, so e is flat-interior
  have hfi : IsFlatInterior f e := by
    refine ⟨Metric.ball e δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, ?_⟩
    exact hballflat
  exact hni hfi

/-- **Degenerate frontier points are strictly on one side of every nearby
U-ruling**: a flat point (in particular a degenerate frontier point) never
lies on the line of a `U`-point's ruling, so the signed functional at `e`
with respect to any ruling is nonzero. -/
lemma degenerate_frontier_not_on_uBend_dir {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e : ℝ²} (heF : e ∈ FlatSet f)
    {q : ℝ²} (hqS : q ∈ stripInterior) (hU : dN f q ≠ 0) :
    signedLineFunc q (unitKernelDir f q) e ≠ 0 := by
  have hd0 : (unitKernelDir f q) 0 ≠ 0 := by
    apply kernel_vector_coord0_ne_zero hf ha hqS hU (unitKernelDir_mem_ker hf hqS)
    exact unitKernelDir_ne_zero (V2f_ne_zero_at_U hf ha hqS hU)
  exact flat_point_not_on_uBend_dir hf ha heF hqS hU
    (unitKernelDir_mem_ker hf hqS)
    (unitKernelDir_ne_zero (V2f_ne_zero_at_U hf ha hqS hU)) hd0

/-! ## Ruling accumulation: coordinate compactness groundwork -/

/-- Coordinate `0` of a vector is bounded by its norm (EuclideanSpace). -/
lemma abs_coord0_le_norm (x : ℝ²) : |x 0| ≤ ‖x‖ := by
  have hle : (x 0) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_coord_sum]
    nlinarith [sq_nonneg (x 1)]
  have hnn : 0 ≤ ‖x‖ := norm_nonneg _
  rw [sq_le_sq] at hle
  simpa [abs_of_nonneg hnn] using hle

/-- Coordinate `1` of a vector is bounded by its norm (EuclideanSpace). -/
lemma abs_coord1_le_norm (x : ℝ²) : |x 1| ≤ ‖x‖ := by
  have hle : (x 1) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_coord_sum]
    nlinarith [sq_nonneg (x 0)]
  have hnn : 0 ≤ ‖x‖ := norm_nonneg _
  rw [sq_le_sq] at hle
  simpa [abs_of_nonneg hnn] using hle

/-- Unit directions have coordinates in `[−1, 1]`: for a sequence of unit
vectors (such as the ruling directions of a `U`-sequence), each coordinate
sequence lies in the compact interval `[−1, 1]` — the input to the
Bolzano–Weierstrass extraction used in the ruling-accumulation lemma. -/
lemma unitDir_coords_bounded {u : ℕ → ℝ²} (h : ∀ n, ‖u n‖ = 1) :
    ∀ n, (u n) 0 ∈ Set.Icc (-1 : ℝ) 1 ∧ (u n) 1 ∈ Set.Icc (-1 : ℝ) 1 := by
  intro n
  have hle0 := abs_coord0_le_norm (u n)
  have hle1 := abs_coord1_le_norm (u n)
  rw [h n] at hle0 hle1
  rcases abs_le.mp hle0 with ⟨hhi0, hlo0⟩
  rcases abs_le.mp hle1 with ⟨hhi1, hlo1⟩
  constructor <;> rw [Set.mem_Icc] <;> constructor <;> linarith

/-- Ruling directions of a `U`-sequence are unit vectors (the mirror kernel
field normalized), ready for subsequence extraction. -/
lemma uBend_dir_seq_unit {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {q : ℕ → ℝ²} (hqS : ∀ n, q n ∈ stripInterior) (hqU : ∀ n, dN f (q n) ≠ 0) :
    ∀ n, ‖unitKernelDir f (q n)‖ = 1 := by
  intro n
  exact norm_unitKernelDir (V2f_ne_zero_at_U hf ha (hqS n) (hqU n))
/-- Coordinatewise convergence implies convergence in the plane (via the
norm bound `‖x‖ ≤ |x 0| + |x 1|`). -/
lemma tendsto_vector_of_coords {u : ℕ → ℝ²} {w : ℝ²}
    (h0 : Tendsto (fun n => (u n) 0) atTop (𝓝 (w 0)))
    (h1 : Tendsto (fun n => (u n) 1) atTop (𝓝 (w 1))) :
    Tendsto u atTop (𝓝 w) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / 2 := by positivity
  have h0e : ∀ᶠ n in atTop, |(u n) 0 - w 0| < ε / 2 := by
    have hd := (Metric.tendsto_nhds.mp h0) (ε / 2) hδ
    filter_upwards [hd] with n hn
    simpa [Real.dist_eq] using hn
  have h1e : ∀ᶠ n in atTop, |(u n) 1 - w 1| < ε / 2 := by
    have hd := (Metric.tendsto_nhds.mp h1) (ε / 2) hδ
    filter_upwards [hd] with n hn
    simpa [Real.dist_eq] using hn
  filter_upwards [h0e, h1e] with n hn0 hn1
  rw [dist_eq_norm]
  have hle := norm_le_abs_coord_sum (u n - w)
  have hb : |(u n - w) 0| + |(u n - w) 1| < ε := by
    have h0' : |(u n - w) 0| = |(u n) 0 - w 0| := by simp
    have h1' : |(u n - w) 1| = |(u n) 1 - w 1| := by simp
    rw [h0', h1']
    linarith
  linarith


/-! ## Ruling accumulation: subsequential convergence of unit directions -/

/-- A sequence of unit vectors in the plane has a convergent subsequence
(coordinatewise Bolzano–Weierstrass through the compact intervals
`[−1,1]`), and the limit is again a unit vector. -/
lemma unitDir_subseq_convergent {u : ℕ → ℝ²} (h : ∀ n, ‖u n‖ = 1) :
    ∃ w : ℝ², ‖w‖ = 1 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 w) := by
  have hb := unitDir_coords_bounded h
  -- coordinate 0 in [−1,1]: extract c₀, φ₀
  rcases (IsCompact.tendsto_subseq (s := Set.Icc (-1 : ℝ) 1) (x := fun n => (u n) 0)
    isCompact_Icc (fun n => (hb n).1)) with ⟨c₀, hc₀i, φ₀, hφ₀mono, hφ₀c⟩
  -- coordinate 1 along φ₀: extract c₁, φ₁
  rcases (IsCompact.tendsto_subseq (s := Set.Icc (-1 : ℝ) 1)
    (x := fun m => (u (φ₀ m)) 1)
    isCompact_Icc (fun m => (hb (φ₀ m)).2)) with ⟨c₁, hc₁i, φ₁, hφ₁mono, hφ₁c⟩
  let φ : ℕ → ℕ := fun m => φ₀ (φ₁ m)
  let w : ℝ² := !₂[c₀, c₁]
  have hφmono : StrictMono φ := by
    exact hφ₀mono.comp hφ₁mono
  -- coordinates of the composed subsequence converge
  have hw0 : w 0 = c₀ := by simp [w]
  have hw1 : w 1 = c₁ := by simp [w]
  have hc0 : Tendsto (fun m => (u (φ m)) 0) atTop (𝓝 (w 0)) := by
    have ht := hφ₀c.comp hφ₁mono.tendsto_atTop
    rw [hw0]
    exact ht
  have hc1 : Tendsto (fun m => (u (φ m)) 1) atTop (𝓝 (w 1)) := by
    rw [hw1]
    exact hφ₁c
  have htvec : Tendsto (fun m => u (φ m)) atTop (𝓝 w) := by
    exact tendsto_vector_of_coords hc0 hc1
  -- the limit is a unit vector (norm is continuous, sequence has norm 1)
  have hwn : ‖w‖ = 1 := by
    have htn := htvec.norm
    have hc : Tendsto (fun m : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have heq : (fun m : ℕ => ‖u (φ m)‖) =ᶠ[atTop] fun _ : ℕ => 1 := by
      filter_upwards with m
      exact h (φ m)
    have htn' : Tendsto (fun m : ℕ => (1 : ℝ)) atTop (𝓝 ‖w‖) := by
      exact htn.congr' heq
    exact tendsto_nhds_unique htn' hc
  exact ⟨w, hwn, φ, hφmono, htvec⟩

/-- **Ruling accumulation at a degenerate frontier point**: for a sequence
of `U`-points approaching `e`, a subsequence of ruling directions converges
to a unit direction (with the base points still approaching `e`). -/
theorem ruling_accumulation {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e : ℝ²} (_heS : e ∈ stripInterior)
    {q : ℕ → ℝ²} (hqS : ∀ n, q n ∈ stripInterior) (hqU : ∀ n, dN f (q n) ≠ 0)
    (hqe : Tendsto q atTop (𝓝 e)) :
    ∃ w : ℝ², ‖w‖ = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => unitKernelDir f (q (φ n))) atTop (𝓝 w) ∧
        Tendsto (fun n => q (φ n)) atTop (𝓝 e) := by
  -- directions are unit vectors, so a subsequence converges
  have hu : ∀ n, ‖unitKernelDir f (q n)‖ = 1 := uBend_dir_seq_unit hf ha hqS hqU
  rcases unitDir_subseq_convergent hu with ⟨w, hw1, φ, hφmono, hφw⟩
  refine ⟨w, hw1, φ, hφmono, ?_, ?_⟩
  · -- direction subsequence converges to w
    exact hφw
  · -- base points still converge to e
    exact hqe.comp hφmono.tendsto_atTop

/-! ## Frontier straightness: cluster directions keep the flat piece closed-sided -/

/-- **Cluster rulings keep the flat piece in the closed half-plane**: if the
rulings of a `U`-sequence `q n → e` converge to direction `w` and each
ruling has the flat piece `C` strictly on its positive side, then the limit
line through `e` in direction `w` has `C` in its closed positive half-plane
(side control passes to the limit by continuity of the signed functional). -/
theorem cluster_ruling_closed_halfplane {f : ℝ² → ℝ³}
    {C : Set ℝ²} (hsconn : IsPreconnected C) (hssub : C ⊆ stripInterior)
    (hflat : ∀ x ∈ C, dN f x = 0)
    {q : ℕ → ℝ²} (hqS : ∀ n, q n ∈ stripInterior) (hqU : ∀ n, dN f (q n) ≠ 0)
    {e w : ℝ²}
    (hqe : Tendsto q atTop (𝓝 e))
    (hdw : Tendsto (fun n => unitKernelDir f (q n)) atTop (𝓝 w))
    (hpos : ∀ n, ∀ z ∈ C, 0 < signedLineFunc (q n) (unitKernelDir f (q n)) z) :
    ∀ z ∈ C, 0 ≤ signedLineFunc e w z := by
  intro z hz
  -- the signed functional along the sequence converges to its limit value
  have hpair : Tendsto (fun n => (q n, unitKernelDir f (q n))) atTop (𝓝 (e, w)) := by
    simpa [nhds_prod_eq] using (Tendsto.prodMk hqe hdw)
  have hG : ContinuousAt (fun qw : ℝ² × ℝ² => signedLineFunc qw.1 qw.2 z) (e, w) := by
    unfold signedLineFunc
    fun_prop
  have hφz : Tendsto (fun n => signedLineFunc (q n) (unitKernelDir f (q n)) z) atTop
      (𝓝 (signedLineFunc e w z)) := by
    have hc := hG.tendsto.comp hpair
    exact hc
  by_contra hlt
  have hL : signedLineFunc e w z < 0 := lt_of_not_ge hlt
  -- converge to a negative limit: eventually the values are negative
  let L : ℝ := signedLineFunc e w z
  have hε : 0 < -L / 2 := div_pos (by linarith) (by norm_num)
  have hev : ∀ᶠ n in atTop, signedLineFunc (q n) (unitKernelDir f (q n)) z < 0 := by
    have hd := (Metric.tendsto_nhds.mp hφz) (-L / 2) hε
    filter_upwards [hd] with n hn
    have habs : |signedLineFunc (q n) (unitKernelDir f (q n)) z - L| < -L / 2 := by
      simpa [Real.dist_eq] using hn
    have hx := abs_lt.mp habs
    linarith
  have hne : ∀ᶠ n in atTop, ¬ 0 < signedLineFunc (q n) (unitKernelDir f (q n)) z := by
    filter_upwards [hev] with n hn
    exact not_lt.mpr (le_of_lt hn)
  have hposE : ∀ᶠ n in atTop, 0 < signedLineFunc (q n) (unitKernelDir f (q n)) z := by
    filter_upwards with n
    exact hpos n z hz
  have hcand := hposE.and hne
  rcases (eventually_atTop.mp hcand) with ⟨N, hN⟩
  have hh := hN (N + 1) (Nat.le_succ N)
  exact hh.2 hh.1

/-- **Pair of cluster directions with the same side data**: if two
`U`-sequences approach the same point `e` with ruling directions converging
to `w₁` resp. `w₂`, and every ruling of both sequences has the flat piece
`C` strictly on its positive side, then `C` lies in the closed cone cut out
by BOTH limit lines through `e` (in the directions `w₁`, `w₂`). -/
theorem cluster_pair_closed_cone {a : ℝ} {f : ℝ² → ℝ³}
    {C : Set ℝ²} (hsconn : IsPreconnected C) (hssub : C ⊆ stripInterior)
    (hflat : ∀ x ∈ C, dN f x = 0)
    {q₁ : ℕ → ℝ²} (hq₁S : ∀ n, q₁ n ∈ stripInterior) (hq₁U : ∀ n, dN f (q₁ n) ≠ 0)
    {q₂ : ℕ → ℝ²} (hq₂S : ∀ n, q₂ n ∈ stripInterior) (hq₂U : ∀ n, dN f (q₂ n) ≠ 0)
    {e w₁ w₂ : ℝ²}
    (hq₁e : Tendsto q₁ atTop (𝓝 e)) (hq₂e : Tendsto q₂ atTop (𝓝 e))
    (hd₁ : Tendsto (fun n => unitKernelDir f (q₁ n)) atTop (𝓝 w₁))
    (hd₂ : Tendsto (fun n => unitKernelDir f (q₂ n)) atTop (𝓝 w₂))
    (hpos₁ : ∀ n, ∀ z ∈ C, 0 < signedLineFunc (q₁ n) (unitKernelDir f (q₁ n)) z)
    (hpos₂ : ∀ n, ∀ z ∈ C, 0 < signedLineFunc (q₂ n) (unitKernelDir f (q₂ n)) z) :
    ∀ z ∈ C, 0 ≤ signedLineFunc e w₁ z ∧ 0 ≤ signedLineFunc e w₂ z := by
  intro z hz
  constructor
  · exact cluster_ruling_closed_halfplane (C := C) hsconn hssub hflat hq₁S hq₁U hq₁e hd₁ hpos₁ z hz
  · exact cluster_ruling_closed_halfplane (C := C) hsconn hssub hflat hq₂S hq₂U hq₂e hd₂ hpos₂ z hz

end Submission.PaperBand

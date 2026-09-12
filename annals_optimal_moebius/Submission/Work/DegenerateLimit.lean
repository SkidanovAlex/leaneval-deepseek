import Submission.Work.ChordSqueeze

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# FI-inside limits at a covered (frontier) height — first application of
the 2-D squeeze (WORK IN PROGRESS, GREEN helpers first)

For a flat component `C` with canonical heights `bw₁ < bw₂`, the leaf
through centreline height `y ∈ (bw₁,bw₂)` lies strictly inside `C`
(between the two frontier chords), hence strictly BELOW the upper
frontier chord `Γ₂` pointwise.  When `y → bw₂`, the 2-D squeeze
(`slope_tendsto_of_chord_below`) forces the leaf slope to the upper
frontier-chord slope — which is the spliced leaf slope at the covered
height `bw₂` (`leafSlope_eq_covFrontSlope`).  This is the component-side
half of the continuity at a covered height.

Helpers (all GREEN in this file):
* `leaf_line_height_eq` — the straight leaf of a `BendData` passes
  through `(1/2, centreHeight)` with slope `slope`: its height at
  `x0 ∈ (0,1)` equals `chordLine centreHeight slope x0`;
* `gen_line_height` — the blend chord (`genA t` to `genB t`) height at
  `x0 = u` equals `(genP t u).1`;
* the main theorem `leafSlope_tendsto_of_interval_to_upper` is the next
  step (once the inside-`betweenChord` bound is assembled from
  `blend_inside`).

Build: `lake build Submission.Work.DegenerateLimit` rc=0, zero sorry.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- The straight leaf of a `BendData` (the segment from `A` on `x0=0` to
`B` on `x0=1`) has height at `x0 ∈ (0,1)` equal to the reference line
through `(1/2, centreHeight)` with slope `slope`. -/
lemma leaf_line_height_eq (b : BendData) (x : ℝ) :
    (1 - x) * (b.A 1) + x * (b.B 1) = chordLine b.centreHeight b.slope x := by
  unfold chordLine BendData.slope BendData.centreHeight
  ring

/-- The blend chord from `genA t` to `genB t` has height at `x0 = u`
equal to the `genP t u` point's height. -/
lemma gen_line_height (α₁ β₁ α₂ β₂ t u : ℝ) :
    (1 - u) * ((genA α₁ β₁ α₂ β₂ t) 1) + u * ((genB α₁ β₁ α₂ β₂ t) 1) =
      (genP α₁ β₁ α₂ β₂ t u) 1 := by
  unfold genA genB genP sideH₁ sideH₂
  simp
  ring

/-- The endpoints of the blend at inverse parameter `t` lie on the two
boundary lines at the seam heights `(1−t)α₁ + tα₂` resp. `(1−t)β₁+tβ₂`
(by `genP_coord1` at `u = 0,1`). -/
lemma genA_height (α₁ β₁ α₂ β₂ t : ℝ) :
    (genA α₁ β₁ α₂ β₂ t) 1 = (1 - t) * α₁ + t * α₂ := by
  unfold genA genP sideH₁ sideH₂
  simp

/-- The right seam height of the blend at inverse parameter `t`. -/
lemma genB_height (α₁ β₁ α₂ β₂ t : ℝ) :
    (genB α₁ β₁ α₂ β₂ t) 1 = (1 - t) * β₁ + t * β₂ := by
  unfold genB genP sideH₁ sideH₂
  simp


/-- `sideH₁ α β u` is the chord line through the centreline point of
height `sideH₁ α β (1/2)` with slope `β − α`. -/
lemma sideH₁_eq_chordLine (α β u : ℝ) :
    sideH₁ α β u = chordLine (sideH₁ α β (1 / 2)) (β - α) u := by
  unfold chordLine sideH₁
  ring

/-- The component leaf equals the blend of the canonical `bw`-chord data. -/
lemma compLeaf_eq_blendBend {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) (y : ℝ) :
    compLeaf hf ha hp y = blendBend
      (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).1
      (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).2
      (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).1
      (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).2 y := by
  unfold compLeaf flatCompBend
  rfl

/-- The interior leaf of a component lies strictly BELOW the upper
frontier chord, pointwise on the open strip: for `y ∈ (bw₁,bw₂)` the leaf
line through `(1/2,y)` is at or below the upper frontier chord's line. -/
lemma compLeaf_line_below_upperChord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {y : ℝ}
    (hy : y ∈ Set.Ioo (bw₁ hf ha hp) (bw₂ hf ha hp)) :
    ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
      chordLine y ((compLeaf hf ha hp y).slope) u <
        chordLine (bw₂ hf ha hp)
          ((frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).2 -
           (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).1) u := by
  let d₁ : ℝ × ℝ := frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)
  let d₂ : ℝ × ℝ := frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)
  have hord : ∀ v : ℝ, v ∈ Set.Ioo 0 1 → sideH₁ d₁.1 d₁.2 v < sideH₁ d₂.1 d₂.2 v := by
    intro v hv
    simpa [d₁, d₂] using (sideH₁_lt_of_heights hf ha p hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)
      (bwlt hf ha hp) v hv)
  have h₁' : sideH₁ d₁.1 d₁.2 (1 / 2) = bw₁ hf ha hp := by
    simpa [d₁] using (sideH₁_data_half hf ha p hp (bwhh₁ hf ha hp))
  have h₂' : sideH₂ d₂.1 d₂.2 (1 / 2) = bw₂ hf ha hp := by
    rw [sideH₂_eq_sideH₁]
    simpa [d₂] using (sideH₁_data_half hf ha p hp (bwhh₂ hf ha hp))
  have hy' : y ∈ Set.Ioo (sideH₁ d₁.1 d₁.2 (1 / 2)) (sideH₂ d₂.1 d₂.2 (1 / 2)) := by
    rw [h₁', h₂']
    exact hy
  let t : ℝ := blendT d₁.1 d₁.2 d₂.1 d₂.2 y
  have ht : t ∈ Set.Ioo 0 1 := by
    dsimp [t]
    exact blendT_mem hord hy'
  intro u hu
  -- the leaf line value at u equals the blendP point height, which lies
  -- strictly below the upper chord (blend_inside + betweenChord)
  have hblend := blend_inside (α₁ := d₁.1) (β₁ := d₁.2) (α₂ := d₂.1) (β₂ := d₂.2)
    hord hy' hu
  have hpt : blendP d₁.1 d₁.2 d₂.1 d₂.2 y u ∈ betweenChord d₁.1 d₁.2 d₂.1 d₂.2 := hblend
  have hmem := (mem_betweenChord.mp hpt).2.2
  have hcoord0 : (blendP d₁.1 d₁.2 d₂.1 d₂.2 y u) 0 = u := by
    dsimp [blendP]
    rw [genP_coord0]
  have hbelow : (blendP d₁.1 d₁.2 d₂.1 d₂.2 y u) 1 < sideH₁ d₂.1 d₂.2 u := by
    rwa [hcoord0] at hmem
  -- connect leaf line value to the blend point height
  have hA : (compLeaf hf ha hp y).A 1 = (genA d₁.1 d₁.2 d₂.1 d₂.2 t) 1 := by
    rw [compLeaf_eq_blendBend hf ha hp y]
    dsimp [t, d₁, d₂]
    rw [blendBend_A_eq]
  have hB : (compLeaf hf ha hp y).B 1 = (genB d₁.1 d₁.2 d₂.1 d₂.2 t) 1 := by
    rw [compLeaf_eq_blendBend hf ha hp y]
    dsimp [t, d₁, d₂]
    rw [blendBend_B_eq]
  have hline := leaf_line_height_eq (compLeaf hf ha hp y) u
  have hc : (compLeaf hf ha hp y).centreHeight = y := by
    dsimp [compLeaf]
    exact flatCompBend_centre hf ha p hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp) (bwlt hf ha hp)
  -- value of leaf line at u:
  have hL1 : chordLine y ((compLeaf hf ha hp y).slope) u =
      (blendP d₁.1 d₁.2 d₂.1 d₂.2 y u) 1 := by
    calc
      chordLine y ((compLeaf hf ha hp y).slope) u
          = chordLine ((compLeaf hf ha hp y).centreHeight) ((compLeaf hf ha hp y).slope) u := by rw [hc]
      _ = (1 - u) * ((compLeaf hf ha hp y).A 1) + u * ((compLeaf hf ha hp y).B 1) := hline.symm
      _ = (1 - u) * ((genA d₁.1 d₁.2 d₂.1 d₂.2 t) 1) + u * ((genB d₁.1 d₁.2 d₂.1 d₂.2 t) 1) := by rw [hA, hB]
      _ = (genP d₁.1 d₁.2 d₂.1 d₂.2 t u) 1 := gen_line_height d₁.1 d₁.2 d₂.1 d₂.2 t u
      _ = (blendP d₁.1 d₁.2 d₂.1 d₂.2 y u) 1 := by
        dsimp [blendP, blendT, t]
  -- upper chord value:
  have hL2 : sideH₁ d₂.1 d₂.2 u =
      chordLine (bw₂ hf ha hp)
        ((frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).2 -
         (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).1) u := by
    have hh := sideH₁_eq_chordLine d₂.1 d₂.2 u
    have hmid : sideH₁ d₂.1 d₂.2 (1 / 2) = bw₂ hf ha hp := by
      simpa [d₂] using (sideH₁_data_half hf ha p hp (bwhh₂ hf ha hp))
    rw [hmid] at hh
    simpa [d₂] using hh
  calc
    chordLine y ((compLeaf hf ha hp y).slope) u
        = (blendP d₁.1 d₁.2 d₂.1 d₂.2 y u) 1 := hL1
    _ < sideH₁ d₂.1 d₂.2 u := hbelow
    _ = chordLine (bw₂ hf ha hp)
          ((frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).2 -
           (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).1) u := hL2



/-- The frontier-chord slope of a covered height computed from ANY
covering component `p` equals the `covFrontSlope` (which uses the
`Classical.choose` covering point): the covering component is unique. -/
lemma covFrontSlope_of_mem_frHeights {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {y₀ : ℝ}
    (hh : y₀ ∈ frHeights f p) :
    covFrontSlope hf ha (⟨p, hp, hh⟩ : CoveredHeight (f := f) y₀) =
      (frCompData hf ha p hp y₀ hh).2 - (frCompData hf ha p hp y₀ hh).1 := by
  let hc : CoveredHeight (f := f) y₀ := ⟨p, hp, hh⟩
  let p' : ℝ² := covPoint y₀ hc
  let hp' : p' ∈ interior (FlatSet f) := covPoint_hp (y := y₀) hc
  let hh' : y₀ ∈ frHeights f p' := covPoint_hh (y := y₀) hc
  have hq₁ : centrePoint y₀ ∈ frontier (flatComponent f p) := by
    have hz := (frSlicePoint_mem (p := p) (h := y₀) hh).1
    have hz' : frSlicePoint f p y₀ ∈ frontier (flatComponent f p) := (mem_frSlice_iff.mp hz).1
    simpa [frSlicePoint, centrePoint] using hz'
  have hq₂ : centrePoint y₀ ∈ frontier (flatComponent f p') := by
    have hz := (frSlicePoint_mem (p := p') (h := y₀) hh').1
    have hz' : frSlicePoint f p' y₀ ∈ frontier (flatComponent f p') := (mem_frSlice_iff.mp hz).1
    simpa [frSlicePoint, centrePoint] using hz'
  have hcomp : flatComponent f p = flatComponent f p' :=
    frontier_centre_unique_component hf ha hp hp' hq₁ hq₂
  have hdata : frCompData hf ha p' hp' y₀ hh' = frCompData hf ha p hp y₀ hh :=
    frCompData_of_equal_components hf ha hp' hp (hcomp.symm) hh' hh
  unfold covFrontSlope
  rw [hdata]

/-- **FI-inside convergence at the upper frontier**: interior leaves of a
flat component approaching its upper frontier height have slopes
converging to the spliced leaf slope at that (covered) height.  The leaves
lie strictly below the upper frontier chord, so the 2-D squeeze applies. -/
theorem leafSlope_tendsto_of_interval_to_upper {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f))
    {z : ℕ → ℝ} (hzI : ∀ n : ℕ, z n ∈ Set.Ioo (bw₁ hf ha hp) (bw₂ hf ha hp))
    (hz : Tendsto z atTop (𝓝 (bw₂ hf ha hp))) :
    Tendsto (fun n : ℕ => leafSlope hf ha (z n)) atTop
      (𝓝 (leafSlope hf ha (bw₂ hf ha hp))) := by
  let d₂ : ℝ × ℝ := frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)
  let m₂ : ℝ := d₂.2 - d₂.1
  have hzC : ∀ n : ℕ, centrePoint (z n) ∈ flatComponent f p := fun n =>
    (mem_centreInterval_iff hf ha hp (z n)).mpr (hzI n)
  have hslope : ∀ n : ℕ, leafSlope hf ha (z n) = (compLeaf hf ha (p := p) hp (z n)).slope := by
    intro n
    unfold leafSlope
    rw [spliceChord_eq_compLeaf_of_centre_mem hf ha (p := p) hp (y := z n) (hzC n)]
  have hbelow : ∀ (n : ℕ) (u : ℝ), u ∈ Set.Ioo 0 1 →
      chordLine (z n) ((compLeaf hf ha (p := p) hp (z n)).slope) u ≤
        chordLine (bw₂ hf ha hp) m₂ u := by
    intro n u hu
    have hlt := compLeaf_line_below_upperChord hf ha hp (hzI n) u hu
    have hm₂ : (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).2 -
        (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).1 = m₂ := by
      dsimp [m₂, d₂]
    rw [hm₂] at hlt
    exact le_of_lt hlt
  have hsq := slope_tendsto_of_chord_below (h₀ := bw₂ hf ha hp) (m₀ := m₂)
    (h := z) (m := fun n : ℕ => (compLeaf hf ha (p := p) hp (z n)).slope)
    hbelow hz
  have hval : leafSlope hf ha (bw₂ hf ha hp) = m₂ := by
    change leafSlope hf ha (bw₂ hf ha hp) =
      (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).2 -
        (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).1
    rw [leafSlope_eq_covFrontSlope hf ha
      (⟨p, hp, bwhh₂ hf ha hp⟩ : CoveredHeight (f := f) (bw₂ hf ha hp))]
    exact covFrontSlope_of_mem_frHeights hf ha hp (bwhh₂ hf ha hp)
  have hfun : (fun n : ℕ => leafSlope hf ha (z n)) =
      fun n : ℕ => (compLeaf hf ha (p := p) hp (z n)).slope := funext hslope
  rw [hfun, hval]
  exact hsq



/-- The interior leaf of a component lies strictly ABOVE the lower
frontier chord, pointwise on the open strip: for `y ∈ (bw₁,bw₂)` the leaf
line through `(1/2,y)` is at or above the lower frontier chord's line. -/
lemma compLeaf_line_above_lowerChord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {y : ℝ}
    (hy : y ∈ Set.Ioo (bw₁ hf ha hp) (bw₂ hf ha hp)) :
    ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
      chordLine (bw₁ hf ha hp)
          ((frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).2 -
           (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).1) u <
        chordLine y ((compLeaf hf ha hp y).slope) u := by
  let d₁ : ℝ × ℝ := frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)
  let d₂ : ℝ × ℝ := frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)
  have hord : ∀ v : ℝ, v ∈ Set.Ioo 0 1 → sideH₁ d₁.1 d₁.2 v < sideH₁ d₂.1 d₂.2 v := by
    intro v hv
    simpa [d₁, d₂] using (sideH₁_lt_of_heights hf ha p hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp)
      (bwlt hf ha hp) v hv)
  have h₁' : sideH₁ d₁.1 d₁.2 (1 / 2) = bw₁ hf ha hp := by
    simpa [d₁] using (sideH₁_data_half hf ha p hp (bwhh₁ hf ha hp))
  have h₂' : sideH₂ d₂.1 d₂.2 (1 / 2) = bw₂ hf ha hp := by
    rw [sideH₂_eq_sideH₁]
    simpa [d₂] using (sideH₁_data_half hf ha p hp (bwhh₂ hf ha hp))
  have hy' : y ∈ Set.Ioo (sideH₁ d₁.1 d₁.2 (1 / 2)) (sideH₂ d₂.1 d₂.2 (1 / 2)) := by
    rw [h₁', h₂']
    exact hy
  let t : ℝ := blendT d₁.1 d₁.2 d₂.1 d₂.2 y
  have ht : t ∈ Set.Ioo 0 1 := by
    dsimp [t]
    exact blendT_mem hord hy'
  intro u hu
  have hblend := blend_inside (α₁ := d₁.1) (β₁ := d₁.2) (α₂ := d₂.1) (β₂ := d₂.2)
    hord hy' hu
  have hmem := (mem_betweenChord.mp hblend).2.1
  have hcoord0 : (blendP d₁.1 d₁.2 d₂.1 d₂.2 y u) 0 = u := by
    dsimp [blendP]
    rw [genP_coord0]
  have habove : sideH₁ d₁.1 d₁.2 u < (blendP d₁.1 d₁.2 d₂.1 d₂.2 y u) 1 := by
    rwa [hcoord0] at hmem
  have hA : (compLeaf hf ha hp y).A 1 = (genA d₁.1 d₁.2 d₂.1 d₂.2 t) 1 := by
    rw [compLeaf_eq_blendBend hf ha hp y]
    dsimp [t, d₁, d₂]
    rw [blendBend_A_eq]
  have hB : (compLeaf hf ha hp y).B 1 = (genB d₁.1 d₁.2 d₂.1 d₂.2 t) 1 := by
    rw [compLeaf_eq_blendBend hf ha hp y]
    dsimp [t, d₁, d₂]
    rw [blendBend_B_eq]
  have hline := leaf_line_height_eq (compLeaf hf ha hp y) u
  have hc : (compLeaf hf ha hp y).centreHeight = y := by
    dsimp [compLeaf]
    exact flatCompBend_centre hf ha p hp (bwhh₁ hf ha hp) (bwhh₂ hf ha hp) (bwlt hf ha hp)
  have hL1 : chordLine y ((compLeaf hf ha hp y).slope) u =
      (blendP d₁.1 d₁.2 d₂.1 d₂.2 y u) 1 := by
    calc
      chordLine y ((compLeaf hf ha hp y).slope) u
          = chordLine ((compLeaf hf ha hp y).centreHeight) ((compLeaf hf ha hp y).slope) u := by rw [hc]
      _ = (1 - u) * ((compLeaf hf ha hp y).A 1) + u * ((compLeaf hf ha hp y).B 1) := hline.symm
      _ = (1 - u) * ((genA d₁.1 d₁.2 d₂.1 d₂.2 t) 1) + u * ((genB d₁.1 d₁.2 d₂.1 d₂.2 t) 1) := by rw [hA, hB]
      _ = (genP d₁.1 d₁.2 d₂.1 d₂.2 t u) 1 := gen_line_height d₁.1 d₁.2 d₂.1 d₂.2 t u
      _ = (blendP d₁.1 d₁.2 d₂.1 d₂.2 y u) 1 := by
        dsimp [blendP, blendT, t]
  have hL2 : sideH₁ d₁.1 d₁.2 u =
      chordLine (bw₁ hf ha hp)
        ((frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).2 -
         (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).1) u := by
    have hh := sideH₁_eq_chordLine d₁.1 d₁.2 u
    have hmid : sideH₁ d₁.1 d₁.2 (1 / 2) = bw₁ hf ha hp := by
      simpa [d₁] using (sideH₁_data_half hf ha p hp (bwhh₁ hf ha hp))
    rw [hmid] at hh
    simpa [d₁] using hh
  calc
    chordLine (bw₁ hf ha hp)
          ((frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).2 -
           (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).1) u
        = sideH₁ d₁.1 d₁.2 u := hL2.symm
    _ < (blendP d₁.1 d₁.2 d₂.1 d₂.2 y u) 1 := habove
    _ = chordLine y ((compLeaf hf ha hp y).slope) u := hL1.symm

/-- **FI-inside convergence at the lower frontier**: interior leaves of a
flat component approaching its lower frontier height have slopes
converging to the spliced leaf slope at that (covered) height. -/
theorem leafSlope_tendsto_of_interval_to_lower {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f))
    {z : ℕ → ℝ} (hzI : ∀ n : ℕ, z n ∈ Set.Ioo (bw₁ hf ha hp) (bw₂ hf ha hp))
    (hz : Tendsto z atTop (𝓝 (bw₁ hf ha hp))) :
    Tendsto (fun n : ℕ => leafSlope hf ha (z n)) atTop
      (𝓝 (leafSlope hf ha (bw₁ hf ha hp))) := by
  let d₁ : ℝ × ℝ := frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)
  let m₁ : ℝ := d₁.2 - d₁.1
  have hzC : ∀ n : ℕ, centrePoint (z n) ∈ flatComponent f p := fun n =>
    (mem_centreInterval_iff hf ha hp (z n)).mpr (hzI n)
  have hslope : ∀ n : ℕ, leafSlope hf ha (z n) = (compLeaf hf ha (p := p) hp (z n)).slope := by
    intro n
    unfold leafSlope
    rw [spliceChord_eq_compLeaf_of_centre_mem hf ha (p := p) hp (y := z n) (hzC n)]
  have habove : ∀ (n : ℕ) (u : ℝ), u ∈ Set.Ioo 0 1 →
      chordLine (bw₁ hf ha hp) m₁ u ≤
        chordLine (z n) ((compLeaf hf ha (p := p) hp (z n)).slope) u := by
    intro n u hu
    have hlt := compLeaf_line_above_lowerChord hf ha hp (hzI n) u hu
    have hm₁ : (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).2 -
        (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).1 = m₁ := by
      dsimp [m₁, d₁]
    rw [hm₁] at hlt
    exact le_of_lt hlt
  have hsq := slope_tendsto_of_chord_above (h₀ := bw₁ hf ha hp) (m₀ := m₁)
    (h := z) (m := fun n : ℕ => (compLeaf hf ha (p := p) hp (z n)).slope)
    habove hz
  have hval : leafSlope hf ha (bw₁ hf ha hp) = m₁ := by
    change leafSlope hf ha (bw₁ hf ha hp) =
      (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).2 -
        (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).1
    rw [leafSlope_eq_covFrontSlope hf ha
      (⟨p, hp, bwhh₁ hf ha hp⟩ : CoveredHeight (f := f) (bw₁ hf ha hp))]
    exact covFrontSlope_of_mem_frHeights hf ha hp (bwhh₁ hf ha hp)
  have hfun : (fun n : ℕ => leafSlope hf ha (z n)) =
      fun n : ℕ => (compLeaf hf ha (p := p) hp (z n)).slope := funext hslope
  rw [hfun, hval]
  exact hsq



/-- The spliced leaf slope at a component's UPPER frontier height equals
the upper frontier-chord slope (computed from the given component data). -/
lemma leafSlope_eq_upper_data {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    leafSlope hf ha (bw₂ hf ha hp) =
      (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).2 -
      (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).1 := by
  rw [leafSlope_eq_covFrontSlope hf ha
    (⟨p, hp, bwhh₂ hf ha hp⟩ : CoveredHeight (f := f) (bw₂ hf ha hp))]
  exact covFrontSlope_of_mem_frHeights hf ha hp (bwhh₂ hf ha hp)

/-- The spliced leaf slope at a component's LOWER frontier height equals
the lower frontier-chord slope (computed from the given component data). -/
lemma leafSlope_eq_lower_data {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    leafSlope hf ha (bw₁ hf ha hp) =
      (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).2 -
      (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).1 := by
  rw [leafSlope_eq_covFrontSlope hf ha
    (⟨p, hp, bwhh₁ hf ha hp⟩ : CoveredHeight (f := f) (bw₁ hf ha hp))]
  exact covFrontSlope_of_mem_frHeights hf ha hp (bwhh₁ hf ha hp)


end Submission

import Submission.Work.DegenerateLimit

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Outer-side convergence at covered heights (the `above(Γ₂)` half)

WORK IN PROGRESS — Stage 1 (the pure no-cross ordering lemma) GREEN.

The companion of `DegenerateLimit.lean`: sequences of FI / Cov heights
approaching a covered height `y₀` from the OUTER side of the flat frontier
chord `Γ₂` (heights `> y₀`).  Their leaves (or the covering components'
frontier chords) pass through centreline points `(1/2, zₙ)` with
`zₙ → y₀⁺`, are FULL strip chords that do not meet `Γ₂` (leaf interiors
are flat-interior, `Γ₂` points are flat NON-interior frontier points of
the other component), and lie strictly ABOVE `Γ₂` at `x0 = 1/2`; hence by
the no-cross ordering lemma they lie at-or-above `Γ₂` everywhere and the
2-D squeeze (`slope_tendsto_of_chord_above`) forces their slopes to the
frontier-chord slope.

* `line_no_cross_above` (GREEN) — pure: two strip-chord lines, the one
  through the higher centreline point, that never meet on `x0 ∈ (0,1)`,
  are ordered (higher) throughout the open strip (IVT);
* `leafPoint` / `compLeaf_point_mem_component` — the point of the leaf at
  `x0 = u`, and its membership in the component (between the frontier
  chords);
* (next) `fi_leaf_line_above` and the outer convergence theorems.

Build: `lake build Submission.Work.OuterSqueeze` rc=0, zero sorry.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- The chord line through the centreline point has height `h` at
`x0 = 1/2`. -/
lemma chordLine_at_half (h m : ℝ) : chordLine h m (1 / 2) = h := by
  unfold chordLine
  ring

/-- **Pure no-cross ordering**: if the chord `(z,m)` (through the
centreline point `(1/2,z)`) does not meet the chord `(y₀,m₂)` at any
`x0 ∈ (0,1)` and `z > y₀`, then the chord `(z,m)` lies strictly above
`(y₀,m₂)` throughout `x0 ∈ (0,1)`. -/
lemma line_no_cross_above {z y₀ m m₂ : ℝ} (hgt : y₀ < z)
    (hnocross : ∀ x : ℝ, x ∈ Set.Ioo 0 1 → chordLine z m x ≠ chordLine y₀ m₂ x) :
    ∀ x : ℝ, x ∈ Set.Ioo 0 1 → chordLine y₀ m₂ x < chordLine z m x := by
  intro x hx
  by_contra hnot
  have hle : chordLine z m x ≤ chordLine y₀ m₂ x := le_of_not_gt hnot
  have hne : chordLine z m x ≠ chordLine y₀ m₂ x := hnocross x hx
  have hlt : chordLine z m x < chordLine y₀ m₂ x := lt_of_le_of_ne hle hne
  let φ : ℝ → ℝ := fun t => chordLine z m t - chordLine y₀ m₂ t
  have hφcont : Continuous φ := by
    unfold φ chordLine
    fun_prop
  have hφmid : 0 < φ (1 / 2) := by
    dsimp [φ]
    rw [chordLine_at_half, chordLine_at_half]
    linarith
  have hφx : φ x < 0 := by
    dsimp [φ]
    unfold chordLine at hlt ⊢
    linarith
  by_cases hxm : x < 1 / 2
  · have hx01 : 0 < x := (Set.mem_Ioo.mp hx).1
    have hxS : x ∈ Set.Icc x (1 / 2) := (Set.mem_Icc).2 ⟨le_rfl, le_of_lt hxm⟩
    have hmidS : (1 / 2 : ℝ) ∈ Set.Icc x (1 / 2) := (Set.mem_Icc).2 ⟨le_of_lt hxm, le_rfl⟩
    have hφcontOn : ContinuousOn φ (Set.Icc x (1 / 2)) := hφcont.continuousOn
    have hzr : (0 : ℝ) ∈ Set.Icc (φ x) (φ (1 / 2)) := (Set.mem_Icc).2 ⟨le_of_lt hφx, le_of_lt hφmid⟩
    have hIVT : Set.Icc (φ x) (φ (1 / 2)) ⊆ φ '' Set.Icc x (1 / 2) :=
      IsPreconnected.intermediate_value isPreconnected_Icc hxS hmidS hφcontOn
    rcases hIVT hzr with ⟨c, hcS, hφc⟩
    have hc01 : c ∈ Set.Ioo 0 1 := by
      rw [Set.mem_Ioo]
      constructor
      · exact lt_of_lt_of_le hx01 (Set.mem_Icc.mp hcS).1
      · have : c ≤ 1 / 2 := (Set.mem_Icc.mp hcS).2
        linarith
    have hcross : chordLine z m c = chordLine y₀ m₂ c := by
      have hz : φ c = 0 := hφc
      dsimp [φ] at hz
      linarith
    exact hnocross c hc01 hcross
  · have hmidx : (1 / 2 : ℝ) ≤ x := le_of_not_gt hxm
    have hxlt1 : x < 1 := (Set.mem_Ioo.mp hx).2
    let ψ : ℝ → ℝ := fun t => -φ t
    have hψcont : Continuous ψ := by
      unfold ψ φ chordLine
      fun_prop
    have hψmid : ψ (1 / 2) < 0 := by
      dsimp [ψ, φ]
      rw [chordLine_at_half, chordLine_at_half]
      linarith
    have hψx : 0 < ψ x := by
      dsimp [ψ, φ]
      unfold chordLine at hlt ⊢
      linarith
    have hhalfS : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2) x := (Set.mem_Icc).2 ⟨le_rfl, hmidx⟩
    have hxS : x ∈ Set.Icc (1 / 2) x := (Set.mem_Icc).2 ⟨hmidx, le_rfl⟩
    have hψcontOn : ContinuousOn ψ (Set.Icc (1 / 2) x) := hψcont.continuousOn
    have hzr : (0 : ℝ) ∈ Set.Icc (ψ (1 / 2)) (ψ x) := (Set.mem_Icc).2 ⟨le_of_lt hψmid, le_of_lt hψx⟩
    have hIVT : Set.Icc (ψ (1 / 2)) (ψ x) ⊆ ψ '' Set.Icc (1 / 2) x :=
      IsPreconnected.intermediate_value isPreconnected_Icc hhalfS hxS hψcontOn
    rcases hIVT hzr with ⟨c, hcS, hψc⟩
    have hc01 : c ∈ Set.Ioo 0 1 := by
      rw [Set.mem_Ioo]
      constructor
      · have : 1 / 2 ≤ c := (Set.mem_Icc.mp hcS).1
        linarith
      · exact lt_of_le_of_lt (Set.mem_Icc.mp hcS).2 hxlt1
    have hcross : chordLine z m c = chordLine y₀ m₂ c := by
      have hz : -φ c = 0 := hψc
      have hφc : φ c = 0 := by linarith
      dsimp [φ] at hφc
      linarith
    exact hnocross c hc01 hcross


/-- The point of the straight leaf of a component leaf at `x0 = u`. -/
noncomputable def compLeafPoint {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) (y u : ℝ) : ℝ² :=
  !₂[u, chordLine y ((compLeaf hf ha hp y).slope) u]

/-- The side height of the LOWER frontier chord is the chord line through
its centreline point with the chord slope. -/
lemma sideH₁_lower_chord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) (u : ℝ) :
    sideH₁ (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).1
           (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).2 u =
      chordLine (bw₁ hf ha hp)
        ((frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).2 -
         (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).1) u := by
  have hl := sideH₁_eq_chordLine
    (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).1
    (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).2 u
  have hmid : sideH₁ (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).1
      (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).2 (1 / 2) = bw₁ hf ha hp :=
    sideH₁_data_half hf ha p hp (bwhh₁ hf ha hp)
  rw [hmid] at hl
  exact hl

/-- The side height of the UPPER frontier chord is the chord line through
its centreline point with the chord slope. -/
lemma sideH₁_upper_chord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) (u : ℝ) :
    sideH₁ (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).1
           (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).2 u =
      chordLine (bw₂ hf ha hp)
        ((frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).2 -
         (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).1) u := by
  have hl := sideH₁_eq_chordLine
    (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).1
    (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).2 u
  have hmid : sideH₁ (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).1
      (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).2 (1 / 2) = bw₂ hf ha hp :=
    sideH₁_data_half hf ha p hp (bwhh₂ hf ha hp)
  rw [hmid] at hl
  exact hl

/-- The leaf point at `x0 = u ∈ (0,1)` (interior centre height) lies
strictly INSIDE the component: it is in the between-region of the two
frontier chords (`compLeaf_line_above_lowerChord`/`_below_upperChord` +
`bwC`). -/
lemma compLeafPoint_mem_component {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {y u : ℝ}
    (hy : y ∈ Set.Ioo (bw₁ hf ha hp) (bw₂ hf ha hp)) (hu : u ∈ Set.Ioo 0 1) :
    compLeafPoint hf ha hp y u ∈ flatComponent f p := by
  have h1 := compLeaf_line_above_lowerChord hf ha hp hy u hu
  have h2 := compLeaf_line_below_upperChord hf ha hp hy u hu
  rw [bwC hf ha hp]
  rw [mem_betweenChord]
  constructor
  · dsimp [compLeafPoint]
    rw [stripInterior]
    constructor <;> simp [Set.mem_Ioo.mp hu]
  constructor
  · have hpt : (compLeafPoint hf ha hp y u) 1 = chordLine y ((compLeaf hf ha hp y).slope) u := by
      rfl
    rw [hpt]
    have hlow : sideH₁ (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).1
        (frCompData hf ha p hp (bw₁ hf ha hp) (bwhh₁ hf ha hp)).2 u <
        chordLine y ((compLeaf hf ha hp y).slope) u := by
      rw [← sideH₁_lower_chord hf ha hp u] at h1
      exact h1
    exact hlow
  · have hpt : (compLeafPoint hf ha hp y u) 1 = chordLine y ((compLeaf hf ha hp y).slope) u := by
      rfl
    rw [hpt]
    have hup : chordLine y ((compLeaf hf ha hp y).slope) u <
        sideH₁ (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).1
               (frCompData hf ha p hp (bw₂ hf ha hp) (bwhh₂ hf ha hp)).2 u := by
      rw [← sideH₁_upper_chord hf ha hp u] at h2
      exact h2
    exact hup


/-- **FI-outer bound**: at a flat-interior height `z` strictly above the
upper frontier height `bw₂` of a component `C₀`, the leaf through
`(1/2,z)` lies strictly ABOVE the frontier chord of `C₀` at `bw₂`,
pointwise on the open strip.  (The leaf is inside its own flat component
— flat-interior — while the frontier chord consists of flat NON-interior
points, so the two lines never meet; and at `x0 = 1/2` the leaf is above
by `z > bw₂`.) -/
lemma fi_leaf_above_frontier {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {z : ℝ}
    (hzF : IsFlatInterior f (centrePoint z)) (hgt : bw₂ hf ha hp₀ < z) :
    ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
      chordLine (bw₂ hf ha hp₀)
          ((frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).2 -
           (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).1) u <
        chordLine z (leafSlope hf ha z) u := by
  let p : ℝ² := centrePoint z
  let hp : p ∈ interior (FlatSet f) :=
    (IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior z)).mp hzF
  have hzC : centrePoint z ∈ flatComponent f p := mem_flatComponent hp
  have hzI : z ∈ Set.Ioo (bw₁ hf ha hp) (bw₂ hf ha hp) :=
    (mem_centreInterval_iff hf ha hp z).mp hzC
  have hslope : leafSlope hf ha z = (compLeaf hf ha (p := p) hp z).slope := by
    unfold leafSlope
    rw [spliceChord_eq_compLeaf_of_centre_mem hf ha (p := p) hp (y := z) hzC]
  apply line_no_cross_above (y₀ := bw₂ hf ha hp₀)
    (m := leafSlope hf ha z)
    (m₂ := (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).2 -
            (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).1) hgt
  intro u hu heq
  -- the shared value at x0 = u
  let P : ℝ² := compLeafPoint hf ha hp z u
  have hPin : P ∈ flatComponent f p := compLeafPoint_mem_component hf ha hp hzI hu
  have hPS : P ∈ stripInterior := by
    rw [stripInterior]
    dsimp [P, compLeafPoint]
    constructor <;> simp [Set.mem_Ioo.mp hu]
  have hPint : IsFlatInterior f P := by
    have hPi : P ∈ interior (FlatSet f) := flatComponent_subset_flatInterior f p hPin
    exact (IsFlatInterior_iff_mem_interior_FlatSet hPS).mpr hPi
  -- P lies on the frontier chord of C₀ at height bw₂
  have hP1 : P 1 = sideH₁
      (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).1
      (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).2 u := by
    dsimp [P]
    -- P1 = chordLine z (compLeaf slope) u = chordLine z (leafSlope z) u = chordLine bw₂ m₂ u = sideH₁ d₂ u
    have hc : chordLine z ((compLeaf hf ha (p := p) hp z).slope) u =
        chordLine (bw₂ hf ha hp₀)
          ((frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).2 -
           (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).1) u := by
      rw [← hslope]
      exact heq
    rw [sideH₁_upper_chord hf ha (p := p₀) hp₀ u]
    dsimp [P, compLeafPoint]
    exact hc
  have hPchord : P ∈ stripChord
      (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).1
      (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).2 := by
    rw [mem_stripChord]
    constructor
    · exact hPS
    · have h0 : P 0 = u := rfl
      rw [h0]
      exact hP1
  have hspec := frCompData_spec hf ha p₀ hp₀ (bwhh₂ hf ha hp₀)
  have hPAt : P ∈ frCompAt f p₀ (bw₂ hf ha hp₀) := by
    rw [← hspec] at hPchord
    exact hPchord
  have hPfront : P ∈ frontier (flatComponent f p₀) :=
    frCompAt_subset_frontier hPAt
  have hPni : ¬ IsFlatInterior f P :=
    flatComponent_frontier_not_flat_interior hPS hPfront
  exact hPni hPint



/-- **FI-outer convergence at the upper frontier**: flat-INTERIOR heights
strictly above the upper frontier height of a component, converging to it,
have leaf slopes converging to the spliced leaf slope at that (covered)
height.  (The leaves lie strictly above the frontier chord, so the 2-D
squeeze `slope_tendsto_of_chord_above` applies via
`fi_leaf_above_frontier`.) -/
theorem leafSlope_tendsto_fi_outer_upper {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f))
    {z : ℕ → ℝ} (hzF : ∀ n : ℕ, IsFlatInterior f (centrePoint (z n)))
    (hzgt : ∀ n : ℕ, bw₂ hf ha hp₀ < z n)
    (hz : Tendsto z atTop (𝓝 (bw₂ hf ha hp₀))) :
    Tendsto (fun n : ℕ => leafSlope hf ha (z n)) atTop
      (𝓝 (leafSlope hf ha (bw₂ hf ha hp₀))) := by
  let d₂ : ℝ × ℝ := frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)
  let m₂ : ℝ := d₂.2 - d₂.1
  have habove : ∀ (n : ℕ) (u : ℝ), u ∈ Set.Ioo 0 1 →
      chordLine (bw₂ hf ha hp₀) m₂ u ≤ chordLine (z n) (leafSlope hf ha (z n)) u := by
    intro n u hu
    have hlt := fi_leaf_above_frontier hf ha hp₀ (hzF n) (hzgt n) u hu
    have hm₂ : (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).2 -
        (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).1 = m₂ := by
      dsimp [m₂, d₂]
    rw [hm₂] at hlt
    exact le_of_lt hlt
  have hsq := slope_tendsto_of_chord_above (h₀ := bw₂ hf ha hp₀) (m₀ := m₂)
    (h := z) (m := fun n : ℕ => leafSlope hf ha (z n)) habove hz
  have hval : leafSlope hf ha (bw₂ hf ha hp₀) = m₂ := by
    change leafSlope hf ha (bw₂ hf ha hp₀) =
      (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).2 -
        (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).1
    rw [leafSlope_eq_covFrontSlope hf ha
      (⟨p₀, hp₀, bwhh₂ hf ha hp₀⟩ : CoveredHeight (f := f) (bw₂ hf ha hp₀))]
    exact covFrontSlope_of_mem_frHeights hf ha hp₀ (bwhh₂ hf ha hp₀)
  rw [hval]
  exact hsq



/-- **Cov-outer bound**: at a covered height `c` strictly above the upper
frontier height of a component `C₀`, the frontier chord through `(1/2,c)`
lies strictly ABOVE the frontier chord of `C₀` at `bw₂`, pointwise on the
open strip.  (The two frontier chords of distinct components cannot meet
inside the strip — a common point would be a common closure point of the
two components; and at `x0 = 1/2` the chord is above by `c > bw₂`.) -/
lemma cov_chord_above_frontier {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {c : ℝ}
    (hc : CoveredHeight (f := f) c) (hcgt : bw₂ hf ha hp₀ < c) :
    ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
      chordLine (bw₂ hf ha hp₀)
          ((frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).2 -
           (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).1) u <
        chordLine c (leafSlope hf ha c) u := by
  let p : ℝ² := covPoint c hc
  let hp : p ∈ interior (FlatSet f) := covPoint_hp (y := c) hc
  let hh : c ∈ frHeights f p := covPoint_hh (y := c) hc
  have hslope : leafSlope hf ha c = (frCompData hf ha p hp c hh).2 - (frCompData hf ha p hp c hh).1 := by
    rw [leafSlope_eq_covFrontSlope hf ha hc]
    unfold covFrontSlope
    dsimp [p, hp, hh]
  apply line_no_cross_above (y₀ := bw₂ hf ha hp₀)
    (m := leafSlope hf ha c)
    (m₂ := (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).2 -
            (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).1) hcgt
  intro u hu heq
  let Q : ℝ² := !₂[u, chordLine c (leafSlope hf ha c) u]
  have hQS : Q ∈ stripInterior := by
    rw [stripInterior]
    dsimp [Q]
    constructor <;> simp [Set.mem_Ioo.mp hu]
  -- Q is on the frontier of C (the component covering c)
  have hQ1p : Q 1 = sideH₁ (frCompData hf ha p hp c hh).1 (frCompData hf ha p hp c hh).2 u := by
    have hl := sideH₁_eq_chordLine (frCompData hf ha p hp c hh).1 (frCompData hf ha p hp c hh).2 u
    have hmid : sideH₁ (frCompData hf ha p hp c hh).1 (frCompData hf ha p hp c hh).2 (1 / 2) = c :=
      sideH₁_data_half hf ha p hp hh
    rw [hmid] at hl
    -- hl : sideH₁ data u = chordLine c (data.2 − data.1) u
    change chordLine c (leafSlope hf ha c) u = sideH₁
      (frCompData hf ha p hp c hh).1 (frCompData hf ha p hp c hh).2 u
    rw [hslope]
    exact hl.symm
  have hQchord : Q ∈ stripChord (frCompData hf ha p hp c hh).1 (frCompData hf ha p hp c hh).2 := by
    rw [mem_stripChord]
    constructor
    · exact hQS
    · have h0 : Q 0 = u := rfl
      rw [h0]
      exact hQ1p
  have hspecp := frCompData_spec hf ha p hp hh
  have hQAtp : Q ∈ frCompAt f p c := by
    rw [← hspecp] at hQchord
    exact hQchord
  have hQfrontp : Q ∈ frontier (flatComponent f p) := frCompAt_subset_frontier hQAtp
  have hQclp : Q ∈ closure (flatComponent f p) := frontier_subset_closure hQfrontp
  -- Q is on the frontier of C₀
  have hQ1₀ : Q 1 = sideH₁
      (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).1
      (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).2 u := by
    rw [sideH₁_upper_chord hf ha (p := p₀) hp₀ u]
    change chordLine c (leafSlope hf ha c) u = chordLine (bw₂ hf ha hp₀)
      ((frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).2 -
       (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).1) u
    exact heq
  have hQchord₀ : Q ∈ stripChord
      (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).1
      (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).2 := by
    rw [mem_stripChord]
    constructor
    · exact hQS
    · have h0 : Q 0 = u := rfl
      rw [h0]
      exact hQ1₀
  have hspec₀ := frCompData_spec hf ha p₀ hp₀ (bwhh₂ hf ha hp₀)
  have hQAt₀ : Q ∈ frCompAt f p₀ (bw₂ hf ha hp₀) := by
    rw [← hspec₀] at hQchord₀
    exact hQchord₀
  have hQfront₀ : Q ∈ frontier (flatComponent f p₀) := frCompAt_subset_frontier hQAt₀
  have hQcl₀ : Q ∈ closure (flatComponent f p₀) := frontier_subset_closure hQfront₀
  -- the components are distinct (c > bw₂ p₀ hp₀ is not a frontier height of C₀)
  have hne : flatComponent f p ≠ flatComponent f p₀ := by
    intro hEq
    have hfr : c ∈ frHeights f p₀ := by
      have hfrp : frHeights f p = frHeights f p₀ := frHeights_of_component_eq hEq
      rw [← hfrp]
      exact hh
    have hext : frHeights f p₀ = {x : ℝ | x = bw₁ hf ha hp₀ ∨ x = bw₂ hf ha hp₀} :=
      frHeights_eq_extremes hf ha hp₀ (bwhh₁ hf ha hp₀) (bwhh₂ hf ha hp₀)
        (bwlt hf ha hp₀) (bwC hf ha hp₀)
    rw [hext] at hfr
    rcases hfr with h₁ | h₂
    · have hbw := bwlt hf ha hp₀
      rw [h₁] at hcgt
      linarith
    · rw [h₂] at hcgt
      linarith
  exact flatComponents_no_common_stripInterior_closure hf ha hne Q hQS ⟨hQcl₀, hQclp⟩

/-- **Cov-outer convergence at the upper frontier**: covered heights
strictly above the upper frontier height of a component, converging to it,
have leaf slopes converging to the spliced leaf slope at that height. -/
theorem leafSlope_tendsto_cov_outer_upper {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f))
    {c : ℕ → ℝ} (hc : ∀ n : ℕ, CoveredHeight (f := f) (c n))
    (hcgt : ∀ n : ℕ, bw₂ hf ha hp₀ < c n)
    (hc₀ : Tendsto c atTop (𝓝 (bw₂ hf ha hp₀))) :
    Tendsto (fun n : ℕ => leafSlope hf ha (c n)) atTop
      (𝓝 (leafSlope hf ha (bw₂ hf ha hp₀))) := by
  let d₂ : ℝ × ℝ := frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)
  let m₂ : ℝ := d₂.2 - d₂.1
  have habove : ∀ (n : ℕ) (u : ℝ), u ∈ Set.Ioo 0 1 →
      chordLine (bw₂ hf ha hp₀) m₂ u ≤ chordLine (c n) (leafSlope hf ha (c n)) u := by
    intro n u hu
    have hlt := cov_chord_above_frontier hf ha hp₀ (hc n) (hcgt n) u hu
    have hm₂ : (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).2 -
        (frCompData hf ha p₀ hp₀ (bw₂ hf ha hp₀) (bwhh₂ hf ha hp₀)).1 = m₂ := by
      dsimp [m₂, d₂]
    rw [hm₂] at hlt
    exact le_of_lt hlt
  have hsq := slope_tendsto_of_chord_above (h₀ := bw₂ hf ha hp₀) (m₀ := m₂)
    (h := c) (m := fun n : ℕ => leafSlope hf ha (c n)) habove hc₀
  have hval : leafSlope hf ha (bw₂ hf ha hp₀) = m₂ := by
    dsimp [m₂, d₂]
    exact leafSlope_eq_upper_data hf ha hp₀
  rw [hval]
  exact hsq



/-- **Pure no-cross ordering (below version)**: if the chord `(z,m)`
through the LOWER centreline point does not meet the chord `(y₀,m₂)` on
`x0 ∈ (0,1)` and `z < y₀`, then the chord `(z,m)` lies strictly below
`(y₀,m₂)` throughout the open strip (swap the roles in
`line_no_cross_above`). -/
lemma line_no_cross_below {z y₀ m m₂ : ℝ} (hlt : z < y₀)
    (hnocross : ∀ x : ℝ, x ∈ Set.Ioo 0 1 → chordLine z m x ≠ chordLine y₀ m₂ x) :
    ∀ x : ℝ, x ∈ Set.Ioo 0 1 → chordLine z m x < chordLine y₀ m₂ x := by
  exact line_no_cross_above (z := y₀) (m := m₂) (y₀ := z) (m₂ := m) hlt
    (by intro x hx h; exact hnocross x hx h.symm)

/-- **FI-outer bound (below version)**: at a flat-interior height `z`
strictly BELOW the lower frontier height `bw₁` of a component `C₀`, the
leaf through `(1/2,z)` lies strictly BELOW the lower frontier chord of
`C₀`, pointwise on the open strip. -/
lemma fi_leaf_below_frontier {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {z : ℝ}
    (hzF : IsFlatInterior f (centrePoint z)) (hlt : z < bw₁ hf ha hp₀) :
    ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
      chordLine z (leafSlope hf ha z) u <
        chordLine (bw₁ hf ha hp₀)
          ((frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).2 -
           (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).1) u := by
  let p : ℝ² := centrePoint z
  let hp : p ∈ interior (FlatSet f) :=
    (IsFlatInterior_iff_mem_interior_FlatSet (centrePoint_mem_stripInterior z)).mp hzF
  have hzC : centrePoint z ∈ flatComponent f p := mem_flatComponent hp
  have hzI : z ∈ Set.Ioo (bw₁ hf ha hp) (bw₂ hf ha hp) :=
    (mem_centreInterval_iff hf ha hp z).mp hzC
  have hslope : leafSlope hf ha z = (compLeaf hf ha (p := p) hp z).slope := by
    unfold leafSlope
    rw [spliceChord_eq_compLeaf_of_centre_mem hf ha (p := p) hp (y := z) hzC]
  apply line_no_cross_below (y₀ := bw₁ hf ha hp₀)
    (m := leafSlope hf ha z)
    (m₂ := (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).2 -
            (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).1) hlt
  intro u hu heq
  let P : ℝ² := compLeafPoint hf ha hp z u
  have hPin : P ∈ flatComponent f p := compLeafPoint_mem_component hf ha hp hzI hu
  have hPS : P ∈ stripInterior := by
    rw [stripInterior]
    dsimp [P, compLeafPoint]
    constructor <;> simp [Set.mem_Ioo.mp hu]
  have hPint : IsFlatInterior f P := by
    have hPi : P ∈ interior (FlatSet f) := flatComponent_subset_flatInterior f p hPin
    exact (IsFlatInterior_iff_mem_interior_FlatSet hPS).mpr hPi
  have hP1 : P 1 = sideH₁
      (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).1
      (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).2 u := by
    have hc : chordLine z ((compLeaf hf ha (p := p) hp z).slope) u =
        chordLine (bw₁ hf ha hp₀)
          ((frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).2 -
           (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).1) u := by
      rw [← hslope]
      exact heq
    rw [sideH₁_lower_chord hf ha (p := p₀) hp₀ u]
    dsimp [P, compLeafPoint]
    exact hc
  have hPchord : P ∈ stripChord
      (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).1
      (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).2 := by
    rw [mem_stripChord]
    constructor
    · exact hPS
    · have h0 : P 0 = u := rfl
      rw [h0]
      exact hP1
  have hspec := frCompData_spec hf ha p₀ hp₀ (bwhh₁ hf ha hp₀)
  have hPAt : P ∈ frCompAt f p₀ (bw₁ hf ha hp₀) := by
    rw [← hspec] at hPchord
    exact hPchord
  have hPfront : P ∈ frontier (flatComponent f p₀) := frCompAt_subset_frontier hPAt
  have hPni : ¬ IsFlatInterior f P :=
    flatComponent_frontier_not_flat_interior hPS hPfront
  exact hPni hPint

/-- **FI-outer convergence at the LOWER frontier**: flat-INTERIOR heights
strictly below the lower frontier height of a component, converging to it,
have leaf slopes converging to the spliced leaf slope there. -/
theorem leafSlope_tendsto_fi_outer_lower {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f))
    {z : ℕ → ℝ} (hzF : ∀ n : ℕ, IsFlatInterior f (centrePoint (z n)))
    (hzlt : ∀ n : ℕ, z n < bw₁ hf ha hp₀)
    (hz : Tendsto z atTop (𝓝 (bw₁ hf ha hp₀))) :
    Tendsto (fun n : ℕ => leafSlope hf ha (z n)) atTop
      (𝓝 (leafSlope hf ha (bw₁ hf ha hp₀))) := by
  let d₁ : ℝ × ℝ := frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)
  let m₁ : ℝ := d₁.2 - d₁.1
  have hbelow : ∀ (n : ℕ) (u : ℝ), u ∈ Set.Ioo 0 1 →
      chordLine (z n) (leafSlope hf ha (z n)) u ≤ chordLine (bw₁ hf ha hp₀) m₁ u := by
    intro n u hu
    have hlt := fi_leaf_below_frontier hf ha hp₀ (hzF n) (hzlt n) u hu
    have hm₁ : (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).2 -
        (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).1 = m₁ := by
      dsimp [m₁, d₁]
    rw [hm₁] at hlt
    exact le_of_lt hlt
  have hsq := slope_tendsto_of_chord_below (h₀ := bw₁ hf ha hp₀) (m₀ := m₁)
    (h := z) (m := fun n : ℕ => leafSlope hf ha (z n)) hbelow hz
  have hval : leafSlope hf ha (bw₁ hf ha hp₀) = m₁ := by
    dsimp [m₁, d₁]
    exact leafSlope_eq_lower_data hf ha hp₀
  rw [hval]
  exact hsq


/-- **Cov-outer bound (BELOW version)**: at a covered height `c` strictly above the upper
frontier height of a component `C₀`, the frontier chord through `(1/2,c)`
lies strictly BELOW the frontier chord of `C₀` at `bw₁`, pointwise on the
open strip.  (The two frontier chords of distinct components cannot meet
inside the strip — a common point would be a common closure point of the
two components; and at `x0 = 1/2` the chord is below by `c < bw₁`.) -/
lemma cov_chord_below_frontier {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f)) {c : ℝ}
    (hc : CoveredHeight (f := f) c) (hclt : c < bw₁ hf ha hp₀) :
    ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
      chordLine c (leafSlope hf ha c) u <
        chordLine (bw₁ hf ha hp₀)
          ((frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).2 -
           (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).1) u := by
  let p : ℝ² := covPoint c hc
  let hp : p ∈ interior (FlatSet f) := covPoint_hp (y := c) hc
  let hh : c ∈ frHeights f p := covPoint_hh (y := c) hc
  have hslope : leafSlope hf ha c = (frCompData hf ha p hp c hh).2 - (frCompData hf ha p hp c hh).1 := by
    rw [leafSlope_eq_covFrontSlope hf ha hc]
    unfold covFrontSlope
    dsimp [p, hp, hh]
  apply line_no_cross_below (y₀ := bw₁ hf ha hp₀)
    (m := leafSlope hf ha c)
    (m₂ := (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).2 -
            (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).1) hclt
  intro u hu heq
  let Q : ℝ² := !₂[u, chordLine c (leafSlope hf ha c) u]
  have hQS : Q ∈ stripInterior := by
    rw [stripInterior]
    dsimp [Q]
    constructor <;> simp [Set.mem_Ioo.mp hu]
  -- Q is on the frontier of C (the component covering c)
  have hQ1p : Q 1 = sideH₁ (frCompData hf ha p hp c hh).1 (frCompData hf ha p hp c hh).2 u := by
    have hl := sideH₁_eq_chordLine (frCompData hf ha p hp c hh).1 (frCompData hf ha p hp c hh).2 u
    have hmid : sideH₁ (frCompData hf ha p hp c hh).1 (frCompData hf ha p hp c hh).2 (1 / 2) = c :=
      sideH₁_data_half hf ha p hp hh
    rw [hmid] at hl
    -- hl : sideH₁ data u = chordLine c (data.2 − data.1) u
    change chordLine c (leafSlope hf ha c) u = sideH₁
      (frCompData hf ha p hp c hh).1 (frCompData hf ha p hp c hh).2 u
    rw [hslope]
    exact hl.symm
  have hQchord : Q ∈ stripChord (frCompData hf ha p hp c hh).1 (frCompData hf ha p hp c hh).2 := by
    rw [mem_stripChord]
    constructor
    · exact hQS
    · have h0 : Q 0 = u := rfl
      rw [h0]
      exact hQ1p
  have hspecp := frCompData_spec hf ha p hp hh
  have hQAtp : Q ∈ frCompAt f p c := by
    rw [← hspecp] at hQchord
    exact hQchord
  have hQfrontp : Q ∈ frontier (flatComponent f p) := frCompAt_subset_frontier hQAtp
  have hQclp : Q ∈ closure (flatComponent f p) := frontier_subset_closure hQfrontp
  -- Q is on the frontier of C₀
  have hQ1₀ : Q 1 = sideH₁
      (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).1
      (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).2 u := by
    rw [sideH₁_lower_chord hf ha (p := p₀) hp₀ u]
    change chordLine c (leafSlope hf ha c) u = chordLine (bw₁ hf ha hp₀)
      ((frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).2 -
       (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).1) u
    exact heq
  have hQchord₀ : Q ∈ stripChord
      (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).1
      (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).2 := by
    rw [mem_stripChord]
    constructor
    · exact hQS
    · have h0 : Q 0 = u := rfl
      rw [h0]
      exact hQ1₀
  have hspec₀ := frCompData_spec hf ha p₀ hp₀ (bwhh₁ hf ha hp₀)
  have hQAt₀ : Q ∈ frCompAt f p₀ (bw₁ hf ha hp₀) := by
    rw [← hspec₀] at hQchord₀
    exact hQchord₀
  have hQfront₀ : Q ∈ frontier (flatComponent f p₀) := frCompAt_subset_frontier hQAt₀
  have hQcl₀ : Q ∈ closure (flatComponent f p₀) := frontier_subset_closure hQfront₀
  -- the components are distinct (c > bw₂ p₀ hp₀ is not a frontier height of C₀)
  have hne : flatComponent f p ≠ flatComponent f p₀ := by
    intro hEq
    have hfr : c ∈ frHeights f p₀ := by
      have hfrp : frHeights f p = frHeights f p₀ := frHeights_of_component_eq hEq
      rw [← hfrp]
      exact hh
    have hext : frHeights f p₀ = {x : ℝ | x = bw₁ hf ha hp₀ ∨ x = bw₂ hf ha hp₀} :=
      frHeights_eq_extremes hf ha hp₀ (bwhh₁ hf ha hp₀) (bwhh₂ hf ha hp₀)
        (bwlt hf ha hp₀) (bwC hf ha hp₀)
    rw [hext] at hfr
    rcases hfr with h₁ | h₂
    · have hbw := bwlt hf ha hp₀
      rw [h₁] at hclt
      linarith
    · rw [h₂] at hclt
      have hbw := bwlt hf ha hp₀
      linarith
  exact flatComponents_no_common_stripInterior_closure hf ha hne Q hQS ⟨hQcl₀, hQclp⟩

/-- **Cov-outer convergence at the LOWER frontier**: covered heights
strictly above the upper frontier height of a component, converging to it,
have leaf slopes converging to the spliced leaf slope at that height. -/
theorem leafSlope_tendsto_cov_outer_lower {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₀ : ℝ²} (hp₀ : p₀ ∈ interior (FlatSet f))
    {c : ℕ → ℝ} (hc : ∀ n : ℕ, CoveredHeight (f := f) (c n))
    (hclt : ∀ n : ℕ, c n < bw₁ hf ha hp₀)
    (hc₀ : Tendsto c atTop (𝓝 (bw₁ hf ha hp₀))) :
    Tendsto (fun n : ℕ => leafSlope hf ha (c n)) atTop
      (𝓝 (leafSlope hf ha (bw₁ hf ha hp₀))) := by
  let d₂ : ℝ × ℝ := frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)
  let m₂ : ℝ := d₂.2 - d₂.1
  have hbelow : ∀ (n : ℕ) (u : ℝ), u ∈ Set.Ioo 0 1 →
      chordLine (c n) (leafSlope hf ha (c n)) u ≤ chordLine (bw₁ hf ha hp₀) m₂ u := by
    intro n u hu
    have hlt := cov_chord_below_frontier hf ha hp₀ (hc n) (hclt n) u hu
    have hm₂ : (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).2 -
        (frCompData hf ha p₀ hp₀ (bw₁ hf ha hp₀) (bwhh₁ hf ha hp₀)).1 = m₂ := by
      dsimp [m₂, d₂]
    rw [hm₂] at hlt
    exact le_of_lt hlt
  have hsq := slope_tendsto_of_chord_below (h₀ := bw₁ hf ha hp₀) (m₀ := m₂)
    (h := c) (m := fun n : ℕ => leafSlope hf ha (c n)) hbelow hc₀
  have hval : leafSlope hf ha (bw₁ hf ha hp₀) = m₂ := by
    dsimp [m₂, d₂]
    exact leafSlope_eq_lower_data hf ha hp₀
  rw [hval]
  exact hsq


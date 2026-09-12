import Submission.Work.SpliceLeaves

open OptimalMoebius Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Per-component leaf data from `flatComponent_between_frontier`

For a flat component `C := flatComponent f p` (`p` flat-interior),
`flatComponent_between_frontier` gives two frontier chord heights
`h₁ < h₂` with `C = betweenChord (data h₁) (data h₂)`.  This file
packages that into the per-component leaf layer:

* `flatComponent_between_with_data` — the between representation with
  the chosen chord data;
* `centreline_of_between` (+ `flatComponent_centreline`) — the centreline
  heights of `C` are exactly `(h₁, h₂)`: `(1/2,y) ∈ C ↔ y ∈ (h₁,h₂)`;
* **`flatComponent_blend_leaves`** — the component leaves: the blended
  chord `blendP (data h₁) (data h₂) y u` at centre height `y ∈ (h₁,h₂)`,
  `u ∈ (0,1)` lies inside `C`; the left and right endpoint HEIGHTS
  `(genA (data) (blendT y))1` and `(genB …)1` are continuous in `y`
  (`continuous_blendA1`/`continuous_blendB1` of the splice file).

Build: `lake build Submission.Work.ComponentLeaves` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- The between-region representation of a flat component with its chord
data made explicit. -/
theorem flatComponent_between_with_data {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    ∃ h₁ h₂ : ℝ, ∃ hh₁ : h₁ ∈ frHeights f p, ∃ hh₂ : h₂ ∈ frHeights f p,
      h₁ < h₂ ∧
      flatComponent f p =
        betweenChord (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
                     (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 := by
  rcases flatComponent_between_frontier hf ha hp with ⟨h₁, h₂, hh₁, hh₂, hlt, hh₁', hh₂', hC⟩
  exact ⟨h₁, h₂, hh₁, hh₂, hlt, hC⟩

/-- The centreline of a between-region of pointwise-ordered chords: its
heights are exactly `(sideH₁ α₁β₁ (1/2), sideH₁ α₂β₂ (1/2))`. -/
theorem centreline_of_between {α₁ β₁ α₂ β₂ : ℝ}
    (hord : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ α₁ β₁ u < sideH₁ α₂ β₂ u) :
    {y : ℝ | (!₂[1 / 2, y] : ℝ²) ∈ betweenChord α₁ β₁ α₂ β₂} =
      Set.Ioo (sideH₁ α₁ β₁ (1 / 2)) (sideH₁ α₂ β₂ (1 / 2)) := by
  ext y
  change ((!₂[1 / 2, y] : ℝ²) ∈ betweenChord α₁ β₁ α₂ β₂) ↔
    sideH₁ α₁ β₁ (1 / 2) < y ∧ y < sideH₁ α₂ β₂ (1 / 2)
  rw [mem_betweenChord]
  constructor
  · intro hy
    rcases hy with ⟨hS, hlt₁, hlt₂⟩
    have hc0 : (!₂[1 / 2, y] : ℝ²) 0 = 1 / 2 := by simp
    have hc1 : (!₂[1 / 2, y] : ℝ²) 1 = y := by simp
    rw [hc0, hc1] at hlt₁ hlt₂
    constructor <;> nlinarith
  · intro hy
    rcases hy with ⟨hy1, hy2⟩
    have hS : (!₂[1 / 2, y] : ℝ²) ∈ stripInterior := by
      rw [stripInterior]
      constructor <;> simp <;> norm_num
    constructor
    · exact hS
    constructor
    · simpa using hy1
    · simpa using hy2

/-- The centreline heights of a flat component are the open interval
between its two frontier chord heights `h₁` and `h₂`. -/
theorem flatComponent_centreline {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    ∃ h₁ h₂ : ℝ, h₁ < h₂ ∧
      (∀ y : ℝ, (!₂[1 / 2, y] : ℝ²) ∈ flatComponent f p ↔ y ∈ Set.Ioo h₁ h₂) := by
  rcases flatComponent_between_with_data hf ha hp with
    ⟨h₁, h₂, hh₁, hh₂, hlt, hC⟩
  refine ⟨h₁, h₂, hlt, ?_⟩
  intro y
  have hord : ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
      sideH₁ (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 u <
      sideH₁ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 u :=
    sideH₁_lt_of_heights hf ha p hp hh₁ hh₂ hlt
  have hinterval : {y : ℝ | (!₂[1 / 2, y] : ℝ²) ∈ betweenChord
        (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
        (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2} =
      Set.Ioo (sideH₁ (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 (1 / 2))
               (sideH₁ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 (1 / 2)) :=
    centreline_of_between hord
  have hh₁' : sideH₁ (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 (1 / 2) = h₁ :=
    sideH₁_data_half hf ha p hp hh₁
  have hh₂' : sideH₁ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 (1 / 2) = h₂ :=
    sideH₁_data_half hf ha p hp hh₂
  rw [hC]
  have hset : ({y : ℝ | (!₂[1 / 2, y] : ℝ²) ∈
      betweenChord (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
                   (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2} : Set ℝ) =
      Set.Ioo h₁ h₂ := by
    rw [hinterval]
    rw [hh₁', hh₂']
  rw [← hset]
  rfl

/-- **Per-component leaves with continuous endpoints**: the flat component
`C` is the between region of two frontier chords at heights `h₁<h₂`; for
every centre height `y ∈ (h₁,h₂)` and segment parameter `u ∈ (0,1)` the
blended chord lies inside `C`, and the endpoint heights of the leaves are
continuous functions of the centre height. -/
theorem flatComponent_blend_leaves {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) :
    ∃ h₁ h₂ : ℝ, ∃ hh₁ : h₁ ∈ frHeights f p, ∃ hh₂ : h₂ ∈ frHeights f p,
      h₁ < h₂ ∧
      (∀ y : ℝ, (!₂[1 / 2, y] : ℝ²) ∈ flatComponent f p ↔ y ∈ Set.Ioo h₁ h₂) ∧
      (∀ y u : ℝ, y ∈ Set.Ioo h₁ h₂ → u ∈ Set.Ioo 0 1 →
        blendP (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
               (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 y u ∈
          flatComponent f p) ∧
      Continuous (fun y : ℝ => (genA (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
          (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 (blendT
            (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
            (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 y)) 1) ∧
      Continuous (fun y : ℝ => (genB (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
          (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 (blendT
            (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
            (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 y)) 1) := by
  rcases flatComponent_between_with_data hf ha hp with
    ⟨h₁, h₂, hh₁, hh₂, hlt, hC⟩
  refine ⟨h₁, h₂, hh₁, hh₂, hlt, ?_, ?_, ?_, ?_⟩
  · -- centreline
    have hcl : ∃ h₁' h₂' : ℝ, h₁' < h₂' ∧
        (∀ y : ℝ, (!₂[1 / 2, y] : ℝ²) ∈ flatComponent f p ↔ y ∈ Set.Ioo h₁' h₂') :=
      flatComponent_centreline hf ha hp
    rcases hcl with ⟨h₁', h₂', hlt', hint'⟩
    -- the heights must be the chosen ones: by the between representation
    have hord : ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
        sideH₁ (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 u <
        sideH₁ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 u :=
      sideH₁_lt_of_heights hf ha p hp hh₁ hh₂ hlt
    have hinterval : {y : ℝ | (!₂[1 / 2, y] : ℝ²) ∈ betweenChord
          (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
          (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2} =
        Set.Ioo (sideH₁ (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 (1 / 2))
                 (sideH₁ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 (1 / 2)) :=
      centreline_of_between hord
    have hh₁' : sideH₁ (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 (1 / 2) = h₁ :=
      sideH₁_data_half hf ha p hp hh₁
    have hh₂' : sideH₁ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 (1 / 2) = h₂ :=
      sideH₁_data_half hf ha p hp hh₂
    intro y
    rw [hC]
    have hset : ({y : ℝ | (!₂[1 / 2, y] : ℝ²) ∈
        betweenChord (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2
                     (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2} : Set ℝ) =
        Set.Ioo h₁ h₂ := by
      rw [hinterval]
      rw [hh₁', hh₂']
    rw [← hset]
    rfl
  · -- leaves inside C
    have hord : ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
        sideH₁ (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 u <
        sideH₁ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 u :=
      sideH₁_lt_of_heights hf ha p hp hh₁ hh₂ hlt
    have hord2 : ∀ u : ℝ, u ∈ Set.Ioo 0 1 →
        sideH₁ (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 u <
        sideH₂ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 u := by
      intro u hu
      rw [sideH₂_eq_sideH₁]
      exact hord u hu
    intro y u hy hu
    have hy' : y ∈ Set.Ioo (sideH₁ (frCompData hf ha p hp h₁ hh₁).1 (frCompData hf ha p hp h₁ hh₁).2 (1 / 2))
        (sideH₂ (frCompData hf ha p hp h₂ hh₂).1 (frCompData hf ha p hp h₂ hh₂).2 (1 / 2)) := by
      rw [Set.mem_Ioo] at hy ⊢
      rw [sideH₁_data_half hf ha p hp hh₁]
      rw [sideH₂_eq_sideH₁]
      rw [sideH₁_data_half hf ha p hp hh₂]
      exact hy
    have hin := blend_inside (hord := hord2) hy' hu
    rw [hC]
    exact hin
  · -- continuity A1
    exact continuous_blendA1 (α₁ := (frCompData hf ha p hp h₁ hh₁).1)
      (β₁ := (frCompData hf ha p hp h₁ hh₁).2)
      (α₂ := (frCompData hf ha p hp h₂ hh₂).1)
      (β₂ := (frCompData hf ha p hp h₂ hh₂).2)
  · -- continuity B1
    exact continuous_blendB1 (α₁ := (frCompData hf ha p hp h₁ hh₁).1)
      (β₁ := (frCompData hf ha p hp h₁ hh₁).2)
      (α₂ := (frCompData hf ha p hp h₂ hh₂).1)
      (β₂ := (frCompData hf ha p hp h₂ hh₂).2)


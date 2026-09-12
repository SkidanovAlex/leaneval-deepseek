import Submission.Work.RegionBetween
import Submission.Work.FlatComp

open OptimalMoebius Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# T1-ii Layers 4–5 (strict case): leaf family of a strict between region

For the STRICT trapezoid case — two pointwise-ordered bounding chords
`stripChord α₁β₁` (below), `stripChord α₂β₂` (above) with strict
endpoint inequalities `α₁<α₂`, `β₁<β₂` — the between region is exactly
the `FlatSideData.region` of the component-level template (`FlatComp`),
so all the template leaf machinery (chords through the centreline
heights `(c₁,c₂)`, leaves inside the region, endpoints on `x0=0` /
`x0=1`, continuity, limits) applies verbatim.

Concretely this file proves:
* `betweenChord_eq_region` / `region_eq_betweenChord` — the two
  definitions of the open between region agree;
* `centre_interval_eq` — the centreline heights of the region are exactly
  `(c₁, c₂)` with `cᵢ = sideH₁ αᵢβᵢ (1/2)`;
* **`between_leaf_inside`** — every template leaf through a centreline
  height of the region lies inside it: for `y ∈ (c₁,c₂)` and
  `u ∈ (0,1)`, `FlatSideData.leafP D y u ∈ betweenChord α₁β₁ α₂β₂`, with the
  endpoints `leafA y` on `x0 = 0` and `leafB y` on `x0 = 1` — the leaf
  connects the two boundary components of the strip inside the region.

The wedge/fan (non-strict) case is left to a later local variant.
Build: `lake build Submission.Work.StrictTrapezoid` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- `sideH₂` agrees with `sideH₁` (both are the affine height
`(1−x)·α + x·β`). -/
lemma sideH₂_eq_sideH₁ (α β x : ℝ) : sideH₂ α β x = sideH₁ α β x := by
  dsimp [sideH₁, sideH₂]

/-- Membership in the open strip is the coordinate pair. -/
lemma mem_stripInterior_iff_coords {x : ℝ²} :
    x ∈ stripInterior ↔ 0 < x 0 ∧ x 0 < 1 := by
  rfl

/-- The between-region of two chords agrees with the `FlatSideData`
region of the same chord data. -/
lemma betweenChord_eq_region {α₁ β₁ α₂ β₂ : ℝ} (hα : α₁ < α₂) (hβ : β₁ < β₂) :
    betweenChord α₁ β₁ α₂ β₂ =
      FlatSideData.region ⟨α₁, β₁, α₂, β₂, hα, hβ⟩ := by
  ext x
  rw [mem_betweenChord, mem_stripInterior_iff_coords, FlatSideData.region]
  simp [FlatSideData.line₁, FlatSideData.line₂, sideH₂_eq_sideH₁]
  tauto

/-- The `FlatSideData` region is the between-region of its side lines. -/
lemma region_eq_betweenChord {α₁ β₁ α₂ β₂ : ℝ} (hα : α₁ < α₂) (hβ : β₁ < β₂) :
    FlatSideData.region ⟨α₁, β₁, α₂, β₂, hα, hβ⟩ = betweenChord α₁ β₁ α₂ β₂ := by
  rw [betweenChord_eq_region hα hβ]

/-- The centre heights of the strict between region. -/
lemma c₁_eq_sideH {α₁ β₁ α₂ β₂ : ℝ} (hα : α₁ < α₂) (hβ : β₁ < β₂) :
    FlatSideData.c₁ ⟨α₁, β₁, α₂, β₂, hα, hβ⟩ = sideH₁ α₁ β₁ (1 / 2) := by
  rfl

lemma c₂_eq_sideH {α₁ β₁ α₂ β₂ : ℝ} (hα : α₁ < α₂) (hβ : β₁ < β₂) :
    FlatSideData.c₂ ⟨α₁, β₁, α₂, β₂, hα, hβ⟩ = sideH₁ α₂ β₂ (1 / 2) := by
  rfl

/-- **Centre interval**: the centreline heights of the strict between
region are exactly `(c₁, c₂)` with `cᵢ = sideH₁ αᵢβᵢ (1/2)`. -/
theorem centre_interval_eq {α₁ β₁ α₂ β₂ : ℝ} (hα : α₁ < α₂) (hβ : β₁ < β₂) :
    {y : ℝ | (!₂[1 / 2, y] : ℝ²) ∈ betweenChord α₁ β₁ α₂ β₂} =
      Set.Ioo (sideH₁ α₁ β₁ (1 / 2)) (sideH₁ α₂ β₂ (1 / 2)) := by
  ext y
  change ((!₂[1 / 2, y] : ℝ²) ∈ betweenChord α₁ β₁ α₂ β₂) ↔ y ∈ Set.Ioo (sideH₁ α₁ β₁ (1 / 2)) (sideH₁ α₂ β₂ (1 / 2))
  rw [mem_betweenChord]
  rw [Set.mem_Ioo]
  constructor
  · intro hy
    rcases hy with ⟨hS, hlt₁, hlt₂⟩
    have hc0 : (!₂[1 / 2, y] : ℝ²) 0 = 1 / 2 := by simp
    have hc1 : (!₂[1 / 2, y] : ℝ²) 1 = y := by simp
    constructor
    · rw [hc0, hc1] at hlt₁
      exact hlt₁
    · rw [hc0, hc1] at hlt₂
      exact hlt₂
  · intro hy
    rcases hy with ⟨h₁lt, hlt₂⟩
    have hS : (!₂[1 / 2, y] : ℝ²) ∈ stripInterior := by
      rw [stripInterior]
      constructor <;> simp <;> norm_num
    constructor
    · exact hS
    constructor
    · simp
      simpa using h₁lt
    · simp
      simpa using hlt₂

/-- **Every template leaf through a centreline height of the strict
between region lies inside it.**  For `y ∈ (c₁,c₂)` and `u ∈ (0,1)`
(with `cᵢ = sideH₁ αᵢβᵢ (1/2)`) the leaf point `FlatSideData.leafP D y u`
is in `betweenChord α₁β₁ α₂β₂`. -/
theorem between_leaf_inside {α₁ β₁ α₂ β₂ : ℝ} (hα : α₁ < α₂) (hβ : β₁ < β₂)
    {y u : ℝ}
    (hy : y ∈ Set.Ioo (sideH₁ α₁ β₁ (1 / 2)) (sideH₁ α₂ β₂ (1 / 2)))
    (hu : u ∈ Set.Ioo 0 1) :
    FlatSideData.leafP (D := ⟨α₁, β₁, α₂, β₂, hα, hβ⟩) y u ∈ betweenChord α₁ β₁ α₂ β₂ := by
  let D : FlatSideData := ⟨α₁, β₁, α₂, β₂, hα, hβ⟩
  have hy' : y ∈ FlatSideData.interval D := by
    dsimp [D, FlatSideData.interval]
    rw [c₁_eq_sideH hα hβ, c₂_eq_sideH hα hβ]
    exact hy
  have hin := FlatSideData.leaf_inside (D := D) hy' hu
  rw [region_eq_betweenChord hα hβ] at hin
  exact hin

/-- The left endpoint of a strict template leaf lies on `x0 = 0`. -/
lemma between_leafA_left_coord {α₁ β₁ α₂ β₂ : ℝ} (hα : α₁ < α₂) (hβ : β₁ < β₂)
    {y : ℝ} : (FlatSideData.leafA (D := ⟨α₁, β₁, α₂, β₂, hα, hβ⟩) y) 0 = 0 := by
  simp [FlatSideData.leafA, genA, genP]

/-- The right endpoint of a strict template leaf lies on `x0 = 1`. -/
lemma between_leafB_right_coord {α₁ β₁ α₂ β₂ : ℝ} (hα : α₁ < α₂) (hβ : β₁ < β₂)
    {y : ℝ} : (FlatSideData.leafB (D := ⟨α₁, β₁, α₂, β₂, hα, hβ⟩) y) 0 = 1 := by
  simp [FlatSideData.leafB, genB, genP]



/-- **Strict trapezoid realisation of a flat component**: if a flat
component `C` is the between-region of two chords with STRICT endpoint
inequalities (`α₁<α₂`, `β₁<β₂`), then `C` is the `FlatSideData.region`
of the component template, its centreline heights are
`(sideH₁ α₁β₁ (1/2), sideH₁ α₂β₂ (1/2))`, and every template leaf
through a centreline height with segment parameter `u ∈ (0,1)` lies
inside `C`, connecting `x0 = 0` (leafA) to `x0 = 1` (leafB). -/
theorem flatComponent_strict_trapezoid {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {α₁ β₁ α₂ β₂ : ℝ}
    (hC : flatComponent f p = betweenChord α₁ β₁ α₂ β₂)
    (hα : α₁ < α₂) (hβ : β₁ < β₂) :
    ∃ D : FlatSideData,
      flatComponent f p = FlatSideData.region D ∧
      FlatSideData.c₁ D = sideH₁ α₁ β₁ (1 / 2) ∧
      FlatSideData.c₂ D = sideH₁ α₂ β₂ (1 / 2) ∧
      ∀ (y u : ℝ), y ∈ Set.Ioo (sideH₁ α₁ β₁ (1 / 2)) (sideH₁ α₂ β₂ (1 / 2)) →
        u ∈ Set.Ioo 0 1 → FlatSideData.leafP (D := D) y u ∈ flatComponent f p := by
  refine ⟨⟨α₁, β₁, α₂, β₂, hα, hβ⟩, ?_, ?_, ?_, ?_⟩
  · rw [hC, betweenChord_eq_region hα hβ]
  · rfl
  · rfl
  · intro y u hy hu
    rw [hC]
    exact between_leaf_inside hα hβ hy hu

end Submission.PaperBand

import Submission.Work.RegionBetween
import Submission.Work.StrictTrapezoid

open OptimalMoebius Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# T1-ii Layer 4–5 (wedge case): the fan leaf family for coincident sides

When the two bounding chords of a flat component MEET at a seam point —
the `α₁ = α₂` case (both chords pass through `(0, α)`, the paper's
"coincident lines" degenerate) — the between-region is a wedge and the
leaf family interpolating between the chords is a FAN of chords through
the common apex `(0, α)`: the leaf at centreline height `y` runs from
`(0, α)` to `(1, 2y − α)`.

The wedge data: apex height `α`, lower side ending at `(1, β₁)` and
upper side at `(1, β₂)` (`β₁ < β₂`).  The region is
`betweenChord α β₁ α β₂` (the two chords share the apex), the centre
heights are `cᵢ = (α+βᵢ)/2`, and

    region = ⋃_{y ∈ (c₁,c₂)} fanLeaf y

where `fanLeaf y := { (u, α + 2u(y−α)) | u ∈ (0,1) }` is the open chord
from `(0,α)` to `(1,2y−α)`.  This file proves that equality (the
wedge analogue of `region_eq_betweenChord`), plus membership facts and
the centre interval.

Build: `lake build Submission.Work.WedgeFan` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- The wedge apex side data: common apex height `α` at `x0 = 0`, lower
side to `(1,β₁)` and upper side to `(1,β₂)`, `β₁ < β₂`. -/
structure FanSideData where
  (α β₁ β₂ : ℝ)
  (hβ : β₁ < β₂)

namespace FanSideData

variable (F : FanSideData)

/-- The wedge region: the open between-region of the two chords through
the apex. -/
def region : Set ℝ² := betweenChord F.α F.β₁ F.α F.β₂

/-- The lower centre height `c₁ = (α+β₁)/2`. -/
def c₁ : ℝ := (F.α + F.β₁) / 2

/-- The upper centre height `c₂ = (α+β₂)/2`. -/
def c₂ : ℝ := (F.α + F.β₂) / 2

/-- The centre-height interval. -/
def interval : Set ℝ := Set.Ioo (c₁ F) (c₂ F)

/-- The fan leaf point at centreline height `y` and segment parameter
`u`: `(u, α + 2u(y−α))`, on the chord from `(0,α)` to `(1, 2y−α)`. -/
def leafP (y u : ℝ) : ℝ² := !₂[u, F.α + 2 * u * (y - F.α)]

/-- The open fan leaf at height `y`. -/
def fanLeaf (y : ℝ) : Set ℝ² := (fun u : ℝ => leafP F y u) '' Set.Ioo 0 1

/-- Left endpoint of a fan leaf: the common apex `(0,α)`. -/
def leafA (y : ℝ) : ℝ² := !₂[0, F.α]

/-- Right endpoint of a fan leaf: `(1, 2y−α)`. -/
def leafB (y : ℝ) : ℝ² := !₂[1, 2 * y - F.α]

/-- The leaf point at height `y` crosses the centreline at `(1/2, y)`. -/
lemma leafP_half (y : ℝ) :
    (leafP F y (1 / 2)) 0 = 1 / 2 ∧ (leafP F y (1 / 2)) 1 = y := by
  constructor <;> simp [leafP]

/-- The fan leaf at height `y` is the affine segment from `leafA` to
`leafB`. -/
lemma leafP_eq_combo (y u : ℝ) :
    leafP F y u = (1 - u) • leafA F y + u • leafB F y := by
  ext i <;> fin_cases i <;> simp [leafP, leafA, leafB, smul_eq_mul, add_mul, mul_add] <;> ring

/-- **Membership of the fan leaf in the wedge region**: for a centre
height `y ∈ (c₁,c₂)` and `u ∈ (0,1)`, the leaf point lies strictly
between the two side chords. -/
theorem leafP_mem_region {y u : ℝ}
    (hy : y ∈ interval F) (hu : u ∈ Set.Ioo 0 1) : leafP F y u ∈ region F := by
  rw [region]
  rw [mem_betweenChord]
  have hu0 : 0 < u := (Set.mem_Ioo.mp hu).1
  have hu1 : u < 1 := (Set.mem_Ioo.mp hu).2
  rcases (Set.mem_Ioo.mp hy) with ⟨hy1, hy2⟩
  dsimp [c₁, c₂] at hy1 hy2
  constructor
  · rw [stripInterior]
    constructor <;> simp [leafP, hu0, hu1]
  constructor
  · -- sideH₁ α β₁ u < α + 2u(y−α)
    have hβ : F.β₁ - F.α < 2 * (y - F.α) := by nlinarith [hy1]
    have hmul : u * (F.β₁ - F.α) < u * (2 * (y - F.α)) :=
      mul_lt_mul_of_pos_left hβ hu0
    simp [leafP, sideH₁]
    nlinarith [hmul]
  · -- α + 2u(y−α) < sideH₁ α β₂ u
    have hβ : 2 * (y - F.α) < F.β₂ - F.α := by nlinarith [hy2]
    have hmul : u * (2 * (y - F.α)) < u * (F.β₂ - F.α) :=
      mul_lt_mul_of_pos_left hβ hu0
    simp [leafP, sideH₁]
    nlinarith [hmul]

/-- Height of a side chord over `x0 = 1/2 = 2⁻¹`. -/
lemma sideH₁_inv2 (α β : ℝ) : sideH₁ α β (2⁻¹) = (α + β) / 2 := by
  simpa [show (1 / 2 : ℝ) = (2⁻¹ : ℝ) by norm_num] using sideH₁_half (α := α) (β := β)

/-- The centreline heights of the wedge region are exactly the interval
`(c₁,c₂)`. -/
theorem centre_interval :
    {y : ℝ | (!₂[1 / 2, y] : ℝ²) ∈ region F} = interval F := by
  ext y
  change ((!₂[1 / 2, y] : ℝ²) ∈ betweenChord F.α F.β₁ F.α F.β₂) ↔
    (F.α + F.β₁) / 2 < y ∧ y < (F.α + F.β₂) / 2
  rw [mem_betweenChord]
  constructor
  · intro hy
    rcases hy with ⟨hS, hlt₁, hlt₂⟩
    have hc0 : (!₂[1 / 2, y] : ℝ²) 0 = 1 / 2 := by simp
    have hc1 : (!₂[1 / 2, y] : ℝ²) 1 = y := by simp
    rw [hc0, hc1] at hlt₁ hlt₂
    rw [sideH₁_half] at hlt₁ hlt₂
    constructor <;> nlinarith [hlt₁, hlt₂]
  · intro hy
    rcases hy with ⟨hy1, hy2⟩
    have hS : (!₂[1 / 2, y] : ℝ²) ∈ stripInterior := by
      rw [stripInterior]
      constructor <;> simp <;> norm_num
    constructor
    · exact hS
    constructor
    · simp
      rw [sideH₁_inv2]
      nlinarith [hy1]
    · simp
      rw [sideH₁_inv2]
      nlinarith [hy2]

/-- **Wedge analogue of `region_eq_betweenChord`**: the wedge region is
the union of its fan leaves over the centre heights. -/
theorem region_eq_union_leaves :
    region F = ⋃ y ∈ interval F, fanLeaf F y := by
  ext z
  constructor
  · intro hz
    rw [Set.mem_iUnion₂]
    rw [region] at hz
    rw [mem_betweenChord] at hz
    rcases hz with ⟨hzS, hlt₁, hlt₂⟩
    have hz0pos : 0 < z 0 := by
      rw [stripInterior] at hzS
      exact hzS.1
    have hz0lt : z 0 < 1 := by
      rw [stripInterior] at hzS
      exact hzS.2
    let y : ℝ := F.α + (z 1 - F.α) / (2 * z 0)
    have hy : y ∈ interval F := by
      rw [interval]
      rw [Set.mem_Ioo]
      dsimp [y, c₁, c₂]
      constructor
      · -- (α+β₁)/2 < α + (z1−α)/(2z0)
        have hlt₁' : F.α + (F.β₁ - F.α) * (z 0) < z 1 := by
          dsimp [sideH₁] at hlt₁
          exact hlt₁
        have hnum : (F.β₁ - F.α) * (z 0) < z 1 - F.α := by nlinarith
        have h2 : (0 : ℝ) < 2 := by norm_num
        have h2m : 2 * ((F.β₁ - F.α) * (z 0)) < 2 * (z 1 - F.α) :=
          mul_lt_mul_of_pos_left hnum h2
        have h2z : 0 < 2 * (z 0) := by nlinarith
        have hdiv : (F.β₁ - F.α) / 2 < (z 1 - F.α) / (2 * (z 0)) := by
          rw [div_lt_div_iff₀ h2 h2z]
          nlinarith [h2m]
        nlinarith
      · -- α + (z1−α)/(2z0) < (α+β₂)/2
        have hlt₂' : z 1 < F.α + (F.β₂ - F.α) * (z 0) := by
          dsimp [sideH₁] at hlt₂
          exact hlt₂
        have hnum : z 1 - F.α < (F.β₂ - F.α) * (z 0) := by nlinarith
        have h2 : (0 : ℝ) < 2 := by norm_num
        have h2m : 2 * (z 1 - F.α) < 2 * ((F.β₂ - F.α) * (z 0)) :=
          mul_lt_mul_of_pos_left hnum h2
        have h2z : 0 < 2 * (z 0) := by nlinarith
        have hdiv : (z 1 - F.α) / (2 * (z 0)) < (F.β₂ - F.α) / 2 := by
          rw [div_lt_div_iff₀ h2z h2]
          nlinarith [h2m]
        nlinarith
    refine ⟨y, hy, ?_⟩
    rw [fanLeaf, Set.mem_image]
    refine ⟨z 0, ⟨hz0pos, hz0lt⟩, ?_⟩
    ext i <;> fin_cases i
    · simp [leafP]
    · dsimp [y, leafP]
      field_simp [show z 0 ≠ 0 by linarith]
      ring
  · intro hz
    rw [Set.mem_iUnion₂] at hz
    rcases hz with ⟨y, hy, hyz⟩
    rcases hyz with ⟨u, hu, hzEq⟩
    have hleaf : leafP F y u ∈ region F := leafP_mem_region (F := F) hy hu
    rw [region] at hleaf
    rw [← hzEq]
    exact hleaf

end FanSideData

end Submission.PaperBand

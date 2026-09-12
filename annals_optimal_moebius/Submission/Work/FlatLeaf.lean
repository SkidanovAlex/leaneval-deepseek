import Submission.Work.GeneralChord

open Filter Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-!
# Flat-leaf reparametrisation by centre height (FlatLeaf)

The `GeneralChord` family is indexed by the side-parameter `t ∈ (0,1)`.
The actual flat leaf through a centreline point `(1/2, y)` must be
indexed by the CENTRE HEIGHT `y`.  Since the chord `genP t` crosses the
centreline `x0 = 1/2` at the convex-combined centre height

    y = (1−t)·h₁(1/2) + t·h₂(1/2) =: (1−t)·c₁ + t·c₂

(`cᵢ := (αᵢ + βᵢ)/2` the centre heights of the two sides `Lᵢ`), the
inverse parameter is affine:

    t(y) := (y − c₁)/(c₂ − c₁) ,

and the leaf through `(1/2, y)` is `genP (t(y))`.  The centre-height
interval of the region between the two sides is `(c₁, c₂)` (open), and
`t` maps it onto `(0,1)`.

This file proves the two facts the flat-component correspondence needs:

* **`flatT_mem`** — for `y ∈ (c₁, c₂)`, the inverse parameter
  `t(y) ∈ (0,1)` (the interval `(c₁,c₂)` is the "flat-height interval" of
  the model region, mapped onto the parameter interval);
* **`flatLeafT_centre`** — the chord `genP (t(y))` passes through
  `(1/2, y)`: its height at `x0 = 1/2` is exactly `y` (the centre
  condition of a `BandFoliation` leaf).

Build: `lake build Submission.Work.FlatLeaf` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

variable {α₁ β₁ α₂ β₂ : ℝ}

/-- The left side `L₁` crosses the centreline at `(α₁ + β₁)/2`. -/
lemma sideH₁_half (α β : ℝ) : sideH₁ α β (1 / 2) = (α + β) / 2 := by
  simp [sideH₁]
  ring

/-- The right side `L₂` crosses the centreline at `(α₂ + β₂)/2`. -/
lemma sideH₂_half (α β : ℝ) : sideH₂ α β (1 / 2) = (α + β) / 2 := by
  simp [sideH₂]
  ring

/-- The centre heights of the two sides are ordered: `c₁ < c₂`. -/
lemma centreH_lt (hα : α₁ < α₂) (hβ : β₁ < β₂) :
    sideH₁ α₁ β₁ (1 / 2) < sideH₂ α₂ β₂ (1 / 2) := by
  exact sideH_lt hα hβ (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc 0 1)

/-- The centre-height denominator is nonzero. -/
lemma centreH_ne (hα : α₁ < α₂) (hβ : β₁ < β₂) :
    sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2) ≠ 0 := by
  have : sideH₁ α₁ β₁ (1 / 2) < sideH₂ α₂ β₂ (1 / 2) := centreH_lt hα hβ
  linarith

/-- The inverse side-parameter for a given centre height `y`:
`t(y) = (y − c₁)/(c₂ − c₁)`. -/
def flatLeafT (α₁ β₁ α₂ β₂ y : ℝ) : ℝ :=
  (y - sideH₁ α₁ β₁ (1 / 2)) / (sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2))

/-- **The centre-height interval maps onto the parameter interval**: for
`y` strictly between the two sides' centre heights `c₁ < y < c₂`, the
inverse parameter satisfies `0 < t(y) < 1`. -/
theorem flatT_mem (hα : α₁ < α₂) (hβ : β₁ < β₂) {y : ℝ}
    (hy : y ∈ Set.Ioo (sideH₁ α₁ β₁ (1 / 2)) (sideH₂ α₂ β₂ (1 / 2))) :
    flatLeafT α₁ β₁ α₂ β₂ y ∈ Set.Ioo 0 1 := by
  have hd : sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2) > 0 := by
    have : sideH₁ α₁ β₁ (1 / 2) < sideH₂ α₂ β₂ (1 / 2) := centreH_lt hα hβ
    linarith
  have hy₁ : sideH₁ α₁ β₁ (1 / 2) < y := (Set.mem_Ioo.mp hy).1
  have hy₂ : y < sideH₂ α₂ β₂ (1 / 2) := (Set.mem_Ioo.mp hy).2
  constructor
  · -- t > 0: y − c₁ > 0, denominator > 0
    dsimp [flatLeafT]
    exact div_pos (by linarith) hd
  · -- t < 1: y − c₁ < c₂ − c₁ ⟺ y < c₂
    dsimp [flatLeafT]
    rw [div_lt_one hd]  -- (a < b) ↔ a < b for a:=y−c₁, b:=c₂−c₁: div_lt_one? need div_lt_one hd : x/d < 1 ↔ x < d given d >0: hmm signature: div_lt_one₀?
    linarith

/-- **The leaf through centre height `y`**: the chord `genP (t(y))`
crosses the centreline `x0 = 1/2` at height exactly `y`. -/
theorem flatLeafT_centre (hα : α₁ < α₂) (hβ : β₁ < β₂) {y : ℝ} :
    (genP α₁ β₁ α₂ β₂ (flatLeafT α₁ β₁ α₂ β₂ y) (1 / 2)) 1 = y := by
  have hd : sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2) ≠ 0 := centreH_ne hα hβ
  rw [genP_coord1]
  have hval : (1 - flatLeafT α₁ β₁ α₂ β₂ y) * sideH₁ α₁ β₁ (1 / 2) +
        flatLeafT α₁ β₁ α₂ β₂ y * sideH₂ α₂ β₂ (1 / 2) = y := by
    dsimp [flatLeafT]
    field_simp [hd]
    ring
  simpa [flatLeafT] using hval

end Submission.PaperBand

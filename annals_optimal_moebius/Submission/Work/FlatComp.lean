import Submission.Work.FlatLeaf
import Submission.Work.GeneralChord

open Filter Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-!
# Component-level trapezoid data and its FlatLeafInstance (FlatComp)

The flat-leaf construction for a REAL flat component needs only the
component-level trapezoid data: the seam endpoints of its two side lines
`L₁ : (0, α₁) → (1, β₁)` and `L₂ : (0, α₂) → (1, β₂)` (with
`α₁ < α₂`, `β₁ < β₂`, so `L₁` is strictly below `L₂` over `[0,1]`), and
the derived centre heights `c₁ = (α₁+β₁)/2`, `c₂ = (α₂+β₂)/2`.  The
concrete prototype of `FlatLeafInstance` (`(0,0,1,3)`) is one instance of
this structure; a genuine component of an actual band will supply its own
`(αᵢ,βᵢ)` once the component geometry (Target-(A)-sides and their seam
hits) is in place.

* **`FlatSideData`** — the bundled data: `α₁ β₁ α₂ β₂ : ℝ` with the side
  order proofs;
* derived objects: `line₁/line₂` (the side lines), `c₁/c₂` (centre
  heights, `c₁ < c₂`), `interval` (`= (c₁, c₂)`), `leafT` (the inverse
  side parameter `(y−c₁)/(c₂−c₁)`), `leafP` (the chord point
  `genP (leafT y) u`), `leafA/leafB` (the endpoints), `region` (the open
  between-the-lines region);
* **the FlatLeafInstance theorems** (each a composition of the green
  `GeneralChord`/`FlatLeaf` lemmas, specialised to `D`):
  * `leafT_mem` — `y ∈ (c₁,c₂)` gives `leafT y ∈ (0,1)`;
  * `leafT_c₁`/`leafT_c₂` — the parameter hits `0`/`1` at the interval
    ends;
  * **`leaf_inside`** — interior chord points lie strictly inside the
    region between the sides;
  * **`leaf_centre`** — the leaf crosses the centreline `x0 = 1/2` at
    height `y`;
  * **`leaf_disjoint`** — distinct heights give disjoint leaves.

Build: `lake build Submission.Work.FlatComp` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- The inverse side parameter is injective in the centre height:
`t(y₁) = t(y₂)` forces `y₁ = y₂` (the side lines are distinct over
`[0,1]`, so the denominator `c₂ − c₁` is nonzero). -/
lemma flatLeafT_injective {α₁ β₁ α₂ β₂ y₁ y₂ : ℝ} (hα : α₁ < α₂) (hβ : β₁ < β₂)
    (h : flatLeafT α₁ β₁ α₂ β₂ y₁ = flatLeafT α₁ β₁ α₂ β₂ y₂) : y₁ = y₂ := by
  dsimp [flatLeafT] at h
  have hd : sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2) ≠ 0 := centreH_ne hα hβ
  field_simp [hd] at h
  linarith

/-- The component-level trapezoid data: seam endpoints of the two side
lines, ordered so that `L₁` is below `L₂` over `x0 ∈ [0,1]`. -/
structure FlatSideData where
  (α₁ β₁ α₂ β₂ : ℝ)
  (hα : α₁ < α₂)
  (hβ : β₁ < β₂)

namespace FlatSideData

variable (D : FlatSideData)

/-- The lower side line `L₁` of the component. -/
def line₁ : ℝ → ℝ := fun x0 => sideH₁ D.α₁ D.β₁ x0

/-- The upper side line `L₂` of the component. -/
def line₂ : ℝ → ℝ := fun x0 => sideH₂ D.α₂ D.β₂ x0

/-- Centre height of the lower side (its crossing of `x0 = 1/2`). -/
def c₁ : ℝ := line₁ D (1 / 2)

/-- Centre height of the upper side (its crossing of `x0 = 1/2`). -/
def c₂ : ℝ := line₂ D (1 / 2)

/-- The centre-height interval of the component's region: `(c₁, c₂)`. -/
def interval : Set ℝ := Set.Ioo (c₁ D) (c₂ D)

/-- The inverse side parameter of a centre height: `(y − c₁)/(c₂ − c₁)`. -/
def leafT (y : ℝ) : ℝ := flatLeafT D.α₁ D.β₁ D.α₂ D.β₂ y

/-- The point of the leaf through centre height `y` at segment
parameter `u`. -/
def leafP (y u : ℝ) : ℝ² := genP D.α₁ D.β₁ D.α₂ D.β₂ (leafT D y) u

/-- Left endpoint of the leaf: on `x0 = 0`. -/
def leafA (y : ℝ) : ℝ² := genA D.α₁ D.β₁ D.α₂ D.β₂ (leafT D y)

/-- Right endpoint of the leaf: on `x0 = 1`. -/
def leafB (y : ℝ) : ℝ² := genB D.α₁ D.β₁ D.α₂ D.β₂ (leafT D y)

/-- The open region of the strip strictly between the two side lines. -/
def region : Set ℝ² :=
  {x | 0 < x 0 ∧ x 0 < 1 ∧ line₁ D (x 0) < x 1 ∧ x 1 < line₂ D (x 0)}

/-- The centre heights are ordered: `c₁ < c₂`. -/
lemma c₁_lt_c₂ : c₁ D < c₂ D := by
  dsimp [c₁, c₂, line₁, line₂]
  exact centreH_lt D.hα D.hβ

/-- The centre-height denominator is nonzero. -/
lemma c_ne : c₂ D - c₁ D ≠ 0 := by
  dsimp [c₁, c₂, line₁, line₂]
  exact centreH_ne D.hα D.hβ

/-- The side lines are strictly ordered on `[0,1]`. -/
lemma line_lt {x : ℝ} (hx : x ∈ Set.Icc 0 1) : line₁ D x < line₂ D x := by
  dsimp [line₁, line₂]
  exact sideH_lt D.hα D.hβ hx

/-- **The centre-height interval maps onto the parameter interval**: for
`y ∈ (c₁, c₂)`, `leafT y ∈ (0,1)`. -/
theorem leafT_mem {y : ℝ} (hy : y ∈ interval D) : leafT D y ∈ Set.Ioo 0 1 := by
  dsimp [interval, leafT] at hy ⊢
  exact flatT_mem D.hα D.hβ hy

/-- The parameter is `0` at the bottom end of the interval. -/
theorem leafT_c₁ : leafT D (c₁ D) = 0 := by
  dsimp [leafT, flatLeafT, c₁, line₁, line₂]
  have hd : sideH₂ D.α₂ D.β₂ (1 / 2) - sideH₁ D.α₁ D.β₁ (1 / 2) ≠ 0 := centreH_ne D.hα D.hβ
  field_simp [hd]
  ring

/-- The parameter is `1` at the top end of the interval. -/
theorem leafT_c₂ : leafT D (c₂ D) = 1 := by
  dsimp [leafT, flatLeafT, c₂, line₁, line₂]
  have hd : sideH₂ D.α₂ D.β₂ (1 / 2) - sideH₁ D.α₁ D.β₁ (1 / 2) ≠ 0 := centreH_ne D.hα D.hβ
  field_simp [hd]

/-- **The leaf lies strictly inside the between-region**: for a centre
height `y ∈ (c₁,c₂)` and an interior segment parameter `u ∈ (0,1)`, the
leaf point is in `region D`. -/
theorem leaf_inside {y u : ℝ} (hy : y ∈ interval D) (hu : u ∈ Set.Ioo 0 1) :
    leafP D y u ∈ region D := by
  have ht : leafT D y ∈ Set.Ioo 0 1 := leafT_mem D hy
  have huIcc : u ∈ Set.Icc 0 1 := by
    exact ⟨le_of_lt (Set.mem_Ioo.mp hu).1, le_of_lt (Set.mem_Ioo.mp hu).2⟩
  have hin := genChord_inside D.hα D.hβ (t := leafT D y) (u := u) ht huIcc
  dsimp [region, leafP]
  constructor
  · rw [genP_coord0]
    exact (Set.mem_Ioo.mp hu).1
  constructor
  · rw [genP_coord0]
    exact (Set.mem_Ioo.mp hu).2
  constructor
  · dsimp [line₁]
    exact hin.1
  · dsimp [line₂] at hin ⊢
    rw [genP_coord0]
    exact hin.2

/-- **The leaf crosses the centreline at its own height**: the point at
`x0 = 1/2` of the leaf through centre height `y` has second coordinate
`y`. -/
theorem leaf_centre {y : ℝ} : (leafP D y (1 / 2)) 1 = y := by
  dsimp [leafP, leafT]
  exact flatLeafT_centre D.hα D.hβ

/-- **Distinct heights give disjoint leaves**: for `y₁ ≠ y₂` in the
centre-height interval, the leaves do not meet. -/
theorem leaf_disjoint {y₁ y₂ u₁ u₂ : ℝ}
    (hy₁ : y₁ ∈ interval D) (hy₂ : y₂ ∈ interval D)
    (hu₁ : u₁ ∈ Set.Icc 0 1) (hu₂ : u₂ ∈ Set.Icc 0 1) (hyne : y₁ ≠ y₂) :
    leafP D y₁ u₁ ≠ leafP D y₂ u₂ := by
  have ht₁ : leafT D y₁ ∈ Set.Ioo 0 1 := leafT_mem D hy₁
  have ht₂ : leafT D y₂ ∈ Set.Ioo 0 1 := leafT_mem D hy₂
  have htne : leafT D y₁ ≠ leafT D y₂ := by
    intro ht
    dsimp [leafT] at ht
    have hinj := flatLeafT_injective D.hα D.hβ ht
    exact hyne hinj
  dsimp [leafP]
  exact genChord_disjoint D.hα D.hβ (t₁ := leafT D y₁) (t₂ := leafT D y₂)
    ht₁ ht₂ hu₁ hu₂ htne

end FlatSideData

end Submission.PaperBand

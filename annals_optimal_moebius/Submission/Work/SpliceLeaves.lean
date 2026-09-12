import Submission.Work.WedgeFan
import Submission.Work.StrictTrapezoid
import Submission.Work.FlatFamily

open OptimalMoebius Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# The strict/wedge SPLICE: one continuous centreline leaf family

For a flat component that is the between-region of two pointwise-ordered
chords `stripChord α₁β₁ < stripChord α₂β₂` (which covers the strict
trapezoid, the `α₁ = α₂` wedge and the `β₁ = β₂` mirror wedge at once),
the spliced leaf at centreline height `y` is the BLENDED chord

    blendP α₁β₁ α₂β₂ y u := genP α₁β₁ α₂β₂ (flatLeafT α₁β₁ α₂β₂ y) u

joining the fraction-`t` point of the two boundary arcs, with
`t = (y−c₁)/(c₂−c₁)`, `cᵢ = sideH₁ αᵢβᵢ (1/2)`.  This file proves:
* `blendT_mem` — for `y ∈ (c₁,c₂)` (pointwise-ordered data) the
  parameter lies in `(0,1)`;
* `blend_inside` — the leaf lies strictly inside the between-region;
* endpoint-height continuity (`continuous_blendA1`/`continuous_blendB1`)
  and the centre crossing (`blendP_half`);
* the AGREEMENT lemmas: `blendP_eq_flatSideData` (in the strict case the
  blend IS the `FlatSideData.leafP` template family) and
  `blendP_eq_fan` (in the `α₁=α₂` wedge case the blend IS the
  `FanSideData` fan leaf), so the single blended family interpolates
  between the strict and fan leaf families continuously.

Build: `lake build Submission.Work.SpliceLeaves` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- The blended leaf at centreline height `y`: the template chord between
the two boundary arcs at inverse parameter `t(y)`. -/
def blendP (α₁ β₁ α₂ β₂ : ℝ) (y u : ℝ) : ℝ² :=
  genP α₁ β₁ α₂ β₂ (flatLeafT α₁ β₁ α₂ β₂ y) u

/-- The inverse parameter of a centreline height. -/
def blendT (α₁ β₁ α₂ β₂ : ℝ) (y : ℝ) : ℝ := flatLeafT α₁ β₁ α₂ β₂ y

/-- `blendT` is the affine inverse parameter `(y−c₁)/(c₂−c₁)` with
`cᵢ = sideH₁ αᵢβᵢ (1/2)`. -/
lemma blendT_eq (α₁ β₁ α₂ β₂ y : ℝ) :
    blendT α₁ β₁ α₂ β₂ y =
      (y - sideH₁ α₁ β₁ (1 / 2)) / (sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2)) := by
  rfl

/-- For pointwise-ordered data, `y ∈ (c₁,c₂)` gives parameter in
`(0,1)`. -/
theorem blendT_mem {α₁ β₁ α₂ β₂ : ℝ}
    (hord : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ α₁ β₁ u < sideH₁ α₂ β₂ u)
    {y : ℝ} (hy : y ∈ Set.Ioo (sideH₁ α₁ β₁ (1 / 2)) (sideH₂ α₂ β₂ (1 / 2))) :
    blendT α₁ β₁ α₂ β₂ y ∈ Set.Ioo 0 1 := by
  rw [blendT_eq]
  rw [Set.mem_Ioo]
  rcases (Set.mem_Ioo.mp hy) with ⟨hy1, hy2⟩
  have hord12 : sideH₁ α₁ β₁ (1 / 2) < sideH₁ α₂ β₂ (1 / 2) := hord (1 / 2) ⟨by norm_num, by norm_num⟩
  have hden : 0 < sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2) := by
    rw [sideH₂_eq_sideH₁]
    linarith
  constructor
  · rw [div_pos_iff]
    left
    constructor <;> linarith
  · rw [div_lt_one hden]
    linarith

/-- The blend of two pointwise-ordered heights lies strictly between
them (for parameter in `(0,1)`). -/
lemma blend_between {h₁ h₂ t : ℝ} (hlt : h₁ < h₂) (ht : t ∈ Set.Ioo 0 1) :
    h₁ < (1 - t) * h₁ + t * h₂ ∧ (1 - t) * h₁ + t * h₂ < h₂ := by
  rcases (Set.mem_Ioo.mp ht) with ⟨ht0, ht1⟩
  constructor
  · have hmul : 0 < t * (h₂ - h₁) := mul_pos ht0 (sub_pos.mpr hlt)
    nlinarith
  · have hmul : t * (h₂ - h₁) < h₂ - h₁ := (mul_lt_iff_lt_one_left (sub_pos.mpr hlt)).mpr ht1
    nlinarith

/-- **The blended leaf lies strictly inside the between-region** for
centre heights `y ∈ (c₁,c₂)` and segment parameter `u ∈ (0,1)`. -/
theorem blend_inside {α₁ β₁ α₂ β₂ : ℝ}
    (hord : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ α₁ β₁ u < sideH₁ α₂ β₂ u)
    {y u : ℝ}
    (hy : y ∈ Set.Ioo (sideH₁ α₁ β₁ (1 / 2)) (sideH₂ α₂ β₂ (1 / 2)))
    (hu : u ∈ Set.Ioo 0 1) :
    blendP α₁ β₁ α₂ β₂ y u ∈ betweenChord α₁ β₁ α₂ β₂ := by
  have ht : blendT α₁ β₁ α₂ β₂ y ∈ Set.Ioo 0 1 := blendT_mem hord hy
  have hord_u : sideH₁ α₁ β₁ u < sideH₂ α₂ β₂ u := by
    rw [sideH₂_eq_sideH₁]
    exact hord u hu
  rw [mem_betweenChord]
  constructor
  · rw [stripInterior]
    rcases (Set.mem_Ioo.mp hu) with ⟨hu0, hu1⟩
    constructor <;> simp [blendP, genP, hu0, hu1]
  constructor
  · have hb := (blend_between hord_u ht).1
    dsimp [blendP]
    rw [genP_coord0, genP_coord1]
    simpa [blendT] using hb
  · have hb := (blend_between hord_u ht).2
    rw [sideH₂_eq_sideH₁] at hb
    dsimp [blendP]
    rw [genP_coord0, genP_coord1, sideH₂_eq_sideH₁]
    simpa [blendT] using hb

/-- The affine inverse-parameter identity: the convex combination of the
two centre heights returns `y`. -/
lemma affine_t_self {c₁ c₂ y : ℝ} (hden : c₂ - c₁ ≠ 0) :
    (1 - (y - c₁) / (c₂ - c₁)) * c₁ + ((y - c₁) / (c₂ - c₁)) * c₂ = y := by
  field_simp [hden]
  ring_nf

/-- The blended leaf crosses the centreline at its own height. -/
theorem blendP_half {α₁ β₁ α₂ β₂ : ℝ}
    (hden : sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2) ≠ 0) {y : ℝ} :
    (blendP α₁ β₁ α₂ β₂ y (1 / 2)) 1 = y := by
  dsimp [blendP]
  rw [genP_coord1]
  have ht : flatLeafT α₁ β₁ α₂ β₂ y =
      (y - sideH₁ α₁ β₁ (1 / 2)) / (sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2)) := by rfl
  rw [ht]
  exact affine_t_self (c₁ := sideH₁ α₁ β₁ (1 / 2)) (c₂ := sideH₂ α₂ β₂ (1 / 2)) hden

/-- In the strict case the blend is exactly the `FlatSideData` template
leaf family. -/
lemma blendP_eq_flatSideData {α₁ β₁ α₂ β₂ : ℝ} (hα : α₁ < α₂) (hβ : β₁ < β₂)
    {y u : ℝ} :
    blendP α₁ β₁ α₂ β₂ y u =
      FlatSideData.leafP (D := ⟨α₁, β₁, α₂, β₂, hα, hβ⟩) y u := by
  simp [blendP, FlatSideData.leafP, FlatSideData.leafT]

/-- The left endpoint height of a blended leaf. -/
lemma blendA1_formula (α₁ β₁ α₂ β₂ y : ℝ) :
    (genA α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)) 1 =
      α₁ + blendT α₁ β₁ α₂ β₂ y * (α₂ - α₁) := by
  dsimp [genA, genP, blendT, sideH₁, sideH₂]
  ring_nf

/-- The right endpoint height of a blended leaf. -/
lemma blendB1_formula (α₁ β₁ α₂ β₂ y : ℝ) :
    (genB α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)) 1 =
      β₁ + blendT α₁ β₁ α₂ β₂ y * (β₂ - β₁) := by
  dsimp [genB, genP, blendT, sideH₁, sideH₂]
  ring_nf

/-- `blendT` in multiplicative-inverse form. -/
lemma blendT_eq_mulinv (α₁ β₁ α₂ β₂ y : ℝ) :
    blendT α₁ β₁ α₂ β₂ y =
      (y - sideH₁ α₁ β₁ (1 / 2)) * (sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2))⁻¹ := by
  rw [blendT_eq, div_eq_mul_inv]

/-- Continuity of the LEFT endpoint height in the centreline height. -/
theorem continuous_blendA1 {α₁ β₁ α₂ β₂ : ℝ} :
    Continuous (fun y : ℝ => (genA α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)) 1) := by
  have hlin : ∀ y : ℝ, (genA α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)) 1 =
      α₁ + ((y - sideH₁ α₁ β₁ (1 / 2)) * (sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2))⁻¹) * (α₂ - α₁) := by
    intro y
    rw [blendA1_formula, blendT_eq_mulinv]
  have hcont : Continuous (fun y : ℝ => α₁ + ((y - sideH₁ α₁ β₁ (1 / 2)) *
      (sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2))⁻¹) * (α₂ - α₁)) := by
    fun_prop
  exact hcont.congr (fun y => (hlin y).symm)

/-- Continuity of the RIGHT endpoint height in the centreline height. -/
theorem continuous_blendB1 {α₁ β₁ α₂ β₂ : ℝ} :
    Continuous (fun y : ℝ => (genB α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)) 1) := by
  have hlin : ∀ y : ℝ, (genB α₁ β₁ α₂ β₂ (blendT α₁ β₁ α₂ β₂ y)) 1 =
      β₁ + ((y - sideH₁ α₁ β₁ (1 / 2)) * (sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2))⁻¹) * (β₂ - β₁) := by
    intro y
    rw [blendB1_formula, blendT_eq_mulinv]
  have hcont : Continuous (fun y : ℝ => β₁ + ((y - sideH₁ α₁ β₁ (1 / 2)) *
      (sideH₂ α₂ β₂ (1 / 2) - sideH₁ α₁ β₁ (1 / 2))⁻¹) * (β₂ - β₁)) := by
    fun_prop
  exact hcont.congr (fun y => (hlin y).symm)

/-- The centre height of the `genP`-chord at side-parameter `t`. -/
def fanCentre (α β₁ β₂ : ℝ) (t : ℝ) : ℝ :=
  (1 - t) * ((α + β₁) / 2) + t * ((α + β₂) / 2)

/-- **Agreement with the fan family in the `α₁ = α₂` wedge case** (in
`t`-parameter form): the `genP` chord between the two boundary arcs at
side-parameter `t` is exactly the `FanSideData` fan leaf whose centre
height is `fanCentre t`. -/
theorem genP_fan_agreement {α β₁ β₂ t u : ℝ} (hβ : β₁ < β₂) :
    genP α β₁ α β₂ t u =
      FanSideData.leafP (F := ⟨α, β₁, β₂, hβ⟩) (fanCentre α β₁ β₂ t) u := by
  ext i <;> fin_cases i
  · simp [genP, FanSideData.leafP, fanCentre]
  · simp [genP, FanSideData.leafP, fanCentre, sideH₁, sideH₂]
    ring_nf

/-- The centre heights at the ends of the parameter interval. -/
lemma fanCentre_zero (α β₁ β₂ : ℝ) : fanCentre α β₁ β₂ 0 = (α + β₁) / 2 := by
  simp [fanCentre]

lemma fanCentre_one (α β₁ β₂ : ℝ) : fanCentre α β₁ β₂ 1 = (α + β₂) / 2 := by
  simp [fanCentre]



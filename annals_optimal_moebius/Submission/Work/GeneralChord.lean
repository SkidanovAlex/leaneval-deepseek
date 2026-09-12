import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open Filter Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-!
# General chord interpolation between two non-crossing side lines

The `ModelChord` family generalised to ARBITRARY two non-crossing full
chords of the strip: the left side `L₁` joins `(0, α₁)` to `(1, β₁)` and
the right side `L₂` joins `(0, α₂)` to `(1, β₂)`, with `α₁ < α₂` and
`β₁ < β₂` (so `L₁` is strictly below `L₂` at every `x0 ∈ [0,1]` — the
affine lines do not cross inside the closed strip).  Their height
functions

    h₁(x0) := α₁ + (β₁−α₁)·x0 ,    h₂(x0) := α₂ + (β₂−α₂)·x0

satisfy `h₁ < h₂` on `[0,1]`.

The affine endpoint interpolation: for a parameter `t ∈ (0,1)` the chord

    chord(t) := { (u, (1−t)·h₁(u) + t·h₂(u))  |  u ∈ [0,1] }

joins `A(t) := (0, (1−t)α₁ + tα₂)` on `x0 = 0` to
`B(t) := (1, (1−t)β₁ + tβ₂)` on `x0 = 1`, and crosses the centreline
`x0 = 1/2` at the convex-combined centre height
`(1−t)·h₁(1/2) + t·h₂(1/2)`.  This is the exact model-instance
(`ModelChord`) when `(α₁,β₁,α₂,β₂) = (0,0,1,3)` with `t = h/2`.

Four structural properties (the `ModelChord` prototype, generalised):

* **`genChord_inside`** — the chord lies strictly BETWEEN the two side
  lines: `h₁(u) < x1 < h₂(u)` for every `t ∈ (0,1)`, `u ∈ [0,1]`;
* **`genChord_disjoint`** — distinct parameters give disjoint chords
  (`t₁ ≠ t₂ ⟹ genP t₁ u₁ ≠ genP t₂ u₂`);
* continuity: `t ↦ A(t)`, `t ↦ B(t)` are continuous (affine);
* endpoint matching: `t → 0` gives the side `L₁` (`A → (0,α₁)`,
  `B → (1,β₁)`), `t → 1` the side `L₂`;
* `genChord_centre` — `genP t (1/2)` has height
  `(1−t)·h₁(1/2) + t·h₂(1/2)` (the centre condition).

Build: `lake build Submission.Work.GeneralChord` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

-- ambient side data
variable {α₁ β₁ α₂ β₂ : ℝ}

/-- Height of the left side line `L₁` over `x0`. -/
def sideH₁ (α₁ β₁ : ℝ) (x0 : ℝ) : ℝ := α₁ + (β₁ - α₁) * x0

/-- Height of the right side line `L₂` over `x0`. -/
def sideH₂ (α₂ β₂ : ℝ) (x0 : ℝ) : ℝ := α₂ + (β₂ - α₂) * x0

/-- The interpolating chord is strictly between the two side lines on
`x0 ∈ [0,1]` whenever `α₁ < α₂` and `β₁ < β₂`. -/
lemma sideH_lt {α₁ β₁ α₂ β₂ : ℝ} (hα : α₁ < α₂) (hβ : β₁ < β₂)
    {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    sideH₁ α₁ β₁ x < sideH₂ α₂ β₂ x := by
  dsimp [sideH₁, sideH₂]
  have hx0 : 0 ≤ x := (Set.mem_Icc.mp hx).1
  have hx1 : x ≤ 1 := (Set.mem_Icc.mp hx).2
  -- difference = (α₁−α₂)(1−x) + (β₁−β₂)x < 0
  have hmain : (α₁ - α₂) * (1 - x) + (β₁ - β₂) * x < 0 := by
    have h₁ : (α₁ - α₂) * (1 - x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have h₂ : (β₁ - β₂) * x ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hx0
    have hsum : (α₁ - α₂) * (1 - x) + (β₁ - β₂) * x ≤ 0 := by linarith
    -- strict: at least one term is strictly negative (x ∈ {0,1} handles it)
    by_cases hx0' : x = 0
    · have : (β₁ - β₂) * x = 0 := by rw [hx0']; simp
      have h1 : (α₁ - α₂) * (1 - x) < 0 := by
        have : 0 < 1 - x := by rw [hx0']; norm_num
        exact mul_neg_of_neg_of_pos (by linarith) this
      linarith
    · have hxgt : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx0')
      have h2 : (β₁ - β₂) * x < 0 :=
        mul_neg_of_neg_of_pos (by linarith) hxgt
      linarith
  linarith

/-- The interpolating chord point at side-parameter `t ∈ (0,1)` and
segment-parameter `u ∈ [0,1]`: `(u, (1−t)·h₁(u) + t·h₂(u))`. -/
def genP (α₁ β₁ α₂ β₂ : ℝ) (t u : ℝ) : ℝ² :=
  !₂[u, (1 - t) * sideH₁ α₁ β₁ u + t * sideH₂ α₂ β₂ u]

/-- Left endpoint of the interpolating chord: `(0, (1−t)α₁ + tα₂)`. -/
def genA (α₁ β₁ α₂ β₂ : ℝ) (t : ℝ) : ℝ² := genP α₁ β₁ α₂ β₂ t 0

/-- Right endpoint of the interpolating chord: `(1, (1−t)β₁ + tβ₂)`. -/
def genB (α₁ β₁ α₂ β₂ : ℝ) (t : ℝ) : ℝ² := genP α₁ β₁ α₂ β₂ t 1

/-- First coordinate of the chord point is the segment parameter. -/
lemma genP_coord0 (α₁ β₁ α₂ β₂ t u : ℝ) : (genP α₁ β₁ α₂ β₂ t u) 0 = u := by
  simp [genP]

/-- Second coordinate of the chord point: the convex combination of the
side heights at `x0 = u`. -/
lemma genP_coord1 (α₁ β₁ α₂ β₂ t u : ℝ) :
    (genP α₁ β₁ α₂ β₂ t u) 1 = (1 - t) * sideH₁ α₁ β₁ u + t * sideH₂ α₂ β₂ u := by
  simp [genP]

/-- **The chord lies strictly between the two side lines (inside
lemma)**: for `α₁ < α₂`, `β₁ < β₂`, `t ∈ (0,1)` and `u ∈ [0,1]` the chord
point satisfies `h₁(u) < x1 < h₂(u)` — it never meets either side in the
strip. -/
theorem genChord_inside (hα : α₁ < α₂) (hβ : β₁ < β₂)
    {t u : ℝ} (ht : t ∈ Set.Ioo 0 1) (hu : u ∈ Set.Icc 0 1) :
    sideH₁ α₁ β₁ u < (genP α₁ β₁ α₂ β₂ t u) 1 ∧
      (genP α₁ β₁ α₂ β₂ t u) 1 < sideH₂ α₂ β₂ u := by
  have hlt := sideH_lt hα hβ hu
  have ht0 : 0 < t := (Set.mem_Ioo.mp ht).1
  have ht1 : t < 1 := (Set.mem_Ioo.mp ht).2
  rw [genP_coord1]
  constructor
  · -- h₁ < (1−t)h₁ + t·h₂ ⟺ 0 < t(h₂−h₁)
    have hmul : 0 < t * (sideH₂ α₂ β₂ u - sideH₁ α₁ β₁ u) := by
      exact mul_pos ht0 (by linarith)
    nlinarith
  · -- (1−t)h₁ + t·h₂ < h₂ ⟺ (1−t)(h₁−h₂) < 0
    have hpos : 0 < 1 - t := by linarith
    have hmul : (1 - t) * (sideH₁ α₁ β₁ u - sideH₂ α₂ β₂ u) < 0 := by
      exact mul_neg_of_pos_of_neg hpos (by linarith)
    nlinarith

/-- **Distinct parameters give disjoint chords**: for `α₁ < α₂`,
`β₁ < β₂`, distinct `t₁ ≠ t₂ ∈ (0,1)` and `u₁, u₂ ∈ [0,1]`, the chord
points differ.  Equality would force `u₁ = u₂` (equal `x0`), then the
height equality `(t₂ − t₁)·(h₂(u) − h₁(u)) = 0` contradicts `t₁ ≠ t₂`
and `h₁(u) < h₂(u)`. -/
theorem genChord_disjoint (hα : α₁ < α₂) (hβ : β₁ < β₂)
    {t₁ t₂ u₁ u₂ : ℝ} (ht₁ : t₁ ∈ Set.Ioo 0 1) (ht₂ : t₂ ∈ Set.Ioo 0 1)
    (hu₁ : u₁ ∈ Set.Icc 0 1) (hu₂ : u₂ ∈ Set.Icc 0 1) (htne : t₁ ≠ t₂) :
    genP α₁ β₁ α₂ β₂ t₁ u₁ ≠ genP α₁ β₁ α₂ β₂ t₂ u₂ := by
  intro hEq
  have hc := congrArg (fun x : ℝ² => x 0) hEq
  have hu : u₁ = u₂ := by simpa [genP] using hc
  have hlt := sideH_lt hα hβ hu₂
  have hc1 := congrArg (fun x : ℝ² => x 1) hEq
  have hc1' : (1 - t₁) * sideH₁ α₁ β₁ u₁ + t₁ * sideH₂ α₂ β₂ u₁ =
      (1 - t₂) * sideH₁ α₁ β₁ u₂ + t₂ * sideH₂ α₂ β₂ u₂ := by
    simpa [genP] using hc1
  -- rearrange: after u₁ = u₂ the height equality gives (t₂−t₁)(H₁−H₂)=0
  let H₁ : ℝ := sideH₁ α₁ β₁ u₁
  let H₂ : ℝ := sideH₂ α₂ β₂ u₁
  have hc1u : (1 - t₁) * H₁ + t₁ * H₂ = (1 - t₂) * H₁ + t₂ * H₂ := by
    simpa [H₁, H₂, hu] using hc1'
  have hm : (t₂ - t₁) * (H₁ - H₂) = 0 := by
    nlinarith
  have hd : H₁ - H₂ ≠ 0 := by
    have : H₁ < H₂ := by simpa [H₁, H₂, hu] using hlt
    linarith
  have ht12 : t₂ - t₁ = 0 := (mul_eq_zero.mp hm).resolve_right hd
  have ht₁₂ : t₁ = t₂ := by linarith
  exact htne ht₁₂

/-- Continuity of the left endpoint map (affine in `t`). -/
lemma continuous_genA (α₁ β₁ α₂ β₂ : ℝ) : Continuous (genA α₁ β₁ α₂ β₂) := by
  unfold genA genP
  fun_prop

/-- Continuity of the right endpoint map (affine in `t`). -/
lemma continuous_genB (α₁ β₁ α₂ β₂ : ℝ) : Continuous (genB α₁ β₁ α₂ β₂) := by
  unfold genB genP
  fun_prop

/-- Endpoint values at `t = 0` (the side `L₁`). -/
lemma genA_zero (α₁ β₁ α₂ β₂ : ℝ) : genA α₁ β₁ α₂ β₂ 0 = !₂[0, α₁] := by
  ext i <;> fin_cases i <;> simp [genA, genP, sideH₁, sideH₂]

/-- Endpoint values at `t = 1` (the side `L₂`). -/
lemma genA_one (α₁ β₁ α₂ β₂ : ℝ) : genA α₁ β₁ α₂ β₂ 1 = !₂[0, α₂] := by
  ext i <;> fin_cases i <;> simp [genA, genP, sideH₁, sideH₂]

/-- Endpoint values at `t = 0` (the side `L₁`). -/
lemma genB_zero (α₁ β₁ α₂ β₂ : ℝ) : genB α₁ β₁ α₂ β₂ 0 = !₂[1, β₁] := by
  ext i <;> fin_cases i <;> simp [genB, genP, sideH₁, sideH₂]

/-- Endpoint values at `t = 1` (the side `L₂`). -/
lemma genB_one (α₁ β₁ α₂ β₂ : ℝ) : genB α₁ β₁ α₂ β₂ 1 = !₂[1, β₂] := by
  ext i <;> fin_cases i <;> simp [genB, genP, sideH₁, sideH₂]

/-- Endpoint limit: as `t → 0` the left endpoint tends to `(0, α₁)`. -/
theorem genA_tendsto_zero (α₁ β₁ α₂ β₂ : ℝ) :
    Tendsto (genA α₁ β₁ α₂ β₂) (𝓝 0) (𝓝 (!₂[0, α₁])) := by
  have h : ContinuousAt (genA α₁ β₁ α₂ β₂) 0 := (continuous_genA α₁ β₁ α₂ β₂).continuousAt
  have hval : genA α₁ β₁ α₂ β₂ 0 = !₂[0, α₁] := genA_zero α₁ β₁ α₂ β₂
  simpa [hval] using h.tendsto

/-- Endpoint limit: as `t → 1` the left endpoint tends to `(0, α₂)`. -/
theorem genA_tendsto_one (α₁ β₁ α₂ β₂ : ℝ) :
    Tendsto (genA α₁ β₁ α₂ β₂) (𝓝 1) (𝓝 (!₂[0, α₂])) := by
  have h : ContinuousAt (genA α₁ β₁ α₂ β₂) 1 := (continuous_genA α₁ β₁ α₂ β₂).continuousAt
  have hval : genA α₁ β₁ α₂ β₂ 1 = !₂[0, α₂] := genA_one α₁ β₁ α₂ β₂
  simpa [hval] using h.tendsto

/-- Endpoint limit: as `t → 0` the right endpoint tends to `(1, β₁)`. -/
theorem genB_tendsto_zero (α₁ β₁ α₂ β₂ : ℝ) :
    Tendsto (genB α₁ β₁ α₂ β₂) (𝓝 0) (𝓝 (!₂[1, β₁])) := by
  have h : ContinuousAt (genB α₁ β₁ α₂ β₂) 0 := (continuous_genB α₁ β₁ α₂ β₂).continuousAt
  have hval : genB α₁ β₁ α₂ β₂ 0 = !₂[1, β₁] := genB_zero α₁ β₁ α₂ β₂
  simpa [hval] using h.tendsto

/-- Endpoint limit: as `t → 1` the right endpoint tends to `(1, β₂)`. -/
theorem genB_tendsto_one (α₁ β₁ α₂ β₂ : ℝ) :
    Tendsto (genB α₁ β₁ α₂ β₂) (𝓝 1) (𝓝 (!₂[1, β₂])) := by
  have h : ContinuousAt (genB α₁ β₁ α₂ β₂) 1 := (continuous_genB α₁ β₁ α₂ β₂).continuousAt
  have hval : genB α₁ β₁ α₂ β₂ 1 = !₂[1, β₂] := genB_one α₁ β₁ α₂ β₂
  simpa [hval] using h.tendsto

/-- **Centre condition**: the chord `genP t` crosses the centreline
`x0 = 1/2` at the convex-combined centre height
`(1−t)·h₁(1/2) + t·h₂(1/2)`. -/
lemma genP_half (α₁ β₁ α₂ β₂ t : ℝ) :
    (genP α₁ β₁ α₂ β₂ t (1 / 2)) 1 =
      (1 - t) * sideH₁ α₁ β₁ (1 / 2) + t * sideH₂ α₂ β₂ (1 / 2) := by
  simp [genP]

end Submission.PaperBand

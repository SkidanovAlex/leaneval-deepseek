import Submission.Work.FlatComp

open Filter Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-!
# Flat-leaf family over the centre-height interval: continuity & limits (FlatFamily)

`FlatComp` gives the per-height chord leaves of a `FlatSideData`
component and their interior properties (inside / centre / disjoint).  A
`BandFoliation`-style splice additionally needs the leaf family to be
CONTINUOUS in the centre height and to LIMIT to the two side chords at
the ends of the centre-height interval.  This file proves those facts at
the general `FlatSideData` level (pure algebra + topology over the green
`GeneralChord`/`FlatLeaf`/`FlatComp` blocks):

* **`leafT` is continuous** (`continuous_leafT`): the inverse side
  parameter `(y − c₁)/(c₂ − c₁)` is affine in `y` (denominator `c₂−c₁`,
  nonzero by `c_ne`);
* hence the endpoint maps are continuous (`continuous_leafA`/`leafB`,
  and the endpoint-HEIGHT functions `continuous_leafA1`/`leafB1` used by
  the `BandFoliation` `cont_left`/`cont_right` fields);
* **endpoint values at the interval ends** (`leafA_at_c₁`, `leafB_at_c₁`,
  `leafA_at_c₂`, `leafB_at_c₂`): the leaf at height `c₁` is the lower
  side chord `(0,α₁)→(1,β₁)` (i.e. `genA/genB` at `t=0`), and at height
  `c₂` the upper side chord `(0,α₂)→(1,β₂)`;
* **endpoint limits** (`leafA_tendsto_c₁`, `leafB_tendsto_c₁`, ...): as
  the centre height tends to `c₁`/`c₂` the leaf endpoints converge to the
  two side chords' endpoints (continuity of the endpoint map at the
  interval ends) — the boundary-matching ingredient of the splice;
* explicit **affine endpoint-height formulas** (`leafA1_formula`,
  `leafB1_formula`): `A1(y) = α₁ + (α₂−α₁)·(y−c₁)/(c₂−c₁)` etc. — the
  seam-interpolation form used when the side endpoints `(αᵢ,βᵢ)` come
  from the bordering U-leaves.

Build: `lake build Submission.Work.FlatFamily` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

namespace FlatSideData

variable (D : FlatSideData)

/-- The affine centre-height-to-parameter map is continuous: the
denominator `c₂ − c₁` is a nonzero constant. -/
lemma continuous_leafT_arg : Continuous (fun y : ℝ => (y - c₁ D) / (c₂ D - c₁ D)) := by
  have hf : Continuous (fun y : ℝ => y - c₁ D) := by fun_prop
  have hg : Continuous (fun y : ℝ => c₂ D - c₁ D) := continuous_const
  have hne : ∀ y : ℝ, c₂ D - c₁ D ≠ 0 := fun _ => c_ne D
  exact hf.div hg hne

/-- The inverse side parameter is continuous in the centre height. -/
lemma continuous_leafT : Continuous (fun y : ℝ => leafT D y) := by
  have hleaf : (fun y : ℝ => leafT D y) = fun y : ℝ => (y - c₁ D) / (c₂ D - c₁ D) := by
    funext y
    dsimp [leafT, flatLeafT, c₁, c₂, line₁, line₂]
  simpa [hleaf] using continuous_leafT_arg D

/-- The whole-leaf left endpoint map is continuous in the centre height. -/
lemma continuous_leafA : Continuous (fun y : ℝ => leafA D y) := by
  have h : (fun y : ℝ => leafA D y) =
      fun y : ℝ => genA D.α₁ D.β₁ D.α₂ D.β₂ (leafT D y) := by
    funext y
    rfl
  rw [h]
  exact (continuous_genA D.α₁ D.β₁ D.α₂ D.β₂).comp (continuous_leafT D)

/-- The whole-leaf right endpoint map is continuous in the centre height. -/
lemma continuous_leafB : Continuous (fun y : ℝ => leafB D y) := by
  have h : (fun y : ℝ => leafB D y) =
      fun y : ℝ => genB D.α₁ D.β₁ D.α₂ D.β₂ (leafT D y) := by
    funext y
    rfl
  rw [h]
  exact (continuous_genB D.α₁ D.β₁ D.α₂ D.β₂).comp (continuous_leafT D)

/-- Boundary coordinate of the left endpoint: `A(y)` lies on `x0 = 0`. -/
lemma leafA_left_coord (y : ℝ) : (leafA D y) 0 = 0 := by
  dsimp [leafA, genA]
  rw [genP_coord0]

/-- Boundary coordinate of the right endpoint: `B(y)` lies on `x0 = 1`. -/
lemma leafB_right_coord (y : ℝ) : (leafB D y) 0 = 1 := by
  dsimp [leafB, genB]
  rw [genP_coord0]

/-- **Endpoint value at the bottom of the interval**: the leaf at centre
height `c₁` is the lower side chord — its left endpoint is `(0, α₁)`. -/
lemma leafA_at_c₁ : leafA D (c₁ D) = !₂[0, D.α₁] := by
  have ht : leafT D (c₁ D) = 0 := leafT_c₁ D
  dsimp [leafA]
  rw [ht]
  exact genA_zero D.α₁ D.β₁ D.α₂ D.β₂

/-- **Endpoint value at the bottom of the interval**: the leaf at centre
height `c₁` is the lower side chord — its right endpoint is `(1, β₁)`. -/
lemma leafB_at_c₁ : leafB D (c₁ D) = !₂[1, D.β₁] := by
  have ht : leafT D (c₁ D) = 0 := leafT_c₁ D
  dsimp [leafB]
  rw [ht]
  exact genB_zero D.α₁ D.β₁ D.α₂ D.β₂

/-- **Endpoint value at the top of the interval**: the leaf at centre
height `c₂` is the upper side chord — its left endpoint is `(0, α₂)`. -/
lemma leafA_at_c₂ : leafA D (c₂ D) = !₂[0, D.α₂] := by
  have ht : leafT D (c₂ D) = 1 := leafT_c₂ D
  dsimp [leafA]
  rw [ht]
  exact genA_one D.α₁ D.β₁ D.α₂ D.β₂

/-- **Endpoint value at the top of the interval**: the leaf at centre
height `c₂` is the upper side chord — its right endpoint is `(1, β₂)`. -/
lemma leafB_at_c₂ : leafB D (c₂ D) = !₂[1, D.β₂] := by
  have ht : leafT D (c₂ D) = 1 := leafT_c₂ D
  dsimp [leafB]
  rw [ht]
  exact genB_one D.α₁ D.β₁ D.α₂ D.β₂

/-- **Affine left-endpoint-height formula**: the left endpoint height is
the seam interpolation `α₁ + (α₂−α₁)·t(y)` with `t(y) = (y−c₁)/(c₂−c₁)`. -/
lemma leafA1_formula (y : ℝ) :
    (leafA D y) 1 = D.α₁ + (D.α₂ - D.α₁) * ((y - c₁ D) / (c₂ D - c₁ D)) := by
  have ht : leafT D y = (y - c₁ D) / (c₂ D - c₁ D) := by
    dsimp [leafT, flatLeafT, c₁, c₂, line₁, line₂]
  dsimp [leafA, genA]
  rw [genP_coord1]
  have h0₁ : sideH₁ D.α₁ D.β₁ 0 = D.α₁ := by simp [sideH₁]
  have h0₂ : sideH₂ D.α₂ D.β₂ 0 = D.α₂ := by simp [sideH₂]
  rw [h0₁, h0₂]
  rw [ht]
  ring

/-- **Affine right-endpoint-height formula**: the right endpoint height is
the seam interpolation `β₁ + (β₂−β₁)·t(y)` with `t(y) = (y−c₁)/(c₂−c₁)`. -/
lemma leafB1_formula (y : ℝ) :
    (leafB D y) 1 = D.β₁ + (D.β₂ - D.β₁) * ((y - c₁ D) / (c₂ D - c₁ D)) := by
  have ht : leafT D y = (y - c₁ D) / (c₂ D - c₁ D) := by
    dsimp [leafT, flatLeafT, c₁, c₂, line₁, line₂]
  dsimp [leafB, genB]
  rw [genP_coord1]
  have h1₁ : sideH₁ D.α₁ D.β₁ 1 = D.β₁ := by simp [sideH₁]
  have h1₂ : sideH₂ D.α₂ D.β₂ 1 = D.β₂ := by simp [sideH₂]
  rw [h1₁, h1₂]
  rw [ht]
  ring

/-- The left endpoint HEIGHT is continuous in the centre height (the
`BandFoliation.cont_left` ingredient on a flat interval). -/
lemma continuous_leafA1 : Continuous (fun y : ℝ => (leafA D y) 1) := by
  have hf : (fun y : ℝ => (leafA D y) 1) =
      fun y : ℝ => D.α₁ + (D.α₂ - D.α₁) * ((y - c₁ D) / (c₂ D - c₁ D)) := by
    funext y
    exact leafA1_formula D y
  rw [hf]
  have hg : Continuous (fun y : ℝ => (D.α₂ - D.α₁) * ((y - c₁ D) / (c₂ D - c₁ D))) := by
    exact continuous_const.mul (continuous_leafT_arg D)
  exact continuous_const.add hg

/-- The right endpoint HEIGHT is continuous in the centre height (the
`BandFoliation.cont_right` ingredient on a flat interval). -/
lemma continuous_leafB1 : Continuous (fun y : ℝ => (leafB D y) 1) := by
  have hf : (fun y : ℝ => (leafB D y) 1) =
      fun y : ℝ => D.β₁ + (D.β₂ - D.β₁) * ((y - c₁ D) / (c₂ D - c₁ D)) := by
    funext y
    exact leafB1_formula D y
  rw [hf]
  have hg : Continuous (fun y : ℝ => (D.β₂ - D.β₁) * ((y - c₁ D) / (c₂ D - c₁ D))) := by
    exact continuous_const.mul (continuous_leafT_arg D)
  exact continuous_const.add hg

/-- **Limit at the bottom of the interval**: as the centre height tends to
`c₁`, the left endpoint converges to the lower side's left endpoint
`(0, α₁)`. -/
lemma leafA_tendsto_c₁ :
    Tendsto (fun y : ℝ => leafA D y) (𝓝 (c₁ D)) (𝓝 (!₂[0, D.α₁])) := by
  have hcont : ContinuousAt (fun y : ℝ => leafA D y) (c₁ D) :=
    (continuous_leafA D).continuousAt
  have hval : leafA D (c₁ D) = !₂[0, D.α₁] := leafA_at_c₁ D
  simpa [hval] using hcont.tendsto

/-- **Limit at the bottom of the interval**: as the centre height tends to
`c₁`, the right endpoint converges to the lower side's right endpoint
`(1, β₁)`. -/
lemma leafB_tendsto_c₁ :
    Tendsto (fun y : ℝ => leafB D y) (𝓝 (c₁ D)) (𝓝 (!₂[1, D.β₁])) := by
  have hcont : ContinuousAt (fun y : ℝ => leafB D y) (c₁ D) :=
    (continuous_leafB D).continuousAt
  have hval : leafB D (c₁ D) = !₂[1, D.β₁] := leafB_at_c₁ D
  simpa [hval] using hcont.tendsto

/-- **Limit at the top of the interval**: as the centre height tends to
`c₂`, the left endpoint converges to the upper side's left endpoint
`(0, α₂)`. -/
lemma leafA_tendsto_c₂ :
    Tendsto (fun y : ℝ => leafA D y) (𝓝 (c₂ D)) (𝓝 (!₂[0, D.α₂])) := by
  have hcont : ContinuousAt (fun y : ℝ => leafA D y) (c₂ D) :=
    (continuous_leafA D).continuousAt
  have hval : leafA D (c₂ D) = !₂[0, D.α₂] := leafA_at_c₂ D
  simpa [hval] using hcont.tendsto

/-- **Limit at the top of the interval**: as the centre height tends to
`c₂`, the right endpoint converges to the upper side's right endpoint
`(1, β₂)`. -/
lemma leafB_tendsto_c₂ :
    Tendsto (fun y : ℝ => leafB D y) (𝓝 (c₂ D)) (𝓝 (!₂[1, D.β₂])) := by
  have hcont : ContinuousAt (fun y : ℝ => leafB D y) (c₂ D) :=
    (continuous_leafB D).continuousAt
  have hval : leafB D (c₂ D) = !₂[1, D.β₂] := leafB_at_c₂ D
  simpa [hval] using hcont.tendsto

/-- **Whole-chord limit at the bottom**: the leaf at centre height `y`
converges (as `y → c₁`) to the lower side chord, pointwise in the segment
parameter `u`. -/
lemma leafP_tendsto_c₁ (u : ℝ) :
    Tendsto (fun y : ℝ => leafP D y u) (𝓝 (c₁ D))
      (𝓝 (genP D.α₁ D.β₁ D.α₂ D.β₂ 0 u)) := by
  have hcgu : Continuous (fun t : ℝ => genP D.α₁ D.β₁ D.α₂ D.β₂ t u) := by
    dsimp [genP]
    fun_prop
  have hc : ContinuousAt (fun y : ℝ => genP D.α₁ D.β₁ D.α₂ D.β₂ (leafT D y) u) (c₁ D) :=
    hcgu.continuousAt.comp (continuous_leafT D).continuousAt
  have h : (fun y : ℝ => leafP D y u) =
      fun y : ℝ => genP D.α₁ D.β₁ D.α₂ D.β₂ (leafT D y) u := by
    funext y
    rfl
  rw [h]
  have hval : leafT D (c₁ D) = 0 := leafT_c₁ D
  simpa [hval] using hc.tendsto

/-- **Whole-chord limit at the top**: the leaf at centre height `y`
converges (as `y → c₂`) to the upper side chord, pointwise in the segment
parameter `u`. -/
lemma leafP_tendsto_c₂ (u : ℝ) :
    Tendsto (fun y : ℝ => leafP D y u) (𝓝 (c₂ D))
      (𝓝 (genP D.α₁ D.β₁ D.α₂ D.β₂ 1 u)) := by
  have hcgu : Continuous (fun t : ℝ => genP D.α₁ D.β₁ D.α₂ D.β₂ t u) := by
    dsimp [genP]
    fun_prop
  have hc : ContinuousAt (fun y : ℝ => genP D.α₁ D.β₁ D.α₂ D.β₂ (leafT D y) u) (c₂ D) :=
    hcgu.continuousAt.comp (continuous_leafT D).continuousAt
  have h : (fun y : ℝ => leafP D y u) =
      fun y : ℝ => genP D.α₁ D.β₁ D.α₂ D.β₂ (leafT D y) u := by
    funext y
    rfl
  rw [h]
  have hval : leafT D (c₂ D) = 1 := leafT_c₂ D
  simpa [hval] using hc.tendsto

end FlatSideData

end Submission.PaperBand

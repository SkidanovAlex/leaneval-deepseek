import Submission.Work.NoVerticalKernel
import Submission.Work.NoFlatStopODE

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
open InnerProductGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# The canonical U-bend through a point (Prop main0, U-part)

Paper §2.1 Lemma `mc`: each `p ∈ U = {dN ≠ 0}` lies in a unique bend
`γ ⊂ U`.  A bend is a straight segment whose interior is a kernel segment of
the band (`dN = 0` along its direction at every interior point) and whose
image is straight (`f` affine, normal constant).

## Established facts (all green, zero sorry)
* `NoVerticalKernel.vertical_kernel_impossible`: no vertical kernel
  direction at an interior point of `U` (affine-unbounded contradiction via
  `f_strip_bounded`); `NoVerticalKernel.exists_crossing_kernel_direction`:
  at every `x ∈ U` there is a kernel direction `w` with `w 0 ≠ 0`.
* `bend_through_U_point`: crossing kernel direction + maximal open interval
  `(α,β) ∋ 0` with interior in `stripInterior ∩ U`, kernel condition, and
  boundary endpoints (assembly of the above with
  `NoFlatStopODE.maximal_kernel_interval_in_U`).
* `interval_full_of_boundary_stops` + `maximal_kernel_segment_full`: the
  maximal interval is **full** — it equals exactly the set of parameters at
  which the ray lies in the strip interior (the whole of
  `line ∩ stripInterior`); endpoints sit on the boundary lines.
* `kernelSegmentSet`/`lineInteriorSet`; `kernelSegmentSet_eq_lineInterior`;
  `full_segment_kernel_and_U`: kernel condition (`dN f y w = 0`) and
  `dN f y ≠ 0` hold at **every** point `y` of the whole line interior.
* `lineInterior_kernel_and_U`, `ubend_disjoint_or_equal` (two full kernel
  segments of `U` that meet coincide), `ubend_unique_through_point` (the
  bend through `x` is independent of the chosen crossing kernel direction),
  `u_bend_canonical` (Lemma `mc` U-part in final form: through each `U`-point
  a maximal kernel interval equal to the full line interior, with kernel and
  `U` along it).
* Canonical object: `uBendDir`/`uBendSet` (the bend through `x` as a set of
  preimage points = full kernel-line interior), with `uBendDir_spec`,
  `uBendSet_mem`, `uBendSet_subset_U_and_kernel`,
  `uBendSet_is_full_kernel_segment`; uniqueness (`mem_kernelSegmentSet_self`,
  `u_bend_canonical_unique`: any two maximal full kernel segments through
  `x` coincide; `uBendSet_eq_any_full_segment`: the canonical bend equals
  any of them) — Lemma `mc` (U-part, existence + uniqueness) is thereby
  complete at the segment level.

## Remaining for Prop main0 (Paper §2.1)
1. *Flat regions of positive area*: components of `Ω−U` with nonempty
   interior are flat trapezoids (Gauss map constant; two opposite sides
   bends, two on `∂Ω`), foliated by their own parallel/coincident chords —
   `FlatRegions`/`FlatBends` provide the flat patches; the trapezoid-edge
   structure and canonical interpolation remain.
2. *Continuity of the U-foliation*: the disjoint maximal segments of `U`
   (through each `U`-point, canonical by `ubend_unique_through_point`) vary
   continuously and, with the flat chords, form the continuous foliation of
   the band; then descend to the quotient `Band a` (centreline
   intersection, parametrisation by `ℝ/aℤ`) — the input of Lemma T.
-/

noncomputable section
namespace Submission.PaperBand

/-- **A canonical U-bend through every point of `U`**: at an interior point
`x` with `dN f x ≠ 0` there is a nonzero crossing kernel direction `w`
(`w 0 ≠ 0`) and a maximal open parameter interval `(α,β)` with `α < 0 < β`
such that the whole open segment `{x + s•w}` lies in `stripInterior ∩ U`,
is a kernel segment (`dN f (·) w = 0` along it), and both endpoints lie on
the boundary lines of the strip. -/
theorem bend_through_U_point {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hU0 : dN f x ≠ 0) :
    ∃ w : ℝ², w ≠ 0 ∧ w 0 ≠ 0 ∧ dN f x w = 0 ∧
      ∃ α β : ℝ, α < 0 ∧ 0 < β ∧
        (∀ s ∈ Set.Ioo α β,
          x + s • w ∈ stripInterior ∧ dN f (x + s • w) w = 0) ∧
        (∀ s ∈ Set.Ioo α β, dN f (x + s • w) ≠ 0) ∧
        ((x + β • w) 0 = 0 ∨ (x + β • w) 0 = 1) ∧
        ((x + α • w) 0 = 0 ∨ (x + α • w) 0 = 1) := by
  rcases exists_crossing_kernel_direction hf ha hx hU0 with ⟨w, hkw, hwne, hw0⟩
  rcases maximal_kernel_interval_in_U hf hx hU0 hkw hwne hw0 with ⟨α, β, hα, hβ, hseg, hU, hβb, hαb⟩
  exact ⟨w, hwne, hw0, hkw, α, β, hα, hβ, hseg, hU, hβb, hαb⟩

/-- The `0`-coordinate along an affine ray is affine in the parameter. -/
lemma coord0_add {x w : ℝ²} {s t : ℝ} :
    (x + (s + t) • w) 0 = (x + s • w) 0 + t * w 0 := by
  rw [ray_coord0, ray_coord0]
  ring

/-- The `0`-coordinate is **strictly increasing** along a ray with positive
`0`-component of the direction. -/
lemma coord0_lt_of_lt_pos {x w : ℝ²} {s t : ℝ} (hwpos : 0 < w 0) (hst : s < t) :
    (x + s • w) 0 < (x + t • w) 0 := by
  have hd : (x + t • w) 0 - (x + s • w) 0 > 0 := by
    calc
      (x + t • w) 0 - (x + s • w) 0 = (t - s) * w 0 := by
        rw [ray_coord0, ray_coord0]
        ring
      _ > 0 := mul_pos (by linarith) hwpos
  linarith

/-- The `0`-coordinate is **strictly decreasing** along a ray with negative
`0`-component of the direction. -/
lemma coord0_lt_of_lt_neg {x w : ℝ²} {s t : ℝ} (hwneg : w 0 < 0) (hst : s < t) :
    (x + t • w) 0 < (x + s • w) 0 := by
  have hd : (x + s • w) 0 - (x + t • w) 0 > 0 := by
    calc
      (x + s • w) 0 - (x + t • w) 0 = (s - t) * w 0 := by
        rw [ray_coord0, ray_coord0]
        ring
      _ > 0 := mul_pos_of_neg_of_neg (by linarith : s - t < 0) hwneg
  linarith

/-- Non-strict version for a positive `0`-component. -/
lemma coord0_le_of_le_pos {x w : ℝ²} {s t : ℝ} (hwpos : 0 < w 0) (hst : s ≤ t) :
    (x + s • w) 0 ≤ (x + t • w) 0 := by
  by_cases h : s = t
  · rw [h]
  · have hlt : s < t := lt_of_le_of_ne hst h
    exact le_of_lt (coord0_lt_of_lt_pos hwpos hlt)

/-- Non-strict version for a negative `0`-component. -/
lemma coord0_le_of_le_neg {x w : ℝ²} {s t : ℝ} (hwneg : w 0 < 0) (hst : s ≤ t) :
    (x + t • w) 0 ≤ (x + s • w) 0 := by
  by_cases h : s = t
  · rw [h]
  · have hlt : s < t := lt_of_le_of_ne hst h
    exact le_of_lt (coord0_lt_of_lt_neg hwneg hlt)

/-- **Maximal intervals reach the boundary and cover the whole interior of
their line**: if `(α,β)` (α<0<β) is a kernel interval in crossing direction
`w₀` whose endpoints lie on the strip boundary lines, then the interval
consists exactly of the parameters at which the ray lies in the interior of
the strip. -/
lemma interval_full_of_boundary_stops {x₀ w₀ : ℝ²} {α β : ℝ}
    (hα : α < 0) (hβ : 0 < β) (hw0 : w₀ 0 ≠ 0)
    (hseg : ∀ s ∈ Set.Ioo α β, x₀ + s • w₀ ∈ stripInterior)
    (hαb : (x₀ + α • w₀) 0 = 0 ∨ (x₀ + α • w₀) 0 = 1)
    (hβb : (x₀ + β • w₀) 0 = 0 ∨ (x₀ + β • w₀) 0 = 1) :
    ∀ s : ℝ, s ∈ Set.Ioo α β ↔ x₀ + s • w₀ ∈ stripInterior := by
  intro s
  constructor
  · intro hs
    exact hseg s hs
  · intro hs
    rw [Set.mem_Ioo]
    have hx0 : x₀ ∈ stripInterior := by
      simpa using (hseg 0 (by rw [Set.mem_Ioo]; exact ⟨hα, hβ⟩))
    have hx₀0 : 0 < x₀ 0 ∧ x₀ 0 < 1 := by
      change x₀ 0 ∈ Set.Ioo (0 : ℝ) 1 at hx0
      exact hx0
    have hc0 : (x₀ + (0 : ℝ) • w₀) 0 = x₀ 0 := by simp
    have hcs : (x₀ + s • w₀) 0 ∈ Set.Ioo (0 : ℝ) 1 := by
      change (x₀ + s • w₀) 0 ∈ Set.Ioo (0 : ℝ) 1 at hs
      exact hs
    rcases hcs with ⟨hs0, hs1⟩
    by_cases hpos : 0 < w₀ 0
    · -- increasing case: c(α) = 0, c(β) = 1
      have hca0 : (x₀ + α • w₀) 0 = 0 := by
        rcases hαb with h | h
        · exact h
        · have hlt : (x₀ + α • w₀) 0 < (x₀ + (0 : ℝ) • w₀) 0 := coord0_lt_of_lt_pos hpos hα
          rw [hc0] at hlt
          linarith
      have hcb1 : (x₀ + β • w₀) 0 = 1 := by
        rcases hβb with h | h
        · have hgt : (x₀ + (0 : ℝ) • w₀) 0 < (x₀ + β • w₀) 0 := coord0_lt_of_lt_pos hpos hβ
          rw [hc0] at hgt
          linarith
        · exact h
      have hsα : α < s := by
        by_contra hnot
        have hsle : s ≤ α := le_of_not_gt hnot
        have hmono : (x₀ + s • w₀) 0 ≤ (x₀ + α • w₀) 0 := coord0_le_of_le_pos hpos hsle
        rw [hca0] at hmono
        linarith
      have hsβ : s < β := by
        by_contra hnot
        have hβs : β ≤ s := le_of_not_gt hnot
        have hmono : (x₀ + β • w₀) 0 ≤ (x₀ + s • w₀) 0 := coord0_le_of_le_pos hpos hβs
        rw [hcb1] at hmono
        linarith
      exact ⟨hsα, hsβ⟩
    · -- decreasing case: c(α) = 1, c(β) = 0
      have hwneg : w₀ 0 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (by
        intro hz
        exact hw0 hz)
      have hca1 : (x₀ + α • w₀) 0 = 1 := by
        rcases hαb with h | h
        · have hgt : (x₀ + (0 : ℝ) • w₀) 0 < (x₀ + α • w₀) 0 := coord0_lt_of_lt_neg hwneg hα
          rw [hc0] at hgt
          linarith
        · exact h
      have hcb0 : (x₀ + β • w₀) 0 = 0 := by
        rcases hβb with h | h
        · exact h
        · have hlt : (x₀ + β • w₀) 0 < (x₀ + (0 : ℝ) • w₀) 0 := coord0_lt_of_lt_neg hwneg hβ
          rw [hc0] at hlt
          linarith
      have hsα : α < s := by
        by_contra hnot
        have hsle : s ≤ α := le_of_not_gt hnot
        have hmono : (x₀ + α • w₀) 0 ≤ (x₀ + s • w₀) 0 := coord0_le_of_le_neg hwneg hsle
        rw [hca1] at hmono
        linarith
      have hsβ : s < β := by
        by_contra hnot
        have hβs : β ≤ s := le_of_not_gt hnot
        have hmono : (x₀ + s • w₀) 0 ≤ (x₀ + β • w₀) 0 := coord0_le_of_le_neg hwneg hβs
        rw [hcb0] at hmono
        linarith
      exact ⟨hsα, hsβ⟩

/-- **The maximal kernel segment is the full interior part of its line**: a
maximal kernel interval in a crossing direction `w₀` through a `U`-point
consists exactly of the parameters at which the ray is in the interior of the
strip — it covers all of `line ∩ stripInterior` and its endpoints are on the
strip boundary lines. -/
theorem maximal_kernel_segment_full {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x₀ w₀ : ℝ²} (hx₀ : x₀ ∈ stripInterior) (hdN₀ : dN f x₀ ≠ 0)
    (hker₀ : dN f x₀ w₀ = 0) (hw₀ : w₀ ≠ 0) (hw0 : w₀ 0 ≠ 0) :
    ∃ α β : ℝ, α < 0 ∧ 0 < β ∧
      (∀ s : ℝ, s ∈ Set.Ioo α β ↔ x₀ + s • w₀ ∈ stripInterior) ∧
      (∀ s ∈ Set.Ioo α β, dN f (x₀ + s • w₀) w₀ = 0) ∧
      (∀ s ∈ Set.Ioo α β, dN f (x₀ + s • w₀) ≠ 0) := by
  rcases maximal_kernel_interval_in_U hf hx₀ hdN₀ hker₀ hw₀ hw0 with ⟨α, β, hα, hβ, hseg, hU, hβb, hαb⟩
  refine ⟨α, β, hα, hβ, ?_, ?_, ?_⟩
  · exact interval_full_of_boundary_stops hα hβ hw0 (fun s hs => (hseg s hs).1) hαb hβb
  · intro s hs
    exact (hseg s hs).2
  · intro s hs
    exact hU s hs

/-- The set of points of the open kernel segment `{x + s • w | α < s < β}`. -/
def kernelSegmentSet (x w : ℝ²) (α β : ℝ) : Set ℝ² :=
  {y | ∃ s ∈ Set.Ioo α β, y = x + s • w}

/-- The interior of the line through `x` in direction `w` inside the strip:
`stripInterior ∩ (x + ℝw)`. -/
def lineInteriorSet (x w : ℝ²) : Set ℝ² :=
  {y | y ∈ stripInterior ∧ ∃ s : ℝ, y = x + s • w}

/-- A maximal kernel segment (full interval) is exactly the interior part of
its line inside the strip. -/
theorem kernelSegmentSet_eq_lineInterior {x w : ℝ²} {α β : ℝ}
    (hfull : ∀ s : ℝ, s ∈ Set.Ioo α β ↔ x + s • w ∈ stripInterior) :
    kernelSegmentSet x w α β = lineInteriorSet x w := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨s, hs, hEq⟩
    constructor
    · have hpt : x + s • w ∈ stripInterior := (hfull s).1 hs
      rwa [hEq]
    · exact ⟨s, hEq⟩
  · intro h
    rcases h with ⟨hy, s, hEq⟩
    have hy' : x + s • w ∈ stripInterior := by simpa [hEq] using hy
    have hs : s ∈ Set.Ioo α β := (hfull s).2 hy'
    exact ⟨s, hs, hEq⟩

/-- Every point of the interior of a full kernel segment lies in `U` and has
the segment direction in its kernel — the kernel condition propagates along
the whole line. -/
theorem full_segment_kernel_and_U {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x₀ w₀ : ℝ²} (hx₀ : x₀ ∈ stripInterior) (hdN₀ : dN f x₀ ≠ 0)
    (hker₀ : dN f x₀ w₀ = 0) (hw₀ : w₀ ≠ 0) (hw0 : w₀ 0 ≠ 0) :
    ∃ α β : ℝ, α < 0 ∧ 0 < β ∧
      kernelSegmentSet x₀ w₀ α β = lineInteriorSet x₀ w₀ ∧
      (∀ s ∈ Set.Ioo α β, dN f (x₀ + s • w₀) w₀ = 0) ∧
      (∀ s ∈ Set.Ioo α β, dN f (x₀ + s • w₀) ≠ 0) := by
  rcases maximal_kernel_segment_full hf hx₀ hdN₀ hker₀ hw₀ hw0 with ⟨α, β, hα, hβ, hfull, hk, hU⟩
  refine ⟨α, β, hα, hβ, ?_, hk, hU⟩
  exact kernelSegmentSet_eq_lineInterior hfull


/-- Translating the base point of a line along itself does not change the
line-interior set. -/
lemma lineInteriorSet_shift {x y w : ℝ²} (h : ∃ s : ℝ, y = x + s • w) :
    lineInteriorSet x w = lineInteriorSet y w := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hpI, s, hEq⟩
    rcases h with ⟨t, ht⟩
    constructor
    · exact hpI
    · refine ⟨s - t, ?_⟩
      calc
        p = x + s • w := hEq
        _ = (x + t • w) + (s - t) • w := by
          calc
            x + s • w = x + (t + (s - t)) • w := by rw [show t + (s - t) = s by ring]
            _ = x + (t • w + (s - t) • w) := by rw [← add_smul]
            _ = (x + t • w) + (s - t) • w := by rw [← add_assoc]
        _ = y + (s - t) • w := by rw [ht]
  · intro hp
    rcases hp with ⟨hpI, s, hEq⟩
    -- p = y + s•w, y = x + t•w
    rcases h with ⟨t, ht⟩
    constructor
    · exact hpI
    · refine ⟨s + t, ?_⟩
      calc
        p = y + s • w := hEq
        _ = (x + t • w) + s • w := by rw [ht]
        _ = x + (t + s) • w := by
          calc
            (x + t • w) + s • w = x + (t • w + s • w) := by rw [add_assoc]
            _ = x + (t + s) • w := by rw [add_smul]
        _ = x + (s + t) • w := by rw [show t + s = s + t by ring]

/-- Scaling the direction of a line by a nonzero factor does not change the
line-interior set. -/
lemma lineInteriorSet_scale {x w v : ℝ²} (h : ∃ c : ℝ, c ≠ 0 ∧ w = c • v) :
    lineInteriorSet x w = lineInteriorSet x v := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hpI, s, hEq⟩
    rcases h with ⟨c, hcne, hw⟩
    constructor
    · exact hpI
    · refine ⟨s * c, ?_⟩
      calc
        p = x + s • w := hEq
        _ = x + s • (c • v) := by rw [hw]
        _ = x + (s * c) • v := by rw [smul_smul]
  · intro hp
    rcases hp with ⟨hpI, s, hEq⟩
    rcases h with ⟨c, hcne, hw⟩
    constructor
    · exact hpI
    · have hv : v = c⁻¹ • w := by
        calc
          v = (c⁻¹ * c) • v := by
            rw [inv_mul_cancel₀ hcne]
            simp
          _ = c⁻¹ • (c • v) := by rw [← smul_smul]
          _ = c⁻¹ • w := by rw [← hw]
      refine ⟨s * c⁻¹, ?_⟩
      calc
        p = x + s • v := hEq
        _ = x + s • (c⁻¹ • w) := by rw [hv]
        _ = x + (s * c⁻¹) • w := by rw [smul_smul]

/-- A point `p` of `lineInteriorSet x w` lies in `U` and has the line
direction `w` in its kernel — provided `w` is a crossing kernel direction at
the `U`-point `x` (so the maximal kernel segment covers the whole
line interior). -/
theorem lineInterior_kernel_and_U {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x w : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0)
    (hker : dN f x w = 0) (hwne : w ≠ 0) (hw0 : w 0 ≠ 0) :
    (∀ y ∈ lineInteriorSet x w, dN f y ≠ 0) ∧
      (∀ y ∈ lineInteriorSet x w, dN f y w = 0) := by
  rcases full_segment_kernel_and_U hf hx hdN hker hwne hw0 with ⟨α, β, hα, hβ, heq, hk, hU⟩
  constructor
  · intro y hy
    have hyseg : y ∈ kernelSegmentSet x w α β := by rwa [heq]
    rcases hyseg with ⟨s, hs, hyEq⟩
    rw [hyEq]
    exact hU s hs
  · intro y hy
    have hyseg : y ∈ kernelSegmentSet x w α β := by rwa [heq]
    rcases hyseg with ⟨s, hs, hyEq⟩
    rw [hyEq]
    exact hk s hs

/-- **Disjoint or equal**: two full kernel segments (line interiors in
crossing directions through `U`-points) that share an interior point of the
strip coincide as sets. -/
theorem ubend_disjoint_or_equal {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x₁ w₁ x₂ w₂ : ℝ²} (hx₁ : x₁ ∈ stripInterior) (hdN₁ : dN f x₁ ≠ 0)
    (hker₁ : dN f x₁ w₁ = 0) (hw₁ : w₁ ≠ 0) (hw₁0 : w₁ 0 ≠ 0)
    (hx₂ : x₂ ∈ stripInterior) (hdN₂ : dN f x₂ ≠ 0)
    (hker₂ : dN f x₂ w₂ = 0) (hw₂ : w₂ ≠ 0) (hw₂0 : w₂ 0 ≠ 0) :
    (∃ z : ℝ², z ∈ lineInteriorSet x₁ w₁ ∧ z ∈ lineInteriorSet x₂ w₂) →
    lineInteriorSet x₁ w₁ = lineInteriorSet x₂ w₂ := by
  intro hz
  rcases hz with ⟨z, hz₁, hz₂⟩
  have hk₁ := (lineInterior_kernel_and_U hf hx₁ hdN₁ hker₁ hw₁ hw₁0).2
  have hU₁ := (lineInterior_kernel_and_U hf hx₁ hdN₁ hker₁ hw₁ hw₁0).1
  have hk₂ := (lineInterior_kernel_and_U hf hx₂ hdN₂ hker₂ hw₂ hw₂0).2
  have hU₂ := (lineInterior_kernel_and_U hf hx₂ hdN₂ hker₂ hw₂ hw₂0).1
  have hzU : dN f z ≠ 0 := hU₁ z hz₁
  have hzI : z ∈ stripInterior := (hz₁.1)
  -- both directions are parallel at z (the kernel is a line)
  have hpar : ∃ c : ℝ, w₂ = c • w₁ := kernel_direction_parallel hf hzI hzU (hk₁ z hz₁) (hk₂ z hz₂) hw₁
  -- both lines pass through z, so both line-interior sets equal the one of z
  have hs₁ : ∃ s : ℝ, z = x₁ + s • w₁ := by
    rcases hz₁ with ⟨hI, s, hEq⟩
    exact ⟨s, hEq⟩
  have hs₂ : ∃ s : ℝ, z = x₂ + s • w₂ := by
    rcases hz₂ with ⟨hI, s, hEq⟩
    exact ⟨s, hEq⟩
  rcases hpar with ⟨c, hc⟩
  have hsc : ∃ d : ℝ, d ≠ 0 ∧ w₂ = d • w₁ := by
    by_cases hc0 : c = 0
    · have hw₂0 : w₂ = 0 := by
        calc
          w₂ = c • w₁ := hc
          _ = 0 := by rw [hc0]; simp
      exfalso
      exact hw₂ hw₂0
    · exact ⟨c, hc0, hc⟩
  calc
    lineInteriorSet x₁ w₁ = lineInteriorSet z w₁ := lineInteriorSet_shift hs₁
    _ = lineInteriorSet z w₂ := (lineInteriorSet_scale hsc).symm
    _ = lineInteriorSet x₂ w₂ := by rw [lineInteriorSet_shift hs₂]

/-- `x` itself lies in the line-interior set of any direction (it is the
`0`-parameter point). -/
lemma mem_lineInterior_self {x w : ℝ²} (hx : x ∈ stripInterior) : x ∈ lineInteriorSet x w := by
  constructor
  · exact hx
  · exact ⟨0, by simp⟩

/-- **The canonical bend through a `U`-point does not depend on the chosen
crossing kernel direction**: two crossing kernel directions at the same
interior `U`-point determine the same full kernel segment (same line
interior). -/
theorem ubend_unique_through_point {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0)
    {w₁ : ℝ²} (hker₁ : dN f x w₁ = 0) (hw₁ : w₁ ≠ 0) (hw₁0 : w₁ 0 ≠ 0)
    {w₂ : ℝ²} (hker₂ : dN f x w₂ = 0) (hw₂ : w₂ ≠ 0) (hw₂0 : w₂ 0 ≠ 0) :
    lineInteriorSet x w₁ = lineInteriorSet x w₂ := by
  apply ubend_disjoint_or_equal hf hx hdN hker₁ hw₁ hw₁0 hx hdN hker₂ hw₂ hw₂0
  exact ⟨x, mem_lineInterior_self (w := w₁) hx, mem_lineInterior_self (w := w₂) hx⟩

/-- **Lemma `mc` (U-part, exists + fullness)**: through every interior point
`x` of `U = {dN ≠ 0}` there is a crossing kernel direction `w` (`w 0 ≠ 0`)
and a maximal open parameter interval `(α,β)` (α<0<β) such that
  * the interval is exactly the set of parameters whose ray-point lies in the
    interior of the strip (`(α,β) = line ∩ stripInterior`),
  * every point of the open segment lies in `U` with `w` in its kernel,
  * the endpoints of the ray lie on the strip boundary lines. -/
theorem u_bend_canonical {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    ∃ w : ℝ², ∃ α β : ℝ,
      w ≠ 0 ∧ w 0 ≠ 0 ∧ dN f x w = 0 ∧ α < 0 ∧ 0 < β ∧
      (∀ s : ℝ, s ∈ Set.Ioo α β ↔ x + s • w ∈ stripInterior) ∧
      (∀ s ∈ Set.Ioo α β, dN f (x + s • w) w = 0) ∧
      (∀ s ∈ Set.Ioo α β, dN f (x + s • w) ≠ 0) := by
  rcases exists_crossing_kernel_direction hf ha hx hdN with ⟨w, hker, hwne, hw0⟩
  rcases maximal_kernel_segment_full hf hx hdN hker hwne hw0 with ⟨α, β, hα, hβ, hfull, hk, hU⟩
  exact ⟨w, α, β, hwne, hw0, hker, hα, hβ, hfull, hk, hU⟩

/-- A canonical crossing kernel direction at an interior point of `U`
(choice function for `exists_crossing_kernel_direction`). -/
noncomputable def uBendDir {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) : ℝ² :=
  Classical.choose (exists_crossing_kernel_direction hf ha hx hdN)

/-- The canonical bend (as a set of preimage points) through an interior
point of `U`: the full interior part of the kernel line of `x` inside the
strip. -/
noncomputable def uBendSet {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) : Set ℝ² :=
  lineInteriorSet x (uBendDir hf ha hx hdN)

/-- The canonical direction is a nonzero crossing kernel direction. -/
theorem uBendDir_spec {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    dN f x (uBendDir hf ha hx hdN) = 0 ∧ uBendDir hf ha hx hdN ≠ 0 ∧
      uBendDir hf ha hx hdN 0 ≠ 0 := by
  exact Classical.choose_spec (exists_crossing_kernel_direction hf ha hx hdN)

/-- `x` lies in its canonical bend. -/
theorem uBendSet_mem {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    x ∈ uBendSet hf ha hx hdN := by
  unfold uBendSet
  exact mem_lineInterior_self hx

/-- The canonical bend through `x` lies in the interior of `U`, and its
direction is a kernel direction at every one of its points. -/
theorem uBendSet_subset_U_and_kernel {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    (∀ y ∈ uBendSet hf ha hx hdN, dN f y ≠ 0) ∧
      (∀ y ∈ uBendSet hf ha hx hdN, dN f y (uBendDir hf ha hx hdN) = 0) := by
  rcases uBendDir_spec hf ha hx hdN with ⟨hker, hwne, hw0⟩
  unfold uBendSet
  exact lineInterior_kernel_and_U hf hx hdN hker hwne hw0

/-- The canonical bend set is the maximal kernel segment: it equals a
maximal parameter interval of its direction, with kernel condition and
`U`-membership along the whole interval (Lemma `mc` U-part, canonical form;
the interval is full, i.e. the whole line interior, by
`maximal_kernel_segment_full`). -/
theorem uBendSet_is_full_kernel_segment {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    ∃ α β : ℝ, α < 0 ∧ 0 < β ∧
      uBendSet hf ha hx hdN = kernelSegmentSet x (uBendDir hf ha hx hdN) α β ∧
      (∀ s ∈ Set.Ioo α β, dN f (x + s • (uBendDir hf ha hx hdN)) ≠ 0) ∧
      (∀ s ∈ Set.Ioo α β, dN f (x + s • (uBendDir hf ha hx hdN)) (uBendDir hf ha hx hdN) = 0) := by
  rcases uBendDir_spec hf ha hx hdN with ⟨hker, hwne, hw0⟩
  rcases maximal_kernel_segment_full hf hx hdN hker hwne hw0 with ⟨α, β, hα, hβ, hfull, hk, hU⟩
  refine ⟨α, β, hα, hβ, ?_, hU, hk⟩
  unfold uBendSet
  rw [kernelSegmentSet_eq_lineInterior hfull]

/-- Every maximal full kernel segment through `x` contains `x`. -/
lemma mem_kernelSegmentSet_self {x w : ℝ²} {α β : ℝ} (hα : α < 0) (hβ : 0 < β) :
    x ∈ kernelSegmentSet x w α β := by
  refine ⟨0, ?_, ?_⟩
  · rw [Set.mem_Ioo]
    exact ⟨hα, hβ⟩
  · simp

/-- **Lemma `mc` (U-part, uniqueness)**: any two maximal full kernel
segments through the same interior `U`-point coincide as point sets (the
geometric bend through `x` is unique; it is `uBendSet`). -/
theorem u_bend_canonical_unique {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0)
    {w₁ : ℝ²} {α₁ β₁ : ℝ} (hfull₁ : ∀ s : ℝ, s ∈ Set.Ioo α₁ β₁ ↔ x + s • w₁ ∈ stripInterior)
    (hker₁ : dN f x w₁ = 0) (hw₁ : w₁ ≠ 0) (hw₁0 : w₁ 0 ≠ 0)
    {w₂ : ℝ²} {α₂ β₂ : ℝ} (hfull₂ : ∀ s : ℝ, s ∈ Set.Ioo α₂ β₂ ↔ x + s • w₂ ∈ stripInterior)
    (hker₂ : dN f x w₂ = 0) (hw₂ : w₂ ≠ 0) (hw₂0 : w₂ 0 ≠ 0) :
    kernelSegmentSet x w₁ α₁ β₁ = kernelSegmentSet x w₂ α₂ β₂ := by
  rw [kernelSegmentSet_eq_lineInterior hfull₁, kernelSegmentSet_eq_lineInterior hfull₂]
  exact ubend_unique_through_point hf hx hdN hker₁ hw₁ hw₁0 hker₂ hw₂ hw₂0

/-- The canonical bend `uBendSet x` is (the point set of) any maximal full
kernel segment through `x`. -/
theorem uBendSet_eq_any_full_segment {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0)
    {w : ℝ²} {α β : ℝ} (hfull : ∀ s : ℝ, s ∈ Set.Ioo α β ↔ x + s • w ∈ stripInterior)
    (hker : dN f x w = 0) (hwne : w ≠ 0) (hw0 : w 0 ≠ 0) :
    uBendSet hf ha hx hdN = kernelSegmentSet x w α β := by
  rw [kernelSegmentSet_eq_lineInterior hfull]
  unfold uBendSet
  rcases uBendDir_spec hf ha hx hdN with ⟨hker₀, hwne₀, hw0₀⟩
  exact ubend_unique_through_point hf hx hdN hker₀ hwne₀ hw0₀ hker hwne hw0

end Submission.PaperBand
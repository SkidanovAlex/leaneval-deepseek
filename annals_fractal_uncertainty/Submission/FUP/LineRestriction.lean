import ChallengeDeps
import Submission.FUP.Metric

open FractalUncertainty
open MeasureTheory FourierTransform Metric
open scoped ENNReal

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-- Interval porosity of a subset of `ℝ` (the 1-dimensional instance of `PorousOnBalls`). -/
def PorousIntervals (ν α₀ α₁ : ℝ) (Z : Set ℝ) : Prop :=
  ∀ y : ℝ, ∀ R ∈ Set.Ioo α₀ α₁, ∃ x ∈ closedBall y (R / 2), closedBall x (ν * R) ∩ Z = ∅

/-- Distance between two points on an affine line `t ↦ p + t • v`. -/
lemma dist_add_smul (p v : ℝᵈ) (a b : ℝ) : dist (p + a • v) (p + b • v) = ‖v‖ * |a - b| := by
  rw [dist_eq_norm]
  calc
    ‖(p + a • v) - (p + b • v)‖ = ‖(a - b) • v‖ := by
      congr 1
      calc
        (p + a • v) - (p + b • v) = a • v - b • v := by abel
        _ = (a - b) • v := by rw [sub_smul]
    _ = ‖a - b‖ * ‖v‖ := by rw [norm_smul]
    _ = |a - b| * ‖v‖ := by rw [Real.norm_eq_abs]
    _ = ‖v‖ * |a - b| := by rw [mul_comm]

lemma smul_line (θ a b : ℝ) (v : ℝᵈ) :
    (1 - θ) • (a • v) + θ • (b • v) = ((1 - θ) * a + θ * b) • v := by
  rw [smul_smul, smul_smul, ← add_smul]

/-- The segment between `p + a•v` and `p + b•v` (with `a ≤ b`) is contained in the image of
`[a,b]` under `t ↦ p + t • v`. -/
lemma mem_segment_affine {p v : ℝᵈ} {a b : ℝ} (hab : a ≤ b) {x' : ℝᵈ}
    (hx' : x' ∈ segment ℝ (p + a • v) (p + b • v)) :
    ∃ t : ℝ, t ∈ Set.Icc a b ∧ x' = p + t • v := by
  rw [segment_eq_image] at hx'
  rcases hx' with ⟨θ, hθ, hEq⟩
  refine ⟨(1 - θ) * a + θ * b, ?_, ?_⟩
  · constructor
    · have hpos : 0 ≤ θ * (b - a) := mul_nonneg hθ.1 (sub_nonneg.mpr hab)
      nlinarith
    · have hpos : 0 ≤ (1 - θ) * (b - a) := mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hab)
      nlinarith
  · rw [← hEq]
    dsimp
    calc
      (1 - θ) • (p + a • v) + θ • (p + b • v)
          = ((1 - θ) • p + (1 - θ) • (a • v)) + (θ • p + θ • (b • v)) := by
            rw [smul_add, smul_add]
      _ = ((1 - θ) • p + θ • p) + ((1 - θ) • (a • v) + θ • (b • v)) := by ac_rfl
      _ = p + (((1 - θ) * a) • v + (θ * b) • v) := by
            rw [add_smul_self θ p, smul_smul, smul_smul]
      _ = p + (((1 - θ) * a + θ * b) • v) := by rw [← add_smul]

/-- Unit-speed affine lines are isometric: pullback along `γ(t) = p + t • v` (‖v‖ = 1). -/
lemma pullback_dist {p v : ℝᵈ} (hv : ‖v‖ = 1) (s t : ℝ) :
    dist (p + s • v) (p + t • v) = |s - t| := by
  rw [dist_add_smul, hv]
  simp

/-- If `Y` is `ν`-porous on lines, then the pullback of `Y` by a unit-speed affine line
`t ↦ p + t • v` is interval-porous in `ℝ` with the same parameters. -/
lemma pullback_porous_of_unitSpeed {ν α₀ α₁ : ℝ} {Y : Set ℝᵈ} (p v : ℝᵈ) (hv : ‖v‖ = 1)
    (hα₀ : 0 < α₀) (hY : PorousOnLines ν α₀ α₁ Y) :
    PorousIntervals ν α₀ α₁ ((fun t : ℝ => p + t • v) ⁻¹' Y) := by
  intro y R hR
  have hRpos : 0 < R := lt_trans hα₀ (Set.mem_Ioo.mp hR).1
  have hab : y - R / 2 ≤ y + R / 2 := by linarith
  have hd : dist (p + (y - R / 2) • v) (p + (y + R / 2) • v) = R := by
    rw [pullback_dist hv]
    have hneg : (y - R / 2) - (y + R / 2) < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  rcases hY R hR (p + (y - R / 2) • v) (p + (y + R / 2) • v) hd with ⟨x', hx', hball⟩
  rcases mem_segment_affine hab hx' with ⟨x, hxI, hxeq⟩
  refine ⟨x, ?_, ?_⟩
  · rw [Metric.mem_closedBall]
    rw [Set.mem_Icc] at hxI
    rw [Real.dist_eq]
    rw [abs_le]
    constructor <;> linarith
  · apply Set.subset_empty_iff.mp
    intro u hu
    have hmem : p + u • v ∈ closedBall x' (ν * R) := by
      rw [Metric.mem_closedBall]
      have hu1 : dist (p + u • v) (p + x • v) ≤ ν * R := by
        have hux : dist u x ≤ ν * R := Metric.mem_closedBall.mp hu.1
        calc
          dist (p + u • v) (p + x • v) = |u - x| := by rw [pullback_dist hv]
          _ = dist u x := by rw [Real.dist_eq]
          _ ≤ ν * R := hux
      rwa [hxeq]
    have hc : p + u • v ∈ closedBall x' (ν * R) ∩ Y := ⟨hmem, hu.2⟩
    simpa [hball] using hc

end Submission.FUP

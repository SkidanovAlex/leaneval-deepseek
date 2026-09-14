import Mathlib
import ChallengeDeps

open Module
open scoped Real BigOperators InnerProductSpace RealInnerProductSpace
set_option autoImplicit false

/-!
# The Voronoi cell of a lattice

For a lattice `ℒ ⊆ E` (a `ℤ`-submodule of a real inner-product space) the Voronoi cell is

`V(ℒ) := {x ∈ E | ∀ y ∈ ℒ, ⟨x, y⟩ ≤ ‖y‖²/2}`,

the set of points at least as close to the origin as to any other lattice point.
We record the elementary geometric facts needed for the analytic part of the
Reverse Minkowski proof:

* `V(ℒ)` is symmetric, convex, closed (hence measurable);
* the closed ball of radius `λ₁(ℒ)/2` is contained in `V(ℒ)`.

The measure-theoretic facts (that `V(ℒ)` is a fundamental domain of `ℒ`, i.e.
that `V(ℒ) + ℒ` tiles `E`, and `vol V(ℒ) = det ℒ`) are built on top of these
in later modules.
-/

namespace Submission.Voronoi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Voronoi cell of a lattice (i.e. a `ℤ`-submodule) in a real inner product space. -/
def voronoi (ℒ : Submodule ℤ E) : Set E :=
  {x | ∀ y : ℒ, ⟪x, (y : E)⟫_ℝ ≤ ‖(y : E)‖ ^ 2 / 2}

/-- Membership in the Voronoi cell -/
lemma mem_voronoi {ℒ : Submodule ℤ E} {x : E} :
    x ∈ voronoi ℒ ↔ ∀ y : ℒ, ⟪x, (y : E)⟫_ℝ ≤ ‖(y : E)‖ ^ 2 / 2 := by
  rfl

/-- The Voronoi cell is symmetric. -/
lemma voronoi_neg_mem {ℒ : Submodule ℤ E} {x : E} (hx : x ∈ voronoi ℒ) : -x ∈ voronoi ℒ := by
  rw [mem_voronoi] at hx ⊢
  intro y
  have h1 := hx ⟨-(y : E), Submodule.neg_mem ℒ y.2⟩
  have h2 : -⟪x, (y : E)⟫_ℝ ≤ ‖(y : E)‖ ^ 2 / 2 := by
    simpa [inner_neg_right] using h1
  have h3 : ⟪-x, (y : E)⟫_ℝ = -⟪x, (y : E)⟫_ℝ := by
    simpa using (inner_neg_left (𝕜 := ℝ) (x := x) (y := (y : E)))
  rw [h3]
  exact h2

/-- If all non-zero lattice vectors have norm at least `r` (i.e. `λ₁ ≥ r`), then
the closed ball of radius `r/2` is contained in the Voronoi cell. -/
lemma ball_subset_voronoi {ℒ : Submodule ℤ E} {r : ℝ}
    (hr : ∀ v : ℒ, v ≠ 0 → r ≤ ‖(v : E)‖) :
    Metric.closedBall (0 : E) (r / 2) ⊆ voronoi ℒ := by
  intro x hx
  rw [mem_voronoi]
  intro y
  by_cases hy0 : y = 0
  · subst y
    simp
  · have hlen : r ≤ ‖(y : E)‖ := hr y hy0
    have hxle : ‖x‖ ≤ r / 2 := by
      have := Metric.mem_closedBall.mp hx
      simp [dist_eq_norm] at this ⊢
      exact this
    have hcs := real_inner_le_norm x (y : E)
    calc
      ⟪x, (y : E)⟫_ℝ ≤ ‖(y : E)‖ * ‖x‖ := by
        simpa [mul_comm] using hcs
      _ ≤ ‖(y : E)‖ * (r / 2) := by
        exact mul_le_mul_of_nonneg_left hxle (norm_nonneg _)
      _ ≤ ‖(y : E)‖ ^ 2 / 2 := by
        nlinarith [mul_nonneg (norm_nonneg (y : E)) (sub_nonneg.mpr hlen), norm_nonneg (y : E)]

/-- When `λ₁(ℒ) ≥ 1`, the ball of radius `1/2` is contained in the Voronoi cell. -/
lemma one_half_ball_subset_voronoi_of_min_norm {ℒ : Submodule ℤ E}
    (hr : ∀ v : ℒ, v ≠ 0 → 1 ≤ ‖(v : E)‖) :
    Metric.closedBall (0 : E) (1 / 2) ⊆ voronoi ℒ := by
  simpa using ball_subset_voronoi (r := 1) hr

/-- The Voronoi cell is convex. -/
lemma voronoi_convex (ℒ : Submodule ℤ E) : Convex ℝ (voronoi ℒ) := by
  intro x hx y hy a b ha hb hab
  rw [mem_voronoi] at hx hy ⊢
  intro v
  have hxle : a * ⟪x, (v : E)⟫_ℝ ≤ a * (‖(v : E)‖ ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left (hx v) ha
  have hyle : b * ⟪y, (v : E)⟫_ℝ ≤ b * (‖(v : E)‖ ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left (hy v) hb
  have hin : ⟪a • x + b • y, (v : E)⟫_ℝ = a * ⟪x, (v : E)⟫_ℝ + b * ⟪y, (v : E)⟫_ℝ := by
    rw [inner_add_left]
    simp [real_inner_smul_left]
  rw [hin]
  nlinarith

/-- The Voronoi cell is closed. -/
lemma voronoi_isClosed (ℒ : Submodule ℤ E) : IsClosed (voronoi ℒ) := by
  rw [show voronoi ℒ = ⋂ y : ℒ, {x : E | ⟪x, (y : E)⟫_ℝ ≤ ‖(y : E)‖ ^ 2 / 2} by
    ext x
    simp [voronoi]]
  exact isClosed_iInter (fun y => by
    have hcont : Continuous fun x : E => ⟪x, (y : E)⟫_ℝ := by
      exact Continuous.inner (𝕜 := ℝ) continuous_id continuous_const
    exact IsClosed.preimage hcont isClosed_Iic)

/-- The Voronoi cell is measurable (in the Borel `σ`-algebra). -/
lemma voronoi_measurable (ℒ : Submodule ℤ E) [MeasurableSpace E] [BorelSpace E] :
    MeasurableSet (voronoi ℒ) :=
  (voronoi_isClosed ℒ).measurableSet

end Submission.Voronoi

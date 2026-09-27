import Mathlib

/-!
# The algebraic core of the (tilted) capsule push

The two identities behind the collision clauses of the capsule push (see
`Submission/Work/Drive/NOTES_disc_route.md` §10b), and the two clauses they imply:

    ⟪z + χ w, w⟫ = ⟪z, w⟫ + χ‖w‖²,      ‖z + χ w‖² = ‖z‖² + 2χ⟪z, w⟫ + χ²‖w‖²

* **sheet one**: a sheet-one source outside the "bullet"
  `D = {⟪·,w⟫ ≤ 0} ∪ B(0,r₀)`, with `χ > 0`, is moved further out and further forward: its image is
  still outside `D`;
* **sheet two**: a sheet-two source in the plateau (`χ = 1`) and inside `B(0, ‖w‖ - r₀)` is moved to
  `z + w`, which is outside `D`.
-/

open scoped RealInnerProductSpace
open Topology

namespace Work.Drive.PushDisc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **First identity**: `⟪z + χ w, w⟫ = ⟪z, w⟫ + χ‖w‖²`. -/
theorem inner_push (z w : E) (χ : ℝ) :
    inner ℝ (z + χ • w) w = inner ℝ z w + χ * ‖w‖ ^ 2 := by
  rw [inner_add_left, inner_smul_left]
  simp [real_inner_self_eq_norm_sq]

/-- **Second identity**: `‖z + χ w‖² = ‖z‖² + 2χ⟪z, w⟫ + χ²‖w‖²`. -/
theorem norm_push_sq (z w : E) (χ : ℝ) :
    ‖z + χ • w‖ ^ 2 = ‖z‖ ^ 2 + 2 * χ * inner ℝ z w + χ ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- **Sheet-one collision clause** (pure algebra): a source `z` outside the bullet (`0 < ⟪z, w⟫`,
`r₀ < ‖z‖`) moved by a positive cut-off `χ > 0` stays outside the bullet. -/
theorem sheet_one_clause (z w : E) (χ r₀ : ℝ) (hχ : 0 < χ) (hz : 0 < inner ℝ z w)
    (hr₀ : 0 < r₀) (hr : r₀ < ‖z‖) :
    0 < inner ℝ (z + χ • w) w ∧ r₀ < ‖z + χ • w‖ := by
  constructor
  · rw [inner_push]
    nlinarith [sq_nonneg ‖w‖, hz, hχ]
  · have hsq : r₀ ^ 2 < ‖z + χ • w‖ ^ 2 := by
      rw [norm_push_sq]
      nlinarith [sq_nonneg ‖w‖, sq_nonneg r₀, norm_nonneg z, hz, hχ, hr,
        mul_pos hχ hz, mul_nonneg (sq_nonneg χ) (sq_nonneg ‖w‖)]
    nlinarith [hsq, hr₀, norm_nonneg (z + χ • w), sq_nonneg r₀, hr, norm_nonneg z]

/-- **Sheet-two collision clause** (pure algebra, with the two geometric inputs of the capsule
design as hypotheses): a sheet-two source in the plateau (`χ = 1`) inside `B(0, ‖w‖ - r₀)` is moved
to `z + w`, which is outside the bullet. -/
theorem sheet_two_clause (z w : E) (r₀ : ℝ) (hr₀ : 0 < r₀) (hz : ‖z‖ < ‖w‖ - r₀) :
    r₀ < ‖z + w‖ ∧ 0 < inner ℝ (z + w) w := by
  constructor
  · have h1 : ‖w‖ ≤ ‖z + w‖ + ‖z‖ := by
      have h := norm_add_le (z + w) (-z)
      simpa [add_assoc, add_comm, add_left_comm] using h
    linarith
  · have h2 : -(‖z‖ * ‖w‖) ≤ inner ℝ z w := by
      have h := abs_real_inner_le_norm z w
      exact (abs_le.mp h).1
    have hp := inner_push z w 1
    simp only [one_smul] at hp
    rw [hp]
    have h3 : 0 < ‖w‖ * (‖w‖ - ‖z‖) := by
      have h4 : 0 < ‖w‖ - ‖z‖ := by linarith
      have h5 : 0 < ‖w‖ := by linarith [norm_nonneg z]
      exact mul_pos h5 h4
    nlinarith [h2, h3]

end Work.Drive.PushDisc

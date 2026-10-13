import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Denseness of the domain `Uax` of the Biot–Savart identification

`Uax = {x₃ ≠ 0, x₀² + x₁² ≠ 0}` is the complement of the axis `r = 0` and of the plane `x₃ = 0`,
i.e. of a finite union of hyperplanes of `ℝ³`.  Its complement therefore has empty interior, so
`Uax` is dense: every point of `ℝ³` can be pushed into `Uax` by an arbitrarily small displacement.

Concretely, `{x₂ ≠ 0}` is dense (a point with `x₂ = 0` is moved to `x + (r/2) e₂`, whose second
coordinate is `r/2 ≠ 0`), and `{x₀² + x₁² ≠ 0}` contains the dense set `{x₀ ≠ 0}`.  Both sets are
open, so their intersection — which is `Uax` — is dense.
-/

set_option autoImplicit false

namespace Work.FTS.BSIdent.Defs

/-- Every coordinate hyperplane complement in `ℝ³` is dense: from a point whose `i`-th coordinate
vanishes one reaches the complement by the displacement `(r/2) • eᵢ`. -/
private theorem dense_coord_ne_zero (i : Fin 3) :
    Dense {x : EuclideanSpace ℝ (Fin 3) | x i ≠ 0} := by
  rw [Metric.dense_iff]
  intro x r hr
  rcases eq_or_ne (x i) 0 with hx | hx
  · refine ⟨x + (r / 2) • FiniteTimeSingularity.e i, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have h1 : x + (r / 2) • FiniteTimeSingularity.e i - x
          = (r / 2) • FiniteTimeSingularity.e i := by abel
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < r / 2),
        show ‖FiniteTimeSingularity.e i‖ = 1 from by simp [FiniteTimeSingularity.e]]
      linarith
    · show (x + (r / 2) • FiniteTimeSingularity.e i) i ≠ 0
      have h2 : (x + (r / 2) • FiniteTimeSingularity.e i) i = r / 2 := by
        simp [FiniteTimeSingularity.e, hx]
      rw [h2]; linarith
  · exact ⟨x, by simpa using hr, hx⟩

/-- **`Uax` is dense in `ℝ³`.**  It is the intersection of the two open dense sets `{x₃ ≠ 0}` and
`{x₀² + x₁² ≠ 0}`. -/
theorem dense_Uax : Dense (Work.FTS.BSIdent.Uax : Set Work.FTS.BSIdent.R3) := by
  have h1 : Dense ({x : Work.FTS.BSIdent.R3 | x 2 ≠ 0} : Set Work.FTS.BSIdent.R3) :=
    dense_coord_ne_zero 2
  have h2 : Dense ({x : Work.FTS.BSIdent.R3 | x 0 ≠ 0} : Set Work.FTS.BSIdent.R3) :=
    dense_coord_ne_zero 0
  have h2' : Dense ({x : Work.FTS.BSIdent.R3 | x 0 ^ 2 + x 1 ^ 2 ≠ 0} :
      Set Work.FTS.BSIdent.R3) :=
    Dense.mono (fun x hx => by
      intro hc
      have h0 : x 0 ^ 2 = 0 := by nlinarith [sq_nonneg (x 1)]
      exact hx (sq_eq_zero_iff.mp h0)) h2
  have hopen : IsOpen ({x : Work.FTS.BSIdent.R3 | x 2 ≠ 0} : Set Work.FTS.BSIdent.R3) :=
    (isOpen_ne (x := (0 : ℝ))).preimage (by fun_prop)
  have hint := Dense.inter_of_isOpen_left h1 h2' hopen
  convert hint using 1
  ext x; simp [Work.FTS.BSIdent.Uax, and_comm]

end Work.FTS.BSIdent.Defs

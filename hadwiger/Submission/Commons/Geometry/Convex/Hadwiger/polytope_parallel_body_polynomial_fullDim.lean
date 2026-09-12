import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_parallel_body_polynomial_fullDim_generic_v2

open scoped Classical Pointwise

namespace Commons.Geometry.Convex.Hadwiger

noncomputable section

/-- Steiner's formula, polytope case (full-dimensional): for a full-dimensional convex
polytope `P = convexHull u` in `EuclideanSpace ℝ (Fin m)` the parallel-body volume
function `t ↦ vol (P + t•B)`, `t ≥ 0`, is the restriction of a polynomial of degree
at most `m`.  (`B` is the unit closed ball.)

This is the full-dimensional polytope instance of the general full-dim polytope theorem
`polytope_parallel_body_polynomial_fullDim_generic_v2` (proved in the commons); here the
generic statement is instantiated with `V := EuclideanSpace ℝ (Fin m)` and the
`ConvexBody` coercions are unwound. -/
theorem polytope_parallel_body_polynomial_fullDim (m : ℕ)
    (P : ConvexBody (EuclideanSpace ℝ (Fin m)))
    (u : Finset (EuclideanSpace ℝ (Fin m)))
    (hP : (P : Set (EuclideanSpace ℝ (Fin m))) = convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin m))))
    (hint : (interior (P : Set (EuclideanSpace ℝ (Fin m)))).Nonempty) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ m ∧
      ∀ t : ℝ, 0 ≤ t →
        let B : ConvexBody (EuclideanSpace ℝ (Fin m)) :=
          ⟨Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1, convex_closedBall (0 : EuclideanSpace ℝ (Fin m)) 1,
            isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) 1, Metric.nonempty_closedBall.mpr zero_le_one⟩
        (MeasureTheory.volume ((P + t • B : ConvexBody (EuclideanSpace ℝ (Fin m))) : Set (EuclideanSpace ℝ (Fin m)))).toReal = p.eval t := by
  classical
  let V : Type _ := EuclideanSpace ℝ (Fin m)
  let B : ConvexBody V :=
    ⟨Metric.closedBall (0 : V) 1, convex_closedBall (0 : V) 1,
      isCompact_closedBall (0 : V) 1, Metric.nonempty_closedBall.mpr zero_le_one⟩
  change ∃ p : Polynomial ℝ, p.natDegree ≤ m ∧
      ∀ t : ℝ, 0 ≤ t →
        (MeasureTheory.volume ((P + t • B : ConvexBody V) : Set V)).toReal = p.eval t
  obtain ⟨p, hdeg, hval⟩ :=
    polytope_parallel_body_polynomial_fullDim_generic_v2 (V := V) (u := u) (P := (P : Set V)) hP hint
  refine ⟨p, ?_, ?_⟩
  · have hfin : Module.finrank ℝ V = m := by
      dsimp [V]
      simp
    rwa [hfin] at hdeg
  · intro t ht
    have hset : ((P + t • B : ConvexBody V) : Set V) = ((P : Set V) + t • (B : Set V)) := by
      simp only [ConvexBody.coe_add, ConvexBody.coe_smul]
    rw [hset]
    have hB : (B : Set V) = Metric.closedBall (0 : V) 1 := rfl
    rw [hB]
    exact hval t ht

end

end Commons.Geometry.Convex.Hadwiger

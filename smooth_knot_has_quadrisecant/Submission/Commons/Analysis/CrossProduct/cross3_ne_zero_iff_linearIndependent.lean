import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct

open scoped Matrix

noncomputable section

namespace Commons.Analysis.CrossProduct

/-- The cross product of two vectors in `EuclideanSpace ℝ (Fin 3)` (i.e. in
`ℝ³` with the Euclidean structure transported through the `WithLp` type
synonym) is nonzero exactly when the two vectors are linearly independent
over `ℝ`. -/
theorem cross3_ne_zero_iff_linearIndependent (u v : EuclideanSpace ℝ (Fin 3)) :
    WithLp.toLp 2 (WithLp.ofLp u ⨯₃ WithLp.ofLp v) ≠ 0 ↔ LinearIndependent ℝ ![u, v] := by
  calc
    WithLp.toLp 2 (WithLp.ofLp u ⨯₃ WithLp.ofLp v) ≠ 0
        ↔ WithLp.ofLp u ⨯₃ WithLp.ofLp v ≠ 0 := by
          exact (WithLp.toLp_eq_zero (p := 2) (x := WithLp.ofLp u ⨯₃ WithLp.ofLp v)).not
    _ ↔ LinearIndependent ℝ ![WithLp.ofLp u, WithLp.ofLp v] := by
          exact crossProduct_ne_zero_iff_linearIndependent (F := ℝ)
            (v := WithLp.ofLp u) (w := WithLp.ofLp v)
    _ ↔ LinearIndependent ℝ ![u, v] := by
          -- `WithLp.ofLp` is the underlying map of the ℝ-linear equivalence
          -- `WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] Fin 3 → ℝ`,
          -- and injective linear maps preserve (and reflect, being injective)
          -- linear independence of families.
          let L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] (Fin 3 → ℝ) :=
            (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap
          have hcomp : L ∘ ![u, v] = ![WithLp.ofLp u, WithLp.ofLp v] := by
            funext i
            fin_cases i <;> rfl
          have hker : LinearMap.ker L = ⊥ := by
            apply LinearMap.ker_eq_bot_of_injective
            simpa [L] using (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).injective
          rw [← hcomp]
          exact LinearMap.linearIndependent_iff (f := L) (v := ![u, v]) hker

end Commons.Analysis.CrossProduct
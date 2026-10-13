import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.InnerProductSpace.PiL2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

theorem fderiv_fderiv_comm (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hW : ∀ n : ℕ, ContDiff ℝ n W) (x a b : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) => fderiv ℝ W w a) x b
      = fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) => fderiv ℝ W w b) x a := by
  -- The two sides are the two mixed second derivatives of `W` at `x`, evaluated on the
  -- constant vector fields `a` and `b`; their difference is the derivative of `W` along the
  -- Lie bracket `[a, b] = 0` of two constant vector fields.
  have h2 : ContDiffAt ℝ 2 W x := (hW 2).contDiffAt
  have hsymm : IsSymmSndFDerivAt ℝ W x := h2.isSymmSndFDerivAt (by simp)
  have h := VectorField.fderiv_apply_lieBracket_of_isSymmSndFDerivAt
    (𝕜 := ℝ) (f := W)
    (V := fun _ : EuclideanSpace ℝ (Fin 3) => b)
    (W := fun _ : EuclideanSpace ℝ (Fin 3) => a)
    h2 hsymm (differentiableAt_const a) (differentiableAt_const b)
  simp only [VectorField.lieBracket, map_sub] at h
  simp at h
  exact sub_eq_zero.mp h.symm

end Work.FTS.PressureOn.Auxiliary

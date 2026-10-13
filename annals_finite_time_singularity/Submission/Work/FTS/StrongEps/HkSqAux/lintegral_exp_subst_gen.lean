import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HkSqAux

open MeasureTheory Set

/-- The `lintegral` change-of-variables formula for the substitution `z = exp s` on `(0, ∞)`,
stated for an arbitrary `ENNReal`-valued function `U` (so no integrability hypothesis is
needed): `∫⁻ z ∈ (0,∞), U z = ∫⁻ s, exp s * U (exp s)`.

This is the one-dimensional change-of-variables formula
`lintegral_image_eq_lintegral_abs_deriv_mul` applied to `Real.exp` on `Set.univ`, using
`Real.range_exp : range exp = Ioi 0`. -/
theorem lintegral_exp_subst_gen (U : ℝ → ENNReal) :
    (∫⁻ z in Set.Ioi 0, U z) = ∫⁻ s, ENNReal.ofReal (Real.exp s) * U (Real.exp s) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
    (s := Set.univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn U
  simpa [image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _)] using h

end Work.FTS.StrongEps.HkSqAux

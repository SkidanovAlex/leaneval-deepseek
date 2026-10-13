import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.HkSqAux.LogCoord

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HkSqAux

open MeasureTheory

/-- **The two-dimensional log-coordinate substitution** `z = e^s`, `θ = arctan (e^ζ)` in
`lintegral` form, for an **arbitrary** `ENNReal`-valued function `V` (no measurability or
integrability hypothesis): the iterated integral over the open quadrant `(0,∞) × (0,π/2)`
becomes an integral over the plane with the Jacobian weight `logJac s ζ = e^s · kappa ζ`.

The proof is a two-step application of the one-dimensional substitutions
`lintegral_exp_subst_gen` (for `z = e^s`) and `lintegral_arctan_exp_subst_gen`
(for `θ = arctan (e^ζ)`), followed by the measurability-free identity
`lintegral_const_mul'` which moves the constant factor `e^s` inside the `ζ`-integral. -/
theorem lintegral_quad_log_subst (V : ℝ → ℝ → ENNReal) :
    (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), V z θ)
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
          * V (Real.exp s) (Real.arctan (Real.exp ζ)) := by
  -- (1) the angular substitution `θ = arctan (e^ζ)`, slice by slice
  rw [show (fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), V z θ)
      = fun z => ∫⁻ ζ, ENNReal.ofReal (kappa ζ) * V z (Real.arctan (Real.exp ζ)) from
        funext (fun z => lintegral_arctan_exp_subst_gen (V z))]
  -- (2) the radial substitution `z = e^s` in the outer integral
  rw [lintegral_exp_subst_gen (fun z => ∫⁻ ζ, ENNReal.ofReal (kappa ζ)
        * V z (Real.arctan (Real.exp ζ)))]
  refine MeasureTheory.lintegral_congr fun s => ?_
  -- (3) pull the constant `e^s` inside the `ζ`-integral (no measurability needed)
  rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (Real.exp s))
        (fun ζ => ENNReal.ofReal (kappa ζ) * V (Real.exp s) (Real.arctan (Real.exp ζ)))
        ENNReal.ofReal_ne_top]
  refine MeasureTheory.lintegral_congr fun ζ => ?_
  -- (4) identify the product of the two Jacobians
  rw [logJac, ENNReal.ofReal_mul (Real.exp_pos s).le]
  ring

end Work.FTS.StrongEps.HkSqAux

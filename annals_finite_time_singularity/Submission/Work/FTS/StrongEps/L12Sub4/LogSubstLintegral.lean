import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.L12Sub4.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongEps.L12Sub4

/-- **The log-coordinate substitution in `lintegral` form** (unconditional, for nonnegative `u`):
the angular weight `K(θ) dθ` pushes forward to `Glw(ζ) dζ` and the radial weight `dr/r` to `ds`,
so the quadrant `∫⁻` (measure `dθ dr`, weight `K(θ)/r`) equals the plane `∫⁻` with weight `Glw`:

  `∫⁻_s ∫⁻_ζ ofReal (Glw ζ · u (e^s) (arctan (e^ζ))) = ∫⁻_z∈(0,∞) ∫⁻_θ∈Iθ ofReal (K(θ) u(z,θ)/z)`.

Hints: the angular part is `HkSqAux.lintegral_arctan_exp_subst_gen` (or
`HkSqAux.lintegral_quad_log_subst`), the radial part `HkSqAux.lintegral_exp_subst_gen`; combine with
`ENNReal.ofReal_mul` and the `kappa`/`logJac` algebra exactly as
`HkSqAux.ofReal_HkSq_eq_logIntegral` does, and replace `Ioo 0 (π/2)` by `Iθ` by a null-set change
(`MeasureTheory.Ioo_ae_eq_Icc`, `setLIntegral_congr`). -/
theorem LogSubstLintegral (u : ℝ → ℝ → ℝ) (hu : ∀ z θ, 0 ≤ u z θ) :
    (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Glw ζ * u (Real.exp s) (Real.arctan (Real.exp ζ))))
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.K θ * u z θ / z) := by
  -- The pointwise identification of the two Jacobian-weighted integrands.
  have hpt : ∀ s ζ : ℝ,
      ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
        * ENNReal.ofReal (Work.Spaces.K (Real.arctan (Real.exp ζ))
            * u (Real.exp s) (Real.arctan (Real.exp ζ)) / Real.exp s)
      = ENNReal.ofReal (Glw ζ * u (Real.exp s) (Real.arctan (Real.exp ζ))) := by
    intro s ζ
    rw [← ENNReal.ofReal_mul (Work.FTS.StrongEps.HkSqAux.logJac_nonneg s ζ)]
    congr 1
    have h1 : Real.exp s ≠ 0 := Real.exp_ne_zero s
    have h2 : (1 : ℝ) + Real.exp (2 * ζ) ≠ 0 := by positivity
    simp only [Glw, Work.FTS.StrongEps.HkSqAux.logJac, Work.FTS.StrongEps.HkSqAux.kappa]
    field_simp
  -- Replace `Iθ = Icc 0 (π/2)` by the open interval `Ioo 0 (π/2)` (a null-set change).
  rw [show (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.K θ * u z θ / z))
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.K θ * u z θ / z) from
    lintegral_congr fun z => (setLIntegral_congr
      (f := fun θ : ℝ => ENNReal.ofReal (Work.Spaces.K θ * u z θ / z))
      (Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2))).symm]
  -- Apply the two-dimensional log-coordinate substitution.
  rw [Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst
    (fun z θ => ENNReal.ofReal (Work.Spaces.K θ * u z θ / z))]
  exact lintegral_congr fun s => lintegral_congr fun ζ => (hpt s ζ).symm

end Work.FTS.StrongEps.L12Sub4

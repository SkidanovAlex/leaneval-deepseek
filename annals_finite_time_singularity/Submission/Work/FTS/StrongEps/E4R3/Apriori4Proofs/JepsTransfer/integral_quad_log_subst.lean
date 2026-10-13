import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `integral_quad_log_subst` — the log-coordinate substitution for Bochner integrals

The Bochner-integral form of the two-dimensional change of variables
`(z, θ) = (e^s, arctan (e^ζ))` on the quadrant `(0,∞) × (0,π/2)`:

  `∫_{z>0} ∫_{0<θ<π/2} F z θ = ∫_s ∫_ζ logJac s ζ · F (e^s) (arctan (e^ζ))`,

where `logJac s ζ = e^s · kappa ζ` is the Jacobian of the substitution
(`Work.FTS.StrongEps.HkSqAux.logJac`).  The `lintegral` version is the sibling
`Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst`; here we need the signed (Bochner) version.

The proof applies the one-dimensional change-of-variables formula for injective differentiable
maps, `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`, twice: for `ζ ↦ arctan (e^ζ)`
(whose range is `(0,π/2)`, with derivative `kappa ≥ 0`) slice by slice, and then for `z = e^s`
(whose range is `(0,∞)`, with derivative `e^s ≥ 0`).
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

open MeasureTheory Set
open scoped Real

theorem integral_quad_log_subst {F : ℝ → ℝ → ℝ}
    (hF : MeasureTheory.Integrable (Function.uncurry F)
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), F z θ)
      = ∫ s, ∫ ζ, Work.FTS.StrongEps.HkSqAux.logJac s ζ
          * F (Real.exp s) (Real.arctan (Real.exp ζ)) := by
  classical
  -- Step 1: the angular substitution `θ = arctan (e^ζ)`, for each slice `z`.
  have hsubθ : ∀ z : ℝ, (∫ θ in Set.Ioo 0 (Real.pi / 2), F z θ)
      = ∫ ζ, Work.FTS.StrongEps.HkSqAux.kappa ζ * F z (Real.arctan (Real.exp ζ)) := by
    intro z
    have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Set.univ) (f := fun ζ : ℝ => Real.arctan (Real.exp ζ))
      (f' := Work.FTS.StrongEps.HkSqAux.kappa) MeasurableSet.univ
      (fun ζ _ => (Work.FTS.StrongEps.HkSqAux.hasDerivAt_arctan_exp ζ).hasDerivWithinAt)
      (Work.FTS.StrongEps.HkSqAux.strictMono_arctan_exp.injective.injOn)
      (fun θ => F z θ)
    rw [Work.FTS.StrongEps.HkSqAux.range_arctan_exp, MeasureTheory.setIntegral_univ] at h
    have habs : ∀ ζ : ℝ, |Work.FTS.StrongEps.HkSqAux.kappa ζ|
        = Work.FTS.StrongEps.HkSqAux.kappa ζ :=
      fun ζ => abs_of_nonneg (Work.FTS.StrongEps.HkSqAux.kappa_nonneg ζ)
    simpa [habs, smul_eq_mul] using h
  have h1 : (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), F z θ)
      = ∫ z in Set.Ioi 0, (∫ ζ, Work.FTS.StrongEps.HkSqAux.kappa ζ
          * F z (Real.arctan (Real.exp ζ))) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => hsubθ z)
  -- Step 2: the radial substitution `z = e^s` in the outer integral.
  have h2 : (∫ z in Set.Ioi 0, (∫ ζ, Work.FTS.StrongEps.HkSqAux.kappa ζ
        * F z (Real.arctan (Real.exp ζ))))
      = ∫ s, Real.exp s * (∫ ζ, Work.FTS.StrongEps.HkSqAux.kappa ζ
          * F (Real.exp s) (Real.arctan (Real.exp ζ))) := by
    have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn
      (fun z => ∫ ζ, Work.FTS.StrongEps.HkSqAux.kappa ζ * F z (Real.arctan (Real.exp ζ)))
    rw [Work.FTS.StrongEps.HkSqAux.range_exp, MeasureTheory.setIntegral_univ] at h
    have habs : ∀ x : ℝ, |Real.exp x| = Real.exp x := fun x => abs_of_pos (Real.exp_pos x)
    simpa [habs, smul_eq_mul] using h
  -- Step 3: move the constant `e^s` inside the `ζ`-integral and identify `logJac`.
  have h3 : ∀ s : ℝ, Real.exp s * (∫ ζ, Work.FTS.StrongEps.HkSqAux.kappa ζ
        * F (Real.exp s) (Real.arctan (Real.exp ζ)))
      = ∫ ζ, Work.FTS.StrongEps.HkSqAux.logJac s ζ
          * F (Real.exp s) (Real.arctan (Real.exp ζ)) := by
    intro s
    rw [show (∫ ζ, Work.FTS.StrongEps.HkSqAux.logJac s ζ
            * F (Real.exp s) (Real.arctan (Real.exp ζ)))
        = ∫ ζ, Real.exp s * (Work.FTS.StrongEps.HkSqAux.kappa ζ
            * F (Real.exp s) (Real.arctan (Real.exp ζ))) from
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ζ => by
          show Work.FTS.StrongEps.HkSqAux.logJac s ζ * F (Real.exp s) (Real.arctan (Real.exp ζ))
            = Real.exp s * (Work.FTS.StrongEps.HkSqAux.kappa ζ
              * F (Real.exp s) (Real.arctan (Real.exp ζ)))
          rw [Work.FTS.StrongEps.HkSqAux.logJac.eq_1]; ring))]
    rw [MeasureTheory.integral_const_mul]
  rw [h1, h2]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h3)

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

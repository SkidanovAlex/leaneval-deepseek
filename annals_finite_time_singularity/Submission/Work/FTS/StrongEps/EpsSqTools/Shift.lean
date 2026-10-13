/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsSqTools/Shift.lean`

The shift step of the `E1`-bound: the integral of the shifted `EpsSq`-integrand over the quadrant
is bounded by `e^{δ(|p₁|+|p₂|)} EpsSq α f`.  In the log coordinates the shift is a translation, so
only the Jacobian `logJac` has to be compared.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.EpsSpace
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.logJac_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_prod_shift
import Submission.Work.FTS.StrongEps.EpsSrc.lintegral_logSubst
import Submission.Work.FTS.StrongEps.EpsSrc.ofReal_EpsSq_eq_lintegral
import Submission.Work.FTS.StrongEps.EpsSqTools.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSqTools

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The shift step**: the integral of the shifted `EpsSq`-integrand is bounded by
`e^{δ(|p₁|+|p₂|)} EpsSq α f`, where `δ` is the constant of the Jacobian comparison
`logJac s ζ ≤ e^{δ(|p₁|+|p₂|)} logJac (s-p₁) (ζ-p₂)`. -/
theorem shift_step {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : EpsMem α f) {δ : ℝ}
    (hJac : ∀ s ζ p₁ p₂ : ℝ, HkSqAux.logJac s ζ
      ≤ Real.exp (δ * (|p₁| + |p₂|)) * HkSqAux.logJac (s - p₁) (ζ - p₂)) (p : ℝ × ℝ) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((f (zShift z p.1) (thShift θ p.2)
          * epsW α (zShift z p.1) (thShift θ p.2)) ^ 2))
      ≤ ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) * ENNReal.ofReal (EpsSq α f) := by
  set G : ℝ → ℝ → ENNReal := fun s ζ => ENNReal.ofReal
    ((f (Real.exp s) (Real.arctan (Real.exp ζ))
      * epsW α (Real.exp s) (Real.arctan (Real.exp ζ))) ^ 2) with hG
  have h1 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((f (zShift z p.1) (thShift θ p.2)
          * epsW α (zShift z p.1) (thShift θ p.2)) ^ 2))
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ) * G (s - p.1) (ζ - p.2) := by
    rw [Work.FTS.StrongEps.EpsSrc.lintegral_logSubst
      (fun z θ => ENNReal.ofReal ((f (zShift z p.1) (thShift θ p.2)
        * epsW α (zShift z p.1) (thShift θ p.2)) ^ 2))]
    refine lintegral_congr (fun s => lintegral_congr (fun ζ => ?_))
    congr 1
    simp only [hG, zShift_exp', thShift_arctan_exp']
  have htrans : (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ) * G (s - p.1) (ζ - p.2))
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac (s + p.1) (ζ + p.2)) * G s ζ :=
    HkSqAux.lintegral_prod_shift_mul (fun s ζ => ENNReal.ofReal (HkSqAux.logJac s ζ)) G p.1 p.2
  have h2 : (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac (s + p.1) (ζ + p.2)) * G s ζ)
      ≤ ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
        * ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ := by
    have hpt : ∀ s ζ : ℝ,
        ENNReal.ofReal (HkSqAux.logJac (s + p.1) (ζ + p.2)) * G s ζ
          ≤ ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * (ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ) := by
      intro s ζ
      have h := hJac (s + p.1) (ζ + p.2) p.1 p.2
      rw [add_sub_cancel_right, add_sub_cancel_right] at h
      calc ENNReal.ofReal (HkSqAux.logJac (s + p.1) (ζ + p.2)) * G s ζ
          ≤ ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)) * HkSqAux.logJac s ζ) * G s ζ :=
            mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal h) zero_le
        _ = (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (HkSqAux.logJac s ζ)) * G s ζ := by
            rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
        _ = ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * (ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ) := by ring
    calc (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac (s + p.1) (ζ + p.2)) * G s ζ)
        ≤ ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * (ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ) :=
          lintegral_mono (fun s => lintegral_mono (fun ζ => hpt s ζ))
      _ = ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ := by
          rw [show (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
                * (ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ))
              = ∫⁻ s, ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
                  * (∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ) from by
                refine lintegral_congr (fun s => ?_)
                exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have h3 : (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ)
      = ENNReal.ofReal (EpsSq α f) := by
    rw [← Work.FTS.StrongEps.EpsSrc.lintegral_logSubst
      (fun z θ => ENNReal.ofReal ((f z θ * epsW α z θ) ^ 2))]
    exact (Work.FTS.StrongEps.EpsSrc.ofReal_EpsSq_eq_lintegral hf).symm
  calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((f (zShift z p.1) (thShift θ p.2)
          * epsW α (zShift z p.1) (thShift θ p.2)) ^ 2))
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ) * G (s - p.1) (ζ - p.2) := h1
    _ = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac (s + p.1) (ζ + p.2)) * G s ζ := htrans
    _ ≤ ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
          * ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (HkSqAux.logJac s ζ) * G s ζ := h2
    _ = ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) * ENNReal.ofReal (EpsSq α f) := by
        rw [h3]

end Work.FTS.StrongEps.EpsSqTools

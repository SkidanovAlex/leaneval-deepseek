import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Pieces.rl1Bound
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.l12densMeasAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The density `L₁₂dens` is integrable when `Fa` is finite

`L₁₂dens f s = ∫_θ K(θ)·f(s,θ)/s dθ = s⁻¹ ∫_θ K(θ)·f(s,θ) dθ` for `s > 0`, hence

  `ofReal |L₁₂dens f s| ≤ ofReal s⁻¹ · ∫⁻_θ ofReal |K(θ)·f(s,θ)|`   (`s > 0`),

by `ofReal |∫| ≤ ∫⁻ ofReal |·|` (`norm_integral_le_lintegral_norm`) followed by pulling the
constant `s⁻¹` out of the lintegral.  Integrating this over `(0,∞)` in `s` gives exactly
`∫⁻_{s>0} ofReal |L₁₂dens f s| ≤ Fa f`, and `Fa f < ⊤` therefore yields
`HasFiniteIntegral (L₁₂dens f) (volume.restrict (Ioi 0))`.  Together with the assumed
a.e. strong measurability this is `IntegrableOn (L₁₂dens f) (Ioi 0)`. -/

/-- For a real-valued function on a measure space,
`ofReal |∫ x in s, h x| ≤ ∫⁻ x in s, ofReal |h x|` (no measurability needed: the
`lintegral` of the pointwise norm always dominates the norm of the Bochner integral). -/
private theorem ofReal_abs_integral_le (h : ℝ → ℝ) (μ : Measure ℝ) (s : Set ℝ) :
    ENNReal.ofReal |∫ x in s, h x ∂μ| ≤ ∫⁻ x in s, ENNReal.ofReal |h x| ∂μ := by
  have h3 := MeasureTheory.norm_integral_le_lintegral_norm h (μ := μ.restrict s)
  rw [Real.norm_eq_abs] at h3
  exact le_trans (ENNReal.ofReal_le_ofReal h3) ENNReal.ofReal_toReal_le

/-- The pointwise domination of the `L₁₂`-density by the `Fa`-integrand:
`ofReal |L₁₂dens f s| ≤ ofReal s⁻¹ · ∫⁻_θ ofReal |K(θ)·f(s,θ)|` for `s > 0`. -/
private theorem ofReal_abs_L12dens_le {f : ℝ → ℝ → ℝ} {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal |Work.Construction.L12dens f s|
      ≤ ENNReal.ofReal s⁻¹
        * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * f s θ| := by
  -- the density is the integral of `K θ · f s θ / s`, so `ofReal |·| ≤ ∫⁻ ofReal |·|`
  have h1 : ENNReal.ofReal |Work.Construction.L12dens f s|
      ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * f s θ / s| := by
    rw [Work.Construction.L12dens, Work.FM.L12dens, Work.Spaces.Iθ]
    exact ofReal_abs_integral_le _ _ _
  -- the integrand factorises as `s⁻¹ · (K θ · f s θ)` for `s > 0`
  have hpt : (fun θ : ℝ => ENNReal.ofReal |Work.Spaces.K θ * f s θ / s|)
      = fun θ : ℝ => ENNReal.ofReal s⁻¹
          * ENNReal.ofReal |Work.Spaces.K θ * f s θ| := by
    funext θ
    have hdiv : Work.Spaces.K θ * f s θ / s = s⁻¹ * (Work.Spaces.K θ * f s θ) := by
      rw [div_eq_inv_mul]
    rw [hdiv, abs_mul, abs_of_pos (inv_pos.mpr hs),
      ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hs))]
  rw [hpt, MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h1
  exact h1

theorem FaDens {f : ℝ → ℝ → ℝ}
    (haesm : MeasureTheory.AEStronglyMeasurable (Work.Construction.L12dens f)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hfa : Work.FTS.Nonlinear.Pieces.Fa f < ⊤) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens f) (Set.Ioi (0 : ℝ)) := by
  have hfin : MeasureTheory.HasFiniteIntegral (Work.Construction.L12dens f)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    refine lt_of_le_of_lt ?_ hfa
    rw [Work.FTS.Nonlinear.Pieces.Fa]
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs]
    exact ofReal_abs_L12dens_le hs
  exact ⟨haesm, hfin⟩

end Work.FTS_MuLipC.RowN

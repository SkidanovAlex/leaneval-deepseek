import Mathlib
import Submission.Work.Analysis.Complex.DbarCauchy.Defs
import Submission.Work.Analysis.Complex.DbarCauchy.cauchyT_contDiff
import Submission.Work.Analysis.Complex.DbarCauchy.hasFDerivAt_cauchyT
import Submission.Work.Analysis.Complex.DbarCauchy.dbar_representation
import Submission.Work.Analysis.RiemannSurface.PlanarCauchy

/-!
# Cauchy–Pompeiu solvability of `∂̄` on `ℂ` for compactly supported `C^∞` data

`dbar_solvable`: for every `ω : ℂ → ℂ` of class `C^∞` with compact support there is `u` of class
`C^∞` with `dbar u = 2 ω`, where `dbar = ∂_x + i∂_y = 2 ∂_z̄` is the unscaled `∂̄` of `Defs.lean`.
The witness is the regularised Cauchy transform `cauchyT ω` (`contDiff_cauchyT`), and the content is
the two identities proved below:

* `cauchyT_dbar` : `cauchyT (fun w => dbar ω w) z = 2 ω z`, from the Cauchy–Pompeiu representation
  `dbar_representation`, the vanishing of the regularising term (`∫ η, cut η/η = 0`, by oddness)
  and the translation invariance of Lebesgue measure;
* `dbar_cauchyT` : `dbar (cauchyT ω) z = cauchyT (fun w => dbar ω w) z`, from
  `fderiv_cauchyT_apply` (interchange of the `∂̄` with the transform) together with the linearity of
  `cauchyT` in its argument (`cauchyT_add`, `cauchyT_const_mul`).

This is the first rung of the Behnke–Stein / Cousin chapter (the plane model of `H¹(X, 𝒪) = 0`).

**Warning (`cauchyT_dbar` is an exact identity, not an estimate).**  `cauchyT (∂̄φ) = 2 φ` holds for
every compactly supported `C¹` `φ`; consequently, for a cutoff `χ` equal to `1` near `K` and
`ω := ∂̄(χ f)` one gets `cauchyT ω = 2 χ f` and the function `χ f - cauchyT ω / 2` is *identically
zero* on `{χ = 1}`.  So the "cutoff + Cauchy transform" route to the approximation step produces the
zero function, and no estimate of `cauchyT ω` in terms of `sup ‖ω‖` and the geometry of the support
can yield smallness: shrinking the transition region of `χ` only increases `sup ‖∂̄χ‖`.  The
approximation step needs either Hörmander's weighted `L²` minimal solution or the duality argument
of `NOTES_divisor_chapter_plan.md` §9, §12 — see also the estimate file `cauchyT_estimate.lean`.

-/

open MeasureTheory
open scoped Topology

set_option maxHeartbeats 8000000

noncomputable section

namespace Work.Analysis.Complex.DbarCauchy

/-! ### Integrability of the Cauchy-transform integrands -/

theorem integrable_cutC_div : Integrable fun η : ℂ => cutC η / η := by
  have h := Work.Analysis.RiemannSurface.integrable_div_sub contDiff_cutC.continuous
    hasCompactSupport_cutC 0
  simpa using h

theorem integral_cutC_div_eq_zero : ∫ η : ℂ, cutC η / η = 0 := by
  have h3 : ∫ η : ℂ, cutC (-η) / (-η) = -∫ η : ℂ, cutC η / η := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show cutC (-η) / (-η) = -(cutC η / η)
    rw [cutC_neg]
    ring
  have h5 : ∫ η : ℂ, cutC η / η = ∫ η : ℂ, cutC (-η) / (-η) :=
    (integral_neg_eq_self (fun η : ℂ => cutC η / η) volume).symm
  have h2 : ∫ η : ℂ, cutC η / η = -∫ η : ℂ, cutC η / η := h5.trans h3
  have h4 : (2 : ℂ) * (∫ η : ℂ, cutC η / η) = 0 := by linear_combination h2
  exact (mul_eq_zero.mp h4).resolve_left (by norm_num)

/-- The Cauchy-transform integrand of a directional derivative of `ω` is integrable. -/
theorem integrable_directional (ω : ℂ → ℂ) (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω)
    (z h : ℂ) :
    Integrable (fun η : ℂ => (fderiv ℝ ω (z + η) h - fderiv ℝ ω z h * cutC η) / η) := by
  refine Integrable.mono' ((integrable_dIntegrand ω hω hc z).norm.const_mul ‖h‖) ?_ ?_
  · have h1 : Continuous fun η : ℂ => fderiv ℝ ω (z + η) h :=
      ((hω.continuous_fderiv (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).comp
        (continuous_const.add continuous_id)).clm_apply continuous_const
    have h2 : Continuous fun η : ℂ => fderiv ℝ ω z h * cutC η :=
      continuous_const.mul contDiff_cutC.continuous
    have hmeas : Measurable
        (fun η : ℂ => (fderiv ℝ ω (z + η) h - fderiv ℝ ω z h * cutC η) / η) :=
      Measurable.div (h1.measurable.sub h2.measurable) measurable_id
    exact hmeas.aestronglyMeasurable
  · filter_upwards with η
    have heq : (dIntegrand ω z η) h
        = (fderiv ℝ ω (z + η) h - fderiv ℝ ω z h * cutC η) / η := by
      rw [dIntegrand_apply, div_eq_mul_inv]
      ring
    rw [← heq]
    calc ‖(dIntegrand ω z η) h‖ ≤ ‖dIntegrand ω z η‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖h‖ * ‖dIntegrand ω z η‖ := by ring

/-! ### Linearity of the Cauchy transform -/

theorem cauchyT_add {f g : ℂ → ℂ} {z : ℂ}
    (hf : Integrable fun η : ℂ => (f (z + η) - f z * cutC η) / η)
    (hg : Integrable fun η : ℂ => (g (z + η) - g z * cutC η) / η) :
    cauchyT (fun w => f w + g w) z = cauchyT f z + cauchyT g z := by
  simp only [cauchyT]
  rw [← mul_add]
  congr 1
  rw [← integral_add hf hg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  ring

theorem cauchyT_const_mul (c : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    cauchyT (fun w => c * f w) z = c * cauchyT f z := by
  simp only [cauchyT]
  rw [show (fun η : ℂ => (c * f (z + η) - c * f z * cutC η) / η)
      = fun η : ℂ => c * ((f (z + η) - f z * cutC η) / η) from by
        funext η; ring,
    integral_const_mul]
  ring

/-! ### `cauchyT (∂̄ω) = 2 ω` -/

theorem cauchyT_dbar (ω : ℂ → ℂ) (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω) (z : ℂ) :
    cauchyT (fun w => dbar ω w) z = 2 * ω z := by
  have hcs : HasCompactSupport fun w : ℂ => dbar ω w := hasCompactSupport_dbar ω hc
  have hcont : Continuous fun w : ℂ => dbar ω w := continuous_dbar ω hω
  have hbase : Integrable fun u : ℂ => dbar ω u / (u - z) :=
    Work.Analysis.RiemannSurface.integrable_div_sub hcont hcs z
  have h1 : Integrable fun η : ℂ => dbar ω (η + z) / η := by
    have := hbase.comp_add_right z
    simpa [add_sub_cancel_right] using this
  have h2 : Integrable fun η : ℂ => dbar ω z * (cutC η / η) :=
    integrable_cutC_div.const_mul (dbar ω z)
  have hsplit : cauchyT (fun w => dbar ω w) z
      = -((Real.pi : ℂ))⁻¹ * ((∫ η : ℂ, dbar ω (η + z) / η)
          - dbar ω z * ∫ η : ℂ, cutC η / η) := by
    simp only [cauchyT]
    congr 1
    rw [show (fun η : ℂ => (dbar ω (z + η) - dbar ω z * cutC η) / η)
        = fun η : ℂ => dbar ω (η + z) / η - dbar ω z * (cutC η / η) from by
          funext η; ring]
    rw [integral_sub h1 h2, integral_const_mul]
  have hpi : ((Real.pi : ℂ))⁻¹ * ((Real.pi * 2 : ℝ) : ℂ) = 2 := by
    push_cast
    field_simp
  rw [hsplit, integral_cutC_div_eq_zero, mul_zero, sub_zero]
  have htrans : (∫ η : ℂ, dbar ω (η + z) / η) = ∫ ζ : ℂ, dbar ω ζ / (ζ - z) := by
    have := integral_add_right_eq_self (μ := volume) (fun ζ : ℂ => dbar ω ζ / (ζ - z)) z
    simpa [add_sub_cancel_right] using this
  rw [htrans, dbar_representation ω hω hc z,
    show -((Real.pi : ℂ))⁻¹ * (-(((2 * Real.pi : ℝ)) : ℂ) * ω z)
      = ((Real.pi : ℂ))⁻¹ * ((Real.pi * 2 : ℝ) : ℂ) * ω z from by ring,
    hpi]

/-! ### `∂̄ (cauchyT ω) = cauchyT (∂̄ ω)` -/

theorem dbar_cauchyT (ω : ℂ → ℂ) (hω : ContDiff ℝ 2 ω) (hc : HasCompactSupport ω) (z : ℂ) :
    dbar (cauchyT ω) z = cauchyT (fun w => dbar ω w) z := by
  have hint2 : Integrable
      (fun η : ℂ => ((fun w => Complex.I * fderiv ℝ ω w Complex.I) (z + η)
        - (fun w => Complex.I * fderiv ℝ ω w Complex.I) z * cutC η) / η) := by
    have h := (integrable_directional ω hω hc z Complex.I).const_mul Complex.I
    refine h.congr (Filter.Eventually.of_forall fun η => ?_)
    show Complex.I * ((fderiv ℝ ω (z + η) Complex.I - fderiv ℝ ω z Complex.I * cutC η) / η)
      = ((fun w => Complex.I * fderiv ℝ ω w Complex.I) (z + η)
        - (fun w => Complex.I * fderiv ℝ ω w Complex.I) z * cutC η) / η
    ring
  have hsum : cauchyT (fun w => fderiv ℝ ω w 1) z
        + cauchyT (fun w => Complex.I * fderiv ℝ ω w Complex.I) z
      = cauchyT (fun w => fderiv ℝ ω w 1 + Complex.I * fderiv ℝ ω w Complex.I) z :=
    (cauchyT_add (integrable_directional ω hω hc z 1) hint2).symm
  simp only [dbar]
  rw [fderiv_cauchyT_apply ω hω hc z 1, fderiv_cauchyT_apply ω hω hc z Complex.I,
    ← cauchyT_const_mul Complex.I (fun w => fderiv ℝ ω w Complex.I) z, hsum]

/-! ### `∂̄`-solvability on `ℂ` -/

theorem one_le_cinf : (1 : WithTop ℕ∞) ≤ cinf := by
  rw [cinf]
  exact WithTop.coe_le_coe.mpr le_top

theorem two_le_cinf : (2 : WithTop ℕ∞) ≤ cinf := by
  rw [cinf]
  exact WithTop.coe_le_coe.mpr le_top

theorem dbar_solvable (ω : ℂ → ℂ) (hω : ContDiff ℝ cinf ω) (hc : HasCompactSupport ω) :
    ∃ u : ℂ → ℂ, ContDiff ℝ cinf u ∧ ∀ z : ℂ, dbar u z = 2 * ω z :=
  ⟨cauchyT ω, contDiff_cauchyT ω hω hc,
    fun z => by
      rw [dbar_cauchyT ω (hω.of_le two_le_cinf) hc z,
        cauchyT_dbar ω (hω.of_le one_le_cinf) hc z]⟩

end Work.Analysis.Complex.DbarCauchy

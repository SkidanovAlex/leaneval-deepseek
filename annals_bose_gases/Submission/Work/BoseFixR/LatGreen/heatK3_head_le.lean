import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Deriv.Inv
import Submission.Work.BoseFixR.LatGreen.MadelungDefs
import Submission.Work.BoseFixR.LatGreen.heatK3_rpow_half_mul_exp_integrable
import Submission.Work.BoseFixR.LatGreen.heatK3_tail_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The head bound for the heat-kernel tail integral `∫₀^η (4πt)^{-3/2} e^{-a/t} dt`

For `a > 0` and `η > 0` the truncated heat-kernel integral

  `∫₀^η (4πt)^{-3/2} e^{-a/t} dt`

is finite and bounded by `√η · e^{-a/η} / (8 π^{3/2} a)`.

**Proof.**  The change of variables `u = a/t` (i.e. `t = a/u`) maps `(0, η)` onto
`(a/η, ∞)` with `dt = -(a/u²) du`, and

  `(4π (a/u))^{-3/2} · (a/u²) = (4π)^{-3/2} a^{-1/2} u^{-1/2}`,

so

  `∫₀^η (4πt)^{-3/2} e^{-a/t} dt = (4π)^{-3/2} a^{-1/2} ∫_{a/η}^∞ u^{-1/2} e^{-u} du`

(exactly the substitution computed in `HeatIntegral` for the untruncated `(0,∞)` case).
On the remaining half line `u > a/η` one has `u^{-1/2} ≤ (a/η)^{-1/2}` and
`∫_{a/η}^∞ e^{-u} du = e^{-a/η}`, giving

  `... ≤ (4π)^{-3/2} a^{-1/2} (a/η)^{-1/2} e^{-a/η}
       = (4π)^{-3/2} a^{-1} √η · e^{-a/η}
       = √η e^{-a/η} / (8 π^{3/2} a)`.

The change of variables is the Mathlib one-dimensional Jacobian formula
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` applied to the injective
differentiable map `u ↦ a/u` on `Set.Ioi (a/η)` (whose image is `Set.Ioo 0 η`).
-/

namespace Work.BoseFixR.LatGreen

theorem heatK3_head_le {a η : ℝ} (ha : 0 < a) (hη : 0 < η) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / t)))
      (Set.Ioc 0 η) ∧
    ∫ t in Set.Ioc 0 η, (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / t))
      ≤ Real.sqrt η * Real.exp (-(a / η)) / (8 * Real.pi ^ (3 / 2 : ℝ) * a) := by
  set c : ℝ := a / η with hc_def
  have hc : 0 < c := by rw [hc_def]; positivity
  set F : ℝ → ℝ := fun t => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / t)) with hF
  set hfun : ℝ → ℝ := fun u => (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * a ^ (-(1 / 2 : ℝ))
      * (u ^ (-(1 / 2 : ℝ)) * Real.exp (-u)) with hhfun
  -- the substituting map `u ↦ a/u` is differentiable on `Ioi c`
  have hφderiv : ∀ u ∈ Set.Ioi c,
      HasDerivWithinAt (fun u : ℝ => a / u) (-(a / u^2)) (Set.Ioi c) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (lt_trans hc hu)
    have h : HasDerivAt (fun y : ℝ => y⁻¹) (-(u^2)⁻¹) u := hasDerivAt_inv hu0
    have h2 : HasDerivAt (fun y : ℝ => a * y⁻¹) (a * (-(u^2)⁻¹)) u := h.const_mul a
    have h3 : HasDerivAt (fun y : ℝ => a / y) (-(a / u^2)) u := by
      have h2' : HasDerivAt (fun y : ℝ => a / y) (a * (-(u^2)⁻¹)) u := h2
      convert h2' using 1
      ring
    exact h3.hasDerivWithinAt
  -- ... it is injective there
  have hφinj : Set.InjOn (fun u : ℝ => a / u) (Set.Ioi c) := by
    intro x hx y hy hxy
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans hc hx)
    have hy0 : y ≠ 0 := ne_of_gt (lt_trans hc hy)
    have h1 : a * y = a * x := (div_eq_div_iff hx0 hy0).mp hxy
    exact (mul_left_cancel₀ (ne_of_gt ha) h1).symm
  -- ... and its image is exactly `(0, η)`
  have himg : (fun u : ℝ => a / u) '' Set.Ioi c = Set.Ioo 0 η := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu0 : 0 < u := lt_trans hc hu
      have hlt : a / u < a / c := div_lt_div_of_pos_left ha hc hu
      have heq : a / c = η := by rw [hc_def]; field_simp
      exact ⟨div_pos ha hu0, by rw [← heq]; exact hlt⟩
    · rintro ⟨ht0, ht1⟩
      refine ⟨a / t, ?_, ?_⟩
      · rw [hc_def]; exact div_lt_div_of_pos_left ha ht0 ht1
      · field_simp
  -- the pointwise substitution identity for the integrand
  have hpt : ∀ u ∈ Set.Ioi c, |-(a / u^2)| • F (a / u) = hfun u := by
    intro u hu
    have hu0 : 0 < u := lt_trans hc hu
    have h1 : a / (a / u) = u := by field_simp
    have h2 : (4 * Real.pi * (a / u)) ^ (-(3 / 2 : ℝ))
        = (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * a ^ (-(3 / 2 : ℝ)) * u ^ (3 / 2 : ℝ) := by
      rw [show (4 : ℝ) * Real.pi * (a / u) = 4 * Real.pi * a / u by ring]
      rw [Real.div_rpow (by positivity) (le_of_lt hu0), Real.mul_rpow (by positivity) (le_of_lt ha),
        Real.rpow_neg (le_of_lt hu0), div_eq_mul_inv, inv_inv]
    have hu2inv : (u ^ 2)⁻¹ = u ^ (-2 : ℝ) := by
      rw [← Real.rpow_natCast u 2, ← Real.rpow_neg_one, ← Real.rpow_mul (le_of_lt hu0)]
      norm_num
    have hA : (a / u ^ 2) * u ^ (3 / 2 : ℝ) = a * u ^ (-(1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, hu2inv, mul_assoc, ← Real.rpow_add hu0]
      norm_num
    have hB0 : a ^ (-(3 / 2 : ℝ)) * a = a ^ (-(1 / 2 : ℝ)) := by
      have hh := Real.rpow_add ha (-(3 / 2 : ℝ)) (1 : ℝ)
      rw [show (-(3 / 2 : ℝ) + 1) = -(1 / 2 : ℝ) by norm_num, Real.rpow_one] at hh
      exact hh.symm
    have hB : a ^ (-(3 / 2 : ℝ)) * (a * u ^ (-(1 / 2 : ℝ)))
        = a ^ (-(1 / 2 : ℝ)) * u ^ (-(1 / 2 : ℝ)) := by rw [← mul_assoc, hB0]
    have habs : |-(a / u^2)| = a / u^2 := by
      rw [abs_neg, abs_of_pos (div_pos ha (pow_pos hu0 2))]
    rw [habs, smul_eq_mul, hF, hhfun]
    beta_reduce
    rw [h1, h2, show (a / u ^ 2)
        * ((4 * Real.pi) ^ (-(3 / 2 : ℝ)) * a ^ (-(3 / 2 : ℝ)) * u ^ (3 / 2 : ℝ)
            * Real.exp (-u))
      = (4 * Real.pi) ^ (-(3 / 2 : ℝ))
          * (a ^ (-(3 / 2 : ℝ)) * ((a / u ^ 2) * u ^ (3 / 2 : ℝ))) * Real.exp (-u) by ring]
    rw [hA, hB]
    ring
  -- integrability of the transformed integrand on `Ioi c`
  have hIntBase : MeasureTheory.IntegrableOn
      (fun u : ℝ => u ^ (-(1 / 2 : ℝ)) * Real.exp (-u)) (Set.Ioi c) :=
    heatK3_rpow_half_mul_exp_integrable hc
  have hIntH : MeasureTheory.IntegrableOn hfun (Set.Ioi c) := by
    rw [hhfun]
    exact hIntBase.const_mul ((4 * Real.pi) ^ (-(3 / 2 : ℝ)) * a ^ (-(1 / 2 : ℝ)))
  have hIntT : MeasureTheory.IntegrableOn (fun u : ℝ => |-(a / u^2)| • F (a / u)) (Set.Ioi c) :=
    hIntH.congr_fun (fun u hu => (hpt u hu).symm) measurableSet_Ioi
  -- transfer integrability along the change of variables, `Ioo 0 η` then `Ioc 0 η`
  have hIntF_oo : MeasureTheory.IntegrableOn F (Set.Ioo 0 η) := by
    rw [← himg]
    exact (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      hφderiv hφinj F).mpr hIntT
  have hIntF : MeasureTheory.IntegrableOn F (Set.Ioc 0 η) :=
    hIntF_oo.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := η)).symm
  refine ⟨hIntF, ?_⟩
  -- the exact value of the truncated integral, by the change of variables
  have hcov : ∫ t in Set.Ioc 0 η, F t = ∫ u in Set.Ioi c, hfun u := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := η)).symm]
    rw [← himg]
    rw [MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hφderiv hφinj F]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => hpt u hu)
  rw [hcov]
  -- the tail estimate on `(a/η, ∞)`
  have htail : ∫ u in Set.Ioi (a / η), hfun u
      ≤ Real.sqrt η * Real.exp (-(a / η)) / (8 * Real.pi ^ (3 / 2 : ℝ) * a) := by
    simpa only [hhfun] using heatK3_tail_bound ha hη
  rw [hc_def]
  exact htail

end Work.BoseFixR.LatGreen

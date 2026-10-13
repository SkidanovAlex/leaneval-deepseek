import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.thetaBoxAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- **The `𝓛`-half of the box coercivity.**  On the open box `(0,R) × (0,π/2)`, the
weighted pairing `∫∫ 𝓛g · g · θW` is at least half of `∫∫ g² · θW`.  The input is the
per-`θ` `z`-integration by parts over the closed interval `[0,R]` (`hzibp`), together
with the joint integrability of the two integrands on the box. -/
theorem box_L_lower (α : ℝ) (g : ℝ → ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hzibp : ∀ θ ∈ Spaces.Iθ,
      ∫ z in Set.Icc 0 R, L g z θ * g z θ * Spaces.w z ^ 2
        = (1 / 2) * (∫ z in Set.Icc 0 R, (g z θ * Spaces.w z) ^ 2)
          + (1 / 2) * (R * (g R θ * Spaces.w R) ^ 2))
    (hIntL : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => L g z θ * g z θ * thetaW α z θ))
      (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)))
    (hIntE : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => g z θ * g z θ * thetaW α z θ))
      (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2))) :
    (1 / 2) * (∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2),
        g p.1 p.2 * g p.1 p.2 * thetaW α p.1 p.2)
      ≤ ∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2),
          L g p.1 p.2 * g p.1 p.2 * thetaW α p.1 p.2 := by
  set μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo 0 R) with hμ
  set ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2)) with hν
  let Gp : ℝ × ℝ → ℝ := Function.uncurry (fun z θ => L g z θ * g z θ * thetaW α z θ)
  let Bp : ℝ × ℝ → ℝ := Function.uncurry (fun z θ => g z θ * g z θ * thetaW α z θ)
  have hmeas : μ.prod ν
      = (volume : Measure (ℝ × ℝ)).restrict (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [hμ, hν, MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  have hGp : MeasureTheory.Integrable Gp (μ.prod ν) := by rw [hmeas]; exact hIntL
  have hBp : MeasureTheory.Integrable Bp (μ.prod ν) := by rw [hmeas]; exact hIntE
  have hkey : ∀ᵐ θ ∂ν, (1 / 2) * (∫ z, Bp (z, θ) ∂μ) ≤ ∫ z, Gp (z, θ) ∂μ := by
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Set.Ioo 0 (π / 2)) measurableSet_Ioo]
      with θ hθ
    have hθI : θ ∈ Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsinpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hrpow_nn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) :=
      Real.rpow_nonneg (le_of_lt hsinpos) _
    have hz := hzibp θ hθI
    have h1 : (∫ z, Gp (z, θ) ∂μ)
        = (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) *
            (∫ z in Set.Ioo 0 R, L g z θ * g z θ * Spaces.w z ^ 2) := by
      rw [hμ]
      rw [show (∫ z in Set.Ioo 0 R, Gp (z, θ))
          = ∫ z in Set.Ioo 0 R,
              (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (L g z θ * g z θ * Spaces.w z ^ 2)
          from MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun z _ => by
            simp only [Gp, Function.uncurry, thetaW_eq]; ring)]
      rw [MeasureTheory.integral_const_mul]
    have h2 : (∫ z in Set.Ioo 0 R, L g z θ * g z θ * Spaces.w z ^ 2)
        = (1 / 2) * (∫ z in Set.Ioo 0 R, (g z θ * Spaces.w z) ^ 2)
          + (1 / 2) * (R * (g R θ * Spaces.w R) ^ 2) := by
      rw [← integral_Icc_eq_Ioo (fun z => L g z θ * g z θ * Spaces.w z ^ 2) 0 R,
        ← integral_Icc_eq_Ioo (fun z => (g z θ * Spaces.w z) ^ 2) 0 R]
      exact hz
    have h4 : (1 / 2) * (∫ z, Bp (z, θ) ∂μ)
        = (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) *
            ((1 / 2) * (∫ z in Set.Ioo 0 R, (g z θ * Spaces.w z) ^ 2)) := by
      rw [hμ]
      rw [show (∫ z in Set.Ioo 0 R, Bp (z, θ))
          = ∫ z in Set.Ioo 0 R,
              (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ * Spaces.w z) ^ 2
          from MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun z _ => by
            simp only [Bp, Function.uncurry, thetaW_eq]; ring)]
      rw [MeasureTheory.integral_const_mul]
      ring
    rw [h1, h4, h2]
    have hnn : 0 ≤ (1 / 2) * (R * (g R θ * Spaces.w R) ^ 2) := by positivity
    nlinarith [hrpow_nn, hnn]
  have hBzI : MeasureTheory.Integrable (fun θ => ∫ z, Bp (z, θ) ∂μ) ν :=
    hBp.integral_prod_right
  have hGzI : MeasureTheory.Integrable (fun θ => ∫ z, Gp (z, θ) ∂μ) ν :=
    hGp.integral_prod_right
  have hmono : (∫ θ, (1 / 2) * (∫ z, Bp (z, θ) ∂μ) ∂ν)
      ≤ (∫ θ, ∫ z, Gp (z, θ) ∂μ ∂ν) :=
    MeasureTheory.integral_mono_ae (hBzI.const_mul (1 / 2)) hGzI hkey
  have hmono2 : (∫ θ, (1 / 2) * (∫ z, Bp (z, θ) ∂μ) ∂ν)
      = (1 / 2) * (∫ θ, ∫ z, Bp (z, θ) ∂μ ∂ν) :=
    MeasureTheory.integral_const_mul _ _
  have hAG : (∫ p, Gp p ∂(μ.prod ν)) = ∫ θ, ∫ z, Gp (z, θ) ∂μ ∂ν :=
    MeasureTheory.integral_prod_symm Gp hGp
  have hAB : (∫ p, Bp p ∂(μ.prod ν)) = ∫ θ, ∫ z, Bp (z, θ) ∂μ ∂ν :=
    MeasureTheory.integral_prod_symm Bp hBp
  change (1 / 2) * (∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2), Bp p)
      ≤ ∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2), Gp p
  rw [show (∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2), Bp p)
        = ∫ p, Bp p ∂(μ.prod ν) from by rw [hmeas],
      show (∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2), Gp p)
        = ∫ p, Gp p ∂(μ.prod ν) from by rw [hmeas]]
  rw [hAB, hAG, ← hmono2]
  exact hmono

/-- **The angular-transport half of the box coercivity.**  On the open box
`(0,R) × (0,π/2)`, the weighted pairing `∫∫ (3/(1+z)) D_θg · g · θW` is at most
`(3α/10) ∫∫ g² · θW`.  The input is the per-`z` angular integration by parts
(`hθibp`), together with the joint integrability of the two integrands on the box. -/
theorem box_T_upper (α : ℝ) (hα : 0 < α) (g : ℝ → ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hθibp : ∀ z ∈ Set.Ioo 0 R,
      ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth g z θ * g z θ
        = (Spaces.gam α - 1) * ∫ θ in Spaces.Iθ,
            Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2)
    (hIntT : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (3 / (1 + z)) * Spaces.Dth g z θ * g z θ * thetaW α z θ))
      (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)))
    (hIntE : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => g z θ * g z θ * thetaW α z θ))
      (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2))) :
    ∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2),
        (3 / (1 + p.1)) * Spaces.Dth g p.1 p.2 * g p.1 p.2 * thetaW α p.1 p.2
      ≤ (3 * α / 10) * (∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2),
          g p.1 p.2 * g p.1 p.2 * thetaW α p.1 p.2) := by
  set μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo 0 R) with hμ
  set ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2)) with hν
  let Tp : ℝ × ℝ → ℝ :=
    Function.uncurry (fun z θ => (3 / (1 + z)) * Spaces.Dth g z θ * g z θ * thetaW α z θ)
  let Bp : ℝ × ℝ → ℝ := Function.uncurry (fun z θ => g z θ * g z θ * thetaW α z θ)
  have hmeas : μ.prod ν
      = (volume : Measure (ℝ × ℝ)).restrict (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [hμ, hν, MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  have hTp : MeasureTheory.Integrable Tp (μ.prod ν) := by rw [hmeas]; exact hIntT
  have hBp : MeasureTheory.Integrable Bp (μ.prod ν) := by rw [hmeas]; exact hIntE
  have hBslice : ∀ᵐ z ∂μ, MeasureTheory.Integrable (fun θ => Bp (z, θ)) ν := hBp.prod_right_ae
  have hνIθ : ν = (volume : Measure ℝ).restrict Spaces.Iθ := by
    rw [hν]
    simpa [Spaces.Iθ] using (MeasureTheory.Measure.restrict_congr_set (ae_eq_Ioo_Icc 0 (π / 2)))
  have hIθ : ∀ f : ℝ → ℝ,
      (∫ θ in Spaces.Iθ, f θ) = ∫ θ in Set.Ioo 0 (π / 2), f θ :=
    fun f => integral_Icc_eq_Ioo f 0 (π / 2)
  have hkey : ∀ᵐ z ∂μ,
      (∫ θ, Tp (z, θ) ∂ν) ≤ 3 * (Spaces.gam α - 1) * (∫ θ, Bp (z, θ) ∂ν) := by
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Set.Ioo 0 R) measurableSet_Ioo, hBslice]
      with z hz hBz
    have hzpos : 0 < z := hz.1
    have h1zpos : 0 < 1 + z := by linarith
    have hz0 : z ≠ 0 := ne_of_gt hzpos
    have hwne : Spaces.w z ^ 2 ≠ 0 := by
      rw [Spaces.w]
      exact pow_ne_zero 2 (div_ne_zero (pow_ne_zero 2 (by positivity)) (pow_ne_zero 2 hz0))
    -- the θ-slice of `g² θW` and of `sin^{-γ} g²`
    have hXν : MeasureTheory.Integrable
        (fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2) ν := by
      refine (hBz.const_mul ((Spaces.w z) ^ 2)⁻¹).congr
        (Filter.Eventually.of_forall (fun θ => ?_))
      have hw1 : Spaces.w z ≠ 0 := by
        rw [Spaces.w]
        exact div_ne_zero (pow_ne_zero 2 (by positivity)) (pow_ne_zero 2 hz0)
      simp only [Bp, Function.uncurry]
      rw [thetaW_eq]
      rw [show (Spaces.w z ^ 2)⁻¹ *
            (g z θ * g z θ * (Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))))
          = ((Spaces.w z ^ 2)⁻¹ * Spaces.w z ^ 2) *
              (g z θ * g z θ * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) from by ring]
      rw [inv_mul_cancel₀ (pow_ne_zero 2 hw1), one_mul]
      ring
    have hXθ : MeasureTheory.Integrable
        (fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2)
        ((volume : Measure ℝ).restrict Spaces.Iθ) := by
      rw [← hνIθ]; exact hXν
    have hCθ : MeasureTheory.Integrable
        (fun θ => Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2)
        ((volume : Measure ℝ).restrict Spaces.Iθ) := by
      refine hXθ.mono' ?_ ?_
      · have h1 : AEStronglyMeasurable (fun θ : ℝ => Real.cos (2 * θ))
            ((volume : Measure ℝ).restrict Spaces.Iθ) :=
          (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
        refine (h1.mul hXθ.aestronglyMeasurable).congr ?_
        filter_upwards with θ
        simp only [Pi.mul_apply]
        ring
      · filter_upwards [MeasureTheory.ae_restrict_mem (s := Spaces.Iθ) measurableSet_Icc]
          with θ hθI
        rw [Real.norm_eq_abs]
        have hsin_nn : 0 ≤ Real.sin (2 * θ) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθI.1])
            (by linarith [hθI.2, Real.pi_pos])
        have hSnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := Real.rpow_nonneg hsin_nn _
        have hGnn : 0 ≤ (g z θ) ^ 2 := sq_nonneg _
        rw [abs_mul, abs_mul, abs_of_nonneg hSnn, abs_of_nonneg hGnn]
        calc |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2
            ≤ 1 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one (2 * θ)) hSnn) hGnn
          _ = (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2 := by ring
    -- the two `θ`-integral identifications
    have hTeq : (∫ θ, Tp (z, θ) ∂ν)
        = (3 / (1 + z)) * (Spaces.w z) ^ 2 *
            (∫ θ in Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth g z θ * g z θ) := by
      rw [hν]
      rw [show (∫ θ in Set.Ioo 0 (π / 2), Tp (z, θ))
          = ∫ θ in Set.Ioo 0 (π / 2),
              ((3 / (1 + z)) * (Spaces.w z) ^ 2) *
                ((Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth g z θ * g z θ)
          from MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by
            simp only [Tp, Function.uncurry, thetaW_eq]; ring)]
      rw [MeasureTheory.integral_const_mul]
      rw [hIθ (fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth g z θ * g z θ)]
    have hBeq : (∫ θ, Bp (z, θ) ∂ν)
        = (Spaces.w z) ^ 2 *
            (∫ θ in Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2) := by
      rw [hν]
      rw [show (∫ θ in Set.Ioo 0 (π / 2), Bp (z, θ))
          = ∫ θ in Set.Ioo 0 (π / 2),
              (Spaces.w z) ^ 2 *
                ((Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2)
          from MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by
            simp only [Bp, Function.uncurry, thetaW_eq]; ring)]
      rw [MeasureTheory.integral_const_mul]
      rw [hIθ (fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2)]
    have hcosle : (∫ θ in Spaces.Iθ,
          Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2)
        ≤ (∫ θ in Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2) := by
      refine MeasureTheory.integral_mono_ae hCθ hXθ ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (s := Spaces.Iθ) measurableSet_Icc]
        with θ hθI
      have hsin_nn : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθI.1])
          (by linarith [hθI.2, Real.pi_pos])
      have hXnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2 :=
        mul_nonneg (Real.rpow_nonneg hsin_nn _) (sq_nonneg _)
      calc Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2
          = Real.cos (2 * θ) * ((Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2) := by
            ring
        _ ≤ 1 * ((Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2) :=
            mul_le_mul_of_nonneg_right (Real.cos_le_one (2 * θ)) hXnn
        _ = (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2 := one_mul _
    have hVle : (∫ θ in Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth g z θ * g z θ)
        ≤ (Spaces.gam α - 1) * (∫ θ in Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2) := by
      rw [hθibp z hz]
      exact mul_le_mul_of_nonneg_left hcosle (by rw [Spaces.gam]; linarith)
    have hYnn : 0 ≤ (∫ θ in Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2) := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (s := Spaces.Iθ) measurableSet_Icc]
        with θ hθI
      exact mul_nonneg (Real.rpow_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθI.1])
          (by linarith [hθI.2, Real.pi_pos])) _) (sq_nonneg _)
    rw [hTeq, hBeq]
    have h3 : 3 / (1 + z) ≤ 3 := by
      rw [div_le_iff₀ h1zpos]; nlinarith [hzpos]
    have hcoef2 : (3 / (1 + z)) * (Spaces.gam α - 1) ≤ 3 * (Spaces.gam α - 1) :=
      mul_le_mul_of_nonneg_right h3 (by rw [Spaces.gam]; linarith)
    have hYv : 0 ≤ (Spaces.w z) ^ 2 * (∫ θ in Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2) :=
      mul_nonneg (sq_nonneg _) hYnn
    calc (3 / (1 + z)) * (Spaces.w z) ^ 2 * (∫ θ in Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth g z θ * g z θ)
        ≤ (3 / (1 + z)) * (Spaces.w z) ^ 2 * ((Spaces.gam α - 1) * (∫ θ in Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left hVle
          exact mul_nonneg (by positivity) (sq_nonneg _)
      _ = ((3 / (1 + z)) * (Spaces.gam α - 1)) * ((Spaces.w z) ^ 2 * (∫ θ in Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2)) := by ring
      _ ≤ (3 * (Spaces.gam α - 1)) * ((Spaces.w z) ^ 2 * (∫ θ in Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (g z θ) ^ 2)) :=
          mul_le_mul_of_nonneg_right hcoef2 hYv
  have hTzI : MeasureTheory.Integrable (fun z => ∫ θ, Tp (z, θ) ∂ν) μ :=
    hTp.integral_prod_left
  have hBzI : MeasureTheory.Integrable (fun z => ∫ θ, Bp (z, θ) ∂ν) μ :=
    hBp.integral_prod_left
  have hmono : (∫ z, ∫ θ, Tp (z, θ) ∂ν ∂μ)
      ≤ (∫ z, 3 * (Spaces.gam α - 1) * (∫ θ, Bp (z, θ) ∂ν) ∂μ) :=
    MeasureTheory.integral_mono_ae hTzI (hBzI.const_mul (3 * (Spaces.gam α - 1))) hkey
  have hmono2 : (∫ z, 3 * (Spaces.gam α - 1) * (∫ θ, Bp (z, θ) ∂ν) ∂μ)
      = 3 * (Spaces.gam α - 1) * (∫ z, ∫ θ, Bp (z, θ) ∂ν ∂μ) :=
    MeasureTheory.integral_const_mul _ _
  have hTF : (∫ p, Tp p ∂(μ.prod ν)) = ∫ z, ∫ θ, Tp (z, θ) ∂ν ∂μ :=
    MeasureTheory.integral_prod Tp hTp
  have hBF : (∫ p, Bp p ∂(μ.prod ν)) = ∫ z, ∫ θ, Bp (z, θ) ∂ν ∂μ :=
    MeasureTheory.integral_prod Bp hBp
  have hcoef : 3 * α / 10 = 3 * (Spaces.gam α - 1) := by rw [Spaces.gam]; ring
  change (∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2), Tp p)
      ≤ (3 * α / 10) * (∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2), Bp p)
  rw [show (∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2), Tp p)
        = ∫ p, Tp p ∂(μ.prod ν) from by rw [hmeas],
      show (∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2), Bp p)
        = ∫ p, Bp p ∂(μ.prod ν) from by rw [hmeas]]
  rw [hTF, hBF, hcoef, ← hmono2]
  exact hmono

/-- The finite-`z`-interval ("box") coercivity estimate of §6: on the box
`(0,R) × (0,π/2)`, the pairing `∫∫ 𝓛(D_θ f)·D_θ f · θW` — with `θW = w²sin(2θ)^{-γ}` —
dominates `(1/2 - 3α/10)` times the energy `∫∫ (D_θ f)² · θW`.

It is assembled from the `𝓛`-half (`box_L_lower`, the `z`-integration by parts `hzibp`) and
the angular-transport half (`box_T_upper`, the `θ`-integration by parts `hθibp`). -/
theorem box_ineq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) (R K : ℝ) (hR : 0 < R)
    (hcont : ContinuousOn (Function.uncurry (fun z θ => L (Spaces.Dth f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))) (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2))
      ∧ ContinuousOn (Function.uncurry (fun z θ => (3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth (Spaces.Dth f) z θ * Spaces.Dth f z θ)) (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2))
      ∧ ContinuousOn (Function.uncurry (fun z θ => (Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))) (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2))
      ∧ ContinuousOn (Function.uncurry (fun z θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Spaces.Dth f z θ) ^ 2)) (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)))
    (hdom : (∀ z ∈ Set.Ioo 0 R, ∀ θ ∈ Spaces.Iθ, |L (Spaces.Dth f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))| ≤ K)
      ∧ (∀ z ∈ Set.Ioo 0 R, ∀ θ ∈ Spaces.Iθ, |(3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth (Spaces.Dth f) z θ * Spaces.Dth f z θ| ≤ K)
      ∧ (∀ z ∈ Set.Ioo 0 R, ∀ θ ∈ Spaces.Iθ, |(Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))| ≤ K)
      ∧ (∀ z ∈ Set.Ioo 0 R, ∀ θ ∈ Spaces.Iθ, |(Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Spaces.Dth f z θ) ^ 2| ≤ K))
    (hIntT : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => (3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth (Spaces.Dth f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2)) (Set.Icc 0 R ×ˢ Spaces.Iθ))
    (hzibp : ∀ θ ∈ Spaces.Iθ, ∫ z in Set.Icc 0 R, L (Spaces.Dth f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2
      = (1 / 2) * (∫ z in Set.Icc 0 R, (Spaces.Dth f z θ * Spaces.w z) ^ 2)
        + (1 / 2) * (R * (Spaces.Dth f R θ * Spaces.w R) ^ 2))
    (hθibp : ∀ z ∈ Set.Ioo 0 R, ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth (Spaces.Dth f) z θ * Spaces.Dth f z θ
      = (Spaces.gam α - 1) * ∫ θ in Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Spaces.Dth f z θ) ^ 2) :
    (1 / 2 - 3 * α / 10) * (∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2), Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2)
      ≤ ∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2), Aop (Spaces.Dth f) p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2 := by
  have hIntL : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => L (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)) := by
    refine (integrableOn_Ioo_prod_of_continuousOn (K := K) hcont.1 (fun p hp => ?_)).congr_fun ?_ ?_
    · rw [Real.norm_eq_abs]
      exact hdom.1 p.1 hp.1 p.2 ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
    · intro p hp
      simp only [Function.uncurry, thetaW_eq]
      ring
    · exact measurableSet_Ioo.prod measurableSet_Ioo
  have hIntE : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)) := by
    refine (integrableOn_Ioo_prod_of_continuousOn (K := K) hcont.2.2.1 (fun p hp => ?_)).congr_fun ?_ ?_
    · rw [Real.norm_eq_abs]
      exact hdom.2.2.1 p.1 hp.1 p.2 ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
    · intro p hp
      simp only [Function.uncurry, thetaW_eq]
      ring
    · exact measurableSet_Ioo.prod measurableSet_Ioo
  have hIntT' : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => (3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth (Spaces.Dth f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2))
      (volume.restrict (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2))) := by
    rw [restrict_box_eq R]
    exact hIntT
  have hIntT'' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (3 / (1 + z)) * Spaces.Dth (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)) := by
    refine hIntT'.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, thetaW_eq]
    ring
  have hLA := box_L_lower α (Spaces.Dth f) R hR hzibp hIntL hIntE
  have hTB := box_T_upper α hα (Spaces.Dth f) R hR hθibp hIntT'' hIntE
  have hsplit : (∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2),
          Aop (Spaces.Dth f) p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2)
      = (∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2),
            L (Spaces.Dth f) p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2)
        - (∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2),
            (3 / (1 + p.1)) * Spaces.Dth (Spaces.Dth f) p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2) := by
    rw [← MeasureTheory.integral_sub
      (f := fun p : ℝ × ℝ => L (Spaces.Dth f) p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2)
      (g := fun p : ℝ × ℝ => (3 / (1 + p.1)) * Spaces.Dth (Spaces.Dth f) p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2)
      hIntL hIntT'']
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    simp only [Aop]
    ring
  rw [hsplit]
  nlinarith [hLA, hTB]

end Work.Coercivity

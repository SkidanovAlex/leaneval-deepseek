import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.gamDth_l2_bound
import Submission.Work.Coercivity.integral_sin_two_neg_rpow_le

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

theorem DthGam_sq_lintegral_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hΓ2 : Work.Coercivity.GammaPointwiseBnd α) :
    MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (fun θ : ℝ => (ENNReal.ofReal (|Work.Coercivity.DthGam α 0 θ|
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))) ^ 2)
      ≤ ENNReal.ofReal (100 * α) := by
  set q : ℝ := 1 - 17 * α / 30 with hqdef
  have hq0 : 0 < q := by simp only [hqdef]; linarith
  have hq1 : q < 1 := by simp only [hqdef]; linarith
  obtain ⟨hBint, hBval⟩ := integral_sin_two_neg_rpow_le q hq0 hq1
  have hmaj : MeasureTheory.Integrable
      (fun θ : ℝ => 4 * α ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      (MeasureTheory.volume.restrict Spaces.Iθ) := hBint.const_mul _
  have hmaj_nn : 0 ≤ᵐ[MeasureTheory.volume.restrict Spaces.Iθ]
      (fun θ : ℝ => 4 * α ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hs0 _)
  -- the pointwise rewriting of the integrand on `Iθ`
  have hpt : ∀ θ ∈ Spaces.Iθ, (ENNReal.ofReal (|DthGam α 0 θ|
        * (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2)))) ^ 2
      = ENNReal.ofReal ((DthGam α 0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) := by
    intro θ hθ
    have hs0 : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hgam : Spaces.gam α ≠ 0 := by simp only [Spaces.gam]; intro h; linarith
    have hne : -(Spaces.gam α / 2) + -(Spaces.gam α / 2) ≠ 0 := by
      intro h; exact hgam (by linarith)
    have hpow : ((Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
      rw [sq, ← Real.rpow_add' hs0 hne]
      congr 1
      ring
    rw [← ENNReal.ofReal_pow (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hs0 _))]
    congr 1
    rw [mul_pow, sq_abs, hpow]
  -- the a.e. comparison with the integrable majorant
  have hle : (fun θ : ℝ => ENNReal.ofReal
        ((DthGam α 0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))))
      ≤ᵐ[MeasureTheory.volume.restrict Spaces.Iθ]
      (fun θ : ℝ => ENNReal.ofReal (4 * α ^ 2 * (Real.sin (2 * θ)) ^ (-q))) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    apply ENNReal.ofReal_le_ofReal
    have h := gamDth_integrand_le α hα hα1 hΓ2 θ hθ
    have hexp : 2 * α / 3 - Spaces.gam α = -q := by simp only [hqdef, Spaces.gam]; ring
    calc (DthGam α 0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
        = (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (DthGam α 0 θ) ^ 2 := by ring
      _ ≤ 4 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Spaces.gam α) := h
      _ = 4 * α ^ 2 * (Real.sin (2 * θ)) ^ (-q) := by rw [hexp]
  have h1 : 1 - q = 17 * α / 30 := by simp only [hqdef]; ring
  have hnum : 4 * α ^ 2 * (4 / (17 * α / 30)) = 480 * α / 17 := by
    field_simp
    ring
  calc MeasureTheory.lintegral (MeasureTheory.volume.restrict Spaces.Iθ)
        (fun θ : ℝ => (ENNReal.ofReal (|DthGam α 0 θ|
          * (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2)))) ^ 2)
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict Spaces.Iθ)
        (fun θ : ℝ => ENNReal.ofReal
          ((DthGam α 0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))) := by
        apply MeasureTheory.lintegral_congr_ae
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact hpt θ hθ
    _ ≤ MeasureTheory.lintegral (MeasureTheory.volume.restrict Spaces.Iθ)
        (fun θ : ℝ => ENNReal.ofReal (4 * α ^ 2 * (Real.sin (2 * θ)) ^ (-q))) :=
        MeasureTheory.lintegral_mono_ae hle
    _ = ENNReal.ofReal (∫ θ in Spaces.Iθ, 4 * α ^ 2 * (Real.sin (2 * θ)) ^ (-q)) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmaj hmaj_nn).symm
    _ = ENNReal.ofReal (4 * α ^ 2 * ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ ENNReal.ofReal (100 * α) := by
        apply ENNReal.ofReal_le_ofReal
        calc 4 * α ^ 2 * ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            ≤ 4 * α ^ 2 * (4 / (1 - q)) := mul_le_mul_of_nonneg_left hBval (by positivity)
          _ = 4 * α ^ 2 * (4 / (17 * α / 30)) := by rw [h1]
          _ = 480 * α / 17 := hnum
          _ ≤ 100 * α := by
              rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 17)]
              nlinarith [hα]

end Work.Coercivity

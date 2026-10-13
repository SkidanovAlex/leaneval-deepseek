import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.thetaAux
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

/-- The pointwise form of the paper's condition `(GammaAssumption2)`:
`(D_θΓ)² ≤ 4α²Γ²`.  Indeed `D_θΓ = sin(2θ) ∂_θΓ` (`DthGam_eq`), so the hypothesis
`|D_θΓ| ≤ 2αΓ` becomes this after squaring. -/
theorem DthGam_sq_le_GamSq (α : ℝ) (hΓ2 : GammaPointwiseBnd α) (θ : ℝ)
    (hθ : θ ∈ Spaces.Iθ) :
    (DthGam α 0 θ) ^ 2 ≤ 4 * α ^ 2 * (Spaces.Gam α θ) ^ 2 := by
  have h := hΓ2 θ hθ
  change (Real.sin (2 * θ) * deriv (fun t => Spaces.Gam α t) θ) ^ 2
      ≤ 4 * α ^ 2 * (Spaces.Gam α θ) ^ 2
  set g : ℝ := deriv (fun t => Spaces.Gam α t) θ with hg
  have hb : 0 ≤ 2 * α * Spaces.Gam α θ := le_trans (abs_nonneg _) h
  have habs : |Real.sin (2 * θ) * g| ≤ |2 * α * Spaces.Gam α θ| := by
    rwa [abs_of_nonneg hb]
  have hsq := sq_le_sq.mpr habs
  calc (Real.sin (2 * θ) * g) ^ 2 ≤ (2 * α * Spaces.Gam α θ) ^ 2 := hsq
    _ = 4 * α ^ 2 * (Spaces.Gam α θ) ^ 2 := by ring

/-- `Γ(θ)² ≤ sin(2θ)^{2α/3}` on the angular interval, for `α > 0`.

Since `Γ = (sin θ cos²θ)^{α/3}` and `sin θ cos²θ ≤ sin(2θ)` on `Iθ` (because
`cos θ ≤ 1 ≤ 2`), this is monotonicity of `rpow` with the nonnegative exponent `2α/3`. -/
theorem Gam_sq_le_sin_two (α : ℝ) (hα : 0 < α) (θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    (Spaces.Gam α θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ (2 * α / 3) := by
  obtain ⟨hb0, hb1⟩ := Spaces.sin_mul_cos_sq_mem_Icc θ hθ
  have hsq : (Spaces.Gam α θ) ^ 2 = (Real.sin θ * Real.cos θ ^ 2) ^ (2 * α / 3) := by
    rw [Spaces.Gam, ← Real.rpow_natCast ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)) 2]
    calc ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)) ^ (2 : ℝ)
        = (Real.sin θ * Real.cos θ ^ 2) ^ ((α / 3) * 2) :=
          (Real.rpow_mul hb0 (α / 3) 2).symm
      _ = (Real.sin θ * Real.cos θ ^ 2) ^ (2 * α / 3) := by
          rw [show α / 3 * 2 = 2 * α / 3 by ring]
  rw [hsq]
  refine Real.rpow_le_rpow hb0 ?_ (by positivity)
  rw [Real.sin_two_mul]
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hsc : 0 ≤ Real.sin θ * Real.cos θ := mul_nonneg hs hc0
  have hc2 : Real.cos θ - 2 ≤ 0 := by linarith
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hsc hc2]

/-- **The pointwise estimate of the integrand of `gamDth_l2_bound`**:
on `Iθ`,
`sin(2θ)^{-γ}(D_θΓ)² ≤ 4α² sin(2θ)^{2α/3-γ}`.

It combines `DthGam_sq_le_GamSq` (from `(GammaAssumption2)`), `Gam_sq_le_sin_two`, and the
`rpow` addition `sin(2θ)^{-γ} sin(2θ)^{2α/3} = sin(2θ)^{2α/3-γ}` (the exponent is
nonzero because `γ = 1 + α/10 > 2α/3` for `α ≤ 1`). -/
theorem gamDth_integrand_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hΓ2 : GammaPointwiseBnd α) (θ : ℝ) (hθ : θ ∈ Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (DthGam α 0 θ) ^ 2
      ≤ 4 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Spaces.gam α) := by
  have hD := DthGam_sq_le_GamSq α hΓ2 θ hθ
  have hG := Gam_sq_le_sin_two α hα θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hw0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := Real.rpow_nonneg hs0 _
  have hne : 2 * α / 3 + (-(Spaces.gam α)) ≠ 0 := by
    have hg : 2 * α / 3 < Spaces.gam α := by
      rw [Spaces.gam]; nlinarith [hα1]
    linarith
  have hcomb : (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Real.sin (2 * θ)) ^ (2 * α / 3)
      = (Real.sin (2 * θ)) ^ (2 * α / 3 - Spaces.gam α) := by
    rw [show 2 * α / 3 - Spaces.gam α = 2 * α / 3 + (-(Spaces.gam α)) by ring,
      Real.rpow_add' hs0 hne]
    ring
  calc (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (DthGam α 0 θ) ^ 2
      ≤ (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (4 * α ^ 2 * (Spaces.Gam α θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hD hw0
    _ = 4 * α ^ 2 * ((Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Spaces.Gam α θ) ^ 2) := by
        ring
    _ ≤ 4 * α ^ 2 * ((Real.sin (2 * θ)) ^ (-(Spaces.gam α))
          * (Real.sin (2 * θ)) ^ (2 * α / 3)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG hw0) (by positivity)
    _ = 4 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Spaces.gam α) := by rw [hcomb]

theorem gamDth_l2_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hΓ2 : GammaPointwiseBnd α) :
    ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (DthGam α 0 θ) ^ 2
      ≤ 100 * α := by
  set q : ℝ := 1 - 17 * α / 30 with hqdef
  have hq0 : 0 < q := by simp only [hqdef]; linarith
  have hq1 : q < 1 := by simp only [hqdef]; linarith
  obtain ⟨hBint, hBval⟩ := integral_sin_two_neg_rpow_le q hq0 hq1
  have hgint : IntegrableOn (fun θ : ℝ => 4 * α ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      Spaces.Iθ := hBint.const_mul _
  have hfnn : 0 ≤ᵐ[volume.restrict Spaces.Iθ]
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (DthGam α 0 θ) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _) (sq_nonneg _)
  have hle : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (DthGam α 0 θ) ^ 2)
      ≤ᵐ[volume.restrict Spaces.Iθ]
      (fun θ : ℝ => 4 * α ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have h := gamDth_integrand_le α hα hα1 hΓ2 θ hθ
    have hexp : 2 * α / 3 - Spaces.gam α = -q := by
      simp only [hqdef, Spaces.gam]; ring
    rwa [hexp] at h
  have hmono := MeasureTheory.integral_mono_of_nonneg hfnn hgint hle
  have hval : ∫ θ in Spaces.Iθ, 4 * α ^ 2 * (Real.sin (2 * θ)) ^ (-q)
      = 4 * α ^ 2 * ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) := by
    rw [MeasureTheory.integral_const_mul]
  have hnum : 4 * α ^ 2 * (4 / (17 * α / 30)) = 480 * α / 17 := by
    field_simp
    ring
  calc ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (DthGam α 0 θ) ^ 2
      ≤ ∫ θ in Spaces.Iθ, 4 * α ^ 2 * (Real.sin (2 * θ)) ^ (-q) := hmono
    _ = 4 * α ^ 2 * ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) := hval
    _ ≤ 4 * α ^ 2 * (4 / (1 - q)) := mul_le_mul_of_nonneg_left hBval (by positivity)
    _ ≤ 100 * α := by
        have h1 : 1 - q = 17 * α / 30 := by simp only [hqdef]; ring
        rw [h1, hnum]
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 17)]
        nlinarith [hα]

end Work.Coercivity

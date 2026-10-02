import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Sobolev.dzbar_mul
import Submission.Work.MRMT.Sobolev.integral_dzbar_eq_zero_of_contDiff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.QC

open MeasureTheory Complex Function

theorem integral_mul_dzbar_eq_neg {f g : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hgs : HasCompactSupport g) :
    ∫ u, f u * Work.MRMT.dzbar g u ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ)
      = -∫ u, Work.MRMT.dzbar f u * g u ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  -- Integration by parts for the real Fréchet derivative, in a fixed direction `v`.
  have ibp : ∀ v : ℂ, ∫ u, f u * fderiv ℝ g u v = -∫ u, fderiv ℝ f u v * g u := by
    intro v
    have h1 : Integrable (fun u => fderiv ℝ f u v * g u) :=
      (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
        hg.continuous).integrable_of_hasCompactSupport hgs.mul_left
    have h2 : Integrable (fun u => f u * fderiv ℝ g u v) :=
      (hf.continuous.mul ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const))
        |>.integrable_of_hasCompactSupport ((hgs.fderiv_apply (𝕜 := ℝ) v).mul_left)
    have h3 : Integrable (fun u => f u * g u) :=
      (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgs.mul_left
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) h1 h2 h3
      (fun x _ => hf.differentiable_one x) (fun x _ => hg.differentiable_one x)
  have hI1 : Integrable (fun u => f u * fderiv ℝ g u 1) :=
    (hf.continuous.mul ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const))
      |>.integrable_of_hasCompactSupport ((hgs.fderiv_apply (𝕜 := ℝ) (1 : ℂ)).mul_left)
  have hII : Integrable (fun u => f u * fderiv ℝ g u Complex.I) :=
    (hf.continuous.mul ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const))
      |>.integrable_of_hasCompactSupport ((hgs.fderiv_apply (𝕜 := ℝ) Complex.I).mul_left)
  have hJ1 : Integrable (fun u => fderiv ℝ f u 1 * g u) :=
    (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
      hg.continuous).integrable_of_hasCompactSupport hgs.mul_left
  have hJI : Integrable (fun u => fderiv ℝ f u Complex.I * g u) :=
    (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
      hg.continuous).integrable_of_hasCompactSupport hgs.mul_left
  -- The left-hand side, in terms of the two directional derivatives of `g`.
  have hL : ∫ u, f u * Work.MRMT.dzbar g u =
      ((∫ u, f u * fderiv ℝ g u 1) + Complex.I * (∫ u, f u * fderiv ℝ g u Complex.I))
        * (2 : ℂ)⁻¹ := by
    calc ∫ u, f u * Work.MRMT.dzbar g u
        = ∫ u, (f u * fderiv ℝ g u 1 + Complex.I * (f u * fderiv ℝ g u Complex.I))
            * (2 : ℂ)⁻¹ := by
          apply integral_congr_ae
          filter_upwards with u
          simp only [Work.MRMT.dzbar, div_eq_mul_inv]
          ring
      _ = (∫ u, (f u * fderiv ℝ g u 1 + Complex.I * (f u * fderiv ℝ g u Complex.I)))
            * (2 : ℂ)⁻¹ := integral_mul_const _ _
      _ = ((∫ u, f u * fderiv ℝ g u 1) + Complex.I * (∫ u, f u * fderiv ℝ g u Complex.I))
            * (2 : ℂ)⁻¹ := by
          rw [integral_add hI1 (hII.const_mul Complex.I), integral_const_mul]
  -- The right-hand side, in terms of the two directional derivatives of `f`.
  have hR : ∫ u, Work.MRMT.dzbar f u * g u =
      ((∫ u, fderiv ℝ f u 1 * g u) + Complex.I * (∫ u, fderiv ℝ f u Complex.I * g u))
        * (2 : ℂ)⁻¹ := by
    calc ∫ u, Work.MRMT.dzbar f u * g u
        = ∫ u, (fderiv ℝ f u 1 * g u + Complex.I * (fderiv ℝ f u Complex.I * g u))
            * (2 : ℂ)⁻¹ := by
          apply integral_congr_ae
          filter_upwards with u
          simp only [Work.MRMT.dzbar, div_eq_mul_inv]
          ring
      _ = (∫ u, (fderiv ℝ f u 1 * g u + Complex.I * (fderiv ℝ f u Complex.I * g u)))
            * (2 : ℂ)⁻¹ := integral_mul_const _ _
      _ = ((∫ u, fderiv ℝ f u 1 * g u) + Complex.I * (∫ u, fderiv ℝ f u Complex.I * g u))
            * (2 : ℂ)⁻¹ := by
          rw [integral_add hJ1 (hJI.const_mul Complex.I), integral_const_mul]
  rw [hL, hR, ibp 1, ibp Complex.I]
  ring

end Work.MRMT.QC

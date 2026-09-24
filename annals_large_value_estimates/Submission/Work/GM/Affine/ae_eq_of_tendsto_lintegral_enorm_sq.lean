import Mathlib

open MeasureTheory Filter
open scoped ENNReal

namespace Work.GM.Affine

/-- If a sequence of complex-valued functions converges to `U` in the mean-square sense
(`∫⁻ ‖f n - U‖^2 → 0`) and converges pointwise a.e. to `g`, then `g = U` a.e.

The proof is Fatou's lemma: the a.e. limit of `‖f n - U‖ₑ ^ 2` is `‖g - U‖ₑ ^ 2`, so
`∫⁻ ‖g - U‖ₑ ^ 2 ≤ liminf ∫⁻ ‖f n - U‖ₑ ^ 2 = 0`, whence `‖g - U‖ₑ ^ 2 = 0` a.e. -/
theorem ae_eq_of_tendsto_lintegral_enorm_sq (f : ℕ → ℝ → ℂ) (g U : ℝ → ℂ)
    (hf : ∀ n, AEMeasurable (f n) MeasureTheory.volume)
    (hg : AEMeasurable g MeasureTheory.volume)
    (hU : AEMeasurable U MeasureTheory.volume)
    (hlim : Filter.Tendsto (fun n => ∫⁻ x, ‖f n x - U x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume) Filter.atTop (nhds 0))
    (hae : ∀ᵐ x ∂MeasureTheory.volume, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x))) :
    g =ᵐ[MeasureTheory.volume] U := by
  let F : ℕ → ℝ → ℝ≥0∞ := fun n x => ‖f n x - U x‖ₑ ^ (2 : ℝ)
  let L : ℝ → ℝ≥0∞ := fun x => ‖g x - U x‖ₑ ^ (2 : ℝ)
  have hFmeas : ∀ n, AEMeasurable (F n) volume := by
    intro n
    exact (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp_aemeasurable
      ((hf n).sub hU).enorm
  have hLmeas : AEMeasurable L volume :=
    (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp_aemeasurable
      (hg.sub hU).enorm
  have hae_conv : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (nhds (L x)) := by
    filter_upwards [hae] with x hx
    exact (ENNReal.continuous_rpow_const (y := (2:ℝ))).tendsto (‖g x - U x‖ₑ) |>.comp
            (continuous_enorm.tendsto (g x - U x) |>.comp (hx.sub_const (U x)))
  have hae_liminf : (fun x => liminf (fun n => F n x) atTop) =ᵐ[volume] L := by
    filter_upwards [hae_conv] with x hx
    exact hx.liminf_eq
  have hle : ∫⁻ x, L x ∂volume ≤ 0 := by
    calc ∫⁻ x, L x ∂volume
        = ∫⁻ x, liminf (fun n => F n x) atTop ∂volume := (lintegral_congr_ae hae_liminf).symm
      _ ≤ liminf (fun n => ∫⁻ x, F n x ∂volume) atTop := lintegral_liminf_le' hFmeas
      _ = 0 := by simpa only [F] using hlim.liminf_eq
  have hzero : ∫⁻ x, L x ∂volume = 0 := le_antisymm hle zero_le
  have hL0 : L =ᵐ[volume] 0 := (lintegral_eq_zero_iff' hLmeas).mp hzero
  filter_upwards [hL0] with x hx
  exact sub_eq_zero.mp
    (enorm_eq_zero.mp ((ENNReal.rpow_eq_zero_iff_of_pos (by norm_num : (0:ℝ) < 2)).mp hx))

end Work.GM.Affine

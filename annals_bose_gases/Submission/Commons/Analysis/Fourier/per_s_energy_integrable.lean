import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.RCLike.Inner
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Submission.Commons.Analysis.Fourier.per_s_energy
import Submission.Commons.Analysis.Fourier.position_reduce
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false

noncomputable section

open Real Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace SchwartzMap FourierTransform ComplexConjugate
open Complex hiding exp

namespace Commons.Analysis.Fourier

/-- The Fourier transform of an integrable function is continuous. -/
lemma continuous_fourier_of_integrable {f : V3 → ℂ} (hf : Integrable f) : Continuous (𝓕 f) := by
  rw [show 𝓕 f = VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ V3) f from rfl]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

/-- `outer_integrable` without the hypothesis that the Fourier transform is integrable:
only measurability of `𝓕 g` is needed, which follows from its continuity. -/
lemma outer_integrable' {g : V3 → ℂ} (hg : Integrable g) (s : ℝ) (hs : 0 < s) :
    Integrable (fun p : V3 × V3 =>
      g p.1 * (gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I) * 𝓕 g p.2))
      (volume.prod volume) := by
  let C : ℝ := ∫ y : V3, ‖g y‖
  have hC : 0 ≤ C := integral_nonneg (by intro y; exact norm_nonneg _)
  have hb : Integrable (fun p : V3 × V3 => C * (‖g p.1‖ * ‖gaussC s p.2‖))
      (volume.prod volume) := by
    have hprod : Integrable (fun p : V3 × V3 => ‖g p.1‖ * ‖gaussC s p.2‖) (volume.prod volume) :=
      (hg.norm.mul_prod (gaussC_integrable s hs).norm)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hprod.const_mul C
  refine hb.mono' ?_ ?_
  · have h1 : AEStronglyMeasurable (fun p : V3 × V3 => g p.1) (volume.prod volume) := hg.1.comp_fst
    have hcont : Continuous (fun p : V3 × V3 =>
        gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I)) := by
      dsimp [gaussC]
      fun_prop
    have h3 : AEStronglyMeasurable (fun p : V3 × V3 => 𝓕 g p.2) (volume.prod volume) :=
      (continuous_fourier_of_integrable hg).aestronglyMeasurable.comp_snd
    exact h1.mul (hcont.aestronglyMeasurable.mul h3)
  · filter_upwards with p
    calc
      ‖g p.1 * (gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I) * 𝓕 g p.2)‖
          ≤ ‖g p.1‖ * ‖gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I) * 𝓕 g p.2‖ := by
            exact norm_mul_le _ _
      _ ≤ ‖g p.1‖ * (‖gaussC s p.2‖ * ‖𝓕 g p.2‖) := by
            have h1 : ‖gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I) * 𝓕 g p.2‖
                ≤ ‖gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I)‖ * ‖𝓕 g p.2‖ := by
                  exact norm_mul_le _ _
            have h2 : ‖gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I)‖
                ≤ ‖gaussC s p.2‖ := by
                  calc
                    ‖gaussC s p.2 * cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I)‖
                        ≤ ‖gaussC s p.2‖ * ‖cexp ((↑(2 * Real.pi * ⟪p.2, p.1⟫) : ℂ) * Complex.I)‖ := by
                          exact norm_mul_le _ _
                    _ = ‖gaussC s p.2‖ := by
                          rw [cexp_norm_eq_one (2 * Real.pi * ⟪p.2, p.1⟫)]
                          ring
            calc
              ‖g p.1‖ * ‖gaussC s p.2 * cexp _ * 𝓕 g p.2‖
                  ≤ ‖g p.1‖ * (‖gaussC s p.2 * cexp _‖ * ‖𝓕 g p.2‖) := by
                    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
              _ ≤ ‖g p.1‖ * (‖gaussC s p.2‖ * ‖𝓕 g p.2‖) := by
                    gcongr
      _ ≤ ‖g p.1‖ * (‖gaussC s p.2‖ * C) := by
            gcongr
            exact ft_norm_le g p.2 hg
      _ = C * (‖g p.1‖ * ‖gaussC s p.2‖) := by
            ring

lemma position_eq_momentum' {g : V3 → ℂ} (hg : Integrable g) {s : ℝ} (hs : 0 < s) :
    (∫ x : V3, g x * (∫ y : V3, g y * heatC s (x - y)))
      = ∫ q : V3, (𝓕 g q) * (𝓕 g (-q)) * gaussC s q := by
  calc
    (∫ x : V3, g x * (∫ y : V3, g y * heatC s (x - y)))
        = ∫ x : V3, g x *
            (∫ q : V3, gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I) * (𝓕 g q)) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [inner_heat_eq hg hs x]
    _ = ∫ x : V3, ∫ q : V3,
            g x * (gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I) * (𝓕 g q)) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [← MeasureTheory.integral_const_mul (g x)]
    _ = ∫ q : V3, ∫ x : V3,
            g x * (gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I) * (𝓕 g q)) := by
          rw [integral_integral_swap (outer_integrable' hg s hs)]
    _ = ∫ q : V3, gaussC s q * (𝓕 g q) *
            (∫ x : V3, g x * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I)) := by
          apply integral_congr_ae
          filter_upwards with q
          calc
            (∫ x : V3,
                g x * (gaussC s q * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I) * (𝓕 g q)))
                = ∫ x : V3,
                    (gaussC s q * 𝓕 g q) * (g x * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I)) := by
                  apply integral_congr_ae
                  filter_upwards with x
                  ring
            _ = (gaussC s q * 𝓕 g q) *
                  (∫ x : V3, g x * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I)) := by
                  exact MeasureTheory.integral_const_mul (gaussC s q * 𝓕 g q)
                    (fun x : V3 => g x * cexp ((↑(2 * Real.pi * ⟪q, x⟫) : ℂ) * Complex.I))
    _ = ∫ q : V3, (𝓕 g q) * (𝓕 g (-q)) * gaussC s q := by
          apply integral_congr_ae
          filter_upwards with q
          rw [ft_neg_eq_integral_cexp]
          ring

theorem per_s_energy_complex' {g : V3 → ℂ} (hg : Integrable g) {s : ℝ} (hs : 0 < s) :
    (∫ q : V3, (𝓕 g q) * (𝓕 g (-q)) * gaussC s q)
      = (∫ x : V3, g x * (∫ y : V3, g y * heatC s (x - y))) :=
  (position_eq_momentum' hg hs).symm

lemma per_s_energy_of' {g : V3 → ℂ} (hg : ∀ x : V3, (g x).im = 0)
    (hgi : Integrable g) {s : ℝ} (hs : 0 < s) :
    (∫ q : V3, ‖𝓕 g q‖ ^ 2 * gaussR s q)
      = ∫ x : V3, (g x).re * (∫ y : V3, (g y).re * heatR s (x - y)) := by
  apply Complex.ofReal_inj.mp
  calc
    (↑(∫ q : V3, ‖𝓕 g q‖ ^ 2 * gaussR s q) : ℂ)
        = ∫ q : V3, (𝓕 g q) * (𝓕 g (-q)) * gaussC s q := momentum_real_cast hg s
    _ = ∫ x : V3, g x * (∫ y : V3, g y * heatC s (x - y)) := per_s_energy_complex' hgi hs
    _ = (↑(∫ x : V3, (g x).re * (∫ y : V3, (g y).re * heatR s (x - y))) : ℂ) :=
          (position_real_cast hg s).symm

/-- **Per-`s` energy identity for an arbitrary integrable real-valued `g` on `ℝ³`.**

For every `s > 0`,

`∫_q ‖ĝ(q)‖² exp(−π s ‖q‖²) dq = ∫_x g(x) (∫_y g(y) s^{−3/2} exp(−π‖x−y‖²/s) dy) dx`.

Unlike `per_s_energy`, no regularity or Fourier-integrability of `g` is assumed:
the only hypothesis is `g ∈ L¹`. -/
theorem per_s_energy_integrable {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : MeasureTheory.Integrable g) {s : ℝ} (hs : 0 < s) : (∫ q : EuclideanSpace ℝ (Fin 3), ‖FourierTransform.fourier (fun x => (g x : ℂ)) q‖ ^ 2 * Real.exp (-(Real.pi * s * ‖q‖ ^ 2))) = ∫ x : EuclideanSpace ℝ (Fin 3), g x * (∫ y : EuclideanSpace ℝ (Fin 3), g y * (s ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖x - y‖ ^ 2) / s))) := by
  have hgi : Integrable (fun x : V3 => (g x : ℂ)) := Integrable.ofReal hg
  have him : ∀ x : V3, ((fun x : V3 => (g x : ℂ)) x).im = 0 := fun x => Complex.ofReal_im (g x)
  have h := per_s_energy_of' him hgi hs
  simpa only [gaussR, heatR, Complex.ofReal_re] using h

end Commons.Analysis.Fourier

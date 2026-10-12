import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import ChallengeDeps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Radial (polar) integration on `EuclideanSpace ℝ (Fin 3)`

Layer-3 (scattering) infrastructure: integrals over `ℝ³` of functions that
depend only on the norm reduce to one-dimensional integrals over the radius.

Mathlib already contains the *general* polar-coordinate change of variables
for additive Haar measures on normed spaces
(`MeasureTheory.Measure.Constructions/HaarToSphere.lean`):

    MeasureTheory.integral_fun_norm_addHaar (μ : Measure E) (f : ℝ → F) :
      ∫ x, f ‖x‖ ∂μ
        = Module.finrank ℝ E • μ.real (ball 0 1) •
            ∫ y in Ioi 0, y ^ (Module.finrank ℝ E - 1) • f y

    MeasureTheory.integrable_fun_norm_addHaar (μ : Measure E) {f : ℝ → F} :
      Integrable (fun x => f ‖x‖) μ
        ↔ IntegrableOn (fun y => y ^ (Module.finrank ℝ E - 1) • f y) (Ioi 0) volume

    MeasureTheory.integrableOn_fun_norm_addHaar {r : ℝ} :
      IntegrableOn (fun x => f ‖x‖) (ball 0 r) μ
        ↔ IntegrableOn (fun y => y ^ (Module.finrank ℝ E - 1) • f y) (Ioo 0 r) volume

This module instantiates these on `E = EuclideanSpace ℝ (Fin 3)` with the
canonical `volume` (an additive Haar measure), dimension `3`, and unit ball
`measureReal = (4/3)π` (from `EuclideanSpace.volume_ball_fin_three`), to get
the classical `4π` surface factor:

    ∫ x : ℝ³, f ‖x‖ = 4π · ∫₀^∞ r² f r dr        (for integrable radial f)

and the corresponding integrability equivalences.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Submission.BoseGases

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

-- instance check: volume on ℝ³ is an additive Haar measure; the space is Borel.
example : (volume : Measure ℝ³).IsAddHaarMeasure := by infer_instance
example : BorelSpace ℝ³ := by infer_instance
example : Nontrivial ℝ³ := by infer_instance
example : FiniteDimensional ℝ ℝ³ := by infer_instance


lemma finrank_r3 : Module.finrank ℝ ℝ³ = 3 := by
  simp

lemma measureReal_unitBall_r3 :
    (volume : Measure ℝ³).real (Metric.ball (0 : ℝ³) 1) = 4 / 3 * π := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.toReal_mul]
  have hpow : (ENNReal.ofReal 1 ^ 3).toReal = 1 := by
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal h01]
    norm_num
  rw [hpow, one_mul]
  have hpi : (0 : ℝ) ≤ π * 4 / 3 := by positivity
  rw [ENNReal.toReal_ofReal hpi]
  ring

theorem integrable_radial_r3 {f : ℝ → ℝ} :
    Integrable (fun x : ℝ³ => f ‖x‖) volume ↔
      IntegrableOn (fun r : ℝ => r ^ 2 * f r) (Set.Ioi (0 : ℝ)) volume := by
  rw [integrable_fun_norm_addHaar (μ := (volume : Measure ℝ³)) (f := f)]
  rw [finrank_r3]
  simp only [smul_eq_mul]

theorem integrable_radial_ball_r3 {f : ℝ → ℝ} (R : ℝ) :
    IntegrableOn (fun x : ℝ³ => f ‖x‖) (Metric.ball (0 : ℝ³) R) volume ↔
      IntegrableOn (fun r : ℝ => r ^ 2 * f r) (Set.Ioo 0 R) volume := by
  rw [integrableOn_fun_norm_addHaar (μ := (volume : Measure ℝ³)) (f := f)]
  rw [finrank_r3]
  simp only [smul_eq_mul]

/-- Radial integral identity on ℝ³ without an integrability hypothesis:
`x ↦ g ‖x‖` is integrable iff the radius integral converges (Bochner integrals
of non-integrable functions are defined and this identity holds unconditionally). -/
lemma integral_fun_norm_r3 {g : ℝ → ℝ} :
    (∫ x : ℝ³, g ‖x‖) = 4 * π * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r) := by
  rw [integral_fun_norm_addHaar (μ := (volume : Measure ℝ³)) (f := g)]
  rw [finrank_r3, measureReal_unitBall_r3]
  simp only [nsmul_eq_mul, smul_eq_mul]
  norm_num
  ring

theorem integral_radial_r3 {f : ℝ → ℝ}
    (hint : IntegrableOn (fun r : ℝ => r ^ 2 * f r) (Set.Ioi (0 : ℝ)) volume) :
    (∫ x : ℝ³, f ‖x‖) = 4 * π * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * f r) := by
  exact integral_fun_norm_r3 (g := f)

theorem integral_radial_ball_r3 (R : ℝ) {f : ℝ → ℝ}
    (hint : IntegrableOn (fun r : ℝ => r ^ 2 * f r) (Set.Ioo 0 R) volume) :
    (∫ x in Metric.ball (0 : ℝ³) R, f ‖x‖) =
      4 * π * (∫ r in Set.Ioo 0 R, r ^ 2 * f r) := by
  let g : ℝ → ℝ := (Set.Iio R).indicator f
  have hLHS : (∫ x in Metric.ball (0 : ℝ³) R, f ‖x‖) = (∫ x : ℝ³, g ‖x‖) := by
    have hind : (fun x : ℝ³ => (Metric.ball (0 : ℝ³) R).indicator (fun y : ℝ³ => f ‖y‖) x) =
        (fun x : ℝ³ => g ‖x‖) := by
      funext x
      by_cases hx : ‖x‖ < R
      · have hmem : x ∈ Metric.ball (0 : ℝ³) R := by
          simpa [Metric.mem_ball, dist_zero_right] using hx
        simp [hmem, hx, g]
      · have hmem : x ∉ Metric.ball (0 : ℝ³) R := by
          simpa [Metric.mem_ball, dist_zero_right] using hx
        simp [hmem, hx, g]
    calc
      (∫ x in Metric.ball (0 : ℝ³) R, f ‖x‖)
          = ∫ x : ℝ³, (Metric.ball (0 : ℝ³) R).indicator (fun y : ℝ³ => f ‖y‖) x := by
            rw [integral_indicator (s := Metric.ball (0 : ℝ³) R)
              (f := fun y : ℝ³ => f ‖y‖) (μ := (volume : Measure ℝ³)) (by measurability)]
      _ = ∫ x : ℝ³, g ‖x‖ := by rw [hind]
  have hRHS : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r) =
      (∫ r in Set.Ioo 0 R, r ^ 2 * f r) := by
    have hfun : (fun r : ℝ => r ^ 2 * g r) =
        (Set.Iio R).indicator (fun r : ℝ => r ^ 2 * f r) := by
      funext r
      by_cases hr : r ∈ Set.Iio R
      · simp [g, hr]
      · simp [g, hr]
    calc
      (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r)
          = ∫ r in Set.Ioi (0 : ℝ), (Set.Iio R).indicator (fun r : ℝ => r ^ 2 * f r) r := by
            rw [hfun]
      _ = ∫ r in Set.Ioi (0 : ℝ) ∩ Set.Iio R, (fun r : ℝ => r ^ 2 * f r) r := by
            rw [setIntegral_indicator (s := Set.Ioi (0 : ℝ)) (t := Set.Iio R)
              (f := fun r : ℝ => r ^ 2 * f r) (μ := (volume : Measure ℝ)) (by measurability)]
      _ = ∫ r in Set.Ioo 0 R, r ^ 2 * f r := by
            rw [Set.Ioi_inter_Iio]
  calc
    (∫ x in Metric.ball (0 : ℝ³) R, f ‖x‖) = (∫ x : ℝ³, g ‖x‖) := hLHS
    _ = 4 * π * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r) := integral_fun_norm_r3 (g := g)
    _ = 4 * π * (∫ r in Set.Ioo 0 R, r ^ 2 * f r) := by rw [hRHS]

lemma volume_ball_r3 (r : ℝ) (hr : 0 ≤ r) :
    (volume : Measure ℝ³) (Metric.closedBall (0 : ℝ³) r) = ENNReal.ofReal ((4 / 3) * π * r ^ 3) := by
  rw [EuclideanSpace.volume_closedBall_fin_three]
  rw [← ENNReal.ofReal_pow hr 3]
  rw [← ENNReal.ofReal_mul (pow_nonneg hr 3)]
  congr 1
  ring

lemma volume_ball_open_r3 (r : ℝ) (hr : 0 ≤ r) :
    (volume : Measure ℝ³) (Metric.ball (0 : ℝ³) r) = ENNReal.ofReal ((4 / 3) * π * r ^ 3) := by
  rw [EuclideanSpace.volume_ball_fin_three]
  rw [← ENNReal.ofReal_pow hr 3]
  rw [← ENNReal.ofReal_mul (pow_nonneg hr 3)]
  congr 1
  ring

lemma volume_sphere_r3 (r : ℝ) :
    (volume : Measure ℝ³) (Metric.sphere (0 : ℝ³) r) = 0 := by
  exact Measure.addHaar_sphere (μ := (volume : Measure ℝ³)) (0 : ℝ³) r

lemma volume_annulus_r3 (R₁ R₂ : ℝ) (hR₁ : 0 ≤ R₁) (hR₂₁ : R₁ ≤ R₂) :
    (volume : Measure ℝ³) {x : ℝ³ | R₁ ≤ ‖x‖ ∧ ‖x‖ ≤ R₂} =
      ENNReal.ofReal ((4 / 3) * π * (R₂ ^ 3 - R₁ ^ 3)) := by
  have hR₂ : 0 ≤ R₂ := le_trans hR₁ hR₂₁
  have hset : {x : ℝ³ | R₁ ≤ ‖x‖ ∧ ‖x‖ ≤ R₂} =
      Metric.closedBall (0 : ℝ³) R₂ \ Metric.ball (0 : ℝ³) R₁ := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨h₁, h₂⟩
      have hx₁ : ¬ ‖x‖ < R₁ := by linarith
      refine ⟨?_, ?_⟩
      · simpa [Metric.mem_closedBall, dist_zero_right] using h₂
      · simpa [Metric.mem_ball, dist_zero_right, hx₁]
    · intro hx
      have hx₂ : ‖x‖ ≤ R₂ := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hx.1
      have hx₁ : R₁ ≤ ‖x‖ := by
        have hnot : ¬ ‖x‖ < R₁ := by
          simpa [Metric.mem_ball, dist_zero_right] using hx.2
        linarith
      exact ⟨hx₁, hx₂⟩
  have hsub : Metric.ball (0 : ℝ³) R₁ ⊆ Metric.closedBall (0 : ℝ³) R₂ := by
    intro x hx
    have hnorm : ‖x‖ < R₁ := by
      simpa [Metric.mem_ball, dist_zero_right] using hx
    have hle : ‖x‖ ≤ R₂ := le_trans (le_of_lt hnorm) hR₂₁
    simpa [Metric.mem_closedBall, dist_zero_right] using hle
  have hfin : (volume : Measure ℝ³) (Metric.ball (0 : ℝ³) R₁) ≠ ⊤ := by
    rw [volume_ball_open_r3 R₁ hR₁]
    exact ENNReal.ofReal_ne_top
  rw [hset]
  rw [measure_sdiff hsub (by measurability) hfin]
  rw [volume_ball_r3 R₂ hR₂, volume_ball_open_r3 R₁ hR₁]
  rw [← ENNReal.ofReal_sub ((4 / 3) * π * R₂ ^ 3) (by positivity)]
  congr 1
  ring

end Submission.BoseGases


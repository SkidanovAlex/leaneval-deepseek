import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.shifted_cut_maximal
import Submission.Work.BourgainPlan.Oscillation.oscZ_cut_of_maximal
import Submission.Work.BourgainPlan.Oscillation.Lacunary.oscZ_cut_of_maximal_bd

/-!
# The block oscillation of the *weighted* shifted sharp cuts

The family of operators

`A_i x = ∫₀¹ r(θ) · 1_{θ ≤ s ρ^{-i}} · (Σ_{n ∈ T} f n e(nθ)) · e(-2πi x θ) dθ`,  `i ∈ ℕ`,

is the family of sharp frequency cuts at the shifted lacunary radii `s ρ^{-i}`, *modulated by an
arbitrary measurable weight* `r` with sup-norm bound `‖r‖ ≤ cap`.  The statement proves Bourgain's
`ℓ²(ℤ)` block-oscillation bound

`oscZ A J k ≤ (C cap)² ∫⁻_n ‖f n‖² d#`

uniformly in the shift `s > 0`, in the weight `r`, in the block structure `k` and in the number of
blocks `J`, with a constant `C` depending on `ρ` only.

The weight is absorbed by observing that the family is the shifted-cut family applied to the single
density `g = r · (Σ_{n∈T} f n e(nθ))`, which is measurable and bounded by `cap · Σ_{n∈T} ‖f n‖`;
`oscZ_cut_of_maximal_bd` (the `L²`-density version of `oscZ_cut_of_maximal`) then bounds the block
oscillation by `4 C₀² ∫⁻_θ ‖g θ‖ₑ² dμ₀₁`, and the pointwise bound `‖g θ‖ ≤ cap ‖P θ‖` together with
Parseval (`trig_lintegral`/`f_lintegral`) turns that into `4 C₀² cap² ∫⁻_n ‖f n‖² d#`.
-/

namespace Work.BourgainPlan.Oscillation.Lacunary

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

theorem oscZ_cut_weighted (ρ : ℝ) (hρ : 1 < ρ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s : ℝ), 0 < s → ∀ (r : ℝ → ℂ), Measurable r → ∀ (cap : ℝ), 0 ≤ cap →
      (∀ θ, ‖r θ‖ ≤ cap) →
      ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
      ∀ (f : ℤ → ℂ) (T : Finset ℤ), (∀ n, n ∉ T → f n = 0) →
        Work.BourgainPlan.Oscillation.oscZ (fun i x =>
            ∫ θ in (0:ℝ)..1,
              (r θ * (if θ ≤ s * ρ ^ (-(i:ℤ)) then (1:ℂ) else 0)) *
              (∑ n ∈ T, f n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ))) *
              Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) J k
          ≤ ENNReal.ofReal ((C * cap) ^ 2) *
              ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨C₀, hC₀pos, hmax⟩ := shifted_cut_maximal ρ hρ
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro s hs r hr cap hcap hrbd J k hk f T hf
  set P : ℝ → ℂ := fun θ => ∑ n ∈ T, f n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ)) with hP
  have hPmeas : Measurable P := by
    rw [hP]
    exact Finset.measurable_sum _ (fun n _ =>
      measurable_const.mul (Complex.measurable_exp.comp (by fun_prop)))
  have hPbd : ∀ θ, ‖P θ‖ ≤ ∑ n ∈ T, ‖f n‖ := by
    intro θ
    rw [hP]
    simpa only [Lacunary.trigP] using norm_trigP_le T f θ
  set g : ℝ → ℂ := fun θ => r θ * P θ with hg
  have hgmeas : Measurable g := by rw [hg]; exact hr.mul hPmeas
  have hK0 : 0 ≤ ∑ n ∈ T, ‖f n‖ := Finset.sum_nonneg (fun n _ => norm_nonneg _)
  have hgbd : ∀ θ, ‖g θ‖ ≤ cap * ∑ n ∈ T, ‖f n‖ := by
    intro θ
    rw [hg, norm_mul]
    exact mul_le_mul (hrbd θ) (hPbd θ) (norm_nonneg _) hcap
  have hfam : (fun (i : ℕ) (x : ℤ) => ∫ θ in (0:ℝ)..1,
          (r θ * (if θ ≤ s * ρ ^ (-(i:ℤ)) then (1:ℂ) else 0)) *
          (∑ n ∈ T, f n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ))) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))))
      = (fun (i : ℕ) (x : ℤ) => ∫ θ, (if θ ≤ s * ρ ^ (-(i:ℤ)) then (1:ℂ) else 0) * g θ
            * Echar x θ ∂mu01) := by
    funext i x
    rw [intervalIntegral_eq_mu01]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [Echar, hg]
    ring
  rw [hfam]
  have hgen := oscZ_cut_of_maximal_bd ρ hρ C₀ hC₀pos hmax s hs g hgmeas
    (cap * ∑ n ∈ T, ‖f n‖) (mul_nonneg hcap hK0) hgbd J k hk
  have hgP : ∫⁻ θ, ‖g θ‖ₑ ^ (2:ℝ) ∂mu01
      ≤ ENNReal.ofReal (cap^2) * ∫⁻ θ, ‖P θ‖ₑ ^ (2:ℝ) ∂mu01 := by
    calc ∫⁻ θ, ‖g θ‖ₑ ^ (2:ℝ) ∂mu01
        ≤ ∫⁻ θ, ENNReal.ofReal (cap^2) * ‖P θ‖ₑ ^ (2:ℝ) ∂mu01 := by
          refine lintegral_mono (fun θ => ?_)
          rw [rpow_two_ofReal, rpow_two_ofReal, ← ENNReal.ofReal_mul (sq_nonneg cap)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hg, norm_mul, mul_pow]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hrbd θ) 2)
            (sq_nonneg _)
      _ = ENNReal.ofReal (cap^2) * ∫⁻ θ, ‖P θ‖ₑ ^ (2:ℝ) ∂mu01 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hPl : ∫⁻ θ, ‖P θ‖ₑ ^ (2:ℝ) ∂mu01 = ENNReal.ofReal (∑ n ∈ T, ‖f n‖ ^ 2) := by
    rw [hP]
    simpa only [Lacunary.trigP] using trig_lintegral T f
  have hfl : ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count
      = ENNReal.ofReal (∑ n ∈ T, ‖f n‖ ^ 2) := f_lintegral T f hf
  have hconst : ENNReal.ofReal (4 * C₀ ^ 2) * ENNReal.ofReal (cap ^ 2)
      = ENNReal.ofReal ((2*C₀*cap)^2) := by
    rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4*C₀^2)]
    congr 1
    ring
  calc oscZ (fun i x => ∫ θ, (if θ ≤ s * ρ ^ (-(i:ℤ)) then (1:ℂ) else 0) * g θ
          * Echar x θ ∂mu01) J k
      ≤ ENNReal.ofReal (4 * C₀ ^ 2) * ∫⁻ θ, ‖g θ‖ₑ ^ (2:ℝ) ∂mu01 := hgen
    _ ≤ ENNReal.ofReal (4 * C₀ ^ 2) * (ENNReal.ofReal (cap^2)
          * ∫⁻ θ, ‖P θ‖ₑ ^ (2:ℝ) ∂mu01) :=
        mul_le_mul_of_nonneg_left hgP (by positivity)
    _ = ENNReal.ofReal ((2*C₀*cap)^2) * ∫⁻ θ, ‖P θ‖ₑ ^ (2:ℝ) ∂mu01 := by
        rw [← mul_assoc, hconst]
    _ = ENNReal.ofReal ((2*C₀*cap)^2)
          * ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
        rw [hPl, ← hfl]

end

end Work.BourgainPlan.Oscillation.Lacunary

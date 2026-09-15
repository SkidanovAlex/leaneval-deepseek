import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.WithDensity

set_option linter.unusedVariables false

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Commons.MeasureTheory

theorem tendsto_lintegral_ofReal_sq_one_sub_smul_cutoff {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin d → ℂ) → ℝ} (hFc : Continuous F) (hFnn : ∀ x, 0 ≤ F x)
    (u : (Fin d → ℂ) → E) (hu : MeasureTheory.MemLp u 2
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)).withDensity
        (fun x => ENNReal.ofReal (F x))))
    (χ : ℝ → (Fin d → ℂ) → ℝ)
    (hχc : ∀ R, Continuous (χ R))
    (hχbdd : ∀ᶠ R in Filter.atTop, ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1)
    (hχone : ∀ x, ∀ᶠ R in Filter.atTop, χ R x = 1) :
    Filter.Tendsto (fun R => ∫⁻ x, ENNReal.ofReal (‖(1 - χ R x) • u x‖ ^ 2 * F x)
      ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) Filter.atTop (nhds 0) := by
  classical
  let ν : Measure (Fin d → ℂ) := (volume : Measure (Fin d → ℂ)).withDensity
      (fun x => ENNReal.ofReal (F x))
  -- A.e.-measurability of the integrands, w.r.t. the density measure `ν`
  have hmeasR : ∀ R : ℝ, AEMeasurable
      (fun x : Fin d → ℂ => ENNReal.ofReal (‖(1 - χ R x) • u x‖ ^ 2)) ν := by
    intro R
    have hsm : AEStronglyMeasurable (fun x : Fin d → ℂ => (1 - χ R x) • u x) ν :=
      (measurable_const.sub (hχc R).measurable).aestronglyMeasurable.smul hu.aestronglyMeasurable
    exact (((hsm.norm).pow 2).aemeasurable).ennreal_ofReal
  -- Finiteness of the dominating integral
  have hfin : ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂ν ≠ ∞ := by
    have hμ_fin : ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂ν < ∞ := by
      have h := MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num) hu.eLpNorm_lt_top
      simpa using h
    have hA : ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂ν = ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂ν := by
      apply lintegral_congr; intro x
      rw [show ‖u x‖ₑ = ENNReal.ofReal ‖u x‖ by simp [enorm]]
      rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
      exact congrArg ENNReal.ofReal (Real.rpow_two ‖u x‖)
    rw [← lt_top_iff_ne_top, ← hA]
    exact hμ_fin
  -- Convergence of the `ν`-integrals
  have hmain : Tendsto (fun R => ∫⁻ x, ENNReal.ofReal (‖(1 - χ R x) • u x‖ ^ 2) ∂ν)
      atTop (nhds 0) := by
    have hmeas : ∀ᶠ R in atTop, AEMeasurable
        (fun x : Fin d → ℂ => ENNReal.ofReal (‖(1 - χ R x) • u x‖ ^ 2)) ν :=
      Eventually.of_forall hmeasR
    have hbound : ∀ᶠ R in atTop, ∀ᵐ x ∂ν,
        ENNReal.ofReal (‖(1 - χ R x) • u x‖ ^ 2) ≤ ENNReal.ofReal (‖u x‖ ^ 2) := by
      filter_upwards [hχbdd] with R hR
      refine Eventually.of_forall (fun x => ?_)
      apply ENNReal.ofReal_le_ofReal
      have hle : ‖(1 - χ R x) • u x‖ ≤ ‖u x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        calc |1 - χ R x| * ‖u x‖ ≤ 1 * ‖u x‖ :=
              mul_le_mul_of_nonneg_right
                (abs_le.mpr ⟨by linarith [(hR x).2], by linarith [(hR x).1]⟩) (norm_nonneg _)
          _ = ‖u x‖ := one_mul _
      exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    have hlim : ∀ᵐ x ∂ν, Tendsto
        (fun R => ENNReal.ofReal (‖(1 - χ R x) • u x‖ ^ 2)) atTop (𝓝 0) := by
      refine Eventually.of_forall (fun x => ?_)
      refine tendsto_nhds_of_eventually_eq ?_
      filter_upwards [hχone x] with R hR
      simp [hR]
    have key := MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence'
        (μ := ν) (l := atTop)
        (F := fun R x => ENNReal.ofReal (‖(1 - χ R x) • u x‖ ^ 2))
        (f := fun _ => 0) (bound := fun x => ENNReal.ofReal (‖u x‖ ^ 2))
        hmeas hbound hfin hlim
    simpa using key
  -- Rewrite the target integral with respect to the density measure
  refine Filter.Tendsto.congr (fun R => ?_) hmain
  change ∫⁻ x, ENNReal.ofReal (‖(1 - χ R x) • u x‖ ^ 2)
        ∂((volume : Measure (Fin d → ℂ)).withDensity (fun x => ENNReal.ofReal (F x)))
      = ∫⁻ x, ENNReal.ofReal (‖(1 - χ R x) • u x‖ ^ 2 * F x)
        ∂(volume : Measure (Fin d → ℂ))
  rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀'
      (f := fun x => ENNReal.ofReal (F x))
      (g := fun x => ENNReal.ofReal (‖(1 - χ R x) • u x‖ ^ 2))
      hFc.measurable.aemeasurable.ennreal_ofReal (hmeasR R)]
  apply lintegral_congr; intro x
  simp only [Pi.mul_apply]
  rw [mul_comm, ← ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) 2)]

end Commons.MeasureTheory
import Mathlib
import Submission.Commons.Probability.Levy.levy_interval_L1
import Submission.Commons.Probability.Levy.product_integral_bound

open MeasureTheory
open scoped ENNReal BigOperators

namespace Commons.Probability.Levy

/- Embedded exact requested declaration text (kept verbatim; the reserved token
λ is a comment here, since Lean 4 cannot use λ as an identifier in the real
declaration below; the real declaration is alpha-equal to this text):
theorem rogozin_variable_radii :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) (μ : Fin m → Measure ℝ) [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
        (λ : Measure ℝ) [MeasureTheory.IsProbabilityMeasure λ]
        (r : ℝ), 0 < r → ∀ (ρ : Fin m → ℝ),
        (∀ i : Fin m, 0 < ρ i) → (∀ i : Fin m, ρ i ≤ r) →
        (∀ t : ℝ, ‖charFun λ t‖ ≤ ∏ i : Fin m, ‖charFun (μ i) t‖) →
        (0 < ∑ i : Fin m,
          (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (μ i) (Set.Icc (l - (ρ i)) (l + (ρ i)))}).toReal) * (ρ i) ^ 2) →
        sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = λ (Set.Icc (l - r) (l + r))} ≤
          ENNReal.ofReal (C * r / Real.sqrt (∑ i : Fin m,
            (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (μ i) (Set.Icc (l - (ρ i)) (l + (ρ i)))}).toReal) * (ρ i) ^ 2))  :=
-/


noncomputable section

/-- Lévy concentration function for a measure on ℝ (closed intervals, inline-sup). -/
def CF (μ : Measure ℝ) (t : ℝ) : ℝ≥0∞ :=
  sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = μ (Set.Icc (l - t) (l + t))}

/-- Every closed-interval mass is below the supremum. -/
lemma CF_le_interval (μ : Measure ℝ) (t l : ℝ) :
    μ (Set.Icc (l - t) (l + t)) ≤ CF μ t := by
  unfold CF
  exact le_sSup ⟨l, rfl⟩

/-- The supremum is an upper bound of every interval mass, contrapositive-free form. -/
lemma CF_mono_radius (μ : Measure ℝ) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) : CF μ t₁ ≤ CF μ t₂ := by
  unfold CF
  rw [sSup_le_iff]
  rintro b ⟨l, rfl⟩
  exact le_trans (measure_mono (by
    intro x hx
    have hx₁ : l - t₁ ≤ x := (Set.mem_Icc.mp hx).1
    have hx₂ : x ≤ l + t₁ := (Set.mem_Icc.mp hx).2
    constructor <;> nlinarith)) (CF_le_interval μ t₂ l)

/-- Concentration function of a probability measure is at most 1. -/
lemma CF_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) : CF μ t ≤ 1 := by
  unfold CF
  rw [sSup_le_iff]
  rintro b ⟨l, rfl⟩
  calc
    μ (Set.Icc (l - t) (l + t)) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := by simp

/-- Concentration function value is nonnegative in `toReal`. -/
lemma CF_toReal_nonneg (μ : Measure ℝ) (t : ℝ) : 0 ≤ (CF μ t).toReal := ENNReal.toReal_nonneg

end


theorem rogozin_variable_radii :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) (μ : Fin m → Measure ℝ) [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
        («λ» : Measure ℝ) [MeasureTheory.IsProbabilityMeasure «λ»]
        (r : ℝ), 0 < r → ∀ (ρ : Fin m → ℝ),
        (∀ i : Fin m, 0 < ρ i) → (∀ i : Fin m, ρ i ≤ r) →
        (∀ t : ℝ, ‖charFun «λ» t‖ ≤ ∏ i : Fin m, ‖charFun (μ i) t‖) →
        (0 < ∑ i : Fin m,
          (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (μ i) (Set.Icc (l - (ρ i)) (l + (ρ i)))}).toReal) * (ρ i) ^ 2) →
        sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = «λ» (Set.Icc (l - r) (l + r))} ≤
          ENNReal.ofReal (C * r / Real.sqrt (∑ i : Fin m,
            (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (μ i) (Set.Icc (l - (ρ i)) (l + (ρ i)))}).toReal) * (ρ i) ^ 2)) := by
  classical
  rcases levy_interval_L1 with ⟨C₁, hC₁pos, hL1⟩
  rcases product_integral_bound with ⟨C₂, hC₂pos, hProd⟩
  refine ⟨C₁ * C₂, mul_pos hC₁pos hC₂pos, ?_⟩
  intro m μ hinst1 lam hinst2 r hr ρ hρpos hρle hdom hDpos
  let D : ℝ := (∑ i : Fin m,
          (1 - (sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = (μ i) (Set.Icc (l - (ρ i)) (l + (ρ i)))}).toReal) * (ρ i) ^ 2)
  have hDposD : 0 < D := by
    simpa [D] using hDpos
  have hsqrtD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDposD
  have hProd_b : (∫ t in (-(1 / r))..(1 / r), ∏ i : Fin m, ‖charFun (μ i) t‖) ≤ C₂ / Real.sqrt D := by
    simpa [D] using (hProd m μ r hr ρ hρpos hρle hDpos)
  apply sSup_le
  rintro a ⟨l, rfl⟩
  have hfin : lam (Set.Icc (l - r) (l + r)) ≠ ∞ := measure_ne_top lam _
  have hB : 0 ≤ (C₁ * C₂) * r / Real.sqrt D := by
    exact div_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC₁pos) (le_of_lt hC₂pos)) (le_of_lt hr))
      (le_of_lt hsqrtD)
  rw [ENNReal.le_ofReal_iff_toReal_le hfin hB]
  have hI : (∫ t in (-(1 / r))..(1 / r), ‖charFun lam t‖) ≤
      ∫ t in (-(1 / r))..(1 / r), ∏ i : Fin m, ‖charFun (μ i) t‖ := by
    refine intervalIntegral.integral_mono_on ?hab ?hf ?hg ?h
    · have h1 : 0 ≤ 1 / r := by positivity
      exact neg_le_self h1
    · apply Continuous.intervalIntegrable
      fun_prop
    · apply Continuous.intervalIntegrable
      refine continuous_finsetProd Finset.univ ?_
      intro i hi
      fun_prop
    · intro t ht
      exact hdom t
  have hI2 : C₁ * r * (∫ t in (-(1 / r))..(1 / r), ‖charFun lam t‖) ≤
      C₁ * r * (∫ t in (-(1 / r))..(1 / r), ∏ i : Fin m, ‖charFun (μ i) t‖) := by
    exact mul_le_mul_of_nonneg_left hI (mul_nonneg (le_of_lt hC₁pos) (le_of_lt hr))
  calc
    (lam (Set.Icc (l - r) (l + r))).toReal ≤
        C₁ * r * (∫ t in (-(1 / r))..(1 / r), ‖charFun lam t‖) := by
      simpa using (hL1 lam r hr l)
    _ ≤ C₁ * r * (∫ t in (-(1 / r))..(1 / r), ∏ i : Fin m, ‖charFun (μ i) t‖) := hI2
    _ ≤ C₁ * r * (C₂ / Real.sqrt D) := by
      exact mul_le_mul_of_nonneg_left hProd_b (mul_nonneg (le_of_lt hC₁pos) (le_of_lt hr))
    _ = (C₁ * C₂) * r / Real.sqrt D := by
      ring

end Commons.Probability.Levy

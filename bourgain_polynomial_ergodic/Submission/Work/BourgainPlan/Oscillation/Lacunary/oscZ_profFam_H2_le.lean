import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.oscZ_lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.Lacunary.dilProfDefs
import Submission.Work.BourgainPlan.Oscillation.Lacunary.sqfn_no_per

namespace Work.BourgainPlan.Oscillation.Lacunary

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

set_option linter.unusedVariables false

/-- A single term of a square-summable lacunary dilation family is bounded by `A`. -/
private lemma norm_le_of_summable_sq_Ioc (ρ : ℝ) (A : ℝ) (hA : 0 ≤ A) (H₂ : ℝ → ℂ)
    (hH₂sum : ∀ θ ∈ Set.Ioc (0:ℝ) 1,
      Summable (fun i : ℕ => ‖H₂ ((lacScale ρ i : ℝ) * θ)‖ ^ 2) ∧
      ∑' i : ℕ, ‖H₂ ((lacScale ρ i : ℝ) * θ)‖ ^ 2 ≤ A ^ 2)
    {θ : ℝ} (hθ : θ ∈ Set.Ioc (0:ℝ) 1) (i : ℕ) :
    ‖H₂ ((lacScale ρ i : ℝ) * θ)‖ ≤ A := by
  have hsum := (hH₂sum θ hθ).1
  have hle : ‖H₂ ((lacScale ρ i : ℝ) * θ)‖ ^ 2
      ≤ ∑' j : ℕ, ‖H₂ ((lacScale ρ j : ℝ) * θ)‖ ^ 2 :=
    hsum.le_tsum i (fun j _ => sq_nonneg _)
  have h2 : ‖H₂ ((lacScale ρ i : ℝ) * θ)‖ ^ 2 ≤ A ^ 2 := le_trans hle (hH₂sum θ hθ).2
  calc ‖H₂ ((lacScale ρ i : ℝ) * θ)‖
      = Real.sqrt (‖H₂ ((lacScale ρ i : ℝ) * θ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (A ^ 2) := Real.sqrt_le_sqrt h2
    _ = A := Real.sqrt_sq hA

theorem oscZ_profFam_H2_le (ρ : ℝ) (hρ : 1 < ρ) (J : ℕ) (k : ℕ → ℕ) (hk : StrictMono k)
    (r : ℝ → ℂ) (hr : Measurable r) (cap A : ℝ) (hcap : 0 ≤ cap) (hA : 0 ≤ A)
    (hrb : ∀ θ, ‖r θ‖ ≤ cap) (H₂ : ℝ → ℂ) (hH₂m : Measurable H₂)
    (hH₂sum : ∀ θ ∈ Set.Ioc (0:ℝ) 1,
      Summable (fun i : ℕ => ‖H₂ ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)‖ ^ 2) ∧
      ∑' i : ℕ, ‖H₂ ((Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) * θ)‖ ^ 2 ≤ A ^ 2)
    (f : ℤ → ℂ) (T : Finset ℤ) (hf : ∀ n, n ∉ T → f n = 0) :
    Work.BourgainPlan.Oscillation.oscZ
        (Work.BourgainPlan.Oscillation.Lacunary.profFam H₂ r f T ρ) J k
      ≤ ENNReal.ofReal (8 * (cap * A) ^ 2) *
          ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  classical
  -- The multiplier of the second profile part, switched off outside `(0,1]`.
  let m : ℕ → ℝ → ℂ :=
    fun i θ => if θ ∈ Set.Ioc (0:ℝ) 1 then r θ * H₂ ((lacScale ρ i : ℝ) * θ) else 0
  -- The corresponding Fourier family.
  let B : ℕ → ℤ → ℂ := fun i x =>
    ∫ θ in (0:ℝ)..1, m i θ *
      (∑ n ∈ T, f n * Complex.exp (2 * Real.pi * Complex.I * ((n : ℤ) : ℂ) * (θ : ℂ))) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))
  -- `profFam` agrees with `B` pointwise.
  have hprof : ∀ i x, profFam H₂ r f T ρ i x = B i x := by
    intro i x
    rw [profFam_def]
    dsimp only [B, m, trigP, Echar]
    rw [intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num),
        intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
    refine setIntegral_congr_fun measurableSet_Ioc (fun θ hθ => ?_)
    rw [if_pos hθ]
  -- Measurability, boundedness and square-summability of the multiplier family.
  have hm : ∀ j, Measurable (m j) := by
    intro j
    dsimp only [m]
    exact Measurable.ite measurableSet_Ioc (hr.mul (hH₂m.comp (by fun_prop))) measurable_const
  have hbound : ∀ j θ, ‖m j θ‖ ≤ cap * A := by
    intro j θ
    dsimp only [m]
    by_cases hθ : θ ∈ Set.Ioc (0:ℝ) 1
    · rw [if_pos hθ, norm_mul]
      exact mul_le_mul (hrb θ) (norm_le_of_summable_sq_Ioc ρ A hA H₂ hH₂sum hθ j)
        (norm_nonneg _) hcap
    · rw [if_neg hθ, norm_zero]
      exact mul_nonneg hcap hA
  have hb : ∀ j, ∃ C : ℝ, ∀ θ, ‖m j θ‖ ≤ C := fun j => ⟨cap * A, hbound j⟩
  have hsum : ∀ θ, Summable (fun j : ℕ => ‖m j θ‖ ^ 2) ∧
      ∑' j : ℕ, ‖m j θ‖ ^ 2 ≤ (cap * A) ^ 2 := by
    intro θ
    by_cases hθ : θ ∈ Set.Ioc (0:ℝ) 1
    · have hH := hH₂sum θ hθ
      have hcongr : (fun j : ℕ => ‖m j θ‖ ^ 2)
          = fun j : ℕ => ‖r θ‖ ^ 2 * ‖H₂ ((lacScale ρ j : ℝ) * θ)‖ ^ 2 := by
        funext j
        dsimp only [m]
        rw [if_pos hθ, norm_mul, mul_pow]
      rw [hcongr]
      refine ⟨hH.1.mul_left (‖r θ‖ ^ 2), ?_⟩
      rw [tsum_mul_left]
      have h1 : ‖r θ‖ ^ 2 ≤ cap ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hcap]
        exact hrb θ
      calc ‖r θ‖ ^ 2 * ∑' j : ℕ, ‖H₂ ((lacScale ρ j : ℝ) * θ)‖ ^ 2
          ≤ cap ^ 2 * A ^ 2 :=
            mul_le_mul h1 hH.2 (tsum_nonneg (fun j => sq_nonneg _)) (sq_nonneg cap)
        _ = (cap * A) ^ 2 := by rw [mul_pow]
    · have hz : ∀ j : ℕ, ‖m j θ‖ ^ 2 = 0 := by
        intro j
        dsimp only [m]
        rw [if_neg hθ, norm_zero]
        norm_num
      have hfun : (fun j : ℕ => ‖m j θ‖ ^ 2) = fun _ : ℕ => (0:ℝ) := funext hz
      rw [hfun, tsum_zero]
      exact ⟨summable_zero, sq_nonneg _⟩
  -- The square function bound of `sqfn_no_per`.
  have hmeasB : ∀ i : ℕ, AEMeasurable (fun x : ℤ => ‖B i x‖ₑ ^ (2:ℝ)) Measure.count :=
    fun i => (measurable_of_countable _).aemeasurable
  have hsqfn : (∑' i : ℕ, ∫⁻ x : ℤ, ‖B i x‖ₑ ^ (2:ℝ) ∂Measure.count)
      ≤ ENNReal.ofReal ((cap * A) ^ 2) *
          ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂Measure.count := by
    rw [← lintegral_tsum hmeasB]
    dsimp only [B]
    exact sqfn_no_per m (cap * A) hm hb hsum f T
  have hconst : (8 : ℝ≥0∞) * ENNReal.ofReal ((cap * A) ^ 2)
      = ENNReal.ofReal (8 * (cap * A) ^ 2) := by
    rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8)]
  calc oscZ (profFam H₂ r f T ρ) J k
      ≤ 8 * ∑' i : ℕ, ∫⁻ x : ℤ, ‖B i x‖ₑ ^ (2:ℝ) ∂Measure.count :=
        oscZ_le_eight_tsum_of_enorm_le (profFam H₂ r f T ρ) B
          (fun i x => by rw [hprof i x]) J k hk
    _ ≤ 8 * (ENNReal.ofReal ((cap * A) ^ 2) *
            ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂Measure.count) :=
          mul_le_mul_of_nonneg_left hsqfn (by norm_num)
    _ = ENNReal.ofReal (8 * (cap * A) ^ 2) *
            ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂Measure.count := by
          rw [← mul_assoc, hconst]

end

end Work.BourgainPlan.Oscillation.Lacunary

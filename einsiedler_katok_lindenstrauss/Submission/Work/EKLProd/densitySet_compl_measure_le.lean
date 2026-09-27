import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLComp.Hopf_inequality

open MeasureTheory

namespace Work.EKLProd

open Work.EKLContract

/-- Iterating the left translation `y ↦ a • y` gives left multiplication by the power `a ^ j`. -/
theorem iter_smul_eq (a : SL3) (j : ℕ) (x : X3) :
    (fun y : X3 => a • y)^[j] x = a^j • x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    show a • (a^j • x) = a^(j+1) • x
    rw [pow_succ', mul_smul]

theorem densitySet_compl_measure_le {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {a : Work.EKLContract.SL3}
    (ha : MeasureTheory.MeasurePreserving (fun y : Work.EKLContract.X3 => a • y) μ μ)
    {K : Set Work.EKLContract.X3} (hK : MeasurableSet K) :
    μ {x : Work.EKLContract.X3 | ∀ n : ℕ, 0 < n →
        (∑ j ∈ Finset.range n, (Kᶜ.indicator (fun _ => (1 : ℝ))) (a^j • x)) ≤ (1/3) * n}ᶜ
      ≤ ENNReal.ofReal (3 * (μ Kᶜ).toReal) := by
  classical
  -- Rewrite the Birkhoff sums of `T = (a • ·)` in terms of the powers `a ^ j`.
  have hbsum : ∀ (n : ℕ) (x : X3),
      birkhoffSum (fun y : X3 => a • y) (Kᶜ.indicator (fun _ => (1 : ℝ))) n x
        = ∑ j ∈ Finset.range n, (Kᶜ.indicator (fun _ => (1 : ℝ))) (a^j • x) := by
    intro n x
    simp only [birkhoffSum]
    exact Finset.sum_congr rfl (fun j _ => by rw [iter_smul_eq a j x])
  have hgint : MeasureTheory.Integrable (Kᶜ.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hK.compl
  have hgn : ∀ x, 0 ≤ (Kᶜ.indicator (fun _ => (1 : ℝ))) x :=
    fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  -- Hopf's weak `(1,1)` maximal inequality with `α = 1/3`.
  have hmain := Work.EKLComp.hopfIneq_maximal_weak_type μ (fun y : X3 => a • y) ha
      (Kᶜ.indicator (fun _ => (1 : ℝ))) hgint hgn (1/3) (by norm_num)
  -- The Hopf maximal set is the complement of the "density" set of the statement.
  have hset : {x : X3 | ∃ n : ℕ, 0 < n ∧
        (1/3) * n < birkhoffSum (fun y : X3 => a • y) (Kᶜ.indicator (fun _ => (1 : ℝ))) n x}
      = {x : X3 | ∀ n : ℕ, 0 < n →
        (∑ j ∈ Finset.range n, (Kᶜ.indicator (fun _ => (1 : ℝ))) (a^j • x)) ≤ (1/3) * n}ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_forall, not_le]
    constructor
    · rintro ⟨n, hn, hlt⟩
      exact ⟨n, hn, by rwa [hbsum n x] at hlt⟩
    · rintro ⟨n, hn, hlt⟩
      exact ⟨n, hn, by rwa [← hbsum n x] at hlt⟩
  -- The integral of the indicator is the measure of `Kᶜ`.
  have hInt : ∫ x, (Kᶜ.indicator (fun _ => (1 : ℝ))) x ∂μ = (μ Kᶜ).toReal := by
    rw [← MeasureTheory.measureReal_def]
    exact integral_indicator_one hK.compl
  rw [hset, hInt] at hmain
  have h31 : ((1 : ℝ) / 3) = 3⁻¹ := by rw [one_div]
  have harith : (μ Kᶜ).toReal / (1/3) = 3 * (μ Kᶜ).toReal := by
    rw [h31, div_inv_eq_mul]
    exact mul_comm _ _
  rwa [harith] at hmain

end Work.EKLProd

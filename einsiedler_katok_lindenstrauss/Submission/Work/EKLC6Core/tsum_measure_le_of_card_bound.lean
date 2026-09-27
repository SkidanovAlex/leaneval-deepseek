import Mathlib

namespace Work.EKLC6Core

open Classical in
theorem tsum_measure_le_of_card_bound {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (B : ℕ → Set α) (hB : ∀ n, MeasurableSet (B n)) {M : ℝ}
    (hM : 0 ≤ M)
    (hcard : ∀ (F : Finset ℕ) (x : α), ((F.filter (fun n => x ∈ B n)).card : ℝ) ≤ M) :
    ∑' n, μ (B n) ≤ ENNReal.ofReal M * μ Set.univ := by
  classical
  -- Each `n` contributes the indicator function of `B n`; these are a.e. measurable.
  have hf_meas : ∀ n, AEMeasurable (fun x => (B n).indicator (1 : α → ENNReal) x) μ :=
    fun n => (measurable_const.indicator (hB n)).aemeasurable
  -- Pointwise multiplicity bound: at every point the total number of sets containing it is `≤ M`.
  have hpt : ∀ x, (∑' n, (B n).indicator (1 : α → ENNReal) x) ≤ ENNReal.ofReal M := by
    intro x
    rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro s
    have hsum : ∑ n ∈ s, (B n).indicator (1 : α → ENNReal) x
        = ((s.filter (fun n => x ∈ B n)).card : ENNReal) := by
      simp only [Set.indicator_apply, Pi.one_apply]
      rw [Finset.sum_boole]
    rw [hsum, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hcard s x)
  -- Sum of the measures is the integral of the multiplicity function.
  calc ∑' n, μ (B n)
      = ∑' n, ∫⁻ x, (B n).indicator (1 : α → ENNReal) x ∂μ := by
          congr 1 with n
          rw [MeasureTheory.lintegral_indicator_one (hB n)]
    _ = ∫⁻ x, ∑' n, (B n).indicator (1 : α → ENNReal) x ∂μ := by
          rw [MeasureTheory.lintegral_tsum hf_meas]
    _ ≤ ∫⁻ x, ENNReal.ofReal M ∂μ := MeasureTheory.lintegral_mono hpt
    _ = ENNReal.ofReal M * μ Set.univ := MeasureTheory.lintegral_const _

end Work.EKLC6Core

import Mathlib
import Submission.Port.Aesm

namespace Work.KMTPlan.A6

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

/-- Fatou's lemma, summed over a finite set: if `gK K n → g n` pointwise for every `n ∈ s`
(as `K → ∞`), then the sum of the squared `L²` norms of the limits is at most the liminf of
the sums of the squared `L²` norms of the approximants. -/
theorem finsetSum_sq_le_liminf {s : Finset ℕ} {g : ℕ → ℤ → ℂ} {gK : ℕ → ℕ → ℤ → ℂ}
    (hlim : ∀ n ∈ s, ∀ x : ℤ, Filter.Tendsto (fun K : ℕ => gK K n x) Filter.atTop (nhds (g n x))) :
    ∑ n ∈ s, (MeasureTheory.eLpNorm (g n) 2 MeasureTheory.Measure.count) ^ (2 : ℕ)
      ≤ Filter.liminf (fun K : ℕ => ∑ n ∈ s,
          (MeasureTheory.eLpNorm (gK K n) 2 MeasureTheory.Measure.count) ^ (2 : ℕ)) Filter.atTop := by
  classical
  set μ : Measure ℤ := Measure.count
  -- The squared `L²` norm is the `lintegral` of the squared extended norm.
  have hpowK : ∀ (n K : ℕ), (eLpNorm (gK K n) 2 μ) ^ (2 : ℕ) = ∫⁻ x, ‖gK K n x‖ₑ ^ (2 : ℕ) ∂μ := by
    intro n K
    have h := eLpNorm_nnreal_pow_eq_lintegral (hf := by pw_aesm) (μ := μ) (f := gK K n) (p := 2)
      (by norm_num : (2 : ℝ≥0) ≠ 0)
    simpa using h
  have hpow : ∀ (n : ℕ), (eLpNorm (g n) 2 μ) ^ (2 : ℕ) = ∫⁻ x, ‖g n x‖ₑ ^ (2 : ℕ) ∂μ := by
    intro n
    have h := eLpNorm_nnreal_pow_eq_lintegral (hf := by pw_aesm) (μ := μ) (f := g n) (p := 2)
      (by norm_num : (2 : ℝ≥0) ≠ 0)
    simpa using h
  -- Everything on `ℤ` with the discrete measurable space is measurable.
  have hmeas : ∀ (n K : ℕ), Measurable (fun x : ℤ => ‖gK K n x‖ₑ ^ (2 : ℕ)) :=
    fun n K => by measurability
  have hmeas' : ∀ (n : ℕ), Measurable (fun x : ℤ => ‖g n x‖ₑ ^ (2 : ℕ)) :=
    fun n => by measurability
  -- Pointwise, the liminf of the sums is the sum of the limits.
  have hlimfun : ∀ x : ℤ, Filter.liminf (fun K : ℕ => ∑ n ∈ s, ‖gK K n x‖ₑ ^ (2 : ℕ)) Filter.atTop
      = ∑ n ∈ s, ‖g n x‖ₑ ^ (2 : ℕ) := by
    intro x
    have htend : Tendsto (fun K : ℕ => ∑ n ∈ s, ‖gK K n x‖ₑ ^ (2 : ℕ)) Filter.atTop
        (nhds (∑ n ∈ s, ‖g n x‖ₑ ^ (2 : ℕ))) := by
      apply tendsto_finsetSum
      intro n hn
      have h1 : Tendsto (fun K : ℕ => ‖gK K n x‖ₑ ^ (2 : ℝ)) Filter.atTop
          (nhds (‖g n x‖ₑ ^ (2 : ℝ))) :=
        ((ENNReal.continuous_rpow_const (y := 2)).tendsto _).comp ((hlim n hn x).enorm)
      simp_rw [← ENNReal.rpow_natCast]
      exact h1
    exact htend.liminf_eq
  calc
    ∑ n ∈ s, (eLpNorm (g n) 2 μ) ^ (2 : ℕ)
        = ∑ n ∈ s, ∫⁻ x, ‖g n x‖ₑ ^ (2 : ℕ) ∂μ :=
          Finset.sum_congr rfl (fun n _ => hpow n)
    _ = ∫⁻ x, ∑ n ∈ s, ‖g n x‖ₑ ^ (2 : ℕ) ∂μ :=
          (lintegral_finsetSum s (fun n _ => hmeas' n)).symm
    _ = ∫⁻ x, Filter.liminf (fun K : ℕ => ∑ n ∈ s, ‖gK K n x‖ₑ ^ (2 : ℕ)) Filter.atTop ∂μ :=
          lintegral_congr (fun x => (hlimfun x).symm)
    _ ≤ Filter.liminf (fun K : ℕ => ∫⁻ x, ∑ n ∈ s, ‖gK K n x‖ₑ ^ (2 : ℕ) ∂μ) Filter.atTop :=
          lintegral_liminf_le (fun K => by measurability)
    _ = Filter.liminf (fun K : ℕ => ∑ n ∈ s, (eLpNorm (gK K n) 2 μ) ^ (2 : ℕ)) Filter.atTop := by
          congr 1
          funext K
          rw [lintegral_finsetSum s (fun n _ => hmeas n K)]
          exact Finset.sum_congr rfl (fun n _ => (hpowK n K).symm)

end Work.KMTPlan.A6

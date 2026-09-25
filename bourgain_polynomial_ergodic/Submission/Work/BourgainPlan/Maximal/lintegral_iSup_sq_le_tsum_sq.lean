import Mathlib
import Submission.Commons.Analysis.Measure.iSup_sq_le_tsum_sq
import Submission.Work.BourgainPlan.Maximal.mstFreezeDefs

namespace Work.BourgainPlan.Maximal

/-- **The `ℓ²` maximal function of a sequence of functions is dominated by the sum of their `ℓ²` norms** (Minkowski/`ℓ²`-triangle for the counting measure, in the `lintegral` shape).  For every family `E : ℕ → ℤ → ℝ≥0∞` (no measurability or finiteness hypotheses needed: `Measure.count` on `ℤ` makes everything measurable),
`∫⁻_x (⨆_n E n x)² ∂count ≤ (Σ'_n (∫⁻_x (E n x)² ∂count)^{1/2})²`.
The *short* proof is: `(⨆_n E n x)² ≤ Σ'_n (E n x)²` pointwise (`iSup` of the single terms is `≤` their sum, then square; or `E n x ≤ (Σ'_m (E m x)²)^{1/2}` for each `n`), integrate (`lintegral_mono`, `lintegral_tsum` — Tonelli needs only `AEMeasurable` of each term, free on `ℤ` via `AEMeasurable.of_discrete`/`Measurable.of_discrete`), and finally `Σ'_n ∫ (E n)² ≤ (Σ'_n (∫ (E n)²)^{1/2})²` (compare the double sum `(Σ a_n)² = Σ_n Σ_m a_n a_m ≥ Σ_n a_n²` with `a_n = (∫(E n)²)^{1/2}`, using `ENNReal.tsum_mul_left`/`ENNReal.tsum_mul_right`; the case of an infinite `a_n` is trivial). -/
theorem lintegral_iSup_sq_le_tsum_sq (E : ℕ → ℤ → ENNReal) :
    MeasureTheory.lintegral MeasureTheory.Measure.count (fun x : ℤ => (⨆ n, E n x) ^ (2 : ℝ))
      ≤ (tsum (fun n : ℕ => (MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => E n x ^ (2 : ℝ))) ^ (1 / 2 : ℝ))) ^ 2 := by
  -- Step 1 (pointwise): `(⨆ n, E n x) ^ 2 ≤ Σ'_n (E n x) ^ 2`, by `iSup` of single terms.
  have h1 : MeasureTheory.lintegral MeasureTheory.Measure.count
        (fun x : ℤ => (⨆ n, E n x) ^ (2 : ℝ))
      ≤ MeasureTheory.lintegral MeasureTheory.Measure.count
        (fun x : ℤ => tsum (fun n : ℕ => (E n x) ^ (2 : ℝ))) :=
    MeasureTheory.lintegral_mono fun x =>
      Commons.Analysis.Measure.iSup_sq_le_tsum_sq (fun n => E n x)
  -- Step 2 (Tonelli, no measurability needed on the discrete space `ℤ`).
  have h2 : MeasureTheory.lintegral MeasureTheory.Measure.count
        (fun x : ℤ => tsum (fun n : ℕ => (E n x) ^ (2 : ℝ)))
      = tsum (fun n : ℕ => MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => (E n x) ^ (2 : ℝ))) :=
    MeasureTheory.lintegral_tsum (fun n => AEMeasurable.of_discrete)
  -- Step 3 (arithmetic): with `b n = (∫⁻ (E n)²)^{1/2}`, `Σ_n b n² ≤ (Σ_n b n)²`.
  have h3 : tsum (fun n : ℕ => MeasureTheory.lintegral MeasureTheory.Measure.count
        (fun x : ℤ => (E n x) ^ (2 : ℝ)))
      ≤ (tsum (fun n : ℕ => (MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => E n x ^ (2 : ℝ))) ^ (1 / 2 : ℝ))) ^ 2 := by
    set S : ENNReal := tsum (fun n : ℕ => (MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => E n x ^ (2 : ℝ))) ^ (1 / 2 : ℝ)) with hS
    have hstep : ∀ n : ℕ, (MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => (E n x) ^ (2 : ℝ)))
        ≤ S * ((MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => E n x ^ (2 : ℝ))) ^ (1 / 2 : ℝ)) := by
      intro n
      have hle : ((MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => E n x ^ (2 : ℝ))) ^ (1 / 2 : ℝ)) ≤ S := by
        rw [hS]; exact ENNReal.le_tsum (f := fun n => (MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun x : ℤ => E n x ^ (2 : ℝ))) ^ (1 / 2 : ℝ)) n
      calc (MeasureTheory.lintegral MeasureTheory.Measure.count (fun x : ℤ => (E n x) ^ (2 : ℝ)))
          = ((MeasureTheory.lintegral MeasureTheory.Measure.count
              (fun x : ℤ => E n x ^ (2 : ℝ))) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
            rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
        _ = ((MeasureTheory.lintegral MeasureTheory.Measure.count
              (fun x : ℤ => E n x ^ (2 : ℝ))) ^ (1 / 2 : ℝ))
            * ((MeasureTheory.lintegral MeasureTheory.Measure.count
              (fun x : ℤ => E n x ^ (2 : ℝ))) ^ (1 / 2 : ℝ)) := by
            rw [ENNReal.rpow_two, pow_two]
        _ ≤ S * ((MeasureTheory.lintegral MeasureTheory.Measure.count
              (fun x : ℤ => E n x ^ (2 : ℝ))) ^ (1 / 2 : ℝ)) := by gcongr
    calc tsum (fun n : ℕ => MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun x : ℤ => (E n x) ^ (2 : ℝ)))
        ≤ tsum (fun n : ℕ => S * ((MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun x : ℤ => E n x ^ (2 : ℝ))) ^ (1 / 2 : ℝ))) :=
          ENNReal.tsum_le_tsum hstep
      _ = S * S := by rw [ENNReal.tsum_mul_left, ← hS]
      _ = S ^ 2 := by rw [pow_two]
  exact h1.trans (h2.le.trans h3)

end Work.BourgainPlan.Maximal

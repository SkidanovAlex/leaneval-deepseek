import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface
import Submission.Port.Aesm

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- **The pointwise power identity for `residueLp`.**  For `p > 0` and
`F : ℤ → ℕ → ℝ≥0∞`, `residueLp p q F x ^ p = q⁻¹ * ∑_{n₀ < q} F x n₀ ^ p` (in `ℝ≥0∞`).

(Reproved here rather than imported, so that this module does not depend on the
`fiberVarSampling` development.) -/
theorem residueLp_pow_eq_local (p : ℝ) (hp : 0 < p) (q : ℕ) (F : ℤ → ℕ → ENNReal) (x : ℤ) :
    Work.KMTAreas.A7.residueLp p q F x ^ p
      = (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q, F x n₀ ^ p := by
  rw [show Work.KMTAreas.A7.residueLp p q F x
      = ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
          ENNReal.rpow (F x n₀) p) (1/p) from rfl]
  simp only [one_div]
  calc ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
          ENNReal.rpow (F x n₀) p) p⁻¹ ^ p
      = ENNReal.rpow (ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
          ENNReal.rpow (F x n₀) p) p⁻¹) p := rfl
    _ = ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q, ENNReal.rpow (F x n₀) p :=
        ENNReal.rpow_inv_rpow hp.ne' _
    _ = (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q, F x n₀ ^ p := by
        change (q : ENNReal) ^ (-1 : ℝ) * ∑ n₀ ∈ Finset.range q, ENNReal.rpow (F x n₀) p
          = (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q, F x n₀ ^ p
        rw [ENNReal.rpow_neg_one]
        rfl

/-- **The `ℓ^p`-norm of the residue average is the residue average of the `ℓ^p`-norms.**  For
`p > 0`, `q ≥ 1` and `F : ℤ → ℕ → ℝ≥0∞`,

`‖ residueLp p q F ‖_{ℓ^p(ℤ)} = (q⁻¹ ∑_{n₀<q} ‖ F · n₀ ‖_{ℓ^p(ℤ)}^p)^{1/p}`,

i.e. the Tonelli/Fubini identity `∫_x q⁻¹ ∑_{n₀<q} F x n₀^p dx = q⁻¹ ∑_{n₀<q} ∫_x F x n₀^p dx`
together with the pointwise power identity `(residueLp p q F x)^p = q⁻¹ ∑_{n₀<q} F x n₀^p`
(this is `Work.KMTAreas.A7Hi.residueLp_pow_eq`, already proved in
`Submission/Work/KMTAreas/A7Hi/FiberVarSamplingG.lean` — restate/reprove it in your own file if you
prefer, or state your result in the "power" form
`(eLpNorm (residueLp p q F) p)^p = q⁻¹ ∑_{n₀<q} (eLpNorm (F · n₀) p)^p`, which is equivalent).
Suggested route: `MeasureTheory.lintegral_count`, `ENNReal.tsum_mul_left`,
`Summable.tsum_finsetSum`, `ENNReal.rpow_inv_rpow`, and
`MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal` (the un-suffixed name is deprecated and takes
`ENNReal.ofReal p ≠ 0` rather than `p ≠ 0`). -/
theorem eLpNormResidueLpEq (p : ℝ) (hp : 0 < p) (q : ℕ)
    (F : ℤ → ℕ → ENNReal) :
    MeasureTheory.eLpNorm (Work.KMTAreas.A7.residueLp p q F) (ENNReal.ofReal p)
        MeasureTheory.Measure.count
      = ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) *
          ∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀)
            (ENNReal.ofReal p) MeasureTheory.Measure.count) ^ p) (1 / p) := by
  have hP0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hPt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hPto : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hpne : p ≠ 0 := hp.ne'
  -- the pointwise power identity
  have hI : ∀ x : ℤ, Work.KMTAreas.A7.residueLp p q F x ^ p
      = (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q, F x n₀ ^ p :=
    residueLp_pow_eq_local p hp q F
  -- the norm-to-integral identity for each residue
  have hB : ∀ n₀ : ℕ, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) (ENNReal.ofReal p)
        MeasureTheory.Measure.count) ^ p
      = ∫⁻ y, F y n₀ ^ p ∂MeasureTheory.Measure.count := by
    intro n₀
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hP0 hPt, hPto]
    simp only [enorm_eq_self, one_div]
    exact ENNReal.rpow_inv_rpow hpne _
  have hmeas : Measurable (fun x : ℤ => ∑ n₀ ∈ Finset.range q, F x n₀ ^ p) := by
    apply Finset.measurable_sum
    intro n₀ hn
    exact measurable_of_countable _
  -- Tonelli/Fubini: the integral of the pointwise powers
  have hlin : ∫⁻ x, Work.KMTAreas.A7.residueLp p q F x ^ p ∂MeasureTheory.Measure.count
      = (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q,
          ∫⁻ x, F x n₀ ^ p ∂MeasureTheory.Measure.count := by
    calc ∫⁻ x, Work.KMTAreas.A7.residueLp p q F x ^ p ∂MeasureTheory.Measure.count
        = ∫⁻ x, (q : ENNReal)⁻¹ * (∑ n₀ ∈ Finset.range q, F x n₀ ^ p)
            ∂MeasureTheory.Measure.count := by
          apply MeasureTheory.lintegral_congr; intro x; exact hI x
      _ = (q : ENNReal)⁻¹ * ∫⁻ x, (∑ n₀ ∈ Finset.range q, F x n₀ ^ p)
            ∂MeasureTheory.Measure.count := MeasureTheory.lintegral_const_mul _ hmeas
      _ = (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q,
            ∫⁻ x, F x n₀ ^ p ∂MeasureTheory.Measure.count := by
          rw [MeasureTheory.lintegral_finsetSum (Finset.range q)]
          exact fun n₀ hn => measurable_of_countable _
  have hR : (∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀)
        (ENNReal.ofReal p) MeasureTheory.Measure.count) ^ p)
      = ∑ n₀ ∈ Finset.range q, ∫⁻ y, F y n₀ ^ p ∂MeasureTheory.Measure.count :=
    Finset.sum_congr rfl fun n₀ _ => hB n₀
  rw [hR]
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hP0 hPt, hPto]
  simp only [enorm_eq_self, one_div]
  rw [hlin]
  rw [show ENNReal.rpow (q : ENNReal) (-1) = (q : ENNReal)⁻¹ from ENNReal.rpow_neg_one (q : ENNReal)]
  rfl

end Work.KMTAreas.A7Hi

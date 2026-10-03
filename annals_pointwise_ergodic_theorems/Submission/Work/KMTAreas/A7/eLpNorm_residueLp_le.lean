import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal BigOperators

set_option maxHeartbeats 1000000

/-- **The pointwise power identity for `residueLp`.**  For `p > 0` and `W : ℤ → ℕ → ℝ≥0∞`,
`residueLp p q W x ^ p = q⁻¹ * ∑_{n₀ < q} W x n₀ ^ p` (in `ℝ≥0∞`).  This is the identity
`(z^p)^{1/p} = z` applied to `z = q⁻¹ ∑_{n₀<q} W x n₀ ^ p`. -/
theorem residueLp_rpow_pow_eq (p : ℝ) (hp : 0 < p) (q : ℕ) (W : ℤ → ℕ → ENNReal) (x : ℤ) :
    residueLp p q W x ^ p = (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q, W x n₀ ^ p := by
  rw [show residueLp p q W x
      = ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
          ENNReal.rpow (W x n₀) p) (1/p) from rfl]
  simp only [one_div]
  calc ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
          ENNReal.rpow (W x n₀) p) p⁻¹ ^ p
      = ENNReal.rpow (ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
          ENNReal.rpow (W x n₀) p) p⁻¹) p := rfl
    _ = ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q, ENNReal.rpow (W x n₀) p :=
        ENNReal.rpow_inv_rpow hp.ne' _
    _ = (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q, W x n₀ ^ p := by
        change (q : ENNReal) ^ (-1 : ℝ) * ∑ n₀ ∈ Finset.range q, ENNReal.rpow (W x n₀) p
          = (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q, W x n₀ ^ p
        rw [ENNReal.rpow_neg_one]
        rfl

/-- **The `ℓ^p`-norm of the residue average is the residue average of the `ℓ^p`-norms.**  For
`p > 0` and `W : ℤ → ℕ → ℝ≥0∞`,

`‖ residueLp p q W ‖_{ℓ^p(ℤ)} = (q⁻¹ ∑_{n₀<q} ‖ W · n₀ ‖_{ℓ^p(ℤ)}^p)^{1/p}`,

i.e. Tonelli's theorem for `Measure.count` together with `residueLp_rpow_pow_eq`. -/
theorem eLpNorm_residueLp_eq_residueAvg (p : ℝ) (hp : 0 < p) (q : ℕ) (W : ℤ → ℕ → ENNReal) :
    MeasureTheory.eLpNorm (fun x : ℤ => residueLp p q W x) (ENNReal.ofReal p)
        MeasureTheory.Measure.count
      = ((q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q,
          (MeasureTheory.eLpNorm (fun x : ℤ => W x n₀) (ENNReal.ofReal p)
            MeasureTheory.Measure.count) ^ p) ^ (1 / p) := by
  have hpne : (ENNReal.ofReal p) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hpt : (ENNReal.ofReal p) ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hcancel : (1 / p) * p = 1 := by field_simp
  have hinner : ∀ n₀ : ℕ,
      (MeasureTheory.eLpNorm (fun x : ℤ => W x n₀) (ENNReal.ofReal p)
        MeasureTheory.Measure.count) ^ p = ∑' x : ℤ, (W x n₀) ^ p := by
    intro n₀
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hpne hpt, htoReal,
      MeasureTheory.lintegral_count]
    simp only [enorm_eq_self, ← ENNReal.rpow_mul, hcancel, ENNReal.rpow_one]
  have hptw : ∀ x : ℤ, (residueLp p q W x) ^ p
      = (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q, (W x n₀) ^ p :=
    residueLp_rpow_pow_eq p hp q W
  have hLHS : MeasureTheory.eLpNorm (fun x : ℤ => residueLp p q W x)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      = ((q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q,
          ∑' x : ℤ, (W x n₀) ^ p) ^ (1 / p) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hpne hpt, htoReal,
      MeasureTheory.lintegral_count]
    simp only [enorm_eq_self]
    rw [tsum_congr hptw, ENNReal.tsum_mul_left,
      Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  rw [hLHS, Finset.sum_congr rfl (fun n₀ _ => hinner n₀)]

/- **The residue `ℓ^p` aggregation.**  `residueLp p q W x = (q⁻¹ ∑_{n₀<q} W x n₀ ^ p)^{1/p}`
(`Work.KMTAreas.A7.residueLp`).  Because the exponent `p` of the residue average is the same as the
outer `ℓ^p` exponent, the `eLpNorm` of the residue average is exactly the `ℓ^p` norm of the
sequence `n₀ ↦ W · n₀` composed with `(q⁻¹∑ (·)^p)^{1/p}`, by Tonelli
(`lintegral` of a finite sum and `(z^p)^{1/p} = z`):

  `eLpNorm (residueLp p q W) (ofReal p) count
     = (q⁻¹ ∑_{n₀<q} (eLpNorm (fun x => W x n₀) (ofReal p) count)^p)^{1/p}  ≤ C`

whenever all the `n₀ < q` terms are `≤ C`.  No loss in `q`.
(The near-identical `Work.KMTAreas.A7.eLpNorm_residueLp_le_of_single`, in
`Submission/Work/KMTAreas/A7/fiberVarSamplingCoreG.lean`, carries an extra `0 < q` hypothesis.) -/
theorem eLpNorm_residueLp_le {p : ℝ} (hp : 0 < p) {q : ℕ} (W : ℤ → ℕ → ENNReal) (C : ENNReal)
    (h : ∀ n₀ : ℕ, n₀ < q →
      MeasureTheory.eLpNorm (fun x : ℤ => W x n₀) (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ C) :
    MeasureTheory.eLpNorm (Work.KMTAreas.A7.residueLp p q W) (ENNReal.ofReal p)
      MeasureTheory.Measure.count ≤ C := by
  rw [eLpNorm_residueLp_eq_residueAvg p hp q W]
  have hp1 : (0 : ℝ) ≤ 1 / p := by positivity
  have hsum : (∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun x : ℤ => W x n₀)
        (ENNReal.ofReal p) MeasureTheory.Measure.count) ^ p)
      ≤ (q : ENNReal) * C ^ p := by
    calc ∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun x : ℤ => W x n₀)
            (ENNReal.ofReal p) MeasureTheory.Measure.count) ^ p
        ≤ ∑ n₀ ∈ Finset.range q, C ^ p :=
          Finset.sum_le_sum (fun n₀ hn =>
            ENNReal.rpow_le_rpow (h n₀ (Finset.mem_range.mp hn)) hp.le)
      _ = (q : ENNReal) * C ^ p := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine le_trans (ENNReal.rpow_le_rpow (mul_le_mul' le_rfl hsum) hp1) ?_
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp only [Nat.cast_zero, zero_mul, mul_zero]
    rw [ENNReal.zero_rpow_of_pos (show (0 : ℝ) < 1 / p from by positivity)]
    exact bot_le
  · have hq0 : (q : ENNReal) ≠ 0 := by exact_mod_cast hq.ne'
    have hqt : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
    rw [← mul_assoc, ENNReal.inv_mul_cancel hq0 hqt, one_mul]
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

end Work.KMTAreas.A7

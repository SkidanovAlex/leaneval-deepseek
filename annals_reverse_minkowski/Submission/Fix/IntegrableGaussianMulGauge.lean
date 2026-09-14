-- ⚠ IMPORT-CLASH WORKAROUND (session 123): verbatim copy of Submission.Commons.Analysis.GaussianMeasure.integrable_gaussian_mul_gauge_of_norm_le
-- with the import chain redirected so that the duplicate constant `toLp_norm_sq` of
-- `…bobkov_strong_nD` is not pulled into the same environment as
-- `…brascamp_lieb_truncated`.  Do not import both this file and the commons original.
import Mathlib
import Submission.Fix.MemLpGaugeHermiteSum
import Submission.Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq

namespace Commons.Analysis.GaussianMeasure

open _root_.MeasureTheory

/-- Elementary growth estimate: `1 + ‖y‖` is controlled by `(1 + ‖c‖) * (1 + ‖y - c‖)`. -/
private lemma one_add_norm_le {N : ℕ} (y c : EuclideanSpace ℝ (Fin N)) :
    1 + ‖y‖ ≤ (1 + ‖c‖) * (1 + ‖y - c‖) := by
  have h1 : ‖y‖ ≤ ‖c‖ + ‖y - c‖ := by
    have h := norm_add_le c (y - c)
    simpa [add_sub_cancel] using h
  have h2 : ‖c‖ + ‖y - c‖ + 1 ≤ (1 + ‖c‖) * (1 + ‖y - c‖) := by
    nlinarith [norm_nonneg c, norm_nonneg (y - c)]
  linarith

theorem integrable_gaussian_mul_gauge_of_norm_le {n N : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKcvx : Convex ℝ K) (hK0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ K) (hKabs : Absorbent ℝ K)
    (hKbdd : Bornology.IsVonNBounded ℝ K) (hKbal : Balanced ℝ K)
    {Φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n)} (hΦc : Continuous Φ)
    {A : ℝ} (hA : 0 ≤ A) {D : ℕ} (hΦ : ∀ y, ‖Φ y‖ ≤ A * (1 + ‖y‖) ^ D)
    (a : ℝ) (ha : 0 < a) (c : EuclideanSpace ℝ (Fin N)) :
    MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin N) => Real.exp (-a * ‖y - c‖ ^ 2) * gauge K (Φ y))
      MeasureTheory.volume := by
  obtain ⟨M, hMpos, hMcont, hMbound⟩ :=
    exists_gauge_bound (V := EuclideanSpace ℝ (Fin n)) hKcvx hK0 hKabs hKbal
  -- Integrability of the dominating profile, translated by `c`.
  have hbase : Integrable (fun v : EuclideanSpace ℝ (Fin N) =>
      (1 + ‖v‖) ^ D * Real.exp (-a * ‖v‖ ^ 2)) volume :=
    Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq a ha D
  have htrans : Integrable (fun y : EuclideanSpace ℝ (Fin N) =>
      (1 + ‖y - c‖) ^ D * Real.exp (-a * ‖y - c‖ ^ 2)) volume :=
    hbase.comp_sub_right c
  have hdom : Integrable (fun y : EuclideanSpace ℝ (Fin N) =>
      (M * A * (1 + ‖c‖) ^ D) *
        ((1 + ‖y - c‖) ^ D * Real.exp (-a * ‖y - c‖ ^ 2))) volume :=
    htrans.const_mul _
  refine hdom.mono' ?_ ?_
  · have hgau : Continuous fun y : EuclideanSpace ℝ (Fin N) => gauge K (Φ y) :=
      hMcont.comp hΦc
    have hexp : Continuous fun y : EuclideanSpace ℝ (Fin N) =>
        Real.exp (-a * ‖y - c‖ ^ 2) := by fun_prop
    exact (hexp.mul hgau).aestronglyMeasurable
  · filter_upwards with y
    have hGnn : 0 ≤ gauge K (Φ y) := gauge_nonneg (Φ y)
    have hEpos : 0 < Real.exp (-a * ‖y - c‖ ^ 2) := Real.exp_pos _
    have hnorm : ‖Real.exp (-a * ‖y - c‖ ^ 2) * gauge K (Φ y)‖
        = Real.exp (-a * ‖y - c‖ ^ 2) * gauge K (Φ y) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hEpos.le hGnn)]
    rw [hnorm]
    -- Growth control of `gauge K (Φ y)`.
    have hP : (1 + ‖y‖) ^ D ≤ (1 + ‖c‖) ^ D * (1 + ‖y - c‖) ^ D := by
      have hle := one_add_norm_le y c
      have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + ‖y‖) hle D
      rwa [mul_pow] at hpow
    have hG : gauge K (Φ y) ≤ M * ‖Φ y‖ := hMbound (Φ y)
    have hstep1 : M * ‖Φ y‖ ≤ M * (A * (1 + ‖y‖) ^ D) :=
      mul_le_mul_of_nonneg_left (hΦ y) hMpos.le
    have hstep2 : M * (A * (1 + ‖y‖) ^ D)
        ≤ (M * A) * ((1 + ‖c‖) ^ D * (1 + ‖y - c‖) ^ D) := by
      have hMA : 0 ≤ M * A := mul_nonneg hMpos.le hA
      have := mul_le_mul_of_nonneg_left hP hMA
      calc M * (A * (1 + ‖y‖) ^ D) = (M * A) * (1 + ‖y‖) ^ D := by ring
        _ ≤ (M * A) * ((1 + ‖c‖) ^ D * (1 + ‖y - c‖) ^ D) := this
    have hGR : gauge K (Φ y)
        ≤ (M * A) * ((1 + ‖c‖) ^ D * (1 + ‖y - c‖) ^ D) :=
      le_trans hG (le_trans hstep1 hstep2)
    calc Real.exp (-a * ‖y - c‖ ^ 2) * gauge K (Φ y)
        ≤ Real.exp (-a * ‖y - c‖ ^ 2)
            * ((M * A) * ((1 + ‖c‖) ^ D * (1 + ‖y - c‖) ^ D)) :=
          mul_le_mul_of_nonneg_left hGR hEpos.le
      _ = (M * A * (1 + ‖c‖) ^ D)
            * ((1 + ‖y - c‖) ^ D * Real.exp (-a * ‖y - c‖ ^ 2)) := by ring

end Commons.Analysis.GaussianMeasure

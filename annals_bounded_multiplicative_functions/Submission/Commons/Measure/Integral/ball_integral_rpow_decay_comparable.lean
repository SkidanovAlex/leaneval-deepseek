import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Measure.Integral

open MeasureTheory

/-- Volume of a Euclidean ball in `ℝ^k` (for every `k`, including `k = 0`), expressed with
`toReal` so that the exact factor `R ^ k` of the unit ball volume appears. -/
lemma volume_ball_euclidean_toReal {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) {R : ℝ} (hR : 0 < R) :
    (volume (Metric.ball x R)).toReal
      = R ^ k * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1)).toReal := by
  rw [MeasureTheory.Measure.addHaar_ball_of_pos volume x hR, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hR.le _)]
  rw [finrank_euclideanSpace, Fintype.card_fin]

/-- The unit ball in `ℝ^k` has positive (real-valued) volume, for every `k` (including `k = 0`,
where it is a single point of measure `1`). -/
lemma volume_unitBall_euclidean_pos (k : ℕ) :
    0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1)).toReal := by
  exact ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
    measure_ball_lt_top.ne

/-- Pointwise lower bound: on `B(x,R)`, the weight `y ↦ (1 + ‖y-c‖/R) ^ (-A)` is bounded below
by `4 ^ (-A)` times its value at the centre `x`, when `A ≥ 0`. -/
lemma ball_integral_rpow_decay_pointwise_lower {k : ℕ} {A : ℝ} (hA0 : 0 ≤ A) {R : ℝ}
    (hR : 0 < R) (y x c : EuclideanSpace ℝ (Fin k)) (hy : y ∈ Metric.ball x R) :
    4 ^ (-A) * (1 + ‖x - c‖ / R) ^ (-A) ≤ (1 + ‖y - c‖ / R) ^ (-A) := by
  have hv : 0 ≤ ‖x - c‖ / R := div_nonneg (norm_nonneg _) hR.le
  rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by linarith : (0:ℝ) ≤ 1 + ‖x - c‖ / R)]
  refine Real.rpow_le_rpow_of_nonpos (x := 1 + ‖y - c‖ / R) (y := 4 * (1 + ‖x - c‖ / R))
    ?_ ?_ (neg_nonpos.mpr hA0)
  · have hu : 0 ≤ ‖y - c‖ / R := div_nonneg (norm_nonneg _) hR.le
    linarith
  · have hyx : ‖y - x‖ < R := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hy
    have hsub : ‖y - c‖ ≤ ‖y - x‖ + ‖x - c‖ := by
      simpa [dist_eq_norm] using dist_triangle y x c
    have h2 : ‖y - c‖ ≤ R + ‖x - c‖ := by linarith
    have h3 : ‖y - c‖ / R ≤ (R + ‖x - c‖) / R := div_le_div_of_nonneg_right h2 hR.le
    have h4 : (R + ‖x - c‖) / R = 1 + ‖x - c‖ / R := by field_simp
    linarith

/-- Pointwise upper bound: on `B(x,R)`, the weight `y ↦ (1 + ‖y-c‖/R) ^ (-A)` is bounded above
by `3 ^ A` times its value at the centre `x`, when `A ≥ 0`. -/
lemma ball_integral_rpow_decay_pointwise_upper {k : ℕ} {A : ℝ} (hA0 : 0 ≤ A) {R : ℝ}
    (hR : 0 < R) (y x c : EuclideanSpace ℝ (Fin k)) (hy : y ∈ Metric.ball x R) :
    (1 + ‖y - c‖ / R) ^ (-A) ≤ 3 ^ A * (1 + ‖x - c‖ / R) ^ (-A) := by
  have hv : 0 ≤ ‖x - c‖ / R := div_nonneg (norm_nonneg _) hR.le
  have hu : 0 ≤ ‖y - c‖ / R := div_nonneg (norm_nonneg _) hR.le
  rcases le_or_gt ‖x - c‖ (2 * R) with hcase | hcase
  · -- near field: the weight is at most `1`, while the value at `x` is at least `3 ^ (-A)`
    have hf1 : (1 + ‖y - c‖ / R) ^ (-A) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (neg_nonpos.mpr hA0)
    have hv2 : ‖x - c‖ / R ≤ 2 := by
      rw [div_le_iff₀ hR]; linarith
    have hbase : 1 + ‖x - c‖ / R ≤ 3 := by linarith
    have hge : 3 ^ (-A) ≤ (1 + ‖x - c‖ / R) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos (x := 1 + ‖x - c‖ / R) (y := 3)
        (by linarith) hbase (neg_nonpos.mpr hA0)
    have hone : (1:ℝ) ≤ 3 ^ A * (1 + ‖x - c‖ / R) ^ (-A) := by
      have h3A : (0:ℝ) ≤ 3 ^ A := Real.rpow_nonneg (by norm_num) A
      have hmul := mul_le_mul_of_nonneg_left hge h3A
      have h3 : (3:ℝ) ^ A * 3 ^ (-A) = 1 := by
        rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
      linarith
    linarith
  · -- far field: `1 + ‖y-c‖/R ≥ (1 + ‖x-c‖/R)/2`
    have hyx : ‖y - x‖ < R := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hy
    have h1 : ‖x - c‖ ≤ ‖x - y‖ + ‖y - c‖ := by
      simpa [dist_eq_norm] using dist_triangle x y c
    have h2 : ‖x - c‖ - R ≤ ‖y - c‖ := by
      have hrev : ‖x - y‖ = ‖y - x‖ := norm_sub_rev x y
      rw [hrev] at h1
      linarith
    have hu1 : (‖x - c‖ - R) / R ≤ ‖y - c‖ / R := div_le_div_of_nonneg_right h2 hR.le
    have hu2 : (‖x - c‖ - R) / R = ‖x - c‖ / R - 1 := by field_simp
    have hdR : 1 ≤ ‖x - c‖ / R := by
      rw [le_div_iff₀ hR]; linarith
    have huv : (1 + ‖x - c‖ / R) / 2 ≤ 1 + ‖y - c‖ / R := by linarith
    have hpos : 0 < (1 + ‖x - c‖ / R) / 2 := by linarith
    have hstep := Real.rpow_le_rpow_of_nonpos (x := (1 + ‖x - c‖ / R) / 2)
      (y := 1 + ‖y - c‖ / R) hpos huv (neg_nonpos.mpr hA0)
    have heq : ((1 + ‖x - c‖ / R) / 2) ^ (-A) = (1 + ‖x - c‖ / R) ^ (-A) * 2 ^ A := by
      rw [Real.div_rpow (by linarith) (by norm_num : (0:ℝ) ≤ 2), div_eq_mul_inv,
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) A, inv_inv]
    have h2le : (2:ℝ) ^ A ≤ 3 ^ A :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) hA0
    have hnn : 0 ≤ (1 + ‖x - c‖ / R) ^ (-A) :=
      Real.rpow_nonneg (by linarith) _
    calc (1 + ‖y - c‖ / R) ^ (-A) ≤ ((1 + ‖x - c‖ / R) / 2) ^ (-A) := hstep
      _ = (1 + ‖x - c‖ / R) ^ (-A) * 2 ^ A := heq
      _ ≤ (1 + ‖x - c‖ / R) ^ (-A) * 3 ^ A := mul_le_mul_of_nonneg_left h2le hnn
      _ = 3 ^ A * (1 + ‖x - c‖ / R) ^ (-A) := mul_comm _ _

/-- **Two-sided local comparability of a radially decaying weight**: the ball average of
`y ↦ (1 + ‖y-c‖/R)^{-A}` over `B(x,R)` is comparable to its value at `x`, with a constant
depending only on `k` and `A` (using `A > k` for the far-field contribution). -/
theorem ball_integral_rpow_decay_comparable {k : ℕ} {A : ℝ} (hA : (k:ℝ) < A) (hA0 : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : EuclideanSpace ℝ (Fin k)) {R : ℝ}, 0 < R →
      ∀ x : EuclideanSpace ℝ (Fin k),
        C⁻¹ * R^k * (1 + ‖x - c‖ / R) ^ (-A)
            ≤ ∫ y in Metric.ball x R, (1 + ‖y - c‖ / R) ^ (-A) ∧
        (∫ y in Metric.ball x R, (1 + ‖y - c‖ / R) ^ (-A))
            ≤ C * R^k * (1 + ‖x - c‖ / R) ^ (-A) := by
  -- `hA` is stronger than what the estimate needs, but we use it to normalise `hA0`.
  have hkA : (0:ℝ) < A := lt_of_le_of_lt (Nat.cast_nonneg k) hA
  have hA0' : 0 ≤ A := by linarith [hA0, hkA]
  let V : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1)).toReal
  have hVpos : 0 < V := volume_unitBall_euclidean_pos k
  have h4Apos : 0 < (4:ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  have h4pos : 0 < (4:ℝ) ^ A / V := div_pos h4Apos hVpos
  refine ⟨max (3 ^ A * V) (4 ^ A / V), lt_max_of_lt_right h4pos, ?_⟩
  intro c R hR x
  have hp_pos : 0 < (1 + ‖x - c‖ / R) ^ (-A) :=
    Real.rpow_pos_of_pos (by
      have h1 : 0 ≤ ‖x - c‖ / R := div_nonneg (norm_nonneg _) hR.le
      linarith) _
  have hRk : 0 < R ^ k := pow_pos hR k
  have hvol : (volume (Metric.ball x R)).toReal = R ^ k * V := by
    rw [volume_ball_euclidean_toReal x hR]
  have hbase_cont : Continuous (fun y : EuclideanSpace ℝ (Fin k) => 1 + ‖y - c‖ / R) := by
    fun_prop
  have hf_cont : Continuous
      (fun y : EuclideanSpace ℝ (Fin k) => (1 + ‖y - c‖ / R) ^ (-A)) := by
    refine hbase_cont.rpow_const (fun y => Or.inl ?_)
    have h1 : 0 ≤ ‖y - c‖ / R := div_nonneg (norm_nonneg _) hR.le
    linarith
  have hf_int : IntegrableOn (fun y : EuclideanSpace ℝ (Fin k) => (1 + ‖y - c‖ / R) ^ (-A))
      (Metric.ball x R) := by
    refine IntegrableOn.of_bound (s := Metric.ball x R) measure_ball_lt_top
      hf_cont.aestronglyMeasurable.restrict 1 ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact Real.rpow_le_one_of_one_le_of_nonpos (by
        have h1 : 0 ≤ ‖y - c‖ / R := div_nonneg (norm_nonneg _) hR.le
        linarith) (neg_nonpos.mpr hA0)
    · exact (Real.rpow_pos_of_pos (by
        have h1 : 0 ≤ ‖y - c‖ / R := div_nonneg (norm_nonneg _) hR.le
        linarith) (-A)).le
  have hK_int : IntegrableOn
      (fun _ : EuclideanSpace ℝ (Fin k) => 3 ^ A * (1 + ‖x - c‖ / R) ^ (-A))
      (Metric.ball x R) := by
    refine IntegrableOn.of_bound (s := Metric.ball x R) measure_ball_lt_top
      aestronglyMeasurable_const |3 ^ A * (1 + ‖x - c‖ / R) ^ (-A)| ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
  have h4_int : IntegrableOn
      (fun _ : EuclideanSpace ℝ (Fin k) => 4 ^ (-A) * (1 + ‖x - c‖ / R) ^ (-A))
      (Metric.ball x R) := by
    refine IntegrableOn.of_bound (s := Metric.ball x R) measure_ball_lt_top
      aestronglyMeasurable_const |4 ^ (-A) * (1 + ‖x - c‖ / R) ^ (-A)| ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
  constructor
  · -- lower bound
    have h_lo : ∀ y ∈ Metric.ball x R,
        4 ^ (-A) * (1 + ‖x - c‖ / R) ^ (-A) ≤ (1 + ‖y - c‖ / R) ^ (-A) :=
      fun y hy => ball_integral_rpow_decay_pointwise_lower hA0' hR y x c hy
    have hI_ge : (volume (Metric.ball x R)).toReal * (4 ^ (-A) * (1 + ‖x - c‖ / R) ^ (-A))
        ≤ ∫ y in Metric.ball x R, (1 + ‖y - c‖ / R) ^ (-A) := by
      calc (volume (Metric.ball x R)).toReal * (4 ^ (-A) * (1 + ‖x - c‖ / R) ^ (-A))
          = ∫ y in Metric.ball x R, (4 ^ (-A) * (1 + ‖x - c‖ / R) ^ (-A)) := by
            rw [setIntegral_const]
            simp only [Measure.real_def, smul_eq_mul]
        _ ≤ ∫ y in Metric.ball x R, (1 + ‖y - c‖ / R) ^ (-A) :=
            setIntegral_mono_on h4_int hf_int measurableSet_ball h_lo
    have hCinv : (max (3 ^ A * V) (4 ^ A / V))⁻¹ ≤ V * 4 ^ (-A) := by
      have hCpos : 0 < max (3 ^ A * V) (4 ^ A / V) := lt_max_of_lt_right h4pos
      have h := (inv_le_inv₀ hCpos h4pos).mpr (le_max_right (3 ^ A * V) (4 ^ A / V))
      calc (max (3 ^ A * V) (4 ^ A / V))⁻¹ ≤ (4 ^ A / V)⁻¹ := h
        _ = V * 4 ^ (-A) := by
            rw [inv_div, div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4) A]
    calc (max (3 ^ A * V) (4 ^ A / V))⁻¹ * R ^ k * (1 + ‖x - c‖ / R) ^ (-A)
        = (max (3 ^ A * V) (4 ^ A / V))⁻¹ * (R ^ k * (1 + ‖x - c‖ / R) ^ (-A)) := by
          ring
      _ ≤ (V * 4 ^ (-A)) * (R ^ k * (1 + ‖x - c‖ / R) ^ (-A)) :=
          mul_le_mul_of_nonneg_right hCinv (mul_nonneg hRk.le hp_pos.le)
      _ = (volume (Metric.ball x R)).toReal * (4 ^ (-A) * (1 + ‖x - c‖ / R) ^ (-A)) := by
          rw [hvol]; ring
      _ ≤ ∫ y in Metric.ball x R, (1 + ‖y - c‖ / R) ^ (-A) := hI_ge
  · -- upper bound
    have h_up : ∀ y ∈ Metric.ball x R,
        (1 + ‖y - c‖ / R) ^ (-A) ≤ 3 ^ A * (1 + ‖x - c‖ / R) ^ (-A) :=
      fun y hy => ball_integral_rpow_decay_pointwise_upper hA0' hR y x c hy
    have hI_le : (∫ y in Metric.ball x R, (1 + ‖y - c‖ / R) ^ (-A))
        ≤ (volume (Metric.ball x R)).toReal * (3 ^ A * (1 + ‖x - c‖ / R) ^ (-A)) := by
      calc (∫ y in Metric.ball x R, (1 + ‖y - c‖ / R) ^ (-A))
          ≤ ∫ y in Metric.ball x R, (3 ^ A * (1 + ‖x - c‖ / R) ^ (-A)) :=
            setIntegral_mono_on hf_int hK_int measurableSet_ball h_up
        _ = (volume (Metric.ball x R)).toReal * (3 ^ A * (1 + ‖x - c‖ / R) ^ (-A)) := by
            rw [setIntegral_const]
            simp only [Measure.real_def, smul_eq_mul]
    have hC1 : 3 ^ A * V ≤ max (3 ^ A * V) (4 ^ A / V) := le_max_left _ _
    calc (∫ y in Metric.ball x R, (1 + ‖y - c‖ / R) ^ (-A))
        ≤ (volume (Metric.ball x R)).toReal * (3 ^ A * (1 + ‖x - c‖ / R) ^ (-A)) := hI_le
      _ = (3 ^ A * V) * (R ^ k * (1 + ‖x - c‖ / R) ^ (-A)) := by rw [hvol]; ring
      _ ≤ max (3 ^ A * V) (4 ^ A / V) * (R ^ k * (1 + ‖x - c‖ / R) ^ (-A)) :=
          mul_le_mul_of_nonneg_right hC1 (mul_nonneg hRk.le hp_pos.le)
      _ = max (3 ^ A * V) (4 ^ A / V) * R ^ k * (1 + ‖x - c‖ / R) ^ (-A) := by ring

end Commons.Measure.Integral
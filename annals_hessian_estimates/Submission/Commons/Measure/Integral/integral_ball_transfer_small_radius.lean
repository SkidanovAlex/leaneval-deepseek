import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Commons.Measure.Integral.ball_integral_rpow_decay_comparable

namespace Commons.Measure.Integral

open MeasureTheory Filter

/-- **Translation invariance of the ball integral.**  Integrating a function of `x - z` over the
ball of centre `z` is the same as integrating the function itself over the ball of the same radius
centred at the origin. -/
lemma setIntegral_ball_sub_translate {k : ℕ}
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (z : EuclideanSpace ℝ (Fin k)) (s : ℝ) :
    (∫ x in Metric.ball z s, F (x - z))
      = ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) s, F y := by
  have hmap : Measure.map (MeasurableEquiv.addLeft (-z))
      (volume : Measure (EuclideanSpace ℝ (Fin k))) = volume :=
    Measure.IsAddLeftInvariant.map_add_left_eq_self (-z)
  have h := setIntegral_map_equiv (μ := volume) (MeasurableEquiv.addLeft (-z)) F
      (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) s)
  rw [hmap] at h
  rw [h]
  have hset : (MeasurableEquiv.addLeft (-z)) ⁻¹'
      (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) s) = Metric.ball z s := by
    ext x
    simp only [Set.mem_preimage, MeasurableEquiv.coe_addLeft, Metric.mem_ball, dist_eq_norm,
      neg_add_eq_sub, norm_sub_rev, sub_zero]
  rw [hset]
  refine setIntegral_congr_fun Metric.isOpen_ball.measurableSet fun x _ => ?_
  simp only [MeasurableEquiv.coe_addLeft, neg_add_eq_sub]

/-- **Scaling of the ball integral.**  For `r > 0`, integrating `F` over the ball of radius
`r * s` equals `r ^ k` times the integral of `u ↦ F (r • u)` over the ball of radius `s`. -/
lemma setIntegral_ball_smul_scale {k : ℕ}
    (F : EuclideanSpace ℝ (Fin k) → ℝ) {r s : ℝ} (hr : 0 < r) :
    (∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (r * s), F y)
      = r ^ k * ∫ u in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) s, F (r • u) := by
  have h := Measure.setIntegral_comp_smul_of_pos (μ := volume) F
      (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) s) hr
  rw [smul_ball hr.ne' (0 : EuclideanSpace ℝ (Fin k)) s, smul_zero,
    Real.norm_of_nonneg hr.le, finrank_euclideanSpace_fin, smul_eq_mul] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero k hr.ne'), one_mul]

/-- The weight `x ↦ (1 + ‖z - x‖ / r) ^ (-A)` is integrable on every ball, for `r > 0`, `A ≥ 0`. -/
lemma integrableOn_ball_rpow_decay {k : ℕ} {A r : ℝ} (hr : 0 < r) (hA : 0 ≤ A)
    (c z : EuclideanSpace ℝ (Fin k)) (s : ℝ) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin k) => (1 + ‖z - x‖ / r) ^ (-A))
      (Metric.ball c s) := by
  have hbase : ∀ x : EuclideanSpace ℝ (Fin k), 0 < 1 + ‖z - x‖ / r := by
    intro x
    have : 0 ≤ ‖z - x‖ / r := div_nonneg (norm_nonneg _) hr.le
    linarith
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin k) => (1 + ‖z - x‖ / r) ^ (-A)) :=
    ((continuous_const.add ((continuous_const.sub continuous_id).norm.div_const r)).rpow_const
      (fun x => Or.inl (ne_of_gt (hbase x))))
  refine IntegrableOn.of_bound measure_ball_lt_top hcont.aestronglyMeasurable.restrict 1 ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hbase x).le _)]
  have h1 : (1 : ℝ) ≤ 1 + ‖z - x‖ / r := by
    have : 0 ≤ ‖z - x‖ / r := div_nonneg (norm_nonneg _) hr.le
    linarith
  exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)

/-- **Arithmetic core of the far-field estimate.**  For `0 < r ≤ R ≤ M`, `k ≤ A` and `A > 0`,
`R ^ k * (2r/M) ^ A ≤ 2 ^ (2A) * r ^ k * (1 + M/R) ^ (-A)`. -/
lemma rpow_far_arith {A R r M : ℝ} (k : ℕ) (hA : 0 < A) (hkA : (k : ℝ) ≤ A)
    (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R) (hRM : R ≤ M) :
    R ^ k * (2 * r / M) ^ A ≤ (2 : ℝ) ^ (2 * A) * r ^ k * (1 + M / R) ^ (-A) := by
  have hM : 0 < M := lt_of_lt_of_le hR hRM
  have hA1 : (2 * r / M) ^ A = (2 : ℝ) ^ A * r ^ A * M ^ (-A) := by
    rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ 2 * r) hM.le A,
      Real.mul_rpow (x := (2 : ℝ)) (y := r) (z := A) (by norm_num) hr.le, div_eq_mul_inv,
      Real.rpow_neg hM.le A]
  have hdiv : (R / M) ^ A = R ^ A * M ^ (-A) := by
    rw [Real.div_rpow hR.le hM.le A, div_eq_mul_inv, Real.rpow_neg hM.le A]
  have h2A : (2 : ℝ) ^ (2 * A) * (2 : ℝ) ^ (-A) = (2 : ℝ) ^ A := by
    rw [← Real.rpow_add (x := (2 : ℝ)) (y := 2 * A) (z := -A) (by norm_num),
      show 2 * A + -A = A by ring]
  have hb : (2 : ℝ) ^ (-A) * (R / M) ^ A ≤ (1 + M / R) ^ (-A) := by
    have h1 : (1 : ℝ) ≤ M / R := (one_le_div hR).mpr hRM
    have hle : 1 + M / R ≤ 2 * (M / R) := by linarith
    have hpos : 0 < 1 + M / R := by linarith
    have hstep := Real.rpow_le_rpow_of_nonpos hpos hle (neg_nonpos.mpr hA.le)
    have heq : (2 * (M / R)) ^ (-A) = (2 : ℝ) ^ (-A) * (R / M) ^ A := by
      rw [Real.mul_rpow (x := (2 : ℝ)) (y := M / R) (z := -A) (by norm_num) (by positivity),
        Real.rpow_neg (x := (2 : ℝ)) (by norm_num) A,
        Real.rpow_neg (x := M / R) (by positivity) A,
        show ((M : ℝ) / R) ^ A = ((R / M) ^ A)⁻¹ by
          rw [show (M : ℝ) / R = (R / M)⁻¹ by rw [inv_div],
            Real.inv_rpow (by positivity : (0 : ℝ) ≤ R / M) A],
        inv_inv]
    rwa [heq] at hstep
  have hc : R ^ k * r ^ A ≤ r ^ k * R ^ A := by
    have h0 : 0 < r / R := div_pos hr hR
    have h1 : r / R ≤ 1 := (div_le_one hR).mpr hrR
    have hpow : (r / R) ^ A ≤ (r / R) ^ k := by
      rw [← Real.rpow_natCast (r / R) k]
      calc (r / R) ^ A = (r / R) ^ ((k : ℝ) + (A - (k : ℝ))) := by
              rw [show (k : ℝ) + (A - (k : ℝ)) = A by ring]
        _ = (r / R) ^ (k : ℝ) * (r / R) ^ (A - (k : ℝ)) :=
              Real.rpow_add h0 (k : ℝ) (A - (k : ℝ))
        _ ≤ (r / R) ^ (k : ℝ) * 1 := mul_le_mul_of_nonneg_left
              (Real.rpow_le_one h0.le h1 (sub_nonneg.mpr hkA))
              (Real.rpow_nonneg h0.le _)
        _ = (r / R) ^ (k : ℝ) := by ring
    have hrA : r ^ A = (r / R) ^ A * R ^ A := by
      rw [← Real.mul_rpow (x := r / R) (y := R) (z := A) h0.le hR.le]; congr 1; field_simp
    have hrk : r ^ k = (r / R) ^ k * R ^ k := by
      rw [← mul_pow]; congr 1; field_simp
    calc R ^ k * r ^ A = R ^ k * ((r / R) ^ A * R ^ A) := by rw [hrA]
      _ = ((r / R) ^ A * R ^ k) * R ^ A := by ring
      _ ≤ ((r / R) ^ k * R ^ k) * R ^ A := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hR.le A)
          exact mul_le_mul_of_nonneg_right hpow (pow_nonneg hR.le k)
      _ = r ^ k * R ^ A := by rw [← hrk]
  calc R ^ k * (2 * r / M) ^ A
      = (2 : ℝ) ^ A * (R ^ k * r ^ A) * M ^ (-A) := by rw [hA1]; ring
    _ ≤ (2 : ℝ) ^ A * (r ^ k * R ^ A) * M ^ (-A) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hM.le (-A))
        exact mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg (by norm_num) A)
    _ = (2 : ℝ) ^ A * r ^ k * R ^ A * M ^ (-A) := by ring
    _ = (2 : ℝ) ^ (2 * A) * r ^ k * ((2 : ℝ) ^ (-A) * (R / M) ^ A) := by
        rw [hdiv]
        rw [show (2 : ℝ) ^ (2 * A) * r ^ k * ((2 : ℝ) ^ (-A) * (R ^ A * M ^ (-A)))
            = ((2 : ℝ) ^ (2 * A) * (2 : ℝ) ^ (-A)) * (r ^ k * R ^ A * M ^ (-A)) by ring, h2A]
        ring
    _ ≤ (2 : ℝ) ^ (2 * A) * r ^ k * (1 + M / R) ^ (-A) :=
        mul_le_mul_of_nonneg_left hb (by positivity)

/-- **Near-field half of the transfer estimate.**  If `M = ‖z - c‖ ≤ 8 R` then the ball integral
of the `r`-scale weight over `B(c, 4R)` is at most `9 ^ A` times the full integral of the
`r`-scale weight around `z`, times `r ^ k` and the value of the `R`-scale weight at the centre. -/
private lemma ball_transfer_near {k : ℕ} {A R r M Kint : ℝ} (hA : 0 < A) (hkA : (k : ℝ) < A)
    (hR : 0 < R) (hr : 0 < r) (c z : EuclideanSpace ℝ (Fin k)) (hMdef : M = ‖z - c‖)
    (hKint : Kint = ∫ u : EuclideanSpace ℝ (Fin k), (1 + ‖u‖) ^ (-A)) (h8 : M ≤ 8 * R) :
    (∫ x in Metric.ball c (4 * R), (1 + ‖z - x‖ / r) ^ (-A))
      ≤ (9 : ℝ) ^ A * Kint * r ^ k * (1 + M / R) ^ (-A) := by
  have hMnn : 0 ≤ M := by rw [hMdef]; exact norm_nonneg _
  have hbasepos : 0 < 1 + M / R := by
    have : 0 ≤ M / R := div_nonneg hMnn hR.le
    linarith
  have hInt : Integrable (fun u : EuclideanSpace ℝ (Fin k) => (1 + ‖u‖) ^ (-A)) volume := by
    refine (integrable_one_add_norm (μ := volume) (E := EuclideanSpace ℝ (Fin k)) (r := A)
      (by rwa [finrank_euclideanSpace_fin])).congr ?_
    filter_upwards with u
    simp
  have hKnn : 0 ≤ Kint := by
    rw [hKint]
    exact integral_nonneg (fun u => Real.rpow_nonneg (by positivity) (-A))
  have hsub : Metric.ball c (4 * R) ⊆ Metric.ball z (12 * R) := by
    intro x hx
    rw [Metric.mem_ball] at hx
    rw [Metric.mem_ball, dist_comm]
    have hx' : dist c x < 4 * R := by rw [dist_comm]; exact hx
    have h1 : dist z x ≤ dist z c + dist c x := dist_triangle z c x
    have h2 : dist z c = M := by rw [hMdef, dist_eq_norm]
    rw [h2] at h1
    linarith
  have hf : IntegrableOn (fun x : EuclideanSpace ℝ (Fin k) => (1 + ‖z - x‖ / r) ^ (-A))
      (Metric.ball z (12 * R)) := integrableOn_ball_rpow_decay hr hA.le z z (12 * R)
  have step1 : (∫ x in Metric.ball c (4 * R), (1 + ‖z - x‖ / r) ^ (-A))
      ≤ ∫ x in Metric.ball z (12 * R), (1 + ‖z - x‖ / r) ^ (-A) :=
    setIntegral_mono_set hf
      (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (by positivity) (-A))
      (Filter.Eventually.of_forall fun _ hx => hsub hx)
  have step2 : (∫ x in Metric.ball z (12 * R), (1 + ‖z - x‖ / r) ^ (-A))
      = r ^ k * ∫ u in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (12 * R / r),
          (1 + ‖u‖) ^ (-A) := by
    have h1 : (∫ x in Metric.ball z (12 * R), (1 + ‖z - x‖ / r) ^ (-A))
        = ∫ x in Metric.ball z (12 * R),
            (fun y : EuclideanSpace ℝ (Fin k) => (1 + ‖y‖ / r) ^ (-A)) (x - z) := by
      refine setIntegral_congr_fun Metric.isOpen_ball.measurableSet fun x _ => ?_
      simp only [norm_sub_rev]
    rw [h1, setIntegral_ball_sub_translate (fun y => (1 + ‖y‖ / r) ^ (-A)) z (12 * R)]
    have h3 := setIntegral_ball_smul_scale
      (fun y : EuclideanSpace ℝ (Fin k) => (1 + ‖y‖ / r) ^ (-A)) (s := 12 * R / r) hr
    have h4 : r * (12 * R / r) = 12 * R := by field_simp
    rw [h4] at h3
    rw [h3]
    congr 1
    refine setIntegral_congr_fun Metric.isOpen_ball.measurableSet fun u _ => ?_
    have h5 : ‖r • u‖ / r = ‖u‖ := by
      rw [norm_smul, Real.norm_of_nonneg hr.le, mul_div_cancel_left₀ _ hr.ne']
    rw [h5]
  have step3 : (∫ u in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (12 * R / r),
      (1 + ‖u‖) ^ (-A)) ≤ Kint := by
    rw [hKint]
    exact setIntegral_le_integral hInt
      (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (by positivity) (-A))
  have hIK : (∫ x in Metric.ball c (4 * R), (1 + ‖z - x‖ / r) ^ (-A)) ≤ r ^ k * Kint :=
    calc (∫ x in Metric.ball c (4 * R), (1 + ‖z - x‖ / r) ^ (-A))
        ≤ ∫ x in Metric.ball z (12 * R), (1 + ‖z - x‖ / r) ^ (-A) := step1
      _ = r ^ k * ∫ u in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (12 * R / r),
            (1 + ‖u‖) ^ (-A) := step2
      _ ≤ r ^ k * Kint := mul_le_mul_of_nonneg_left step3 (pow_nonneg hr.le k)
  have hT9 : (9 : ℝ) ^ (-A) ≤ (1 + M / R) ^ (-A) := by
    refine Real.rpow_le_rpow_of_nonpos hbasepos ?_ (neg_nonpos.mpr hA.le)
    have hMR : M / R ≤ 8 := by rw [div_le_iff₀ hR]; linarith
    linarith
  have h9T : 1 ≤ (9 : ℝ) ^ A * (1 + M / R) ^ (-A) := by
    have h9A : (0 : ℝ) < (9 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) _
    have h := mul_le_mul_of_nonneg_left hT9 h9A.le
    have h9 : (9 : ℝ) ^ A * (9 : ℝ) ^ (-A) = 1 := by
      rw [← Real.rpow_add (x := (9 : ℝ)) (y := A) (z := -A) (by norm_num), add_neg_cancel,
        Real.rpow_zero]
    rwa [h9] at h
  calc (∫ x in Metric.ball c (4 * R), (1 + ‖z - x‖ / r) ^ (-A)) ≤ r ^ k * Kint := hIK
    _ ≤ r ^ k * (Kint * ((9 : ℝ) ^ A * (1 + M / R) ^ (-A))) :=
        mul_le_mul_of_nonneg_left (by simpa using mul_le_mul_of_nonneg_left h9T hKnn)
          (pow_nonneg hr.le k)
    _ = (9 : ℝ) ^ A * Kint * r ^ k * (1 + M / R) ^ (-A) := by ring

/-- **Far-field half of the transfer estimate.**  If `M = ‖z - c‖ > 8 R` then the ball integral of
the `r`-scale weight over `B(c, 4R)` is bounded by the volume of `B(c,4R)` (expressed as
`(4R) ^ k V`, `V` the volume of the unit ball), times the value of the weight at distance `M/2`. -/
private lemma ball_transfer_far {k : ℕ} {A R r M : ℝ} (hA : 0 < A) (hkA : (k : ℝ) ≤ A)
    (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R) (c z : EuclideanSpace ℝ (Fin k)) {V : ℝ}
    (hV : 0 ≤ V) (hMdef : M = ‖z - c‖)
    (hvol : (volume (Metric.ball c (4 * R))).toReal = (4 * R) ^ k * V) (h8 : 8 * R < M) :
    (∫ x in Metric.ball c (4 * R), (1 + ‖z - x‖ / r) ^ (-A))
      ≤ 4 ^ k * V * (2 : ℝ) ^ (2 * A) * r ^ k * (1 + M / R) ^ (-A) := by
  have hMpos : 0 < M := by linarith [mul_pos (by norm_num : (0 : ℝ) < 8) hR]
  have hRM : R ≤ M := by linarith
  have hf : IntegrableOn (fun x : EuclideanSpace ℝ (Fin k) => (1 + ‖z - x‖ / r) ^ (-A))
      (Metric.ball c (4 * R)) := integrableOn_ball_rpow_decay hr hA.le c z (4 * R)
  have hg : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin k) => (2 * r / M) ^ A)
      (Metric.ball c (4 * R)) :=
    IntegrableOn.of_bound (f := fun _ : EuclideanSpace ℝ (Fin k) => (2 * r / M) ^ A)
      measure_ball_lt_top aestronglyMeasurable_const _
      (Filter.Eventually.of_forall fun _ => le_refl _)
  have hpoint : ∀ x ∈ Metric.ball c (4 * R),
      (1 + ‖z - x‖ / r) ^ (-A) ≤ (2 * r / M) ^ A := by
    intro x hx
    have hx' : dist c x < 4 * R := by rw [dist_comm]; exact hx
    have htri : M - dist c x ≤ dist z x := by
      have h := dist_triangle z x c
      have hc : dist z c = M := by rw [hMdef, dist_eq_norm]
      rw [hc, dist_comm x c] at h
      linarith
    have hlo : M / 2 ≤ ‖z - x‖ := by
      rw [← dist_eq_norm]
      linarith
    have hbase_pos : 0 < 1 + M / (2 * r) := by
      have : 0 < M / (2 * r) := div_pos hMpos (by linarith)
      linarith
    have hle : 1 + M / (2 * r) ≤ 1 + ‖z - x‖ / r := by
      have hdiv : M / (2 * r) ≤ ‖z - x‖ / r := by
        rw [show M / (2 * r) = M / 2 / r by ring]
        exact div_le_div_of_nonneg_right hlo hr.le
      linarith
    have hstep1 : (1 + ‖z - x‖ / r) ^ (-A) ≤ (1 + M / (2 * r)) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos hbase_pos hle (neg_nonpos.mpr hA.le)
    have hstep2 : (1 + M / (2 * r)) ^ (-A) ≤ (M / (2 * r)) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos (div_pos hMpos (by linarith)) (by linarith)
        (neg_nonpos.mpr hA.le)
    have hstep3 : (M / (2 * r)) ^ (-A) = (2 * r / M) ^ A := by
      rw [show M / (2 * r) = (2 * r / M)⁻¹ by rw [inv_div],
        Real.inv_rpow (div_nonneg (by linarith) hMpos.le) (-A),
        Real.rpow_neg (div_nonneg (by linarith) hMpos.le) A, inv_inv]
    linarith
  have hbound : (∫ x in Metric.ball c (4 * R), (1 + ‖z - x‖ / r) ^ (-A))
      ≤ (volume (Metric.ball c (4 * R))).toReal * (2 * r / M) ^ A :=
    calc (∫ x in Metric.ball c (4 * R), (1 + ‖z - x‖ / r) ^ (-A))
        ≤ ∫ x in Metric.ball c (4 * R), (2 * r / M) ^ A :=
          setIntegral_mono_on hf hg Metric.isOpen_ball.measurableSet hpoint
      _ = (volume (Metric.ball c (4 * R))).toReal * (2 * r / M) ^ A := by
          rw [setIntegral_const]
          simp only [Measure.real_def, smul_eq_mul]
  calc (∫ x in Metric.ball c (4 * R), (1 + ‖z - x‖ / r) ^ (-A))
      ≤ (volume (Metric.ball c (4 * R))).toReal * (2 * r / M) ^ A := hbound
    _ = (4 * R) ^ k * V * (2 * r / M) ^ A := by rw [hvol]
    _ = 4 ^ k * V * (R ^ k * (2 * r / M) ^ A) := by rw [mul_pow]; ring
    _ ≤ 4 ^ k * V * ((2 : ℝ) ^ (2 * A) * r ^ k * (1 + M / R) ^ (-A)) :=
        mul_le_mul_of_nonneg_left (rpow_far_arith k hA hkA hR hr hrR hRM)
          (mul_nonneg (pow_nonneg (by norm_num) k) hV)
    _ = 4 ^ k * V * (2 : ℝ) ^ (2 * A) * r ^ k * (1 + M / R) ^ (-A) := by ring

/-- **Transfer of a ball integral from a small radius `r` to a large radius `R`.**

For `A > k ≥ 1` there is `C > 0` such that for all `R ≥ r > 0` and all centres `c, z`
`∫_{B(c,4R)} (1 + ‖z - x‖ / r) ^ (-A) dx ≤ C r ^ k (1 + ‖z - c‖ / R) ^ (-A)`. -/
theorem integral_ball_transfer_small_radius {k : ℕ} (hk : 1 ≤ k) {A : ℝ} (hA : (k : ℝ) < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R r : ℝ), 0 < R → 0 < r → r ≤ R →
      ∀ (c z : EuclideanSpace ℝ (Fin k)),
        (∫ x in Metric.ball c (4 * R), (1 + ‖z - x‖ / r) ^ (-A))
          ≤ C * r ^ k * (1 + ‖z - c‖ / R) ^ (-A) := by
  have hApos : 0 < A := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  set V : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1)).toReal with hVdef
  have hVpos : 0 < V := by rw [hVdef]; exact volume_unitBall_euclidean_pos k
  obtain ⟨Kint, hKint⟩ : ∃ Kint : ℝ,
      Kint = ∫ u : EuclideanSpace ℝ (Fin k), (1 + ‖u‖) ^ (-A) := ⟨_, rfl⟩
  refine ⟨max ((9 : ℝ) ^ A * Kint) (4 ^ k * V * (2 : ℝ) ^ (2 * A)),
    lt_max_of_lt_right ?_, ?_⟩
  · exact mul_pos (mul_pos (pow_pos (by norm_num) k) hVpos) (Real.rpow_pos_of_pos (by norm_num) _)
  intro R r hR hr hrR c z
  set M : ℝ := ‖z - c‖ with hMdef
  have hbasenn : 0 ≤ 1 + M / R := by
    have hMnn : 0 ≤ M := by rw [hMdef]; exact norm_nonneg _
    have : 0 ≤ M / R := div_nonneg hMnn hR.le
    linarith
  have hTnn : 0 ≤ (1 + M / R) ^ (-A) := Real.rpow_nonneg hbasenn _
  by_cases hcase : M ≤ 8 * R
  · calc (∫ x in Metric.ball c (4 * R), (1 + ‖z - x‖ / r) ^ (-A))
        ≤ (9 : ℝ) ^ A * Kint * r ^ k * (1 + M / R) ^ (-A) :=
          ball_transfer_near hApos hA hR hr c z hMdef hKint hcase
      _ ≤ max ((9 : ℝ) ^ A * Kint)
            (4 ^ k * V * (2 : ℝ) ^ (2 * A)) * r ^ k * (1 + M / R) ^ (-A) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hr.le k)) hTnn
  · have hcase' : 8 * R < M := not_le.mp hcase
    have hvol : (volume (Metric.ball c (4 * R))).toReal = (4 * R) ^ k * V := by
      rw [hVdef]
      exact volume_ball_euclidean_toReal c (by linarith)
    calc (∫ x in Metric.ball c (4 * R), (1 + ‖z - x‖ / r) ^ (-A))
        ≤ 4 ^ k * V * (2 : ℝ) ^ (2 * A) * r ^ k * (1 + M / R) ^ (-A) :=
          ball_transfer_far hApos hA.le hR hr hrR c z hVpos.le hMdef hvol hcase'
      _ ≤ max ((9 : ℝ) ^ A * Kint)
            (4 ^ k * V * (2 : ℝ) ^ (2 * A)) * r ^ k * (1 + M / R) ^ (-A) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hr.le k)) hTnn

end Commons.Measure.Integral
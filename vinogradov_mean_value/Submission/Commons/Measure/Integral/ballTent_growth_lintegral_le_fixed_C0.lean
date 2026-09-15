import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Submission.Commons.Measure.Integral.ball_integral_rpow_decay_comparable
import Submission.Commons.Analysis.Convolution.integral_Ioi_rpow_max_one
import Submission.Commons.Analysis.Convolution.integrableOn_Ioi_rpow_max_one

namespace Commons.Measure.Integral

open MeasureTheory Metric
open scoped ENNReal Pointwise

set_option linter.style.haveILetI false

noncomputable section


/-! ## Elementary helpers -/

private lemma one_add_max_zero_sub_one (t : ℝ) : 1 + max 0 (t - 1) = max 1 t := by
  by_cases h : 1 ≤ t
  · rw [max_eq_right (by linarith : 0 ≤ t - 1), max_eq_right h]; ring
  · rw [max_eq_left (by linarith : t - 1 ≤ 0), add_zero, max_eq_left (by linarith)]

private lemma max_zero_div (a b : ℝ) (hb : 0 < b) : max 0 a / b = max 0 (a / b) := by
  rw [← max_div_div_right hb.le (0 : ℝ) a, zero_div]

private lemma max_zero_sub_div (a : ℝ) {b : ℝ} (hb : 0 < b) :
    max 0 (a - b) / b = max 0 (a / b - 1) := by
  rw [max_zero_div _ _ hb, show (a - b) / b = a / b - 1 by rw [sub_div, div_self hb.ne']]

/-- The distance from a point to the open ball around `0` of radius `R` is
`max 0 (‖x‖ - R)`. -/
private lemma infDist_ball_zero_eq_max {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (x : E) :
    Metric.infDist x (Metric.ball (0 : E) R) = max 0 (‖x‖ - R) := by
  have hne : (Metric.ball (0 : E) R).Nonempty := ⟨0, by simp [Metric.mem_ball, hR]⟩
  refine le_antisymm ?_ ?_
  · refine le_of_forall_gt_imp_ge_of_dense (fun c hc => ?_)
    have hcpos : 0 < c := lt_of_le_of_lt (le_max_left (0 : ℝ) _) hc
    refine le_of_lt ((Metric.infDist_lt_iff hne).2 ?_)
    rcases lt_or_ge ‖x‖ R with h | h
    · exact ⟨x, by simp [Metric.mem_ball, dist_zero_right, h], by simpa using hcpos⟩
    · have hcx : ‖x‖ - R < c := lt_of_le_of_lt (le_max_right _ _) hc
      have hρx : 0 < ‖x‖ := lt_of_lt_of_le hR h
      set δ : ℝ := min (R / 2) ((c - (‖x‖ - R)) / 2) with hδ
      have hδpos : 0 < δ := by rw [hδ]; exact lt_min (by linarith) (by linarith)
      have hδρ : δ < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      refine ⟨((R - δ) / ‖x‖) • x, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity), div_mul_eq_mul_div, div_lt_iff₀ hρx]
        nlinarith [hρx]
      · rw [dist_eq_norm]
        have h1 : x - ((R - δ) / ‖x‖) • x = (1 - (R - δ) / ‖x‖) • x := by
          rw [sub_smul, one_smul]
        rw [h1, norm_smul, Real.norm_eq_abs]
        have h2 : (0 : ℝ) ≤ 1 - (R - δ) / ‖x‖ := by
          rw [sub_nonneg, div_le_one hρx]; linarith
        rw [abs_of_nonneg h2]
        have h3 : (1 - (R - δ) / ‖x‖) * ‖x‖ = ‖x‖ - R + δ := by
          field_simp; ring
        rw [h3]
        have : δ ≤ (c - (‖x‖ - R)) / 2 := min_le_right _ _
        linarith
  · rw [Metric.le_infDist hne]
    intro y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    have h1 : ‖x‖ - R ≤ dist x y := by
      have h3 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
        calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
          _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
      rw [dist_eq_norm]; linarith
    exact max_le dist_nonneg h1

private lemma one_add_infDist_div_eq_max {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (x : E) :
    1 + Metric.infDist x (Metric.ball (0 : E) R) / R = max 1 (‖x‖ / R) := by
  rw [infDist_ball_zero_eq_max hR x, max_zero_sub_div (‖x‖) hR]
  exact one_add_max_zero_sub_one (‖x‖ / R)

private lemma one_add_mul_rpow_le {C₀ s B : ℝ} (hC₀ : 0 ≤ C₀) (hB : 0 ≤ B) (hs : 0 ≤ s) :
    (1 + C₀ * s) ^ B ≤ (1 + C₀) ^ B * (max 1 s) ^ B := by
  have hbase : 1 + C₀ * s ≤ (1 + C₀) * max 1 s := by
    rcases le_or_gt 1 s with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h.le]; nlinarith
  have hpos1 : 0 ≤ 1 + C₀ * s := by nlinarith
  have hpos2 : 0 ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
  calc (1 + C₀ * s) ^ B ≤ ((1 + C₀) * max 1 s) ^ B := Real.rpow_le_rpow hpos1 hbase hB
    _ = (1 + C₀) ^ B * (max 1 s) ^ B := Real.mul_rpow (by linarith) hpos2

/-! ## The one-dimensional radial pieces -/

/-- Scaling of the radial integral: `∫₀^∞ y^{n-1}(max 1 (y/R))^{-σ} dy = R^n (1/n + 1/(σ-n))`. -/
private lemma radial_value {n : ℕ} (hn : 1 ≤ n) {σ R : ℝ} (hR : 0 < R) (hσ : (n : ℝ) < σ) :
    (∫ y in Set.Ioi (0 : ℝ), y ^ (n - 1) * (max 1 (y / R)) ^ (-σ))
      = R ^ n * (1 / (n : ℝ) + 1 / (σ - (n : ℝ))) := by
  set I : ℝ := ∫ x in Set.Ioi (0:ℝ), x ^ (n-1) * (max 1 (x/R)) ^ (-σ) with hIdef
  have hsub := Measure.setIntegral_comp_smul_of_pos (μ := (volume : Measure ℝ))
      (f := fun y : ℝ => y ^ (n-1) * (max 1 (y/R)) ^ (-σ)) (Set.Ioi (0:ℝ)) hR
  rw [Module.finrank_self, pow_one] at hsub
  have hIoi : (R • Set.Ioi (0:ℝ)) = Set.Ioi (0:ℝ) := by
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem₀ hR.ne', Set.mem_Ioi, smul_eq_mul]
    exact ⟨fun h => (mul_pos_iff_of_pos_left (inv_pos.mpr hR)).mp h,
           fun h => (mul_pos_iff_of_pos_left (inv_pos.mpr hR)).mpr h⟩
  rw [hIoi] at hsub
  have hLHS : (∫ x in Set.Ioi (0:ℝ), (R • x) ^ (n-1) * (max 1 ((R • x)/R)) ^ (-σ))
      = R^(n-1) * (∫ x in Set.Ioi (0:ℝ), x ^ (n-1) * (max 1 x) ^ (-σ)) := by
    rw [show (∫ x in Set.Ioi (0:ℝ), (R • x) ^ (n-1) * (max 1 ((R • x)/R)) ^ (-σ))
        = ∫ x in Set.Ioi (0:ℝ), R^(n-1) * (x ^ (n-1) * (max 1 x) ^ (-σ)) from ?_]
    · rw [MeasureTheory.integral_const_mul]
    · refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      have h1 : R * x / R = x := by field_simp
      rw [smul_eq_mul, mul_pow, h1]
      ring
  rw [hLHS] at hsub
  rw [Commons.Analysis.Convolution.integral_Ioi_rpow_max_one n hn σ hσ] at hsub
  rw [smul_eq_mul] at hsub
  have hfin : I = R * (R^(n-1) * (1/(n:ℝ) + 1/(σ-(n:ℝ)))) := by
    rw [hIdef, hsub, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
  rw [hfin]
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn]

/-- Integrability of the scaled radial function without prefactor. -/
private lemma radial_integrable_base {n : ℕ} (hn : 1 ≤ n) {σ R : ℝ} (hR : 0 < R)
    (hσ : (n : ℝ) < σ) :
    MeasureTheory.IntegrableOn (fun y : ℝ => y ^ (n - 1) * (max 1 (y / R)) ^ (-σ))
      (Set.Ioi (0 : ℝ)) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi hR.le, MeasureTheory.integrableOn_union]
  constructor
  · have hcont : ContinuousOn (fun y : ℝ => y ^ (n - 1)) (Set.Icc 0 R) :=
      (continuous_pow (n - 1)).continuousOn
    have hIcc : MeasureTheory.IntegrableOn (fun y : ℝ => y ^ (n - 1)) (Set.Icc 0 R) :=
      hcont.integrableOn_Icc
    refine (hIcc.mono_set Set.Ioc_subset_Icc_self).congr_fun (fun y hy => ?_) measurableSet_Ioc
    rw [max_eq_left ((div_le_one hR).mpr hy.2), Real.one_rpow, mul_one]
  · have hlt : ((n : ℝ) - 1 - σ) < -1 := by linarith
    have hb : MeasureTheory.IntegrableOn (fun y : ℝ => R ^ σ * y ^ ((n : ℝ) - 1 - σ))
        (Set.Ioi R) := (integrableOn_Ioi_rpow_of_lt hlt hR).const_mul (R ^ σ)
    refine hb.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : 0 < y := lt_trans hR hy
    have hyR : 1 < y / R := (one_lt_div hR).mpr hy
    have h1 : (y / R) ^ (-σ) = y ^ (-σ) * R ^ σ := by
      rw [Real.div_rpow hy0.le hR.le, Real.rpow_neg hR.le, div_eq_mul_inv, inv_inv]
    have hmul : y ^ (n - 1) * (y / R) ^ (-σ) = R ^ σ * y ^ ((n : ℝ) - 1 - σ) := by
      rw [h1, ← Real.rpow_natCast y (n - 1), Nat.cast_sub hn, Nat.cast_one,
        show y ^ ((n : ℝ) - 1) * (y ^ (-σ) * R ^ σ)
            = R ^ σ * (y ^ ((n : ℝ) - 1) * y ^ (-σ)) from by ring,
        ← Real.rpow_add hy0, show (n : ℝ) - 1 + -σ = (n : ℝ) - 1 - σ from by ring]
    rw [max_eq_right hyR.le]
    exact hmul.symm

/-- Integrability of the scaled radial function with a constant prefactor. -/
private lemma radial_integrable {n : ℕ} (hn : 1 ≤ n) {σ R c : ℝ} (hR : 0 < R)
    (hσ : (n : ℝ) < σ) :
    MeasureTheory.IntegrableOn (fun y : ℝ => y ^ (n - 1) * (c * (max 1 (y / R)) ^ (-σ)))
      (Set.Ioi (0 : ℝ)) := by
  have h1 := radial_integrable_base (n := n) hn hR hσ
  have h2 : MeasureTheory.IntegrableOn
      (fun y : ℝ => c * (y ^ (n - 1) * (max 1 (y / R)) ^ (-σ))) (Set.Ioi (0 : ℝ)) :=
    h1.const_mul c
  refine h2.congr_fun (fun y _ => ?_) measurableSet_Ioi
  ring

/-- Value of the scaled radial integral with a constant prefactor. -/
private lemma radial_value_const {n : ℕ} (hn : 1 ≤ n) {σ R c : ℝ} (hR : 0 < R)
    (hσ : (n : ℝ) < σ) :
    (∫ y in Set.Ioi (0 : ℝ), y ^ (n - 1) * (c * (max 1 (y / R)) ^ (-σ)))
      = c * (R ^ n * (1 / (n : ℝ) + 1 / (σ - (n : ℝ)))) := by
  have h : (∫ y in Set.Ioi (0 : ℝ), y ^ (n - 1) * (c * (max 1 (y / R)) ^ (-σ)))
      = ∫ y in Set.Ioi (0 : ℝ), c * (y ^ (n - 1) * (max 1 (y / R)) ^ (-σ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => by ring)
  rw [h, MeasureTheory.integral_const_mul, radial_value hn hR hσ]

/-! ## Pointwise domination -/

private lemma ballTent_growth_pointwise {n : ℕ} {A B : ℝ} (hB : 0 ≤ B) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    {R : ℝ} (hR : 0 < R) (w : EuclideanSpace ℝ (Fin n)) :
    ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal)⁻¹
        * (1 + Metric.infDist w (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) / R) ^ (-A)
        * (1 + C₀ * ‖w‖ / R) ^ B
    ≤ ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal)⁻¹
        * (1 + C₀) ^ B * (max 1 (‖w‖ / R)) ^ (-(A - B)) := by
  have hcR : 0 ≤ ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal)⁻¹ :=
    inv_nonneg.mpr ENNReal.toReal_nonneg
  rw [one_add_infDist_div_eq_max hR w]
  have hs : 0 ≤ ‖w‖ / R := div_nonneg (norm_nonneg _) hR.le
  have hmax1 : (1:ℝ) ≤ max 1 (‖w‖ / R) := le_max_left _ _
  have hmaxpos : 0 < max 1 (‖w‖ / R) := lt_of_lt_of_le zero_lt_one hmax1
  have hgrowth := one_add_mul_rpow_le hC₀ hB hs
  rw [show C₀ * (‖w‖ / R) = C₀ * ‖w‖ / R from by ring] at hgrowth
  have hdecay_nn : 0 ≤ (max 1 (‖w‖ / R)) ^ (-A) :=
    Real.rpow_nonneg (le_trans zero_le_one hmax1) _
  have hpow : (max 1 (‖w‖ / R)) ^ (-A) * (max 1 (‖w‖ / R)) ^ B
      = (max 1 (‖w‖ / R)) ^ (-(A - B)) := by
    rw [← Real.rpow_add hmaxpos]; congr 1; ring
  calc ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal)⁻¹
        * (max 1 (‖w‖ / R)) ^ (-A) * (1 + C₀ * ‖w‖ / R) ^ B
      = ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal)⁻¹
        * ((max 1 (‖w‖ / R)) ^ (-A) * (1 + C₀ * ‖w‖ / R) ^ B) := by ring
    _ ≤ ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal)⁻¹
        * ((max 1 (‖w‖ / R)) ^ (-A) * ((1 + C₀) ^ B * (max 1 (‖w‖ / R)) ^ B)) := by
          apply mul_le_mul_of_nonneg_left _ hcR
          exact mul_le_mul_of_nonneg_left hgrowth hdecay_nn
    _ = ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal)⁻¹
        * (1 + C₀) ^ B * (max 1 (‖w‖ / R)) ^ (-(A - B)) := by
          rw [show ((max 1 (‖w‖ / R)) ^ (-A) * ((1 + C₀) ^ B * (max 1 (‖w‖ / R)) ^ B))
              = (1 + C₀) ^ B * ((max 1 (‖w‖ / R)) ^ (-A) * (max 1 (‖w‖ / R)) ^ B)
              from by ring]
          rw [hpow, ← mul_assoc]

/-! ## The ENNReal integrand as `ofReal` of a real function -/

private lemma target_integrand_eq {n : ℕ} {A B : ℝ} {R : ℝ} (hR : 0 < R) (C₀ : ℝ)
    (hC₀ : 0 ≤ C₀) (w : EuclideanSpace ℝ (Fin n)) :
    (ENNReal.ofReal (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal)⁻¹
        * ENNReal.ofReal ((1 + Metric.infDist w (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) / R) ^ (-A))
        * ENNReal.ofReal ((1 + C₀ * ‖w‖ / R) ^ B)
      = ENNReal.ofReal (((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal)⁻¹
          * (1 + Metric.infDist w (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) / R) ^ (-A)
          * (1 + C₀ * ‖w‖ / R) ^ B) := by
  have hxR : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ hR).ne' measure_ball_lt_top.ne
  have hu : 0 ≤ (1 + Metric.infDist w (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) / R) ^ (-A) :=
    le_of_lt (Real.rpow_pos_of_pos (by
      have h1 : 0 ≤ Metric.infDist w (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) / R :=
        div_nonneg Metric.infDist_nonneg hR.le
      linarith) _)
  have hv : 0 ≤ (1 + C₀ * ‖w‖ / R) ^ B :=
    Real.rpow_nonneg (by
      have h1 : 0 ≤ C₀ * ‖w‖ / R := div_nonneg (mul_nonneg hC₀ (norm_nonneg w)) hR.le
      linarith) _
  rw [← ENNReal.ofReal_inv_of_pos hxR,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hxR.le),
    ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hxR.le) hu)]

end

/-! ## Main theorem -/

theorem ballTent_growth_lintegral_le_fixed_C0 {n : ℕ} {A B : ℝ} (hB : 0 ≤ B)
    (hAB : B + (n : ℝ) < A) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ), 0 < R →
      MeasureTheory.lintegral MeasureTheory.volume
        (fun w : EuclideanSpace ℝ (Fin n) =>
          (ENNReal.ofReal (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal)⁻¹
          * ENNReal.ofReal ((1 + Metric.infDist w (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) / R) ^ (-A))
          * ENNReal.ofReal ((1 + C₀ * ‖w‖ / R) ^ B))
      ≤ ENNReal.ofReal C := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `n = 0`: the space is a single point, the integrand is identically `1`.
    subst hn0
    refine ⟨1, zero_le_one, ?_⟩
    intro R hR
    have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 0))) Set.univ = 1 := by
      have h1 : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
        rw [volume_pi, Measure.pi_univ]; simp
      have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 0)
      rw [← hmp.map_eq] at h1
      rw [Measure.map_apply hmp.measurable MeasurableSet.univ] at h1
      simpa using h1
    have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) R = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro w
      rw [Metric.mem_ball]
      rw [show w = 0 from Subsingleton.elim _ _, dist_self]; exact hR
    have hF : ∀ w : EuclideanSpace ℝ (Fin 0),
        (ENNReal.ofReal (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) R)).toReal)⁻¹
          * ENNReal.ofReal ((1 + Metric.infDist w (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) R) / R) ^ (-A))
          * ENNReal.ofReal ((1 + C₀ * ‖w‖ / R) ^ B) = 1 := by
      intro w
      have hnorm : ‖w‖ = 0 := by
        rw [show w = 0 from Subsingleton.elim _ _, norm_zero]
      have hid : Metric.infDist w (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) R) = 0 := by
        rw [hball]
        have h : Metric.infDist w (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) ≤ dist w w :=
          Metric.infDist_le_dist_of_mem (Set.mem_univ w)
        rw [dist_self] at h
        exact le_antisymm h Metric.infDist_nonneg
      have e1 : (ENNReal.ofReal (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) R)).toReal)⁻¹ = 1 := by
        rw [hball, hvol, ENNReal.toReal_one, ENNReal.ofReal_one, inv_one]
      have e2 : ENNReal.ofReal ((1 + Metric.infDist w (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) R) / R) ^ (-A)) = 1 := by
        rw [hid, zero_div, add_zero, Real.one_rpow, ENNReal.ofReal_one]
      have e3 : ENNReal.ofReal ((1 + C₀ * ‖w‖ / R) ^ B) = 1 := by
        rw [hnorm, mul_zero, zero_div, add_zero, Real.one_rpow, ENNReal.ofReal_one]
      rw [e1, e2, e3]
      simp
    rw [MeasureTheory.lintegral_congr hF, MeasureTheory.lintegral_const, hvol]
    simp
  · -- `n ≥ 1`
    have hn1 : 1 ≤ n := hnpos
    haveI : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
    have hσn : (n : ℝ) < A - B := by linarith
    set V : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal with hVdef
    have hVpos : 0 < V := volume_unitBall_euclidean_pos n
    have hσpos : 0 < A - B - (n : ℝ) := by linarith
    set C : ℝ := (1 + C₀) ^ B * (1 + (n : ℝ) / (A - B - (n : ℝ))) with hCdef
    have hCnn : 0 ≤ C := by
      rw [hCdef]
      have h1 : (0 : ℝ) ≤ (1 + C₀) ^ B := Real.rpow_nonneg (by linarith) B
      have h2 : 0 ≤ 1 + (n : ℝ) / (A - B - (n : ℝ)) := by
        have := div_nonneg (Nat.cast_nonneg n) hσpos.le
        linarith
      exact mul_nonneg h1 h2
    refine ⟨C, hCnn, ?_⟩
    intro R hR
    set cR : ℝ := ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal)⁻¹ with hcRdef
    have hcRnn : 0 ≤ cR := by rw [hcRdef]; exact inv_nonneg.mpr ENNReal.toReal_nonneg
    have hRnpos : 0 < R ^ n := pow_pos hR n
    have hcRRn : cR * R ^ n = V⁻¹ := by
      rw [hcRdef, volume_ball_euclidean_toReal (0 : EuclideanSpace ℝ (Fin n)) hR, hVdef]
      field_simp
    set G : ℝ → ℝ := fun t => cR * (1 + C₀) ^ B * (max 1 (t / R)) ^ (-(A - B)) with hGdef
    have hGnn : ∀ t, 0 ≤ G t := fun t => by
      rw [hGdef]
      exact mul_nonneg (mul_nonneg hcRnn (Real.rpow_nonneg (by linarith) B))
        (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
    have hint : MeasureTheory.Integrable (fun w : EuclideanSpace ℝ (Fin n) => G ‖w‖)
        MeasureTheory.volume := by
      rw [MeasureTheory.integrable_fun_norm_addHaar, finrank_euclideanSpace, Fintype.card_fin]
      have h := radial_integrable (n := n) hn1 (σ := A - B) (R := R)
        (c := cR * (1 + C₀) ^ B) hR hσn
      refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
      rw [hGdef, smul_eq_mul]
    have hval : (∫ w : EuclideanSpace ℝ (Fin n), G ‖w‖) ≤ C := by
      rw [MeasureTheory.integral_fun_norm_addHaar, MeasureTheory.Measure.real_def, ← hVdef,
        finrank_euclideanSpace, Fintype.card_fin]
      have hinner : (∫ y in Set.Ioi (0:ℝ), y ^ (n - 1) • G y)
          = cR * (1 + C₀) ^ B * (R ^ n * (1 / (n : ℝ) + 1 / ((A - B) - (n : ℝ)))) := by
        have hcongr : (∫ y in Set.Ioi (0:ℝ), y ^ (n - 1) • G y)
            = ∫ y in Set.Ioi (0:ℝ),
                y ^ (n - 1) * ((cR * (1 + C₀) ^ B) * (max 1 (y / R)) ^ (-(A - B))) := by
          refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
          rw [hGdef, smul_eq_mul]
        rw [hcongr]
        exact radial_value_const hn1 hR hσn
      rw [hinner, nsmul_eq_mul, smul_eq_mul]
      have hnR : (n : ℝ) ≠ 0 := by positivity
      have hkey : (n : ℝ) * V * (cR * (1 + C₀) ^ B * (R ^ n * (1 / (n : ℝ) + 1 / ((A - B) - (n : ℝ)))))
          = C := by
        rw [show (n : ℝ) * V * (cR * (1 + C₀) ^ B * (R ^ n * (1 / (n : ℝ) + 1 / ((A - B) - (n : ℝ)))))
            = (n : ℝ) * V * (1 + C₀) ^ B * (cR * R ^ n)
                * (1 / (n : ℝ) + 1 / ((A - B) - (n : ℝ))) from by ring]
        rw [hcRRn, hCdef]
        field_simp
      rw [← mul_assoc, hkey]
    have hbound : ∀ w : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal)⁻¹
          * (1 + Metric.infDist w (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) / R) ^ (-A)
          * (1 + C₀ * ‖w‖ / R) ^ B)
        ≤ ENNReal.ofReal (G ‖w‖) := by
      intro w
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hGdef]
      exact ballTent_growth_pointwise hB C₀ hC₀ hR w
    calc MeasureTheory.lintegral MeasureTheory.volume
          (fun w : EuclideanSpace ℝ (Fin n) =>
            (ENNReal.ofReal (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal)⁻¹
            * ENNReal.ofReal ((1 + Metric.infDist w (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) / R) ^ (-A))
            * ENNReal.ofReal ((1 + C₀ * ‖w‖ / R) ^ B))
        = MeasureTheory.lintegral MeasureTheory.volume
            (fun w : EuclideanSpace ℝ (Fin n) =>
              ENNReal.ofReal (((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)).toReal)⁻¹
                * (1 + Metric.infDist w (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) / R) ^ (-A)
                * (1 + C₀ * ‖w‖ / R) ^ B)) :=
          MeasureTheory.lintegral_congr (fun w => target_integrand_eq hR C₀ hC₀ w)
      _ ≤ MeasureTheory.lintegral MeasureTheory.volume
            (fun w : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (G ‖w‖)) :=
          MeasureTheory.lintegral_mono (fun w => hbound w)
      _ = ENNReal.ofReal (∫ w : EuclideanSpace ℝ (Fin n), G ‖w‖) := by
          rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall (fun w => hGnn ‖w‖))]
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hval

end Commons.Measure.Integral
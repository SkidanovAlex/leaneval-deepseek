import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Commons.Analysis.Inequalities.loomis_whitney

namespace Commons.Measure.EuclideanSpace

open MeasureTheory MeasureTheory.Measure Metric
open scoped ENNReal BigOperators

/-- The squared norm of `WithLp.toLp 2 x` in `EuclideanSpace ℝ (Fin n)` is the sum of the
squares of the coordinates. -/
lemma norm_toLp_sq (n : ℕ) (x : Fin n → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 = ∑ i, x i ^ 2 := by
  have h : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ = (∑ i, x i ^ 2) ^ (1/2 : ℝ) := by
    rw [PiLp.norm_eq_sum (p := 2) (by norm_num)]
    simp [Real.norm_eq_abs, sq_abs]
  rw [h, ← Real.rpow_natCast, ← Real.rpow_mul]
  · norm_num
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- The Lebesgue measure of the set of points of `Fin n → ℝ` whose euclidean norm is `< r`
coincides with the volume of the ball of radius `r` in `EuclideanSpace ℝ (Fin n)`. -/
lemma pi_volume_euclid_ball {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Fin n → ℝ)) {x | ∑ i, x i ^ 2 < r ^ 2}
      = (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 r) := by
  have hset : {x : Fin n → ℝ | ∑ i, x i ^ 2 < r ^ 2}
      = (WithLp.toLp 2) ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_ball, dist_zero_right,
      ← norm_toLp_sq n x, sq_lt_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hr]
  rw [hset]
  exact (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    (measurableSet_ball.nullMeasurableSet)

/-- For `x ≥ 0` one has `(√x)^n = x^{n/2}`. -/
lemma sqrt_pow_eq_rpow (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt x ^ n = x ^ ((n:ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  ring_nf

/-- Fubini decomposition of the volume of the unit ball in `Fin (n+1) → ℝ`. -/
lemma pi_volume_split (n : ℕ) :
    (volume : Measure (Fin (n+1) → ℝ)) {x | ∑ i, x i ^ 2 < 1}
      = ∫⁻ u : ℝ, (volume : Measure (Fin n → ℝ)) {v | u ^ 2 + ∑ j, v j ^ 2 < 1} := by
  set c : ℝ × (Fin n → ℝ) → (Fin (n+1) → ℝ) := fun p => Fin.cons p.1 p.2 with hc_def
  have hc : MeasurePreserving c volume volume :=
    Commons.Analysis.Inequalities.volume_preserving_cons n
  set B : Set (Fin (n+1) → ℝ) := {x | ∑ i, x i ^ 2 < 1} with hB_def
  set S : Set (ℝ × (Fin n → ℝ)) := {p | p.1 ^ 2 + ∑ j, (p.2 j) ^ 2 < 1} with hS_def
  have hpre : c ⁻¹' B = S := by
    ext p
    simp only [Set.mem_preimage, hB_def, Set.mem_ofPred_eq, hS_def, c]
    rw [Fin.sum_univ_succ]
    simp [Fin.cons_zero, Fin.cons_succ]
  have hcont : Continuous (fun x : Fin (n+1) → ℝ => ∑ i, x i ^ 2) := by fun_prop
  have hBm : MeasurableSet B := by
    have : B = {x : Fin (n+1) → ℝ | (∑ i, x i ^ 2) < 1} := rfl
    rw [this]
    exact measurableSet_lt hcont.measurable measurable_const
  have hSm : MeasurableSet S := by
    rw [← hpre]
    exact hBm.preimage hc.measurable
  have h1 : (volume : Measure (Fin (n+1) → ℝ)) B
      = (volume.prod volume : Measure (ℝ × (Fin n → ℝ))) S := by
    rw [← hpre, ← hc.measure_preimage hBm.nullMeasurableSet, volume_eq_prod]
  rw [h1, Measure.prod_apply hSm]
  apply lintegral_congr
  intro u
  congr 1

/-- The volume of the section of the unit ball at height `u` in `(-1,1)`. -/
lemma section_volume (n : ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (-1) 1) :
    (volume : Measure (Fin n → ℝ)) {v | u ^ 2 + ∑ j, v j ^ 2 < 1}
      = ENNReal.ofReal ((1 - u^2) ^ ((n:ℝ)/2)) *
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
  have hpos : 0 < 1 - u ^ 2 := by have h1 := hu.1; have h2 := hu.2; nlinarith
  have hset : {v : Fin n → ℝ | u ^ 2 + ∑ j, v j ^ 2 < 1}
      = {v : Fin n → ℝ | ∑ j, v j ^ 2 < (Real.sqrt (1 - u^2)) ^ 2} := by
    ext v
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Real.sq_sqrt (le_of_lt hpos)]
    constructor <;> intro h <;> linarith
  rw [hset, pi_volume_euclid_ball (Real.sqrt_nonneg _)]
  rw [Measure.addHaar_ball_of_pos volume (0 : EuclideanSpace ℝ (Fin n))
    (Real.sqrt_pos.mpr hpos)]
  rw [finrank_euclideanSpace, Fintype.card_fin]
  congr 1
  rw [sqrt_pow_eq_rpow _ (le_of_lt hpos) n]

/-- The section of the unit ball at height `u` with `|u| ≥ 1` is empty. -/
lemma section_volume_zero (n : ℕ) {u : ℝ} (hu : u ∉ Set.Ioo (-1) 1) :
    (volume : Measure (Fin n → ℝ)) {v | u ^ 2 + ∑ j, v j ^ 2 < 1} = 0 := by
  have hle : 1 - u ^ 2 ≤ 0 := by
    simp only [Set.mem_Ioo, not_and_or, not_lt] at hu
    rcases hu with h | h <;> nlinarith
  have hempty : {v : Fin n → ℝ | u ^ 2 + ∑ j, v j ^ 2 < 1} = ∅ := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (v j))
    linarith
  rw [hempty, measure_empty]

theorem volume_ball_succ_integral (n : ℕ) :
    (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).toReal
      = (∫ u in (-1:ℝ)..1, (1 - u ^ 2) ^ ((n : ℝ) / 2)) *
          (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
  set C : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) with hC
  set V : ℝ := C.toReal with hV
  set f : ℝ → ℝ≥0∞ := fun u => (volume : Measure (Fin n → ℝ)) {v | u ^ 2 + ∑ j, v j ^ 2 < 1}
    with hf
  set Fold : ℝ → ℝ≥0∞ := (Set.Ioo (-1:ℝ) 1).indicator
      (fun u => ENNReal.ofReal ((1 - u^2) ^ ((n:ℝ)/2)) * C) with hFold
  set g : ℝ → ℝ := (Set.Ioo (-1:ℝ) 1).indicator
      (fun u => (1 - u^2) ^ ((n:ℝ)/2) * V) with hg
  have hCLT : C < ∞ := by rw [hC]; exact measure_ball_lt_top
  have hFold_meas : Measurable Fold := by
    rw [hFold]
    exact Measurable.indicator (by measurability) measurableSet_Ioo
  have hFold_lt_top : ∀ u, Fold u < ∞ := by
    intro u
    rw [hFold]
    by_cases hu : u ∈ Set.Ioo (-1:ℝ) 1
    · rw [Set.indicator_of_mem hu]
      have hpos : 0 < 1 - u ^ 2 := by have h1 := hu.1; have h2 := hu.2; nlinarith
      have hx0 : 0 ≤ (1 - u^2) ^ ((n:ℝ)/2) := Real.rpow_nonneg (le_of_lt hpos) _
      have hx1 : (1 - u^2) ^ ((n:ℝ)/2) ≤ 1 :=
        Real.rpow_le_one (le_of_lt hpos) (by nlinarith [sq_nonneg u]) (by positivity)
      have hle1 : ENNReal.ofReal ((1 - u^2) ^ ((n:ℝ)/2)) ≤ 1 := by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hx1
      calc ENNReal.ofReal ((1 - u^2) ^ ((n:ℝ)/2)) * C ≤ 1 * C :=
            mul_le_mul_of_nonneg_right hle1 (bot_le : (0:ℝ≥0∞) ≤ C)
        _ = C := one_mul C
        _ < ∞ := hCLT
    · rw [Set.indicator_of_notMem hu]; simp
  have hf_eq : f = Fold := by
    funext u
    rw [hf, hFold]
    by_cases hu : u ∈ Set.Ioo (-1:ℝ) 1
    · rw [Set.indicator_of_mem hu]; exact section_volume n hu
    · rw [Set.indicator_of_notMem hu]; exact section_volume_zero n hu
  have hintegrand : ∀ u, (Fold u).toReal = g u := by
    intro u
    rw [hFold, hg]
    by_cases hu : u ∈ Set.Ioo (-1:ℝ) 1
    · have hpos : 0 < 1 - u ^ 2 := by have h1 := hu.1; have h2 := hu.2; nlinarith
      rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (Real.rpow_nonneg (le_of_lt hpos) _)]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, ENNReal.toReal_zero]
  have hball : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n+1))) 1))
      = (volume : Measure (Fin (n+1) → ℝ)) {x | ∑ i, x i ^ 2 < 1} := by
    rw [← pi_volume_euclid_ball (n := n+1) (r := 1) zero_le_one]
    norm_num
  rw [hball, pi_volume_split n, ← hf, hf_eq,
    ← integral_toReal hFold_meas.aemeasurable (Filter.Eventually.of_forall hFold_lt_top)]
  simp_rw [hintegrand]
  rw [hg, integral_indicator measurableSet_Ioo, integral_mul_const,
    setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]

end Commons.Measure.EuclideanSpace
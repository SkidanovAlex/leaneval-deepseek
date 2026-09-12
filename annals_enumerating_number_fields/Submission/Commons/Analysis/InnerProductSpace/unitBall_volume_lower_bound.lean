import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Commons.MeasureTheory.Volume.volume_pi_Icc

namespace Commons.Analysis.InnerProductSpace

-- Lower bound for the volume of the unit ball of a finite-dimensional real inner product space:
-- it contains the cube of side 2/sqrt m (m = dimension), giving vol >= (2/sqrt m)^m.
-- Equivalent forms: the ball of radius sqrt m contains the cube of side 2, so
-- (2/sqrt m)^m * vol(unit ball) = vol(ball of radius 1/sqrt m) >= vol(cube of side 2/sqrt m).
theorem unitBall_volume_lower_bound {m : ℕ} (hm : 0 < m) :
    (2 / Real.sqrt m) ^ m ≤
      ENNReal.toReal (MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
  set r : ℝ := 1 / Real.sqrt m with hr
  have hrpos : 0 < r := by
    rw [hr]; exact one_div_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hm))
  have hsq : r ^ 2 = (m : ℝ)⁻¹ := by
    rw [hr, div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg m), one_div]
  have hmul : (m : ℝ) * r ^ 2 = 1 := by
    rw [hsq, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hm.ne')]
  have hvolC : (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))
      (Set.pi Set.univ (fun _ : Fin m => Set.Icc (-r) r)) = ENNReal.ofReal ((2*r)^m) :=
    Commons.MeasureTheory.Volume.volume_pi_Icc r hrpos.le
  have hsub : Set.pi Set.univ (fun _ : Fin m => Set.Icc (-r) r) ⊆
      WithLp.toLp 2 ⁻¹' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) := by
    intro y hy
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    have hyi : ∀ i : Fin m, |y i| ≤ r := by
      intro i
      have h : y i ∈ Set.Icc (-r) r := hy i (Set.mem_univ i)
      exact abs_le.mpr (by rw [Set.mem_Icc] at h; exact h)
    have hsum : (∑ i : Fin m, ‖y i‖ ^ 2) ≤ 1 := by
      have h1 : ∀ i : Fin m, ‖y i‖ ^ 2 ≤ r ^ 2 := by
        intro i
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hyi i) 2
      calc (∑ i : Fin m, ‖y i‖ ^ 2) ≤ ∑ _i : Fin m, r ^ 2 := Finset.sum_le_sum (fun i _ => h1 i)
        _ = (m : ℝ) * r ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = 1 := hmul
    have hL2 : ‖WithLp.toLp 2 y‖ ^ 2 = ∑ i : Fin m, ‖y i‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
    have hle1 : ‖WithLp.toLp 2 y‖ ^ 2 ≤ 1 := by rw [hL2]; exact hsum
    have hnorm_le : ‖WithLp.toLp 2 y‖ ≤ 1 := by
      have h := (sq_le_one_iff_abs_le_one ‖WithLp.toLp 2 y‖).mp hle1
      rwa [abs_of_nonneg (norm_nonneg _)] at h
    exact hnorm_le
  have hpre : (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))
      (WithLp.toLp 2 ⁻¹' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)) =
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m)))
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    (PiLp.volume_preserving_toLp (Fin m)).measure_preimage
      (measurableSet_closedBall (x := (0 : EuclideanSpace ℝ (Fin m))) (ε := 1)).nullMeasurableSet
  have hmono : (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))
        (Set.pi Set.univ (fun _ : Fin m => Set.Icc (-r) r)) ≤
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m)))
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) := by
    calc (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))
            (Set.pi Set.univ (fun _ : Fin m => Set.Icc (-r) r))
        ≤ (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))
            (WithLp.toLp 2 ⁻¹' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
          MeasureTheory.measure_mono hsub
      _ = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m)))
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) := hpre
  have hle : ENNReal.ofReal ((2*r)^m) ≤
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m)))
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) := by
    rw [← hvolC]; exact hmono
  have hfin : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m)))
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) ≠ ⊤ :=
    (MeasureTheory.measure_closedBall_lt_top (μ := MeasureTheory.volume)
      (x := (0 : EuclideanSpace ℝ (Fin m))) (r := 1)).ne
  have htoReal := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_ofReal (pow_nonneg (by linarith [hrpos] : (0:ℝ) ≤ 2*r) m)] at htoReal
  have hr2 : 2 * r = 2 / Real.sqrt m := by rw [hr, mul_one_div]
  simpa [hr2] using htoReal

end Commons.Analysis.InnerProductSpace
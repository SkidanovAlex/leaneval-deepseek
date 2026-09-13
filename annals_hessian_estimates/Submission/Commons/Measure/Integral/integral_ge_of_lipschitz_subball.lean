import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace Commons.Measure.Integral

open MeasureTheory Metric
open scoped ENNReal

/-- The ratio of the Lebesgue volumes of two balls in `EuclideanSpace ℝ (Fin n)`. -/
private theorem volume_ball_toReal_ratio {n : ℕ} {x₀ y : EuclideanSpace ℝ (Fin n)} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    (MeasureTheory.volume (Metric.ball y s)).toReal
      = (s / r) ^ n * (MeasureTheory.volume (Metric.ball x₀ r)).toReal := by
  have hvol : ∀ (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 < t →
      MeasureTheory.volume (Metric.ball x t)
        = ENNReal.ofReal (t ^ n) *
          MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    intro x t ht
    rw [MeasureTheory.Measure.addHaar_ball_of_pos MeasureTheory.volume x ht,
        finrank_euclideanSpace, Fintype.card_fin]
  have hnum : (MeasureTheory.volume (Metric.ball y s)).toReal
      = s ^ n * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
    rw [hvol y s hs, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hs.le n)]
  have hden : (MeasureTheory.volume (Metric.ball x₀ r)).toReal
      = r ^ n * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
    rw [hvol x₀ r hr, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le n)]
  rw [hnum, hden, ← mul_assoc, ← mul_pow, div_mul_cancel₀ s (ne_of_gt hr)]

/-- If `h` is `K`-Lipschitz on the ball `ball x₀ r`, and `y ∈ ball x₀ (r/2)`, then over a
sub-ball `ball y s` (with `s ≤ r/2` and `s K ≤ |h y|/2`) the function `|h|` is at least `|h y|/2`,
so the average of `|h|` over `ball x₀ r` is at least `(|h y|/2) * (s/r)^n`. -/
theorem integral_ge_of_lipschitz_subball {n : ℕ} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ y : EuclideanSpace ℝ (Fin n)} {r s K : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r / 2)
    (hy : y ∈ Metric.ball x₀ (r / 2))
    (hK : 0 ≤ K)
    (hlip : ∀ z ∈ Metric.closedBall x₀ r, ∀ w ∈ Metric.closedBall x₀ r,
        |h z - h w| ≤ K * dist z w)
    (hsK : s * K ≤ |h y| / 2) :
    (|h y| / 2) * (s / r) ^ n
      ≤ (∫ z in Metric.ball x₀ r, |h z|)
          / (MeasureTheory.volume (Metric.ball x₀ r)).toReal := by
  classical
  set B := Metric.ball x₀ r with hB
  set C := Metric.ball y s with hC
  set A := |h y| / 2 with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  -- `y ∈ closedBall x₀ r`
  have hyB : y ∈ Metric.closedBall x₀ r := by
    rw [Metric.mem_closedBall]
    have h := hy
    rw [Metric.mem_ball] at h
    linarith
  -- `C ⊆ B`
  have hCB : C ⊆ B := by
    intro z hz
    rw [hC, Metric.mem_ball] at hz
    rw [hB, Metric.mem_ball]
    have hzy : dist z y < s := hz
    have hyx : dist y x₀ < r / 2 := by
      have h := hy; rw [Metric.mem_ball] at h; exact h
    calc dist z x₀ ≤ dist z y + dist y x₀ := dist_triangle _ _ _
      _ < s + r / 2 := add_lt_add hzy hyx
      _ ≤ r / 2 + r / 2 := by linarith
      _ = r := by ring
  have hz_closed : ∀ z ∈ C, z ∈ Metric.closedBall x₀ r :=
    fun z hz => Metric.ball_subset_closedBall (hCB hz)
  -- continuity of `h` on `closedBall x₀ r`
  have hcont : ContinuousOn h (Metric.closedBall x₀ r) := by
    have hLip : LipschitzOnWith (Real.toNNReal K) h (Metric.closedBall x₀ r) :=
      LipschitzOnWith.of_dist_le_mul fun z hz w hw => by
        rw [Real.dist_eq, Real.coe_toNNReal K hK]
        exact hlip z hz w hw
    exact hLip.continuousOn
  -- a.e.-strong measurability of `|h|` on `B`
  have haesm : AEStronglyMeasurable (fun z => |h z|) (MeasureTheory.volume.restrict B) := by
    have h2 : AEStronglyMeasurable h (MeasureTheory.volume.restrict B) :=
      hcont.aestronglyMeasurable_of_subset_isCompact (isCompact_closedBall x₀ r)
        measurableSet_ball Metric.ball_subset_closedBall
    simpa only [Real.norm_eq_abs] using h2.norm
  -- bound on `|h|` on `B`
  have hbound : ∀ z ∈ B, |h z| ≤ |h x₀| + K * r := by
    intro z hz
    have hzr : z ∈ Metric.closedBall x₀ r := Metric.ball_subset_closedBall hz
    have hx0 : x₀ ∈ Metric.closedBall x₀ r := by
      rw [Metric.mem_closedBall, dist_self]; exact hr.le
    have hdist : dist z x₀ < r := by rw [hB] at hz; rwa [Metric.mem_ball] at hz
    have h2 : |h z - h x₀| ≤ K * r := by
      calc |h z - h x₀| ≤ K * dist z x₀ := hlip z hzr x₀ hx0
        _ ≤ K * r := mul_le_mul_of_nonneg_left (le_of_lt hdist) hK
    have h3 : |h z| ≤ |h x₀| + |h z - h x₀| := by
      calc |h z| = |h x₀ + (h z - h x₀)| := by rw [show h x₀ + (h z - h x₀) = h z by ring]
        _ ≤ |h x₀| + |h z - h x₀| := abs_add_le _ _
    linarith
  -- finiteness / positivity of the volume of `B`
  have hBfin : MeasureTheory.volume B < ∞ :=
    lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall x₀ r).measure_lt_top
  have hVpos : 0 < (MeasureTheory.volume B).toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨Metric.measure_ball_pos MeasureTheory.volume x₀ hr, hBfin⟩
  -- integrability of `|h|` on `B`
  have hIntB : IntegrableOn (fun z => |h z|) B MeasureTheory.volume := by
    refine IntegrableOn.of_bound hBfin haesm (|h x₀| + K * r) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_ball] with z hz
    simpa only [Real.norm_eq_abs, abs_abs] using hbound z hz
  -- `C` has finite measure; integrability on `C`
  have hCfin : MeasureTheory.volume C < ∞ :=
    lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall y s).measure_lt_top
  have hIntC : IntegrableOn (fun z => |h z|) C MeasureTheory.volume := hIntB.mono_set hCB
  have hIntCconst :
      IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => A) C MeasureTheory.volume := by
    refine IntegrableOn.of_bound hCfin aestronglyMeasurable_const A ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg hA0]
  -- pointwise lower bound on `C`
  have hpt : ∀ z ∈ C, A ≤ |h z| := by
    intro z hz
    have hzr : z ∈ Metric.closedBall x₀ r := hz_closed z hz
    have hzy : dist z y < s := by rw [hC] at hz; rwa [Metric.mem_ball] at hz
    have h2 : |h z - h y| ≤ |h y| / 2 := by
      have h1 : |h z - h y| ≤ K * dist z y := hlip z hzr y hyB
      have h3 : K * dist z y ≤ K * s := mul_le_mul_of_nonneg_left (le_of_lt hzy) hK
      have h4 : K * s = s * K := by ring
      linarith [hsK, hA]
    have h3 : |h y| ≤ |h z - h y| + |h z| := by
      calc |h y| = |(h y - h z) + h z| :=
            by rw [show (h y - h z) + h z = h y by ring]
        _ ≤ |h y - h z| + |h z| := abs_add_le _ _
        _ = |h z - h y| + |h z| := by rw [abs_sub_comm]
    linarith [h2, h3, hA]
  -- integral comparisons
  have hmono : (∫ z in C, |h z|) ≤ ∫ z in B, |h z| :=
    setIntegral_mono_set hIntB (Filter.Eventually.of_forall fun z => abs_nonneg (h z))
      (Filter.Eventually.of_forall fun z hz => hCB hz)
  have hconst : (∫ z in C, A) ≤ ∫ z in C, |h z| :=
    setIntegral_mono_on hIntCconst hIntC measurableSet_ball (fun z hz => hpt z hz)
  have hval : (∫ z in C, A) = (MeasureTheory.volume C).toReal * A := by
    rw [setIntegral_const, measureReal_def, smul_eq_mul]
  have hratio : (MeasureTheory.volume C).toReal
      = (s / r) ^ n * (MeasureTheory.volume B).toReal :=
    volume_ball_toReal_ratio (x₀ := x₀) (y := y) (r := r) (s := s) hr hs
  rw [le_div_iff₀ hVpos]
  calc A * (s / r) ^ n * (MeasureTheory.volume B).toReal
      = A * ((s / r) ^ n * (MeasureTheory.volume B).toReal) := by ring
    _ = A * (MeasureTheory.volume C).toReal := by rw [hratio]
    _ = (MeasureTheory.volume C).toReal * A := by ring
    _ = ∫ z in C, A := hval.symm
    _ ≤ ∫ z in C, |h z| := hconst
    _ ≤ ∫ z in B, |h z| := hmono

end Commons.Measure.Integral
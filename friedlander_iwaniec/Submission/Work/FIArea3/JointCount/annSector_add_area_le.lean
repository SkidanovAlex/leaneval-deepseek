import Mathlib
import Submission.Work.FIArea3.JointCount.sharp_defs
import Submission.Work.FIArea3.JointCount.polarBand_volume
import Submission.Work.FIArea3.JointCount.diam_annSector_le
import Submission.Work.FIArea3.JointCount.threshold_le
import Submission.Work.FIArea3.JointCount.convexHull_add_parallelogram_le
import Submission.Work.FIArea3.JointCount.annSector_add_ball_volume_le
import Submission.Work.FIArea3.JointCount.convexHull_annSector_gap_le

namespace Work.FIArea3.JointCount

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Vocabulary for the geometric bound -/

/-- The closed segment from `0` to `z`. -/
def segm (z : ℂ) : Set ℂ := {w : ℂ | ∃ t ∈ Set.Icc (0 : ℝ) 1, w = t • z}

/-- The measure of the projection of `K` onto the direction `u`: for `u` a unit vector this is
the width of `K` in the direction `u`. -/
def pwidth (K : Set ℂ) (u : ℂ) : ℝ :=
  (MeasureTheory.volume ((fun w : ℂ => w.re * u.re + w.im * u.im) '' K)).toReal

/-! ## The parallelogram of the basis is contained in the ball of radius `(|g₁|+|g₂|)/2` -/

theorem Llc_image_uCell_subset_closedBall (g₁ g₂ : ℂ) :
    Llc g₁ g₂ '' uCell ⊆ Metric.closedBall (0 : ℂ) ((‖g₁‖ + ‖g₂‖) / 2) := by
  intro f hf
  rw [Set.mem_image] at hf
  obtain ⟨q, hq, rfl⟩ := hf
  have hq' := (mem_uCell q).mp hq
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  rw [Llc_apply]
  calc ‖q.re • g₁ + q.im • g₂‖ ≤ ‖q.re • g₁‖ + ‖q.im • g₂‖ := norm_add_le _ _
    _ = |q.re| * ‖g₁‖ + |q.im| * ‖g₂‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (1 / 2) * ‖g₁‖ + (1 / 2) * ‖g₂‖ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right
            (abs_le.mpr ⟨by linarith [hq'.1], by linarith [hq'.2.1]⟩) (norm_nonneg _)
        · exact mul_le_mul_of_nonneg_right
            (abs_le.mpr ⟨by linarith [hq'.2.2.1], by linarith [hq'.2.2.2]⟩) (norm_nonneg _)
    _ = (‖g₁‖ + ‖g₂‖) / 2 := by ring

/-! ## The volume of the annulus sector is at most `π (θ a)²` -/

theorem annSector_volume_le (a θ φ : ℝ) (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (MeasureTheory.volume (annSector a (a * Real.sqrt (1 + θ)) φ (2 * Real.pi * θ))).toReal
      ≤ Real.pi * (θ * a) ^ 2 := by
  set b : ℝ := a * Real.sqrt (1 + θ) with hb
  have hb' : a ≤ b := by
    rw [hb]
    have h1 : (1:ℝ) ≤ Real.sqrt (1 + θ) := Real.one_le_sqrt.mpr (by linarith)
    nlinarith [ha.le]
  have hsq : b ^ 2 = a ^ 2 * (1 + θ) := by
    rw [hb, mul_pow, Real.sq_sqrt (by linarith)]
  have hmain := polarBand_volume a b (Set.Ioc φ (φ + 2 * Real.pi * θ)) ha.le hb' measurableSet_Ioc
  have hR : annSector a b φ (2 * Real.pi * θ)
      = {z : ℂ | a < ‖z‖ ∧ ‖z‖ ≤ b ∧ Complex.arg z ∈ Set.Ioc φ (φ + 2 * Real.pi * θ)} := by
    ext z; simp [annSector, Set.mem_Ioc, and_assoc]
  have hY : (MeasureTheory.volume (Set.Ioc φ (φ + 2 * Real.pi * θ)
      ∩ Set.Ioo (-Real.pi) Real.pi)).toReal ≤ 2 * Real.pi * θ := by
    have h1 : MeasureTheory.volume (Set.Ioc φ (φ + 2 * Real.pi * θ)
        ∩ Set.Ioo (-Real.pi) Real.pi) ≤ ENNReal.ofReal (2 * Real.pi * θ) := by
      calc _ ≤ MeasureTheory.volume (Set.Ioc φ (φ + 2 * Real.pi * θ)) :=
            measure_mono Set.inter_subset_left
        _ = ENNReal.ofReal (2 * Real.pi * θ) := by rw [Real.volume_Ioc]; ring_nf
    calc _ ≤ (ENNReal.ofReal (2 * Real.pi * θ)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      _ = 2 * Real.pi * θ := ENNReal.toReal_ofReal (by positivity)
  have hna : (0:ℝ) ≤ (b ^ 2 - a ^ 2) / 2 := by rw [hsq]; nlinarith [ha.le, hθ0]
  rw [hR, hmain, ENNReal.toReal_ofReal (mul_nonneg hna ENNReal.toReal_nonneg)]
  calc (b ^ 2 - a ^ 2) / 2
        * (MeasureTheory.volume (Set.Ioc φ (φ + 2 * Real.pi * θ)
            ∩ Set.Ioo (-Real.pi) Real.pi)).toReal
      ≤ (b ^ 2 - a ^ 2) / 2 * (2 * Real.pi * θ) := mul_le_mul_of_nonneg_left hY hna
    _ = Real.pi * (θ * a) ^ 2 := by rw [hsq]; ring

/-! ## The main theorem -/

theorem annSector_add_area_le (a θ φ : ℝ) (g₁ g₂ : ℂ) (c : ℝ)
    (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hc0 : 0 ≤ c) (hdet : |g₁.re * g₂.im - g₁.im * g₂.re| = c) :
    (MeasureTheory.volume (Set.image2 (· + ·)
        (Work.FIArea3.JointCount.annSector a (a * Real.sqrt (1 + θ)) φ (2 * Real.pi * θ))
        (Work.FIArea3.JointCount.Llc g₁ g₂ '' Work.FIArea3.JointCount.uCell))).toReal
      ≤ Real.pi * (θ * a) ^ 2 + 16 * (θ * a) * (‖g₁‖ + ‖g₂‖) + c := by
  set R : Set ℂ := annSector a (a * Real.sqrt (1 + θ)) φ (2 * Real.pi * θ) with hRdef
  set r : ℝ := (‖g₁‖ + ‖g₂‖) / 2 with hrdef
  have hbR : R ⊆ Metric.closedBall (0 : ℂ) (a * Real.sqrt (1 + θ)) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hz.2.1
  have hbR0 : 0 ≤ a * Real.sqrt (1 + θ) := by positivity
  by_cases hcase : r ≤ min a (1.2 * θ * a)
  · -- Disc regime
    have hr0 : 0 ≤ r := by rw [hrdef]; positivity
    have hr1 : r ≤ a := le_trans hcase (min_le_left _ _)
    have hr2 : r ≤ 1.2 * θ * a := le_trans hcase (min_le_right _ _)
    have hFsub : Llc g₁ g₂ '' uCell ⊆ Metric.closedBall (0 : ℂ) r := by
      rw [hrdef]; exact Llc_image_uCell_subset_closedBall g₁ g₂
    have hfin : MeasureTheory.volume (Set.image2 (· + ·) R (Metric.closedBall (0 : ℂ) r)) ≠ ⊤ := by
      have hsub : Set.image2 (· + ·) R (Metric.closedBall (0 : ℂ) r)
          ⊆ Metric.closedBall (0 : ℂ) (a * Real.sqrt (1 + θ) + r) := by
        rintro x ⟨u, hu, v, hv, rfl⟩
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hv ⊢
        have hu' := hbR hu
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hu'
        calc ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le _ _
          _ ≤ a * Real.sqrt (1 + θ) + r := add_le_add hu' hv
      refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
      rw [Complex.volume_closedBall]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.coe_ne_top
    calc (MeasureTheory.volume (Set.image2 (· + ·) R (Llc g₁ g₂ '' uCell))).toReal
        ≤ (MeasureTheory.volume (Set.image2 (· + ·) R (Metric.closedBall (0 : ℂ) r))).toReal :=
          ENNReal.toReal_mono hfin (measure_mono (Set.image2_subset_left (f := fun x y : ℂ => x + y) hFsub))
      _ ≤ Real.pi * (θ * a) ^ 2 + 32 * (θ * a) * r :=
          annSector_add_ball_volume_le a θ φ r ha hθ0 hθ1 hr0 hr1 hr2
      _ = Real.pi * (θ * a) ^ 2 + 16 * (θ * a) * (‖g₁‖ + ‖g₂‖) := by rw [hrdef]; ring
      _ ≤ Real.pi * (θ * a) ^ 2 + 16 * (θ * a) * (‖g₁‖ + ‖g₂‖) + c := by linarith
  · -- Convex-hull regime
    push_neg at hcase
    have hthr := threshold_le a θ ha hθ0 hθ1
    have hconv := convexHull_add_parallelogram_le a θ φ g₁ g₂ ha hθ0 hθ1
    have hgap := convexHull_annSector_gap_le a θ φ ha hθ0 hθ1
    have hvol := annSector_volume_le a θ φ ha hθ0 hθ1
    have hthr' : a * min ((2 * Real.pi * θ) ^ 3 / 6) (2 * Real.pi * θ + 1 + θ) ≤ 32 * θ * r := by
      have h1 : a * min ((2 * Real.pi * θ) ^ 3 / 6) (2 * Real.pi * θ + 1 + θ) / (32 * θ)
          ≤ r := le_trans hthr hcase.le
      rcases eq_or_lt_of_le hθ0 with hθ | hθ
      · rw [← hθ] at h1 ⊢
        norm_num at h1 ⊢
      · have h2 := (div_le_iff₀ (by positivity : (0:ℝ) < 32 * θ)).mp h1
        linarith
    have hgap' : (a ^ 2 / 2) * min ((2 * Real.pi * θ) ^ 3 / 6) (2 * Real.pi * θ + 1 + θ)
        ≤ 16 * (θ * a) * r := by
      have h3 : a * (a * min ((2 * Real.pi * θ) ^ 3 / 6) (2 * Real.pi * θ + 1 + θ))
          ≤ a * (32 * θ * r) := mul_le_mul_of_nonneg_left hthr' ha.le
      nlinarith [h3, ha.le]
    calc (MeasureTheory.volume (Set.image2 (· + ·) R (Llc g₁ g₂ '' uCell))).toReal
        ≤ (MeasureTheory.volume (convexHull ℝ R)).toReal
            + 8 * θ * a * (‖g₁‖ + ‖g₂‖) + |g₁.re * g₂.im - g₁.im * g₂.re| := hconv
      _ ≤ ((MeasureTheory.volume R).toReal
            + (a ^ 2 / 2) * min ((2 * Real.pi * θ) ^ 3 / 6) (2 * Real.pi * θ + 1 + θ))
            + 8 * θ * a * (‖g₁‖ + ‖g₂‖) + c := by
          rw [hdet]; linarith [hgap]
      _ ≤ (Real.pi * (θ * a) ^ 2 + (a ^ 2 / 2) * min ((2 * Real.pi * θ) ^ 3 / 6)
              (2 * Real.pi * θ + 1 + θ))
            + 8 * θ * a * (‖g₁‖ + ‖g₂‖) + c := by linarith [hvol]
      _ ≤ Real.pi * (θ * a) ^ 2 + 16 * (θ * a) * r + 8 * θ * a * (‖g₁‖ + ‖g₂‖) + c := by
          linarith [hgap']
      _ = Real.pi * (θ * a) ^ 2 + 16 * (θ * a) * (‖g₁‖ + ‖g₂‖) + c := by rw [hrdef]; ring

end

end Work.FIArea3.JointCount

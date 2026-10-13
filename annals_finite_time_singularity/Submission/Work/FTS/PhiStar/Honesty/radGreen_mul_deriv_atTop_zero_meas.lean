import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Honesty.radGreen_sq_mul_self_atTop_zero
import Submission.Work.FTS.EllExist.Honesty.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.radGreen_branch_pointwise
import Submission.Work.FTS.PhiStar.Honesty.rgHonest_aemeas
import Submission.Work.FTS.PhiStar.Honesty.radGreen_zderiv_honest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The definitional identity `radGreen = rgK (rgG1 + rgG2)`. -/
private lemma radGreen_eq_rgK_mul (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m c z
      = Work.FTS.EllExist.rgK α m
        * (Work.FTS.EllExist.rgG1 α m c z + Work.FTS.EllExist.rgG2 α m c z) := by
  rw [Work.FTS.EllExist.radGreen_eq]
  simp only [Work.FTS.EllExist.rgG1, Work.FTS.EllExist.rgG2]

theorem radGreen_mul_deriv_atTop_zero_meas {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    Filter.Tendsto (fun z : ℝ => z * Work.FTS.PhiStar.Radial.radGreen α m c z
        * (z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z)) Filter.atTop (nhds 0) := by
  obtain ⟨hA1, hA2, hB⟩ := rgHonest_aemeas hα hα4 hm hc hnear hfar
  have hZderiv : ∀ z : ℝ, 2 ≤ z → z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
      = Work.FTS.EllExist.rgK α m * (Work.FTS.EllExist.rgP α m * Work.FTS.EllExist.rgG2 α m c z
          - Work.FTS.EllExist.rgQ α m * Work.FTS.EllExist.rgG1 α m c z) :=
    radGreen_zderiv_honest hα hα4 hm hfar hA1 hA2 hB
  obtain ⟨b1, b2, hb1, hb2, ht1, ht2⟩ := radGreen_branch_pointwise hα hα4 hm hnear hfar
  -- pointwise identity at every `z ≥ 2`
  have hkey : ∀ z : ℝ, 2 ≤ z →
      z * Work.FTS.PhiStar.Radial.radGreen α m c z
        * (z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z)
      = (Work.FTS.EllExist.rgK α m) ^ 2
        * (Work.FTS.EllExist.rgP α m * (z * Work.FTS.EllExist.rgG2 α m c z ^ 2)
          - Work.FTS.EllExist.rgQ α m * (z * Work.FTS.EllExist.rgG1 α m c z ^ 2)
          + (Work.FTS.EllExist.rgP α m - Work.FTS.EllExist.rgQ α m)
            * (z * Work.FTS.EllExist.rgG1 α m c z * Work.FTS.EllExist.rgG2 α m c z)) := by
    intro z hz
    rw [hZderiv z hz, radGreen_eq_rgK_mul]
    ring
  -- the dominating function, made nonnegative
  have hbound : ∀ z : ℝ, 2 ≤ z →
      ‖z * Work.FTS.PhiStar.Radial.radGreen α m c z
        * (z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z)‖
      ≤ (Work.FTS.EllExist.rgK α m) ^ 2
        * (|Work.FTS.EllExist.rgP α m| * max (b2 z) 0
          + |Work.FTS.EllExist.rgQ α m| * max (b1 z) 0
          + |Work.FTS.EllExist.rgP α m - Work.FTS.EllExist.rgQ α m|
            * Real.sqrt (max (b1 z) 0) * Real.sqrt (max (b2 z) 0)) := by
    intro z hz
    have hz1 : 1 ≤ z := by linarith
    have hz0 : (0 : ℝ) ≤ z := by linarith
    rw [hkey z hz, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sq_nonneg (Work.FTS.EllExist.rgK α m))]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg (Work.FTS.EllExist.rgK α m))
    have hu1 : 0 ≤ z * Work.FTS.EllExist.rgG1 α m c z ^ 2 := by positivity
    have hu2 : 0 ≤ z * Work.FTS.EllExist.rgG2 α m c z ^ 2 := by positivity
    have h1 : |Work.FTS.EllExist.rgP α m * (z * Work.FTS.EllExist.rgG2 α m c z ^ 2)|
        ≤ |Work.FTS.EllExist.rgP α m| * max (b2 z) 0 := by
      rw [abs_mul, abs_of_nonneg hu2]
      exact mul_le_mul_of_nonneg_left (le_trans (hb2 z hz1) (le_max_left _ _)) (abs_nonneg _)
    have h2 : |Work.FTS.EllExist.rgQ α m * (z * Work.FTS.EllExist.rgG1 α m c z ^ 2)|
        ≤ |Work.FTS.EllExist.rgQ α m| * max (b1 z) 0 := by
      rw [abs_mul, abs_of_nonneg hu1]
      exact mul_le_mul_of_nonneg_left (le_trans (hb1 z hz1) (le_max_left _ _)) (abs_nonneg _)
    have hw : |z * Work.FTS.EllExist.rgG1 α m c z * Work.FTS.EllExist.rgG2 α m c z|
        ≤ Real.sqrt (max (b1 z) 0) * Real.sqrt (max (b2 z) 0) := by
      have huv : (z * Work.FTS.EllExist.rgG1 α m c z * Work.FTS.EllExist.rgG2 α m c z) ^ 2
          = (z * Work.FTS.EllExist.rgG1 α m c z ^ 2)
            * (z * Work.FTS.EllExist.rgG2 α m c z ^ 2) := by ring
      calc |z * Work.FTS.EllExist.rgG1 α m c z * Work.FTS.EllExist.rgG2 α m c z|
          = Real.sqrt ((z * Work.FTS.EllExist.rgG1 α m c z
              * Work.FTS.EllExist.rgG2 α m c z) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ = Real.sqrt ((z * Work.FTS.EllExist.rgG1 α m c z ^ 2)
              * (z * Work.FTS.EllExist.rgG2 α m c z ^ 2)) := by rw [huv]
        _ = Real.sqrt (z * Work.FTS.EllExist.rgG1 α m c z ^ 2)
              * Real.sqrt (z * Work.FTS.EllExist.rgG2 α m c z ^ 2) := Real.sqrt_mul hu1 _
        _ ≤ Real.sqrt (max (b1 z) 0) * Real.sqrt (max (b2 z) 0) :=
            mul_le_mul (Real.sqrt_le_sqrt (le_trans (hb1 z hz1) (le_max_left _ _)))
              (Real.sqrt_le_sqrt (le_trans (hb2 z hz1) (le_max_left _ _)))
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h3 : |(Work.FTS.EllExist.rgP α m - Work.FTS.EllExist.rgQ α m)
        * (z * Work.FTS.EllExist.rgG1 α m c z * Work.FTS.EllExist.rgG2 α m c z)|
        ≤ |Work.FTS.EllExist.rgP α m - Work.FTS.EllExist.rgQ α m|
          * Real.sqrt (max (b1 z) 0) * Real.sqrt (max (b2 z) 0) := by
      calc |(Work.FTS.EllExist.rgP α m - Work.FTS.EllExist.rgQ α m)
            * (z * Work.FTS.EllExist.rgG1 α m c z * Work.FTS.EllExist.rgG2 α m c z)|
          = |Work.FTS.EllExist.rgP α m - Work.FTS.EllExist.rgQ α m|
            * |z * Work.FTS.EllExist.rgG1 α m c z * Work.FTS.EllExist.rgG2 α m c z| :=
            abs_mul _ _
        _ ≤ |Work.FTS.EllExist.rgP α m - Work.FTS.EllExist.rgQ α m|
            * (Real.sqrt (max (b1 z) 0) * Real.sqrt (max (b2 z) 0)) :=
            mul_le_mul_of_nonneg_left hw
              (abs_nonneg (Work.FTS.EllExist.rgP α m - Work.FTS.EllExist.rgQ α m))
        _ = |Work.FTS.EllExist.rgP α m - Work.FTS.EllExist.rgQ α m|
            * Real.sqrt (max (b1 z) 0) * Real.sqrt (max (b2 z) 0) := by ring
    have hA := abs_add_le (Work.FTS.EllExist.rgP α m * (z * Work.FTS.EllExist.rgG2 α m c z ^ 2)
        - Work.FTS.EllExist.rgQ α m * (z * Work.FTS.EllExist.rgG1 α m c z ^ 2))
      ((Work.FTS.EllExist.rgP α m - Work.FTS.EllExist.rgQ α m)
        * (z * Work.FTS.EllExist.rgG1 α m c z * Work.FTS.EllExist.rgG2 α m c z))
    have hB : |Work.FTS.EllExist.rgP α m * (z * Work.FTS.EllExist.rgG2 α m c z ^ 2)
        - Work.FTS.EllExist.rgQ α m * (z * Work.FTS.EllExist.rgG1 α m c z ^ 2)|
        ≤ |Work.FTS.EllExist.rgP α m * (z * Work.FTS.EllExist.rgG2 α m c z ^ 2)|
          + |Work.FTS.EllExist.rgQ α m * (z * Work.FTS.EllExist.rgG1 α m c z ^ 2)| := by
      have h := abs_add_le (Work.FTS.EllExist.rgP α m * (z * Work.FTS.EllExist.rgG2 α m c z ^ 2))
        (-(Work.FTS.EllExist.rgQ α m * (z * Work.FTS.EllExist.rgG1 α m c z ^ 2)))
      rw [abs_neg] at h
      rwa [sub_eq_add_neg]
    linarith
  -- the dominating function tends to `0`
  have htB1 : Tendsto (fun z : ℝ => max (b1 z) 0) atTop (nhds 0) := by
    have h := ht1.max (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0))
    simpa using h
  have htB2 : Tendsto (fun z : ℝ => max (b2 z) 0) atTop (nhds 0) := by
    have h := ht2.max (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0))
    simpa using h
  have htS1 : Tendsto (fun z : ℝ => Real.sqrt (max (b1 z) 0)) atTop (nhds 0) := by
    simpa [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp htB1)
  have htS2 : Tendsto (fun z : ℝ => Real.sqrt (max (b2 z) 0)) atTop (nhds 0) := by
    simpa [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp htB2)
  have hlim : Tendsto (fun z : ℝ => (Work.FTS.EllExist.rgK α m) ^ 2
      * (|Work.FTS.EllExist.rgP α m| * max (b2 z) 0
        + |Work.FTS.EllExist.rgQ α m| * max (b1 z) 0
        + |Work.FTS.EllExist.rgP α m - Work.FTS.EllExist.rgQ α m|
          * Real.sqrt (max (b1 z) 0) * Real.sqrt (max (b2 z) 0))) atTop (nhds 0) := by
    have h1 : Tendsto (fun z : ℝ => |Work.FTS.EllExist.rgP α m| * max (b2 z) 0)
        atTop (nhds 0) := by
      simpa using htB2.const_mul |Work.FTS.EllExist.rgP α m|
    have h2 : Tendsto (fun z : ℝ => |Work.FTS.EllExist.rgQ α m| * max (b1 z) 0)
        atTop (nhds 0) := by
      simpa using htB1.const_mul |Work.FTS.EllExist.rgQ α m|
    have h3 : Tendsto (fun z : ℝ => |Work.FTS.EllExist.rgP α m - Work.FTS.EllExist.rgQ α m|
        * Real.sqrt (max (b1 z) 0) * Real.sqrt (max (b2 z) 0)) atTop (nhds 0) := by
      have h := (htS1.mul htS2).const_mul
        |Work.FTS.EllExist.rgP α m - Work.FTS.EllExist.rgQ α m|
      simpa [mul_assoc] using h
    have h4 : Tendsto (fun z : ℝ => (|Work.FTS.EllExist.rgP α m| * max (b2 z) 0
        + |Work.FTS.EllExist.rgQ α m| * max (b1 z) 0)
        + |Work.FTS.EllExist.rgP α m - Work.FTS.EllExist.rgQ α m|
          * Real.sqrt (max (b1 z) 0) * Real.sqrt (max (b2 z) 0)) atTop (nhds 0) := by
      simpa using (h1.add h2).add h3
    have h5 := h4.const_mul ((Work.FTS.EllExist.rgK α m) ^ 2)
    simpa using h5
  exact squeeze_zero_norm' (f := fun z : ℝ => z * Work.FTS.PhiStar.Radial.radGreen α m c z
      * (z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z))
    (a := fun z : ℝ => (Work.FTS.EllExist.rgK α m) ^ 2
      * (|Work.FTS.EllExist.rgP α m| * max (b2 z) 0
        + |Work.FTS.EllExist.rgQ α m| * max (b1 z) 0
        + |Work.FTS.EllExist.rgP α m - Work.FTS.EllExist.rgQ α m|
          * Real.sqrt (max (b1 z) 0) * Real.sqrt (max (b2 z) 0)))
    (by filter_upwards [eventually_ge_atTop (2 : ℝ)] with z hz; exact hbound z hz) hlim

end Work.FTS.PhiStar.Honesty

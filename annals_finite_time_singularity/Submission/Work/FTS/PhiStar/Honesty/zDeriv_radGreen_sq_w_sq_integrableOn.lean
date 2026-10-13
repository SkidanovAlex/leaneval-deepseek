/-
# `Work.FTS.PhiStar.Honesty.zDeriv_radGreen_sq_w_sq_integrableOn`

Weighted `L²`-honesty of the *first `z`-derivative* of the mode-`m` radial Green function:

  `∫_0^∞ (z · ∂_z radGreen α m c z)² · w(z)² dz < ∞`,   `w(z) = (1+z)²/z²`,

under the same weak (a.e.-measurability only) hypotheses as the order-`0` statement
`Work.FTS.PhiStar.Honesty.radGreen_sq_w_sq_integrableOn`, namely
`AEMeasurable c`, `∫_0^1 c²/t⁴ < ∞` and `∫_1^∞ c² < ∞`.

Route: the two `c`-terms of the branch relations `z ∂_z rgG1 = -q·rgG1 + c` and
`z ∂_z rgG2 = p·rgG2 - c` cancel to first order (`z * ∂_z radGreen = rgK·(p·rgG2 - q·rgG1)` a.e.),
so that

  `(z ∂_z radGreen z)² w(z)² ≤ 16·rgK²·(2p²·rgG2² + 2q²·rgG1²)·(1/z⁴ on (0,1), 1 on (1,∞))`,

and the four weighted square integrability statements for the two branches
(`rgG1_sq_div_z4_Ioo`, `rgG2_sq_div_z4_Ioo`, `rgG1_sq_Ioi`, `rgG2_sq_Ioi`) close the estimate.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.zDerivAux
import Submission.Work.FTS.PhiStar.Honesty.zDerivAux2
import Submission.Work.FTS.PhiStar.Honesty.rgG1_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Honesty.rgG1_sq_Ioi
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_Ioi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open Work.FTS.EllExist

namespace Work.FTS.PhiStar.Honesty

set_option maxHeartbeats 3200000

/-- `(1+z)^4 ≤ 16` on `(0,1)`. -/
private lemma one_add_pow_four_le {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    (1 + z) ^ 4 ≤ 16 := by
  have h0 : (0 : ℝ) ≤ 1 + z := by linarith
  have h1 : 1 + z ≤ 2 := by linarith
  calc (1 + z) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 h1 4
    _ = 16 := by norm_num

/-- `(1+z)^4 ≤ 16·z^4` for `z ≥ 1`. -/
private lemma one_add_pow_four_le_mul {z : ℝ} (hz1 : 1 ≤ z) :
    (1 + z) ^ 4 ≤ 16 * z ^ 4 := by
  have h0 : (0 : ℝ) ≤ 1 + z := by linarith
  have h1 : 1 + z ≤ 2 * z := by linarith
  calc (1 + z) ^ 4 ≤ (2 * z) ^ 4 := pow_le_pow_left₀ h0 h1 4
    _ = 16 * z ^ 4 := by ring

/-- The weight identity `(w z)² = (1+z)⁴/z⁴`. -/
private lemma w_sq_eq (z : ℝ) : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
  rw [Work.Spaces.w, div_pow]
  rw [show ((1 + z) ^ 2) ^ 2 = (1 + z) ^ 4 by ring, show (z ^ 2) ^ 2 = z ^ 4 by ring]

/-- `(a - b)² ≤ 2a² + 2b²`. -/
private lemma sq_sub_le (a b : ℝ) : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a + b)]

theorem zDeriv_radGreen_sq_w_sq_integrableOn {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hae := zg_ae_zderiv_radGreen hα hα4 hm hc hnear hfar
  have hG1n := rgG1_sq_div_z4_Ioo (α := α) (m := m) (c := c) hα hα4 hm hc hnear hfar
  have hG2n := rgG2_sq_div_z4_Ioo (α := α) (m := m) (c := c) hα hα4 hm hc hnear hfar
  have hG1f := rgG1_sq_Ioi (α := α) (m := m) (c := c) hα hα4 hm hc hnear hfar
  have hG2f := rgG2_sq_Ioi (α := α) (m := m) (c := c) hα hα4 hm hc hnear hfar
  -- continuity of `w²` on `(0,∞)`
  have hwcont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have h : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
      funext z
      rw [Work.Spaces.w]
    rw [h]
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.div ?_ ?_ ?_
    · exact ((continuous_const.add continuous_id).pow 2).continuousOn
    · exact (continuous_id.pow 2).continuousOn
    · intro z hz
      exact pow_ne_zero 2 (ne_of_gt hz)
  have hderiv_meas : Measurable (fun z : ℝ =>
      (z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) ^ 2) :=
    (measurable_id.mul (measurable_deriv _)).pow_const 2
  -- the near piece
  have hnear_int : MeasureTheory.IntegrableOn
      (fun z : ℝ => (z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioo 0 1) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun z : ℝ => 16 * (rgK α m) ^ 2 *
          (2 * (rgP α m) ^ 2 * ((rgG2 α m c z) ^ 2 / z ^ 4)
            + 2 * (rgQ α m) ^ 2 * ((rgG1 α m c z) ^ 2 / z ^ 4))) (Set.Ioo 0 1) :=
      (((hG2n.const_mul (2 * (rgP α m) ^ 2)).add
        (hG1n.const_mul (2 * (rgQ α m) ^ 2))).const_mul (16 * (rgK α m) ^ 2))
    refine Integrable.mono' hdom ?_ ?_
    · have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
          (volume.restrict (Set.Ioo 0 1)) :=
        (hwcont.mono (fun z hz => hz.1)).aestronglyMeasurable measurableSet_Ioo
      exact (hderiv_meas.aestronglyMeasurable.mul hw)
    · filter_upwards [hae.filter_mono (ae_mono Measure.restrict_le_self),
        ae_restrict_mem measurableSet_Ioo] with z hzid hzmem
      have hz0 : (0 : ℝ) < z := hzmem.1
      have hz1 : z ≤ 1 := hzmem.2.le
      rw [hzid hz0, Real.norm_of_nonneg (by positivity)]
      have hwle : (Work.Spaces.w z) ^ 2 ≤ 16 / z ^ 4 := by
        rw [w_sq_eq z]
        gcongr
        exact one_add_pow_four_le hz0 hz1
      have hsq : (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z) ^ 2
          ≤ 2 * (rgP α m * rgG2 α m c z) ^ 2 + 2 * (rgQ α m * rgG1 α m c z) ^ 2 :=
        sq_sub_le _ _
      have hstep : (rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z)) ^ 2
          * (Work.Spaces.w z) ^ 2
          ≤ (rgK α m) ^ 2 * (2 * (rgP α m * rgG2 α m c z) ^ 2
              + 2 * (rgQ α m * rgG1 α m c z) ^ 2) * (16 / z ^ 4) := by
        rw [mul_pow]
        refine mul_le_mul (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)) hwle (sq_nonneg _) ?_
        positivity
      calc (rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z)) ^ 2
            * (Work.Spaces.w z) ^ 2
          ≤ (rgK α m) ^ 2 * (2 * (rgP α m * rgG2 α m c z) ^ 2
              + 2 * (rgQ α m * rgG1 α m c z) ^ 2) * (16 / z ^ 4) := hstep
        _ = 16 * (rgK α m) ^ 2 *
              (2 * (rgP α m) ^ 2 * ((rgG2 α m c z) ^ 2 / z ^ 4)
                + 2 * (rgQ α m) ^ 2 * ((rgG1 α m c z) ^ 2 / z ^ 4)) := by ring
  -- the far piece
  have hfar_int : MeasureTheory.IntegrableOn
      (fun z : ℝ => (z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioi 1) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun z : ℝ => 16 * (rgK α m) ^ 2 *
          (2 * (rgP α m) ^ 2 * (rgG2 α m c z) ^ 2
            + 2 * (rgQ α m) ^ 2 * (rgG1 α m c z) ^ 2)) (Set.Ioi 1) :=
      (((hG2f.const_mul (2 * (rgP α m) ^ 2)).add
        (hG1f.const_mul (2 * (rgQ α m) ^ 2))).const_mul (16 * (rgK α m) ^ 2))
    refine Integrable.mono' hdom ?_ ?_
    · have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
          (volume.restrict (Set.Ioi 1)) :=
        (hwcont.mono (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))).aestronglyMeasurable measurableSet_Ioi
      exact (hderiv_meas.aestronglyMeasurable.mul hw)
    · filter_upwards [hae.filter_mono (ae_mono Measure.restrict_le_self),
        ae_restrict_mem measurableSet_Ioi] with z hzid hzmem
      have hz1 : (1 : ℝ) ≤ z := hzmem.le
      have hz0 : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz1
      rw [hzid hz0, Real.norm_of_nonneg (by positivity)]
      have hwle : (Work.Spaces.w z) ^ 2 ≤ 16 := by
        rw [w_sq_eq z, div_le_iff₀ (by positivity)]
        exact one_add_pow_four_le_mul hz1
      have hsq : (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z) ^ 2
          ≤ 2 * (rgP α m * rgG2 α m c z) ^ 2 + 2 * (rgQ α m * rgG1 α m c z) ^ 2 :=
        sq_sub_le _ _
      have hstep : (rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z)) ^ 2
          * (Work.Spaces.w z) ^ 2
          ≤ (rgK α m) ^ 2 * (2 * (rgP α m * rgG2 α m c z) ^ 2
              + 2 * (rgQ α m * rgG1 α m c z) ^ 2) * 16 := by
        rw [mul_pow]
        refine mul_le_mul (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)) hwle (sq_nonneg _) ?_
        positivity
      calc (rgK α m * (rgP α m * rgG2 α m c z - rgQ α m * rgG1 α m c z)) ^ 2
            * (Work.Spaces.w z) ^ 2
          ≤ (rgK α m) ^ 2 * (2 * (rgP α m * rgG2 α m c z) ^ 2
              + 2 * (rgQ α m * rgG1 α m c z) ^ 2) * 16 := hstep
        _ = 16 * (rgK α m) ^ 2 *
              (2 * (rgP α m) ^ 2 * (rgG2 α m c z) ^ 2
                + 2 * (rgQ α m) ^ 2 * (rgG1 α m c z) ^ 2) := by ring
  -- glue `(0,1)` and `(1,∞)`
  have hA : MeasureTheory.IntegrableOn
      (fun z : ℝ => (z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Icc (0 : ℝ) 1) :=
    hnear_int.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc).symm
  have hB : MeasureTheory.IntegrableOn
      (fun z : ℝ => (z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ici (1 : ℝ)) :=
    hfar_int.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici).symm
  have hU := hA.union hB
  have hset : Set.Icc (0 : ℝ) 1 ∪ Set.Ici (1 : ℝ) = Set.Ici 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro (⟨h1, _⟩ | h3) <;> linarith
    · intro h
      rcases le_or_gt x 1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr h'.le
  rw [hset] at hU
  exact hU.mono_set Set.Ioi_subset_Ici_self

end Work.FTS.PhiStar.Honesty

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.integrableAbsOfSqSeta
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.SliceLocal

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- On the open quadrant `(0, π/2)` the angular operator `Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u`
is continuous as soon as `u` is of class `C²` there (the `tan` singularity is excluded because
`cos θ ≠ 0` on the open quadrant). -/
theorem continuousOn_Lzero1_of_contDiffOn_two (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (Work.FTS.EllipticEst.Lzero1 u) (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hk : ContDiffAt ℝ 2 u θ := hu.contDiffAt (hU.mem_nhds hθ)
  have hdu : ContDiffAt ℝ 1 (fun s => deriv u s) θ := hk.derivWithin (m := 1) (by norm_num)
  have hddu : ContDiffAt ℝ 0 (fun t => deriv (fun s => deriv u s) t) θ :=
    hdu.derivWithin (m := 0) (by norm_num)
  have htan : ContDiffAt ℝ 2 Real.tan θ := (Real.contDiffAt_tan (n := 2)).mpr hcos
  have hmul : ContDiffAt ℝ 2 (fun s => Real.tan s * u s) θ := htan.mul hk
  have hA : ContDiffAt ℝ 0 (fun t => deriv (fun s => Real.tan s * u s) t) θ :=
    hmul.derivWithin (m := 0) (by norm_num)
  have hB : ContDiffAt ℝ 0 (fun t => (6 : ℝ) * u t) θ :=
    (contDiffAt_const (c := (6 : ℝ))).mul (hk.of_le (by norm_num))
  have hsum : ContDiffAt ℝ 0
      (fun t => -deriv (fun s => deriv u s) t + deriv (fun s => Real.tan s * u s) t
        - 6 * u t) θ := (hddu.neg.add hA).sub hB
  exact hsum.continuousAt.continuousWithinAt

/-- **Integrability of the slice pairing against `sin θ cos²θ`.**  If `u` is of class `C²` on the
open quadrant and the weighted square of its angular operator is integrable on
`Iθ = [0, π/2]`, then `θ ↦ sin θ cos²θ · Lzero1 u θ` is integrable there.

Indeed `|sin θ cos²θ| ≤ 1` on `Iθ`, so the claim follows from the integrability of `|Lzero1 u|`,
which is `Work.FTS.EllipticEst.integrableAbsOfSqSeta` applied to the continuity of `Lzero1 u`
on the open quadrant. -/
theorem integrableOn_sinCos2_Lzero1 (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hF : MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun σ => Real.sin σ * (Real.cos σ) ^ 2 * Work.FTS.EllipticEst.Lzero1 u σ)
      Work.Spaces.Iθ := by
  have hcont : ContinuousOn (Work.FTS.EllipticEst.Lzero1 u) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_Lzero1_of_contDiffOn_two u hu
  -- the absolute value of the operator is integrable on the closed quadrant
  have hb : MeasureTheory.IntegrableOn (fun θ => |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.integrableAbsOfSqSeta hcont hF
  -- the two endpoints form a null set: the restricted measures agree
  have hms : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine MeasureTheory.Measure.restrict_congr_set ?_
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2)).symm
  -- almost everywhere strong measurability of the operator and of the product
  have hbasm : AEStronglyMeasurable (Work.FTS.EllipticEst.Lzero1 u)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [hms]
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  have haasm : AEStronglyMeasurable (fun σ : ℝ => Real.sin σ * (Real.cos σ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn.aestronglyMeasurable
      measurableSet_Icc
  have hfasm : AEStronglyMeasurable
      (fun σ => Real.sin σ * (Real.cos σ) ^ 2 * Work.FTS.EllipticEst.Lzero1 u σ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := haasm.mul hbasm
  -- the pointwise domination and the conclusion
  refine MeasureTheory.Integrable.mono' hb hfasm ?_
  filter_upwards with σ
  have h1 : |Real.sin σ| ≤ 1 := Real.abs_sin_le_one σ
  have h2 : |(Real.cos σ) ^ 2| ≤ 1 := by
    rw [abs_pow]
    nlinarith [Real.abs_cos_le_one σ, abs_nonneg (Real.cos σ)]
  have key : |Real.sin σ * (Real.cos σ) ^ 2 * Work.FTS.EllipticEst.Lzero1 u σ|
      = |Real.sin σ| * |(Real.cos σ) ^ 2| * |Work.FTS.EllipticEst.Lzero1 u σ| := by
    rw [abs_mul, abs_mul]
  rw [Real.norm_eq_abs, key]
  calc |Real.sin σ| * |(Real.cos σ) ^ 2| * |Work.FTS.EllipticEst.Lzero1 u σ|
      ≤ 1 * 1 * |Work.FTS.EllipticEst.Lzero1 u σ| := by gcongr
    _ = |Work.FTS.EllipticEst.Lzero1 u σ| := by ring

end Work.FTS.EllipticEst.SliceLocal

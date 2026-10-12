import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BlockBound4.DiagWF
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators
open Submission BoseGases

namespace Work.BlockBound4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-- **Integrability of `K^F·N̂` on the exterior** `d1Ext c₀ = {2c₀ ≤ ‖q‖}`: dominated by the
exterior majorant of `diagKF_le_ext` (the sharp weight `ℬ²/F` and the quartic `d1QuartF`). -/
lemma integrableOn_diagKF_ext {s c0 av M : ℝ} (hs : 0 < s) (hc0 : 0 < c0) (hav : 0 < av)
    (hM : 0 ≤ M) {W : ℝ³ → ℝ} (hWmeas : Measurable (d1Bcoef W))
    (hWb : ∀ q : ℝ³, |d1Bcoef W q| ≤ 16 * Real.pi * av)
    (hInt : MeasureTheory.Integrable (fun q : ℝ³ => (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2)) :
    IntegrableOn (fun q : ℝ³ => diagKF s c0 av M W q * M) (d1Ext c0) volume := by
  have hsharp : Integrable (fun q : ℝ³ => (d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖)
      ((volume : Measure ℝ³).restrict (d1Ext c0)) :=
    integrableOn_sharp_weight hc0 hWmeas hInt
  have hquart : Integrable (d1QuartF s c0 av M W) ((volume : Measure ℝ³).restrict (d1Ext c0)) :=
    integrableOn_d1QuartF hs hc0 hav hM hWmeas hWb
  have hg : Integrable (fun q : ℝ³ =>
      (((M + 1) / (4 * s ^ 3)) * ((d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖)
        + d1QuartF s c0 av M W q) * M) ((volume : Measure ℝ³).restrict (d1Ext c0)) :=
    MeasureTheory.Integrable.mul_const
      (MeasureTheory.Integrable.add
        (MeasureTheory.Integrable.const_mul hsharp ((M + 1) / (4 * s ^ 3))) hquart) M
  refine Integrable.mono' hg ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    have hAcont : Continuous (fun q : ℝ³ => diagAF s c0 av M q) := by
      unfold diagAF fsKinCoeff
      fun_prop
    have hB : Measurable (fun q : ℝ³ => d1Bcoef W q) := hWmeas
    unfold diagKF
    exact ((hAcont.measurable.sub
      (((hAcont.measurable.pow_const 2).sub (hB.pow_const 2)).sqrt)).div_const 2).mul_const M
  · filter_upwards [ae_restrict_mem (measurableSet_d1Ext c0)] with q hq
    have hq' : 2 * c0 ≤ ‖q‖ := hq
    have hqeq : d1QuartF s c0 av M W q
        = ((M + 1) ^ 3 / (4 * s ^ 9)) * ((d1Bcoef W q) ^ 4 / (fsKinCoeff c0 ‖q‖) ^ 3) := by
      unfold d1QuartF
      ring
    have hle : diagKF s c0 av M W q
        ≤ ((M + 1) / (4 * s ^ 3)) * ((d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖)
          + d1QuartF s c0 av M W q := by
      rw [hqeq]
      exact diagKF_le_ext (c0 := c0) hs hM hav hc0 hWb hq'
    rw [Real.norm_of_nonneg (mul_nonneg (diagKF_nonneg (c0 := c0) hs hM hav hWb q) hM)]
    exact mul_le_mul_of_nonneg_right hle hM

/-- Faithful main-term bookkeeping.  Suggested route: split `∫ q, diagKF s c0 av M W q * M`
into the exterior `d1Ext c0` and the interior `d1Int c0` (disjoint, union `Set.univ`;
use `MeasureTheory.setIntegral_union` with `IntegrableOn (fun q => diagKF ... q * M) (d1Int c0)`,
which is `DiagWF.integrableOn_diagKF_int`).  On the exterior use the pointwise
`DiagWF.diagKF_le_ext` (multiplied by `M ≥ 0`) and the integrabilities
`Submission.BoseGases.integrableOn_sharp_weight` (`ℬ²/F` on `d1Ext`) and
`DiagWF.integrableOn_d1QuartF`, then `hpB` and `hqE`; on the interior use
`DiagWF.diagKF_le_int_const` and `hCi` (the constant function is integrable on the finite-measure
ball `d1Int c0`).  Finally pull the `M` and the `(2π)⁻³` out. -/
theorem diag_main_term_le_sharp {s c0 av M : ℝ} (hs : 0 < s) (hc0 : 0 < c0) (hav : 0 < av)
    (hM : 0 ≤ M) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWmeas : Measurable (d1Bcoef W))
    (hWb : ∀ q : EuclideanSpace ℝ (Fin 3), |d1Bcoef W q| ≤ 16 * Real.pi * av)
    (hInt : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
        (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2))
    {Clog QE Ci : ℝ}
    (hpB : (∫ q in d1Ext c0,
        (d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖)
      ≤ (1 + 6 * c0 * av) * (∫ q, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) + Clog)
    (hqE : (∫ q in d1Ext c0,
        Work.BlockBound4.d1QuartF s c0 av M W q) ≤ QE)
    (hCi : (∫ q in d1Int c0,
        (2 * Real.pi * av + Real.pi / 2 * av)) ≤ Ci) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ q, Work.BlockBound4.diagKF s c0 av M W q * M
      ≤ M * ((2 * Real.pi) ^ 3)⁻¹ * (((M + 1) / (4 * s ^ 3))
            * ((1 + 6 * c0 * av) * (∫ q, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) + Clog)
          + QE + Ci) := by
  have hA1 : (0 : ℝ) ≤ (M + 1) / (4 * s ^ 3) := by positivity
  have hKext : IntegrableOn (fun q : ℝ³ => diagKF s c0 av M W q * M) (d1Ext c0) volume :=
    integrableOn_diagKF_ext hs hc0 hav hM hWmeas hWb hInt
  have hKint : IntegrableOn (fun q : ℝ³ => diagKF s c0 av M W q * M) (d1Int c0) volume :=
    integrableOn_diagKF_int hs hc0 hav hM hWmeas hWb
  have hdisj : Disjoint (d1Ext c0) (d1Int c0) := by
    rw [Set.disjoint_left]
    intro q hq1 hq2
    simp only [d1Ext, Set.mem_setOf_eq] at hq1
    rw [d1Int, Metric.mem_ball, dist_eq_norm, sub_zero] at hq2
    linarith
  have hun : d1Ext c0 ∪ d1Int c0 = Set.univ := by
    rw [Set.union_comm]; exact d1Int_union_d1Ext c0
  have hsplit : (∫ q, diagKF s c0 av M W q * M)
      = (∫ q in d1Ext c0, diagKF s c0 av M W q * M)
        + (∫ q in d1Int c0, diagKF s c0 av M W q * M) := by
    have h := setIntegral_union (s := d1Ext c0) (t := d1Int c0) hdisj
      (measurableSet_d1Int c0) hKext hKint
    rw [hun, setIntegral_univ] at h
    exact h
  have hext : (∫ q in d1Ext c0, diagKF s c0 av M W q * M)
      ≤ M * (((M + 1) / (4 * s ^ 3))
            * ((1 + 6 * c0 * av) * (∫ q, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) + Clog) + QE) := by
    have hsharp : Integrable (fun q : ℝ³ => (d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖)
        ((volume : Measure ℝ³).restrict (d1Ext c0)) :=
      integrableOn_sharp_weight hc0 hWmeas hInt
    have hquart : Integrable (d1QuartF s c0 av M W) ((volume : Measure ℝ³).restrict (d1Ext c0)) :=
      integrableOn_d1QuartF hs hc0 hav hM hWmeas hWb
    have hAB : Integrable (fun q : ℝ³ => ((M + 1) / (4 * s ^ 3))
        * ((d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖)) ((volume : Measure ℝ³).restrict (d1Ext c0)) :=
      MeasureTheory.Integrable.const_mul hsharp _
    have hg : Integrable (fun q : ℝ³ => (((M + 1) / (4 * s ^ 3))
        * ((d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖) + d1QuartF s c0 av M W q) * M)
        ((volume : Measure ℝ³).restrict (d1Ext c0)) :=
      MeasureTheory.Integrable.mul_const (MeasureTheory.Integrable.add hAB hquart) M
    have hmono : (∫ q in d1Ext c0, diagKF s c0 av M W q * M)
        ≤ ∫ q in d1Ext c0, (((M + 1) / (4 * s ^ 3))
          * ((d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖) + d1QuartF s c0 av M W q) * M :=
      setIntegral_mono_of_nonneg (s := d1Ext c0)
        (fun q _ => mul_nonneg (diagKF_nonneg (c0 := c0) hs hM hav hWb q) hM)
        (fun q hq => by
          have hq' : 2 * c0 ≤ ‖q‖ := hq
          have hqeq : d1QuartF s c0 av M W q
              = ((M + 1) ^ 3 / (4 * s ^ 9)) * ((d1Bcoef W q) ^ 4 / (fsKinCoeff c0 ‖q‖) ^ 3) := by
            unfold d1QuartF; ring
          rw [hqeq]
          exact mul_le_mul_of_nonneg_right
            (diagKF_le_ext (c0 := c0) hs hM hav hc0 hWb hq') hM)
        hg
    have hgval : (∫ q in d1Ext c0, (((M + 1) / (4 * s ^ 3))
          * ((d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖) + d1QuartF s c0 av M W q) * M)
        = M * (((M + 1) / (4 * s ^ 3))
            * (∫ q in d1Ext c0, (d1Bcoef W q) ^ 2 / fsKinCoeff c0 ‖q‖)
          + (∫ q in d1Ext c0, d1QuartF s c0 av M W q)) := by
      rw [MeasureTheory.integral_mul_const,
          MeasureTheory.integral_add hAB hquart,
          MeasureTheory.integral_const_mul]
      ring
    refine le_trans hmono ?_
    rw [hgval]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hpB hA1) hqE) hM
  have hint : (∫ q in d1Int c0, diagKF s c0 av M W q * M) ≤ M * Ci := by
    haveI : IsFiniteMeasure ((volume : Measure ℝ³).restrict (d1Int c0)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      refine lt_of_le_of_lt (measure_mono ?_)
        (isCompact_closedBall (0 : ℝ³) (2 * c0)).measure_lt_top
      intro q hq
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      rw [d1Int, Metric.mem_ball, dist_eq_norm, sub_zero] at hq
      exact hq.le
    have hcI : Integrable (fun q : ℝ³ => (2 * Real.pi * av + Real.pi / 2 * av) * M)
        ((volume : Measure ℝ³).restrict (d1Int c0)) :=
      MeasureTheory.Integrable.mul_const
        (MeasureTheory.integrable_const (2 * Real.pi * av + Real.pi / 2 * av)) M
    have hmono : (∫ q in d1Int c0, diagKF s c0 av M W q * M)
        ≤ ∫ q in d1Int c0, (2 * Real.pi * av + Real.pi / 2 * av) * M :=
      setIntegral_mono_of_nonneg (s := d1Int c0)
        (fun q _ => mul_nonneg (diagKF_nonneg (c0 := c0) hs hM hav hWb q) hM)
        (fun q _ => mul_le_mul_of_nonneg_right
          (diagKF_le_int_const (c0 := c0) hs hM hav hWb q) hM)
        hcI
    have hval : (∫ q in d1Int c0, (2 * Real.pi * av + Real.pi / 2 * av) * M)
        = (∫ q in d1Int c0, (2 * Real.pi * av + Real.pi / 2 * av)) * M :=
      MeasureTheory.integral_mul_const M (fun _ : ℝ³ => (2 * Real.pi * av + Real.pi / 2 * av))
    refine le_trans hmono ?_
    rw [hval]
    calc (∫ q in d1Int c0, (2 * Real.pi * av + Real.pi / 2 * av)) * M
        ≤ Ci * M := mul_le_mul_of_nonneg_right hCi hM
      _ = M * Ci := by ring
  have hmain : (∫ q, diagKF s c0 av M W q * M)
      ≤ M * (((M + 1) / (4 * s ^ 3))
            * ((1 + 6 * c0 * av) * (∫ q, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) + Clog) + QE + Ci) := by
    rw [hsplit]
    linarith [hext, hint]
  have h2πinv : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
  calc ((2 * Real.pi) ^ 3)⁻¹ * ∫ q, diagKF s c0 av M W q * M
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * (M * (((M + 1) / (4 * s ^ 3))
            * ((1 + 6 * c0 * av) * (∫ q, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) + Clog) + QE + Ci)) :=
          mul_le_mul_of_nonneg_left hmain h2πinv
    _ = M * ((2 * Real.pi) ^ 3)⁻¹ * (((M + 1) / (4 * s ^ 3))
            * ((1 + 6 * c0 * av) * (∫ q, (d1Bcoef W q) ^ 2 / ‖q‖ ^ 2) + Clog) + QE + Ci) := by
          ring

end Work.BlockBound4

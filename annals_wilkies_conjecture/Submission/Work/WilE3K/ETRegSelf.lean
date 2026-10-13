/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): the `ETRegValue` genericity
  input of `Work.WilE3K.ET_good_exists` (independent of the delegated
  `Work.WilE3K.ETReg_bad_null`).

  `¬ E.ETRegValue y` means `∃ z, E.psiMap z = y ∧ E.gLast z = 0 ∧ (E.jac z).det = 0`, i.e. `y` is
  the image under the remaining system of a *critical* point of the square map `E.map` that lies
  on the zero set of the eliminated arctan equation `E.gLast = E.tanFun (Fin.last rt)`.

  The zero set of `E.gLast` is the graph of the chart `E.chart` (`ETRegDefs.lean`), whose domain
  `E.chartDom = {x | -(π/2) < E.ell x ∧ E.ell x < π/2}` is open.  Writing
  `E.chartMap x = E.psiMap (E.chart x)` for the square chart map, the criticality transfer
  `ETData.dmap_det_eq_zero_iff_dG_det` (`ETRegCore.lean`) shows that a critical point of `E.map` on
  the graph is exactly a critical point of `E.chartMap`; consequently

    `{y | ¬ E.ETRegValue y} ⊆ E.chartMap '' {x ∈ E.chartDom | det (fderiv ℝ E.chartMap x) = 0}`,

  and the right-hand side is Lebesgue-null by Sard's lemma for a `C¹` map on an open subset of
  `ℝ^N` (`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`).

  The chart facts proved here are: `E.lin (Fin.last rt) (E.chart x) = E.ell x` (`lin_chart_self`),
  `E.gLast (E.chart x) = 0` on the chart domain (`gLast_chart_self`), the surjectivity of the chart
  onto `{gLast = 0}` (`chart_surj_self`), the differentiability of the chart and of the chart map
  with the explicit derivatives `E.dchart x`, `E.dG x` (`hasFDerivAt_chart_self`,
  `hasFDerivAt_chartMap_self`), and the openness of the chart domain.
-/
import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE3K.ETRegDefs
import Submission.Work.WilE3K.ETRegCore
import Submission.Work.WilE3K.contDiff_map_and_det
import Submission.Work.WilE2.khoReg_bad_null

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {N rt n re : ℕ}

namespace ETData

variable (E : ETData N (rt + 1) n re)

/-! ## §1. The chart -/

/-- `E.ell` is the affine functional `E.dell` plus the constant `E.mu (Fin.last rt)`. -/
theorem ell_eq_dell : E.ell = fun x : Fin N → ℝ => E.dell x + E.mu (Fin.last rt) := by
  funext x
  rw [ETData.ell, E.dell_apply]

theorem continuous_ell_self : Continuous E.ell := by
  rw [E.ell_eq_dell]
  exact E.dell.continuous.add continuous_const

/-- The chart domain is open. -/
theorem isOpen_chartDom_self : IsOpen E.chartDom := by
  have h : E.chartDom = E.ell ⁻¹' Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := rfl
  rw [h]
  exact isOpen_Ioo.preimage E.continuous_ell_self

/-- The free coordinates of the chart point are the free coordinates of `x`. -/
theorem lin_chart_self (x : Fin N → ℝ) : E.lin (Fin.last rt) (E.chart x) = E.ell x := by
  rw [ETData.lin, ETData.ell]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [E.chart_of_ne x (E.freeCoord_ne_lastRow i),
    E.outIdx_freeCoord i (E.freeCoord_ne_lastRow i)]

/-- **The chart parametrises the zero set of the eliminated equation.** -/
theorem gLast_chart_self {x : Fin N → ℝ} (hx : x ∈ E.chartDom) : E.gLast (E.chart x) = 0 := by
  have h1 : E.chart x (E.tanCoord (Fin.last rt)) = Real.tan (E.ell x) := by
    rw [E.tanCoord_last_eq_lastRow, E.chart_lastRow]
  change E.tanFun (Fin.last rt) (E.chart x) = 0
  rw [ETData.tanFun_eq, h1, E.lin_chart_self x, Real.arctan_tan hx.1 hx.2, sub_self]

/-- The linear functional `E.ell` at the chart point of a point `z` is `E.lin (Fin.last rt) z`. -/
theorem ell_chart_surj_self (z : Fin (N + 1) → ℝ) :
    E.ell (fun i => z (E.lastRow.succAbove i)) = E.lin (Fin.last rt) z := by
  rw [ETData.ell, ETData.lin]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [E.succAbove_freeIdx]

/-- **Surjectivity of the chart onto the zero set of the eliminated equation.** -/
theorem chart_surj_self {z : Fin (N + 1) → ℝ} (hz : E.gLast z = 0) :
    ∃ x : Fin N → ℝ, x ∈ E.chartDom ∧ E.chart x = z := by
  have hg : E.lin (Fin.last rt) z = Real.arctan (z E.lastRow) := by
    have h := hz
    change E.tanFun (Fin.last rt) z = 0 at h
    rw [ETData.tanFun_eq, E.tanCoord_last_eq_lastRow] at h
    linarith
  have hell : E.ell (fun i => z (E.lastRow.succAbove i)) = Real.arctan (z E.lastRow) := by
    rw [E.ell_chart_surj_self, hg]
  refine ⟨fun i => z (E.lastRow.succAbove i), ?_, ?_⟩
  · rw [ETData.chartDom]
    exact ⟨by rw [hell]; exact Real.neg_pi_div_two_lt_arctan _,
      by rw [hell]; exact Real.arctan_lt_pi_div_two _⟩
  · funext r
    by_cases hr : r = E.lastRow
    · subst hr
      rw [E.chart_lastRow, hell, Real.tan_arctan]
    · rw [E.chart_of_ne (fun i => z (E.lastRow.succAbove i)) hr, E.succAbove_outIdx r hr]

/-! ## §2. Differentiability of the chart -/

/-- `1 + tan t ^ 2 = 1 / cos t ^ 2` where `cos t ≠ 0`. -/
theorem one_add_tan_sq_self {t : ℝ} (h : Real.cos t ≠ 0) :
    1 + Real.tan t ^ 2 = 1 / Real.cos t ^ 2 := by
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  nlinarith [Real.cos_sq_add_sin_sq t]

/-- **The differential of the chart is the explicit `E.dchart`.** -/
theorem hasFDerivAt_chart_self (x : Fin N → ℝ) (hx : x ∈ E.chartDom) :
    HasFDerivAt E.chart (E.dchart x) x := by
  have hcos : Real.cos (E.ell x) ≠ 0 := (Real.cos_pos_of_mem_Ioo hx).ne'
  have htansq : 1 / Real.cos (E.ell x) ^ 2 = 1 + Real.tan (E.ell x) ^ 2 :=
    (one_add_tan_sq_self hcos).symm
  rw [show E.dchart x = ContinuousLinearMap.pi (fun r : Fin (N + 1) =>
      if h : r = E.lastRow then (1 + Real.tan (E.ell x) ^ 2) • E.dell
      else (ContinuousLinearMap.proj (E.outIdx r h) : (Fin N → ℝ) →L[ℝ] ℝ)) from rfl]
  refine hasFDerivAt_pi.mpr (fun r => ?_)
  by_cases hr : r = E.lastRow
  · subst hr
    rw [dif_pos rfl]
    have hfun : (fun x' : Fin N → ℝ => E.chart x' E.lastRow) = fun x' => Real.tan (E.ell x') := by
      funext x'; rw [E.chart_lastRow]
    rw [hfun]
    have h1 : HasFDerivAt E.ell E.dell x := by
      rw [E.ell_eq_dell]
      exact (E.dell.hasFDerivAt).add_const (E.mu (Fin.last rt))
    have h2 := (Real.hasDerivAt_tan hcos).comp_hasFDerivAt x h1
    exact h2.congr_fderiv (by rw [htansq])
  · rw [dif_neg hr]
    have hfun : (fun x' : Fin N → ℝ => E.chart x' r) = fun x' => x' (E.outIdx r hr) := by
      funext x'; rw [E.chart_of_ne x' hr]
    rw [hfun]
    exact hasFDerivAt_apply (E.outIdx r hr) x

/-- **The differential of the chart map is the explicit `E.dG`.** -/
theorem hasFDerivAt_chartMap_self (x : Fin N → ℝ) (hx : x ∈ E.chartDom) :
    HasFDerivAt E.chartMap (E.dG x) x := by
  let π : (Fin (N + 1) → ℝ) →L[ℝ] (Fin N → ℝ) :=
    ContinuousLinearMap.pi fun i =>
      (ContinuousLinearMap.proj (E.lastRow.succAbove i) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)
  have hchart := E.hasFDerivAt_chart_self x hx
  have hmap := E.map_hasFDerivAt (E.chart x)
  have hcomp : HasFDerivAt (fun x' : Fin N → ℝ => E.map (E.chart x'))
      ((E.dmap (E.chart x)).comp (E.dchart x)) x := hmap.comp x hchart
  have h3 : HasFDerivAt (fun x' : Fin N → ℝ => π (E.map (E.chart x')))
      (π.comp ((E.dmap (E.chart x)).comp (E.dchart x))) x :=
    (ContinuousLinearMap.hasFDerivAt π).comp x hcomp
  have hfun : (fun x' : Fin N → ℝ => π (E.map (E.chart x'))) = E.chartMap := by
    funext x' i
    show (E.map (E.chart x')) (E.lastRow.succAbove i) = (E.psiMap (E.chart x')) i
    rw [E.psiMap_apply]
  rw [hfun] at h3
  refine h3.congr_fderiv ?_
  have hpsi : π.comp ((E.dmap (E.chart x)).comp (E.dchart x))
      = (E.dpsi (E.chart x)).comp (E.dchart x) := by
    ext v i
    simp only [ContinuousLinearMap.comp_apply, π, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.proj_apply, E.dmap_apply, E.dpsi_apply]
  rw [hpsi]
  rfl

/-! ## §3. The bad set is the critical value set of the chart map -/

/-- Every value at which `ETRegValue` fails is a critical value of the chart map. -/
theorem chartMap_bad_subset_self :
    {y : Fin N → ℝ | ¬ E.ETRegValue y} ⊆
      E.chartMap '' {x : Fin N → ℝ | x ∈ E.chartDom ∧ (E.dG x).det = 0} := by
  intro y hy
  simp only [ETData.ETRegValue] at hy
  push_neg at hy
  obtain ⟨z, hzy, hzg, hzj⟩ := hy
  obtain ⟨x, hx, hxz⟩ := E.chart_surj_self hzg
  refine ⟨x, ⟨hx, ?_⟩, ?_⟩
  · rw [← E.dmap_det_eq_zero_iff_dG_det x, hxz, E.dmap_det_eq_jac_det]
    exact hzj
  · rw [ETData.chartMap, hxz, hzy]

/-- **The `ETRegValue` condition fails only on a null set of values.** -/
theorem ETRegBadNull {N rt n re : ℕ} (E : ETData N (rt + 1) n re) :
    MeasureTheory.volume {y : Fin N → ℝ | ¬ E.ETRegValue y} = 0 := by
  have hS : MeasureTheory.volume
      (E.chartMap '' {x : Fin N → ℝ | x ∈ E.chartDom ∧ (E.dG x).det = 0}) = 0 := by
    refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (μ := MeasureTheory.volume)
      (s := {x : Fin N → ℝ | x ∈ E.chartDom ∧ (E.dG x).det = 0})
      (f := E.chartMap) (f' := fun x => E.dG x) ?_ ?_
    · intro x hx
      exact (E.hasFDerivAt_chartMap_self x hx.1).hasFDerivWithinAt
    · intro x hx
      exact hx.2
  exact MeasureTheory.measure_mono_null E.chartMap_bad_subset_self hS

end ETData

end Work.WilE3K

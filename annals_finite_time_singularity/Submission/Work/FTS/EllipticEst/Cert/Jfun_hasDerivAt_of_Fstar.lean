import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.Gsing_ode
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

open MeasureTheory Set Filter
open scoped Topology

theorem Jfun_hasDerivAt_of_Fstar (α : ℝ) (F : ℝ → ℝ → ℝ)
    (hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0))
    (hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0))
    (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  -- the exponent `(5-α)/α` is nonnegative (indeed positive)
  have hcpos : (0 : ℝ) < (5 - α) / α := div_pos (by linarith) hα
  have hcnonneg : (0 : ℝ) ≤ (5 - α) / α := le_of_lt hcpos
  -- `F_*` is continuous on `(0,∞)`, hence so is the integrand
  have hFcont : ContinuousOn (Work.Elliptic.Fstar F) (Set.Ioi (0 : ℝ)) := (hFsm 0).continuousOn
  have hfcontOn : ContinuousOn
      (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) (Set.Ioi (0 : ℝ)) := by
    intro x hx
    exact ((Real.continuous_rpow_const hcnonneg).continuousAt).continuousWithinAt.mul
      (hFcont x hx)
  have hcont : ContinuousAt (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) z :=
    (Real.continuousAt_rpow_const z ((5 - α) / α) (Or.inl (ne_of_gt hzpos))).mul
      (hFcont.continuousAt (isOpen_Ioi.mem_nhds hz))
  have hmeas : StronglyMeasurableAtFilter
      (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) (𝓝 z) MeasureTheory.volume :=
    hfcontOn.stronglyMeasurableAtFilter isOpen_Ioi z hz
  -- integrability of the integrand on the interval `(0,z]`
  have hint : IntegrableOn (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
      (Set.Ioc (0 : ℝ) z) := by
    -- `F_*(x)/x` is integrable on `(0,z]`, hence (a null set apart) on `[0,z]`
    have hgIoc : IntegrableOn (fun x : ℝ => Work.Elliptic.Fstar F x / x) (Set.Ioc (0 : ℝ) z) :=
      hFint.mono_set (fun x hx => hx.1)
    have hIcc : IntegrableOn (fun x : ℝ => Work.Elliptic.Fstar F x / x) (Set.Icc (0 : ℝ) z) :=
      (integrableOn_Icc_iff_integrableOn_Ioc).mpr hgIoc
    -- multiply by the continuous bounded factor `x^((5-α)/α+1) = x^{5/α}`
    have hcont' : ContinuousOn (fun x : ℝ => x ^ ((5 - α) / α + 1)) (Set.Icc (0 : ℝ) z) :=
      (Real.continuous_rpow_const (by linarith)).continuousOn
    have hmul : IntegrableOn
        (fun x : ℝ => (Work.Elliptic.Fstar F x / x) * x ^ ((5 - α) / α + 1))
        (Set.Icc (0 : ℝ) z) := hIcc.mul_continuousOn hcont' isCompact_Icc
    have hmul' : IntegrableOn
        (fun x : ℝ => (Work.Elliptic.Fstar F x / x) * x ^ ((5 - α) / α + 1))
        (Set.Ioc (0 : ℝ) z) := hmul.mono_set Set.Ioc_subset_Icc_self
    refine hmul'.congr_fun ?_ measurableSet_Ioc
    intro x hx
    have hxpos : 0 < x := hx.1
    have hrw : x ^ ((5 - α) / α + 1) = x ^ ((5 - α) / α) * x := by
      rw [Real.rpow_add hxpos, Real.rpow_one]
    show Work.Elliptic.Fstar F x / x * x ^ ((5 - α) / α + 1)
      = x ^ ((5 - α) / α) * Work.Elliptic.Fstar F x
    rw [hrw]
    field_simp
  have hInt : IntervalIntegrable
      (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) MeasureTheory.volume 0 z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hzpos.le).mpr hint
  exact intervalIntegral.integral_hasDerivAt_right hInt hmeas hcont

end Work.FTS.EllipticEst.Cert

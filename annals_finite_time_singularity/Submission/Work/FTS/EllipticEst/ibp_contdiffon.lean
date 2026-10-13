import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory Set

/-- Integration by parts on `[a, b]` for `h` of class `C²` on the interval (`ContDiffOn`) and
`ψ` globally `C²`.  Only the derivative on the *open* interval is required, so `h` need not be
differentiable at the endpoints. -/
theorem ibp_contdiffon {a b : ℝ} (hab : a < b) {h ψ : ℝ → ℝ}
    (hh : ContDiffOn ℝ 2 h (Set.Icc a b)) (hψ : ContDiff ℝ 2 ψ) :
    ∫ x in a..b, deriv h x * ψ x = h b * ψ b - h a * ψ a - ∫ x in a..b, h x * deriv ψ x := by
  have hmin : min a b = a := min_eq_left hab.le
  have hmax : max a b = b := max_eq_right hab.le
  have hIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab.le
  -- continuity on the interval
  have hhcont : ContinuousOn h (Set.uIcc a b) := by
    rw [hIcc]; exact hh.continuousOn
  have hψcont : ContinuousOn ψ (Set.uIcc a b) := hψ.continuous.continuousOn
  -- two-sided derivatives in the interior
  have hhderiv : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt h (deriv h x) x := by
    intro x hx
    rw [hmin, hmax] at hx
    exact (hh.contDiffAt (Icc_mem_nhds hx.1 hx.2)).differentiableAt (by norm_num) |>.hasDerivAt
  have hψderiv : ∀ x ∈ Set.Ioo (min a b) (max a b), HasDerivAt ψ (deriv ψ x) x := by
    intro x _
    exact ((hψ.differentiable (by norm_num)) x).hasDerivAt
  -- integrability of the derivatives
  have hψint : IntervalIntegrable (deriv ψ) volume a b :=
    (hψ.continuous_deriv (by norm_num)).intervalIntegrable a b
  have huniq : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
  have hdwc : ContinuousOn (derivWithin h (Set.Icc a b)) (Set.Icc a b) :=
    hh.continuousOn_derivWithin huniq (by norm_num)
  have hint1 : IntervalIntegrable (derivWithin h (Set.Icc a b)) volume a b :=
    ContinuousOn.intervalIntegrable (by rw [hIcc]; exact hdwc)
  have hint2 : IntervalIntegrable (deriv h) volume a b :=
    hint1.congr_uIoo (by
      intro x hx
      rw [Set.uIoo_of_le hab.le] at hx
      exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2))
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := h) (v := ψ) (u' := deriv h) (v' := deriv ψ)
    hhcont hψcont hhderiv hψderiv hint2 hψint
  linarith [key]

end Work.FTS.EllipticEst

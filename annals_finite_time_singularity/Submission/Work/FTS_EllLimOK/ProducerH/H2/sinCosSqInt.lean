import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS_EllLimOK.ProducerH.H2

theorem sinCosSqInt {F : ℝ → ℝ} {x C : ℝ}
    (hc : ContinuousOn F (Set.Ioo 0 (Real.pi / 2)))
    (hb : ∀ t ∈ Set.Ioo 0 (Real.pi / 2), |F t| ≤ C)
    (hx : 0 < x) (hx2 : x ≤ Real.pi / 2) :
    IntervalIntegrable (fun t => Real.sin t * (Real.cos t) ^ 2 * F t) volume x (Real.pi / 2) := by
  -- The only singular point of the integrand would be the endpoint `π / 2`, where `cos` vanishes;
  -- the (global) factor `cos²` kills it, and the complement of the open interval is null.
  have hsub : Set.Ioo x (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    Set.Ioo_subset_Ioo_left (le_of_lt hx)
  have hcont : ContinuousOn (fun t : ℝ => Real.sin t * (Real.cos t) ^ 2 * F t)
      (Set.Ioo x (Real.pi / 2)) :=
    ((Real.continuous_sin.continuousOn.mul (Real.continuous_cos.continuousOn.pow 2))).mul
      (hc.mono hsub)
  -- It suffices to prove integrability on the open interval `(x, π/2)`.
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hx2]
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioo_lt_top ?_ C ?_
  · exact hcont.aestronglyMeasurable measurableSet_Ioo
  · -- Pointwise bound: `|sin t| ≤ 1`, `|cos t|² ≤ 1`, and `|F t| ≤ C` on the open interval.
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo ?_
    intro t ht
    have ht' : t ∈ Set.Ioo 0 (Real.pi / 2) := hsub ht
    have hFt : |F t| ≤ C := hb t ht'
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    calc |Real.sin t| * |Real.cos t| ^ 2 * |F t|
        ≤ 1 * 1 * |F t| := by
          gcongr
          · exact Real.abs_sin_le_one t
          · exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one t)
      _ = |F t| := by ring
      _ ≤ C := hFt

end Work.FTS_EllLimOK.ProducerH.H2

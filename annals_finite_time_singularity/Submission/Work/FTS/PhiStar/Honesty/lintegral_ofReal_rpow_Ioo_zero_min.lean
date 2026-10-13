import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.PhiStar.Honesty.lintegral_ofReal_rpow_Ioo
import Submission.Work.FTS.PhiStar.Honesty.lintegral_ofReal_rpow_Ioo_left

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

-- Intended file: Submission/Work/FTS/PhiStar/Honesty/lintegral_ofReal_rpow_Ioo_zero_min.lean
-- Intended namespace: Work.FTS.PhiStar.Honesty.
-- Siblings to imitate: Submission/Work/FTS/PhiStar/Honesty/lintegral_ofReal_rpow_Ioo.lean
-- (`∫⁻ z in Ioo 1 t, ofReal (z^p) = ofReal ((t^(p+1)-1)/(p+1))` for `0 < p`, `1 ≤ t`) and
-- `lintegral_ofReal_rpow_Ioo_left.lean` (`∫⁻ z in Ioo t 1, ofReal (z^r)` for `r < -1`).
-- The interval here is `(0,1) ∩ (0,t)` and the exponent satisfies `-1 < r`.
open MeasureTheory Set Filter

/-- For `-1 < r` and any upper endpoint `m > 0`, the `ENNReal`-valued integral of
`z ↦ ofReal (z^r)` over `(0,m)` is exactly the `ofReal` of the Riemann integral
`∫_0^m z^r dz = m^(r+1)/(r+1)`. -/
theorem lintegral_ofReal_rpow_Ioo_zero_end (r m : ℝ) (hr : -1 < r) (hm : 0 < m) :
    (∫⁻ z in Set.Ioo (0 : ℝ) m, ENNReal.ofReal (z ^ r))
      = ENNReal.ofReal (m ^ (r + 1) / (r + 1)) := by
  have hr1 : 0 < r + 1 := by linarith
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [MeasureTheory.restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hm.le]
    rw [integral_rpow (Or.inl hr), Real.zero_rpow hr1.ne']
    ring
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hm.le).mp
      (intervalIntegral.intervalIntegrable_rpow' hr)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact Real.rpow_nonneg hx.1.le r

/-- For `-1 < r` and `t > 0`, the `ENNReal`-valued integral of `z ↦ ofReal (z^r)` over the
interval `(0,1) ∩ (0,t)` is at most `ofReal (t^(r+1)/(r+1))`.  (Equality holds for `t ≤ 1`,
where the interval is `(0,t)`; for `t > 1` the interval is `(0,1)` and the value is
`ofReal (1/(r+1)) ≤ ofReal (t^(r+1)/(r+1))`.) -/
theorem lintegral_ofReal_rpow_Ioo_zero_min {r t : ℝ} (hr : -1 < r) (ht : 0 < t) :
    (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t), ENNReal.ofReal (z ^ r))
      ≤ ENNReal.ofReal (t ^ (r + 1) / (r + 1)) := by
  have hr1 : 0 < r + 1 := by linarith
  have hm : 0 < min (1 : ℝ) t := lt_min zero_lt_one ht
  have hset : Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t = Set.Ioo 0 (min 1 t) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iio]
    exact ⟨fun ⟨⟨h0, h1⟩, ht'⟩ => ⟨h0, lt_min h1 ht'⟩,
      fun ⟨h0, h⟩ => ⟨⟨h0, lt_of_lt_of_le h (min_le_left _ _)⟩,
        lt_of_lt_of_le h (min_le_right _ _)⟩⟩
  rw [hset, lintegral_ofReal_rpow_Ioo_zero_end r (min 1 t) hr hm]
  refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hr1.le)
  exact Real.rpow_le_rpow (le_of_lt hm) (min_le_right _ _) hr1.le

end Work.FTS.PhiStar.Honesty

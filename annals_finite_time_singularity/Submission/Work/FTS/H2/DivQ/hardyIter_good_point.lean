import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS.H2.DivQ

/-- Mean-value "good point" statement: if `u` is continuous on the compact interval `[ε, 2ε]`
(`ε > 0`), nonnegative on `(0,2ε]` and integrable on `(0,2ε]`, then some `y ∈ [ε,2ε]` satisfies
`y·u(y) ≤ 2·∫_{(0,2ε]} u`.

Route: take `y ∈ [ε,2ε]` attaining the minimum of `u` (`IsCompact.exists_isMinOn`); then
`ε·u(y) ≤ ∫_{(ε,2ε]} u` because `∫_{(ε,2ε]}(u - u y) ≥ 0`; finally
`y·u(y) ≤ 2ε·u(y) ≤ 2·∫_{(ε,2ε]} u ≤ 2·∫_{(0,2ε]} u`
(second inequality uses `0 ≤ u y`, the last one monotonicity of the set integral with
`Ioc ε (2ε) ⊆ Ioc 0 (2ε)` and `0 ≤ u` on `(0,2ε]`). -/
theorem hardyIter_good_point {u : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hcont : ContinuousOn u (Set.Icc ε (2 * ε)))
    (hnn : ∀ x ∈ Set.Ioc 0 (2 * ε), 0 ≤ u x)
    (hint : MeasureTheory.IntegrableOn u (Set.Ioc 0 (2 * ε))) :
    ∃ y ∈ Set.Icc ε (2 * ε), y * u y ≤ 2 * ∫ x in Set.Ioc 0 (2 * ε), u x := by
  have hε2 : ε ≤ 2 * ε := by linarith
  -- a point of `[ε,2ε]` where `u` is minimal
  obtain ⟨y, hy, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (⟨ε, le_rfl, hε2⟩ : (Set.Icc ε (2 * ε)).Nonempty) hcont
  have hy0 : 0 < y := lt_of_lt_of_le hε hy.1
  have hyu : 0 ≤ u y := hnn y ⟨hy0, hy.2⟩
  have hmin' : ∀ x ∈ Set.Icc ε (2 * ε), u y ≤ u x := fun x hx => hmin hx
  have hu_int : MeasureTheory.IntegrableOn u (Set.Ioc ε (2 * ε)) :=
    hint.mono_set (fun x hx => ⟨lt_trans hε hx.1, hx.2⟩)
  have hII : IntervalIntegrable u volume ε (2 * ε) :=
    intervalIntegrable_iff.mpr (by rwa [uIoc_of_le hε2])
  -- `ε * u y ≤ ∫_{(ε,2ε]} u`, by monotonicity against the constant `u y`
  have h1 : ∫ x in ε..(2 * ε), (fun _ => u y) x ≤ ∫ x in ε..(2 * ε), u x :=
    intervalIntegral.integral_mono_on hε2 intervalIntegrable_const hII (fun x hx => hmin' x hx)
  have h2 : (∫ x in ε..(2 * ε), (fun _ => u y) x) = ε * u y := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have h3 : (∫ x in ε..(2 * ε), u x) = ∫ x in Set.Ioc ε (2 * ε), u x :=
    intervalIntegral.integral_of_le hε2
  have h4 : ε * u y ≤ ∫ x in Set.Ioc ε (2 * ε), u x := by
    rw [← h2, ← h3]
    exact h1
  -- enlarge the domain `(ε,2ε]` to `(0,2ε]`, using `0 ≤ u` there
  have h5 : ∫ x in Set.Ioc ε (2 * ε), u x ≤ ∫ x in Set.Ioc 0 (2 * ε), u x :=
    setIntegral_mono_set hint (ae_restrict_of_forall_mem measurableSet_Ioc hnn)
      (ae_of_all volume (fun x hx => ⟨lt_trans hε hx.1, hx.2⟩))
  refine ⟨y, hy, ?_⟩
  calc y * u y ≤ (2 * ε) * u y := mul_le_mul_of_nonneg_right hy.2 hyu
    _ = 2 * (ε * u y) := by ring
    _ ≤ 2 * ∫ x in Set.Ioc ε (2 * ε), u x := by linarith
    _ ≤ 2 * ∫ x in Set.Ioc 0 (2 * ε), u x := by linarith

end Work.FTS.H2.DivQ

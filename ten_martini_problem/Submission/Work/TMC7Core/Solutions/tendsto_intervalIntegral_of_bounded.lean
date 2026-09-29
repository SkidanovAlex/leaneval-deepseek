import Mathlib

open MeasureTheory Set

namespace Work.TMC7Core.Solutions

theorem tendsto_intervalIntegral_of_bounded {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {C : ℝ}
    (hF : ∀ k, Continuous (F k)) (hC : 0 ≤ C)
    (hbound : ∀ k x, x ∈ Set.Icc (0 : ℝ) 1 → |F k x| ≤ C)
    (hlim : ∀ x, Filter.Tendsto (fun k => F k x) Filter.atTop (nhds (G x))) :
    Filter.Tendsto (fun k => ∫ x in (0 : ℝ)..1, F k x) Filter.atTop
      (nhds (∫ x in (0 : ℝ)..1, G x)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := 0) (b := 1) (F := F) (f := G) (fun _ => C) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun n => (hF n).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    rw [Real.norm_eq_abs]
    exact hbound n x ⟨le_of_lt hx.1, hx.2⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun x _ => hlim x

end Work.TMC7Core.Solutions

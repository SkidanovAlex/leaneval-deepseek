import Mathlib

namespace Commons.Geometry.Ulam

open MeasureTheory Set Filter
open scoped Topology Interval ContDiff RealInnerProductSpace BigOperators

set_option autoImplicit false

lemma profile_measurable_smooth_general_inf {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf_support : Function.support f ⊆ Set.Icc a b)
    (hf_cont : ContDiffOn ℝ ∞ f (Set.Ioo a b))
    (hf_left : f a = 0) (hf_right : f b = 0) :
    Measurable f := by
  classical
  let s : Set ℝ := Set.Ioo a b
  let g : ℝ → ℝ := s.piecewise f (fun _ => 0)
  have hcont_f : ContinuousOn f s := hf_cont.continuousOn
  have hcont_zero : ContinuousOn (fun _ : ℝ => (0 : ℝ)) sᶜ := continuous_const.continuousOn
  have hg_meas : Measurable g := by
    dsimp [g, s]
    exact ContinuousOn.measurable_piecewise hcont_f hcont_zero measurableSet_Ioo
  have hfg : f = g := by
    ext t
    by_cases ht : t ∈ s
    · simp [g, s, ht]
    · have hzero : f t = 0 := by
        by_cases htc : t ∈ Set.Icc a b
        · have ht1 : a ≤ t := htc.1
          have ht2 : t ≤ b := htc.2
          have hnot : ¬ (a < t ∧ t < b) := by simpa [s] using ht
          have hle_or : t = a ∨ t = b := by
            by_cases hlt : a < t
            · right
              have hnotlt : ¬ t < b := by
                intro h; exact hnot ⟨hlt, h⟩
              exact le_antisymm ht2 (le_of_not_gt hnotlt)
            · left
              exact le_antisymm (le_of_not_gt hlt) ht1
          rcases hle_or with rfl | rfl <;> simp [hf_left, hf_right]
        · by_contra hz
          have hmem : t ∈ Function.support f := by
            simpa [Function.mem_support] using hz
          exact htc (hf_support hmem)
      simp [g, ht, hzero]
  rw [hfg]
  exact hg_meas

end Commons.Geometry.Ulam

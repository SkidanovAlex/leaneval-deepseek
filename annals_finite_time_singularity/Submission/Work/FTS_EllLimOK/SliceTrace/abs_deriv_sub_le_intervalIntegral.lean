import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS_EllLimOK.SliceTrace

theorem abs_deriv_sub_le_intervalIntegral {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    |deriv f b - deriv f a| ≤ ∫ x in a..b, |deriv (deriv f) x| := by
  -- `[a,b]` sits inside the open interval where `f` is `C²`
  have hsub : Set.uIcc a b ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
    exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  -- `deriv f` is `C¹` on that interval, hence `deriv (deriv f)` is continuous there
  have hc1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    hf.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)
  have hcont : ContinuousOn (deriv (deriv f)) (Set.uIcc a b) := by
    have h0 : ContinuousOn (deriv (deriv f)) (Set.Ioo 0 (Real.pi / 2)) :=
      ((hf.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).deriv_of_isOpen (m := 0)
        isOpen_Ioo (by norm_num)).continuousOn
    exact h0.mono hsub
  have hint : IntervalIntegrable (deriv (deriv f)) volume a b := hcont.intervalIntegrable
  have hdiff : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ (deriv f) x := by
    intro x hx
    exact (hc1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds (hsub hx))
  -- fundamental theorem of calculus for `deriv f`, whose derivative is `deriv (deriv f)`
  have hFTC : ∫ x in a..b, deriv (deriv f) x = deriv f b - deriv f a :=
    intervalIntegral.integral_deriv_eq_sub hdiff hint
  rw [← hFTC]
  exact intervalIntegral.abs_integral_le_integral_abs hab

end Work.FTS_EllLimOK.SliceTrace

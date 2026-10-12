import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Submission.Work.BoseBoxFix.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseGateFS

/-- The cut profile `fu.f` of a `Work.BoseBoxFix.LowCut` is a smooth function which is
constant `1` on `(-∞, 1]` and constant `0` on `[2, ∞)`; hence its derivative vanishes off
the compact window `[1, 2]`, on which it is continuous.  Consequently `deriv fu.f` is
uniformly bounded. -/
theorem LowCut_deriv_bound (fu : Work.BoseBoxFix.LowCut) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, |deriv fu.f s| ≤ M := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((fu.smooth.continuous_deriv (by simp)).continuousOn (s := Set.Icc (1:ℝ) 2))
  refine ⟨max C 0, le_max_right _ _, fun s => ?_⟩
  by_cases hs : s ∈ Set.Icc (1:ℝ) 2
  · exact le_trans (hC s hs) (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
    rcases hs with hs | hs
    · -- `s < 1`: `fu.f` is `1` on a neighbourhood of `s`
      have hconst : fu.f =ᶠ[nhds s] fun _ => (1:ℝ) := by
        refine Filter.eventually_of_mem (isOpen_Iio.mem_nhds hs) ?_
        intro t ht
        exact fu.one t (le_of_lt ht)
      rw [hconst.deriv_eq, deriv_const]
      simp
    · -- `2 < s`: `fu.f` is `0` on a neighbourhood of `s`
      have hconst : fu.f =ᶠ[nhds s] fun _ => (0:ℝ) := by
        refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hs) ?_
        intro t ht
        exact fu.zero t (le_of_lt ht)
      rw [hconst.deriv_eq, deriv_const]
      simp

end Work.BoseGateFS

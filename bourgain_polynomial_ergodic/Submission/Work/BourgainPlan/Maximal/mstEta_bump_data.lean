import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs

namespace Work.BourgainPlan.Maximal

open Filter
open scoped Topology

/-- **Bump data for `η`.**  A `C²` bump `η : ℝ → ℂ` vanishing on `{|x| ≥ 1/2}` admits a single
constant `M > 0` controlling `η`, `|x| η'` and `|x|² η''` simultaneously.

The three functions `x ↦ ‖η x‖`, `x ↦ |x| ‖η' x‖`, `x ↦ |x|² ‖η'' x‖` are continuous on the
compact interval `[-1/2, 1/2]` (using `ContDiff ℝ 2 η`), hence bounded there by
`IsCompact.exists_bound_of_continuousOn`; off `[-1/2, 1/2]` the function `η` is *eventually* zero,
so all its derivatives vanish there (`Filter.EventuallyEq.deriv_eq`,
`Filter.EventuallyEq.iteratedDeriv_eq`). -/
theorem mstEta_bump_data (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    ∃ M : ℝ, 0 < M ∧ (∀ x : ℝ, ‖η x‖ ≤ M) ∧
      (∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M) ∧
      (∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M) := by
  have hI : IsCompact (Set.Icc (-(1/2 : ℝ)) (1/2)) := isCompact_Icc
  have h0c : ContinuousOn η (Set.Icc (-(1/2 : ℝ)) (1/2)) := hηc.continuous.continuousOn
  have h1c : ContinuousOn (fun x : ℝ => |x| * ‖deriv η x‖) (Set.Icc (-(1/2 : ℝ)) (1/2)) :=
    (continuous_abs.mul (hηc.continuous_deriv (by norm_num)).norm).continuousOn
  have h2c : ContinuousOn (fun x : ℝ => |x| ^ 2 * ‖iteratedDeriv 2 η x‖)
      (Set.Icc (-(1/2 : ℝ)) (1/2)) :=
    ((continuous_abs.pow 2).mul (hηc.continuous_iteratedDeriv 2 (by norm_num)).norm).continuousOn
  obtain ⟨C0, hC0⟩ := hI.exists_bound_of_continuousOn h0c
  obtain ⟨C1, hC1⟩ := hI.exists_bound_of_continuousOn h1c
  obtain ⟨C2, hC2⟩ := hI.exists_bound_of_continuousOn h2c
  -- `η` vanishes on a neighbourhood of every point with `|x| > 1/2`
  have hzero_ev : ∀ x : ℝ, 1 / 2 < |x| → η =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℂ)) := by
    intro x hx
    have hev : ∀ᶠ y in 𝓝 x, (1 : ℝ) / 2 < |y| :=
      (isOpen_lt continuous_const continuous_abs).mem_nhds hx
    filter_upwards [hev] with y hy
    exact hηsup y hy.le
  set M : ℝ := max 1 (max |C0| (max |C1| |C2|)) with hMdef
  have hM0 : 0 < M := by
    rw [hMdef]; exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC0le : |C0| ≤ M := by
    rw [hMdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hC1le : |C1| ≤ M := by
    rw [hMdef]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hC2le : |C2| ≤ M := by
    rw [hMdef]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨M, hM0, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : |x| ≤ 1/2
    · have hxmem : x ∈ Set.Icc (-(1/2:ℝ)) (1/2) := by
        rw [Set.mem_Icc]; exact abs_le.mp hx
      exact le_trans (hC0 x hxmem) (le_trans (le_abs_self C0) hC0le)
    · have hx' : (1:ℝ)/2 < |x| := lt_of_not_ge hx
      rw [hηsup x hx'.le, norm_zero]
      exact le_of_lt hM0
  · intro x
    by_cases hx : |x| ≤ 1/2
    · have hxmem : x ∈ Set.Icc (-(1/2:ℝ)) (1/2) := by
        rw [Set.mem_Icc]; exact abs_le.mp hx
      calc |x| * ‖deriv η x‖ ≤ |(|x| * ‖deriv η x‖)| := le_abs_self _
        _ ≤ C1 := hC1 x hxmem
        _ ≤ |C1| := le_abs_self C1
        _ ≤ M := hC1le
    · have hx' : (1:ℝ)/2 < |x| := lt_of_not_ge hx
      have hd : deriv η x = 0 := by
        rw [(hzero_ev x hx').deriv_eq]; simp
      rw [hd, norm_zero, mul_zero]
      exact le_of_lt hM0
  · intro x
    by_cases hx : |x| ≤ 1/2
    · have hxmem : x ∈ Set.Icc (-(1/2:ℝ)) (1/2) := by
        rw [Set.mem_Icc]; exact abs_le.mp hx
      calc |x| ^ 2 * ‖iteratedDeriv 2 η x‖
            ≤ |(|x| ^ 2 * ‖iteratedDeriv 2 η x‖)| := le_abs_self _
        _ ≤ C2 := hC2 x hxmem
        _ ≤ |C2| := le_abs_self C2
        _ ≤ M := hC2le
    · have hx' : (1:ℝ)/2 < |x| := lt_of_not_ge hx
      have hd : iteratedDeriv 2 η x = 0 := by
        rw [(hzero_ev x hx').iteratedDeriv_eq 2]; simp
      rw [hd, norm_zero, mul_zero]
      exact le_of_lt hM0

end Work.BourgainPlan.Maximal

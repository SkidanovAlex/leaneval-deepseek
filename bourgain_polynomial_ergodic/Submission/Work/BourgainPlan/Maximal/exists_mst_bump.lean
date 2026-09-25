import Mathlib

/-!
# An `M`-bump `η : ℝ → ℂ` with `Mikhlin-type` weighted bounds

We construct a `C²` bump `η : ℝ → ℂ`, equal to `1` on `[-1/4, 1/4]` and supported in `[-1/2, 1/2]`,
together with a single constant `M > 0` bounding `η`, `|x| η'(x)` and `|x|² η''(x)`.

The bump is Mathlib's `ContDiffBump (0 : ℝ)` with inner radius `1/4` and outer radius `1/2`, viewed
in `ℂ`.  The point is the *existence of a common* `M`: since `η` is a fixed smooth compactly
supported function, the continuous functions `x ↦ |x| ‖η'(x)‖` and `x ↦ |x|² ‖η''(x)‖` are bounded
on the compact interval `[-1/2, 1/2]` (by `IsCompact.exists_bound_of_continuousOn`), while off that
interval `η` vanishes on a neighbourhood of every point, so all its derivatives vanish there as
well (`Filter.EventuallyEq.deriv_eq`, `Filter.EventuallyEq.iteratedDeriv_eq`).
-/

namespace Work.BourgainPlan.Maximal

open Filter
open scoped Topology

theorem exists_mst_bump :
    ∃ (η : ℝ → ℂ) (M : ℝ), 0 < M ∧ ContDiff ℝ 2 η ∧ (∀ x : ℝ, ‖η x‖ ≤ M) ∧
      (∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M) ∧
      (∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M) ∧
      (∀ x : ℝ, |x| ≤ 1 / 4 → η x = 1) ∧ (∀ x : ℝ, 1 / 2 < |x| → η x = 0) := by
  let b : ContDiffBump (0 : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩
  let η : ℝ → ℂ := fun x => (b x : ℂ)
  have hbout : b.rOut = 1 / 2 := rfl
  have hbin : b.rIn = 1 / 4 := rfl
  have hzero_ev : ∀ x : ℝ, 1 / 2 < |x| → η =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℂ)) := by
    intro x hx
    have hev : ∀ᶠ y in 𝓝 x, (1 : ℝ) / 2 < |y| :=
      (isOpen_lt continuous_const continuous_abs).mem_nhds hx
    filter_upwards [hev] with y hy
    have hy0 : b y = (0 : ℝ) :=
      b.zero_of_le_dist (by rw [hbout, dist_zero_right, Real.norm_eq_abs]; exact le_of_lt hy)
    change (b y : ℂ) = 0
    rw [hy0]; simp
  have hcont : ContDiff ℝ 2 η := by
    have h : ContDiff ℝ 2 (fun x : ℝ => (b x : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (b.contDiff (n := 2))
    simpa only [η] using h
  have hI : IsCompact (Set.Icc (-(1/2:ℝ)) (1/2)) := isCompact_Icc
  have hg1c : ContinuousOn (fun x : ℝ => |x| * ‖deriv η x‖) (Set.Icc (-(1/2:ℝ)) (1/2)) :=
    (continuous_abs.mul (hcont.continuous_deriv (by norm_num)).norm).continuousOn
  have hg2c : ContinuousOn (fun x : ℝ => |x| ^ 2 * ‖iteratedDeriv 2 η x‖)
      (Set.Icc (-(1/2:ℝ)) (1/2)) :=
    ((continuous_abs.pow 2).mul (hcont.continuous_iteratedDeriv 2 (by norm_num)).norm).continuousOn
  obtain ⟨C1, hC1⟩ := hI.exists_bound_of_continuousOn hg1c
  obtain ⟨C2, hC2⟩ := hI.exists_bound_of_continuousOn hg2c
  refine ⟨η, max 1 (max |C1| |C2|), ?_, hcont, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro x
    calc ‖η x‖ = |b x| := by simp [η]
      _ ≤ 1 := by rw [abs_of_nonneg (b.nonneg (x := x))]; exact b.le_one (x := x)
      _ ≤ max 1 (max |C1| |C2|) := le_max_left _ _
  · intro x
    by_cases hx : |x| ≤ 1 / 2
    · have hxmem : x ∈ Set.Icc (-(1/2:ℝ)) (1/2) := by
        rw [Set.mem_Icc]; constructor <;> linarith [neg_abs_le x, le_abs_self x, hx]
      calc |x| * ‖deriv η x‖ ≤ |(|x| * ‖deriv η x‖)| := le_abs_self _
        _ ≤ C1 := hC1 x hxmem
        _ ≤ |C1| := le_abs_self C1
        _ ≤ max 1 (max |C1| |C2|) := le_trans (le_max_left _ _) (le_max_right _ _)
    · have hx' : (1:ℝ)/2 < |x| := lt_of_not_ge hx
      have hd : deriv η x = 0 := by
        have h := (hzero_ev x hx').deriv_eq
        rw [h]; simp
      rw [hd, norm_zero, mul_zero]
      exact le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  · intro x
    by_cases hx : |x| ≤ 1 / 2
    · have hxmem : x ∈ Set.Icc (-(1/2:ℝ)) (1/2) := by
        rw [Set.mem_Icc]; constructor <;> linarith [neg_abs_le x, le_abs_self x, hx]
      calc |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ |(|x| ^ 2 * ‖iteratedDeriv 2 η x‖)| := le_abs_self _
        _ ≤ C2 := hC2 x hxmem
        _ ≤ |C2| := le_abs_self C2
        _ ≤ max 1 (max |C1| |C2|) := le_trans (le_max_right _ _) (le_max_right _ _)
    · have hx' : (1:ℝ)/2 < |x| := lt_of_not_ge hx
      have hd : iteratedDeriv 2 η x = 0 := by
        have h := (hzero_ev x hx').iteratedDeriv_eq 2
        rw [h]; simp
      rw [hd, norm_zero, mul_zero]
      exact le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  · intro x hx
    change (b x : ℂ) = 1
    have hx' : x ∈ Metric.closedBall (0:ℝ) b.rIn := by
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, hbin]; exact hx
    have h1 := b.one_of_mem_closedBall hx'
    rw [h1]; simp
  · intro x hx
    change (b x : ℂ) = 0
    have hy0 : b x = (0:ℝ) :=
      b.zero_of_le_dist (by rw [hbout, dist_zero_right, Real.norm_eq_abs]; exact le_of_lt hx)
    rw [hy0]; simp

end Work.BourgainPlan.Maximal

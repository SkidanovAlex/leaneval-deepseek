/-
# Smoothness of the periodized bump `arcTileH`

`arcTileH u = Σ'_m arcBump0 (u - m)` is the periodization of the compactly supported smooth bump
`arcBump0` (which equals `1` on `[-3/8,3/8]` and vanishes off `(-3/4,3/4)`).

The series is *locally finite*: for `u` in a fixed neighbourhood of a point `x` only the
finitely many integers `m` with `|u - m| < 3/4` contribute, and those all lie in the fixed window
`Icc (-(N+1)) (N+1)` for any `N` with `|x| ≤ N`.  Hence `arcTileH` agrees near `x` with a finite
sum of translates of the smooth bump, and is therefore smooth.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.arcBumpBasic

set_option autoImplicit false

open scoped BigOperators

namespace Work.KMTAreas.A4

theorem arcTileH_contDiff : ContDiff ℝ (⊤ : ℕ∞) Work.KMTAreas.A4.arcTileH := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨N, hN⟩ := exists_nat_ge |x|
  set s : Finset ℤ := Finset.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1) with hs
  -- Off the window `s` the bump is supported away from any `u` near `x`.
  have key : ∀ (u : ℝ), |u - x| < 1 / 4 → ∀ m : ℤ, m ∉ s → arcBump0 (u - m) = 0 := by
    intro u hu m hm
    have hmI : m < -((N : ℤ) + 1) ∨ ((N : ℤ) + 1) < m := by
      rw [hs, Finset.mem_Icc] at hm
      omega
    have hm2 : (N : ℝ) + 2 ≤ |(m : ℝ)| := by
      rcases hmI with h | h
      · have h1 : ((N : ℤ) + 2) ≤ -m := by omega
        have h2 : (m : ℝ) ≤ 0 := by
          have : m ≤ 0 := by omega
          exact_mod_cast this
        rw [abs_of_nonpos h2]
        exact_mod_cast h1
      · have h1 : ((N : ℤ) + 2) ≤ m := by omega
        have h2 : (0 : ℝ) ≤ (m : ℝ) := by
          have : (0 : ℤ) ≤ m := by omega
          exact_mod_cast this
        rw [abs_of_nonneg h2]
        exact_mod_cast h1
    have huN : |u| < (N : ℝ) + 1 := by
      have h3 : |u| ≤ |x| + |u - x| := by
        calc |u| = |(u - x) + x| := by congr 1; ring
          _ ≤ |u - x| + |x| := abs_add_le (u - x) x
          _ = |x| + |u - x| := by ring
      linarith
    have h4 : |(m : ℝ)| - |u| ≤ |u - m| := by
      have h5 : |(m : ℝ)| - |u| ≤ |(m : ℝ) - u| := abs_sub_abs_le_abs_sub _ _
      rwa [abs_sub_comm] at h5
    exact arcBump0_eq_zero _ (by linarith)
  refine ContDiffAt.congr_of_eventuallyEq (f := fun u => ∑ m ∈ s, arcBump0 (u - m)) ?_ ?_
  · -- a finite sum of smooth translates is smooth
    apply ContDiffAt.sum
    intro m _
    exact (arcBump0_contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
  · -- `arcTileH` equals that finite sum near `x`
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1 / 4)] with u hu
    have hu' : |u - x| < 1 / 4 := by
      rw [Metric.mem_ball, Real.dist_eq] at hu
      simpa [abs_sub_comm] using hu
    show arcTileH u = ∑ m ∈ s, arcBump0 (u - m)
    rw [arcTileH]
    exact tsum_eq_sum (fun m hm => key u hu' m hm)

end Work.KMTAreas.A4

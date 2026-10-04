import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep7

/-- On `ι → ℝ` the (sup) norm is dominated by the Euclidean norm `√(Σ yᵢ²)`.  This is the bridge
between the hypothesis of `rho_lipschitz` (stated with `Σ yᵢ²`) and the sup-norm ball used for
compactness. -/
private lemma norm_le_sqrt_sum_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ‖x‖ ≤ Real.sqrt (∑ i, (x i) ^ 2) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr (fun i => ?_)
  have h1 : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  calc ‖x i‖ = Real.sqrt ((x i) ^ 2) := by rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
    _ ≤ Real.sqrt (∑ j, (x j) ^ 2) := Real.sqrt_le_sqrt h1

/-- **A smooth bump supported in the ball `Σ yᵢ² ≤ 2` is globally Lipschitz.**  Route (do *not* use `‖ρ‖ ≤ 1`, which is not a hypothesis): `hρ0` says `ρ` vanishes outside the closed ball of radius `√2` and `hρs` makes `fderiv ρ` continuous with the same support, so `M := sup over the compact closed ball of radius 3 of ‖fderiv ρ‖` is finite and the mean value inequality `Convex.norm_image_sub_le_of_norm_fderiv_le` (or `Convex.norm_image_sub_le_of_norm_deriv_le_segment` for the `ι → ℝ`-valued case) on the convex ball of radius 3 bounds `‖ρ y − ρ z‖` by `M‖y − z‖` for `y, z` in that ball; for points outside, `ρ` is `0` on the far side (with `Σ yᵢ² > 2`) and the segment argument can be applied on the ball whenever both endpoints are in it. -/
theorem rho_lipschitz {ι : Type*} [Fintype ι] (ρ : (ι → ℝ) → ℝ)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρ0 : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖ := by
  have hcont : Continuous (fderiv ℝ ρ) := hρs.continuous_fderiv (by simp)
  -- `hρ0` is an `L²`-ball condition; the sup-norm ball of radius `√2` is contained in it.
  have hsum2 : ∀ y : ι → ℝ, Real.sqrt 2 < ‖y‖ → 2 < ∑ i, (y i) ^ 2 := by
    intro y hy
    have h1 : (Real.sqrt 2) ^ 2 < ‖y‖ ^ 2 := by
      rw [sq_lt_sq]
      rwa [abs_of_nonneg (Real.sqrt_nonneg 2), abs_of_nonneg (norm_nonneg y)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h1
    have h2 : ‖y‖ ^ 2 ≤ ∑ i, (y i) ^ 2 :=
      (Real.le_sqrt (norm_nonneg y) (Finset.sum_nonneg fun i _ => sq_nonneg (y i))).mp
        (norm_le_sqrt_sum_sq y)
    linarith
  have hzero : ∀ y : ι → ℝ, Real.sqrt 2 < ‖y‖ → ρ y = 0 := fun y hy => hρ0 y (hsum2 y hy)
  -- hence `fderiv ρ` vanishes on the complement of that ball (it is locally `0` there)
  have hfderiv_zero : ∀ y : ι → ℝ, Real.sqrt 2 < ‖y‖ → fderiv ℝ ρ y = 0 := by
    intro y hy
    have hε : 0 < ‖y‖ - Real.sqrt 2 := sub_pos.mpr hy
    have hev : ρ =ᶠ[nhds y] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds y hε] with z hz
      have hd : dist z y < ‖y‖ - Real.sqrt 2 := hz
      have h3 : ‖y‖ - ‖z‖ ≤ dist z y := by
        have h4 := abs_norm_sub_norm_le z y
        have h5 : ‖y‖ - ‖z‖ ≤ |‖z‖ - ‖y‖| := by
          rw [abs_sub_comm]
          exact le_abs_self _
        rw [dist_eq_norm]
        linarith
      exact hzero z (by linarith)
    rw [hev.fderiv_eq]
    simp
  -- `fderiv ρ` is continuous with compact support, so its norm is globally bounded
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ι → ℝ) (2 : ℝ)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hbound : ∀ y : ι → ℝ, ‖fderiv ℝ ρ y‖ ≤ max C 0 := by
    intro y
    by_cases hy : ‖y‖ ≤ Real.sqrt 2
    · refine le_trans (hC y ?_) (le_max_left _ _)
      have : ‖y‖ ≤ 2 := le_trans hy (by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩)
      simpa [Metric.mem_closedBall, dist_eq_norm] using this
    · rw [hfderiv_zero y (lt_of_not_ge hy)]
      simp
  refine ⟨max C 0, le_max_right _ _, fun y z => ?_⟩
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ) (f := ρ) (C := max C 0)
    (fun x _ => (hρs.differentiable (by simp)).differentiableAt) (fun x _ => hbound x)
    convex_univ (Set.mem_univ z) (Set.mem_univ y)

end Work.Diff.STE.B3.SymCalcStep7

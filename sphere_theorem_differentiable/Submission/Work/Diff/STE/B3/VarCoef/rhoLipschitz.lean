import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A smooth bump supported in the Euclidean ball `∑ yᵢ² ≤ 2` is globally Lipschitz

`Work.Diff.STE.B3.VarCoef.rhoLipschitz`: a smooth (indeed `C^∞`) function
`ρ : (ι → ℝ) → ℝ` which vanishes on the complement of the closed Euclidean ball
`{y | ∑ i, (y i) ^ 2 ≤ 2}` is Lipschitz for the sup norm of `ι → ℝ`.

The proof is the standard compact-support argument.

* The bridge between the hypothesis, stated with `∑ i, (y i) ^ 2`, and the sup-norm ball used
  for compactness is `norm_le_sqrt_sum_sq_pi` (on `ι → ℝ` the norm is the sup norm, and it is
  dominated by the Euclidean norm `√(∑ yᵢ²)`), so the *open* sup-norm ball of radius `√2` is
  contained in the zero set of `ρ`.
* Hence `ρ` is locally `0` at every `y` with `‖y‖ > √2`, and therefore `fderiv ℝ ρ y = 0` there.
* `fderiv ℝ ρ` is continuous (`ContDiff.continuous_fderiv`), so `M := max C 0`, where `C` bounds
  `‖fderiv ℝ ρ‖` on the compact closed ball of radius `2` (which contains the whole region where
  the derivative can fail to vanish), is a global bound for `‖fderiv ℝ ρ‖`.
* The mean value inequality on the convex set `Set.univ`
  (`Convex.norm_image_sub_le_of_norm_fderiv_le`) then gives the Lipschitz bound.

This statement was already available in the workspace as
`Work.Diff.STE.B3.SymCalcStep7.rho_lipschitz`; the proof is reproduced here so that this module
is self-contained (it imports only `Mathlib`).
-/

namespace Work.Diff.STE.B3.VarCoef

/-- On `ι → ℝ` (which carries the sup norm) the norm is dominated by the Euclidean norm
`√(Σ yᵢ²)`.  This is the bridge between the hypothesis `2 < Σ yᵢ²` of `rhoLipschitz` and the
sup-norm ball used for compactness. -/
private lemma norm_le_sqrt_sum_sq_pi {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ‖x‖ ≤ Real.sqrt (∑ i, (x i) ^ 2) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr (fun i => ?_)
  have h1 : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  calc ‖x i‖ = Real.sqrt ((x i) ^ 2) := by rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
    _ ≤ Real.sqrt (∑ j, (x j) ^ 2) := Real.sqrt_le_sqrt h1

theorem rhoLipschitz {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρ0 : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖ := by
  have hcont : Continuous (fderiv ℝ ρ) := hρs.continuous_fderiv (by simp)
  -- `hρ0` is an `L²`-ball condition; the strict sup-norm ball of radius `√2` is contained in it.
  have hsum2 : ∀ y : ι → ℝ, Real.sqrt 2 < ‖y‖ → 2 < ∑ i, (y i) ^ 2 := by
    intro y hy
    have h1 : (Real.sqrt 2) ^ 2 < ‖y‖ ^ 2 := by
      rw [sq_lt_sq]
      rwa [abs_of_nonneg (Real.sqrt_nonneg 2), abs_of_nonneg (norm_nonneg y)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h1
    have h2 : ‖y‖ ^ 2 ≤ ∑ i, (y i) ^ 2 :=
      (Real.le_sqrt (norm_nonneg y) (Finset.sum_nonneg fun i _ => sq_nonneg (y i))).mp
        (norm_le_sqrt_sum_sq_pi y)
    linarith
  have hzero : ∀ y : ι → ℝ, Real.sqrt 2 < ‖y‖ → ρ y = 0 := fun y hy => hρ0 y (hsum2 y hy)
  -- hence `fderiv ρ` vanishes on the complement of that ball (where `ρ` is locally `0`)
  have hfderiv_zero : ∀ y : ι → ℝ, Real.sqrt 2 < ‖y‖ → fderiv ℝ ρ y = 0 := by
    intro y hy
    have hε : 0 < ‖y‖ - Real.sqrt 2 := sub_pos.mpr hy
    have hev : ρ =ᶠ[nhds y] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds y hε] with z hz
      have hd : dist z y < ‖y‖ - Real.sqrt 2 := hz
      have h3 : ‖y‖ - ‖z‖ ≤ dist z y := by
        have h5 : ‖y‖ - ‖z‖ ≤ |‖z‖ - ‖y‖| := by
          rw [abs_sub_comm]
          exact le_abs_self _
        rw [dist_eq_norm]
        linarith [abs_norm_sub_norm_le z y]
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

end Work.Diff.STE.B3.VarCoef

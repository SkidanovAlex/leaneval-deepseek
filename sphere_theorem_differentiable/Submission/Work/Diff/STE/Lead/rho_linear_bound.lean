import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A linear bound for a smooth function that is `1` at the origin and `|ρ| ≤ 1`

This file proves `Work.Diff.STE.Lead.rho_linear_bound`: a smooth function `ρ : (ι → ℝ) → ℝ`
with `ρ 0 = 1` and `‖ρ y‖ ≤ 1` everywhere satisfies `(ρ y - 1)² ≤ C² ∑ i, (y i)²` for some
`C ≥ 0`.

The proof is elementary.  The domain `ι → ℝ` carries the *sup* norm (the `Pi` instance), so
`‖y‖²` only controls the individual coordinates through `‖y‖² ≤ ∑ i, (y i)²`
(`norm_sq_le_sum_sq_pi` below).  The ingredients are

* a Lipschitz bound for `ρ` on the (compact, convex) closed unit ball of the sup norm, obtained
  from `ContDiffOn.exists_lipschitzOnWith` — this gives `|ρ y - 1| ≤ K ‖y‖` for `‖y‖ ≤ 1`;
* the trivial bound `|ρ y - 1| ≤ 2`, together with `1 ≤ ‖y‖² ≤ ∑ i, (y i)²`, for `‖y‖ ≥ 1`.

Taking `C := max K 2` finishes.
-/

namespace Work.Diff.STE.Lead

/-- For a finite family of reals, the square of the sup norm is at most the sum of the squares.
(On `ι → ℝ` the norm is the sup norm; `∑ i, (y i)^2` is the squared Euclidean norm of `y`.) -/
lemma norm_sq_le_sum_sq_pi {ι : Type*} [Fintype ι] (y : ι → ℝ) :
    ‖y‖ ^ 2 ≤ ∑ i, (y i) ^ 2 := by
  have hS : (0 : ℝ) ≤ ∑ i, (y i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (y i))
  have h : ‖y‖ ≤ Real.sqrt (∑ i, (y i) ^ 2) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    have h2 : (y i) ^ 2 ≤ ∑ j, (y j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
    exact Real.abs_le_sqrt h2
  calc ‖y‖ ^ 2 ≤ (Real.sqrt (∑ i, (y i) ^ 2)) ^ 2 :=
        sq_le_sq' (by linarith [Real.sqrt_nonneg (∑ i, (y i) ^ 2), norm_nonneg y]) h
    _ = ∑ i, (y i) ^ 2 := Real.sq_sqrt hS

theorem rho_linear_bound {ι : Type*} [Fintype ι]
    (ρ : (ι → ℝ) → ℝ) (hρ0 : ρ 0 = 1)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ι → ℝ, (ρ y - 1) ^ 2 ≤ C ^ 2 * ∑ i, (y i) ^ 2 := by
  -- `ρ` is in particular `C^1`, hence Lipschitz on the compact unit ball.
  have h1 : ContDiff ℝ (1 : WithTop ℕ∞) ρ := hρs.of_le (by simp)
  obtain ⟨K, hK⟩ := (h1.contDiffOn (s := Metric.closedBall (0 : ι → ℝ) 1)).exists_lipschitzOnWith
    one_ne_zero (convex_closedBall _ _) (isCompact_closedBall _ _)
  refine ⟨max (K : ℝ) 2, le_max_of_le_right (by norm_num), ?_⟩
  intro y
  have hsum : ‖y‖ ^ 2 ≤ ∑ i, (y i) ^ 2 := norm_sq_le_sum_sq_pi y
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have hKsq : (K : ℝ) ^ 2 ≤ (max (K : ℝ) 2) ^ 2 :=
    pow_le_pow_left₀ hK0 (le_max_left _ _) 2
  by_cases hsmall : ‖y‖ ≤ 1
  · -- Inside the unit ball we use the mean value (Lipschitz) bound.
    have hy : y ∈ Metric.closedBall (0 : ι → ℝ) 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hsmall
    have h0 : (0 : ι → ℝ) ∈ Metric.closedBall 0 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; norm_num
    have hbd := hK.dist_le_mul y hy 0 h0
    simp only [dist_eq_norm, Real.norm_eq_abs, hρ0, sub_zero] at hbd
    have hsq1 : (ρ y - 1) ^ 2 ≤ ((K : ℝ) * ‖y‖) ^ 2 := by
      rw [sq_le_sq, abs_mul, abs_of_nonneg hK0, abs_of_nonneg (norm_nonneg y)]
      exact hbd
    calc (ρ y - 1) ^ 2 ≤ ((K : ℝ) * ‖y‖) ^ 2 := hsq1
      _ = (K : ℝ) ^ 2 * ‖y‖ ^ 2 := by ring
      _ ≤ (max (K : ℝ) 2) ^ 2 * ∑ i, (y i) ^ 2 :=
          mul_le_mul hKsq hsum (by positivity) (by positivity)
  · -- Outside the unit ball we only use `|ρ y| ≤ 1`.
    have hbig : 1 < ‖y‖ := not_le.mp hsmall
    have hb : |ρ y| ≤ 1 := by
      simpa only [Real.norm_eq_abs] using hρb y
    have hb1 := (abs_le.mp hb).1
    have hb2 := (abs_le.mp hb).2
    have hsq2 : (ρ y - 1) ^ 2 ≤ 4 := by nlinarith
    have hone : (1 : ℝ) ≤ ∑ i, (y i) ^ 2 := by nlinarith [hsum, hbig, norm_nonneg y]
    have h4 : (4 : ℝ) ≤ (max (K : ℝ) 2) ^ 2 := by
      have h2 : (2 : ℝ) ≤ max (K : ℝ) 2 := le_max_right _ _
      nlinarith
    calc (ρ y - 1) ^ 2 ≤ 4 := hsq2
      _ = 4 * 1 := by norm_num
      _ ≤ (max (K : ℝ) 2) ^ 2 * ∑ i, (y i) ^ 2 :=
          mul_le_mul h4 hone (by norm_num) (by positivity)

end Work.Diff.STE.Lead

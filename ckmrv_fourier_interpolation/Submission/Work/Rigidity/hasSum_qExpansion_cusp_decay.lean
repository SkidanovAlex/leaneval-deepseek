import Mathlib
import Submission.Work.Kernels.ModerateGrowth

namespace Work.Rigidity

/-- **A `q`-expansion with vanishing constant term decays like `q`.**

Let `F : ℍ → ℂ` be given on the upper half plane by a convergent `q`-expansion
`F τ = ∑_{m ≥ 0} c m * q^m`, `q = Function.Periodic.qParam 1 (τ : ℂ) = exp (2 π i τ)`, with
arbitrary complex coefficients `c m` (hypothesis `H`).  Then `F` differs from its constant
term `c 0` by `O(q)`: there are `A B : ℝ` with `0 ≤ B` and
`‖F τ - c 0‖ ≤ B * Real.exp (-(2 * Real.pi * τ.im))` for all `τ` with `A ≤ τ.im`.

Sketch.  From `H τ` and `hasSum_nat_add_iff` (with shift `1`) one gets
`HasSum (fun m => c (m+1) * q^(m+1)) (F τ - c 0)`; multiplying by `q⁻¹` and simplifying gives
`HasSum (fun m => c (m+1) * q^m) ((F τ - c 0) / q)`.  The function
`τ ↦ (F τ - c 0) / Function.Periodic.qParam 1 (τ : ℂ)` therefore has a convergent
`q`-expansion with nonnegative exponents, so it is bounded at `i∞` by
`UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion` (`h := 1`): there are `A B` with
`‖(F τ - c 0)/q‖ ≤ B` for `A ≤ τ.im`.  Multiplying by `‖q‖ = Real.exp (-(2π τ.im))`
(`Function.Periodic.norm_qParam`) gives the claim. -/
theorem hasSum_qExpansion_cusp_decay {F : UpperHalfPlane → ℂ} {c : ℕ → ℂ}
    (H : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => c m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ)) :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ τ : UpperHalfPlane, A ≤ τ.im →
      ‖F τ - c 0‖ ≤ B * Real.exp (-(2 * Real.pi * τ.im)) := by
  -- The quotient by `q` has a convergent `q`-expansion with non-negative exponents, hence is
  -- bounded at `i∞`; `isBoundedAtImInfty_of_hasSum_qExpansion` supplies that bound.
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty
      (fun τ : UpperHalfPlane => (F τ - c 0) / Function.Periodic.qParam 1 (τ : ℂ)) := by
    refine UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion (h := 1) (by norm_num)
      (c := fun m => c (m + 1))
      (f := fun τ => (F τ - c 0) / Function.Periodic.qParam 1 (τ : ℂ)) ?_
    intro τ
    have h1 : HasSum (fun m : ℕ => c m * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
        (F τ - c 0 + c 0 * Function.Periodic.qParam 1 (τ : ℂ) ^ 0) := by
      simpa using H τ
    -- remove the `m = 0` term: the tail sums to `F τ - c 0`
    have h2 : HasSum (fun m : ℕ => c (m + 1) * Function.Periodic.qParam 1 (τ : ℂ) ^ (m + 1))
        (F τ - c 0) :=
      (hasSum_nat_add_iff
        (f := fun m : ℕ => c m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) 1).mpr
        (by simpa using h1)
    -- divide by `q`, turning `q^(m+1)` into `q^m`
    have hq : Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
    have hfun : (fun m : ℕ => c (m + 1) * Function.Periodic.qParam 1 (τ : ℂ) ^ (m + 1)
          / Function.Periodic.qParam 1 (τ : ℂ))
        = fun m => c (m + 1) * Function.Periodic.qParam 1 (τ : ℂ) ^ m := by
      funext m
      rw [pow_succ, mul_div_assoc, mul_div_cancel_right₀ _ hq]
    have h3 : HasSum (fun m : ℕ => c (m + 1) * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
        ((F τ - c 0) / Function.Periodic.qParam 1 (τ : ℂ)) := by
      simpa only [hfun] using h2.div_const (Function.Periodic.qParam 1 (τ : ℂ))
    simpa only [smul_eq_mul] using h3
  obtain ⟨M, A, hMA⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.mp hbdd
  refine ⟨A, max M 0, le_max_right _ _, fun τ hτ => ?_⟩
  have hM := hMA τ hτ
  have hq : Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
  have hdiv : (F τ - c 0) / Function.Periodic.qParam 1 (τ : ℂ) * Function.Periodic.qParam 1 (τ : ℂ)
      = F τ - c 0 := div_mul_cancel₀ _ hq
  have hexp : Real.exp (-2 * Real.pi * (τ : ℂ).im / 1) = Real.exp (-(2 * Real.pi * τ.im)) := by
    congr 1
    rw [UpperHalfPlane.coe_im]; ring
  have hGle : ‖(F τ - c 0) / Function.Periodic.qParam 1 (τ : ℂ)‖ ≤ max M 0 :=
    le_trans hM (le_max_left _ _)
  calc ‖F τ - c 0‖
      = ‖(F τ - c 0) / Function.Periodic.qParam 1 (τ : ℂ)‖
          * ‖Function.Periodic.qParam 1 (τ : ℂ)‖ := by
          conv_lhs => rw [← hdiv]
          rw [norm_mul]
    _ = ‖(F τ - c 0) / Function.Periodic.qParam 1 (τ : ℂ)‖
          * Real.exp (-2 * Real.pi * (τ : ℂ).im / 1) := by
          rw [Function.Periodic.norm_qParam]
    _ = ‖(F τ - c 0) / Function.Periodic.qParam 1 (τ : ℂ)‖
          * Real.exp (-(2 * Real.pi * τ.im)) := by rw [hexp]
    _ ≤ max M 0 * Real.exp (-(2 * Real.pi * τ.im)) :=
        mul_le_mul_of_nonneg_right hGle (Real.exp_nonneg _)

end Work.Rigidity

import Mathlib

namespace Work.NN.Newton.ThinProfile

open Real Filter Set

/-- Absolute constants for `Real.smoothTransition` `σ`.  `M0` bounds `|σ'|` and is also a
Lipschitz constant for `σ`; `M1` is a Lipschitz constant for `σ' = deriv σ`; and `σ'(0) = 0`.

Route: `deriv σ` vanishes on `(-∞,0]` (where `σ = 0`) and on `[1,∞)` (where `σ = 1`), hence has
compact support `⊆ Icc 0 1`; it is continuous (it is `C^∞` since `σ` is), so
`HasCompactSupport.exists_bound_of_continuous` gives `M0` bounding `|σ'|` (take `max · 0`).
The Lipschitz clause for `σ` with the same `M0` follows from `|σ'| ≤ M0` by the mean value
theorem (`Convex.norm_image_sub_le_of_norm_deriv_le` on `univ`, `σ` being differentiable).
For `M1`: `deriv σ = fun x => fderiv ℝ σ x 1` is `C^∞` with the same compact support, so
`ContDiff.lipschitzWith_of_hasCompactSupport` gives a Lipschitz constant.  For `σ'(0) = 0` use
that `σ` is `0` on a neighbourhood of `0` from the left and `Filter.EventuallyEq.deriv_eq`, or
`derivWithin` on `Iic 0` together with `uniqueDiffWithinAt_Iic`. -/
theorem smoothTransitionConstants :
    ∃ M0 M1 : ℝ, 0 ≤ M0 ∧ 0 ≤ M1 ∧
      (∀ x : ℝ, |deriv Real.smoothTransition x| ≤ M0) ∧
      (∀ x y : ℝ, |Real.smoothTransition x - Real.smoothTransition y| ≤ M0 * |x - y|) ∧
      (∀ x y : ℝ, |deriv Real.smoothTransition x - deriv Real.smoothTransition y| ≤ M1 * |x - y|) ∧
      deriv Real.smoothTransition 0 = 0 := by
  -- `σ'` vanishes to the left of `0`
  have hzero : ∀ x : ℝ, x < 0 → deriv Real.smoothTransition x = 0 := by
    intro x hx
    have h : Real.smoothTransition =ᶠ[nhds x] (fun _ => (0:ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    simpa using h.deriv_eq
  -- `σ'` vanishes to the right of `1`
  have hone : ∀ x : ℝ, 1 < x → deriv Real.smoothTransition x = 0 := by
    intro x hx
    have h : Real.smoothTransition =ᶠ[nhds x] (fun _ => (1:ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    simpa using h.deriv_eq
  -- hence `σ'` has compact support contained in `[0,1]`
  have hcs : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (K := Set.Icc (0:ℝ) 1) isCompact_Icc ?_
    intro x hx
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    exact hx.elim (hzero x) (hone x)
  -- `σ` is `C^∞`, so is `σ'`
  have h0 : ContDiff ℝ (↑(⊤:ℕ∞) : WithTop ℕ∞) Real.smoothTransition :=
    Real.smoothTransition.contDiff
  have hd1 : ContDiff ℝ (↑(⊤:ℕ∞) : WithTop ℕ∞) (deriv Real.smoothTransition) :=
    h0.iterate_deriv 1
  have hc : Continuous (deriv Real.smoothTransition) := hd1.continuous
  have hne : (↑(⊤:ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- a uniform bound for `|σ'|`
  obtain ⟨C0, hC0⟩ := hcs.exists_bound_of_continuous hc
  have hC0' : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ max C0 0 := by
    intro x
    have h := hC0 x
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  -- a Lipschitz constant for `σ'`
  obtain ⟨C1, hC1⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hd1 hne
  refine ⟨max C0 0, max C1 0, le_max_right _ _, le_max_right _ _, hC0', ?_, ?_, ?_⟩
  · -- mean value theorem turns the bound on `|σ'|` into the Lipschitz property for `σ`
    intro x y
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (f := Real.smoothTransition)
      (C := max C0 0)
      (fun x _ => (h0.differentiable hne).differentiableAt)
      (fun x _ => by rw [Real.norm_eq_abs]; exact hC0' x)
      convex_univ (mem_univ x) (mem_univ y)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_sub_comm (Real.smoothTransition y) (Real.smoothTransition x), abs_sub_comm y x] at h
    exact h
  · -- the Lipschitz property for `σ'`
    intro x y
    have h := hC1.dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  · -- `σ'(0) = 0`: `σ'` is continuous and vanishes on `(-∞,0)`, whose closure contains `0`
    have hclosed : IsClosed {x : ℝ | deriv Real.smoothTransition x = 0} :=
      isClosed_eq hc continuous_const
    have hsub : Set.Iio (0:ℝ) ⊆ {x : ℝ | deriv Real.smoothTransition x = 0} :=
      fun x hx => hzero x hx
    have hmem : (0:ℝ) ∈ closure (Set.Iio (0:ℝ)) := by
      rw [closure_Iio]; exact mem_Iic.2 le_rfl
    exact hclosed.closure_subset (closure_mono hsub hmem)

end Work.NN.Newton.ThinProfile

import Mathlib

namespace Work.CKFinal.Socket

/-- For `0 ≤ t ≤ 1` we have `sinh t ≤ 2 * t`.
The bound follows from the mean value theorem: `sinh t ≤ t * cosh t` morally, and more
precisely `(2x - sinh x)` is monotone on `[0,1]` because its derivative `2 - cosh x` is
nonnegative there (using `cosh x ≤ cosh 1 < 2`). -/
theorem sinh_le_two_mul (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : Real.sinh t ≤ 2 * t := by
  -- Numerical bound: `cosh 1 < 2`, via `cosh 1 = (e + e⁻¹)/2 ≤ (e + 1)/2 < 2`.
  have hcosh_one_lt_two : Real.cosh 1 < 2 := by
    rw [Real.cosh_eq]
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hexp_neg : Real.exp (-1) < 1 := by
      have := Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num)
      rwa [Real.exp_zero] at this
    linarith
  -- On `[0,1]`, `cosh` is bounded by `cosh 1 < 2`.
  have hcosh_le : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.cosh x ≤ 2 := by
    intro x hx
    have hle : Real.cosh x ≤ Real.cosh 1 := by
      rw [Real.cosh_le_cosh, abs_of_nonneg hx.1, abs_one]
      exact hx.2
    linarith
  -- `fun x => 2 * x - Real.sinh x` is monotone on `[0,1]`.
  have hmono : MonotoneOn (fun x : ℝ => 2 * x - Real.sinh x) (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact ((continuous_const.mul continuous_id).sub Real.continuous_sinh).continuousOn
    · exact (differentiableOn_id.const_mul (2 : ℝ)).sub
        Real.differentiable_sinh.differentiableOn
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      have hc := hcosh_le x hx'
      have hd : HasDerivAt (fun x : ℝ => 2 * x - Real.sinh x) (2 - Real.cosh x) x := by
        have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 x := by
          simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
        exact hlin.sub (Real.hasDerivAt_sinh x)
      rw [hd.deriv]
      linarith
  have h := hmono (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1) ⟨h0, h1⟩ h0
  simp only [mul_zero, Real.sinh_zero, sub_zero] at h
  linarith

end Work.CKFinal.Socket

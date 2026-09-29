import Mathlib

namespace Work.CNum

/-- Tail bound for the artanh series: for `0 ≤ x < 1`, the remainder
`atanh x - Σ_{i<n} x^{2i+1}/(2i+1)` is at most `x^{2n+1}/((2n+1)(1-x^2))`.

This is obtained by integrating the exact remainder integrand
`t^{2n}/(1-t^2)` against the uniform bound `1/(1-t^2) ≤ 1/(1-x^2)`,
equivalently by the monotonicity argument on
`K y = atanh y - Σ_{i<n} y^{2i+1}/(2i+1) - y^{2n+1}/((2n+1)(1-x^2))`. -/
theorem artanh_tail_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    1 / 2 * Real.log ((1 + x) / (1 - x)) - ∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * ↑i + 1)
      ≤ x ^ (2 * n + 1) / ((2 * ↑n + 1) * (1 - x ^ 2)) := by
  let F : ℝ → ℝ := fun y => 1 / 2 * Real.log ((1 + y) / (1 - y)) -
    ∑ i ∈ Finset.range n, y ^ (2 * i + 1) / (2 * ↑i + 1)
  let c : ℝ := (2 * ↑n + 1) * (1 - x ^ 2)
  let K : ℝ → ℝ := fun y => F y - y ^ (2 * n + 1) / c
  have hsub : Set.Icc (0:ℝ) x ⊆ Set.Ioo (-1:ℝ) 1 := by
    intro y hy
    simp only [Set.mem_Icc] at hy
    constructor <;> linarith [hy.1, hy.2]
  -- The derivative of `K`: on `(-1,1)` it is `y^{2n}/(1-y^2) - y^{2n}/(1-x^2) ≤ 0`.
  have hderiv : ∀ y ∈ Set.Ioo (-1:ℝ) 1,
      HasDerivAt K ((y ^ 2) ^ n / (1 - y ^ 2) - (2 * ↑n + 1) * y ^ (2 * n) / c) y := by
    intro y hy
    have hF : HasDerivAt F ((y ^ 2) ^ n / (1 - y ^ 2)) y :=
      Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range n hy.1 hy.2
    have hg : HasDerivAt (fun y : ℝ => y ^ (2 * n + 1) / c)
        ((2 * ↑n + 1) * y ^ (2 * n) / c) y := by
      simpa [Nat.add_sub_cancel, push_cast] using
        (hasDerivAt_pow (2 * n + 1) y).div_const c
    exact hF.sub hg
  have hKmono : AntitoneOn K (Set.Icc 0 x) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 x)
      (fun y hy => (hderiv y (hsub hy)).continuousAt.continuousWithinAt)
      (fun y hy => (hderiv y (hsub (interior_subset hy))).hasDerivWithinAt) ?_
    intro y hy
    simp only [interior_Icc, Set.mem_Ioo] at hy
    have h1x : 0 < 1 - x ^ 2 := by nlinarith
    have hle : 1 - x ^ 2 ≤ 1 - y ^ 2 := by nlinarith
    have hkey : (2 * (n:ℝ) + 1) * y ^ (2 * n) / c = y ^ (2 * n) / (1 - x ^ 2) := by
      simp only [c]
      rw [mul_div_mul_left]
      positivity
    rw [hkey, ← pow_mul]
    exact sub_nonpos.mpr (div_le_div_of_nonneg_left (pow_nonneg hy.1.le _) h1x hle)
  have hK0 : K 0 = 0 := by simp [K, F]
  have hKx : K x ≤ K 0 := hKmono ⟨le_rfl, h0⟩ ⟨h0, le_rfl⟩ h0
  rw [hK0] at hKx
  have : F x ≤ x ^ (2 * n + 1) / c := by
    simp only [K] at hKx
    linarith
  simpa [F, c] using this

end Work.CNum

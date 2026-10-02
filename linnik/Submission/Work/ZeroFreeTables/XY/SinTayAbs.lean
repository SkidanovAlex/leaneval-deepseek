import Mathlib

namespace Work.ZeroFreeTables.XY

open scoped BigOperators

/-- Splitting a sum over `Finset.range (2*N)` into its even and odd parts. -/
theorem sum_range_two_mul (f : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range (2*N), f k = ∑ k ∈ Finset.range N, (f (2*k) + f (2*k+1)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 from by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring_nf

/-- `iteratedDeriv (2*m) Real.sin 0 = 0`. -/
theorem iteratedDeriv_sin_zero_even (m : ℕ) : iteratedDeriv (2*m) Real.sin 0 = 0 := by
  rw [Real.iteratedDeriv_even_sin m]
  simp

/-- `iteratedDeriv (2*m+1) Real.sin 0 = (-1)^m`. -/
theorem iteratedDeriv_sin_zero_odd (m : ℕ) : iteratedDeriv (2*m+1) Real.sin 0 = (-1:ℝ)^m := by
  rw [Real.iteratedDeriv_odd_sin m]
  simp

/-- The Taylor polynomial of `sin` of order `2N+1` based at `0`, evaluated at `θ`, equals the
`(N+1)`-term partial sum of the Taylor series of `sin` at `0`. -/
theorem taylorWithinEval_sin (θ : ℝ) (hθ : θ ≠ 0) (N : ℕ) :
    taylorWithinEval Real.sin (2*N+1) (Set.uIcc 0 θ) 0 θ
      = ∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k+1)/((2*k+1).factorial) := by
  have hwithin : ∀ k : ℕ,
      iteratedDerivWithin k Real.sin (Set.uIcc 0 θ) 0 = iteratedDeriv k Real.sin 0 := by
    intro k
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm hθ))
      Real.contDiff_sin.contDiffAt (by simp)
  rw [taylor_within_apply]
  simp only [hwithin, smul_eq_mul, sub_zero]
  rw [show 2*N+1+1 = 2*(N+1) from by ring]
  have hsplit :
      (∑ k ∈ Finset.range (2*(N+1)),
          ((k.factorial : ℝ))⁻¹ * θ^k * iteratedDeriv k Real.sin 0)
        = ∑ k ∈ Finset.range (N+1),
            (((2*k).factorial : ℝ)⁻¹ * θ^(2*k) * iteratedDeriv (2*k) Real.sin 0
             + ((2*k+1).factorial : ℝ)⁻¹ * θ^(2*k+1) * iteratedDeriv (2*k+1) Real.sin 0) := by
    simpa using sum_range_two_mul
      (fun k : ℕ => ((k.factorial : ℝ))⁻¹ * θ^k * iteratedDeriv k Real.sin 0) (N+1)
  rw [hsplit]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [iteratedDeriv_sin_zero_even k, iteratedDeriv_sin_zero_odd k, mul_zero, zero_add,
    div_eq_mul_inv]
  ring

theorem SinTayAbs (θ : ℝ) (N : ℕ) :
    |Real.sin θ - ∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k+1)/((2*k+1).factorial)|
      ≤ |θ|^(2*N+2)/((2*N+2).factorial) := by
  rcases eq_or_ne θ 0 with h0 | hθ
  · subst h0
    have hz : (∑ k ∈ Finset.range (N+1),
        (-1:ℝ)^k * (0:ℝ)^(2*k+1)/((2*k+1).factorial)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hk0 : (0:ℝ)^(2*k+1) = 0 := by
        apply zero_pow
        omega
      rw [hk0, mul_zero, zero_div]
    have hN0 : (0:ℝ)^(2*N+2) = 0 := by
      apply zero_pow
      omega
    rw [Real.sin_zero, hz, sub_zero, abs_zero, hN0, zero_div]
  · have hsum := taylorWithinEval_sin θ hθ N
    obtain ⟨x', hx', hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (f := Real.sin) (x := θ) (x₀ := 0)
        (n := 2*N+1) (Ne.symm hθ) Real.contDiff_sin.contDiffOn
    rw [← hsum, hrem]
    rw [show 2*N+1+1 = 2*N+2 from by ring]
    simp only [sub_zero]
    have hpos : (0:ℝ) < ((2*N+2).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos (2*N+2)
    have hd : |iteratedDeriv (2*N+2) Real.sin x'| ≤ 1 := Real.abs_iteratedDeriv_sin_le_one _ _
    calc |iteratedDeriv (2*N+2) Real.sin x' * θ ^ (2*N+2) / ((2*N+2).factorial : ℝ)|
        = |iteratedDeriv (2*N+2) Real.sin x'| * |θ| ^ (2*N+2) / ((2*N+2).factorial : ℝ) := by
          rw [abs_div, abs_mul, abs_pow, abs_of_pos hpos]
      _ ≤ 1 * |θ| ^ (2*N+2) / ((2*N+2).factorial : ℝ) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hd (pow_nonneg (abs_nonneg θ) _)) (le_of_lt hpos)
      _ = |θ| ^ (2*N+2) / ((2*N+2).factorial : ℝ) := by rw [one_mul]

end Work.ZeroFreeTables.XY

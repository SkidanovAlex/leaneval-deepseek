import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ChiSmallWallis

/-- Wallis-type reduction step for the integral of an even power of `Real.cos`
over `[0, π/2]`: integrating `cos^(2(m+1)) = cos^(2m) * cos^2` by parts (via
Mathlib's `integral_cos_pow`) and noting that the boundary term
`cos^(2m+1) * sin` vanishes at both endpoints gives

  `∫₀^{π/2} cos^{2(m+1)} = ((2m+1)/(2m+2)) · ∫₀^{π/2} cos^{2m}`. -/
private lemma cos_pow_half_pi_succ (m : ℕ) :
    (∫ x in (0:ℝ)..(Real.pi/2), Real.cos x ^ (2*(m+1)))
      = (((2*m+1 : ℕ) : ℝ) / ((2*m+2 : ℕ) : ℝ))
        * ∫ x in (0:ℝ)..(Real.pi/2), Real.cos x ^ (2*m) := by
  rw [show 2 * (m + 1) = 2 * m + 2 from by omega]
  rw [integral_cos_pow (a := (0:ℝ)) (b := Real.pi/2) (2*m)]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero, Real.sin_zero,
    zero_pow (by omega : (2*m+1) ≠ 0), one_pow, mul_one, mul_zero, sub_zero]
  push_cast
  ring

/-- Wallis' integral formula (elementary form): for every `M : ℕ`,
`∫₀^{π/2} cos^{2M} x dx = (π/2) · ∏_{i<M} (2i+1)/(2i+2)`.  This is the
standard product form of the Wallis integral, obtained by iterating the
reduction step `cos_pow_half_pi_succ` from the base case `∫₀^{π/2} 1 = π/2`. -/
lemma cos_pow_half_pi_interval (M : ℕ) :
    ∫ x in (0:ℝ)..(Real.pi/2), Real.cos x ^ (2*M)
      = Real.pi/2 * ∏ i ∈ Finset.range M, (2*(i:ℝ)+1)/(2*i+2) := by
  have key : ∀ m : ℕ,
      (∫ x in (0:ℝ)..(Real.pi/2), Real.cos x ^ (2*m))
        = Real.pi/2 * ∏ i ∈ Finset.range m, (2*(i:ℝ)+1)/(2*i+2) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [cos_pow_half_pi_succ m, ih, Finset.prod_range_succ]
      push_cast
      ring
  exact key M

end Work.ChiSmallWallis

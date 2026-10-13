import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

/-- `rpow` algebra on a non-negative base, in the "positive half exponent" form used by the
`D_z`-slots: for `a ≥ 0` and arbitrary real `e`,
`(A·(W · a^{-e/2}))² = A²·(W²·a^{-e})`.

At `a = 0` both sides survive Lean's totalised `rpow`: for `e ≠ 0` we have
`0^{-e/2} = 0 = 0^{-e}` (`Real.zero_rpow`), while for `e = 0` both `0^{0}` factors are `1`.
For `a > 0` the identity is `sq_rpow_mul_two` (`(a^{-e/2})² = a^{(-e/2)·2} = a^{-e}`) followed
by `mul_pow`. -/
private lemma sq_mul_rpow_neg_half (A W a e : ℝ) (ha : 0 ≤ a) :
    (A * (W * a ^ (-(e / 2)))) ^ 2 = A ^ 2 * (W ^ 2 * a ^ (-e)) := by
  rcases eq_or_lt_of_le ha with h | h
  · subst h
    by_cases he : e = 0
    · subst he; simp only [neg_zero, zero_div, Real.rpow_zero, mul_one]; ring
    · have h1 : (0 : ℝ) ^ (-(e / 2)) = 0 := Real.zero_rpow (by intro hh; exact he (by linarith))
      have h2 : (0 : ℝ) ^ (-e) = 0 := Real.zero_rpow (neg_ne_zero.mpr he)
      rw [h1, h2]; ring
  · have hsq : (a ^ (-(e / 2))) ^ 2 = a ^ (-e) := by
      rw [← Real.rpow_natCast (a ^ (-(e / 2))) 2, ← Real.rpow_mul (le_of_lt h)]
      congr 1; ring
    rw [mul_pow, mul_pow, hsq]

/-- The same identity in the "division" form used by the goal as stated:
for `a ≥ 0` and arbitrary real `e`, `(A·(W / a^{e/2}))² = A²·(W²·a^{-e})`.
`div_eq_mul_inv` and `Real.rpow_neg` turn the `a^{e/2}` in the denominator into the factor
`a^{-e/2}`, reducing to `sq_mul_rpow_neg_half`. -/
private lemma sq_div_rpow_half (A W a e : ℝ) (ha : 0 ≤ a) :
    (A * (W / a ^ (e / 2))) ^ 2 = A ^ 2 * (W ^ 2 * a ^ (-e)) := by
  rw [div_eq_mul_inv, ← Real.rpow_neg ha (e / 2)]
  exact sq_mul_rpow_neg_half A W a e ha

-- The stated lemma carries `hz : z ∈ Iz` for compatibility with its call sites, although the
-- identity proved below holds for every real `w z`: only the non-negativity of `sin(2θ)` on `Iθ`
-- is used, and both slot weights enter through `sq_div_rpow_half`/`sq_mul_rpow_neg_half`.
set_option linter.unusedVariables false in
/-- The pointwise `rpow` algebra converting the `T1Hard` slot weights into the corresponding
summands of `HkIntegrand`: for `z ∈ Iz` (so `w z = (1+z)²/z² ≥ 0`) and `θ ∈ Iθ` (so
`0 ≤ sin(2θ)`) and arbitrary reals `A`, `B`,
`(w z)²·(A²·sin(2θ)^{-η}) = (A·(w z / sin(2θ)^{η/2}))²`
and `(w z)²·(B²·sin(2θ)^{-γ}) = (B·Wt α z θ)²` (`Wt α z θ = w z·sin(2θ)^{-γ/2}`).
Route: `Real.rpow_mul` (`(s^{-η/2})² = s^{-η}` when `0 ≤ s`), `Real.rpow_neg`, `Real.div_rpow`,
`div_pow`, `inv_pow`, `Real.rpow_nonneg`; the degenerate cases `sin(2θ) = 0` and `w z = 0`
(`z = 0`) are handled by `Real.zero_rpow` and by `0^p = 0` for `p ≠ 0` (note `0^k = 0` for `k`
like `η/2 ≠ 0`); `ring` at the end. -/
theorem T1HardWeightAlg (α : ℝ) (z θ A B : ℝ) (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z) ^ 2 * (A ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        = (A * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ∧ (Work.Spaces.w z) ^ 2 * (B ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α))
        = (B * Work.Spaces.Wt α z θ) ^ 2 := by
  -- On `Iθ = [0,π/2]` the base `sin(2θ)` of every `rpow` below is non-negative.
  have ha : 0 ≤ Real.sin (2 * θ) := by
    have h1 : (0 : ℝ) ≤ θ := hθ.1
    have h2 : θ ≤ Real.pi / 2 := hθ.2
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  constructor
  · -- `(w z)²·(A²·s^{-η}) = (A·(w z / s^{η/2}))²`: apply the `rpow` algebra to the right-hand
    -- side and commute the factors.
    rw [sq_div_rpow_half A (Work.Spaces.w z) (Real.sin (2 * θ)) Work.Spaces.eta ha]
    ring
  · -- `(w z)²·(B²·s^{-γ}) = (B·Wt α z θ)²`: unfold `Wt α z θ = w z·s^{-γ/2}` and apply the
    -- `rpow` algebra with `e = γ = gam α`.
    rw [Work.Spaces.Wt, Work.Spaces.wTheta,
      sq_mul_rpow_neg_half B (Work.Spaces.w z) (Real.sin (2 * θ)) (Work.Spaces.gam α) ha]
    ring

end Work.FTS.H2

import Mathlib
import Submission.Work.PARIMPL.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Work.PARIMPL

open Complex

/-- The seven-term triangle inequality. -/
private lemma norm_seven_le (x1 x2 x3 x4 x5 x6 x7 : ℂ) :
    ‖x1 + x2 + x3 + x4 + x5 + x6 + x7‖ ≤ ‖x1‖+‖x2‖+‖x3‖+‖x4‖+‖x5‖+‖x6‖+‖x7‖ := by
  have h1 : ‖x1+x2+x3+x4+x5+x6+x7‖ ≤ ‖x1+x2+x3+x4+x5+x6‖ + ‖x7‖ := norm_add_le _ _
  have h2 : ‖x1+x2+x3+x4+x5+x6‖ ≤ ‖x1+x2+x3+x4+x5‖ + ‖x6‖ := norm_add_le _ _
  have h3 : ‖x1+x2+x3+x4+x5‖ ≤ ‖x1+x2+x3+x4‖ + ‖x5‖ := norm_add_le _ _
  have h4 : ‖x1+x2+x3+x4‖ ≤ ‖x1+x2+x3‖ + ‖x4‖ := norm_add_le _ _
  have h5 : ‖x1+x2+x3‖ ≤ ‖x1+x2‖ + ‖x3‖ := norm_add_le _ _
  have h6 : ‖x1+x2‖ ≤ ‖x1‖ + ‖x2‖ := norm_add_le _ _
  linarith

/-- For `0 ≤ x ≤ 1`, `x³ ≤ x²`. -/
private lemma cube_le_sq {x : ℝ} (_h0 : 0 ≤ x) (h1 : x ≤ 1) : x^3 ≤ x^2 := by
  calc x^3 = x^2 * x := by ring
    _ ≤ x^2 * 1 := by gcongr
    _ = x^2 := by ring

/-- **The second-order algebraic estimate in the rotated normalisation.**

With `hz = τ + h₁ζ + O(ζ²)`, `κ = τ − h₁/τ`, `‖τ‖ = 1`, `‖hz‖ ≤ 3/2`, `‖ζ‖ ≤ 1/4`,
`‖a‖ ≤ 1/4`, the remainder of the rotated approximate Écalle step satisfies

`‖τ − hz + ζhz² − κζhz − κaζhz²‖ ≤ C·(‖ζ‖² + ‖a‖²)`

for an explicit constant `C` depending only on `h₁`, `τ`, `A` (in particular not on
`κ`, which is determined by `κ = τ − h₁/τ`, whence `‖κ‖ ≤ 1 + ‖h₁‖`). -/
theorem norm_S_le_rot (h1 τ : ℂ) (A : ℝ) (hA : 0 ≤ A) (hτ : ‖τ‖ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ζ hz a κ : ℂ), κ = τ - h1 / τ →
      ‖hz - τ - h1 * ζ‖ ≤ A * ‖ζ‖ ^ 2 → ‖hz‖ ≤ 3 / 2 → ‖ζ‖ ≤ 1 / 4 → ‖a‖ ≤ 1 / 4 →
      ‖τ - hz + ζ * hz ^ 2 - κ * ζ * hz - κ * a * ζ * hz ^ 2‖
        ≤ C * (‖ζ‖ ^ 2 + ‖a‖ ^ 2) := by
  refine ⟨2*‖h1‖ + 2*A + (‖h1‖ + A)^2 + ‖h1‖*(1 + ‖h1‖) + A + (1 + ‖h1‖)*A
      + 9*(1 + ‖h1‖)/8, ?_, ?_⟩
  · have h1n : (0:ℝ) ≤ ‖h1‖ := norm_nonneg h1
    have hsq : (0:ℝ) ≤ (‖h1‖ + A)^2 := sq_nonneg _
    have ha1 : (0:ℝ) ≤ ‖h1‖*(1 + ‖h1‖) := mul_nonneg h1n (by positivity)
    have ha2 : (0:ℝ) ≤ (1 + ‖h1‖)*A := mul_nonneg (by positivity) hA
    have ha3 : (0:ℝ) ≤ 9*(1 + ‖h1‖)/8 := by positivity
    have ha4 : (0:ℝ) ≤ 2*‖h1‖ := by positivity
    have ha5 : (0:ℝ) ≤ 2*A := by linarith
    linarith
  · intro ζ hz a κ hκ hhe hhz hζ1 ha1
    have hτ0 : τ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hτ; norm_num at hτ
    have hκτ : κ * τ = τ^2 - h1 := by
      rw [hκ, sub_mul, div_mul_cancel₀ h1 hτ0]; ring
    have hκb : ‖κ‖ ≤ 1 + ‖h1‖ := by
      rw [hκ]
      calc ‖τ - h1/τ‖ ≤ ‖τ‖ + ‖h1/τ‖ := norm_sub_le _ _
        _ = 1 + ‖h1‖ := by rw [norm_div, hτ, div_one]
    have hexpr : τ - hz + ζ*hz^2 - κ*ζ*hz - κ*a*ζ*hz^2
        = τ - (1 - κ*a)*hz + (1 - κ*a)*ζ*hz^2 - κ*(ζ + a)*hz := by ring
    rw [hexpr]
    set e : ℂ := hz - τ - h1*ζ with hedef
    have hhe' : ‖e‖ ≤ A*‖ζ‖^2 := by rw [hedef]; exact hhe
    have hzdecomp : hz = τ + h1*ζ + e := by rw [hedef]; ring
    have hS : τ - (1 - κ*a)*hz + (1 - κ*a)*ζ*hz^2 - κ*(ζ + a)*hz
        = ζ*(τ^2 - h1 - κ*τ) + (2*τ*h1*ζ^2 + 2*τ*ζ*e + ζ*(h1*ζ + e)^2 - h1*κ*ζ^2
            - e - κ*ζ*e - κ*a*ζ*hz^2) := by
      rw [hzdecomp]; ring
    have hzero : τ^2 - h1 - κ*τ = 0 := by rw [hκτ]; ring
    rw [hS, hzero, mul_zero, zero_add]
    have hζ0 : (0:ℝ) ≤ ‖ζ‖ := norm_nonneg ζ
    have hh10 : (0:ℝ) ≤ ‖h1‖ := norm_nonneg h1
    have hκ0 : (0:ℝ) ≤ ‖κ‖ := norm_nonneg κ
    have hX1 : ‖2*τ*h1*ζ^2‖ ≤ 2*‖h1‖*‖ζ‖^2 := by
      have heq : ‖2*τ*h1*ζ^2‖ = 2*‖h1‖*‖ζ‖^2 := by
        first | (rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat, hτ]; ring)
              | rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat, hτ]
      exact heq.le
    have hX2 : ‖2*τ*ζ*e‖ ≤ 2*A*‖ζ‖^2 := by
      have heq : ‖2*τ*ζ*e‖ = 2*‖ζ‖*‖e‖ := by
        first | (rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, hτ]; ring)
              | rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, hτ]
      rw [heq]
      have h3 : ‖ζ‖^3 ≤ ‖ζ‖^2 := cube_le_sq hζ0 (by linarith)
      nlinarith [hhe', h3, hA, hζ0, hh10]
    have hX3 : ‖ζ*(h1*ζ + e)^2‖ ≤ (‖h1‖ + A)^2*‖ζ‖^2 := by
      have h1' : ‖h1*ζ + e‖ ≤ (‖h1‖ + A)*‖ζ‖ := by
        have h2 : ‖h1*ζ + e‖ ≤ ‖h1‖*‖ζ‖ + A*‖ζ‖^2 := by
          have hh2 := norm_add_le (h1*ζ) e
          rw [norm_mul] at hh2
          linarith [hh2, hhe']
        have h3 : A*‖ζ‖^2 ≤ A*‖ζ‖ := by
          have : ‖ζ‖^2 ≤ ‖ζ‖ := by nlinarith [hζ0, hζ1]
          exact mul_le_mul_of_nonneg_left this hA
        have h4 : (‖h1‖ + A)*‖ζ‖ = ‖h1‖*‖ζ‖ + A*‖ζ‖ := by ring
        rw [h4]; linarith [h2, h3]
      have h5 : ‖ζ*(h1*ζ + e)^2‖ = ‖ζ‖ * ‖h1*ζ + e‖^2 := by
        rw [norm_mul, norm_pow]
      rw [h5]
      have h6 : ‖h1*ζ + e‖^2 ≤ ((‖h1‖ + A)*‖ζ‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1' 2
      have h3 : ‖ζ‖^3 ≤ ‖ζ‖^2 := cube_le_sq hζ0 (by linarith)
      have h8 : (0:ℝ) ≤ (‖h1‖ + A)^2 := sq_nonneg _
      nlinarith [h6, h3, h8]
    have hX4 : ‖h1*κ*ζ^2‖ ≤ ‖h1‖*‖κ‖*‖ζ‖^2 := by
      have heq : ‖h1*κ*ζ^2‖ = ‖h1‖*‖κ‖*‖ζ‖^2 := by
        first | (rw [norm_mul, norm_mul, norm_pow]; ring) | rw [norm_mul, norm_mul, norm_pow]
      exact heq.le
    have hX5 : ‖e‖ ≤ A*‖ζ‖^2 := hhe'
    have hX6 : ‖κ*ζ*e‖ ≤ ‖κ‖*A*‖ζ‖^2 := by
      have heq : ‖κ*ζ*e‖ = ‖κ‖*‖ζ‖*‖e‖ := by
        first | (rw [norm_mul, norm_mul]; ring) | rw [norm_mul, norm_mul]
      rw [heq]
      calc ‖κ‖*‖ζ‖*‖e‖ ≤ ‖κ‖*‖ζ‖*(A*‖ζ‖^2) :=
            mul_le_mul_of_nonneg_left hhe' (mul_nonneg hκ0 hζ0)
        _ = ‖κ‖*A*‖ζ‖^3 := by ring
        _ ≤ ‖κ‖*A*‖ζ‖^2 := by
            have h3 : ‖ζ‖^3 ≤ ‖ζ‖^2 := cube_le_sq hζ0 (by linarith)
            exact mul_le_mul_of_nonneg_left h3 (mul_nonneg hκ0 hA)
    have hX7 : ‖κ*a*ζ*hz^2‖ ≤ (9*‖κ‖/8)*(‖ζ‖^2 + ‖a‖^2) := by
      have heq : ‖κ*a*ζ*hz^2‖ = ‖κ‖*‖a‖*‖ζ‖*‖hz‖^2 := by
        first | (rw [norm_mul, norm_mul, norm_mul, norm_pow]; ring)
              | rw [norm_mul, norm_mul, norm_mul, norm_pow]
      rw [heq]
      have hhz2 : ‖hz‖^2 ≤ 9/4 := by nlinarith [hhz, norm_nonneg hz]
      have h9 : ‖κ‖*‖a‖*‖ζ‖*‖hz‖^2 ≤ ‖κ‖*‖a‖*‖ζ‖*(9/4) := by
        have h0 : (0:ℝ) ≤ ‖κ‖*‖a‖*‖ζ‖ := by positivity
        exact mul_le_mul_of_nonneg_left hhz2 h0
      have h10 : ‖ζ‖*‖a‖ ≤ (‖ζ‖^2 + ‖a‖^2)/2 := by nlinarith [sq_nonneg (‖ζ‖ - ‖a‖)]
      have h11 : (9/4)*‖κ‖*(‖ζ‖*‖a‖) ≤ (9/4)*‖κ‖*((‖ζ‖^2 + ‖a‖^2)/2) := by
        have h0 : (0:ℝ) ≤ (9/4)*‖κ‖ := by positivity
        exact mul_le_mul_of_nonneg_left h10 h0
      nlinarith [h9, h11]
    have htri : ‖2*τ*h1*ζ^2 + 2*τ*ζ*e + ζ*(h1*ζ + e)^2 - h1*κ*ζ^2 - e - κ*ζ*e
          - κ*a*ζ*hz^2‖
        ≤ ‖2*τ*h1*ζ^2‖ + ‖2*τ*ζ*e‖ + ‖ζ*(h1*ζ + e)^2‖ + ‖h1*κ*ζ^2‖ + ‖e‖ + ‖κ*ζ*e‖
          + ‖κ*a*ζ*hz^2‖ := by
      have h := norm_seven_le (2*τ*h1*ζ^2) (2*τ*ζ*e) (ζ*(h1*ζ + e)^2) (-(h1*κ*ζ^2)) (-e)
        (-(κ*ζ*e)) (-(κ*a*ζ*hz^2))
      simpa only [norm_neg, sub_eq_add_neg, add_assoc] using h
    refine htri.trans ?_
    -- explicit combination of the seven bounds
    have hQ0 : (0:ℝ) ≤ ‖a‖^2 := sq_nonneg ‖a‖
    have hS0 : (0:ℝ) ≤ ‖ζ‖^2 + ‖a‖^2 := by linarith [sq_nonneg ‖ζ‖, hQ0]
    have hC1nn : (0:ℝ) ≤ 2*‖h1‖ + 2*A + (‖h1‖ + A)^2 + ‖h1‖*‖κ‖ + A + ‖κ‖*A := by
      have h1n : (0:ℝ) ≤ ‖h1‖ := norm_nonneg h1
      have h3 : (0:ℝ) ≤ ‖h1‖*‖κ‖ := mul_nonneg h1n hκ0
      have h4 : (0:ℝ) ≤ ‖κ‖*A := mul_nonneg hκ0 hA
      have h5 : (0:ℝ) ≤ (‖h1‖ + A)^2 := sq_nonneg _
      have h6 : (0:ℝ) ≤ 2*‖h1‖ := by linarith
      have h7 : (0:ℝ) ≤ 2*A := by linarith
      linarith
    have h6exp : (2*‖h1‖ + 2*A + (‖h1‖ + A)^2 + ‖h1‖*‖κ‖ + A + ‖κ‖*A) * ‖ζ‖^2
        = 2*‖h1‖*‖ζ‖^2 + 2*A*‖ζ‖^2 + (‖h1‖+A)^2*‖ζ‖^2 + ‖h1‖*‖κ‖*‖ζ‖^2
          + A*‖ζ‖^2 + ‖κ‖*A*‖ζ‖^2 := by ring
    have h6 : ‖2*τ*h1*ζ^2‖ + ‖2*τ*ζ*e‖ + ‖ζ*(h1*ζ + e)^2‖ + ‖h1*κ*ζ^2‖ + ‖e‖
        + ‖κ*ζ*e‖
        ≤ (2*‖h1‖ + 2*A + (‖h1‖ + A)^2 + ‖h1‖*‖κ‖ + A + ‖κ‖*A) * ‖ζ‖^2 := by
      rw [h6exp]; linarith [hX1, hX2, hX3, hX4, hX5, hX6]
    have hKleC : (2*‖h1‖ + 2*A + (‖h1‖ + A)^2 + ‖h1‖*‖κ‖ + A + ‖κ‖*A) + 9*‖κ‖/8
        ≤ 2*‖h1‖ + 2*A + (‖h1‖ + A)^2 + ‖h1‖*(1 + ‖h1‖) + A + (1 + ‖h1‖)*A
          + 9*(1 + ‖h1‖)/8 := by
      have hk1 : ‖h1‖*‖κ‖ ≤ ‖h1‖*(1 + ‖h1‖) := mul_le_mul_of_nonneg_left hκb hh10
      have hk2 : ‖κ‖*A ≤ (1 + ‖h1‖)*A := mul_le_mul_of_nonneg_right hκb hA
      have hk3 : 9*‖κ‖/8 ≤ 9*(1 + ‖h1‖)/8 := by linarith
      linarith
    calc ‖2*τ*h1*ζ^2‖ + ‖2*τ*ζ*e‖ + ‖ζ*(h1*ζ + e)^2‖ + ‖h1*κ*ζ^2‖ + ‖e‖ + ‖κ*ζ*e‖
          + ‖κ*a*ζ*hz^2‖
        ≤ (2*‖h1‖ + 2*A + (‖h1‖ + A)^2 + ‖h1‖*‖κ‖ + A + ‖κ‖*A) * ‖ζ‖^2
          + (9*‖κ‖/8)*(‖ζ‖^2 + ‖a‖^2) := by linarith [h6, hX7]
      _ ≤ (2*‖h1‖ + 2*A + (‖h1‖ + A)^2 + ‖h1‖*‖κ‖ + A + ‖κ‖*A) * (‖ζ‖^2 + ‖a‖^2)
          + (9*‖κ‖/8)*(‖ζ‖^2 + ‖a‖^2) := by
          have hle : ‖ζ‖^2 ≤ ‖ζ‖^2 + ‖a‖^2 := by linarith [hQ0]
          linarith [mul_le_mul_of_nonneg_left hle hC1nn]
      _ = ((2*‖h1‖ + 2*A + (‖h1‖ + A)^2 + ‖h1‖*‖κ‖ + A + ‖κ‖*A) + 9*‖κ‖/8)
          * (‖ζ‖^2 + ‖a‖^2) := by ring
      _ ≤ (2*‖h1‖ + 2*A + (‖h1‖ + A)^2 + ‖h1‖*(1 + ‖h1‖) + A + (1 + ‖h1‖)*A
          + 9*(1 + ‖h1‖)/8) * (‖ζ‖^2 + ‖a‖^2) :=
          mul_le_mul_of_nonneg_right hKleC hS0

end Work.PARIMPL

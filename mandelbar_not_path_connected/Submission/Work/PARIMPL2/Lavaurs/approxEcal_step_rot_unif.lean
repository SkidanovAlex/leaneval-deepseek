/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# Uniform-in-the-germ per-step error of the rotated approximate Écalle coordinate

`Work.PARIMPL.approxEcal_step_rot` gives, for a *fixed* germ `(h, τ, h₁)`, an existential
constant `C` with the per-step estimate `O(‖ζ‖² + λ²)`.  The transit of the Lavaurs endgame is
applied in the `c`-chart (`h := P.h c`, `τ := P.h c 0`, `h₁ := P.h1 c`) and needs a constant that
is *uniform in `c`*: only `A`, `r` and a bound `B` on `‖h₁‖` are uniform, while
`κ c = τ c − h₁ c/τ c` is bounded by `1 + B` because `‖τ c‖ = 1`.

The proof copies the two estimates `Work.PARIMPL.norm_S_le_rot` and
`Work.PARIMPL.approxEcal_step_rot` *privately* with `‖h₁‖` replaced by the bound `B`:
the algebraic constant of `norm_S_le_rot` is monotone in `‖h₁‖` on `[0, B]` (lemma `Kmono`),
and everything else in the analytic estimate depends on `‖κ‖ ≤ 1 + B` only.  The constant
exhibited is

`|2B + 2A + (B+A)² + B(1+B) + A + (1+B)A + 9(1+B)/8 + 32(1 + (1+B)/4) + 9(1+B)/2|`.
-/
import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Windows
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL.norm_S_le_rot

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace Work.PARIMPL2.Lavaurs

open Complex
open Work.Implosion
open Work.Implosion.Approx

/-! ## The algebraic core, with an explicit constant -/

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

/-- **The second-order algebraic estimate of `norm_S_le_rot`, with its constant made explicit.**

This is the proof of `Work.PARIMPL.norm_S_le_rot`, transcribed so that the constant it produces
is visible: `2‖h₁‖ + 2A + (‖h₁‖+A)² + ‖h₁‖(1+‖h₁‖) + A + (1+‖h₁‖)A + 9(1+‖h₁‖)/8`. -/
private theorem norm_S_le_rot_expl (h1 τ : ℂ) (A : ℝ) (hA : 0 ≤ A) (hτ : ‖τ‖ = 1) :
    ∀ (ζ hz a κ : ℂ), κ = τ - h1 / τ →
      ‖hz - τ - h1 * ζ‖ ≤ A * ‖ζ‖ ^ 2 → ‖hz‖ ≤ 3 / 2 → ‖ζ‖ ≤ 1 / 4 → ‖a‖ ≤ 1 / 4 →
      ‖τ - hz + ζ * hz ^ 2 - κ * ζ * hz - κ * a * ζ * hz ^ 2‖
        ≤ (2*‖h1‖ + 2*A + (‖h1‖ + A)^2 + ‖h1‖*(1 + ‖h1‖) + A + (1 + ‖h1‖)*A
            + 9*(1 + ‖h1‖)/8) * (‖ζ‖ ^ 2 + ‖a‖ ^ 2) := by
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

/-- The explicit constant of `norm_S_le_rot_expl` is monotone on `[0, B]`. -/
private lemma Kmono {A B b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) (hbB : b ≤ B) :
    2*b + 2*A + (b + A)^2 + b*(1 + b) + A + (1 + b)*A + 9*(1 + b)/8
      ≤ 2*B + 2*A + (B + A)^2 + B*(1 + B) + A + (1 + B)*A + 9*(1 + B)/8 := by
  have hdiff : 2*B + 2*A + (B + A)^2 + B*(1 + B) + A + (1 + B)*A + 9*(1 + B)/8
      - (2*b + 2*A + (b + A)^2 + b*(1 + b) + A + (1 + b)*A + 9*(1 + b)/8)
      = (B - b) * (2*(B + b) + 3*A + 33/8) := by ring
  have h1 : (0:ℝ) ≤ B - b := by linarith
  have h2 : (0:ℝ) ≤ 2*(B + b) + 3*A + 33/8 := by nlinarith
  nlinarith [mul_nonneg h1 h2]

/-- **The algebraic core with a constant depending only on the bound `B ≥ ‖h₁‖`.** -/
private lemma norm_S_le_rot_B (h1 τ : ℂ) (A B : ℝ) (hA : 0 ≤ A) (hτ : ‖τ‖ = 1)
    (hB : ‖h1‖ ≤ B) :
    ∀ (ζ hz a κ : ℂ), κ = τ - h1 / τ →
      ‖hz - τ - h1 * ζ‖ ≤ A * ‖ζ‖ ^ 2 → ‖hz‖ ≤ 3 / 2 → ‖ζ‖ ≤ 1 / 4 → ‖a‖ ≤ 1 / 4 →
      ‖τ - hz + ζ * hz ^ 2 - κ * ζ * hz - κ * a * ζ * hz ^ 2‖
        ≤ (2*B + 2*A + (B + A)^2 + B*(1 + B) + A + (1 + B)*A + 9*(1 + B)/8)
          * (‖ζ‖ ^ 2 + ‖a‖ ^ 2) := by
  intro ζ hz a κ hκ hhe hhz hζ1 ha1
  have hb0 : (0:ℝ) ≤ ‖h1‖ := norm_nonneg h1
  have hS0 : (0:ℝ) ≤ ‖ζ‖ ^ 2 + ‖a‖ ^ 2 := by positivity
  have hK := Kmono hA hb0 hB
  calc ‖τ - hz + ζ * hz ^ 2 - κ * ζ * hz - κ * a * ζ * hz ^ 2‖
      ≤ (2*‖h1‖ + 2*A + (‖h1‖ + A)^2 + ‖h1‖*(1 + ‖h1‖) + A + (1 + ‖h1‖)*A
          + 9*(1 + ‖h1‖)/8) * (‖ζ‖ ^ 2 + ‖a‖ ^ 2) :=
        norm_S_le_rot_expl h1 τ A hA hτ ζ hz a κ hκ hhe hhz hζ1 ha1
    _ ≤ (2*B + 2*A + (B + A)^2 + B*(1 + B) + A + (1 + B)*A + 9*(1 + B)/8)
          * (‖ζ‖ ^ 2 + ‖a‖ ^ 2) := mul_le_mul_of_nonneg_right hK hS0

/-! ## The per-step error, uniform in the germ -/

/-- **The per-step error of the rotated approximate Écalle coordinate, with a constant that is
uniform in the germ.**  This is `Work.PARIMPL.approxEcal_step_rot` with the existential constant
`C` moved *outside* the germ: the constant depends only on `A`, `r` and a bound `B` on `‖h1‖`, not
on the particular germ `(h, τ, h1)`.

Needed because the transit is applied in the `c`-chart with `h := P.h c`, `τ := P.h c 0`,
`h1 := P.h1 c`, and the constant of the final estimate must be uniform in `c` (only `A = P.A`,
`r = P.r` and `‖P.h1 c‖ ≤ B` are uniform; `κ c = τ - h1/τ` is bounded by `1 + B` since `‖τ‖ = 1`).

The delivered proof exhibits the explicit constant
`|2B + 2A + (B+A)² + B(1+B) + A + (1+B)A + 9(1+B)/8 + 32(1 + (1+B)/4) + 9(1+B)/2|`. -/
theorem approxEcal_step_rot_unif (A r B : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℂ → ℂ) (τ h1 : ℂ), Work.PARIMPL.ParBounds h τ h1 A r →
      ‖h1‖ ≤ B → ∀ (lam R : ℝ) (a : ℂ), 0 < lam → a = (lam : ℂ) * Complex.I →
      ∀ u : ℂ, Work.PARIMPL.GoodTransitRot a h τ lam R u → ‖Work.Implosion.ecalPt a u‖ < r →
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        Complex.sinh (a * (u + (t : ℂ) * Work.Implosion.modelDisp a h u)) / a ∈ Complex.slitPlane) →
      ‖Work.Implosion.approxEcal a (τ - h1 / τ) (u + Work.Implosion.modelDisp a h u)
        - Work.Implosion.approxEcal a (τ - h1 / τ) u + τ‖
        ≤ C * (‖Work.Implosion.ecalPt a u‖ ^ 2 + lam ^ 2) := by
  set C₀ : ℝ := |2*B + 2*A + (B + A)^2 + B*(1 + B) + A + (1 + B)*A + 9*(1 + B)/8
      + 32*(1 + (1 + B)/4) + 9*(1 + B)/2| with hC₀def
  refine ⟨C₀, ?_, ?_⟩
  · rw [hC₀def]; exact abs_nonneg _
  intro h τ h1 hb hB
  set κ : ℂ := τ - h1 / τ with hκdef
  have hτnorm : ‖τ‖ = 1 := hb.2.1
  let K : ℝ := 2*B + 2*A + (B + A)^2 + B*(1 + B) + A + (1 + B)*A + 9*(1 + B)/8
  have hKbound : ∀ (ζ hz a' κ' : ℂ), κ' = τ - h1 / τ →
      ‖hz - τ - h1 * ζ‖ ≤ A * ‖ζ‖ ^ 2 → ‖hz‖ ≤ 3 / 2 → ‖ζ‖ ≤ 1 / 4 → ‖a'‖ ≤ 1 / 4 →
      ‖τ - hz + ζ * hz ^ 2 - κ' * ζ * hz - κ' * a' * ζ * hz ^ 2‖
        ≤ K * (‖ζ‖ ^ 2 + ‖a'‖ ^ 2) :=
    norm_S_le_rot_B h1 τ A B hA hτnorm hB
  let C : ℝ := K + 32*(1 + ‖κ‖/4) + 9*‖κ‖/2
  intro lam R a hlam ha u hgt hzr hslit
  subst ha
  obtain ⟨hstrip, hR4, hsmall, hhτ, hh1, hh2, hZslit⟩ := hgt
  rw [mem_transitStrip_iff] at hstrip
  obtain ⟨hstr1, hstr2⟩ := hstrip
  have hane : ((lam : ℂ) * I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast ne_of_gt hlam) Complex.I_ne_zero
  have hna : ‖((lam : ℂ) * I)‖ = lam := by
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_of_nonneg hlam.le]
  set ζ : ℂ := ecalPt ((lam : ℂ) * I) u with hζdef
  set Φ : ℂ := modelDisp ((lam : ℂ) * I) h u with hΦdef
  simp only [approxEcal]
  set W : ℂ := Complex.sinh (((lam : ℂ) * I) * (u + Φ)) / ((lam : ℂ) * I) with hWdef
  set Z : ℂ := Complex.sinh (((lam : ℂ) * I) * u) / ((lam : ℂ) * I) with hZdef
  have hsum : ‖ζ‖ + lam ≤ 1/4 := by linarith [hsmall]
  have hζle : ‖ζ‖ ≤ 1/4 := by linarith [hsum, norm_nonneg ζ]
  have hlamle : lam ≤ 1/4 := by linarith [hsum, norm_nonneg ζ]
  have hζ3 : ‖h ζ‖ ≤ 3/2 := by
    calc ‖h ζ‖ = ‖(h ζ - τ) + τ‖ := by ring_nf
      _ ≤ ‖h ζ - τ‖ + ‖τ‖ := norm_add_le _ _
      _ ≤ 1/2 + 1 := by rw [hτnorm]; linarith
      _ = 3/2 := by norm_num
  have hζr : ‖ζ‖ < r := by simpa [← hζdef] using hzr
  have he : ‖h ζ - τ - h1*ζ‖ ≤ A*‖ζ‖^2 := hb.2.2.1 ζ hζr
  have hRΦ : ‖Φ + h ζ - ζ*h ζ^2‖ ≤ 32*(‖ζ‖^2 + lam^2) := by
    have h4 : 4 * (‖ecalPt ((lam:ℂ)*I) u‖ + ‖((lam:ℂ)*I)‖) ≤ 1 := by
      have hζ' : ‖ecalPt ((lam:ℂ)*I) u‖ = ‖ζ‖ := by rw [← hζdef]
      rw [hζ', hna]; exact hsmall
    have hres := modelDisp_second_order ((lam:ℂ)*I) h u hane h4 hh2
    simpa [← hΦdef, ← hζdef, hna] using hres
  have hΦn : ‖Φ‖ ≤ 65/16 := by
    have h1 : Φ = (Φ + h ζ - ζ*h ζ^2) - h ζ + ζ*h ζ^2 := by ring
    have htri : ‖(Φ + h ζ - ζ*h ζ^2) - h ζ + ζ*h ζ^2‖
        ≤ ‖Φ + h ζ - ζ*h ζ^2‖ + ‖h ζ‖ + ‖ζ*h ζ^2‖ := by
      have hadd := norm_add_le ((Φ + h ζ - ζ*h ζ^2) - h ζ) (ζ*h ζ^2)
      have hsub2 := norm_sub_le (Φ + h ζ - ζ*h ζ^2) (h ζ)
      linarith [hadd, hsub2]
    have h32 : 32*(‖ζ‖^2 + lam^2) ≤ 2 := by nlinarith [hsum, norm_nonneg ζ]
    have hz1 : ‖ζ*h ζ^2‖ ≤ (1/4)*(3/2)^2 := by
      rw [norm_mul, norm_pow]
      have h2 : ‖h ζ‖^2 ≤ (3/2)^2 := pow_le_pow_left₀ (norm_nonneg _) hζ3 2
      nlinarith [hζle, h2, norm_nonneg ζ]
    rw [h1]
    linarith [htri, hRΦ, h32, hz1, hζ3]
  have hA2decomp : dispNum2 ((lam:ℂ)*I) h u = (ζ + (lam:ℂ)*I) * h ζ := by
    rw [show dispNum2 ((lam:ℂ)*I) h u
        = (ecalPt ((lam:ℂ)*I) u + (lam:ℂ)*I) * h (ecalPt ((lam:ℂ)*I) u) from rfl,
      ← hζdef]
  have hA1decomp : dispNum1 ((lam:ℂ)*I) h u = (ζ - (lam:ℂ)*I) * h ζ := by
    rw [show dispNum1 ((lam:ℂ)*I) h u
        = (ecalPt ((lam:ℂ)*I) u - (lam:ℂ)*I) * h (ecalPt ((lam:ℂ)*I) u) from rfl,
      ← hζdef]
  have hA2le : ‖dispNum2 ((lam:ℂ)*I) h u‖ ≤ (‖ζ‖ + lam)*(3/2) := by
    rw [hA2decomp, norm_mul]
    have h1' : ‖ζ + ((lam:ℂ)*I)‖ ≤ ‖ζ‖ + lam := by
      have := norm_add_le ζ ((lam:ℂ)*I); rwa [hna] at this
    exact mul_le_mul h1' hζ3 (norm_nonneg _) (by positivity)
  have hA2n : ‖dispNum2 ((lam:ℂ)*I) h u‖ ≤ 3/8 := by
    calc ‖dispNum2 ((lam:ℂ)*I) h u‖ ≤ (‖ζ‖ + lam)*(3/2) := hA2le
      _ ≤ 3/8 := by nlinarith [hsum]
  have hA1le : ‖dispNum1 ((lam:ℂ)*I) h u‖ ≤ (‖ζ‖ + lam)*(3/2) := by
    rw [hA1decomp, norm_mul]
    have h1' : ‖ζ - ((lam:ℂ)*I)‖ ≤ ‖ζ‖ + lam := by
      have := norm_sub_le ζ ((lam:ℂ)*I); rwa [hna] at this
    exact mul_le_mul h1' hζ3 (norm_nonneg _) (by positivity)
  have hA1n : ‖dispNum1 ((lam:ℂ)*I) h u‖ ≤ 3/8 := by
    calc ‖dispNum1 ((lam:ℂ)*I) h u‖ ≤ (‖ζ‖ + lam)*(3/2) := hA1le
      _ ≤ 3/8 := by nlinarith [hsum]
  have hA2small : ‖dispNum2 ((lam:ℂ)*I) h u‖ ≤ 1/2 := by linarith
  have hA1ne : 1 + dispNum1 ((lam:ℂ)*I) h u ≠ 0 := by
    intro hh
    have h2 : dispNum1 ((lam:ℂ)*I) h u = -1 := by linear_combination hh
    rw [h2, norm_neg, norm_one] at hA1n
    linarith
  have hA2ne : 1 + dispNum2 ((lam:ℂ)*I) h u ≠ 0 := by
    intro hh
    have h2 : dispNum2 ((lam:ℂ)*I) h u = -1 := by linear_combination hh
    rw [h2, norm_neg, norm_one] at hA2n
    linarith
  have hEne : ecalE ((lam:ℂ)*I) u ≠ 1 := by
    intro hE
    have hmem : u ∈ periodLattice ((lam:ℂ)*I) := hE
    rw [mem_periodLattice_iff _ _ hane] at hmem
    obtain ⟨n, hn⟩ := hmem
    have hratio : Real.pi * I / ((lam:ℂ)*I) = ((Real.pi/lam : ℝ) : ℂ) := by
      rw [mul_div_mul_right _ _ Complex.I_ne_zero]
      exact (Complex.ofReal_div _ _).symm
    rw [hratio] at hn
    have hure : u.re = (n:ℝ) * (Real.pi/lam) := by
      rw [hn]; simp [Complex.mul_re]
    have hπ : 0 < Real.pi/lam := div_pos Real.pi_pos hlam
    have h1' : (n:ℝ) * (Real.pi/lam) ≥ R := by rw [← hure]; exact hstr1
    have hpos : 0 < (n:ℝ) := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [h1', hπ, hR4]
    have hposZ : (0:ℤ) < n := by exact_mod_cast hpos
    have hn1 : (1:ℤ) ≤ n := Int.lt_iff_add_one_le.mp hposZ
    have hn1R : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    have h2' : u.re ≥ Real.pi/lam := by
      rw [hure]; nlinarith [hn1R, hπ]
    linarith [hstr2, h2']
  have hWslit : W ∈ Complex.slitPlane := by
    have hh := hslit 1 (by norm_num)
    simpa [hWdef, hΦdef] using hh
  have hZre : 0 < Z.re := by
    rw [hZdef]
    exact sinh_mul_I_div_re_pos lam R hlam hR4 u hstr1 hstr2
  have hWne : W ≠ 0 := Complex.slitPlane_ne_zero hWslit
  have hZne : Z ≠ 0 := Complex.slitPlane_ne_zero hZslit
  have hiden : W * (1 + dispNum2 ((lam:ℂ)*I) h u)
      = Z * Complex.exp (-(((lam:ℂ)*I) * Φ)) := by
    rw [hWdef, hZdef, hΦdef]
    exact sinh_modelDisp_identity ((lam:ℂ)*I) h u hane hA1ne hA2ne hEne
  have hΔ : Complex.log W - Complex.log Z
      = -(((lam:ℂ)*I) * Φ) - Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u) := by
    refine eq_of_exp_eq_of_im_lt (Complex.log W - Complex.log Z)
      (-(((lam:ℂ)*I) * Φ) - Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)) ?_ ?_
    · rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_log hWne, Complex.exp_log hZne,
        Complex.exp_log hA2ne]
      rw [div_eq_div_iff hZne hA2ne]
      rw [hiden]; ring
    · have hWpi : W.arg < Real.pi := by
        have hWslit' : 0 < W.re ∨ W.im ≠ 0 := hWslit
        rw [Complex.arg_lt_pi_iff]
        rcases hWslit' with hh | hh
        · exact Or.inl (le_of_lt hh)
        · exact Or.inr hh
      have hargW : |W.arg| < Real.pi := (abs_lt).mpr ⟨Complex.neg_pi_lt_arg W, hWpi⟩
      have hargZ : |Z.arg| < Real.pi/2 :=
        Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hZre)
      have hImval : ((Complex.log W - Complex.log Z)
          - (-(((lam:ℂ)*I) * Φ) - Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u))).im
          = W.arg - Z.arg + (((lam:ℂ)*I) * Φ).im
            + (Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im := by
        simp only [Complex.sub_im, Complex.neg_im, Complex.log_im]
        ring
      rw [hImval]
      have haΦ : |((((lam:ℂ)*I) * Φ)).im| ≤ lam*(65/16) := by
        calc |((((lam:ℂ)*I) * Φ)).im| ≤ ‖((lam:ℂ)*I) * Φ‖ := Complex.abs_im_le_norm _
          _ = ‖((lam:ℂ)*I)‖ * ‖Φ‖ := norm_mul _ _
          _ = lam * ‖Φ‖ := by rw [hna]
          _ ≤ lam*(65/16) := by gcongr
      have hLa2 : |(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im| ≤ 33/64 := by
        have hlog : ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
            - dispNum2 ((lam:ℂ)*I) h u‖ ≤ ‖dispNum2 ((lam:ℂ)*I) h u‖^2 :=
          norm_log_one_add_sub_self_le_of_le_half hA2small
        have h1' : ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)‖
            ≤ ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
              - dispNum2 ((lam:ℂ)*I) h u‖ + ‖dispNum2 ((lam:ℂ)*I) h u‖ := by
          have h := norm_add_le (Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
            - dispNum2 ((lam:ℂ)*I) h u) (dispNum2 ((lam:ℂ)*I) h u)
          rwa [sub_add_cancel] at h
        have hnorm : ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)‖ ≤ 33/64 := by
          nlinarith [h1', hlog, hA2n, sq_nonneg ‖dispNum2 ((lam:ℂ)*I) h u‖,
            norm_nonneg (dispNum2 ((lam:ℂ)*I) h u)]
        have h2 := Complex.abs_im_le_norm (Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u))
        linarith [h2, hnorm]
      have htri : |W.arg - Z.arg + (((lam:ℂ)*I) * Φ).im
          + (Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im|
          ≤ |W.arg - Z.arg| + |((((lam:ℂ)*I) * Φ)).im|
            + |(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im| := by
        have h1 := abs_add_le (W.arg - Z.arg + (((lam:ℂ)*I) * Φ).im)
          ((Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im)
        have h2 := abs_add_le (W.arg - Z.arg) ((((lam:ℂ)*I) * Φ).im)
        linarith [h1, h2]
      have hsub : |W.arg - Z.arg| ≤ |W.arg| + |Z.arg| := by
        calc |W.arg - Z.arg| = |W.arg + (-Z.arg)| := by rw [sub_eq_add_neg]
          _ ≤ |W.arg| + |-Z.arg| := abs_add_le _ _
          _ = |W.arg| + |Z.arg| := by rw [abs_neg]
      have hpi : (49:ℝ)/16 < Real.pi := lt_trans (by norm_num) Real.pi_gt_d20
      linarith [htri, hsub, hargW, hargZ, haΦ, hLa2, hpi]
  have happrox : (u + Φ) + κ*Complex.log W - (u + κ*Complex.log Z) + τ
      = Φ + κ*(Complex.log W - Complex.log Z) + τ := by ring
  rw [happrox, hΔ]
  have hsimpl : Φ + κ*(-(((lam:ℂ)*I) * Φ) - Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)) + τ
      = (1 - κ*((lam:ℂ)*I))*Φ + τ - κ*Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u) := by ring
  rw [hsimpl]
  set S : ℂ := τ - (1 - κ*((lam:ℂ)*I))*(h ζ) + (1 - κ*((lam:ℂ)*I))*ζ*(h ζ)^2
      - κ*(ζ + ((lam:ℂ)*I))*(h ζ) with hSdef
  have hdecomp : (1 - κ*((lam:ℂ)*I))*Φ + τ - κ*Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
      = S + (1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)
        - κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u) - dispNum2 ((lam:ℂ)*I) h u) := by
    rw [hSdef, hA2decomp]; ring
  rw [hdecomp]
  have hSbound : ‖S‖ ≤ K * (‖ζ‖^2 + lam^2) := by
    have hconv : S = τ - h ζ + ζ*(h ζ)^2 - κ*ζ*(h ζ) - κ*((lam:ℂ)*I)*ζ*(h ζ)^2 := by
      rw [hSdef]; ring
    rw [hconv]
    have hres := hKbound ζ (h ζ) ((lam:ℂ)*I) κ hκdef he hζ3 hζle
      (by rw [hna]; exact hlamle)
    simpa [hna] using hres
  have hRΦb : ‖(1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)‖
      ≤ 32*(1+‖κ‖/4)*(‖ζ‖^2 + lam^2) := by
    rw [norm_mul]
    have hconst : ‖1 - κ*((lam:ℂ)*I)‖ ≤ 1 + ‖κ‖/4 := by
      calc ‖1 - κ*((lam:ℂ)*I)‖ ≤ ‖(1:ℂ)‖ + ‖κ*((lam:ℂ)*I)‖ := norm_sub_le _ _
        _ = 1 + ‖κ‖*lam := by rw [norm_one, norm_mul, hna]
        _ ≤ 1 + ‖κ‖/4 := by nlinarith [hlamle, norm_nonneg κ]
    calc ‖1 - κ*((lam:ℂ)*I)‖ * ‖Φ + h ζ - ζ*(h ζ)^2‖
        ≤ (1 + ‖κ‖/4) * (32*(‖ζ‖^2+lam^2)) := by gcongr
      _ = 32*(1+‖κ‖/4)*(‖ζ‖^2+lam^2) := by ring
  have hA22 : ‖dispNum2 ((lam:ℂ)*I) h u‖^2 ≤ (9/2)*(‖ζ‖^2 + lam^2) := by
    have h2 : ((‖ζ‖+lam)*(3/2))^2 ≤ (9/2)*(‖ζ‖^2+lam^2) := by
      nlinarith [sq_nonneg (‖ζ‖ - lam), norm_nonneg ζ]
    calc ‖dispNum2 ((lam:ℂ)*I) h u‖^2 ≤ ((‖ζ‖+lam)*(3/2))^2 :=
          pow_le_pow_left₀ (norm_nonneg _) hA2le 2
      _ ≤ (9/2)*(‖ζ‖^2+lam^2) := h2
  have hE2b : ‖κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
        - dispNum2 ((lam:ℂ)*I) h u)‖ ≤ (9*‖κ‖/2)*(‖ζ‖^2 + lam^2) := by
    rw [norm_mul]
    have hlog : ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
        - dispNum2 ((lam:ℂ)*I) h u‖ ≤ ‖dispNum2 ((lam:ℂ)*I) h u‖^2 :=
      norm_log_one_add_sub_self_le_of_le_half hA2small
    calc ‖κ‖ * ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
          - dispNum2 ((lam:ℂ)*I) h u‖
        ≤ ‖κ‖ * ‖dispNum2 ((lam:ℂ)*I) h u‖^2 := by gcongr
      _ ≤ ‖κ‖ * ((9/2)*(‖ζ‖^2+lam^2)) := by gcongr
      _ = (9*‖κ‖/2)*(‖ζ‖^2+lam^2) := by ring
  have hfin : ‖S + (1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)
        - κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
            - dispNum2 ((lam:ℂ)*I) h u)‖ ≤ C * (‖ζ‖^2 + lam^2) := by
    have htri2 : ‖S + (1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)
        - κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
            - dispNum2 ((lam:ℂ)*I) h u)‖
        ≤ ‖S‖ + ‖(1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)‖
          + ‖κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
              - dispNum2 ((lam:ℂ)*I) h u)‖ := by
      have hsub3 := norm_sub_le (S + (1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2))
        (κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
          - dispNum2 ((lam:ℂ)*I) h u))
      have hadd2 := norm_add_le S ((1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2))
      linarith [hsub3, hadd2]
    refine htri2.trans ?_
    have hCexp : C = K + 32*(1 + ‖κ‖/4) + 9*‖κ‖/2 := by dsimp only [C]
    rw [hCexp]
    nlinarith [hSbound, hRΦb, hE2b, sq_nonneg ‖ζ‖, sq_nonneg lam]
  have hκbB : ‖κ‖ ≤ 1 + B := by
    rw [hκdef]
    have hτ0 : τ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hτnorm; norm_num at hτnorm
    calc ‖τ - h1 / τ‖ ≤ ‖τ‖ + ‖h1 / τ‖ := norm_sub_le _ _
      _ = 1 + ‖h1‖ := by rw [norm_div, hτnorm, div_one]
      _ ≤ 1 + B := by linarith
  have hCle : C ≤ C₀ := by
    rw [hC₀def]
    have hCexp : C = K + 32*(1 + ‖κ‖/4) + 9*‖κ‖/2 := by dsimp only [C]
    rw [hCexp]
    have h1' : 32*(1 + ‖κ‖/4) + 9*‖κ‖/2 ≤ 32*(1 + (1 + B)/4) + 9*(1 + B)/2 := by
      nlinarith [hκbB]
    linarith [h1', le_abs_self (K + 32*(1 + (1 + B)/4) + 9*(1 + B)/2)]
  exact hfin.trans (mul_le_mul_of_nonneg_right hCle (by positivity))

end Work.PARIMPL2.Lavaurs

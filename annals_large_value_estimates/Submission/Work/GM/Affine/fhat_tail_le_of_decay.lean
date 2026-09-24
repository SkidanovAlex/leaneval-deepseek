import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.far_mass_le

/-!
# Tail `L²` bound for `Fhat f` from a single power-decay estimate (GM §9)

If `‖Fhat f ξ‖ ≤ B (T/|ξ|)^J` for every `ξ ≠ 0`, with `J ≥ 2`, `B ≥ 0` and `T > 0`, then the
`L²` mass of `Fhat f` outside the interval `(-Y, Y)` (`Y > 0`) is at most the integral of the
majorant `B² (T/|ξ|)^{2J}`, namely

  `2 B² T^{2J} / ((2J - 1) Y^{2J-1})`.

The mathematical content is the explicit evaluation of `∫_{|ξ| ≥ Y} (T/|ξ|)^{2J}`
(the lemma `integral_abs_div_pow` of `far_mass_le.lean`) together with monotonicity of the
set integral.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.GM.Affine

noncomputable section

theorem fhat_tail_le_of_decay {f : ℝ → ℝ} {B T Y : ℝ} {J : ℕ} (hJ : 2 ≤ J) (hB : 0 ≤ B)
    (hT : 0 < T) (hY : 0 < Y) (hint : MeasureTheory.Integrable (fun ξ : ℝ => ‖Work.GM.Affine.Fhat f ξ‖ ^ 2))
    (hdec : ∀ ξ : ℝ, ξ ≠ 0 → ‖Work.GM.Affine.Fhat f ξ‖ ≤ B * (T / |ξ|) ^ J) :
    ∫ ξ in {ξ : ℝ | Y ≤ |ξ|}, ‖Work.GM.Affine.Fhat f ξ‖ ^ 2
      ≤ 2 * B ^ 2 * T ^ (2 * J) / ((2 * J - 1) * Y ^ (2 * J - 1)) := by
  have h2J : 1 < 2 * J := by omega
  -- the majorant is integrable on `{|ξ| ≥ Y}`
  have hIntK : IntegrableOn (fun y : ℝ => (T / |y|) ^ (2 * J)) {y : ℝ | Y ≤ |y|} :=
    integrableOn_abs_div_pow hT hY h2J
  have hIntG : IntegrableOn (fun y : ℝ => B ^ 2 * (T / |y|) ^ (2 * J)) {y : ℝ | Y ≤ |y|} :=
    hIntK.const_mul (B ^ 2)
  -- pointwise comparison
  have hpoint : ∀ y ∈ {y : ℝ | Y ≤ |y|}, ‖Fhat f y‖ ^ 2 ≤ B ^ 2 * (T / |y|) ^ (2 * J) := by
    intro y hy
    have hy0 : 0 < |y| := lt_of_lt_of_le hY hy
    have hyne : y ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hy0
      exact lt_irrefl _ hy0
    have hd := hdec y hyne
    have hTy : 0 ≤ T / |y| := div_nonneg hT.le hy0.le
    have hA0 : 0 ≤ B * (T / |y|) ^ J := mul_nonneg hB (pow_nonneg hTy J)
    have hsq : ‖Fhat f y‖ ^ 2 ≤ (B * (T / |y|) ^ J) ^ 2 := by
      nlinarith [hd, norm_nonneg (Fhat f y), hA0]
    calc ‖Fhat f y‖ ^ 2 ≤ (B * (T / |y|) ^ J) ^ 2 := hsq
      _ = B ^ 2 * (T / |y|) ^ (2 * J) := by
          rw [mul_pow, ← pow_mul, Nat.mul_comm J 2]
  have hmono : ∫ y in {y : ℝ | Y ≤ |y|}, ‖Fhat f y‖ ^ 2 ≤
      ∫ y in {y : ℝ | Y ≤ |y|}, B ^ 2 * (T / |y|) ^ (2 * J) :=
    setIntegral_mono_of_nonneg (fun y _ => sq_nonneg _) hpoint hIntG
  -- value of the majorant integral
  have hvalK : ∫ y in {y : ℝ | Y ≤ |y|}, (T / |y|) ^ (2 * J)
      = 2 * T * (T / Y) ^ (2 * J - 1) / (((2 * J : ℕ) : ℝ) - 1) :=
    integral_abs_div_pow hT hY h2J
  have hvalG : ∫ y in {y : ℝ | Y ≤ |y|}, B ^ 2 * (T / |y|) ^ (2 * J)
      = B ^ 2 * (2 * T * (T / Y) ^ (2 * J - 1) / (((2 * J : ℕ) : ℝ) - 1)) := by
    rw [integral_const_mul, hvalK]
  have hmain : ∫ y in {y : ℝ | Y ≤ |y|}, ‖Fhat f y‖ ^ 2
      ≤ B ^ 2 * (2 * T * (T / Y) ^ (2 * J - 1) / (((2 * J : ℕ) : ℝ) - 1)) := by
    rw [hvalG] at hmono
    exact hmono
  refine le_trans hmain ?_
  -- elementary arithmetic
  have hcast : (((2 * J : ℕ) : ℝ) - 1) = ((2 * J - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * J), Nat.cast_one]
  have hTpow : T ^ (2 * J) = T * T ^ (2 * J - 1) := by
    conv_lhs => rw [show 2 * J = (2 * J - 1) + 1 by omega]
    rw [pow_succ']
  have hYne : Y ^ (2 * J - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hY)
  have hden : ((2 * J - 1 : ℕ) : ℝ) ≠ 0 := by
    have hpos : (0 : ℕ) < 2 * J - 1 := by omega
    exact_mod_cast ne_of_gt hpos
  rw [hcast, div_pow, hTpow]
  field_simp
  have hd2 : (2 : ℝ) * (J : ℝ) - 1 = ((2 * J - 1 : ℕ) : ℝ) := by
    rw [← hcast]; push_cast; ring
  rw [hd2]
  rw [mul_div_cancel_right₀ _ hden]

end

end Work.GM.Affine

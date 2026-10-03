import Mathlib
import Submission.Work.FITop.RCPrelude

namespace Work.FIPiChain.P2Rho

theorem ExpMulLogRpowLe (B B₀ : ℝ) (hB₀ : B₀ + 5 ≤ B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      Real.exp 1 * (Real.log (x : ℝ)) ^ (-(B + 2)) ≤ (Real.log (x : ℝ)) ^ (-B₀) := by
  -- Once `Real.log x ≥ 3` the inequality is elementary; `Real.log x → ∞` makes this eventual.
  have hlog : ∀ᶠ x : ℕ in Filter.atTop, (3 : ℝ) ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 3)
  filter_upwards [hlog] with x hx
  have ht0 : (0 : ℝ) < Real.log (x : ℝ) := by linarith
  have h1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by linarith
  -- The gap between the exponents is at least `7`.
  have hle : B₀ - B - 2 ≤ (-7 : ℝ) := by linarith
  have hpow : (Real.log (x : ℝ)) ^ (B₀ - B - 2) ≤ (Real.log (x : ℝ)) ^ (-7 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h1 hle
  -- `exp 1 ≤ (log x) ^ 7`, because `exp 1 < 3 ≤ log x ≤ (log x) ^ 7`.
  have he7 : Real.exp 1 ≤ (Real.log (x : ℝ)) ^ (7 : ℝ) := by
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h37 : (3 : ℝ) ≤ (Real.log (x : ℝ)) ^ (7 : ℝ) := by
      calc (3 : ℝ) ≤ Real.log (x : ℝ) := hx
        _ = (Real.log (x : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (Real.log (x : ℝ)) ^ (7 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    linarith
  have hmain : Real.exp 1 * (Real.log (x : ℝ)) ^ (-7 : ℝ) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right he7 (Real.rpow_nonneg (le_of_lt ht0) (-7))
    rw [← Real.rpow_add ht0 7 (-7)] at h
    simpa using h
  -- Split `-(B+2) = -B₀ + (B₀ - B - 2)` and compare termwise.
  have hstep : Real.exp 1 * (Real.log (x : ℝ)) ^ (-(B + 2))
      = Real.exp 1 * ((Real.log (x : ℝ)) ^ (-B₀) * (Real.log (x : ℝ)) ^ (B₀ - B - 2)) := by
    rw [show -(B + 2) = -B₀ + (B₀ - B - 2) by ring, Real.rpow_add ht0]
  rw [hstep]
  calc Real.exp 1 * ((Real.log (x : ℝ)) ^ (-B₀) * (Real.log (x : ℝ)) ^ (B₀ - B - 2))
      = (Real.exp 1 * (Real.log (x : ℝ)) ^ (B₀ - B - 2)) * (Real.log (x : ℝ)) ^ (-B₀) := by
        ring_nf
    _ ≤ (Real.exp 1 * (Real.log (x : ℝ)) ^ (-7 : ℝ)) * (Real.log (x : ℝ)) ^ (-B₀) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos 1)))
          (Real.rpow_nonneg (le_of_lt ht0) _)
    _ ≤ 1 * (Real.log (x : ℝ)) ^ (-B₀) :=
        mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg (le_of_lt ht0) _)
    _ = (Real.log (x : ℝ)) ^ (-B₀) := one_mul _

end Work.FIPiChain.P2Rho

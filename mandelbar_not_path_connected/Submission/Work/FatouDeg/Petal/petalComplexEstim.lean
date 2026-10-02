import Mathlib
import Submission.Work.FatouDeg.Petal.petalGeomDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

set_option linter.unusedVariables false

/-- The real part of a natural power written in polar form:
`((r * exp(θ i))^n).re = r^n * cos (n θ)`. -/
lemma re_pow_mul_exp_arg (r θ : ℝ) (n : ℕ) :
    (((r : ℂ) * Complex.exp (θ * Complex.I)) ^ n).re = r ^ n * Real.cos (n * θ) := by
  rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow]
  rw [show (↑n : ℂ) * (↑θ * Complex.I) = ↑((n : ℝ) * θ) * Complex.I by push_cast; ring]
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem petalComplexEstim (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) (M : ℝ) (hM : 0 ≤ M)
    (cm : ℝ) {z : ℂ} (hz : z ≠ 0) (hG : ‖G.eval z‖ ≤ M)
    (hcos : Real.cos (((m : ℝ) - 1) * z.arg) ≥ cm) :
    (z ^ (m - 1) * (1 - z * G.eval z)).re ≥ cm * ‖z‖ ^ (m - 1) - ‖z‖ ^ m * M ∧
      ‖z ^ (m - 1) * (1 - z * G.eval z)‖ ≤ ‖z‖ ^ (m - 1) * (1 + ‖z‖ * M) := by
  have hm1 : 1 ≤ m := by omega
  have hmcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm1]
    norm_num
  have hm_eq : (m - 1) + 1 = m := by omega
  -- polar form of `z`
  have hzr : z = (‖z‖ : ℂ) * Complex.exp (z.arg * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I z).symm
  -- the real part of `z ^ (m-1)`
  have hre : (z ^ (m - 1)).re = ‖z‖ ^ (m - 1) * Real.cos (((m : ℝ) - 1) * z.arg) := by
    have h1 : z ^ (m - 1) = ((‖z‖ : ℂ) * Complex.exp (z.arg * Complex.I)) ^ (m - 1) :=
      congrArg (fun w : ℂ => w ^ (m - 1)) hzr
    rw [h1, re_pow_mul_exp_arg, hmcast]
  have hr0 : (0 : ℝ) ≤ ‖z‖ ^ (m - 1) := by positivity
  have hre_ge : (z ^ (m - 1)).re ≥ cm * ‖z‖ ^ (m - 1) := by
    rw [hre]
    calc cm * ‖z‖ ^ (m - 1) = ‖z‖ ^ (m - 1) * cm := by ring
      _ ≤ ‖z‖ ^ (m - 1) * Real.cos (((m : ℝ) - 1) * z.arg) :=
            mul_le_mul_of_nonneg_left hcos hr0
  -- the second (error) term is bounded by `‖z‖^m * M`
  have hpow : ‖z‖ ^ m = ‖z‖ ^ (m - 1) * ‖z‖ := by
    conv_lhs => rw [← hm_eq]
    rw [pow_succ]
  have hBnorm : ‖z ^ (m - 1) * (z * G.eval z)‖ = ‖z‖ ^ m * ‖G.eval z‖ := by
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_pow, ← mul_assoc, ← hpow]
  have hB : (z ^ (m - 1) * (z * G.eval z)).re ≤ ‖z‖ ^ m * M := by
    calc (z ^ (m - 1) * (z * G.eval z)).re
        ≤ ‖z ^ (m - 1) * (z * G.eval z)‖ := Complex.re_le_norm _
      _ = ‖z‖ ^ m * ‖G.eval z‖ := hBnorm
      _ ≤ ‖z‖ ^ m * M := mul_le_mul_of_nonneg_left hG (by positivity)
  -- the first inequality
  have hmain : (z ^ (m - 1) * (1 - z * G.eval z)).re ≥ cm * ‖z‖ ^ (m - 1) - ‖z‖ ^ m * M := by
    have hfac : z ^ (m - 1) * (1 - z * G.eval z)
        = z ^ (m - 1) - z ^ (m - 1) * (z * G.eval z) := by ring
    rw [hfac, Complex.sub_re]
    linarith [hre_ge, hB]
  -- the second inequality
  have hnorm : ‖z ^ (m - 1) * (1 - z * G.eval z)‖ ≤ ‖z‖ ^ (m - 1) * (1 + ‖z‖ * M) := by
    rw [Complex.norm_mul, Complex.norm_pow]
    have h1 : ‖1 - z * G.eval z‖ ≤ 1 + ‖z‖ * M := by
      calc ‖1 - z * G.eval z‖ ≤ ‖(1 : ℂ)‖ + ‖z * G.eval z‖ := norm_sub_le _ _
        _ = 1 + ‖z‖ * ‖G.eval z‖ := by rw [Complex.norm_mul]; simp
        _ ≤ 1 + ‖z‖ * M := by
              have := mul_le_mul_of_nonneg_left hG (norm_nonneg z)
              linarith
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  exact ⟨hmain, hnorm⟩

end Work.FatouDeg.Petal

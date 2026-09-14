import Submission.Vdw.PerIrrTheta
import Submission.Vdw.WeylExpSum

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The §4 Fourier input is unconditional (elementary Weyl saving)

Main result: the paper's §4 index-condition input in the `δ`-parametrised form
`PerIrrTheta.PerrIrrBoundTheta` holds **unconditionally** at the threshold

    `δ = 2^{-n}/(2n)`   (`radical D ≤ H^{1+2^{-n}/(2n)}`),

with the constant depending only on `n`.  The only input is the elementary Weyl
bound for complete polynomial exponential sums, already in the shared commons
and turned into the per-prime power saving `θ = 2^{-n}` in
`Submission.Vdw.WeylExpSum`.

The three bookkeeping inequalities that the derivation needs are
`0 < θ ≤ 1`, `θ ≤ n`, `-1 < δ ≤ 1`, `0 < logGap n θ δ` and
`((n:ℝ)-1)(1+δ) ≤ n`; with `δ = θ/(2n)` they read

    `logGap n θ δ = θ(1+δ) - δn = θ/2 + θδ > 0`,
    `((n:ℝ)-1)(1+δ) = (n-1) + (n-1)δ ≤ (n-1) + 1/2 ≤ n`   (`n ≥ 3`).

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw
noncomputable section

/-- The Weyl saving exponent `θ = 2^{-n}`. -/
def weylθ (n : ℕ) : ℝ := (2:ℝ) ^ (-(n:ℝ))

/-- The associated Case-I radical threshold `δ = θ/(2n) = 2^{-n}/(2n)`; for
`n ≥ 3` this satisfies `δ ≲ θ/n`, the balance required by the multi-prime
congruence-density argument. -/
def weylδ (n : ℕ) : ℝ := weylθ n / (2 * (n : ℝ))

theorem weylθ_pos (n : ℕ) : 0 < weylθ n :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem weylθ_le_one (n : ℕ) : weylθ n ≤ 1 := by
  rw [weylθ]
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    (show -((n:ℝ)) ≤ 0 by exact neg_nonpos.mpr (Nat.cast_nonneg n))
  simpa using h

theorem weylδ_pos (n : ℕ) (hn : 1 ≤ n) : 0 < weylδ n := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  rw [weylδ]
  exact div_pos (weylθ_pos n) (by linarith)

theorem weylδ_le_one (n : ℕ) (hn : 1 ≤ n) : weylδ n ≤ 1 := by
  rw [weylδ]
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h : weylθ n / (2 * (n:ℝ)) ≤ 1 / (2 * (n:ℝ)) :=
    div_le_div_of_nonneg_right (weylθ_le_one n) (by linarith)
  have h2 : 1 / (2 * (n:ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  linarith

theorem weylδ_le (n : ℕ) (hn : 1 ≤ n) : weylδ n ≤ 1 / (2 * (n:ℝ)) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  exact div_le_div_of_nonneg_right (weylθ_le_one n) (by linarith)

theorem weylδ_mul_nat (n : ℕ) (hn : n ≠ 0) : weylδ n * (n:ℝ) = weylθ n / 2 := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  rw [weylδ]
  field_simp

theorem logGap_weyl_pos (n : ℕ) (hn : 1 ≤ n) : 0 < logGap n (weylθ n) (weylδ n) := by
  have hkey : logGap n (weylθ n) (weylδ n)
      = weylθ n * (1 + weylδ n) - weylδ n * (n:ℝ) := by
    rw [logGap]; ring
  rw [hkey, weylδ_mul_nat n (by omega)]
  nlinarith [weylθ_pos n, weylδ_pos n hn]

theorem weylδ_bookkeeping (n : ℕ) (hn : 3 ≤ n) :
    ((n:ℝ) - 1) * (1 + weylδ n) ≤ (n:ℝ) := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hprod : ((n:ℝ) - 1) * weylδ n ≤ 1 := by
    have h1 : ((n:ℝ) - 1) * weylδ n ≤ ((n:ℝ) - 1) * (1 / (2 * (n:ℝ))) :=
      mul_le_mul_of_nonneg_left (weylδ_le n (by omega)) (by linarith)
    have h2 : ((n:ℝ) - 1) * (1 / (2 * (n:ℝ))) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]
      linarith
    linarith
  nlinarith [hprod, hn1]

/-- `mIndexSaving_weyl` is exactly `MIndexBoundSaving` at `θ = 2^{-n}`. -/
theorem mIndexBoundSaving_weyl (n : ℕ) (hn : 1 ≤ n) : MIndexBoundSaving n (weylθ n) :=
  mIndexSaving_weyl n hn

/-- **The eventual §4 input at the Weyl threshold** — unconditional. -/
theorem perIrrBoundEvTheta_weyl (n : ℕ) (hn : 3 ≤ n) : PerIrrBoundEvTheta n (weylδ n) :=
  perIrrBoundEvTheta_of_MIndexBoundSaving n hn (weylθ n) (weylδ n)
    (weylθ_pos n) (weylθ_le_one n) (by
      have : (1:ℝ) ≤ (n:ℝ) := by
        have : 1 ≤ n := by omega
        exact_mod_cast this
      linarith [weylθ_le_one n])
    (weylδ_le_one n (by omega)) (by linarith [weylδ_pos n (by omega)])
    (logGap_weyl_pos n (by omega))
    (mIndexBoundSaving_weyl n (by omega))

/-- **The §4 index-condition input at the Weyl threshold** — unconditional, with
a constant depending only on `n`. -/
theorem perIrrBoundTheta_weyl (n : ℕ) (hn : 3 ≤ n) :
    ∃ c, 1 ≤ c ∧ PerIrrBoundTheta n (weylδ n) c :=
  perIrrBoundTheta_of_perIrrBoundEvTheta n hn (weylδ n)
    (by linarith [weylδ_pos n (by omega)])
    (weylδ_bookkeeping n hn) (perIrrBoundEvTheta_weyl n hn)

end
end Submission.Vdw

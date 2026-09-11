import Mathlib
import Submission.LogLemmas

/-!
# Fitting the final constant (base-1.9 lower bound vs the Finset bound)

In the last step of the whole proof we need:

  (w + r + 1) · (Ksf · r · log(2w))^w  ≤  (C · r³ · logb_{1.9} w · logb_{1.9}(logb_{1.9} w))^w

for all r ≥ 3, w ≥ 2, where Ksf = 2^72 and C is a huge absolute constant.
Everything here is pure real analysis; the module is imported by the final
`Submission.lean` assembly.
-/
open scoped BigOperators
open Real

namespace Submission.FinalFit

/-- Ksf constant (equals `Submission.Sun.Ksf` = 2^72). -/
noncomputable def KsfF : ℝ := 2 ^ 72

/-- the absolute constant C used in Theorem 1.4. -/
noncomputable def Cf : ℝ := 2 ^ 82

/-- `w + r + 1 ≤ r^w` for r ≥ 3, w ≥ 2 (real version). -/
lemma r_pow_ge {r w : ℕ} (hr : 3 ≤ r) (hw : 2 ≤ w) :
    (w + r + 1 : ℕ) ≤ r ^ w := by
  refine Nat.le_induction (m := 2) ?base ?step w hw
  · -- base w = 2 : r + 3 ≤ r^2
    calc
      2 + r + 1 = r + 3 := by omega
      _ ≤ 3 * r := by omega
      _ ≤ r * r := by exact Nat.mul_le_mul_right r hr
      _ = r ^ 2 := by rw [pow_two]
  · intro n hn ih
    calc
      (n + 1) + r + 1 = n + r + 2 := by omega
      _ ≤ 3 * (n + r + 1) := by omega
      _ ≤ 3 * r ^ n := by exact Nat.mul_le_mul_left 3 ih
      _ ≤ r * r ^ n := by exact Nat.mul_le_mul_right (r ^ n) hr
      _ = r ^ (n + 1) := by rw [pow_succ, mul_comm]

/-- main fitting inequality. -/
lemma fit_main {r w : ℕ} (hr : 3 ≤ r) (hw : 2 ≤ w) :
    ((w : ℝ) + (r : ℝ) + 1) * (KsfF * (r : ℝ) * Real.log (2 * (w : ℝ))) ^ w
      ≤ (Cf * (r : ℝ) ^ 3 * Real.logb (1.9 : ℝ) (w : ℝ) *
          Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ))) ^ w := by
  let L1 : ℝ := Real.logb (1.9 : ℝ) (w : ℝ)
  let L2 : ℝ := Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ))
  -- L1 > 0, L2 > 0
  have hL1 : 0 < L1 := by
    have h : (1 : ℝ) ≤ Real.logb (1.9 : ℝ) (w : ℝ) := by
      exact le_trans Submission.LogLemmas.logb19_two_ge_one
        (Submission.LogLemmas.logb19_w_ge_logb19_two hw)
    unfold L1
    linarith
  have hL2 : 0 < L2 := by
    unfold L2
    exact Submission.LogLemmas.logb19_logb19_w_pos hw
  -- r ≥ 3, w ≥ 2 as reals
  have hrR : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hwR : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hrge0 : 0 ≤ (r : ℝ) := by linarith
  have h2w1 : (1 : ℝ) ≤ 2 * (w : ℝ) := by nlinarith
  have hlogge0 : 0 ≤ Real.log (2 * (w : ℝ)) := Real.log_nonneg h2w1
  have hKge0 : 0 ≤ KsfF := by
    unfold KsfF
    norm_num
  -- the log-ratio bound, in L1/L2 notation
  have hlog : Real.log (2 * (w : ℝ)) ≤ 40 * L1 * L2 := by
    simpa [L1, L2] using (Submission.LogLemmas.log_ratio_bound hw)
  -- w + r + 1 ≤ r^w (real version)
  have h1 : ((w : ℝ) + (r : ℝ) + 1) ≤ (r : ℝ) ^ w := by
    exact_mod_cast (r_pow_ge hr hw)
  -- coefficient 40 * KsfF ≤ Cf * r
  have hcoef' : (40 : ℝ) * KsfF ≤ Cf * (r : ℝ) := by
    unfold KsfF Cf
    calc
      (40 : ℝ) * 2 ^ 72 ≤ (3 : ℝ) * 2 ^ 82 := by norm_num
      _ ≤ (r : ℝ) * 2 ^ 82 := by
        exact mul_le_mul_of_nonneg_right hrR (by norm_num : 0 ≤ (2 ^ 82 : ℝ))
      _ = (2 ^ 82 : ℝ) * (r : ℝ) := by ring
  -- 40 * KsfF * r² ≤ Cf * r³
  have hcoef'' : (40 : ℝ) * KsfF * (r : ℝ) ^ 2 ≤ Cf * (r : ℝ) ^ 3 := by
    calc
      (40 : ℝ) * KsfF * (r : ℝ) ^ 2 ≤ (Cf * (r : ℝ)) * (r : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_right hcoef' (sq_nonneg (r : ℝ))
      _ = Cf * (r : ℝ) ^ 3 := by ring
  -- final coefficient: (40 * KsfF * r²) * L1 * L2 ≤ (Cf * r³) * L1 * L2
  have hcoefFinal : (40 : ℝ) * KsfF * (r : ℝ) ^ 2 * L1 * L2 ≤
      Cf * (r : ℝ) ^ 3 * L1 * L2 := by
    have h1' := mul_le_mul_of_nonneg_right hcoef'' (le_of_lt hL1)
    exact mul_le_mul_of_nonneg_right h1' (le_of_lt hL2)
  -- nonnegativity of the "middle" base
  have hL1ge0 : 0 ≤ L1 := le_of_lt hL1
  have hL2ge0 : 0 ≤ L2 := le_of_lt hL2
  have hMge0 : 0 ≤ (40 : ℝ) * KsfF * (r : ℝ) ^ 2 * L1 * L2 := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (40 : ℝ)) hKge0) (sq_nonneg (r : ℝ)))
        hL1ge0) hL2ge0
  -- base of LHS power is nonnegative
  have hB1ge0 : 0 ≤ KsfF * (r : ℝ) * Real.log (2 * (w : ℝ)) := by
    exact mul_nonneg (mul_nonneg hKge0 hrge0) hlogge0
  calc
    ((w : ℝ) + (r : ℝ) + 1) * (KsfF * (r : ℝ) * Real.log (2 * (w : ℝ))) ^ w
        ≤ (r : ℝ) ^ w * (KsfF * (r : ℝ) * Real.log (2 * (w : ℝ))) ^ w := by
            exact mul_le_mul_of_nonneg_right h1 (pow_nonneg hB1ge0 w)
    _ = (KsfF * (r : ℝ) ^ 2 * Real.log (2 * (w : ℝ))) ^ w := by
            rw [← mul_pow]
            congr 1
            ring
    _ ≤ (KsfF * (r : ℝ) ^ 2 * (40 * L1 * L2)) ^ w := by
            have hb : KsfF * (r : ℝ) ^ 2 * Real.log (2 * (w : ℝ))
                ≤ KsfF * (r : ℝ) ^ 2 * (40 * L1 * L2) := by
              exact mul_le_mul_of_nonneg_left hlog (mul_nonneg hKge0 (sq_nonneg (r : ℝ)))
            have hbge : 0 ≤ KsfF * (r : ℝ) ^ 2 * Real.log (2 * (w : ℝ)) := by
              exact mul_nonneg (mul_nonneg hKge0 (sq_nonneg (r : ℝ))) hlogge0
            exact pow_le_pow_left₀ hbge hb w
    _ = ((40 : ℝ) * KsfF * (r : ℝ) ^ 2 * L1 * L2) ^ w := by
            congr 1
            ring
    _ ≤ (Cf * (r : ℝ) ^ 3 * L1 * L2) ^ w := by
            exact pow_le_pow_left₀ hMge0 hcoefFinal w

end Submission.FinalFit

import Mathlib
import Submission.Work.CNum.LgInfra
import Submission.Work.CNum.LgSerGe
import Submission.Work.CNum.LgRemGe
import Submission.Work.CNum.artanh_tail_le
import Submission.Work.ANum.hasSum_log_div
import Submission.Work.ANum.log_series_tail_sharp

/-!
# `Work.CNum.LgCoreUp` — the rounded-up artanh computation is an upper bound for `log`

`Work.CNum.lgCore n true` is, for `SC ≤ n ≤ 2·SC`, the fixed-point (scale `SC = 2^30`)
evaluation of `2 · artanh v` at the *upward* rounded artanh variable
`v = ⌈(n - SC)/(n + SC)⌉` (`v = lgvUp n`), namely

`lgCore n true = lgSer (lgvUp n) true + lgRem (lgvUp n) true`,

the partial sum of the artanh series with `LOGP` terms (every product/quotient rounded up,
`LgSerGe`) plus the outward-rounded geometric remainder estimate (`LgRemGe`).

Since `2 · artanh ((x-1)/(x+1)) = log x`, and the artanh variable of `x = m2r n` is
`(n - SC)/(n + SC) ≤ lgvUp n`, the whole computation over-estimates `log (m2r n)`: this is
the statement proved here.  The hypothesis `n ≤ 2·SC` is what makes the rounded variable
`m2r (lgvUp n)` stay below `1`, so that the geometric remainder is finite.

The proof is the chain
`log (m2r n) = log ((1+v)/(1-v)) ≤ log ((1+V)/(1-V))`
`  ≤ 2·(Σ_{i<LOGP} V^{2i+1}/(2i+1) + V^{2·LOGP+1}/((2·LOGP+1)(1-V²)))`
`  ≤ m2r (lgSer (lgvUp n) true) + m2r (lgRem (lgvUp n) true) = m2r (lgCore n true)`,
where `v = (n-SC)/(n+SC)`, `V = m2r (lgvUp n)`, the first inequality is the monotonicity of
`log` (with `v ≤ V < 1`), the second is the tail estimate `artanh_tail_le`, and the last one
uses the two soundness lemmas `LgSerGe` and `LgRemGe` for the rounded primitives.
-/

namespace Work.CNum

open Work.ANum

theorem LgCoreUp {n : ℤ} (h1 : Work.ANum.SC ≤ n) (h2 : n ≤ 2 * Work.ANum.SC) :
    Real.log (Work.ANum.m2r n) ≤ Work.ANum.m2r (Work.CNum.lgCore n true) := by
  -- the artanh denominator is positive
  have hSCpos : (0 : ℤ) < SC := SC_pos
  have hnpos : (0 : ℤ) < n + SC := by omega
  have hn0R : (0 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (le_trans (le_of_lt SC_pos) h1)
  have hden : (0 : ℝ) < (n : ℝ) + (SC : ℝ) := by linarith [SC_posR]
  have hdene : (n : ℝ) + (SC : ℝ) ≠ 0 := ne_of_gt hden
  -- the artanh variable `v = (n-SC)/(n+SC)` of `m2r n` lies in `[0,1)`
  have hv0 : 0 ≤ ((n : ℝ) - SC) / ((n : ℝ) + SC) := by
    apply div_nonneg _ hden.le
    have hSCn : (SC : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  have hv1 : ((n : ℝ) - SC) / ((n : ℝ) + SC) < 1 := by
    rw [div_lt_one hden]
    linarith [SC_posR]
  -- the rounded variable `V = m2r (lgvUp n)` dominates it ...
  have hVge : ((n : ℝ) - SC) / ((n : ℝ) + SC) ≤ m2r (lgvUp n) :=
    lgvUp_ge (n := n) hnpos
  -- ... and, since `n ≤ 2·SC`, stays strictly below `1`
  have hSC2 : (2 : ℤ) ≤ SC := by norm_num [Work.ANum.SC]
  have hn1 : n - SC ≤ SC := by omega
  have hB2 : 2 * SC ≤ n + SC := by omega
  have hA1 : (n - SC) * SC ≤ SC * SC := mul_le_mul_of_nonneg_right hn1 (le_of_lt SC_pos)
  have hA2 : (SC - 1) * (2 * SC) ≤ (SC - 1) * (n + SC) :=
    mul_le_mul_of_nonneg_left hB2 (by linarith : (0 : ℤ) ≤ SC - 1)
  have hA3 : SC * SC ≤ (SC - 1) * (2 * SC) := by nlinarith [hSC2]
  have hA : (n - SC) * SC ≤ (SC - 1) * (n + SC) := le_trans hA1 (le_trans hA3 hA2)
  have hlt : lgvUp n < SC := by
    have hle : (-SC + 1) ≤ -((n - SC) * SC) / (n + SC) := by
      rw [Int.le_ediv_iff_mul_le hnpos]
      nlinarith [hA]
    have hle2 : lgvUp n ≤ SC - 1 := by
      show -(-((n - SC) * SC) / (n + SC)) ≤ SC - 1
      have hneg := neg_le_neg hle
      have he : (-SC + 1 : ℤ) = -(SC - 1) := by ring
      rw [he] at hneg
      simpa using hneg
    omega
  have hVlt1 : m2r (lgvUp n) < 1 := by
    have h := m2r_lt hlt
    rwa [m2r_SC] at h
  have hV0 : 0 ≤ m2r (lgvUp n) := le_trans hv0 hVge
  have hvZ : 0 ≤ lgvUp n := (m2r_nonneg_iff _).mp hV0
  -- `log (m2r n)` is the log of the artanh quotient
  have hratio : (1 + ((n : ℝ) - SC) / ((n : ℝ) + SC)) /
      (1 - ((n : ℝ) - SC) / ((n : ℝ) + SC)) = m2r n := by
    have h1' : 1 - ((n : ℝ) - ↑SC) / ((n : ℝ) + ↑SC) = (2 * (SC : ℝ)) / ((n : ℝ) + ↑SC) := by
      rw [← div_self hdene, ← sub_div,
        show (n : ℝ) + ↑SC - ((n : ℝ) - ↑SC) = 2 * (SC : ℝ) from by ring]
    have h2' : 1 + ((n : ℝ) - ↑SC) / ((n : ℝ) + ↑SC) = (2 * (n : ℝ)) / ((n : ℝ) + ↑SC) := by
      rw [← div_self hdene, ← add_div,
        show (n : ℝ) + ↑SC + ((n : ℝ) - ↑SC) = 2 * (n : ℝ) from by ring]
    rw [h1', h2', m2r, div_div_div_cancel_right₀ hdene]
    exact mul_div_mul_left (n : ℝ) (SC : ℝ) (by norm_num : (2 : ℝ) ≠ 0)
  -- monotonicity of `log` between the two artanh variables
  have hlog1 : Real.log ((1 + ((n : ℝ) - SC) / ((n : ℝ) + SC)) /
        (1 - ((n : ℝ) - SC) / ((n : ℝ) + SC)))
      ≤ Real.log ((1 + m2r (lgvUp n)) / (1 - m2r (lgvUp n))) := by
    refine Real.log_le_log (div_pos (by linarith) (by linarith)) ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [hVge]
  -- the rounded-up partial sum dominates the exact partial sum at `V`
  have hSer : 2 * (∑ i ∈ Finset.range LOGP,
        (m2r (lgvUp n)) ^ (2 * i + 1) / (2 * (i : ℝ) + 1))
      ≤ m2r (lgSer (lgvUp n) true) :=
    LgSerGe (lgvUp n) hvZ
  -- the rounded-up remainder estimate dominates the geometric tail at `V`
  have hRem : 2 * ((m2r (lgvUp n)) ^ (2 * LOGP + 1) /
        ((2 * (LOGP : ℝ) + 1) * (1 - (m2r (lgvUp n)) ^ 2)))
      ≤ m2r (lgRem (lgvUp n) true) := by
    have h := LgRemGe (lgvUp n) hvZ hVlt1
    rwa [mul_div_assoc] at h
  -- the truncated series plus the geometric tail bound `log ((1+V)/(1-V))`
  have htail' : Real.log ((1 + m2r (lgvUp n)) / (1 - m2r (lgvUp n)))
      ≤ 2 * ((∑ i ∈ Finset.range LOGP,
            (m2r (lgvUp n)) ^ (2 * i + 1) / (2 * (i : ℝ) + 1))
          + (m2r (lgvUp n)) ^ (2 * LOGP + 1) /
            ((2 * (LOGP : ℝ) + 1) * (1 - (m2r (lgvUp n)) ^ 2))) := by
    have h := artanh_tail_le hV0 hVlt1 LOGP
    linarith [h]
  have hlg : lgCore n true = lgSer (lgvUp n) true + lgRem (lgvUp n) true := rfl
  calc Real.log (m2r n)
      = Real.log ((1 + ((n : ℝ) - SC) / ((n : ℝ) + SC)) /
          (1 - ((n : ℝ) - SC) / ((n : ℝ) + SC))) := by rw [hratio]
    _ ≤ Real.log ((1 + m2r (lgvUp n)) / (1 - m2r (lgvUp n))) := hlog1
    _ ≤ 2 * ((∑ i ∈ Finset.range LOGP,
            (m2r (lgvUp n)) ^ (2 * i + 1) / (2 * (i : ℝ) + 1))
          + (m2r (lgvUp n)) ^ (2 * LOGP + 1) /
            ((2 * (LOGP : ℝ) + 1) * (1 - (m2r (lgvUp n)) ^ 2))) := htail'
    _ = 2 * (∑ i ∈ Finset.range LOGP,
            (m2r (lgvUp n)) ^ (2 * i + 1) / (2 * (i : ℝ) + 1))
          + 2 * ((m2r (lgvUp n)) ^ (2 * LOGP + 1) /
            ((2 * (LOGP : ℝ) + 1) * (1 - (m2r (lgvUp n)) ^ 2))) := by ring
    _ ≤ m2r (lgSer (lgvUp n) true) + m2r (lgRem (lgvUp n) true) := add_le_add hSer hRem
    _ = m2r (lgCore n true) := by rw [hlg, m2r_add]

end Work.CNum

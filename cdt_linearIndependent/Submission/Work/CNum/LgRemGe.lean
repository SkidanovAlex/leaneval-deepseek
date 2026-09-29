import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.LgInfra

/-!
# `Work.CNum.LgRemGe` — the artanh remainder is never underestimated

`Work.CNum.lgRem v true` is the outward-rounded value (a `ℤ` mantissa at scale `SC = 2^30`) of
the remainder
`2 v^(2P+1) / ((2P+1)(1-v²))`  (`P = LOGP = 18`)

of the artanh series `2 Σ_{i<P} v^(2i+1)/(2i+1)`, as used by `lgCore` for the upper bound of
`log`.  Since the mantissa `q = powM true v LOGP` already over-approximates `(m2r v)^LOGP`, the
computed value is at least `2 (m2r v)^LOGP / ((2P+1)(1-(m2r v)²))`, which dominates the requested
remainder because `m2r v < 1` and `LOGP ≤ 2·LOGP+1`.

The proof is the chain
`2 x^(2P+1)/D ≤ 2 x^P/D ≤ 2 (m2r q)/D = num/(den·SC) ≤ ⌈num/den⌉/SC = m2r (lgRem v true)`,
where `x = m2r v`, `P = LOGP`, `D = (2P+1)(1-x²)`, `q = powM true v LOGP`,
`num = 2q·SC²` and `den = (2P+1)(SC² - v²)`; the last inequality is the ceiling-division
soundness `divUz_ge`.
-/

namespace Work.CNum

open Work.ANum

theorem LgRemGe (v : ℤ) (hv : 0 ≤ v) (hv1 : Work.ANum.m2r v < 1) :
    2 * (Work.ANum.m2r v) ^ (2 * LOGP + 1) / ((2 * (LOGP : ℝ) + 1) * (1 - (Work.ANum.m2r v) ^ 2)) ≤ Work.ANum.m2r (lgRem v true) := by
  set x : ℝ := m2r v with hx
  have hx0 : 0 ≤ x := by
    rw [hx]; simp only [m2r]; exact div_nonneg (by exact_mod_cast hv) SC_posR.le
  have hx1 : x < 1 := by rw [hx]; exact hv1
  have hx2 : x ^ 2 < 1 := by nlinarith
  have h1x2 : 0 < 1 - x ^ 2 := by linarith
  have hvx : (v : ℝ) = (SC : ℝ) * x := by
    rw [hx]; simp only [m2r]; rw [mul_div_cancel₀ _ (ne_of_gt SC_posR)]
  have hSv : (SC:ℝ)*(SC:ℝ) - (v:ℝ)*(v:ℝ) = (SC:ℝ)*(SC:ℝ)*(1 - x^2) := by rw [hvx]; ring
  have hSq : (0:ℤ) < SC*SC - v*v := by
    have hR : (0:ℝ) < ((SC*SC - v*v : ℤ) : ℝ) := by
      push_cast; rw [hSv]; exact mul_pos (mul_pos SC_posR SC_posR) h1x2
    exact_mod_cast hR
  have hdenpos : (0:ℤ) < ((2*LOGP+1:ℕ):ℤ) * (SC*SC - v*v) := by
    have h1 : (0:ℤ) < ((2*LOGP+1:ℕ):ℤ) := by
      exact_mod_cast (by norm_num [LOGP] : (0:ℕ) < 2*LOGP+1)
    exact mul_pos h1 hSq
  -- the ceiling division soundness: `lgRem` is `num/den` rounded up
  have hceil : m2r (2 * powM true v LOGP * (SC*SC)) /
        ((((2*LOGP+1:ℕ):ℤ) * (SC*SC - v*v)) : ℝ)
      ≤ m2r (divUz (2 * powM true v LOGP * (SC*SC))
        (((2*LOGP+1:ℕ):ℤ) * (SC*SC - v*v))) := by
    simpa using divUz_ge hdenpos (2 * powM true v LOGP * (SC*SC))
  -- the power computed by `powM` over-approximates `x ^ LOGP`
  have hpow : x ^ LOGP ≤ m2r (powM true v LOGP) := by
    have h := powM_true_ge (q := v) hx0 LOGP
    rwa [← hx] at h
  have hxpow : x ^ (2*LOGP+1) ≤ m2r (powM true v LOGP) :=
    le_trans (pow_le_pow_of_le_one hx0 hx1.le (by omega : LOGP ≤ 2*LOGP+1)) hpow
  have hDpos : 0 < (2*(LOGP:ℝ)+1) * (1 - x^2) :=
    mul_pos (by positivity) h1x2
  have hstep : 2 * x ^ (2*LOGP+1) / ((2*(LOGP:ℝ)+1)*(1-x^2))
      ≤ 2 * m2r (powM true v LOGP) / ((2*(LOGP:ℝ)+1)*(1-x^2)) := by
    apply div_le_div_of_nonneg_right _ hDpos.le
    linarith
  -- identification of the mantissa `lgRem` with `num/(den·SC)`
  have hkey : 2 * m2r (powM true v LOGP) / ((2*(LOGP:ℝ)+1)*(1-x^2))
      = m2r (2 * powM true v LOGP * (SC*SC)) /
        ((((2*LOGP+1:ℕ):ℤ) * (SC*SC - v*v)) : ℝ) := by
    simp only [m2r]
    push_cast
    rw [hSv]
    field_simp
  exact le_trans hstep (hkey ▸ hceil)

end Work.CNum

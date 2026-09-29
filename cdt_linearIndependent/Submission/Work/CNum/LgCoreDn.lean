import Mathlib
import Submission.Work.CNum.LgInfra
import Submission.Work.ANum.hasSum_log_div

/-!
# `Work.CNum.LgCoreDn` — the rounded-down artanh series is a lower bound for `log`

`Work.CNum.lgCore n false` is the fixed-point (scale `SC = 2^30`) evaluation of the artanh
series `2 Σ_{i < LOGP} v^{2i+1}/(2i+1)` at the *downward* rounded artanh variable
`v = ⌊(n - SC)/(n + SC)⌋`, with every product and quotient rounded downwards (`mulD`, `divD`).

Since `2 · artanh ((x-1)/(x+1)) = log x`, and since all the terms of the artanh series are
nonnegative for `0 ≤ v < 1`, the truncated downward-rounded sum never exceeds
`log (n/SC) = log (m2r n)`.  This module proves that (`LgCoreDn`), together with the invariant
which drives the induction:

* `lgSerAux_dn_le`: if the running mantissa `q` satisfies `m2r q ≤ (m2r v)^{2i+1}` and the
  squared step `v2` satisfies `m2r v2 ≤ (m2r v)^2` (with `v2 ≥ 0`), then
  `lgSerAux false v2 m q i acc` never exceeds `m2r acc` plus the exact partial sum
  `Σ_{k<m} (m2r v)^{2(i+k)+1}/(2(i+k)+1)`.

The companion upper bound (`lgSer v true ≥ …`) is `Work.CNum.LgSerGe`.
-/

namespace Work.CNum

open Work.ANum

/-- Soundness invariant of the rounded-down artanh partial sum.  If the current mantissa `q`
under-approximates `(m2r v)^{2i+1}` and the squared step `v2` under-approximates `(m2r v)^2`,
then `lgSerAux false v2 m q i acc` under-approximates the accumulator `m2r acc` plus the exact
partial sum of the artanh series up to `m` terms (all in mantissa units). -/
lemma lgSerAux_dn_le (v v2 : ℤ) (hv : 0 ≤ m2r v) (hv2n : 0 ≤ v2)
    (hv2 : m2r v2 ≤ (m2r v) ^ 2) :
    ∀ (m : ℕ) (q : ℤ) (i : ℕ) (acc : ℤ), m2r q ≤ (m2r v) ^ (2 * i + 1) →
      m2r (lgSerAux false v2 m q i acc) ≤
        m2r acc + ∑ k ∈ Finset.range m,
          (m2r v) ^ (2 * (i + k) + 1) / ↑(2 * (i + k) + 1) := by
  intro m
  induction m with
  | zero =>
      intro q i acc hq
      simp only [Finset.range_zero, Finset.sum_empty, add_zero]
      exact le_rfl
  | succ m ih =>
      intro q i acc hq
      have hstep : lgSerAux false v2 (m + 1) q i acc
          = lgSerAux false v2 m (mulD q v2) (i + 1) (acc + divD q (2 * i + 1)) := rfl
      rw [hstep]
      -- the next mantissa still under-approximates the next power of `m2r v`
      have hq' : m2r (mulD q v2) ≤ (m2r v) ^ (2 * (i + 1) + 1) := by
        have hexp : 2 * (i + 1) + 1 = (2 * i + 1) + 2 := by omega
        rw [hexp, pow_add]
        exact le_trans (mulD_le q v2)
          (mul_le_mul hq hv2 ((m2r_nonneg_iff v2).mpr hv2n) (pow_nonneg hv _))
      have ih' := ih (mulD q v2) (i + 1) (acc + divD q (2 * i + 1)) hq'
      -- the new term is dominated by the rounded quotient
      have hterm : m2r (divD q (2 * i + 1)) ≤ (m2r v) ^ (2 * i + 1) / ↑(2 * i + 1) := by
        calc m2r (divD q (2 * i + 1)) ≤ m2r q / ↑(2 * i + 1) := divD_le (by omega) q
          _ ≤ (m2r v) ^ (2 * i + 1) / ↑(2 * i + 1) :=
              div_le_div_of_nonneg_right hq (by positivity)
      rw [Finset.sum_range_succ']
      have hcongr : ∀ k, (m2r v) ^ (2 * (i + (k + 1)) + 1) / ↑(2 * (i + (k + 1)) + 1)
          = (m2r v) ^ (2 * ((i + 1) + k) + 1) / ↑(2 * ((i + 1) + k) + 1) := by
        intro k
        rw [show 2 * (i + (k + 1)) + 1 = 2 * ((i + 1) + k) + 1 by omega]
      rw [Finset.sum_congr rfl (fun k _ => hcongr k)]
      simp only [Nat.add_zero]
      rw [m2r_add] at ih'
      linarith [ih', hterm]

/-- `m2r (lgSer v false)` is at most `2` times the exact truncated artanh sum at `m2r v`. -/
lemma lgSer_dn_le (v : ℤ) (hv : 0 ≤ v) :
    m2r (lgSer v false) ≤
      2 * (∑ i ∈ Finset.range LOGP, (m2r v) ^ (2 * i + 1) / ↑(2 * i + 1)) := by
  have hv0 : 0 ≤ m2r v := div_nonneg (by exact_mod_cast hv) SC_posR.le
  have hv2n : 0 ≤ mulD v v := Int.ediv_nonneg (mul_nonneg hv hv) (le_of_lt SC_pos)
  have hv2 : m2r (mulD v v) ≤ (m2r v) ^ 2 := by
    rw [pow_two]; exact mulD_le v v
  have hsum := lgSerAux_dn_le v (mulD v v) hv0 hv2n hv2 LOGP v 0 0 (by norm_num)
  have hlg : lgSer v false = 2 * lgSerAux false (mulD v v) LOGP v 0 0 := rfl
  rw [hlg, m2r_two_mul]
  have hconv : (∑ k ∈ Finset.range LOGP, (m2r v) ^ (2 * (0 + k) + 1) / ↑(2 * (0 + k) + 1))
      = ∑ i ∈ Finset.range LOGP, (m2r v) ^ (2 * i + 1) / ↑(2 * i + 1) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show 2 * (0 + k) + 1 = 2 * k + 1 by omega]
  rw [hconv] at hsum
  simp only [m2r_zero, zero_add] at hsum
  linarith [hsum]

theorem LgCoreDn {n : ℤ} (h1 : Work.ANum.SC ≤ n) :
    Work.ANum.m2r (Work.CNum.lgCore n false) ≤ Real.log (Work.ANum.m2r n) := by
  have hden : (0 : ℝ) < (n : ℝ) + ↑SC := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (le_trans (le_of_lt SC_pos) h1)
    linarith [SC_posR]
  have hdene : (n : ℝ) + ↑SC ≠ 0 := ne_of_gt hden
  -- the artanh variable is nonnegative and below `1`
  have hvZ : 0 ≤ lgvDn n := by
    have hSCnn : (0 : ℤ) ≤ SC := le_of_lt SC_pos
    simp only [lgvDn]
    exact Int.ediv_nonneg (mul_nonneg (by omega) (le_of_lt SC_pos)) (by omega)
  have hu : 0 ≤ m2r (lgvDn n) := (m2r_nonneg_iff _).mpr hvZ
  have hu0 : m2r (lgvDn n) ≤ ((n : ℝ) - SC) / ((n : ℝ) + SC) := by
    have hSCposZ : (0 : ℤ) < SC := SC_pos
    exact lgvDn_le (by omega)
  have hu1' : ((n : ℝ) - SC) / ((n : ℝ) + SC) < 1 := by
    rw [div_lt_one hden]; linarith [SC_posR]
  have hu1 : m2r (lgvDn n) < 1 := lt_of_le_of_lt hu0 hu1'
  -- the artanh variable is the logarithm argument
  have hratio : (1 + ((n : ℝ) - SC) / ((n : ℝ) + SC)) / (1 - ((n : ℝ) - SC) / ((n : ℝ) + SC))
      = m2r n := by
    have h1 : 1 - ((n : ℝ) - ↑SC) / ((n : ℝ) + ↑SC) = (2 * (SC : ℝ)) / ((n : ℝ) + ↑SC) := by
      rw [← div_self hdene, ← sub_div,
        show (n : ℝ) + ↑SC - ((n : ℝ) - ↑SC) = 2 * (SC : ℝ) from by ring]
    have h2 : 1 + ((n : ℝ) - ↑SC) / ((n : ℝ) + ↑SC) = (2 * (n : ℝ)) / ((n : ℝ) + ↑SC) := by
      rw [← div_self hdene, ← add_div,
        show (n : ℝ) + ↑SC + ((n : ℝ) - ↑SC) = 2 * (n : ℝ) from by ring]
    rw [h1, h2, m2r, div_div_div_cancel_right₀ hdene]
    exact mul_div_mul_left (n : ℝ) (SC : ℝ) (by norm_num : (2 : ℝ) ≠ 0)
  -- the two halves of the estimate
  have hmain : m2r (lgCore n false) ≤
      2 * (∑ i ∈ Finset.range LOGP, (m2r (lgvDn n)) ^ (2 * i + 1) / ↑(2 * i + 1)) :=
    lgSer_dn_le (lgvDn n) hvZ
  have htail : 2 * (∑ i ∈ Finset.range LOGP, (m2r (lgvDn n)) ^ (2 * i + 1) / ↑(2 * i + 1)) ≤
      Real.log ((1 + ((n : ℝ) - SC) / ((n : ℝ) + SC)) /
        (1 - ((n : ℝ) - SC) / ((n : ℝ) + SC))) := by
    have h := Real.sum_range_le_log_div hu hu1 LOGP
    have hconv : (∑ i ∈ Finset.range LOGP, (m2r (lgvDn n)) ^ (2 * i + 1) / ↑(2 * i + 1))
        = ∑ i ∈ Finset.range LOGP, (m2r (lgvDn n)) ^ (2 * i + 1) / (2 * (i : ℝ) + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show (↑(2 * i + 1) : ℝ) = 2 * (i : ℝ) + 1 from by push_cast; ring]
    rw [← hconv] at h
    have hmono : (1 + m2r (lgvDn n)) / (1 - m2r (lgvDn n)) ≤
        (1 + ((n : ℝ) - SC) / ((n : ℝ) + SC)) / (1 - ((n : ℝ) - SC) / ((n : ℝ) + SC)) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith [hu, hu0, hu1']
    have hpos : 0 < (1 + m2r (lgvDn n)) / (1 - m2r (lgvDn n)) := by
      apply div_pos <;> linarith
    linarith [Real.log_le_log hpos hmono]
  calc m2r (lgCore n false)
      ≤ 2 * (∑ i ∈ Finset.range LOGP, (m2r (lgvDn n)) ^ (2 * i + 1) / ↑(2 * i + 1)) := hmain
    _ ≤ Real.log ((1 + ((n : ℝ) - SC) / ((n : ℝ) + SC)) /
          (1 - ((n : ℝ) - SC) / ((n : ℝ) + SC))) := htail
    _ = Real.log (m2r n) := by rw [hratio]

end Work.CNum

import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.LgInfra

/-!
# Soundness of the rounded artanh partial sum `lgSer`

`Work.CNum.lgSer v true` is the fixed-point evaluation of the artanh series
`2 Σ_{i < LOGP} v^{2i+1} / (2i+1)` in which every product and quotient is rounded *upwards*
(`mulU`, `divU`), so it must dominate the exact real partial sum.  This module proves exactly
that (`LgSerGe`), together with the functional invariant which drives the induction:

* `lgSerAux_sum_le`: if the running mantissa `q` satisfies `(m2r v)^{2i+1} ≤ m2r q` and the
  squared step `v2` dominates `(m2r v)^2`, then `m2r acc + Σ_{k<m} (m2r v)^{2(i+k)+1}/(2(i+k)+1)`
  is at most `m2r (lgSerAux true v2 m q i acc)`.
-/

namespace Work.CNum

open Work.ANum

/-- Soundness invariant of the rounded-up artanh partial sum.  If the current mantissa `q`
dominates `(m2r v)^{2i+1}` and the squared step `v2` dominates `(m2r v)^2`, then the
accumulator `acc` together with the exact tail of the series up to `m` terms is dominated by
the rounded mantissa `lgSerAux true v2 m q i acc` (all in mantissa units). -/
lemma lgSerAux_sum_le (v v2 : ℤ) (hv : 0 ≤ m2r v) (hv2 : (m2r v) ^ 2 ≤ m2r v2) :
    ∀ (m : ℕ) (q : ℤ) (i : ℕ) (acc : ℤ), (m2r v) ^ (2 * i + 1) ≤ m2r q →
      m2r acc + ∑ k ∈ Finset.range m, (m2r v) ^ (2 * (i + k) + 1) / ↑(2 * (i + k) + 1)
        ≤ m2r (lgSerAux true v2 m q i acc) := by
  intro m
  induction m with
  | zero =>
      intro q i acc hq
      simp only [Finset.range_zero, Finset.sum_empty, add_zero]
      exact le_rfl
  | succ m ih =>
      intro q i acc hq
      have hstep : lgSerAux true v2 (m + 1) q i acc
          = lgSerAux true v2 m (mulU q v2) (i + 1) (acc + divU q (2 * i + 1)) := rfl
      rw [hstep]
      -- the next mantissa still dominates the next power of `m2r v`
      have hq' : (m2r v) ^ (2 * (i + 1) + 1) ≤ m2r (mulU q v2) := by
        have hexp : 2 * (i + 1) + 1 = (2 * i + 1) + 2 := by omega
        rw [hexp, pow_add]
        exact le_trans (mul_le_mul hq hv2 (pow_nonneg hv 2)
              (le_trans (pow_nonneg hv _) hq)) (le_mulU q v2)
      have ih' := ih (mulU q v2) (i + 1) (acc + divU q (2 * i + 1)) hq'
      -- the new term is dominated by the rounded quotient
      have hterm : (m2r v) ^ (2 * i + 1) / ↑(2 * i + 1) ≤ m2r (divU q (2 * i + 1)) := by
        calc (m2r v) ^ (2 * i + 1) / ↑(2 * i + 1) ≤ m2r q / ↑(2 * i + 1) :=
              div_le_div_of_nonneg_right hq (by positivity)
          _ ≤ m2r (divU q (2 * i + 1)) := divU_ge (k := 2 * i + 1) (by omega) q
      rw [Finset.sum_range_succ']
      have hcongr : ∀ k, (m2r v) ^ (2 * (i + (k + 1)) + 1) / ↑(2 * (i + (k + 1)) + 1)
          = (m2r v) ^ (2 * ((i + 1) + k) + 1) / ↑(2 * ((i + 1) + k) + 1) := by
        intro k
        rw [show 2 * (i + (k + 1)) + 1 = 2 * ((i + 1) + k) + 1 by omega]
      rw [Finset.sum_congr rfl (fun k _ => hcongr k)]
      simp only [Nat.add_zero]
      rw [m2r_add] at ih'
      linarith [ih', hterm]

theorem LgSerGe (v : ℤ) (hv : 0 ≤ v) :
    2 * (∑ i ∈ Finset.range LOGP, (Work.ANum.m2r v) ^ (2 * i + 1) / (2 * i + 1)) ≤ Work.ANum.m2r (lgSer v true) := by
  have hv0 : 0 ≤ m2r v := div_nonneg (by exact_mod_cast hv) SC_posR.le
  have hv2 : (m2r v) ^ 2 ≤ m2r (mulU v v) := by rw [pow_two]; exact le_mulU v v
  have hsum := lgSerAux_sum_le v (mulU v v) hv0 hv2 LOGP v 0 0 (by simp)
  simp only [m2r_zero, zero_add] at hsum
  push_cast at hsum
  have hlg : lgSer v true = 2 * lgSerAux true (mulU v v) LOGP v 0 0 := rfl
  rw [hlg, m2r_two_mul]
  linarith [hsum]

end Work.CNum

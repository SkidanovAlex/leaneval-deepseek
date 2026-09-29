import Mathlib
import Submission.Work.CNum.LogUpMSpec

/-!
# `Work.CNum.LogUpMSpecPos` — `logUpM` soundness with the weak lower bound `1 ≤ hi`

`Work.CNum.logUpM hi` is an integer mantissa (at scale `SC = 2^30`) bounding `Real.log x` from
above for every `x ≤ hi/SC`, `x > 0`.  The file `Work.CNum.LogUpMSpec` proves this for
`SC/4 ≤ hi`; the certificate `Work.CNum.serUp` can call it with mantissas as small as `1`, and the
proof of the small branch only ever uses `1 ≤ hi`:

* large branch `SC ≤ hi`: unchanged;
* small branch `hi < SC`: `1 ≤ hi` gives `SC²/hi ≤ 2^60`, which is all that is needed to invoke
  `lgDn_spec`.
-/

namespace Work.CNum

open Work.ANum

/-- **`logUpM` soundness, sharpened.**  If `1 ≤ hi ≤ 2^60` then `m2r (logUpM hi)` bounds
`Real.log x` from above for every `x ≤ m2r hi` with `x > 0`. -/
theorem LogUpMSpec_pos {hi : ℤ} (h1 : 1 ≤ hi) (h2 : hi ≤ 2 ^ 60) {x : ℝ}
    (hx : x ≤ m2r hi) (hx0 : 0 < x) : Real.log x ≤ m2r (logUpM hi) := by
  by_cases hSC : SC ≤ hi
  · have hlog : logUpM hi = lgUp hi := by unfold logUpM; rw [if_pos hSC]
    rw [hlog]
    exact le_trans (Real.log_le_log hx0 hx) (lgUp_spec hSC h2)
  · have hlt : hi < SC := lt_of_not_ge hSC
    have hlog : logUpM hi = -lgDn (Int.ediv (SC * SC) hi) := by unfold logUpM; rw [if_neg hSC]
    rw [hlog, m2r_neg]
    have hhipos : 0 < hi := lt_of_lt_of_le zero_lt_one h1
    have hmul1 : SC * hi ≤ SC * SC := by
      have : (0:ℤ) ≤ SC := SC_pos.le
      nlinarith
    set m := Int.ediv (SC * SC) hi with hm
    have hmSC : SC ≤ m := by
      rw [hm]
      exact (Int.le_ediv_iff_mul_le hhipos (a := SC) (b := SC * SC) (c := hi)).mpr hmul1
    have hSC60 : SC * SC = 2 ^ 60 := by norm_num [SC]
    have hmul2 : SC * SC < 2 ^ 60 * hi + hi := by
      rw [hSC60]
      nlinarith
    have hm60 : m ≤ 2 ^ 60 := by
      rw [hm]
      exact (Int.ediv_le_iff_le_mul (k := hi) (x := SC * SC) (y := 2 ^ 60) hhipos).mpr hmul2
    have hmm : m2r m ≤ 1 / x := by
      have hmul : m * hi ≤ SC * SC := by
        rw [hm]; exact Int.ediv_mul_le (SC * SC) (ne_of_gt hhipos)
      have hmulR : (m : ℝ) * (hi : ℝ) ≤ (SC : ℝ) * (SC : ℝ) := by
        have hc : ((m * hi : ℤ) : ℝ) ≤ ((SC * SC : ℤ) : ℝ) := by exact_mod_cast hmul
        push_cast at hc
        exact hc
      have hhiR : (0 : ℝ) < (hi : ℝ) := by exact_mod_cast hhipos
      have hstep1 : m2r m ≤ (SC : ℝ) / (hi : ℝ) := by
        rw [m2r]
        rw [div_le_div_iff₀ SC_posR hhiR]
        linarith [hmulR]
      have hstep2 : (SC : ℝ) / (hi : ℝ) ≤ 1 / x := by
        have h1' : 1 / ((hi : ℝ) / (SC : ℝ)) ≤ 1 / x := one_div_le_one_div_of_le hx0 hx
        have h2' : 1 / ((hi : ℝ) / (SC : ℝ)) = (SC : ℝ) / (hi : ℝ) := by rw [one_div_div]
        linarith [h1', h2']
      linarith
    have hmpos : 0 < m2r m := (m2r_pos_iff m).mpr (lt_of_lt_of_le SC_pos hmSC)
    have hkey : m2r (lgDn m) ≤ -Real.log x := by
      have hspec := lgDn_spec hmSC hm60
      have h2' : Real.log (m2r m) ≤ Real.log (1 / x) := Real.log_le_log hmpos hmm
      simp only [one_div, Real.log_inv] at h2'
      linarith
    linarith

end Work.CNum

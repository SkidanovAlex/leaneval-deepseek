import Mathlib
import Submission.Work.CNum.LogUpMSpec

/-!
# `Work.CNum.LogDnMWeak` — `logDnM` soundness down to the mantissa `lo = 1`

`Work.CNum.logDnM lo` is an integer mantissa (at scale `SC = 2^30`) bounding `Real.log x` from
below for every `x ≥ lo/SC`, `x > 0`.  `Work.CNum.LogDnMSpec` proves this for `SC/4 ≤ lo`; the
certificates can call it with mantissas as small as `1`, and the proof of the small branch only
needs `1 ≤ lo`:

* large branch `SC ≤ lo`: unchanged (this is exactly `lgDn_spec`);
* small branch `lo < SC`: `1 ≤ lo` gives `⌈SC²/lo⌉ ≤ SC² = 2^60`, which is all that is needed
  to invoke `lgUp_spec` on the reciprocal endpoint.
-/

namespace Work.CNum

open Work.ANum

/-- **`logDnM` soundness, sharpened.**  If `1 ≤ lo ≤ 2^60` then `m2r (logDnM lo)` bounds
`Real.log x` from below for every `x ≥ m2r lo` with `x > 0`. -/
theorem LogDnMWeak {lo : ℤ} (h1 : 1 ≤ lo) (h2 : lo ≤ 2 ^ 60) {x : ℝ} (hx0 : 0 < x) (hx : Work.ANum.m2r lo ≤ x) : Work.ANum.m2r (Work.CNum.logDnM lo) ≤ Real.log x := by
  by_cases hSC : SC ≤ lo
  · -- large argument: `logDnM lo = lgDn lo`
    have hlog : logDnM lo = lgDn lo := by unfold logDnM; rw [if_pos hSC]
    rw [hlog]
    have hlo_pos : 0 < m2r lo := (m2r_pos_iff lo).mpr (lt_of_lt_of_le SC_pos hSC)
    exact le_trans (lgDn_spec hSC h2) (Real.log_le_log hlo_pos hx)
  · -- small argument: `lo < SC`, bound `log (1/x)` from above
    have hlt : lo < SC := lt_of_not_ge hSC
    have hlog : logDnM lo = -lgUp (-Int.ediv (-(SC * SC)) lo) := by
      unfold logDnM; rw [if_neg hSC]
    rw [hlog, m2r_neg]
    set m : ℤ := -(Int.ediv (-(SC * SC)) lo) with hm
    have hloc : 0 < lo := lt_of_lt_of_le zero_lt_one h1
    have hloR : 0 < m2r lo := (m2r_pos_iff lo).mpr hloc
    -- `m ≥ SC`
    have hmSC : SC ≤ m := by
      rw [hm]
      have hkey : lo * (SC - 1) < SC * SC := by
        have h1' : lo * (SC - 1) ≤ SC * (SC - 1) :=
          mul_le_mul_of_nonneg_right hlt.le (by linarith [SC_pos])
        nlinarith [h1', SC_pos]
      suffices h : Int.ediv (-(SC * SC)) lo ≤ -SC by linarith
      exact (Int.ediv_le_iff_le_mul hloc (x := -(SC * SC)) (y := -SC) (k := lo)).mpr
        (by nlinarith [hkey])
    -- `m ≤ 2^60` (this is where `1 ≤ lo` replaces `SC/4 ≤ lo`)
    have hm60 : m ≤ 2 ^ 60 := by
      rw [hm]
      have hle : -(SC * SC) ≤ Int.ediv (-(SC * SC)) lo :=
        (Int.le_ediv_iff_mul_le hloc (a := -(SC * SC)) (b := -(SC * SC)) (c := lo)).mpr
          (by nlinarith [h1, SC_pos])
      have hSCsq : SC * SC = 2 ^ 60 := by norm_num [SC]
      linarith
    -- `m · lo ≥ SC²`, i.e. `m ≥ ⌈SC²/lo⌉` has no rounding loss downwards
    have hmul : SC * SC ≤ m * lo := by
      rw [← neg_le_neg_iff]
      have he : -(m * lo) = Int.ediv (-(SC * SC)) lo * lo := by rw [hm]; ring
      rw [he]
      exact Int.ediv_mul_le (-(SC * SC)) (ne_of_gt hloc)
    have hone : (1 : ℝ) ≤ m2r m * m2r lo := by
      have h := m2r_le hmul
      rw [m2r_mul SC SC, m2r_SC, m2r_mul m lo] at h
      simp only [one_mul] at h
      exact le_of_mul_le_mul_left h SC_posR
    have hstep : 1 / x ≤ m2r m := by
      have hrec : 1 / m2r lo ≤ m2r m := by
        rw [div_le_iff₀ hloR]; linarith [hone]
      exact le_trans (one_div_le_one_div_of_le hloR hx) hrec
    have hlog1 : Real.log (1 / x) ≤ m2r (lgUp m) :=
      le_trans (Real.log_le_log (one_div_pos.mpr hx0) hstep) (lgUp_spec hmSC hm60)
    rw [one_div, Real.log_inv] at hlog1
    linarith

end Work.CNum

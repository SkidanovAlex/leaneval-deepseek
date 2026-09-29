import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.LogUpMSpec

/-!
# Soundness of the fixed-point logarithm `logDnM`

Mirror of `Work.CNum.LogUpMSpec` for the lower endpoint.  `Work.CNum.logDnM lo` is an integer
mantissa (at scale `SC = 2^30`) intended to bound `Real.log x` from below for every `x ≥ lo/SC`
with `x > 0`, provided `SC/4 ≤ lo ≤ 2^60` (see `Work.CNum.Fx`):

  `logDnM lo = if SC ≤ lo then lgDn lo else - lgUp ⌈SC²/lo⌉`.

* In the range `lo ≥ SC` we are in the "large argument" regime and `lgDn lo` bounds `log (lo/SC)`
  from below, whence `log x ≥ log(lo/SC) ≥ lgDn lo`.
* In the range `lo < SC` we have `x ≥ lo/SC < 1`, so `-log x = log(1/x)` and it suffices to bound
  `log (1/x)` from above.  Since `x ≥ lo/SC > 0` gives `1/x ≤ SC/lo ≤ ⌈SC²/lo⌉/SC`, the upper
  bound `lgUp` of `log` at `⌈SC²/lo⌉ ≥ SC` finishes the job.

The analytic cores are `Work.CNum.LgCoreUp` / `Work.CNum.LgCoreDn`, the normalisation is
`Work.CNum.LgNormSpec`, and the endpoint soundness lemmas `lgUp_spec` / `lgDn_spec` live in
`Submission.Work.CNum.LogUpMSpec`.
-/

namespace Work.CNum

open Work.ANum

/-- **The assignment.**  `logDnM` soundness: if `SC/4 ≤ lo ≤ 2^60`, then `m2r (logDnM lo)`
bounds `Real.log x` from below for every `x ≥ m2r lo` with `x > 0`. -/
theorem LogDnMSpec {lo : ℤ} (h1 : Work.ANum.SC / 4 ≤ lo) (h2 : lo ≤ 2 ^ 60) {x : ℝ} (hx0 : 0 < x) (hx : Work.ANum.m2r lo ≤ x) : Work.ANum.m2r (Work.CNum.logDnM lo) ≤ Real.log x := by
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
    have hquarter : SC / 4 = (2 : ℤ) ^ 28 := by norm_num [SC]
    have hloc : 0 < lo := by
      have h : (0 : ℤ) < (2 : ℤ) ^ 28 := by norm_num
      have h' : (2 : ℤ) ^ 28 ≤ lo := by rw [← hquarter]; exact h1
      linarith
    have hloR : 0 < m2r lo := (m2r_pos_iff lo).mpr hloc
    have hSC4 : SC ≤ 4 * lo := by
      have h4 : (4 : ℤ) * (SC / 4) = SC := by norm_num [SC]
      nlinarith [h1, h4]
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
    -- `m ≤ 4·SC`
    have hm4 : m ≤ 4 * SC := by
      rw [hm]
      suffices h : -(4 * SC) ≤ Int.ediv (-(SC * SC)) lo by linarith
      refine (Int.le_ediv_iff_mul_le hloc (a := -(4 * SC)) (b := -(SC * SC)) (c := lo)).mpr ?_
      have hSC4' : SC * SC ≤ 4 * lo * SC := mul_le_mul_of_nonneg_right hSC4 (le_of_lt SC_pos)
      nlinarith [hSC4']
    have hm60 : m ≤ 2 ^ 60 := by
      have h4SC : (4 : ℤ) * SC = 2 ^ 32 := by norm_num [SC]
      calc m ≤ 4 * SC := hm4
        _ = 2 ^ 32 := h4SC
        _ ≤ 2 ^ 60 := by norm_num
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
      have h2 : (SC : ℝ) * 1 ≤ (SC : ℝ) * (m2r m * m2r lo) := h
      exact le_of_mul_le_mul_left h2 SC_posR
    have hstep : 1 / x ≤ m2r m := by
      have hrec : 1 / m2r lo ≤ m2r m := by
        rw [div_le_iff₀ hloR]; linarith [hone]
      exact le_trans (one_div_le_one_div_of_le hloR hx) hrec
    have hlog1 : Real.log (1 / x) ≤ m2r (lgUp m) :=
      le_trans (Real.log_le_log (one_div_pos.mpr hx0) hstep) (lgUp_spec hmSC hm60)
    rw [one_div, Real.log_inv] at hlog1
    linarith

end Work.CNum

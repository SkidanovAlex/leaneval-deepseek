import Mathlib
import Submission.Work.CNum.LgInfra
import Submission.Work.CNum.LgCoreUp
import Submission.Work.CNum.LgCoreDn
import Submission.Work.CNum.LgNormSpec

/-!
# Soundness of the fixed-point logarithm `logUpM`

`Work.CNum.logUpM hi` is an integer mantissa (at scale `SC = 2^30`) intended to bound
`Real.log x` from above for every `x ≤ hi/SC` with `x > 0`, provided `SC/4 ≤ hi ≤ 2^60`
(see `Work.CNum.Fx`):

  `logUpM hi = if SC ≤ hi then lgUp hi else - lgDn (SC² / hi)`.

* In the range `hi ≥ SC` the value `lgUp hi` is `lgNorm·LOG2UP + lgCore (halveU ·) true + 2`:
  the mantissa is halved `lgNorm hi` times (rounded up, `halveU`) until it lands in
  `[SC, 2·SC]`, and on that last value the artanh series of `lgCore · true` is evaluated, the
  halvings being paid for by `lgNorm·LOG2UP ≥ lgNorm·log 2` and the `+2` (equal to `2/SC`)
  absorbing the rounding slack.
* In the range `hi < SC` we have `x < 1`, so `log x < 0` and it suffices to bound
  `log (SC²/hi) ≥ -log x = log(1/x)` from below by `lgDn`, whence
  `log x ≤ -lgDn (SC²/hi) = m2r (logUpM hi)`.

The analytic core is `Work.CNum.LgCoreUp` / `Work.CNum.LgCoreDn` (the artanh series plus its
tail), the normalisation fact is `Work.CNum.LgNormSpec`, and the rounding lemmas for the
primitives are in `Work.CNum.LgInfra`.
-/

namespace Work.CNum

open Work.ANum

/-- Soundness of `lgUp`: for `SC ≤ n ≤ 2^60` the mantissa `lgUp n` bounds `log (n/SC)` from
above. -/
theorem lgUp_spec {n : ℤ} (h1 : SC ≤ n) (h2 : n ≤ 2 ^ 60) :
    Real.log (m2r n) ≤ m2r (lgUp n) := by
  obtain ⟨hUlo, hUhi, hDlo, hDhi⟩ := LgNormSpec h1 h2
  have hn0 : 0 ≤ n := le_trans SC_pos.le h1
  have hnpos : 0 < m2r n := (m2r_pos_iff n).mpr (lt_of_lt_of_le SC_pos h1)
  have hlgUp : lgUp n = (lgNorm n : ℤ) * LOG2UP + lgCore (halveU (lgNorm n) n) true + 2 := by
    unfold lgUp
    rw [if_neg (not_lt.mpr h1)]
  rw [hlgUp]
  simp only [m2r_add]
  have hA : (lgNorm n : ℝ) * Real.log 2 ≤ m2r ((lgNorm n : ℤ) * LOG2UP) := by
    rw [m2r_mul_int']
    exact mul_le_mul_of_nonneg_left log_two_le_LOG2UP (by positivity)
  have hB : Real.log (m2r (halveU (lgNorm n) n)) ≤ m2r (lgCore (halveU (lgNorm n) n) true) :=
    LgCoreUp hUlo hUhi
  have hC : Real.log (m2r n) - (lgNorm n : ℝ) * Real.log 2
      ≤ Real.log (m2r (halveU (lgNorm n) n)) := by
    have hle := halveU_ge (lgNorm n) n hn0
    have hp2 : (0 : ℝ) < 2 ^ (lgNorm n) := by positivity
    have hp3 : 0 < m2r n / 2 ^ (lgNorm n) := div_pos hnpos hp2
    have hlog : Real.log (m2r n / 2 ^ (lgNorm n))
        = Real.log (m2r n) - (lgNorm n : ℝ) * Real.log 2 := by
      rw [Real.log_div (ne_of_gt hnpos) (ne_of_gt hp2), Real.log_pow]
    rw [← hlog]
    exact Real.log_le_log hp3 hle
  have h2pos : 0 ≤ m2r (2 : ℤ) := by rw [m2r_nonneg_iff]; norm_num
  linarith

/-- Soundness of `lgDn`: for `SC ≤ n ≤ 2^60` the mantissa `lgDn n` bounds `log (n/SC)` from
below. -/
theorem lgDn_spec {n : ℤ} (h1 : SC ≤ n) (h2 : n ≤ 2 ^ 60) :
    m2r (lgDn n) ≤ Real.log (m2r n) := by
  obtain ⟨hUlo, hUhi, hDlo, hDhi⟩ := LgNormSpec h1 h2
  have hn0 : 0 ≤ n := le_trans SC_pos.le h1
  have hnpos : 0 < m2r n := (m2r_pos_iff n).mpr (lt_of_lt_of_le SC_pos h1)
  have hlgDn : lgDn n = (lgNorm n : ℤ) * LOG2DN + lgCore (halveD (lgNorm n) n) false - 2 := by
    unfold lgDn
    rw [if_neg (not_lt.mpr h1)]
  rw [hlgDn]
  simp only [m2r_sub, m2r_add]
  have hA : m2r ((lgNorm n : ℤ) * LOG2DN) ≤ (lgNorm n : ℝ) * Real.log 2 := by
    rw [m2r_mul_int']
    exact mul_le_mul_of_nonneg_left LOG2DN_le_log_two (by positivity)
  have hB : m2r (lgCore (halveD (lgNorm n) n) false) ≤ Real.log (m2r (halveD (lgNorm n) n)) :=
    LgCoreDn hDlo
  have hC : Real.log (m2r (halveD (lgNorm n) n))
      ≤ Real.log (m2r n) - (lgNorm n : ℝ) * Real.log 2 := by
    have hle := halveD_le (lgNorm n) n hn0
    have hp3 : 0 < m2r (halveD (lgNorm n) n) :=
      (m2r_pos_iff _).mpr (lt_of_lt_of_le SC_pos hDlo)
    have hp2 : (0 : ℝ) < 2 ^ (lgNorm n) := by positivity
    have hlog : Real.log (m2r n / 2 ^ (lgNorm n))
        = Real.log (m2r n) - (lgNorm n : ℝ) * Real.log 2 := by
      rw [Real.log_div (ne_of_gt hnpos) (ne_of_gt hp2), Real.log_pow]
    rw [← hlog]
    exact Real.log_le_log hp3 hle
  have h2pos : 0 ≤ m2r (2 : ℤ) := by rw [m2r_nonneg_iff]; norm_num
  linarith

/-- **The assignment.**  `logUpM` soundness: if `SC/4 ≤ hi ≤ 2^60`, then `m2r (logUpM hi)`
bounds `Real.log x` from above for every `x ≤ m2r hi` with `x > 0`. -/
theorem LogUpMSpec {hi : ℤ} (h1 : Work.ANum.SC / 4 ≤ hi) (h2 : hi ≤ 2 ^ 60) {x : ℝ} (hx : x ≤ Work.ANum.m2r hi) (hx0 : 0 < x) : Real.log x ≤ Work.ANum.m2r (logUpM hi) := by
  by_cases hSC : SC ≤ hi
  · -- large argument: `logUpM hi = lgUp hi`
    have hlog : logUpM hi = lgUp hi := by unfold logUpM; rw [if_pos hSC]
    rw [hlog]
    exact le_trans (Real.log_le_log hx0 hx) (lgUp_spec hSC h2)
  · -- small argument: `x < 1`, so bound `log (1/x)` from below
    have hlt : hi < SC := lt_of_not_ge hSC
    have hlog : logUpM hi = -lgDn (Int.ediv (SC * SC) hi) := by unfold logUpM; rw [if_neg hSC]
    rw [hlog, m2r_neg]
    have hSc : SC = (2 : ℤ) ^ 30 := by norm_num [SC]
    have hhipos : 0 < hi := by have hh := h1; rw [hSc] at hh; norm_num at hh; linarith
    have h4 : (2 : ℤ) ^ 28 ≤ hi := by have hh := h1; rw [hSc] at hh; norm_num at hh ⊢; exact hh
    set m := Int.ediv (SC * SC) hi with hm
    have hmul1 : SC * hi ≤ SC * SC := by rw [hSc] at hlt ⊢; nlinarith
    have hmSC : SC ≤ m := by
      rw [hm]
      exact (Int.le_ediv_iff_mul_le hhipos (a := SC) (b := SC * SC) (c := hi)).mpr hmul1
    have hmul2 : SC * SC < 2 ^ 60 * hi + hi := by rw [hSc]; nlinarith [h4]
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

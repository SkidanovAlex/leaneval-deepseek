import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.Defs

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Classical

open scoped BigOperators

noncomputable section

/-- **The trivial (principal) strict character modulo `4d`**: `1` on the units modulo `4d`,
`0` off them.  Its Hecke `L`-function (weight `0`) is the one datum of the log-derivative bound
`heckeLSeries_logDeriv_bound_re_gt_one` whose completed function has a *pole* at `s = 1` (and not
an entire completion), namely `∏_{𝔭 ∤ 4d} (1 - N𝔭^{-s})^{-1} = ζ_K(s)·∏_{𝔭 | 4d}(1 - N𝔭^{-s})`. -/
def chiTriv (d : ℕ) : GaussianInt → ℂ := fun z =>
  if Work.FIArea5.S16Hecke.IsUnitMod4d d z then 1 else 0

/-- **Arithmetic comparison**: for `d ≥ 1`, `M ≥ 3` and `ε ≤ 1`,

  `log (4·d·M) + d^ε ≤ 6·d·(log M)²`.

The three ingredients are `log (4d) ≤ 4d`, `log M ≤ (log M)²` (as `log M ≥ 1`) and `d^ε ≤ d`. -/
theorem log_four_d_mul_add_rpow_le (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ 1 ≤ C ∧ ∀ (d : ℕ) (M : ℝ), 1 ≤ d → 3 ≤ M →
      Real.log (4 * (d : ℝ) * M) + (d : ℝ) ^ ε ≤
        C * (d : ℝ) * (Real.log M) ^ (2 : ℕ) := by
  refine ⟨6, by norm_num, by norm_num, ?_⟩
  intro d M hd hM
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  set L : ℝ := Real.log M with hL
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    rw [Real.log_exp] at h
    exact le_of_lt h
  have hL3 : Real.log 3 ≤ L := by rw [hL]; exact Real.log_le_log (by norm_num) hM3
  have hL1 : 1 ≤ L := le_trans hlog3 hL3
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL1
  have hlogM : L ≤ L ^ (2 : ℕ) := by nlinarith [hL1]
  have hlog4 : Real.log (4 * (d : ℝ)) ≤ 4 * (d : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (x := 4 * (d : ℝ)) (by positivity)
    linarith
  have hdε : (d : ℝ) ^ ε ≤ (d : ℝ) := by
    calc (d : ℝ) ^ ε ≤ (d : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hd1 hε
      _ = (d : ℝ) := Real.rpow_one _
  have harg : (0 : ℝ) < 4 * (d : ℝ) := by positivity
  calc Real.log (4 * (d : ℝ) * M) + (d : ℝ) ^ ε
      = Real.log (4 * (d : ℝ)) + Real.log M + (d : ℝ) ^ ε := by
        rw [Real.log_mul (by positivity) (ne_of_gt hM0)]
    _ ≤ 4 * (d : ℝ) + L + (d : ℝ) := by
        rw [← hL]; linarith
    _ ≤ 4 * (d : ℝ) + (d : ℝ) * L ^ (2 : ℕ) + (d : ℝ) := by
        nlinarith [hlogM, hd0]
    _ = 5 * (d : ℝ) + (d : ℝ) * L ^ (2 : ℕ) := by ring
    _ ≤ 6 * (d : ℝ) * L ^ (2 : ℕ) := by nlinarith [hL1, hd1]

end

end Work.FIArea6Hecke.R

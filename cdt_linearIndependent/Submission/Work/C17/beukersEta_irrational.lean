import Mathlib
import Submission.Work.CRad.deps
import Submission.Helpers
import Submission.Transcendence.LindemannC

/-!
# Irrationality of `beukersEta z` for integer `z ≥ 3`

`beukersEta a = ½·log((a+1)/(a−1))` (`Submission.CDT.beukersEta`).  For an
integer `z ≥ 3` the argument `(z+1)/(z−1)` is a rational number `> 1`, and the
real logarithm of a positive rational `≠ 1` is irrational (indeed
transcendental — `Submission.Transcendence.transcendental_log_rat`, Lindemann's
theorem from the Lindemann–Weierstrass chapter).  Hence `beukersEta z` is
irrational.

The proof is a general statement about rational `a > 1` plus the cast
bookkeeping for `a = z`.
-/

namespace Work.C17

open Submission.CDT

/-- The real logarithm of a positive rational `q ≠ 1` is irrational (a
corollary of Lindemann: `log q` is transcendental). -/
lemma irrational_log_ratCast {q : ℚ} (hqpos : 0 < q) (hq1 : q ≠ 1) :
    Irrational (Real.log (q : ℝ)) := by
  rintro ⟨r, hr⟩
  refine Submission.Transcendence.transcendental_log_rat hqpos hq1 ?_
  rw [← hr]
  exact Submission.Transcendence.isAlgebraic_rat_complex r

/-- `beukersEta` of a rational `a > 1` is irrational: `η_a = ½·log((a+1)/(a−1))`
with `(a+1)/(a−1)` a positive rational `≠ 1`. -/
lemma beukersEta_irrational_rat (a : ℚ) (ha : 1 < a) :
    Irrational (beukersEta (a : ℝ)) := by
  have hqpos : 0 < (a + 1) / (a - 1) := by
    apply div_pos <;> linarith
  have hq1 : (a + 1) / (a - 1) ≠ 1 := by
    intro h
    have hne : a - 1 ≠ 0 := by linarith
    have h' : a + 1 = a - 1 := by
      simpa using (div_eq_one_iff_eq hne).mp h
    linarith
  have hcast : (((a + 1) / (a - 1) : ℚ) : ℝ) = ((a : ℝ) + 1) / ((a : ℝ) - 1) := by
    push_cast
    ring
  have hmain : beukersEta (a : ℝ)
      = (1 / 2 : ℝ) * Real.log ((((a + 1) / (a - 1) : ℚ) : ℝ)) := by
    unfold beukersEta
    rw [← hcast]
  rw [hmain]
  have h := (irrational_log_ratCast hqpos hq1).ratCast_mul (q := (1 / 2 : ℚ)) (by norm_num)
  simpa using h

theorem beukersEta_irrational (z : ℤ) (hz : 3 ≤ z) :
    Irrational (Submission.CDT.beukersEta (z : ℝ)) := by
  have h1 : (1 : ℚ) < (z : ℚ) := by
    have : (1 : ℤ) < z := by omega
    exact_mod_cast this
  simpa using beukersEta_irrational_rat (z : ℚ) h1

end Work.C17

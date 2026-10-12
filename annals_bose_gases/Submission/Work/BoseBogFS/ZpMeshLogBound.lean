import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseB6.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.ZpMeshLogBound`

The elementary numerical fact about FS's dimensionless mesh `meshD n = 2π/(n+1)`:

* `meshD n ≤ 9/10` whenever `meshD n ≤ 1` (integrality of `n`: `meshD n ≤ 1` forces
  `n + 1 ≥ 7`, whence `meshD n ≤ 2π/7 ≤ 9/10` because `π < 3.15`);
* `1 - meshD n ≤ log (1 / meshD n)`, which for `0 < δ` is the standard inequality
  `log δ ≤ δ - 1` with `log (1/δ) = -log δ`.
-/

noncomputable section

namespace Work.BoseBogFS

/-- `meshD n = 2π/(n+1) ≤ 1` forces `n + 1 ≥ 7` (as an integer). -/
private lemma meshD_seven_le {n : ℕ} (hδ1 : Work.BoseB6.meshD n ≤ 1) : 7 ≤ n + 1 := by
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2π : 2 * Real.pi ≤ (n : ℝ) + 1 := by
    have h := (div_le_iff₀ hden).mp hδ1
    simpa only [Work.BoseB6.meshD, one_mul] using h
  have h6 : (6 : ℝ) < (n : ℝ) + 1 := by nlinarith [Real.pi_gt_three]
  have : (6 : ℕ) < n + 1 := by
    have : (6 : ℝ) < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  omega

/-- The numeric bound `2π/7 ≤ 9/10` (from `π < 3.15`). -/
private lemma two_pi_div_seven_le : 2 * Real.pi / 7 ≤ 9 / 10 := by
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 7)]
  nlinarith [Real.pi_lt_d2]

theorem ZpMeshLogBound {n : ℕ} (hn : 1 ≤ n) (hδ1 : Work.BoseB6.meshD n ≤ 1) :
    Work.BoseB6.meshD n ≤ 9 / 10 ∧ 1 - Work.BoseB6.meshD n ≤ Real.log (1 / Work.BoseB6.meshD n) := by
  have hδpos : 0 < Work.BoseB6.meshD n := by
    simp only [Work.BoseB6.meshD]; positivity
  have h7 : (7 : ℝ) ≤ (n : ℝ) + 1 := by
    have h := meshD_seven_le hδ1
    have : ((7 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith
  constructor
  · -- `meshD n = 2π/(n+1) ≤ 2π/7 ≤ 9/10`
    have hmono : Work.BoseB6.meshD n ≤ 2 * Real.pi / 7 := by
      simp only [Work.BoseB6.meshD]
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) h7
    linarith [two_pi_div_seven_le]
  · -- `1 - δ ≤ log (1/δ)` from `log δ ≤ δ - 1`
    have hlog : Real.log (Work.BoseB6.meshD n) ≤ Work.BoseB6.meshD n - 1 :=
      Real.log_le_sub_one_of_pos hδpos
    have hinv : Real.log (1 / Work.BoseB6.meshD n) = -Real.log (Work.BoseB6.meshD n) := by
      rw [one_div, Real.log_inv]
    rw [hinv]
    linarith

end Work.BoseBogFS

/-
Copyright: work module for the Elgindi finite-time singularity project.

# `logCutDefs` — the two-sided logarithmic cut-off of the AM-GM / coercivity layer

This module defines the family

  `logChi n z = Work.ChiExplicit.chi (Real.log z / Real.log ((n : ℝ) + 2))`

which is the *logarithmic* cut-off used by `Work.FTS.EllipticEst.TT.slice_coercive` and
the AM-GM certificates: `chi` is the explicit smooth bump `t ↦ smoothTransition (2 - |t|)`
of `Work.ChiExplicit` (`= 1` on `[-1,1]`, `= 0` for `|t| ≥ 2`, `0 ≤ chi ≤ 1`), and the
rescaling `log z / log ((n:ℝ)+2)` makes the truncation happen "multiplicatively": since
`|log z| / log ((n:ℝ)+2) ≥ 2` for `z ≤ 1/((n:ℝ)+2)²` and for `z ≥ ((n:ℝ)+2)²`, the cut-off
vanishes in those two regions and interpolates in between.

Note that for *every* `n : ℕ` the constant `(n : ℝ) + 2` is `≥ 2 > 1`, so
`Real.log ((n:ℝ)+2) > 0`: no hypothesis on `n` is needed.  (This is what differs from the
`Work.FTS.EllipticEst.ZCuts.*` interface, which is parametrised by a natural `k` and therefore
carries a hypothesis `2 ≤ k`; here the parameter is the *real* number `(n:ℝ) + 2`.)

## What is here

The definition `logChi`, the elementary arithmetic of the parameter
(`one_lt_two_add_natCast`, `log_two_add_natCast_pos`, `log_two_le_log`), the value bound
`logChi_mem_Icc`, and the two vanishing statements `logChi_eq_zero_of_le`,
`logChi_eq_zero_of_ge`.

The analytic content — `C^∞`-smoothness on `(0,∞)`, the uniform commutator bound
`|z (logChi n)'(z)| ≤ K`, and the pointwise convergence `logChi n z → 1` — is stated in the
sibling modules `logChi_contDiffOn`, `logChi_deriv_bound` and `logChi_tendsto`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Submission.Work.ChiExplicit.Defs
import Submission.Work.ChiExplicit.chi_contDiff
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.EllipticEst.TT

/-- **THE LOGARITHMIC CUT-OFF FAMILY.**
`logChi n z = chi (log z / log ((n:ℝ)+2))`, where `chi = Work.ChiExplicit.chi` is the explicit
bump `t ↦ smoothTransition (2 - |t|)`.  It is `1` for `z` in the multiplicative window
`[1/((n:ℝ)+2), (n:ℝ)+2]` and `0` outside `(1/((n:ℝ)+2)², ((n:ℝ)+2)²)`. -/
noncomputable def logChi (n : ℕ) : ℝ → ℝ :=
  fun z => Work.ChiExplicit.chi (Real.log z / Real.log ((n : ℝ) + 2))

/-- The definition, as a rewrite rule. -/
theorem logChi_apply (n : ℕ) (z : ℝ) :
    logChi n z = Work.ChiExplicit.chi (Real.log z / Real.log ((n : ℝ) + 2)) := rfl

/-! ## The arithmetic of the parameter `(n : ℝ) + 2` -/

/-- `(n : ℝ) + 2 > 1` for every `n : ℕ`. -/
lemma one_lt_two_add_natCast (n : ℕ) : (1 : ℝ) < (n : ℝ) + 2 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- `(n : ℝ) + 2 ≥ 2`, hence `> 0`. -/
lemma two_le_two_add_natCast (n : ℕ) : (2 : ℝ) ≤ (n : ℝ) + 2 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The denominator of the rescaling is strictly positive: `log ((n:ℝ)+2) > 0`. -/
lemma log_two_add_natCast_pos (n : ℕ) : 0 < Real.log ((n : ℝ) + 2) :=
  Real.log_pos (one_lt_two_add_natCast n)

/-- `log ((n:ℝ)+2) ≥ log 2`, the uniform lower bound on the denominator that makes the
commutator bound `|z χ'(z)| ≤ K / log 2` uniform in `n`. -/
lemma log_two_le_log (n : ℕ) : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
  Real.log_le_log (by norm_num) (two_le_two_add_natCast n)

/-! ## The elementary value facts -/

/-- `logChi n` takes values in `[0,1]` everywhere. -/
lemma logChi_mem_Icc (n : ℕ) (z : ℝ) : 0 ≤ logChi n z ∧ logChi n z ≤ 1 :=
  ⟨Work.ChiExplicit.chi_nonneg _, Work.ChiExplicit.chi_le_one _⟩

/-- **Vanishing at the small end**: for `0 < z ≤ 1/((n:ℝ)+2)²` the rescaled logarithm is
`≤ -2`, so `logChi n z = 0`. -/
lemma logChi_eq_zero_of_le {n : ℕ} {z : ℝ} (hz : 0 < z)
    (h : z ≤ 1 / ((n : ℝ) + 2) ^ 2) : logChi n z = 0 := by
  have hlog : 0 < Real.log ((n : ℝ) + 2) := log_two_add_natCast_pos n
  have h1 : Real.log z ≤ Real.log (1 / ((n : ℝ) + 2) ^ 2) := Real.log_le_log hz h
  have h2 : Real.log (1 / ((n : ℝ) + 2) ^ 2) = -(2 * Real.log ((n : ℝ) + 2)) := by
    rw [one_div, Real.log_inv, Real.log_pow]
    push_cast
    ring
  have ht : Real.log z / Real.log ((n : ℝ) + 2) ≤ -2 := by
    rw [div_le_iff₀ hlog]
    linarith
  rw [logChi_apply]
  exact Work.ChiExplicit.chi_eq_zero (by
    rw [abs_of_nonpos (by linarith)]; linarith)

/-- **Vanishing at the large end**: for `z ≥ ((n:ℝ)+2)²` the rescaled logarithm is `≥ 2`, so
`logChi n z = 0`. -/
lemma logChi_eq_zero_of_ge {n : ℕ} {z : ℝ} (h : ((n : ℝ) + 2) ^ 2 ≤ z) : logChi n z = 0 := by
  have hc : 0 < (n : ℝ) + 2 := lt_trans one_pos (one_lt_two_add_natCast n)
  have hlog : 0 < Real.log ((n : ℝ) + 2) := log_two_add_natCast_pos n
  have h1 : Real.log (((n : ℝ) + 2) ^ 2) ≤ Real.log z :=
    Real.log_le_log (pow_pos hc 2) h
  have h2 : Real.log (((n : ℝ) + 2) ^ 2) = 2 * Real.log ((n : ℝ) + 2) := by
    rw [Real.log_pow]
    push_cast
    ring
  have ht : (2 : ℝ) ≤ Real.log z / Real.log ((n : ℝ) + 2) := by
    rw [le_div_iff₀ hlog]
    linarith
  rw [logChi_apply]
  exact Work.ChiExplicit.chi_eq_zero (by
    rw [abs_of_nonneg (by linarith)]; linarith)

end Work.FTS.EllipticEst.TT

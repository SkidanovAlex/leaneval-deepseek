/-
# `Submission.Work.FIArea6Hecke.R.logDerivCore`

The **content** of the logarithmic-derivative bound of *FI* (16.20)/(16.23): the definitions
(`IsCompleted`, `divR`), the archimedean block, the Hadamard partial-fraction kernel bounds, the
archimedean conversion `(Lval)′/Lval = Λ′/Λ − (heckeArch)′/heckeArch` and the two assemblies
`logDerivReLower_of` / `logDerivReLower_of_baseBounds`.

This module is the body of `R/logDerivReLower` without the target theorem itself.  It is split off
so that the downstream modules proving the *inputs* of the assembly (`R/lamGrowth`,
`R/zerosInStrip`, `R/baseLowerTwoUniform`, `R/baseLowerNegTwoUniform`, …) can import the content
without importing the module that contains the final theorem — which has to import them.
-/

import Mathlib
import Submission.Work.FIArea6Hecke.R.LogDerivStatementDefs
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea5.HeckeZFR.Lam_partialFraction
import Submission.Work.FIArea5.HeckeZFR.LamBaseBound
import Submission.Work.FIArea5.HeckeZFR.HeckeNonvanishing
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound
import Submission.Commons.NumberTheory.Linnik.goodRadius_pair
import Submission.Work.FIArea5.HeckeZFR.DigammaShift
import Submission.Work.FIArea6Hecke.R.HeckeCompletionAll
import Submission.Work.FIArea6Hecke.R.wzsOfPfDiff
import Submission.Work.FIArea6Hecke.R.zfrRealAxisPLight
import Submission.Port.LogDerivCompat

/-
# `Submission.Work.FIArea6Hecke.R.logDerivReLower` — the one-sided logarithmic-derivative bound in
the zero-free region (*FI* (16.20)/(16.23))

## The target

`LogDerivReLower ε` (defined in `R/LogDerivStatementDefs`): there are `c, C > 0` such that for every
strict character `χ` mod `4d`, every `m : ℤ`, every entire completion `Λ` of `Λ(s,ψ)` and every `s`
with `1 - c·min(1/log(4d+|m|+|s.im|+1), d^{-ε}) ≤ re s ≤ 2`,

  `Re ((Lval)'(s)/Lval(s)) ≥ -C·log(4d(|m|+|s.im|+3))`.

## What is proved here (sorry-free)

* `heckeArch` facts: `heckeArch d m s = (4d/π)^s Γ(s+|m|/2)`, nonvanishing for `re s > 0`, its
  logarithmic derivative is `log(4d/π) + ψ(s+|m|/2)`, whose real part is
  `≤ 7·log(4d(|m|+|s.im|+3))` in the strip `1/2 ≤ re s ≤ 2`
  (via `DigammaShift.digamma_re_le_of_half_le`);
* `kernel_ineq`, `kernelReGe`: the pointwise bound for the rebasing kernel,
  `Re(1/(s-u) − 1/(2+i·im s − u)) ≥ −12/(1 + (im s − im u)²)`, valid for `0 ≤ re s ≤ 2`,
  `-1 ≤ re u ≤ 1`, as soon as `u` is not to the right of `s` at comparable height;
* `logDeriv_re_ge_of_pf`: **the Hadamard partial fraction gives the one-sided bound**
  `Re(Λ'/Λ)(s) ≥ Re(Λ'/Λ)(2+i·im s) − 12·W`, where `W` bounds the weighted zero sum
  `Σ_u ord(u)/(1+(im s − im u)²)`; this is the step at which the zero-free region enters (a zero to
  the right of `s` at comparable height is exactly what the region excludes);
* `lval_logDeriv_eq`: the archimedean conversion `(Lval)'/Lval = Λ'/Λ − (heckeArch)'/heckeArch`;
* `logDerivReLower_of`: **the assembly** — from

  1. the Hadamard partial fraction of the completion (for every admissible datum),
  2. the weighted zero sum `Σ_u ord(u)/(1+(t−Im u)²) ≪ log(4d(|m|+|t|+3))`,
  3. the base bound `Re(Λ'/Λ)(2+iγ) ≥ −C·log(4d(|m|+|γ|+3))`,
  4. the location of the zeros in `[-1,1]`,
  5. `ZFRoffAxis` (*FI* (16.20), de la Vallée Poussin) and `ZFRrealAxis ε` (*FI* Lemma 16.1,
     Landau–Siegel),

  it derives `LogDerivReLower ε`.

## The two assemblies

* `logDerivReLower_of` takes the weighted zero sum of item 2 above as a hypothesis;
* `logDerivReLower_of_baseBounds` *derives* it (through the proved
  `Work.FIArea6Hecke.R.wzsOfPfDiff`, which extracts the weighted zero sum from the Hadamard partial
  fraction at the pair `(2+it, -2+it)` and the bounds on `Re (Λ'/Λ)` at the two vertical lines
  `re = 2`, `re = -2`), so its hypotheses are exactly:
  the Hadamard partial fraction, the three bounds on `Re (Λ'/Λ)` at `re = 2±` and `re = -2`,
  the zero location, and the two zero-free-region inputs.

## What remains for the unconditional statement

Each remaining input is being supplied by the fleet as a separate lemma, all stated in terms of the
definitions of this file:

* `Work.FIArea5.HeckeZFR.Hadm.factorZero`, `goodRadius`, `cofactorBound`, `pfConv` — the four
  classical Hadamard pieces consumed by `Lam_partialFraction` (via its sorry-free assembly
  `Lam_aux_of`);
* `Work.FIArea6Hecke.R.lamGrowthStrict` (`R/lamGrowthStrict.lean`, delegated) — the circle growth
  `log ‖Λ z‖ ≤ C·R·(log (R+2) + K)` of the completion (order-1 growth, from the
  conductor-normalised functional equation `R/heckeFEStrictConductorUni` and the strip bounds; the
  *twisted* functional equation `R/heckeTwistFE_strict` is false for imprimitive `χ` — see
  `R/NOTES_logDerivReLower.md`);
* `Work.FIArea6Hecke.R.lamPartialFraction` — the Hadamard partial fraction, from the growth and the
  four pieces;
* `Work.FIArea6Hecke.R.baseUpperTwo`, `baseLowerTwo`, `baseLowerNegTwo` — the bounds on `Re (Λ'/Λ)`
  at `re = 2` (both sides) and at `re = -2` (below), from the digamma asymptotics, the absolutely
  convergent Dirichlet series and the functional equation.  The *uniform* forms used by the
  capstone are `R/HeckeLambdaLogDerivBounds.lam_logDeriv_re_at_two_le_uniform` (upper bound at
  `re = 2`), `Work.FIArea6Hecke.R.baseLowerTwoUniform` (`R/baseLowerTwoUniform.lean`, delegated;
  lower bound at `re = 2`) and `Work.FIArea6Hecke.R.baseLowerNegTwoUniform`
  (`R/baseLowerNegTwoUniform.lean`, lower bound at `re = -2`, proved from
  `R/heckeFEStrictConductorUni`); the zero location is `Work.FIArea6Hecke.R.zerosInStrip`
  (`R/zerosInStrip.lean`).

The remaining two are the deep analytic inputs of *FI* §16:

* `ZFRoffAxis` — (16.20), the de la Vallée Poussin region: from the `3-4-1` inequality
  (`Work.FIArea6Hecke.R.hecke_three_four_one`, proved), the axis bound, and the near-zero
  log-derivative bound (which `FIArea5/HeckeZFR/Rebase.re_logDeriv_rebase_of_pf` together with
  `logDeriv_FE_at_neg_one` supplies from the partial fraction and the base bound);
* `ZFRrealAxis ε` — *FI* Lemma 16.1 (Landau–Siegel).  This one is **not** an artefact of the
  formalisation: the region of the statement is genuinely deeper than `1 - c/log` (its depth is
  `min(1/log, d^{-ε})`), so a real zero of an admissible completion at distance `≪ d^{-ε}` from `1`
  would lie inside the region, and just to the left of it the logarithmic derivative behaves like
  `-1/|s-ρ| + O(1)` and the bound fails.  Only ineffective methods (Siegel, Goldfeld) give the
  `d^{-ε}` depth.

Given `ZFRoffAxis` and `ZFRrealAxis ε`, the chain `lamGrowthStrict → lamPartialFraction → hpf`, the
three base bounds, the zero location and `logDerivReLower_of_baseBounds` yields `LogDerivReLower ε`;
this assembly is written out in `R/logDerivReLowerCapstone.lean`
(`Work.FIArea6Hecke.R.logDerivReLower_of_hadamard`), whose only remaining hypotheses are the circle
growth, the uniform lower bound at `re = 2` and the two zero-free-region inputs.
-/

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Complex Metric Filter
open scoped BigOperators Topology

noncomputable section

/-! ## A bridge for `R/heckeStripLogDerivConductor`

`R/heckeStripLogDerivConductor` uses the elementary comparison `log a ≤ 2 log b` (for `0 < a ≤ 2b`,
`2 ≤ b`) under the name `log_le_two_mul_log`; that lemma lives in `R/heckeStripBallRegions`, whose
import it lost.  The statement is duplicated here (verbatim) so that the logarithmic-derivative
chain remains importable; if the original import is restored, this copy must be dropped again. -/
lemma log_le_two_mul_log {a b : ℝ} (ha : 0 < a) (hb : 2 ≤ b) (hab : a ≤ 2 * b) :
    Real.log a ≤ 2 * Real.log b := by
  have hbpos : 0 < b := by linarith
  have h1 : Real.log a ≤ Real.log (2 * b) := Real.log_le_log ha hab
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hbpos)] at h1
  have h2 : Real.log 2 ≤ Real.log b := Real.log_le_log (by norm_num) hb
  linarith

-- `heckeArch d m s = (4d/π)^s Γ(s + |m|/2)`

lemma heckeArch_eq (d : ℕ) (m : ℤ) (s : ℂ) :
    Work.FITop4.Bridge.heckeArch d m s
      = (4 * (d : ℂ) / (Real.pi : ℂ)) ^ s * Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) := rfl

lemma heckeArch_base_ne_zero (d : ℕ) (hd : 1 ≤ d) :
    (4 * (d : ℂ) / (Real.pi : ℂ)) ≠ 0 := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have : (4 * (d : ℂ) / (Real.pi : ℂ)) = ((4 * (d : ℝ) / Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_ne_zero]
  positivity

lemma heckeArch_cpow_ne_zero (d : ℕ) (hd : 1 ≤ d) (s : ℂ) :
    (4 * (d : ℂ) / (Real.pi : ℂ)) ^ s ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero (heckeArch_base_ne_zero d hd)]
  exact Complex.exp_ne_zero _

lemma heckeArch_ne_zero_of_pos_re (d : ℕ) (hd : 1 ≤ d) (m : ℤ) {s : ℂ} (hs : 0 < s.re) :
    Work.FITop4.Bridge.heckeArch d m s ≠ 0 := by
  rw [heckeArch_eq]
  refine mul_ne_zero (heckeArch_cpow_ne_zero d hd s) ?_
  refine Complex.Gamma_ne_zero_of_re_pos ?_
  have h1 : ((|(m : ℝ)| / 2 : ℝ) : ℂ).re = |(m : ℝ)| / 2 := by simp
  rw [Complex.add_re, h1]
  have := abs_nonneg (m : ℝ)
  linarith

lemma heckeArch_eq_zero_imp_re_le_zero (d : ℕ) (hd : 1 ≤ d) {m : ℤ} {s : ℂ}
    (h : Work.FITop4.Bridge.heckeArch d m s = 0) : s.re ≤ 0 := by
  by_contra hc
  push Not at hc
  exact heckeArch_ne_zero_of_pos_re d hd m hc h

lemma gamma_ne_zero_of_ne_neg_nat (z : ℂ) (h : ∀ n : ℕ, z ≠ -((n : ℕ) : ℂ)) :
    Complex.Gamma z ≠ 0 := by
  intro h0
  obtain ⟨n, hn⟩ := (Complex.Gamma_eq_zero_iff z).mp h0
  exact h n hn

lemma logDeriv_heckeArch (d : ℕ) (hd : 1 ≤ d) (m : ℤ) {s : ℂ}
    (hs : ∀ n : ℕ, s + ((|(m : ℝ)| / 2 : ℝ) : ℂ) ≠ -((n : ℕ) : ℂ)) :
    logDeriv (fun z => Work.FITop4.Bridge.heckeArch d m z) s
      = (4 * (d : ℂ) / (Real.pi : ℂ)).log
        + Complex.digamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) := by
  have hfun : (fun z => Work.FITop4.Bridge.heckeArch d m z)
      = fun z => (4 * (d : ℂ) / (Real.pi : ℂ)) ^ z * Complex.Gamma (z + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) := by
    funext z; rw [heckeArch_eq]
  have h1 : logDeriv (fun z => (4 * (d : ℂ) / (Real.pi : ℂ)) ^ z
      * Complex.Gamma (z + ((|(m : ℝ)| / 2 : ℝ) : ℂ))) s
      = logDeriv (fun z => (4 * (d : ℂ) / (Real.pi : ℂ)) ^ z) s
        + logDeriv (fun z => Complex.Gamma (z + ((|(m : ℝ)| / 2 : ℝ) : ℂ))) s :=
    Submission.Port.logDeriv_mul_fun s (heckeArch_cpow_ne_zero d hd s)
      (gamma_ne_zero_of_ne_neg_nat _ hs)
      (DifferentiableAt.const_cpow differentiableAt_id (Or.inl (heckeArch_base_ne_zero d hd)))
      (DifferentiableAt.comp s (by fun_prop) (differentiableAt_id.add_const _))
  rw [hfun, h1, Work.FIArea5.S16Hecke.logDeriv_const_cpow _ (heckeArch_base_ne_zero d hd) s,
    Work.FIArea5.S16Hecke.logDeriv_Gamma_add_const _ _ hs]

/-- **The archimedean part of the logarithmic derivative is bounded above** by
`7·log(4d(|m|+|t|+3))` in the strip `1/2 ≤ re s ≤ 2`. -/
lemma logDeriv_heckeArch_re_le (d : ℕ) (hd : 1 ≤ d) (m : ℤ) {s : ℂ}
    (hlo : (1 / 2 : ℝ) ≤ s.re) (hhi : s.re ≤ 2) :
    (logDeriv (fun z => Work.FITop4.Bridge.heckeArch d m z) s).re
      ≤ 7 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) := by
  have hne : ∀ n : ℕ, s + ((|(m : ℝ)| / 2 : ℝ) : ℂ) ≠ -((n : ℕ) : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.natCast_re] at hre
    have hmm : (0 : ℝ) ≤ |(m : ℝ)| / 2 := by positivity
    have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rw [logDeriv_heckeArch d hd m hne]
  have hdig := Work.FIArea5.S16Hecke.digamma_re_le_of_half_le (s.re + |(m : ℝ)| / 2) s.im (by
    have := abs_nonneg (m : ℝ); linarith)
  have hcast : (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) = ((s.re + |(m : ℝ)| / 2 : ℝ) : ℂ)
      + (s.im : ℂ) * I := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im] <;> ring
  have hlog_re : ((4 * (d : ℂ) / (Real.pi : ℂ)).log).re ≤ Real.log (4 * (d : ℝ)) := by
    rw [Complex.log_re]
    have h1 : ‖(4 * (d : ℂ) / (Real.pi : ℂ))‖ = 4 * (d : ℝ) / Real.pi := by
      rw [show (4 * (d : ℂ) / (Real.pi : ℂ)) = ((4 * (d : ℝ) / Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [h1]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ Real.pi_pos]
    have hp : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    nlinarith
  rw [hcast]
  rw [Complex.add_re]
  have hlog4 : Real.log (4 * (d : ℝ)) ≤ Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) := by
    refine Real.log_le_log (by positivity) ?_
    have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg s.im
    have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hlogT : Real.log (2 + |s.im|) ≤ Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) := by
    refine Real.log_le_log (by positivity) ?_
    have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg s.im
    have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hlogM : 2 * Real.log (4 * (s.re + |(m : ℝ)| / 2))
      ≤ 2 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) := by
    have h0 : (0 : ℝ) < 4 * (s.re + |(m : ℝ)| / 2) := by
      have := abs_nonneg (m : ℝ); linarith
    have hle : 4 * (s.re + |(m : ℝ)| / 2) ≤ 4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3) := by
      have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg s.im
      have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      nlinarith
    exact mul_le_mul_of_nonneg_left (Real.log_le_log h0 hle) (by norm_num)
  have h6 : (6 : ℝ) ≤ 3 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) := by
    have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg s.im
    have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hL : Real.log 12 ≤ Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) := by
      refine Real.log_le_log (by norm_num) ?_
      nlinarith
    have h12 : (2 : ℝ) < Real.log 12 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have h1 := Real.exp_one_lt_d9
      have hpos := Real.exp_pos 1
      rw [hsq]
      nlinarith
    linarith
  linarith [hdig, hlog_re, hlog4, hlogT, hlogM, h6]


/-- The divisor of an entire `Λ` on the closed ball of radius `R`. -/
def divR (Λ : ℂ → ℂ) (R : ℝ) : ℂ → ℤ := MeromorphicOn.divisor Λ (Metric.closedBall 0 R)

lemma kernel_ineq (a b d : ℝ) (ha3 : |a| ≤ 3) (hb1 : 1 ≤ b) (hb3 : b ≤ 3)
    (hcase : 0 ≤ a ∨ 1 ≤ |d|) :
    12 / (1 + d ^ 2) * (-1) ≤ a / (a ^ 2 + d ^ 2) - b / (b ^ 2 + d ^ 2) := by
  have hden' : 0 < b ^ 2 + d ^ 2 := by positivity
  have hden'' : 0 < 1 + d ^ 2 := by positivity
  have hsq : ∀ x : ℝ, x ^ 2 = |x| ^ 2 := fun x => (sq_abs x).symm
  by_cases hden : a ^ 2 + d ^ 2 = 0
  · have haz : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg d]
    have hdz : d = 0 := by nlinarith [sq_nonneg a, sq_nonneg d]
    subst haz; subst hdz
    have hbpos : (0:ℝ) < b := by linarith
    have hbne : (0:ℝ) ≠ b := by linarith
    have hzero : (0:ℝ) / (0 ^ 2 + 0 ^ 2) = 0 := by norm_num
    have hbs : b ^ 2 + (0:ℝ) ^ 2 = b * b := by ring
    have hone : b / (b * b) = 1 / b := by
      field_simp
    rw [hzero, hbs, hone]
    rw [show (12:ℝ) / (1 + 0 ^ 2) * (-1) = -12 by norm_num]
    rw [zero_sub, neg_le_neg_iff]
    rw [div_le_iff₀ hbpos]
    nlinarith [hb1]
  · have hdenp : 0 < a ^ 2 + d ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hden)
    rcases hcase with ha | hd
    · have h1 : 0 ≤ a / (a ^ 2 + d ^ 2) := div_nonneg ha hdenp.le
      have h2 : b / (b ^ 2 + d ^ 2) ≤ 12 / (1 + d ^ 2) := by
        rw [div_le_div_iff₀ hden' hden'']
        nlinarith [hb1, hb3, sq_nonneg d, sq_nonneg b]
      have h3 : -(12 / (1 + d ^ 2)) ≤ -(b / (b ^ 2 + d ^ 2)) := by linarith
      linarith
    · have hd1 : 1 ≤ d ^ 2 := by
        rw [hsq d]; nlinarith [hd, abs_nonneg d]
      have ha' : -(|a| / (a ^ 2 + d ^ 2)) ≤ a / (a ^ 2 + d ^ 2) := by
        rw [← neg_div, div_le_div_iff₀ hdenp hdenp]
        nlinarith [neg_abs_le a]
      have h2 : |a| / (a ^ 2 + d ^ 2) ≤ 3 / d ^ 2 := by
        rw [div_le_div_iff₀ hdenp (by positivity)]
        nlinarith [ha3, abs_nonneg a, sq_nonneg d, sq_nonneg a]
      have h3 : b / (b ^ 2 + d ^ 2) ≤ 3 / d ^ 2 := by
        rw [div_le_div_iff₀ hden' (by positivity)]
        nlinarith [hb3, sq_nonneg b, sq_nonneg d]
      have h4 : 6 / d ^ 2 ≤ 12 / (1 + d ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) hden'']
        nlinarith [hd1]
      have h6 : -(12 / (1 + d ^ 2)) ≤ -(3 / d ^ 2) - 3 / d ^ 2 := by
        have hsum : (3:ℝ) / d ^ 2 + 3 / d ^ 2 = 6 / d ^ 2 := by ring
        linarith [h4]
      linarith

theorem kernelReGe (σ t β γ : ℝ) (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) (hβ0 : -1 ≤ β) (hβ1 : β ≤ 1)
    (hcase : 0 ≤ σ - β ∨ 1 ≤ |t - γ|) :
    -12 / (1 + (t - γ) ^ 2)
      ≤ (1 / (((σ : ℂ) + (t : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I))
        - 1 / (((2 : ℂ) + (t : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I))).re := by
  have h1 : ((σ : ℂ) + (t : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I)
      = (((σ - β : ℝ)) : ℂ) + (((t - γ : ℝ)) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have h2 : ((2 : ℂ) + (t : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I)
      = (((2 - β : ℝ)) : ℂ) + (((t - γ : ℝ)) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have h3 : (1 / (((σ : ℂ) + (t : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I))).re
      = (σ - β) / ((σ - β) ^ 2 + (t - γ) ^ 2) := by
    rw [h1, one_div, Complex.inv_re, Complex.normSq_apply]
    simp
    ring
  have h4 : (1 / (((2 : ℂ) + (t : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I))).re
      = (2 - β) / ((2 - β) ^ 2 + (t - γ) ^ 2) := by
    rw [h2, one_div, Complex.inv_re, Complex.normSq_apply]
    simp
    ring
  rw [Complex.sub_re, h3, h4]
  have ha3 : |σ - β| ≤ 3 := by rw [abs_le]; constructor <;> linarith
  have hb1 : 1 ≤ 2 - β := by linarith
  have hb3 : (2 : ℝ) - β ≤ 3 := by linarith
  have hk := kernel_ineq (σ - β) (2 - β) (t - γ) ha3 hb1 hb3 hcase
  rw [show (12:ℝ) / (1 + (t - γ) ^ 2) * (-1) = -12 / (1 + (t - γ) ^ 2) by ring] at hk
  exact hk

/-- The pointwise kernel bound for a zero of `Λ`. -/
lemma kernel_of_zero {Λ : ℂ → ℂ} {σ t : ℝ} {s : ℂ} (hs : s = (σ : ℂ) + (t : ℂ) * Complex.I)
    (hz : ∀ u : ℂ, Λ u = 0 → -1 ≤ u.re ∧ u.re ≤ 1)
    (hleft : ∀ u : ℂ, Λ u = 0 → |t - u.im| < 1 → u.re ≤ σ)
    (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) {u : ℂ} (hu : Λ u = 0) :
    -12 / (1 + (t - u.im) ^ 2)
      ≤ (1 / (s - u) - 1 / (((2 : ℂ) + (t : ℂ) * Complex.I) - u)).re := by
  obtain ⟨hβ0, hβ1⟩ := hz u hu
  have hcase : 0 ≤ σ - u.re ∨ 1 ≤ |t - u.im| := by
    by_cases h : |t - u.im| < 1
    · left; have := hleft u hu h; linarith
    · right; push Not at h; exact h
  have hker := kernelReGe σ t u.re u.im hσ0 hσ2 hβ0 hβ1 hcase
  have hu' : u = (u.re : ℂ) + (u.im : ℂ) * Complex.I := by apply Complex.ext <;> simp
  rw [← hs, ← hu'] at hker
  have e1 : s - u = ((σ - u.re : ℝ) : ℂ) + ((t - u.im : ℝ) : ℂ) * Complex.I := by
    rw [hs, hu']; apply Complex.ext <;> simp
  have e2 : ((2 : ℂ) + (t : ℂ) * Complex.I) - u
      = ((2 - u.re : ℝ) : ℂ) + ((t - u.im : ℝ) : ℂ) * Complex.I := by
    rw [hu']; apply Complex.ext <;> simp
  rw [e1, e2] at hker
  rw [e1, e2]
  exact hker

/-- Each summand of the Hadamard partial fraction is bounded below by the weighted multiplicity. -/
lemma summand_re_ge {Λ : ℂ → ℂ} (hAn : AnalyticOn ℂ Λ Set.univ)
    {σ t : ℝ} {s : ℂ} (hs : s = (σ : ℂ) + (t : ℂ) * Complex.I)
    (hz : ∀ u : ℂ, Λ u = 0 → -1 ≤ u.re ∧ u.re ≤ 1)
    (hleft : ∀ u : ℂ, Λ u = 0 → |t - u.im| < 1 → u.re ≤ σ)
    (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) (R : ℝ) (u : ℂ) :
    ((divR Λ R u : ℤ) : ℝ) * (-12 / (1 + (t - u.im) ^ 2))
      ≤ (((divR Λ R u : ℤ) : ℂ) * (1 / (s - u) - 1 / (((2 : ℂ) + (t : ℂ) * Complex.I) - u))).re := by
  have hDiff : Differentiable ℂ Λ := differentiableOn_univ.mp hAn.differentiableOn
  by_cases hD : divR Λ R u = 0
  · rw [hD]; simp
  · have hAn' : AnalyticOnNhd ℂ Λ (Metric.closedBall 0 R) :=
      Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable hDiff (Metric.closedBall 0 R)
    have hzero : Λ u = 0 := Commons.Analysis.Complex.zero_of_divisor_ne_zero hAn' hD
    have hDnn : (0 : ℝ) ≤ ((divR Λ R u : ℤ) : ℝ) :=
      Commons.Analysis.Complex.divisor_nonneg_on_closedBall hAn' u
    have hcast : ((divR Λ R u : ℤ) : ℂ) = (((divR Λ R u : ℤ) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_left (kernel_of_zero hs hz hleft hσ0 hσ2 hzero) hDnn

/-- **The Hadamard partial fraction gives the one-sided logarithmic-derivative bound.** -/
lemma logDeriv_re_ge_of_pf {Λ : ℂ → ℂ} (hAn : AnalyticOn ℂ Λ Set.univ)
    (hpf : ∀ s s₁ : ℂ, Λ s ≠ 0 → Λ s₁ ≠ 0 →
      Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ, (((divR Λ R u : ℤ) : ℂ)
          * (1 / (s - u) - 1 / (s₁ - u)))) Filter.atTop
        (nhds (deriv Λ s / Λ s - deriv Λ s₁ / Λ s₁)))
    (hz : ∀ u : ℂ, Λ u = 0 → -1 ≤ u.re ∧ u.re ≤ 1)
    {σ t W : ℝ} {s : ℂ} (hs : s = (σ : ℂ) + (t : ℂ) * Complex.I)
    (hleft : ∀ u : ℂ, Λ u = 0 → |t - u.im| < 1 → u.re ≤ σ)
    (hW : ∀ R : ℝ, 1 ≤ R →
      ∑ᶠ u : ℂ, ((divR Λ R u : ℤ) : ℝ) / (1 + (t - u.im) ^ 2) ≤ W)
    (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2)
    (hs0 : Λ s ≠ 0) (hs1 : Λ ((2 : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    (deriv Λ ((2 : ℂ) + (t : ℂ) * Complex.I) / Λ ((2 : ℂ) + (t : ℂ) * Complex.I)).re - 12 * W
      ≤ (deriv Λ s / Λ s).re := by
  set s₁ : ℂ := (2 : ℂ) + (t : ℂ) * Complex.I with hs₁
  have hs1' : Λ s₁ ≠ 0 := by rwa [hs₁]
  have hlim := hpf s s₁ hs0 hs1'
  -- finite supports
  have hfs : ∀ R : ℝ, Function.HasFiniteSupport
      (fun u : ℂ => (((divR Λ R u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₁ - u)))) := fun R =>
    ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
      (fun u hu => by
        simp only [divR] at hu ⊢
        rw [Function.mem_support] at hu ⊢
        intro h0
        exact hu (by rw [h0]; simp))
  have hfs' : ∀ R : ℝ, Function.HasFiniteSupport
      (fun u : ℂ => ((divR Λ R u : ℤ) : ℝ) * (-12 / (1 + (t - u.im) ^ 2))) := fun R =>
    ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
      (fun u hu => by
        simp only [divR] at hu ⊢
        rw [Function.mem_support] at hu ⊢
        intro h0
        exact hu (by rw [h0]; simp))
  have hfsd : ∀ R : ℝ, Function.HasFiniteSupport
      (fun u : ℂ => ((divR Λ R u : ℤ) : ℝ) / (1 + (t - u.im) ^ 2)) := fun R =>
    ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)).subset
      (fun u hu => by
        simp only [divR] at hu ⊢
        rw [Function.mem_support] at hu ⊢
        intro h0
        exact hu (by rw [h0]; simp))
  have hmain : ∀ R : ℝ, 1 ≤ R → -12 * W ≤
      (∑ᶠ u : ℂ, (((divR Λ R u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₁ - u)))).re := by
    intro R hR
    -- sum the pointwise bounds
    have h1 : (∑ᶠ u : ℂ, (((divR Λ R u : ℤ) : ℂ)
        * (1 / (s - u) - 1 / (s₁ - u)))).re
        = ∑ᶠ u : ℂ, ((((divR Λ R u : ℤ) : ℂ)
        * (1 / (s - u) - 1 / (s₁ - u)))).re := by
      have := AddMonoidHom.map_finsum (Complex.reCLM : ℂ →+ ℝ) (hfs R)
      simpa using this
    have h2 : ∑ᶠ u : ℂ, ((divR Λ R u : ℤ) : ℝ) * (-12 / (1 + (t - u.im) ^ 2))
        ≤ ∑ᶠ u : ℂ, ((((divR Λ R u : ℤ) : ℂ)
        * (1 / (s - u) - 1 / (s₁ - u)))).re := by
      refine finsum_le_finsum' (hfs' R) ((hfs R).subset ?_) (fun u => ?_)
      · intro u hu
        rw [Function.mem_support] at hu ⊢
        intro h0
        exact hu (by rw [h0]; simp)
      · exact summand_re_ge hAn hs hz hleft hσ0 hσ2 R u
    have h3 : ∑ᶠ u : ℂ, ((divR Λ R u : ℤ) : ℝ) * (-12 / (1 + (t - u.im) ^ 2))
        = (-12) * ∑ᶠ u : ℂ, ((divR Λ R u : ℤ) : ℝ) / (1 + (t - u.im) ^ 2) := by
      have hA : (∑ᶠ u : ℂ, ((divR Λ R u : ℤ) : ℝ) * (-12 / (1 + (t - u.im) ^ 2)))
          = ∑ᶠ u : ℂ, (-12) * (((divR Λ R u : ℤ) : ℝ) / (1 + (t - u.im) ^ 2)) :=
        finsum_congr (fun u => by ring)
      rw [hA]
      have hm := AddMonoidHom.map_finsum (AddMonoidHom.mulLeft (-12 : ℝ)) (hfsd R)
      simpa using hm.symm
    have h4 : (-12) * (∑ᶠ u : ℂ, ((divR Λ R u : ℤ) : ℝ) / (1 + (t - u.im) ^ 2))
        ≥ (-12) * W := by
      have := hW R hR
      nlinarith
    rw [h1]
    linarith
  have htend : Filter.Tendsto (fun R : ℝ =>
      (∑ᶠ u : ℂ, (((divR Λ R u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₁ - u)))).re) Filter.atTop
      (nhds ((deriv Λ s / Λ s - deriv Λ s₁ / Λ s₁).re)) :=
    (Complex.continuous_re.tendsto _).comp hlim
  have hfin := ge_of_tendsto htend (Filter.eventually_atTop.mpr ⟨1, fun R hR => hmain R hR⟩)
  rw [Complex.sub_re] at hfin
  linarith


/-- The admissibility predicate of the target statement: `Λ` is an entire completion of the Hecke
`L`-function of `ψ_m(z) = χ(z)(z/|z|)^m`, for a strict character `χ` modulo `4d`. -/
def IsCompleted (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ) : Prop :=
  1 ≤ d ∧ Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi ∧ AnalyticOn ℂ Lam Set.univ ∧
    (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d m s * Work.FIArea5.S16Hecke.heckeLSeries chi m s)

/-- `Lval = Λ/heckeArch`, so the logarithmic derivatives differ by that of `heckeArch`. -/
lemma lval_logDeriv_eq (d : ℕ) (hd : 1 ≤ d) {m : ℤ} {Lam : ℂ → ℂ}
    (hAn : AnalyticOn ℂ Lam Set.univ) {s : ℂ} (hs : 0 < s.re) (hLs : Lam s ≠ 0) :
    deriv (Lval d m Lam) s / Lval d m Lam s
      = deriv Lam s / Lam s
        - deriv (fun z => Work.FITop4.Bridge.heckeArch d m z) s
            / Work.FITop4.Bridge.heckeArch d m s := by
  have hA : Work.FITop4.Bridge.heckeArch d m s ≠ 0 := heckeArch_ne_zero_of_pos_re d hd m hs
  have hfac : ∀ n : ℕ, s + ((|(m : ℝ)| / 2 : ℝ) : ℂ) ≠ -((n : ℕ) : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.natCast_re] at hre
    have hmm : (0 : ℝ) ≤ |(m : ℝ)| / 2 := by positivity
    have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hdiffA : DifferentiableAt ℂ (fun z => Work.FITop4.Bridge.heckeArch d m z) s := by
    have hfun : (fun z => Work.FITop4.Bridge.heckeArch d m z)
        = fun z => (4 * (d : ℂ) / (Real.pi : ℂ)) ^ z
            * Complex.Gamma (z + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) := by
      funext z; rw [heckeArch_eq]
    rw [hfun]
    exact (DifferentiableAt.const_cpow differentiableAt_id
        (Or.inl (heckeArch_base_ne_zero d hd))).mul
      (DifferentiableAt.comp s (Complex.differentiableAt_Gamma _ hfac)
        (differentiableAt_id.add_const _))
  have hdiffL : DifferentiableAt ℂ Lam s := (hAn.analyticAt (Filter.univ_mem)).differentiableAt
  have key : logDeriv (Lval d m Lam) s
      = logDeriv Lam s - logDeriv (fun z => Work.FITop4.Bridge.heckeArch d m z) s := by
    have hfun : Lval d m Lam = fun z => Lam z / Work.FITop4.Bridge.heckeArch d m z := rfl
    rw [hfun, logDeriv_fun_div s hLs hA hdiffL hdiffA]
  simpa only [logDeriv_apply] using key


/-- **The one-sided logarithmic-derivative bound from its classical inputs.**  Given

* the Hadamard partial fraction for every admissible completion `Λ`,
* the weighted zero sum `Σ_u ord(u)/(1+(t-Im u)²) ≪ log(4d(|m|+|t|+3))`,
* the base-point bound `Re (Λ'/Λ)(2+it) ≪ log(4d(|m|+|t|+3))`,
* the location of the zeros of `Λ` in `[-1,1]`,
* the de la Vallée Poussin region `ZFRoffAxis` and the Siegel bound `ZFRrealAxis ε`,

the one-sided bound `LogDerivReLower ε` holds. -/
theorem logDerivReLower_of (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (hpf : ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ s s₁ : ℂ, Lam s ≠ 0 → Lam s₁ ≠ 0 →
        Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ, (((divR Lam R u : ℤ) : ℂ)
          * (1 / (s - u) - 1 / (s₁ - u)))) Filter.atTop
          (nhds (deriv Lam s / Lam s - deriv Lam s₁ / Lam s₁)))
    (hWZS : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ (t R : ℝ), 1 ≤ R →
        ∑ᶠ u : ℂ, ((divR Lam R u : ℤ) : ℝ) / (1 + (t - u.im) ^ 2)
          ≤ C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)))
    (hBase : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ γ : ℝ,
        -(C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
          ≤ (deriv Lam ((2 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((2 : ℂ) + (γ : ℂ) * Complex.I)).re)
    (hZeros : ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ u : ℂ, Lam u = 0 → -1 ≤ u.re ∧ u.re ≤ 1)
    (hoff : ZFRoffAxis) (hreal : ZFRrealAxis ε) :
    LogDerivReLower ε := by
  obtain ⟨c₁, hc₁, hoff'⟩ := hoff
  obtain ⟨c₂, hc₂, hrealP'⟩ := zfrRealAxisPLight ε hε hε4 hreal
  obtain ⟨CW, hCW, hWZS'⟩ := hWZS
  obtain ⟨CB, hCB, hBase'⟩ := hBase
  refine ⟨min (min c₁ c₂ / 4) (1 / 4), CB + 12 * CW + 7, lt_min (by positivity) (by norm_num),
    by positivity, ?_⟩
  intro d chi m Lam hd hchi hAn hagr s hlo hhi
  have hadm : IsCompleted d chi m Lam := ⟨hd, hchi, hAn, hagr⟩
  have hcpos : 0 < min (min c₁ c₂ / 4) (1 / 4) := lt_min (by positivity) (by norm_num)
  have hc₁' : min (min c₁ c₂ / 4) (1 / 4) ≤ c₁ := by
    have h1 : min c₁ c₂ ≤ c₁ := min_le_left _ _
    have h2 : min c₁ c₂ / 4 ≤ min c₁ c₂ := by
      have : (0 : ℝ) < min c₁ c₂ := lt_min hc₁ hc₂
      linarith
    have h3 : min (min c₁ c₂ / 4) (1 / 4) ≤ min c₁ c₂ / 4 := min_le_left _ _
    linarith
  have hc₂' : min (min c₁ c₂ / 4) (1 / 4) ≤ c₂ := by
    have h1 : min c₁ c₂ ≤ c₂ := min_le_right _ _
    have h2 : min c₁ c₂ / 4 ≤ min c₁ c₂ := by
      have : (0 : ℝ) < min c₁ c₂ := lt_min hc₁ hc₂
      linarith
    have h3 : min (min c₁ c₂ / 4) (1 / 4) ≤ min c₁ c₂ / 4 := min_le_left _ _
    linarith
  have hLpos : 0 < Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) := by
    refine Real.log_pos ?_
    have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg s.im
    have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hLnn : 0 ≤ Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) := hLpos.le
  by_cases hLv : Lval d m Lam s = 0
  · rw [hLv, div_zero]
    simp only [Complex.zero_re]
    exact neg_nonpos.mpr (mul_nonneg (by positivity) hLnn)
  · have hσ_half : (1 : ℝ) / 2 ≤ s.re := by
      have hden : (0 : ℝ) < (d : ℝ) ^ ε := Real.rpow_pos_of_pos (by exact_mod_cast hd) ε
      have hmin1 : min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1))
          (1 / (d : ℝ) ^ ε) ≤ 1 := by
        refine le_trans (min_le_right _ _) ?_
        rw [div_le_one hden]
        exact Real.one_le_rpow (by exact_mod_cast hd) hε.le
      have hcm : min (min c₁ c₂ / 4) (1 / 4)
          * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)) (1 / (d : ℝ) ^ ε)
          ≤ min (min c₁ c₂ / 4) (1 / 4) := by
        calc min (min c₁ c₂ / 4) (1 / 4)
            * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)) (1 / (d : ℝ) ^ ε)
            ≤ min (min c₁ c₂ / 4) (1 / 4) * 1 :=
              mul_le_mul_of_nonneg_left hmin1 hcpos.le
          _ = min (min c₁ c₂ / 4) (1 / 4) := mul_one _
      have hquarter : min (min c₁ c₂ / 4) (1 / 4) ≤ 1 / 4 := min_le_right _ _
      linarith
    have hA : Work.FITop4.Bridge.heckeArch d m s ≠ 0 :=
      heckeArch_ne_zero_of_pos_re d hd m (by linarith)
    have hLs : Lam s ≠ 0 := by
      intro h0
      exact hLv (by rw [Lval, h0, zero_div])
    have hs₁_ne : Lam ((2 : ℂ) + (s.im : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have hz2 := (hZeros d chi m Lam hadm _ h0).2
      have hre : ((2 : ℂ) + (s.im : ℂ) * Complex.I).re = 2 := by simp
      rw [hre] at hz2
      norm_num at hz2
    have hleft : ∀ u : ℂ, Lam u = 0 → |s.im - u.im| < 1 → u.re ≤ s.re := by
      intro u hu hlt
      by_cases hA0 : Work.FITop4.Bridge.heckeArch d m u = 0
      · have := heckeArch_eq_zero_imp_re_le_zero d hd hA0
        linarith
      · have hLval_u : Lval d m Lam u = 0 := by rw [Lval, hu, zero_div]
        by_cases hexc : u.im = 0 ∧ PsiRealPrimary chi m
        · have hzr : u.re ≤ 1 - c₂ * (1 / (d : ℝ) ^ ε) := by
            by_contra hcon
            push Not at hcon
            have hcon' : 1 - c₂ / (d : ℝ) ^ ε < u.re := by
              have he : c₂ * (1 / (d : ℝ) ^ ε) = c₂ / (d : ℝ) ^ ε := by
                rw [div_eq_mul_inv]; ring
              linarith
            exact (hrealP' d chi m Lam hd hchi hAn hagr hexc.2 u hexc.1 hcon'
              (by have := (hZeros d chi m Lam hadm u hu).2; linarith)) hLval_u
          have hcmp : min (min c₁ c₂ / 4) (1 / 4)
              * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)) (1 / (d : ℝ) ^ ε)
              ≤ c₂ * (1 / (d : ℝ) ^ ε) := by
            have h2 : min (min c₁ c₂ / 4) (1 / 4) * (1 / (d : ℝ) ^ ε)
                ≤ c₂ * (1 / (d : ℝ) ^ ε) :=
              mul_le_mul_of_nonneg_right hc₂' (by positivity)
            have h3 : min (min c₁ c₂ / 4) (1 / 4)
                * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)) (1 / (d : ℝ) ^ ε)
                ≤ min (min c₁ c₂ / 4) (1 / 4) * (1 / (d : ℝ) ^ ε) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) hcpos.le
            linarith
          linarith
        · have hzr : u.re ≤ 1 - c₁ * (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|)) := by
            by_contra hcon
            push Not at hcon
            have hcon' : 1 - c₁ / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|) < u.re := by
              have he : c₁ * (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|))
                  = c₁ / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|) := by
                rw [div_eq_mul_inv]; ring
              linarith
            exact (hoff' d chi m Lam hd hchi hAn hagr u hcon'
              (by have := (hZeros d chi m Lam hadm u hu).2; linarith) hexc) hLval_u
          have hlogpos' : 0 < Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|) := by
            refine Real.log_pos ?_
            have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg u.im
            have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
            nlinarith
          have hlogpos'' : 0 < Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1) := by
            refine Real.log_pos ?_
            have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg s.im
            have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
            nlinarith
          have hlog1 : Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|)
              ≤ Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1) := by
            refine Real.log_le_log (by positivity) ?_
            have h1 : |u.im| ≤ |u.im - s.im| + |s.im| := by
              have := abs_add_le (u.im - s.im) s.im
              simpa using this
            have h2 : |u.im - s.im| < 1 := by rw [abs_sub_comm]; exact hlt
            linarith
          have hcmp : min (min c₁ c₂ / 4) (1 / 4)
              * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)) (1 / (d : ℝ) ^ ε)
              ≤ c₁ * (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|)) := by
            have h3 : min (min c₁ c₂ / 4) (1 / 4)
                * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)) (1 / (d : ℝ) ^ ε)
                ≤ min (min c₁ c₂ / 4) (1 / 4)
                  * (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)) :=
              mul_le_mul_of_nonneg_left (min_le_left _ _) hcpos.le
            have h5 : min (min c₁ c₂ / 4) (1 / 4)
                * (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1))
                ≤ c₁ * (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)) :=
              mul_le_mul_of_nonneg_right hc₁' (by positivity)
            have h6 : (1 : ℝ) / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)
                ≤ 1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|) := by
              rw [one_div, one_div]
              exact inv_anti₀ hlogpos' hlog1
            have h7 : c₁ * (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1))
                ≤ c₁ * (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|)) :=
              mul_le_mul_of_nonneg_left h6 hc₁.le
            linarith
          linarith
    have hmain := logDeriv_re_ge_of_pf (Λ := Lam) hAn (hpf d chi m Lam hadm)
      (hZeros d chi m Lam hadm) (s := s) (σ := s.re) (t := s.im)
      (W := CW * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)))
      (by apply Complex.ext <;> simp) hleft
      (fun R hR => hWZS' d chi m Lam hadm s.im R hR) (by linarith) hhi hLs hs₁_ne
    have hbasei := hBase' d chi m Lam hadm s.im
    have harch := logDeriv_heckeArch_re_le d hd m (s := s) hσ_half hhi
    rw [logDeriv_apply] at harch
    have hident := lval_logDeriv_eq (m := m) d hd hAn (s := s) (by linarith) hLs
    rw [hident, Complex.sub_re]
    linarith


/-- **The one-sided bound from the Hadamard partial fraction and the base bounds.**  This is
`logDerivReLower_of` with its weighted-zero-sum hypothesis *derived* (via `wzsOfPfDiff`) from the
partial fraction and the bounds on `Re (Λ'/Λ)` at the two vertical lines `re = 2`, `re = -2`;
the three bound functions are those of the genuinely classical inputs (the base bounds of *FI*
§16, available from the absolutely convergent Euler product and the functional equation). -/
theorem logDerivReLower_of_baseBounds (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (hpf : ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ s s₁ : ℂ, Lam s ≠ 0 → Lam s₁ ≠ 0 →
        Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ, (((divR Lam R u : ℤ) : ℂ)
          * (1 / (s - u) - 1 / (s₁ - u)))) Filter.atTop
          (nhds (deriv Lam s / Lam s - deriv Lam s₁ / Lam s₁)))
    (hBase2u : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ γ : ℝ,
        (deriv Lam ((2 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((2 : ℂ) + (γ : ℂ) * Complex.I)).re
          ≤ C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
    (hBase2l : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ γ : ℝ,
        -(C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
          ≤ (deriv Lam ((2 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((2 : ℂ) + (γ : ℂ) * Complex.I)).re)
    (hBasem2l : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ γ : ℝ,
        -(C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
          ≤ (deriv Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)).re)
    (hZeros : ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ u : ℂ, Lam u = 0 → -1 ≤ u.re ∧ u.re ≤ 1)
    (hoff : ZFRoffAxis) (hreal : ZFRrealAxis ε) :
    LogDerivReLower ε := by
  obtain ⟨C1, hC1, hB2u⟩ := hBase2u
  obtain ⟨C2, hC2, hB2l⟩ := hBase2l
  obtain ⟨C3, hC3, hBm2l⟩ := hBasem2l
  have hlogpos : ∀ (d : ℕ) (m : ℤ) (t : ℝ), 1 ≤ d →
      0 < Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)) := by
    intro d m t hd
    refine Real.log_pos ?_
    have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg t
    have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hWZS : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ (t R : ℝ), 1 ≤ R →
        ∑ᶠ u : ℂ, ((divR Lam R u : ℤ) : ℝ) / (1 + (t - u.im) ^ 2)
          ≤ C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)) := by
    refine ⟨13 * (C1 + (C2 + C3)), by positivity, ?_⟩
    intro d chi m Lam hadm t R hR
    have hd : 1 ≤ d := hadm.1
    have hL := hlogpos d m t hd
    have hDiff : Differentiable ℂ Lam :=
      differentiableOn_univ.mp hadm.2.2.1.differentiableOn
    have hBm2' : ∀ γ : ℝ,
        -((C2 + C3) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
          ≤ (deriv Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)
              / Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)).re := by
      intro γ
      have hb := hBm2l d chi m Lam hadm γ
      have hle : C3 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3))
          ≤ (C2 + C3) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
        have hgamma := hlogpos d m γ hd
        nlinarith [hgamma.le, hC2]
      linarith
    have hw := wzsOfPfDiff Lam hDiff (hpf d chi m Lam hadm) (hZeros d chi m Lam hadm)
      (fun γ : ℝ => C1 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
      (fun γ : ℝ => (C2 + C3) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
      (fun γ => hB2u d chi m Lam hadm γ) hBm2' t R hR
    simp only [divR] at hw ⊢
    have hgoal : 13 * (C1 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3))
        + (C2 + C3) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)))
        = 13 * (C1 + (C2 + C3)) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)) := by
      ring
    linarith [hw, hgoal.le, hgoal.ge]
  exact logDerivReLower_of ε hε hε4 hpf hWZS ⟨C2, hC2, hB2l⟩ hZeros hoff hreal

end

end Work.FIArea6Hecke.R

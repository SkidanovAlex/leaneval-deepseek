/-
# `Submission.Work.FIChain.s3RemPlus_cutfree_defs` — the `ℓ`-free REM integrands

The two forms of the REM integrand of the `(1.7)`-split of the `λ⁺`-level integral
(`Submission/Work/FIChain/s3RemPlus_defs.lean`), **in the regime where both `(1.7)`-cuts are
`ℓ`-free** (`x ≤ sz` and `z ≤ Cm`):

* `cfU x Cm ℓ u = Σ_{d ≤ ⌊u⌋₊} μ d · (r̃(ℓ d, x) − r̃(ℓ d, ⌊ℓ·Cm·u⌋₊))` — the integrand in the
  `u`-variable, i.e. the `s3RemPlus` integrand with `⌊min (ℓ·sz) x⌋₊` replaced by `x` and
  `⌊max (ℓ·z) (ℓ·Cm·u)⌋₊` replaced by `⌊ℓ·Cm·u⌋₊` (`cf_integrand_eq`);

* `cfT x Cm ℓ t` — the same thing after the substitution `t := ℓ·Cm·u`, written with a range of
  summation independent of `t` (an indicator `d·ℓ·Cm ≤ t`) so that it is manifestly a finite sum of
  measurable functions of `t`:

      cfT x Cm ℓ t = Σ_{d ≤ ⌊x/Cm⌋₊} [d·ℓ·Cm ≤ t] · μ d · (r̃(ℓ d, x) − r̃(ℓ d, ⌊t⌋₊)).

  The two agree: `cfU x Cm ℓ u = cfT x Cm ℓ (ℓ·Cm·u)` (`cfU_eq_cfT_mul`), which is the form in
  which the substitution `t := ℓ·Cm·u` of `∫_1^{x/(ℓ·Cm)} (du/u)·cfU u` may be evaluated
  (`cf_integral_subst`).  After the substitution the modulus of every term of the fibre is
  `ζ = ℓ·d ≤ t/Cm` and **both** `r̃`-arguments (`x` and `⌊t⌋₊`) are independent of `ℓ` — which is
  exactly what `(R′)` (`Work.FIChain.remainder_all_at_07`) can consume.

Definitions only here; the lemmas about them live in the companion files
`cf_integrand_eq`, `cf_integral_subst`, `cf_abs_integral_le`, `cf_pairs_le`, `cf_fibre_le`,
`cf_sum_integral_swap`, all of which import this module.
-/
import Mathlib
import Submission.Work.FIChain.s3RemPlus_defs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The honest remainder `r̃(ζ,m)` of the `λ⁺`-half (`Submission.ASP.rtildeFull` at the FI data). -/
abbrev cfR (ζ m : ℕ) : ℝ :=
  Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
    Submission.ASP.FIgtil Submission.ASP.FIa ζ m

/-- The REM integrand of `s3RemPlus` in the `u`-variable, in the `ℓ`-free regime: both `(1.7)`-cuts
are replaced by their `ℓ`-free values (`⌊min (ℓ·sz) x⌋₊ = x`, `⌊max (ℓ·z) (ℓ·Cm·u)⌋₊ = ⌊ℓ·Cm·u⌋₊`
for `u ≥ 1`; for `u < 1` both sums are empty). -/
def cfU (x : ℕ) (Cm ℓ : ℕ) (u : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
    (cfR (ℓ * d) x - cfR (ℓ * d) ⌊((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)

/-- The same integrand after the substitution `t := ℓ·Cm·u`, with the range of summation made
independent of `t` (the indicator `d·ℓ·Cm ≤ t`): this is the form in which the fibre grouping
`ζ = ℓ·d` and the `(R′)`-application are performed. -/
def cfT (x : ℕ) (Cm ℓ : ℕ) (t : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊(x : ℝ) / (Cm : ℝ)⌋₊,
    if (d : ℝ) * ((ℓ : ℝ) * (Cm : ℝ)) ≤ t then
      (ArithmeticFunction.moebius d : ℝ) * (cfR (ℓ * d) x - cfR (ℓ * d) ⌊t⌋₊)
    else 0

/-- `cfT` vanishes below the substitution scale `ℓ·Cm`. -/
lemma cfT_eq_zero_of_lt (x Cm ℓ : ℕ) {t : ℝ} (h : t < (ℓ : ℝ) * (Cm : ℝ)) :
    cfT x Cm ℓ t = 0 := by
  rw [cfT]
  refine Finset.sum_eq_zero (fun d hd => ?_)
  rw [Finset.mem_Icc] at hd
  have hnn : (0 : ℝ) ≤ (ℓ : ℝ) * (Cm : ℝ) := by positivity
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.1
  have hle : (ℓ : ℝ) * (Cm : ℝ) ≤ (d : ℝ) * ((ℓ : ℝ) * (Cm : ℝ)) := by
    nlinarith [hd1, hnn]
  rw [if_neg (by linarith)]

end

end Work.FIChain

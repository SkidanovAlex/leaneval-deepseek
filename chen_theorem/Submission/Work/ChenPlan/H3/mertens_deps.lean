import Mathlib
import Submission.ChenPlan.Interfaces
import Submission.Chen.Switch
import Submission.Work.ChenPlan.H3.Defs
import Submission.Commons.NumberTheory.Mertens.first_mertens_bounded
import Submission.Commons.NumberTheory.Mertens.sum_log_div_le_log_sharp
import Submission.Commons.NumberTheory.Mertens.mertens_range_gap_bound

/-!
# Import bundle for the odd-prime Mertens interval estimate (Chen `h3`, v6 repair)

This module only collects the imports needed to *state* (and prove) the interval form of Mertens'
first theorem for the density `ν(p) = 1/(p-1)` on the odd primes, used to establish
`Submission.ChenPlan.IsLinearMertens` for the sieve problems of Chen's `h1`/`h3`
(all odd primes below the limit, `ν = invTotient`):

* `oddLt` / `oddPrimLt` / `mem_oddLt` (`Submission.Chen.Switch`, `...ChenEight`);
* `Commons.NumberTheory.Mertens.sum_log_div_le_log_sharp`
  (`∃ A > 0, ∀ y ≥ 2, |Σ_{p ≤ y} log p/(p-1) − log y| ≤ A`);
* `Commons.NumberTheory.Mertens.first_mertens_bounded`, `mertens_range_gap_bound`
  (the `log p / p` form, and the `Σ_{Icc u v}` vs `Σ_{primesLE}` splitting technique).
-/

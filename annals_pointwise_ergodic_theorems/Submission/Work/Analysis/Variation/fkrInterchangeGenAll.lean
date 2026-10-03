/-
# The `fkr` interchange for *all* pairs of exponents with `R < s` and `R < p`

Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, arXiv:2008.00857, Lemma `fkr` (the **interchange of variational and Lebesgue norms**)
is available in this workspace in two forms:

* `Work.KMTPlan.A6.FkrInterchange`: the *diagonal* case, where the variation exponent and the
  Lebesgue exponent coincide (`p = s`);
* `Work.KMTAreas.A7Hi.fkrInterchangeGen`: the case `s ≤ p` of the two exponents (there the
  pointwise `ℓ^s`-norm over the dyadic pieces is passed through `L^p` by **Minkowski's inequality
  for the `ℓ^s`-norm**, which needs `s ≤ p`).

This file supplies the remaining case `p ≤ s`, and hence the statement for *all* pairs `(p, s)`
with `1 ≤ R < p` and `R < s` -- `Work.Analysis.Variation.fkrInterchangeGenAll`.

The new ingredient is one elementary monotonicity: **the variation part is antitone in its
exponent**.  For `1 ≤ p ≤ s` the finite `ℓ^r`-"norms" of a vector decrease in `r`, so
`varPart s a ≤ varPart p a` (`varPart_antitone` below).  Then, in the regime `p ≤ s`, one
compares `varPart s ≤ varPart p` pointwise and applies the diagonal case `FkrInterchange` at the
(diagonal) exponent `p`, whose right-hand side is *the same* `V^R(ℕ; L^p)`-norm that the target
asks for.

The elementary `ℓ^r`-comparison is the workspace's
`Work.KMTAreas.A7Hi.rpow_sum_le_rpow_sum_of_le` (for `0 < P ≤ R`, the finite `ℓ^R`-norm of an
`ℝ≥0∞`-family is dominated by its `ℓ^P`-norm) together with the identification of the `WithLp`
norm of a finite vector with the `rpow`-sum
(`Work.KMTAreas.A7.ofReal_norm_toLp_eq_sum`), which is exactly the shape of the summands of
`Submission.PointwiseErgodicTheorems.varPart`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Hi.rpow_sum_le_rpow_sum_of_le
import Submission.Work.KMTAreas.A7.variationalNorm_mul_le
import Submission.Work.KMTPlan.A6.FkrStep
import Submission.Work.KMTPlan.A6.fkrW_zero_varPart

set_option autoImplicit false

namespace Work.Analysis.Variation

open MeasureTheory
open scoped ENNReal BigOperators

/-- **The variation part is antitone in the variation exponent.**  For `1 ≤ p ≤ s` and every
sequence `a : ℕ → ℂ`,

  `varPart s a ≤ varPart p a`.

Indeed, for a fixed chain `N` the cost `(∑_i ‖a (N (i+1)) - a (N i)‖^s)^{1/s}` is the finite
`ℓ^s`-norm of the vector of moduli, and the `ℓ^r`-norms of a finite vector decrease in `r`
(`Work.KMTAreas.A7Hi.rpow_sum_le_rpow_sum_of_le`); taking the supremum over chains preserves the
inequality. -/
theorem varPart_antitone {p s : NNReal} (hp : 1 ≤ p) (hps : p ≤ s) (a : ℕ → ℂ) :
    Submission.PointwiseErgodicTheorems.varPart s a
      ≤ Submission.PointwiseErgodicTheorems.varPart p a := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hp)
  have hpsR : (p : ℝ) ≤ (s : ℝ) := by exact_mod_cast hps
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  refine le_trans ?_ (le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl)))
  rw [Work.KMTAreas.A7.ofReal_norm_toLp_eq_sum s (le_trans hp hps)
        (fun i : Fin J => a (N (i + 1)) - a (N i)),
      Work.KMTAreas.A7.ofReal_norm_toLp_eq_sum p hp
        (fun i : Fin J => a (N (i + 1)) - a (N i))]
  exact Work.KMTAreas.A7Hi.rpow_sum_le_rpow_sum_of_le hp0 hpsR
    (fun i : Fin J => ‖a (N (i + 1)) - a (N i)‖ₑ)

end Work.Analysis.Variation

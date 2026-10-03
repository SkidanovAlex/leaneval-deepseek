/-
# Vocabulary for the triangular-smoothing (`triConv`) variational estimate

This module fixes the two auxiliary functionals used in the proof of
`Work.KMTAreas.A7.lacDilTriVar` (the martingale/Lépingle half of the lacunary bump-dilation
variational estimate).

* `varPathCL L y r` — the `r`-variation of a sequence `y : ℕ → ℂ` over *strictly increasing*
  finite chains of levels that are bounded by `L`.  This is the truncated version of the corpus's
  `Work.Analysis.Hilbert.varPathC` (`varPathC y r = ⨆ L, varPathCL L y r`).

* `latVarSupR r L τ h` — the *reversed-chain* variation of the shifted dyadic lattice conditional
  expectations `k ↦ latticeExpR k τ h` at the dyadic horizon `L`: the supremum, over strictly
  increasing `u : ℕ → ℕ` and over `J`, of
  `(∑_{j < J} |latticeExpR (L - u (j+1)) τ h x - latticeExpR (L - u j) τ h x| ^ r) ^ (1/r)`.
  This is *exactly* the integrand whose `ℓ^p` norm is bounded by the already proved martingale
  Lépingle estimate `Work.Analysis.Hilbert.latticeWalk_var_le`.

The point of the reversal `k ↦ L - k` is that `latticeExpR · τ h` is a *reverse* martingale (the
σ-algebras `latticeSpan k τ` decrease with `k`), so that the increasing chains in `n` of the
application correspond to the decreasing chains `j ↦ L - u j` of the reversed (honest) martingale
`j ↦ latticeSpan (L - j) τ`.
-/
import Mathlib
import ChallengeDeps
import Submission.VarNorm
import Submission.Work.Analysis.Hilbert.lattice_exp_average

set_option autoImplicit false

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped ENNReal BigOperators

noncomputable section

/-- The `r`-variation of a sequence over strictly increasing chains of levels bounded by `L`. -/
def varPathCL (L : ℕ) (y : ℕ → ℂ) (r : ℝ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (u : Fin (J + 1) → ℕ), ⨆ (_ : StrictMono u) (_ : ∀ i, u i ≤ L),
    ENNReal.ofReal ((∑ j : Fin J, ‖y (u j.succ) - y (u j.castSucc)‖ ^ r) ^ (1 / r))

/-- The reversed-chain variation of the shifted dyadic lattice conditional expectations at the
dyadic horizon `L`. -/
def latVarSupR (r : NNReal) (L : ℕ) (τ : ℤ) (h : ℤ → ℝ) : ℤ → ℝ≥0∞ :=
  fun x => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
    ENNReal.ofReal ((∑ j ∈ Finset.range J,
      |Work.Analysis.Hilbert.latticeExpR (L - u.1 (j + 1)) τ h x
        - Work.Analysis.Hilbert.latticeExpR (L - u.1 j) τ h x| ^ (r : ℝ)) ^ (1 / (r : ℝ)))

end

end Work.KMTAreas.A7

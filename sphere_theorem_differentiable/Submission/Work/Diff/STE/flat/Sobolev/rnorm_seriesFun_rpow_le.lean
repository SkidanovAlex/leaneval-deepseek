import Mathlib
import Submission.Work.Diff.STE.flat.norm_seriesFun_rpow_le
import Submission.Work.Diff.STE.flat.Sobolev.block_rnorm_le_rpow
import Submission.Work.Diff.STE.flat.Sobolev.tsum_annulus
import Submission.Work.Diff.STE.flat.Sobolev.rnorm_tsum_le
import Submission.Work.Diff.STE.flat.Sobolev.summable_blockMass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The sharp `L^{2p}` Sobolev bound on the torus (corrected statement)

The statement requested at `Submission/Work/Diff/STE/flat/norm_seriesFun_rpow_le.lean` is false:
its right-hand side exponent is written `(1 / 2)`, which Lean elaborates as natural number division
(`(1 : ℕ) / 2 = 0`), so that the right-hand side degenerates to the constant `C`; see
`Work.Diff.STE.flat.requested_statement_false` there for the formal refutation.

This file proves the statement *intended* by the docstring, i.e. with the real exponent
`(1 / 2 : ℝ)`:

`‖seriesFun γ‖_{L^{2p}} ≤ C · (Σ_k ⟨k⟩^{2j} ‖γ k‖²)^{1/2}`   for   `j > n/2 - n/(2p)`.

It is the sharp Sobolev embedding `H^j(𝕋^ι) ⊆ L^{2p}(𝕋^ι)`; the exponent threshold is exactly the
critical one, so the result is *not* available from Mathlib.

Proof: the assembly `Work.Diff.STE.flat.exists_bound_of_pieces` (in the sibling file) reduces the
statement to four analytic inputs, which are supplied here:

* `Work.Diff.STE.flat.Sobolev.block_rnorm_le_rpow` — the per-dyadic-block Littlewood–Paley
  estimate (with the real exponent `(1 / 2 : ℝ)`; the originally requested
  `Work.Diff.STE.flat.Sobolev.block_rnorm_le` has the same `(1 : ℕ)/2`-elision defect as the
  statement refuted here, and the prover of that lemma machine-checked its negation there);
* `Work.Diff.STE.flat.Sobolev.tsum_annulus` — the rearrangement of a lattice series into its
  dyadic blocks (used both for the pointwise decomposition of `seriesFun` and for the identity
  `Σ_m blockMass j m γ = Σ_k (wt k)^j ‖γ k‖²`);
* `Work.Diff.STE.flat.Sobolev.summable_blockMass` — summability of the block masses;
* `Work.Diff.STE.flat.Sobolev.rnorm_tsum_le` — Minkowski's inequality for a countable series in
  `L^q`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace Work.Diff.STE.flat.Sobolev

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Sharp `L^{2p}` Sobolev bound for a Fourier series with a real (fractional) weight level.**
For `p ≥ 1` real and a real level `j > n/2 - n/(2p)` (`n = Fintype.card ι`, and `wt k = ⟨k⟩²` so
that `(wt k)^j = ⟨k⟩^{2j}` displays the level `j`) one has
`‖seriesFun γ‖_{L^{2p}} ≤ C * (∑_k (wt k)^j ‖γ k‖²)^{1/2}`, with `C` depending only on `ι`, `p`, `j`.

This is the statement of `Work.Diff.STE.flat.norm_seriesFun_rpow_le` with the (intended) **real**
exponent `(1 / 2 : ℝ)` on the right-hand side; the exponent `(1 / 2)` without the type ascription
elaborates as `(1 : ℕ) / 2 = 0`, which makes the original statement false (see
`Work.Diff.STE.flat.requested_statement_false`). -/
theorem rnorm_seriesFun_rpow_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (hp : 1 ≤ p) (j : ℝ)
    (hj : (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)) < j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ γ : (ι → ℤ) → ℂ,
      Summable (fun k : ι → ℤ => ((Work.Diff.STE.wt k) ^ j) * ‖γ k‖ ^ 2) →
      (∫ x in Work.Diff.STE.unitCube (ι := ι),
          ‖Work.Diff.STE.seriesFun γ x‖ ^ (2 * p)) ^ (1 / (2 * p))
        ≤ C * (∑' k : ι → ℤ, ((Work.Diff.STE.wt k) ^ j) * ‖γ k‖ ^ 2) ^ (1 / 2 : ℝ) := by
  classical
  refine Work.Diff.STE.flat.exists_bound_of_pieces p hp j hj
    ((6 : ℝ) ^ ((Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p))))
    (j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))
    (Real.rpow_nonneg (by norm_num) _) (sub_pos.mpr hj) ?_ ?_ ?_ ?_ ?_
  · intro m γ h1 h2
    exact block_rnorm_le_rpow p hp j (le_of_lt hj) m γ h1 h2
  · intro g hg
    exact tsum_annulus (E := ℂ) g hg
  · intro g hg
    exact tsum_annulus (E := ℝ) g hg
  · intro γ h1 h2
    exact summable_blockMass j γ h2
  · intro q hq g f hm hf hfg hsum
    exact rnorm_tsum_le q hq hm hf hfg hsum

end Work.Diff.STE.flat.Sobolev

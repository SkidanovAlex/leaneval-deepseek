import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.ResMath.resA_norm_le
import Submission.Work.ResMath.resS_rowsum_reindex

/-!
# The Gaussian weight of the window, as a function of an integer index

The retained ideal weights of output `k` of the 1-D resampling word are

`auWi p α s t k i = (1/(2α))·e^{−π (t·(auK s t k + i − auM p α) − s·k)²/(α²t²)}`.

Writing `n = auK s t k + i − auM p α` for the (un-wrapped) window index, this is

`auPsi α s t k n = (1/(2α))·e^{−π (n − s·k/t)²/α² }`,

the Gaussian weight attached to the integer `n` (and `t ≠ 0` is needed for the
identification).  Because `i ↦ n` is injective, the sum of the retained weights
of output `k` is a partial sum of `∑' n : ℤ, auPsi α s t k n`.

Reindexing that full sum by `ℤ ≃ Fin s × ℤ` (`Int.divModEquiv`) turns it into the
double coset sum defining the `k`-th row of the Gaussian matrix `resSmat s t α`,
whose row sum is `≤ 1 + α⁻¹`; hence `∑' n, auPsi α s t k n = ∑ j, ‖(resA s t α) k j‖ ≤ 3/4`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- The Gaussian weight `(1/(2α))·e^{−π(n − sk/t)²/α²}` of the integer index `n`:
`auWi p α s t k i` evaluated at `n = auK s t k + i − auM p α`. -/
noncomputable def auPsi (α s t k : ℕ) (n : ℤ) : ℝ :=
  (1 / (2 * (α : ℝ))) * Real.exp (-(Real.pi / (α : ℝ) ^ 2) *
    ((n : ℝ) - (s : ℝ) * (k : ℝ) / (t : ℝ)) ^ 2)

end Work.Resample

/-
# Area 4 (round 6): the log-sine Fourier step `expLog6 ≤ (log N+1)² · M`

The target `Work.FIArea4.A6R2.ExpLogBound6` is *FI* (15.4)–(15.7): the exponential sum
`expLog6`, which carries the round-6 logarithmic weight `Work.FITop4.logFac6`, is dominated by
`(log N + 1)²` times any uniform bound `M` for the *separated* sums `expSum6 ℓ`.

The `A6R2` vocabulary (`Submission/Work/FIArea4/A6R2/Defs.lean`) was introduced as a copy of the
`A6psi` vocabulary (`Submission/Work/FIArea4/A6psi/Defs.lean`, at FI's ratio symbol
`(z₂/z₁|d)`): `w6 = S15w6`, `coef6 = S15coef6`, `expSum6 = S15expSum6`,
`expLog6 = S15expLog6` — the two are **definitionally equal** (same bodies, same `S15ixSet`,
same `S15theta`, `S15phase`, `logFac6`), and only the names differ.  Hence the already-proved
colleague lemma

  `Work.FIArea4.A6psi.expLog6_le_expSum6`,
  `∃ C > 0, ‖S15expLog6 Pa X j β u t‖ ≤ C (log Pa.N + 1)² M` for every uniform bound
  `M ≥ sup_ℓ ‖S15expSum6 Pa X j β ℓ u t‖`,

whose proof is the paper's step (per-pair log-sine expansion of `logFac6` on the polar box,
`Work.FIArea4.S15red.logFac_expansion` with `Σ_ℓ ‖c ℓ‖ ≤ C₀ (log N + 1)²`, summed against
`S15theta ℓ = e^{iℓ(α₂-α₁)}` and exchanged with the finite index-set sum), transfers verbatim
to `ExpLogBound6`.

This file therefore records the (definitional) identification of the two vocabularies and
transports that lemma.
-/
import Mathlib
import Submission.Work.FIArea4.A6R2.Defs
import Submission.Work.FIArea4.A6psi.expLog6_le_expSum6

namespace Work.FIArea4.A6R2

open Finset
open scoped BigOperators

noncomputable section

/-! ## 1. The two round-6 vocabularies coincide definitionally -/

/-- The round-6 weight `w6` of `A6R2` is the `A6psi` weight `S15w6`. -/
lemma w6_eq_S15w6 (i : S15Id) : w6 i = Work.FIArea4.A6psi.S15w6 i := rfl

/-- The round-6 coefficient `coef6` of `A6R2` is the `A6psi` coefficient `S15coef6`. -/
lemma coef6_eq_S15coef6 (β : GaussianInt → ℂ) (i : S15Id) :
    coef6 β i = Work.FIArea4.A6psi.S15coef6 β i := rfl

/-- The separated round-6 sums `expSum6` and `S15expSum6` agree. -/
lemma expSum6_eq_S15expSum6 (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ)
    (u t : ℝ) :
    expSum6 Pa X j β ℓ u t = Work.FIArea4.A6psi.S15expSum6 Pa X j β ℓ u t := rfl

/-- The `logFac6`-weighted round-6 sums `expLog6` and `S15expLog6` agree. -/
lemma expLog6_eq_S15expLog6 (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ)
    (u t : ℝ) :
    expLog6 Pa X j β u t = Work.FIArea4.A6psi.S15expLog6 Pa X j β u t := rfl

/-! ## 2. The log-sine Fourier step -/

theorem expLogBound6 : Work.FIArea4.A6R2.ExpLogBound6 := by
  obtain ⟨C, hC, h⟩ := Work.FIArea4.A6psi.expLog6_le_expSum6
  exact ⟨C, hC, fun Pa X j φ β u t M hβ hX hM => h Pa X j φ β u t M hβ hX hM⟩

end

end Work.FIArea4.A6R2

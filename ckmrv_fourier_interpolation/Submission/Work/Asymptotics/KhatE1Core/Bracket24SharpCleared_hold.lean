import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24E2PrimeDefs
import Submission.Work.Asymptotics.KhatE1Core.Bracket24E2Prime_bound
import Submission.Work.Asymptotics.KhatE1Core.Bracket24TailCore
import Submission.Work.Asymptotics.KhatE1Core.Bracket24TailCore_proof

namespace Work.Asymptotics.KhatE1Core

/-! See `Submission/Work/Asymptotics/KhatE1Core/Bracket24E2PrimeDefs.lean` for the reduction
`Bracket24SharpClearedRaw_of_pieces'`, `Bracket24E2Prime_bound` for the *proved* bound on the
explicit `E(z)²`-coefficient, and `Bracket24TailCore.lean` for the master splitting

  `Sh τ z · Bracket24 ℓ τ z = KPlus24Group + KMinus24Group`

and the reduction `Bracket24Tail'_of_core : Bracket24TailCore ℓ → Bracket24Tail' ℓ`.

The split-form tail bound `Bracket24TailCore` — the sharp `d = 24` bracket bound, *equivalent*
to the target itself given `Bracket24E2Prime_bound` — is proved in
`Submission/Work/Asymptotics/KhatE1Core/Bracket24TailCore_proof.lean`; the coefficient-wise
inputs are `KhatE1Core/Bracket24BCoeffs.lean` (the explicit higher `E(z)^k`-coefficients
`Bracket24B4`, `Bracket24B6`, `Bracket24B7`), the bound `KhatE1Core/Bracket24B4Bound_proof.lean`
(the `E(z)^4`-coefficient cancellation, the `d = 24` analogue of `KdevA4plusBound`), the crude
bounds `Bracket24B6Bound_proof`/`Bracket24B7Bound_proof`, the `E(z)³`- and `E(z)⁵`-coefficient
bounds in `Bracket24P24Bound.lean` (`Big 1`), and the first-order identities
`KhatE1/E1combo24_first_order.lean`, `KhatE1/E1combo8FirstOrderBound.lean`. -/

/-- The tail bound: the split-form bound `Bracket24TailCore`, proved in
`Submission/Work/Asymptotics/KhatE1Core/Bracket24TailCore_proof.lean`. -/
theorem Bracket24Tail'_hold (ℓ : Work.Kernels.LogLambdaData) : Bracket24Tail' ℓ :=
  Bracket24Tail'_of_core ℓ (Bracket24TailCore_proof ℓ)

theorem Bracket24SharpCleared_hold (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.KhatE1.Bracket24 ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) :=
  Bracket24SharpClearedRaw_of_pieces' ℓ (Bracket24E2Prime_bound ℓ) (Bracket24Tail'_hold ℓ)

end Work.Asymptotics.KhatE1Core

import Mathlib
import Submission.Work.Asymptotics.KhatE1.ShBracketAux
import Submission.Work.Asymptotics.KhatE1Core.Bracket24SharpCleared_hold

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-!
# The sharp `d = 24` funnel bracket

The target of this file is the sharp bound on the explicit bracket

  `Bracket24 ℓ τ z = (K₊^{(24)} - 𝒢₊^{(24)}) + (3456π)⁻¹(E(z)(R24 - R24_p0) + Dev24Sum - A·E(z))`

on the funnel strip `τ ∈ 𝔽`, `0 ≤ Re z ≤ 1`, `Im z = t ≥ Im τ + 1`:

  `‖Bracket24 ℓ τ z‖ ≤ C ‖q(τ)‖ (scale τ)^N (1+t)^M e^{-2πt}`.

## The `Sh`-cleared form

By `Kdev24BracketSharp_of_cleared` (`KhatE1/ShBracketAux.lean`) and `‖Sh τ z‖ ≥ 1/16` on the
strip, the target is *equivalent* to the `Sh`-cleared bound `Bracket24SharpCleared ℓ`, which is
proved by the `Sh`-cleared `d = 24` chain:

* `KhatE1Core.Bracket24SharpCleared_hold` — the `Sh`-cleared bound, from the split-form tail
  bound `KhatE1Core.Bracket24TailCore` and the explicit `E(z)²`-coefficient bound;
* `KhatE1Core/Bracket24TailCore_proof.lean` — the tail bound, from `Bracket24ExpansionHold_proof`;
* `KhatE1/Bracket24E2_bound.lean`, `KhatE1Core/Bracket24E2Prime_bound.lean` — the `E(z)²`-coefficient.

The `K₊`- and `K₋`-groups of the split (`KhatE1Core.KPlus24Group`, `KMinus24Group`) are those of
`KhatE1Core/Bracket24TailCore.lean`, and the splitting identity `Sh_mul_Bracket24_master` there
uses the `Sh`-clearing lemmas of `KhatE1/ShBracketAux.lean`.
-/

/-- **The sharp `d = 24` bracket bound** (the requested statement).  It follows from the
`Sh`-cleared bound `KhatE1Core.Bracket24SharpCleared_hold` via
`Kdev24BracketSharp_of_cleared`, using `‖Sh τ z‖ ≥ 1/16` on the strip. -/
theorem Kdev24BracketSharp (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.KhatE1.Bracket24 ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) :=
  Kdev24BracketSharp_of_cleared ℓ (Work.Asymptotics.KhatE1Core.Bracket24SharpCleared_hold ℓ)

end

end Work.Asymptotics.KhatE1

import Mathlib
import Submission.Work.Asymptotics.KhatE1.Kdev24RemCore
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KhatE1.Kdev24Lead
import Submission.Work.Asymptotics.KhatE1.Kdev24BracketSharp
import Submission.Work.Asymptotics.KhatE1Core.Bracket24E2PrimeDefs
import Submission.Work.Asymptotics.KhatE1Core.Bracket24E2Prime_bound
import Submission.Work.Asymptotics.KhatE1Core.Bracket24TailCore
import Submission.Work.Asymptotics.KhatE1Core.Bracket24TailCore_proof

namespace Work.Asymptotics.KhatE1

/-- **The `d = 24` sharp funnel remainder (leading coefficient form).**

`KdevLead24 ℓ τ` is the explicit `τ`-atom leading coefficient defined in
`KhatE1/Kdev24RemCore.lean` (the `d = 24` analogue of `E1combo8/(288π)`, chosen so that the
next coefficient cancels), and `Kdev ℓ 24 τ z = K̂^{(24)}(τ,z) - (𝒢₊^{(24)} - 𝒢₋^{(24)})/2` is the
funnel deviation.  This states that on the funnel strip `0 ≤ Re z ≤ 1`, `t = Im z ≥ Im τ + 1`,

`‖Kdev ℓ 24 τ z - KdevLead24 ℓ τ · Ept z‖ ≤ C ‖q(τ)‖ (scale τ)^N (1+t)^M e^{-2πt}`,

i.e. that after removing the leading term the deviation is one power of `Ept z` and one power of
`q(τ)` smaller than it.  It is the single remaining ingredient of
`KhatE1.Kdev24RemCore` (`Kdev24RemCore_of_lead` turns it into the explicit bracket bound
`Kdev24RemCore`), and hence of `KhatE1.Kdev_leading_core` (the `d = 24` branch) and of the
assignment `KhatE1.Kdev_cusp0_strip`.

This is exactly the definition `Work.Asymptotics.KhatE1.Kdev24LeadProp ℓ` of
`Submission/Work/Asymptotics/KhatE1/Kdev24RemCore.lean` (stated here under its own name so that
it can be proved as a standalone leaf), and it is the `d = 24` analogue of the `d = 8` statement
`KhatE1.KdevRem_strip_sharp` (proved in the workspace).  NOTE: do not prove it by
`exact Kdev24Lead ℓ` -- the sibling `KhatE1/Kdev24Lead.lean` states the same thing with an
inline `sorry`.

Route: `Kdev ℓ 24 τ z - KdevLead24 ℓ τ · Ept z` equals (up to the factor `2`, by
`Kdev24RemCore_key`) the explicit bracket
`(KPlus 24 τ z - Gplus 24 τ z) + (3456π)⁻¹(Ept z·(R24 - R24_p0) + Dev24Sum
   - (-73728 Δ(τ) - 384(ψ₂E₁₀ - ψ₄E₈))·Ept z)`; its `Ept z^k`-coefficients (`k = 1,…,6`) are
explicit combinations of `E₂, E₄, E₆, Δ, j, ψ₂, ψ₄` which cancel to `O(‖q(τ)‖(scale τ)^N)`
using the cusp expansion of `𝓛` (`Compact.cuspC_spec`), `ψ₂ = ξ₂𝓛 + (ξ₂|₂S)𝓛_S`,
`ψ₄ = ξ₄𝓛 + (ξ₄|₄S)𝓛_S` together with the classical identities
`E₄ = (U²+V²+W²)/2`, `E₆ = (U+V)(2U-V)(U-2V)/2`, `ξ₂ = 2U-V`, `W = U-V`, `Δ = (UVW)²/256`,
`ψ₂E₁₀/Δ = ψ₂ j E₆/E₄`.  For `d = 8` a closely related piece of exactly this computation is
done in the proved leaf `KhatE1.Kdev8BracketE2_z0`, and the `d = 8` `E²`-coefficient bound
`KhatE1.KdevE2_bound` plus `KhatE1.KdevE2fun_funnel` are proved too; the `d = 8` sibling of this
statement is `KhatE1.KdevRem_strip_sharp`.

The assembly of the target from the split-form tail bound `Bracket24TailCore` (below,
`Kdev24LeadProp_of_tailCore`) uses only proved lemmas: `Bracket24Tail'_of_core`,
`Bracket24E2Prime_bound` + `Bracket24SharpClearedRaw_of_pieces'`,
`Kdev24BracketSharp_of_cleared` (via `‖Sh τ z‖ ≥ 1/16`), and `Kdev24Lead_of_bracket`
(via the identity `Bracket24 = 2(Kdev - KdevLead24·E(z))` of `Bracket24_eq_two_KdevRem`).
This makes the single mathematical obligation the tail bound `Bracket24TailCore` of
`KhatE1Core/Bracket24TailCore_proof.lean` (= the `E(z)`-expansion remainder
`Bracket24ExpansionHold`). -/
theorem Kdev24LeadProp_of_tailCore (ℓ : Work.Kernels.LogLambdaData)
    (h : Work.Asymptotics.KhatE1Core.Bracket24TailCore ℓ) :
    Work.Asymptotics.KhatE1.Kdev24LeadProp ℓ := by
  have htail : Work.Asymptotics.KhatE1Core.Bracket24Tail' ℓ :=
    Work.Asymptotics.KhatE1Core.Bracket24Tail'_of_core ℓ h
  have hpieces : Work.Asymptotics.KhatE1Core.Bracket24E2Bound' ℓ :=
    Work.Asymptotics.KhatE1Core.Bracket24E2Prime_bound ℓ
  have hraw : Work.Asymptotics.KhatE1Core.Bracket24SharpClearedRaw ℓ :=
    Work.Asymptotics.KhatE1Core.Bracket24SharpClearedRaw_of_pieces' ℓ hpieces htail
  have hcl : Work.Asymptotics.KhatE1.Bracket24SharpCleared ℓ := hraw
  have hsharp : Work.Asymptotics.KhatE1.Bracket24Sharp ℓ :=
    Work.Asymptotics.KhatE1.Kdev24BracketSharp_of_cleared ℓ hcl
  exact Work.Asymptotics.KhatE1.Kdev24Lead_of_bracket ℓ hsharp

theorem Kdev24LeadProp_proof (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Kdev24LeadProp ℓ :=
  Kdev24LeadProp_of_tailCore ℓ (Work.Asymptotics.KhatE1Core.Bracket24TailCore_proof ℓ)

end Work.Asymptotics.KhatE1

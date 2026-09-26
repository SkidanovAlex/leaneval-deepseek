import Mathlib
import Submission.Work.Asymptotics.Funnel24Tail.Tref24FunnelBound
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KhatE1.Kdev24Base
import Submission.Work.Residues.ThetaEpt

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

/-!
# The explicit `d = 24` bracket: definitions

This module holds the *definitions*

  `Bracket24 ℓ τ z = (K₊^{(24)} - 𝒢₊^{(24)}) + (3456π)⁻¹(E(z)(R24 - R24_p0) + Dev24Sum - Am24·E(z))`

and the bound predicate `Bracket24Sharp ℓ`, together with the identity
`Bracket24_eq_two_KdevRem` expressing the bracket as twice the leading-term-free deviation
`Kdev ℓ 24 τ z - KdevLead24 ℓ τ · E(z)` (`Kdev24RemCore_key`).

They are *split out of* `KhatE1/Kdev24Lead.lean` (which re-exports them, so nothing changes for
its users) because the `Sh`-cleared `d = 24` chain states its obligations about `Bracket24`
(`KhatE1/ShBracketAux.lean`, `KhatE1/Bracket24ClearedDefs.lean`,
`KhatE1Core/Bracket24E2PrimeDefs.lean`, …) and must therefore sit *below* the target theorem
`KhatE1.Kdev24Lead` in the import graph, while the target's proof needs the chain.  Keeping the
definitions here breaks that cycle. -/

noncomputable section

/-- **The explicit bracket of the `d = 24` sharp remainder.**  By `Kdev24RemCore_key` it equals
twice the leading-term-free deviation `Kdev ℓ 24 τ z - KdevLead24 ℓ τ · Ept z`. -/
noncomputable def Bracket24 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (Work.Kernels.KPlus 24 τ z - Work.Asymptotics.Compact.Gplus 24 τ z)
    + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
        (Work.Residues.Ept z * (Work.Asymptotics.Compact.R24 ℓ τ z
            - Work.Asymptotics.Compact.R24_p0 ℓ τ)
          + Work.Asymptotics.Compact.Dev24Sum ℓ τ z
          - Am24 ℓ τ * Work.Residues.Ept z)

/-- **The `d = 24` sharp bracket bound.**  The remaining core: the explicit bracket is
`O(‖q(τ)‖ (scale τ)^N (1+t)^M e^{-2πt})` on the funnel strip. -/
def Bracket24Sharp (ℓ : Work.Kernels.LogLambdaData) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
      0 ≤ z.re → z.re ≤ 1 → z.im = t →
      ‖Bracket24 ℓ τ z‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * Real.exp (-(2 * Real.pi * t))

/-- The bracket is twice the leading-term-free deviation (`Kdev24RemCore_key`). -/
theorem Bracket24_eq_two_KdevRem (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0) :
    Bracket24 ℓ τ z = 2 * (Work.Asymptotics.Kdev ℓ 24 τ z
      - Work.Asymptotics.KhatE1.KdevLead24 ℓ τ * Work.Residues.Ept z) := by
  have h := Kdev24RemCore_key ℓ τ z hSh
  simpa only [Bracket24, Am24] using h

end

end Work.Asymptotics.KhatE1

import Mathlib
import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8WresTailGlue
import Submission.Work.Asymptotics.KhatE1Sharp.WresPolyBound_core
import Submission.Work.Asymptotics.KhatE1Sharp.WresDevBound
import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8WresPolyDevBound

/-!
# `Kdev8TailSharpFleet`: the sharp funnel tail of the `d = 8` bracket

## The requested statement (kept verbatim below)

  `∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (τ z : UpperHalfPlane) (t : ℝ),
      Funnel τ → τ.im + 1 ≤ t → -1 ≤ z.re → z.re ≤ 2 → z.im = t →
      ‖Kdev8Bracket ℓ τ z - 2·KdevE2 ℓ τ z·Ept z²‖
        ≤ C·‖q(τ)‖·(scale τ)^N·(1+t)^M·exp(-2πt)`.

## Proof

The statement is *character-for-character* the conclusion of the final assembly
`Work.Asymptotics.KhatE1.Kdev8BracketTail_of_three` (`Kdev8WresTailGlue.lean`), which composes the
three function-level estimates of the doubly-cleared residual

  `Δ(τ)·(Δ(τ)·Sh(τ,z)·Wres) = WresPoly(τ,z) + WresDev(τ,z)`,  `Wres = Kdev8Bracket - 2·KdevE2·u²`

(`u = Ept z`) with the proved lower bounds `‖Δ(τ)‖ ≥ ‖q(τ)‖/2` and `‖Δ(τ)Sh(τ,z)‖ ≥ ‖q(τ)‖/32`:

* `hP : ‖WresPolyPol ℓ τ z‖ ≤ C‖q(τ)‖³‖u‖²(scale τ)^N(1+t)^M`
  (`KhatE1Core.WresPolyPol_bound`, `WresPolyBound_core.lean`): the polynomial part
  `WresPolyPol = Σ_{k=3}^{16} p_k·u^k` of the cleared residual, whose coefficients satisfy
  `p₃ = Δ²·KdevA3`, `p₄ = Δ²·KdevA4`, `p₅ = Δ²(KdevA5 + (720-j)KdevA3 - (48/5π)E₄)` and
  `‖p_k‖ ≤ C‖q(τ)‖(scale τ)^N(1+t)^M` for `k ≥ 6`, together with `‖u‖² ≤ ‖q(τ)‖`;
* `hdev : ‖WresPolyDevRem ℓ τ z‖ ≤ C‖q(τ)‖³‖u‖²(scale τ)^N(1+t)^M`
  (`KhatE1.Kdev8WresPolyDevBound`, `Kdev8WresPolyDevBound.lean`): the deviation remainder
  `(3456π)⁻¹Δ·Dev8Rem - tailC⁻¹Δ²·kdevNum0Rem` of the split `WresPoly = WresPolyPol + dev`;
* `hD : ‖WresDev ℓ τ z‖ ≤ C‖q(τ)‖³‖u‖²(scale τ)^N(1+t)^M`
  (`KhatE1Core.WresDevBound`, `WresDevBound.lean`): the three deviation aggregates of
  `KdevWresClearedPoly_decomp`.

All three estimates are free of placeholders and rest only on
`propext, Classical.choice, Quot.sound`, so this final lemma does too.

This module is the copy of `KhatE1/Kdev8TailSharpFleet.lean` inside the *cycle-free* duplicate
chain `KhatE1Sharp/` (same declaration names, namespace `Work.Asymptotics.KhatE1`, but importing
only the sibling copies and never the original modules that were mutually importing each other).
Consequently this lemma can be imported by a client even while the original modules are unusable,
and it does not depend on `KhatE1/Kdev8BracketTailBound.lean`.
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- **The requested sharp funnel tail bound for the `d = 8` bracket.**

The `E(z)²`-coefficient `2·KdevE2` of the bracket is removed, leaving a tail one power of
`‖q(τ)‖` smaller than the bracket itself, with the form factor `exp(-2πt)`. -/
theorem Kdev8TailSharpFleet (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) :=
  Kdev8BracketTail_of_three ℓ
    (Work.Asymptotics.KhatE1Core.WresPolyPol_bound ℓ)
    (Work.Asymptotics.KhatE1.Kdev8WresPolyDevBound ℓ)
    (Work.Asymptotics.KhatE1Core.WresDevBound ℓ)

end

end Work.Asymptotics.KhatE1

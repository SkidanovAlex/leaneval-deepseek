/-
Copyright: work module for the Elgindi finite-time singularity project.

# `bslOp α Ψ` is `C^∞` on the open quadrant (consumer-facing name)

The elliptic chapter works with sources `F` which are `C^∞` on the *open* quadrant
`Q0 = (0,∞) × (0,π/2)` (`Work.FTS.EllipticEst.SmoothOpen`).  The source produced by the
elliptic law `bslOp α Ψ = F` is of that kind as soon as `Ψ` is smooth on a neighbourhood of
the closed quadrant (`Work.Spaces.SmoothNbhd Ψ`), and this is the certificate used by the
downstream modules

* `Work.FTS.EllipticEst.Cert.Fstar_div_integrable_of_EllHyp`,
* …

## Why `SmoothNbhd` and not something stronger

`SmoothNbhd` — analyticity on the box `(-1,∞) × (-1, π/2 + 1)` — contains the pole
`θ = π/2` of `Real.tan`, and Lean's `Real.tan` is totalised (`Real.tan (π/2) = 0`), so
`θ ↦ bslOp α Ψ z θ` genuinely jumps there: `SmoothNbhd (bslOp α Ψ)` is *false* in general
(cf. `Submission/Work/FTS/EllipticEst/Cert/FstarSmooth/Defs.lean`).  On the open quadrant
`θ ∈ (0, π/2)` one has `cos θ ≠ 0`, so `tan` is analytic and all operations defining
`Lzero`/`bslOp` preserve `C^∞` there:

`bslOp α Ψ = -α²z²·∂_z²Ψ - α(5+α)z·∂_zΨ + Lzero Ψ`,
`Lzero Ψ = -∂_θ²Ψ + ∂_θ(tan θ·Ψ) - 6Ψ`.

## Proof

This is the certificate `Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp` of
`Submission/Work/FTS/EllipticEst/Cert/SmoothOpen_bslOp.lean`, whose proof checks each of the
five summands against the closure properties of `SmoothOpen` (`SmoothOpen.pzIter`,
`SmoothOpen.pz`, `SmoothOpen.pth` and the elementary addition/subtraction/negation/
multiplication rules, together with the concrete `C^∞` factors `z`, `z²`, `tan θ`).  The
present module merely re-exports it under the name the elliptic chapter consumes, so that the
consumer does not have to depend on the internals of the certificate module.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

/-- **`bslOp α Ψ` is `C^∞` on the open quadrant** whenever `Ψ` is smooth on a neighbourhood
of the closed quadrant: the uncurried `Work.Elliptic.bslOp α Ψ` is `ContDiffOn ℝ ∞` on
`Q0 = (0,∞) × (0,π/2)`, i.e. `Work.FTS.EllipticEst.SmoothOpen (bslOp α Ψ)`.

This is the certificate `Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp`; see the module
docstring for the decomposition of `bslOp` into `C^∞` pieces. -/
theorem SmoothOpBsll (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
  SmoothOpen_bslOp α Ψ hΨ

end Work.FTS.EllipticEst.Cert

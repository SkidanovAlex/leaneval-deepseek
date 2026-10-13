/-
Copyright: work module for the Elgindi finite-time singularity project.

# The layer certificate `F_*(F)·sin 2θ ∈ ℋ^k` for the elliptic data `EllHyp`

The main result is `Work.FTS.EllipticEst.Cert.FstarSin_layer`:

  ∃ C > 0, ∀ α F Ψ,  `0 < α` → `α ≤ 1/4` → `EllHyp α k F Ψ` ⟹
  `F_*(F)·sin 2θ ∈ ℋ^k`  and  `|F_*(F)·sin 2θ|_{H^k} ≤ C |F|_{H^k}`.

## Why the two halves are stated for the *open-quadrant* class

`EllHyp α k F Ψ` only determines the source `F` on the open quadrant `(0,∞) × (0,π/2)`: it
gives `bslOp α Ψ = F` there and the smoothness of `Ψ` near the closed quadrant, but
`z ↦ bslOp α Ψ z θ` genuinely jumps at `θ = π/2` (Lean's `Real.tan` is totalised,
`Real.tan (π/2) = 0`, while `tan θ Ψ` blows up from *above* `π/2`).  Hence `F` is *not*
`Work.Spaces.SmoothNbhd`, and the delivered certificate `Fstar_sin_HkMem_HkNorm` — which
assumes exactly that — cannot be applied to it.  Both halves are therefore proved in the
open-quadrant class `Work.FTS.EllipticEst.SmoothOpen`:

* membership: `Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin_open` (module
  `Cert/FstarSin_mem.lean`), which works with the separated form of the `ℋ^k`-integrand and
  the moment tower of the source;
* estimate: `Work.FTS.EllipticEst.Cert.Fstar_Hk_le_open` (module `Cert/FstarSin_norm.lean`),
  the open-quadrant counterpart of `Fstar_sin_HkMem_HkNorm`, whose radial content is the
  Cauchy–Schwarz bound for the angular moment.

The bridge `EllHyp α k F Ψ → SmoothOpen F` is `Cert.SmoothOpen_bslOp` (the operator
`bslOp` is `C^∞` on the open quadrant as soon as `Ψ` is smooth near the closed quadrant)
together with the equation `bslOp α Ψ = F` of `IsBslSol` on the open quadrant.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.Cert.FstarSin_norm
import Submission.Work.FTS.EllipticEst.Cert.FstarSin_mem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The layer certificate.**  For every `k` there is a constant `C = C_k > 0`, independent of
`α ∈ (0,1/4]`, such that for every solution `Ψ` of the elliptic problem (PolarBSL) with source
`F` in the class `EllHyp` (in particular `F ∈ ℋ^k`),

  `F_*(F)(z)·sin 2θ ∈ ℋ^k`  and  `|F_*(F)·sin 2θ|_{H^k} ≤ C_k |F|_{H^k}`. -/
theorem FstarSin_layer (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 / 4 → Work.FTS.EllipticEst.EllHyp α k F Ψ →
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) ∧
      Work.Spaces.HkNorm α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ))
        ≤ C * Work.Spaces.HkNorm α k F := by
  obtain ⟨C, hCpos, hCle⟩ := Fstar_Hk_le_open k
  refine ⟨C, hCpos, fun α F Ψ hα hα4 hHyp => ?_⟩
  have hα1 : α ≤ 1 := by linarith
  have hF : SmoothOpen F := by
    refine smoothOpen_of_forall fun n => ?_
    refine ((SmoothOpen_bslOp_int α Ψ hHyp.smooth).forall n).congr ?_
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := mem_Q0.mp hp
    exact (hHyp.sol.1 p.1 hz p.2 hθ0 hθ1).symm
  exact ⟨HkMem_Fstar_sin_open α k F hα hα1 hF hHyp.memF,
    hCle α F hα hα1 (fun n => hF.forall n) hHyp.memF⟩

end Work.FTS.EllipticEst.Cert

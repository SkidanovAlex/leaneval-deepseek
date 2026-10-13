/-
Copyright: work module for the Elgindi finite-time singularity project.

# The smoothness class of the `ℛ`-transfer

The elliptic chapter's estimates (`Work.FTS.EllipticEst.divSin_Hk_gen`,
`Blocks.theta_Hk_poincare`, …) are stated for `Work.Spaces.SmoothNbhd`, i.e. for functions
`C^∞` on an *open neighbourhood of the closed quadrant*

  `SmoothNbhd f = ContDiffOn ℝ ⊤ (uncurry f) (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π/2 + 1))`.

That hypothesis is **not available** for the straightened residual
`Ξ = Work.Elliptic.EllResid α F Ψ = Ψ - (1/(4α))·sin 2θ·L₁₂(F)`: by `EllHyp.sol` the source `F`
equals `bslOp α Ψ` only on the *open quadrant*, so `F` is completely unconstrained for `z < 0`,
whence `L₁₂(F)(z) = 3∫_z^∞ F_*(r)/r dr` has no reason to be smooth on `(-1,0)`.  A concrete
counterexample (`α = 3/20`, `k = 2`) is recorded in
`Submission/Work/Blocks/NOTES_EllResid_certs_counterexample.md`: `EllHyp` + `OrthCond (Ψ + …)`
hold while `z ↦ L₁₂(F)(z)` is not `C²` at `0⁻`, so `SmoothNbhd Ξ` is false.

What *is* available, and what the estimates really use, is smoothness **from the right**: the
angular slices of `Ξ` are smooth on a neighbourhood of `[0, π/2]`, and `Ξ` is jointly smooth on
the half-strip `z > 0`, `θ ∈ (-1, π/2+1)`.  `SmoothHalf` records exactly this.  For the data of
`EllHyp` it holds because `F = bslOp α Ψ` for `z > 0` makes `F_*(z)/z` smooth on `(0,∞)` and
extend smooth to `z = 0⁺`, hence so does `L₁₂(F)`.

This module is deliberately tiny and dependency-light so that the delegated estimates
(`Work.FTS.EllipticEst.Blocks.divSin_Half`, `…poincare_Half`, `…EllResid_certs_half`, …) and
the assembly `Submission/Work/FTS/EllipticEst/Rop_EllResid_le.lean` can share the definition.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The half-strip smoothness class of the `ℛ`-transfer.**  A function `f` is `SmoothHalf` if

* every angular slice `θ ↦ f z θ` with `z ∈ [0,∞)` is smooth on an open neighbourhood of
  `[0, π/2]` (`Work.FTS.EllipticEst.SliceSmooth`);
* `f` is jointly `C^∞` on the half-strip `z > 0`, `θ ∈ (-1, π/2+1)`.

This is weaker than `Work.Spaces.SmoothNbhd` (which also demands smoothness on `z < 0`) and is
exactly what the slicewise Hardy/Poincaré estimates use.  In particular it is satisfied by
`Ξ = Work.Elliptic.EllResid α F Ψ` for the data of `EllHyp α k F Ψ`. -/
def SmoothHalf (f : ℝ → ℝ → ℝ) : Prop :=
  (∀ z ∈ Work.Spaces.Iz, SliceSmooth (fun θ => f z θ)) ∧
    ContDiffOn ℝ ⊤ (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1))

/-- `SmoothHalf` implies smoothness on the open quadrant. -/
theorem SmoothHalf.smoothOpen {f : ℝ → ℝ → ℝ} (h : SmoothHalf f) : SmoothOpen f := by
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Q0
  refine (h.2.mono ?_).of_le le_top
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := mem_Q0.mp (show (p.1, p.2) ∈ Q0 from hp)
  exact ⟨hz, by linarith, by linarith [Real.pi_pos]⟩

/-- `SmoothHalf` implies smoothness of every angular slice at `z > 0`. -/
theorem SmoothHalf.slice_of_pos {f : ℝ → ℝ → ℝ} (h : SmoothHalf f) {z : ℝ} (hz : 0 < z) :
    SliceSmooth (fun θ => f z θ) := by
  have hg : ContDiffOn ℝ ⊤ (fun θ : ℝ => ((z, θ) : ℝ × ℝ))
      (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    (contDiffOn_const (c := z)).prodMk
      (contDiffOn_id : ContDiffOn ℝ ⊤ (fun θ : ℝ => θ) (Set.Ioo (-1) (Real.pi / 2 + 1)))
  refine (h.2.comp hg (fun θ hθ => (⟨hz, hθ⟩ :
    ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)))).congr ?_
  intro θ _
  rfl

/-- The `θ`-slice of a `SmoothHalf` function, at every `z ∈ [0,∞)`. -/
theorem SmoothHalf.slice {f : ℝ → ℝ → ℝ} (h : SmoothHalf f) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    SliceSmooth (fun θ => f z θ) := h.1 z hz

/-- **The division by `sin 2θ` in the half-strip class**: the statement of the sibling
`Work.FTS.EllipticEst.Blocks.divSin_Half`, i.e. `divSin_Hk_gen` with `SmoothNbhd` weakened to
`SmoothHalf`. -/
def DivHalf (k : ℕ) (_hk : 1 ≤ k) : Prop := ∃ C : ℝ, 0 < C ∧
  ∀ (α : ℝ) (Φ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → SmoothHalf Φ → Work.Spaces.VanishTheta Φ →
    Work.Spaces.HkMem α k (Work.Spaces.pth Φ) →
    Work.Spaces.HkMem α k (fun z θ => Φ z θ / Real.sin (2 * θ)) ∧
    Work.Spaces.HkNorm α k (fun z θ => Φ z θ / Real.sin (2 * θ))
      ≤ C * Work.Spaces.HkNorm α k (Work.Spaces.pth Φ)

/-- **The weighted angular Poincaré estimate in the half-strip class**: the statement of the
sibling `Work.FTS.EllipticEst.Blocks.poincare_Half`, i.e. `theta_Hk_poincare` with
`SmoothNbhd` weakened to `SmoothHalf`. -/
def PoinHalf (k : ℕ) (_hk : 2 ≤ k) : Prop := ∃ C : ℝ, 0 < C ∧
  ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → SmoothHalf f → Work.Spaces.VanishTheta f →
    Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 f) →
    Work.Spaces.HkNorm α k f ≤ C * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 f) ∧
    Work.Spaces.HkNorm α k (Work.Spaces.pth f)
      ≤ C * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 f)

/-- **The certificates for the straightened residual in the half-strip class**: the statement of
the sibling `Work.FTS.EllipticEst.Blocks.EllResid_certs_half`. -/
def CertsHalf (k : ℕ) (_hk : 2 ≤ k) : Prop :=
  ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 → EllHyp α k F Ψ →
    Work.Elliptic.OrthCond (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) →
    SmoothHalf (Work.Elliptic.EllResid α F Ψ) ∧
    Work.Spaces.VanishTheta (Work.Elliptic.EllResid α F Ψ) ∧
    Work.Spaces.HkMem α k (Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ)) ∧
    Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ)) ∧
    SmoothOpen (fun z θ => Work.Elliptic.EllResid α F Ψ z θ / Real.sin (2 * θ)) ∧
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.EllResid α F Ψ z θ / Real.sin (2 * θ)) ∧
    Work.Spaces.HkMem α k (Work.Spaces.Dz
      (fun z θ => Work.Elliptic.EllResid α F Ψ z θ / Real.sin (2 * θ))) ∧
    SmoothHalf (Work.Spaces.Dz (Work.Elliptic.EllResid α F Ψ)) ∧
    Work.Spaces.VanishTheta (Work.Spaces.Dz (Work.Elliptic.EllResid α F Ψ)) ∧
    Work.Spaces.HkMem α k (Work.Spaces.pth (Work.Spaces.Dz (Work.Elliptic.EllResid α F Ψ)))

end Work.FTS.EllipticEst

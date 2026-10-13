import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.VopGen.Gate

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.VopGen.CoreSplit` — the two halves of the level-`2` core inequality

`CoreASlot11Hyp` (the tree's `Cores.Aux.coreASlot11`, the `(1,1)`-slot/T2 wall) is the single gate
of the level-parametric `V`-slot (`VopGen/Gate.lean`, `VopGen/a11OfCore.lean`).  The documented
route of `Cores/ASlot11Aux/coreASlot11.lean` splits it into two *independent* halves:

* `SliceAgmonStmt` — the **a.e.-slicewise angular Agmon inequality** for the slice
  `f := z ↦ D_z(z²∂_z²Ψ)(z,·)`: for a.e. `z > 0`,

    `∫_θ (f')² μ ≤ -∫_θ f · f'' · μ`,   `μ = sin(2θ)^{2-γ}`,

  which is `Prop.sliceAgmonMu` (`Prop/mixedSlotInterpEta.lean`, PROVED) applied slicewise, its six
  hypotheses being supplied by the weak class `EllWeakPos α 2 F Ψ`: smoothness of `Aof Ψ`
  (`Prop.smoothOpen_zsq_mul`), the two endpoint bounds `|f θ| ≤ M·sin(2θ)`, `|f'| ≤ M`
  (`Cores/InterpGammaCore/InterpJumpAux/{value_abs_le_mul_left,value_abs_le_mul_right,
  exists_deriv_abs_bound}`, PROVED), the vanishing of the endpoint *values* of `f`
  (`Prop.aof_tendsto_zero`, PROVED), and the `σ_η`-honesty of `f'' = ∂_θ²(D_z(z²∂_z²Ψ))`
  (`VopGen.hkMem_pth2_Dz_AofGen`, PROVED; equivalently
  `Prop.HkMem_zero_pthIter2_Ab` after Clairaut).

* `TruncStmt` — everything after the slice inequality: the logarithmic cut-off
  `Work.Blocks.logCutoff_open` (smooth, supported in `(0,∞)`, increasing to `1`, with
  `‖D_zχ_k‖_∞ ≤ K/log(k+2)`), the per-`θ`-slice radial integration by parts
  (`Prop.radialIbpWild`, PROVED — its flux vanishes because the cut-off is compactly supported in
  `(0,∞)`), Cauchy–Schwarz in `z` and then in `θ` (giving `√(qr) + 3√(pr)` with
  `p = ∫∫X²ρμ`, `q = ∫∫(D_zX)²ρμ`, `r = ∫∫Y²ρμ`, `X = D_z(z²∂_z²Ψ)`, `Y = ∂_θ²(z²∂_z²Ψ)`), the
  passage `k → ∞` (Fatou on the left, the uniform bound on the right), and AM–GM (`K = 2`
  suffices).

The glue is definitional: `coreASlot11_of_pieces hA hB = hB hA`.
-/
noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.VopGen

set_option autoImplicit false

/-- **The a.e.-slicewise angular Agmon inequality** for `f = D_z(z²∂_z²Ψ)` (the "slice half" of
the level-`2` core inequality). -/
def SliceAgmonStmt : Prop :=
  ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ -(∫ θ in Work.Spaces.Iθ,
            Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ
              * (Work.Spaces.pthIter 2 (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ))) z θ
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))

/-- **The "truncation half" of the level-`2` core inequality**: from the a.e.-slicewise Agmon
inequality, the core inequality (`= Cores.Aux.coreASlot11`). -/
def TruncStmt : Prop :=
  SliceAgmonStmt → CoreASlot11Hyp

/-- **The level-`2` core inequality from its two halves.** -/
theorem coreASlot11_of_pieces (hA : SliceAgmonStmt) (hB : TruncStmt) : CoreASlot11Hyp := hB hA

end Work.FTS.ClassC.VopGen

import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.ClassC.VopGen.a11OfCore
import Submission.Work.FTS.ClassC.VopGen.coreASlot11Gen
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5

/-- **The `(1,1)`-slot of `A = z²∂_z²Ψ` at level 2 (the "T2 wall")**, restated in this area so
that the assembly of `Work.FTS.EllSol.ellPkgK_transferC_k5` can consume it directly (the tree's
own copy is `Work.FTS.EllipticEst.Cores.ASlot11Bound`).  For data of the weak class
`TT.EllWeakPos α 2 F Ψ` and the level-0 estimate `EllWeak0`:
`α⁴ · Tk α 1 (D_z A) ≤ C |F|²_{ℋ²}`, i.e. `α⁴ · L2Sq (mixed 1 1 A · Wt α) ≤ C HkSq α 2 F`.

This is the genuine open gate of `TT.EllEstUnif 2` (hence of the elliptic chapter), not
bookkeeping: the tree's twin `Cores.aSlotsTwoPieces.aSlotsTwoT2x` goes through the refuted
`InterpGammaCore` (`Cores/NOTES_TopSlotsTwoClean.md` §1) and the `α⁴` is load-bearing (the
*unweighted* form is false).  Proved ingredients available:
`Cores.InterpGammaCore.sliceInterpJumpSigEta` (the 1-D product case, α-uniform),
`H2W.AslotTk_le`, `Cores.aHypotheses` (the interpolation hypotheses at `G = z²∂_z²Ψ` derived from
`EllWeakPos α 2`), `Cores.TSCAssembly.TopSlotsTwoClean_of` (this slot ⇒ the six level-2 slots),
`Cores.ShiftedTwoL2Clean`, `Prop.levelTwoBSlot`.

The statement is produced from the tree's *core-free* route (which avoids `InterpGammaCore`
altogether): `Work.FTS.ClassC.VopGen.coreASlot11Gen` is the level-`2` light-weight core
inequality

`∫∫ (∂_θ D_z A)² w² sin(2θ)^{2-γ} ≤ K (∫∫ (D_z²A)² w² sin(2θ)^{2-γ}
   + ∫∫ (D_zA)² w² sin(2θ)^{2-γ} + ∫∫ (∂_θ²A)² w² sin(2θ)^{2-γ})`,  `A = z²∂_z²Ψ`,

proved from the a.e.-slicewise angular Agmon inequality (`VopGen.SliceAgmonStmt`,
`VopGen.sliceAgmonAofGen`) and the logarithmic truncation / radial integration by parts that
removes the radial flux (`VopGen.TruncStmt`, `VopGen.Core.truncProof`).  The bridge
`Work.FTS.ClassC.VopGen.a11OfCore` turns that core inequality into the `Tk`-form below, using
`(sin 2θ · Wt α)² = w² sin(2θ)^{2-γ}` on `Iθ` for the left-hand side and the level-`0` slot
bounds `Prop.HkSq_zero_Ab_DzIter_le`, `Prop.HkSq_zero_pthIter2_Ab_le` (via the identity
`∂_θ²A = D_z²(∂_θ²Ψ) − D_z(∂_θ²Ψ)`) for the three right-hand side slots. -/
theorem aSlot11T2 (h0 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
          (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  have h : Work.FTS.ClassC.VopGen.A11Hyp :=
    Work.FTS.ClassC.VopGen.a11OfCore Work.FTS.ClassC.VopGen.coreASlot11Gen
  unfold Work.FTS.ClassC.VopGen.A11Hyp at h
  exact h

end Work.FTS.EllSol.PkgK5

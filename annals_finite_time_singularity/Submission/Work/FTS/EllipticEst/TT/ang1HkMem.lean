import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Blocks.HkMem_of_majorant_aesm
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.remov.pth_zero_of_HkMem
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.hkMem_ang1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

/-- In the weak class `EllWeakPos α 0 F Ψ` (with `0 < α ≤ 1/4`, plus `HkMem α 0 Ψ` and
`HkMem α 0 (z ∂_zΨ)`), the angular first-order quantity
`U := ∂_θ(tan θ · Ψ)` is again honest: `HkMem α 0 (fun z θ => ∂_θ(tan θ · Ψ)(z,θ))`.

Route (the rearranged equation together with a five-term domination):
on the open quadrant the definition of `Work.Elliptic.bslOp` and `EllWeakPos.eq` give

`U = α² z² ∂_zzΨ + α(5+α) z ∂_zΨ + ∂_θθΨ + F + 6Ψ`,

so with `maj := 5 · (HkIntegrand α 0 (α² z²∂_zzΨ) + HkIntegrand α 0 ((α(5+α)) z∂_zΨ)
+ HkIntegrand α 0 (∂_θθΨ) + HkIntegrand α 0 F + HkIntegrand α 0 (6Ψ))` one has
`HkIntegrand α 0 U ≤ maj` a.e. on `Iz ×ˢ Iθ` (five-term Cauchy–Schwarz `(Σa)² ≤ 5Σa²`); the
already-proved `Honest.HkIntegrand_zero_le_five` performs this step.  Each of the five summands is
`HkMem α 0` (`EllWeakPos.memA`, `EllWeakPos.memB`, `EllWeakPos.memF`, the two extra hypotheses, and
multiplication by the constants via `Submission.Work.FTS.LocData.HkMem_const_mul`), and `U` is
jointly smooth on the open quadrant, so `Work.Blocks.HkMem_of_majorant_aesm` gives the conclusion.
(The companion file `Submission/Work/FTS/EllipticEst/AngAWeak/hkMemAng1.lean` carries a complete
proof of this same statement in the `AeData` shape -- its helper `scaled_rad2_eq` is the pointwise
rearrangement, and `H2W.Ae.AeData α Ψ F` follows from `EllWeakPos α 0 F Ψ` because the pointwise
`Fstar = 0` for `z > 0` gives the a.e. version -- but its import cone is currently not buildable,
so the statement is re-proved here from `EllWeakPos` directly.  Useful imports beyond the listed
ones: `Submission.Work.FTS.EllipticEst.H2W.Ae.Defs`, `Submission.Work.FTS.EllipticEst.AngAWeak`,
`Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen`.) -/
theorem ang1HkMem : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
    Work.Spaces.HkMem α 0 Ψ →
    Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) →
    Work.Spaces.HkMem α 0
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) := by
  intro α F Ψ hα hα4 hE hΨ hG
  -- The pointwise moment conditions of `EllWeakPos` give the a.e. ones of `AeData`.
  have haeΨ : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar Ψ z = 0 :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => hE.orthPsi z hz)
  have haeF : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar F z = 0 :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => hE.orthF z hz)
  have hA : Work.FTS.EllipticEst.H2W.Ae.AeData α Ψ F :=
    ⟨hα, hα4, hE.eq, hE.zero, hE.pi_half, hE.smooth, hE.memF, hE.memA, hE.memB, haeΨ, haeF⟩
  have hres : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.ang1 Ψ) :=
    Work.FTS.EllipticEst.H2W.Ae.hkMem_ang1 α Ψ F hA hΨ hG
  exact hres

end Work.FTS.EllipticEst.TT

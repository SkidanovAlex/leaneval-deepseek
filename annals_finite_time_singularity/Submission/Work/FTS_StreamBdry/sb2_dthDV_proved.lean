import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS_StreamBdry.SB2.sb2_dthDV

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sb2_dthDV_proved` — the frozen SB2 sub-leaf `StreamBdryIface.sb2_dthDV`

`∂_θ D_z V(psiP)` is bounded: the elliptic law for `psiP` (`SB3.law_psiP`) gives
`∂_θV(psiP) = -(αG²D_z² + 5αG D_z + 6)psiP - F`, and Clairaut (with `psiP ∈ C²`, `SB3.psiP_c2`)
turns `∂_θ D_zV(psiP)` into `D_z∂_θV(psiP)`, bounded by the `D_z^3` bound `hD3` and `|D_zF| ≤ Mf`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_StreamBdry

open Work.FTS.StreamBdryIface (SlotBd SrcOK psiP)
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **SB2 sub-leaf proved** (frozen type `sb2_dthDV`). -/
theorem sb2_dthDV_proved {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : Fn}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) (hF : SrcOK F L Mf)
    (hD3 : ∃ K : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 3,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ K * Work.Construction.s2 θ) :
    ∃ K' : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1
        (Work.Construction.Vop (psiP αG Ψ))) z θ| ≤ K' :=
  SB2.sb2_dthDV hαG hsol h3 hslot hF hD3

end Work.FTS_StreamBdry

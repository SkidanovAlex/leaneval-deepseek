import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.SB2.sb2_c2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sb2_c2_proved` — the frozen SB2 producer `StreamBdryIface.sb2_c2`

`oddPerS (psiP αG Ψ)` is `C²` on the strip `Ioi 0 × (-(π/2)-1, π/2+1)`: on the interior pieces it is
`±psiP` composed with `θ ↦ ±θ`, `θ ↦ π - θ` (`SB25.oddPerS_pieces`, `SB3.psiP_c2`), and across the
seams `θ = 0, ±π/2` the gluing lemma `SB25.glue_line_C2` is fed by the edge limits
`SB25.psiP_edge_zero` / `SB25.psiP_edge_axis` (which is where `hdthDV` is used).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_StreamBdry

open Work.FTS.StreamBdryIface (SlotBd SrcOK psiP oddPerS)
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **SB2 proved** (frozen type `sb2_c2`). -/
theorem sb2_c2_proved {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : Fn}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) (hF : SrcOK F L Mf)
    (hdthDV : ∃ K' : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1
        (Work.Construction.Vop (psiP αG Ψ))) z θ| ≤ K') :
    ContDiffOn ℝ 2 (Function.uncurry (oddPerS (psiP αG Ψ)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2) - 1) (Real.pi / 2 + 1)) :=
  SB2.sb2_c2 hαG hsol h3 hslot hF hdthDV

end Work.FTS_StreamBdry

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SBpsiP.Assembly
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB3.psiP_DzLe` — `|D_z^j psiP| ≤ M·sin 2θ` for `j ≤ 2`

The SB3 bound `Work.FTS_StreamBdry.PsiPDzLe`: for a `C³` stream function `Ψ` on the open
quadrant whose slot `U'(Ψ) = (-3Ψ - αG z∂_zΨ)/sin 2θ` satisfies the `SlotBd` bounds
(`|D_z^j U'(Ψ)| ≤ M` for `j ≤ 2`, `|D_θ U'(Ψ)| ≤ M`, `|D_z^j V(Ψ)| ≤ M` for `j ≤ 1`), the
`U`-slot part `psiP αG Ψ` of `Ψ` satisfies `|D_z^j (psiP)| ≤ M·sin 2θ` there, for `j ≤ 2`.

Proof (see `SBpsiP/Assembly.lean`): `psiP αG Ψ = -(s2 θ/αG)·J c (U'(Ψ))` *definitionally*
(`c = 3/αG - 1`, `J` the scaled parameter integral of `SB3/DzJDefs`), and `D_z = z∂_z`
commutes with that integral (`SBpsiP.J_Dz_eq`, the crux), hence

  `D_z^j (psiP αG Ψ) = -(s2 θ/αG)·J c (D_z^j U'(Ψ))`   (`j ≤ 2`),

so with `|J c h z θ| ≤ M·(αG/3)` whenever `|h| ≤ M` (`SBpsiP.J_bound_self`),

  `|D_z^j (psiP)| ≤ (s2/αG)·M·(αG/3) = M·sin 2θ/3 ≤ M·sin 2θ`.

The two structural ingredients are the finite-order smoothness of the slot iterates
(`SBpsiP.UprimeIterSmooth_self`, from `Ψ ∈ C³`) and the elementary scaled-integral bound.
-/

noncomputable section

open scoped Real Topology

namespace Work.FTS_StreamBdry.SB3

set_option autoImplicit false

theorem psiP_DzLe {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M) :
    Work.FTS_StreamBdry.PsiPDzLe αG M Ψ := by
  exact Work.FTS_StreamBdry.SBpsiP.psiP_DzLe_of_pieces
    (fun αG hαG Ψ h3 => Work.FTS_StreamBdry.SBpsiP.UprimeIterSmooth_self hαG h3)
    (fun c B hc hB φ hcont hφ => Work.FTS_StreamBdry.SBpsiP.J_bound_self hc hB hcont hφ)
    hαG h3 hslot

end Work.FTS_StreamBdry.SB3

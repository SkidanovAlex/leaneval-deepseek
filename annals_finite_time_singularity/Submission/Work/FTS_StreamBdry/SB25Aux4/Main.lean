import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25Aux4.Part1
import Submission.Work.FTS_StreamBdry.SB25Aux4.Part2
import Submission.Work.FTS_StreamBdry.SB25Aux4.Part3
import Submission.Work.FTS_StreamBdry.SB25Aux4.Part4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux4.psiP_edge_axis_aux`

Assembly of the three parts into the full `θ = π/2` edge-limit statement for
`P := psiP αG Ψ`, with the edge traces `Vb` (of `V(P)`) and `DVb` (of `D_z(V(P))`) as inputs.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25Aux4

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP)

set_option autoImplicit false

theorem psiP_edge_axis_aux {αG M L Mf K' : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M)
    (hsrc : SrcOK F L Mf)
    (hK' : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1
        (Work.Construction.Vop (psiP αG Ψ))) z θ| ≤ K')
    (Vb : ℝ → ℝ) (hVbc : ContinuousOn Vb (Set.Ioi 0))
    (hVb : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Construction.Vop (psiP αG Ψ) z θ - Vb z|
        ≤ ((αG ^ 2 + 5 * αG + 6) * M + Mf) * (Real.pi / 2 - θ))
    (DVb : ℝ → ℝ) (hDVbc : ContinuousOn DVb (Set.Ioi 0))
    (hDVb : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter 1 (Work.Construction.Vop (psiP αG Ψ)) z θ - DVb z|
        ≤ |K'| * (Real.pi / 2 - θ)) :
    ∀ z0 : ℝ, 0 < z0 →
      (Tendsto (Function.uncurry (psiP αG Ψ)) (𝓝[Work.Construction.Qd] (z0, Real.pi / 2))
          (𝓝 0) ∧
        Tendsto (Function.uncurry (Work.Spaces.pz (psiP αG Ψ)))
            (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 0) ∧
          Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz (psiP αG Ψ))))
            (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 0) ∧
            Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth (psiP αG Ψ))))
              (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 0) ∧
              (∃ l, Tendsto (Function.uncurry (Work.Spaces.pth (psiP αG Ψ)))
                (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 l)) ∧
                ∃ l, Tendsto (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth (psiP αG Ψ))))
                    (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 l) ∧
                  Tendsto (Function.uncurry (Work.Spaces.pth (Work.Spaces.pz (psiP αG Ψ))))
                    (𝓝[Work.Construction.Qd] (z0, Real.pi / 2)) (𝓝 l)) := by
  intro z0 hz0
  obtain ⟨h1, h2, h3'⟩ := psiP_edge_axis_zero123 hαG h3 hslot z0 hz0
  exact ⟨h1, h2, h3',
    psiP_edge_axis_pthth hαG hsol h3 hslot hsrc Vb hVbc hVb z0 hz0,
    psiP_edge_axis_pth hαG h3 hslot Vb hVbc hVb z0 hz0,
    psiP_edge_axis_mixed (K' := K') hαG h3 hslot hK' DVb hDVbc hDVb z0 hz0⟩

end Work.FTS_StreamBdry.SB25Aux4

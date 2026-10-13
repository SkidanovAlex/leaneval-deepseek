import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.lip_edge_trace
import Submission.Work.FTS_StreamBdry.SB25Aux3.PsiPC3
import Submission.Work.FTS_StreamBdry.SB25.pze_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux3.trace_DzVop_psiP`

The function `f := D_z V(psiP αG Ψ)` on the open quadrant has a continuous edge trace at
`θ = π/2`, approached at the linear rate given by the pointwise bound `K'` on its `θ`-derivative
`∂_θ D_z V(psiP αG Ψ)`.

This is leaf SB2 of the `SB3/SB2/SB5` route (`NOTES_SB3_route.md` §4): the `θ`-edge trace of
`D_z V(psiP)`.  The proof is the general `SB25.lip_edge_trace` (leaf B2) applied to `f`, so all
that is needed is the regularity of `f` on the open quadrant — which comes from the `C³` hypothesis
on `Ψ`:

* `SB25Aux3.psiP_c3` : `psiP αG Ψ` is `C³` on `Qd`;
* `SB25.pze_contDiffOn_uncurry_Vop_Qd` : hence `V(psiP)` is `C²` there;
* `SB25.pze_contDiffOn_uncurry_pz_Qd` : hence `∂_z V(psiP)` is `C¹`, and `D_z V(psiP) = z∂_zV(psiP)`
  is `C¹`, so its `θ`-slices are differentiable and `f` is continuous;

and then `SB25.lip_edge_trace` produces the trace at `b = π/2` with rate `|K'|` (the bound on
`|∂_θ f|` is upgraded from `K'` to `|K'|`).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_StreamBdry.SB25Aux3

set_option autoImplicit false

theorem trace_DzVop_psiP {αG M K' : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hK' : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1
        (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ))) z θ| ≤ K') :
    ∃ DVb : ℝ → ℝ, ContinuousOn DVb (Set.Ioi 0) ∧
      ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        |Work.Spaces.DzIter 1 (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ)) z θ - DVb z|
          ≤ |K'| * (Real.pi / 2 - θ) := by
  -- The regularity of the `U`-slot `P := psiP αG Ψ` on the open quadrant.
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hP3 : ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS.StreamBdryIface.psiP αG Ψ)) Work.Construction.Qd :=
    psiP_c3 hαG h3 hslot
  have hV2 : ContDiffOn ℝ 2
      (Function.uncurry (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ)))
      Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB25.pze_contDiffOn_uncurry_Vop_Qd hP3
  have hpz1 : ContDiffOn ℝ 1
      (Function.uncurry
        (Work.Spaces.pz (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ))))
      Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB25.pze_contDiffOn_uncurry_pz_Qd hV2
  -- `D_z V(P) = z · ∂_z V(P)` is therefore `C¹` on the quadrant.
  have hf1 : ContDiffOn ℝ 1
      (Function.uncurry
        (Work.Spaces.DzIter 1 (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ))))
      Work.Construction.Qd := by
    have hfun : Function.uncurry
          (Work.Spaces.DzIter 1 (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ)))
        = fun p : ℝ × ℝ =>
            p.1 * Function.uncurry
              (Work.Spaces.pz (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ))) p := by
      funext p
      rcases p with ⟨z, θ⟩
      rfl
    rw [hfun]
    exact contDiff_fst.contDiffOn.mul hpz1
  -- Leaf B2: the edge trace at `b = π/2` with rate `|K'|`.
  obtain ⟨fa, fb, hfa_cont, hfb_cont, hrate⟩ :=
    Work.FTS_StreamBdry.SB25.lip_edge_trace
      (Work.Spaces.DzIter 1 (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ)))
      0 (Real.pi / 2) |K'| (by positivity) hf1.continuousOn
      (fun z θ hz hθ =>
        Work.Spaces.differentiableAt_curry_right
          ((hf1.differentiableOn (by norm_num)).differentiableAt
            (hQd.mem_nhds (show (z, θ) ∈ Work.Construction.Qd from ⟨hz, hθ⟩))))
      (fun z θ hz hθ =>
        le_trans (hK' z θ (show (z, θ) ∈ Work.Construction.Qd from ⟨hz, hθ⟩))
          (le_abs_self K'))
  exact ⟨fb, hfb_cont, fun z θ h =>
    (hrate z θ (Work.FTS_StreamBdry.mem_Qd.mp h).1 (Work.FTS_StreamBdry.mem_Qd.mp h).2).2⟩

end Work.FTS_StreamBdry.SB25Aux3

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25Aux3.trace_Vop_psiP
import Submission.Work.FTS_StreamBdry.SB25Aux3.trace_DzVop_psiP
import Submission.Work.FTS_StreamBdry.SB25Aux4.Main

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.psiP_edge_axis` — leaf B6 of the SB2/SB5 plan

The edge limits of `P := psiP αG Ψ` at `θ = π/2`: with `V := Vop`, `D := Dz`,

* `P`, `∂_zP`, `∂_z²P`, `∂_θ²P → 0` as `(z,θ) → (z₀, π/2)` inside the open quadrant;
* `∂_θP` and the mixed second partials have limits;

all uniformly in `z` near a fixed `z₀ > 0`.

The two edge traces used by the argument are produced separately:

* `SB25Aux3.trace_Vop_psiP` — the trace `Vb` of `V(P)` at `θ = π/2`, at rate
  `K_V = (αG²+5αG+6)M + Mf` (`lip_edge_trace` applied to `V(P)`, whose `θ`-derivative is bounded
  by the law `law_psiP`);
* `SB25Aux3.trace_DzVop_psiP` — the trace `DVb` of `D_z(V(P))` at `θ = π/2`, at rate `|K'|`
  (the `K'` supplied by the statement; `SB2.sb2_dthDV` is what produces it downstream).

The assembly is `SB25Aux4.psiP_edge_axis_aux`, whose parts are
`SB25Aux4.psiP_edge_axis_zero123` (the three vanishing `z`-derivative limits),
`SB25Aux4.psiP_edge_axis_pthth` (`∂_θ²P → 0`), `SB25Aux4.psiP_edge_axis_pth` (the limit of
`∂_θP`) and `SB25Aux4.psiP_edge_axis_mixed` (the mixed second partials).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP)

set_option autoImplicit false

theorem psiP_edge_axis {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ} :
    Work.FTS_StreamBdry.SB25.PsiPEdgeAxis αG M L Mf F Ψ := by
  intro hsol h3 hslot hsrc hK'
  obtain ⟨K', hK'b⟩ := hK'
  obtain ⟨Vb, hVbc, hVb⟩ :=
    Work.FTS_StreamBdry.SB25Aux3.trace_Vop_psiP (αG := αG) (M := M) (L := L) (Mf := Mf)
      hαG hsol h3 hslot hsrc
  obtain ⟨DVb, hDVbc, hDVb⟩ :=
    Work.FTS_StreamBdry.SB25Aux3.trace_DzVop_psiP (αG := αG) (M := M) hαG h3 hslot hK'b
  exact Work.FTS_StreamBdry.SB25Aux4.psiP_edge_axis_aux (αG := αG) (M := M) (L := L)
    (Mf := Mf) (K' := K') hαG hsol h3 hslot hsrc hK'b Vb hVbc hVb DVb hDVbc hDVb

end Work.FTS_StreamBdry.SB25

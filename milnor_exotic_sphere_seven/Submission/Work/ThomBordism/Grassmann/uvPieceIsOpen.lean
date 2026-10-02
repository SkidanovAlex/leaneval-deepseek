import Mathlib
import Submission.Work.ThomBordism.Grassmann.UVOverlap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `uvPiece Reg` is open in `UR ∩ VR` for every open `Reg ⊆ ℂ`

The ratio `uvRatio : ↥(UR ∩ VR) → ℂ` of the overlap introduces a "ratio coordinate space": for
every region `Reg ⊆ ℂ` of ratio values, `Work.ThomBordism.Grassmann.uvPiece Reg` is the part of the
overlap on which the ratio takes its values in `Reg`.  This module proves that `uvPiece` sends open
regions to open sets (`uvPieceIsOpen`), which is what makes the four pieces `uvA`, `uvB` (complement
of a closed ray) and `uvP`, `uvQ` (half planes) of `UVOverlap.lean` *open* — the hypothesis of the
Mayer–Vietoris argument for `H³(UR ∩ VR) = 0`.

The topological content is local.  The fibre coordinates of the model fibre are *not* continuous
functions of a point of the total space of a `VectorBundleCore` (the topology is the one for which
the *local trivialisations* are homeomorphisms, and `indexAt` is an arbitrary choice function); the
ratio is continuous nevertheless, because on each chart-open piece `{p | base(p) ∈ W.baseSet i}` the
trivialisation `W.localTriv i` is continuous and the ratio equals the ratio `uvVi i / uvUi i` of the
chart coordinates (`uvRatio_eq_chart_div`), a continuous function of the chart coordinates.  The
three chart-open pieces cover `UR ∩ VR`, and each is open, so `uvPiece Reg` is a union of open sets.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

/-- **The complex coordinate `ccoord` of the model fibre `ℝ²` of `zStd` is continuous.** -/
theorem continuous_ccoord : Continuous ccoord := by
  rw [show ccoord = (fun z : EuclideanSpace ℂ (Fin 1) => z 0) ∘
    (equivC1R2.symm : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℂ (Fin 1)) from rfl]
  fun_prop

/-- The chart-open pieces of the overlap: a point of `UR ∩ VR` whose base point lies in the chart
`i` of `W`. -/
def uvChartSet (i : Fin 3) : Set ↥(UR ∩ VR) := {p | p.1.1.1 ∈ W.baseSet i}

theorem isOpen_uvChartSet (i : Fin 3) : IsOpen (uvChartSet i) := by
  have hcoe : Continuous (fun p : ↥(UR ∩ VR) => (p.1.1 : W.TotalSpace)) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact (W.localTriv i).open_source.preimage hcoe

/-- On a chart-open piece, the ratio is the composition of the continuous trivialisation
`W.localTriv i` with the (continuous) ratio of the chart coordinates. -/
theorem continuousOn_uvRatio_uvChartSet (i : Fin 3) : ContinuousOn uvRatio (uvChartSet i) := by
  have hcoe : Continuous (fun p : ↥(UR ∩ VR) => (p.1.1 : W.TotalSpace)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hchart : ContinuousOn (fun p : ↥(UR ∩ VR) => W.localTriv i (p.1.1)) (uvChartSet i) :=
    (W.localTriv i).continuousOn_toFun.comp hcoe.continuousOn (fun p hp => hp)
  have hnum : ContinuousOn (fun p : ↥(UR ∩ VR) =>
      ccoord (Work.Thom.cxImPart ((W.localTriv i (p.1.1)).2))) (uvChartSet i) :=
    ((continuous_ccoord.comp (cxImPartCLM.continuous.comp continuous_snd)).continuousOn).comp
      hchart (fun p hp => Set.mem_univ _)
  have hden : ContinuousOn (fun p : ↥(UR ∩ VR) =>
      ccoord (Work.Thom.cxRePart ((W.localTriv i (p.1.1)).2))) (uvChartSet i) :=
    ((continuous_ccoord.comp (cxRePartCLM.continuous.comp continuous_snd)).continuousOn).comp
      hchart (fun p hp => Set.mem_univ _)
  have hdiv := hnum.div hden (fun p hp => uvUi_ne_zero i p hp)
  refine ContinuousOn.congr hdiv ?_
  intro p hp
  rw [uvRatio_eq_chart_div i p hp]
  rfl

/-- **Every region of ratio values pulls back to an open set.** -/
theorem uvPieceIsOpen (Reg : Set ℂ) (hReg : IsOpen Reg) : IsOpen (uvPiece Reg) := by
  have hcover : uvPiece Reg = ⋃ i : Fin 3, (uvChartSet i ∩ uvPiece Reg) := by
    ext p
    constructor
    · intro hp
      exact Set.mem_iUnion.mpr ⟨W.indexAt p.1.1.1, W.mem_baseSet_at p.1.1.1, hp⟩
    · intro hp
      rcases Set.mem_iUnion.mp hp with ⟨i, -, h2⟩
      exact h2
  rw [hcover]
  refine isOpen_iUnion fun i => ?_
  exact (continuousOn_uvRatio_uvChartSet i).isOpen_inter_preimage (isOpen_uvChartSet i) hReg

end

end Work.ThomBordism.Grassmann

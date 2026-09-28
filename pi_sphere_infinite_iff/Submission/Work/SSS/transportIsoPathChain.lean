import Mathlib
import Submission.Work.SSS.transport_eq_topEnd
import Submission.Work.SSS.pbTransportDefs
import Submission.Work.Stems.hurewiczMapN_surjective

namespace Work.SSS

/-- **The path transport computed by a chain in the pullback.**

If `z` and `w` are cycles of the fibres over the two endpoints of a path `γ` (of a Serre fibration
`p`), and the difference of their images under the source and target chain maps of the edge is the
boundary of a chain `W` of the pullback — `∂ W = sourceChainMap z - targetChainMap w` — then the
classes of `z` and `w` correspond under the canonical fibre transport along `γ`.

This is the element-level form of the *functoriality* of `transportIsoPath` on chains: the transport
sends the homology class of `z` to the homology class of `w`, whenever the two are homologous in the
pullback of `p` along `γ`.  It generalises `Work.SSS.transport_eq_topEnd` (there `z` and `w` are the
chain of a simplex and the top end of its coherent lift, and `W` is the spread). -/
theorem transportIsoPathChain {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : ContinuousMap E B) (hp : Work.StemsB.IsSerreFibration p) {b₀ b₁ : B} (γ : Path b₀ b₁) (t : ℕ)
    (z : (Work.Stems.hChain (Work.StemsB.fibre p b₀)).X t)
    (hz : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₀)).d t
        ((ComplexShape.down ℕ).next t))) z = 0)
    (w : (Work.Stems.hChain (Work.StemsB.fibre p b₁)).X t)
    (hw : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₁)).d t
        ((ComplexShape.down ℕ).next t))) w = 0)
    (W : (Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap)).X (t+1))
    (hW : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap)).d
          (t+1) t)) W
        = (ModuleCat.Hom.hom ((Work.SSS.sourceChainMap p γ).f t)) z
          - (ModuleCat.Hom.hom ((Work.SSS.targetChainMap p γ).f t)) w) :
    (Work.SSS.transportIsoPath p hp γ t).hom
        ((ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₀)).homologyπ t))
          ((Work.Stems.hChain (Work.StemsB.fibre p b₀)).cyclesMk z
            ((ComplexShape.down ℕ).next t) rfl hz))
      = (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₁)).homologyπ t))
          ((Work.Stems.hChain (Work.StemsB.fibre p b₁)).cyclesMk w
            ((ComplexShape.down ℕ).next t) rfl hw) := by
  -- The transport is the source chain map on homology, followed by the "post" factor.
  rw [Work.SSS.transportIsoPath_apply p hp γ t]
  -- The source and target chain maps agree on the two homology classes: their difference on the
  -- chain representatives is `∂W`, hence a boundary.
  have hmap : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSS.sourceChainMap p γ) t))
        ((ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₀)).homologyπ t))
          ((Work.Stems.hChain (Work.StemsB.fibre p b₀)).cyclesMk z
            ((ComplexShape.down ℕ).next t) rfl hz))
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.SSS.targetChainMap p γ) t))
        ((ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₁)).homologyπ t))
          ((Work.Stems.hChain (Work.StemsB.fibre p b₁)).cyclesMk w
            ((ComplexShape.down ℕ).next t) rfl hw)) := by
    rw [Work.SSS.homologyMap_homologypi_cyclesMk' (Work.SSS.sourceChainMap p γ) t
          ((ComplexShape.down ℕ).next t) rfl z hz
          (by rw [Work.SSS.chainMap_comm_apply_C, hz, map_zero]),
        Work.SSS.homologyMap_homologypi_cyclesMk' (Work.SSS.targetChainMap p γ) t
          ((ComplexShape.down ℕ).next t) rfl w hw
          (by rw [Work.SSS.chainMap_comm_apply_C, hw, map_zero])]
    apply (Work.SSS.homologypi_eq_iff_sub_mem_range _ t _ _).mpr
    rw [Work.SSS.iCycles_cyclesMk_C, Work.SSS.iCycles_cyclesMk_C]
    exact ⟨W, hW⟩
  rw [hmap]
  -- The "post" factor inverts the target chain map on homology.
  exact Work.SSS.transportPost_apply p hp γ t _

end Work.SSS

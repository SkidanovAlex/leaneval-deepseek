import Mathlib
import Submission.Work.ThomBordism.gaussDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.Gauss

open Work.Tubular Work.ThomBordism.Grassmann Work.ThomBordism.PontryaginThom

/-- **Continuity of the inverse gauge `Φ⁻¹` on the overlap of the chart `S` of the oriented
Grassmannian with the chart `t` of the normal data.**

`phiInvCLM E ND S t x` is `matLin (phiInvMat E ND S t x)`, and

`phiInvMat E ND S t x = orientMat S (gauss E ND x) * frameMatrix S (ambFrame (orthFrame E ND t x))`

is a product of two matrix-valued functions: the orientation gauge `orientMat S (gauss E ND x)`,
continuous on `gauss E ND ⁻¹' baseSet S` because `gauss E ND` is continuous and `orientMat S` is
continuous on `baseSet S` (`continuousOn_orientMat`), and the `S`-coordinate matrix of the normal
frame, continuous on `ND.D.baseSet t` because the orthonormal frame `orthFrame E ND t` is
(`Work.Tubular.continuousOn_orthFrame`).  Continuity of `matLin` (`continuous_matLin`) finishes. -/
theorem continuousOn_phiInvCLM {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (S : Work.ThomBordism.Grassmann.ChartIdx k 8)
    (t : Work.ThomBordism.PontryaginThom.CoverIdx V k) :
    ContinuousOn (fun x => Work.ThomBordism.Gauss.phiInvCLM E ND S t x)
      {x : V.pt | Work.ThomBordism.Gauss.gauss E ND x ∈ Work.ThomBordism.Grassmann.baseSet S ∧
        x ∈ ND.D.baseSet t} := by
  set T : Set V.pt :=
    {x : V.pt | gauss E ND x ∈ baseSet S ∧ x ∈ ND.D.baseSet t} with hT
  change ContinuousOn (fun x => phiInvCLM E ND S t x) T
  -- the orientation gauge, pulled back along the Gauss map
  have hOri : ContinuousOn (fun x : V.pt => orientMat S (gauss E ND x)) T :=
    (continuousOn_orientMat S).comp ((gauss E ND).continuous.continuousOn)
      (fun x hx => hx.1)
  -- the normal frame, reindexed into `Amb (k+8)`
  have hamb : ContinuousOn (fun x : V.pt => ambFrame (orthFrame E ND t x)) (ND.D.baseSet t) := by
    rw [continuousOn_pi]
    intro a
    exact (ambEquiv k).continuous.comp_continuousOn
      (Work.Tubular.continuousOn_orthFrame E ND t a)
  -- the `S`-coordinate matrix of a frame, as a function of the frame
  have hcfm : Continuous (fun f : Fin k → Amb (k + 8) => frameMatrix S f) := by
    refine continuous_matrix fun i j => ?_
    exact (EuclideanSpace.proj (𝕜 := ℝ)
        (((S.1.equivFinOfCardEq S.2).symm i : ↥S.1) : Fin (k + 8))).continuous.comp
      (continuous_apply j)
  have hFr : ContinuousOn (fun x : V.pt => frameMatrix S (ambFrame (orthFrame E ND t x)))
      (ND.D.baseSet t) := hcfm.comp_continuousOn hamb
  -- the gauge matrix `phiInvMat`, continuous on the overlap
  have hMat : ContinuousOn (fun x : V.pt => phiInvMat E ND S t x) T :=
    hOri.mul (hFr.mono (fun x hx => hx.2))
  -- and `matLin` transports continuity to the space of continuous linear maps
  exact (continuous_matLin (k := k)).comp_continuousOn hMat

end Work.ThomBordism.Gauss

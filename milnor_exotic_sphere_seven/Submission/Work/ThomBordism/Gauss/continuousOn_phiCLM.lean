import Mathlib
import Submission.Work.ThomBordism.gaussDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Continuity of the gauge transformation `phiCLM`

For a point `x` of `V` lying in the chart `ND.D.baseSet t` of the normal data and whose Gauss point
`gauss E ND x` lies in the chart `baseSet S` of the oriented Grassmannian, the gauge transformation
`phiCLM E ND S t x` from the tautological `S`-coordinates to the normal `t`-coordinates is the
linear map `matLin (phiMat E ND S t x)` with matrix

`phiMat E ND S t x = (frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹ * orientMat S (gauss E ND x)`.

Both factors are continuous on the relevant sets: the normal frame `orthFrame E ND t ·` is continuous
on the chart `ND.D.baseSet t` (`continuousOn_orthFrame`), hence so is its `S`-frame matrix, whose
determinant does not vanish there; the matrix inverse is continuous where the determinant does not
vanish (`continuousOn_matrix_inv`); and the sign gauge `orientMat S (gauss E ND ·)` is continuous
because `gauss` is continuous and `orientMat S` is continuous on `baseSet S`
(`continuousOn_orientMat`).  Finally `matLin` is continuous in the matrix (`continuous_matLin`).
-/

open scoped Manifold ContDiff Topology BigOperators

namespace Work.ThomBordism.Gauss

open Work.ThomBordism.PontryaginThom Work.ThomBordism.OrthFrame Work.ThomBordism.Grassmann
open Work.Tubular

noncomputable section

theorem continuousOn_phiCLM {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (S : Work.ThomBordism.Grassmann.ChartIdx k 8)
    (t : Work.ThomBordism.PontryaginThom.CoverIdx V k) :
    ContinuousOn (fun x => Work.ThomBordism.Gauss.phiCLM E ND S t x)
      {x : V.pt | Work.ThomBordism.Gauss.gauss E ND x ∈ Work.ThomBordism.Grassmann.baseSet S ∧
        x ∈ ND.D.baseSet t} := by
  set s : Set V.pt := {x : V.pt | gauss E ND x ∈ baseSet S ∧ x ∈ ND.D.baseSet t} with hs
  have hsel : ∀ x ∈ s, gauss E ND x ∈ baseSet S := fun x hx => hx.1
  have hselt : ∀ x ∈ s, x ∈ ND.D.baseSet t := fun x hx => hx.2
  -- the sign gauge composed with the Gauss map
  have hgauss : ContinuousOn (fun x => orientMat S (gauss E ND x)) s :=
    (continuousOn_orientMat S).comp
      ((gauss E ND).continuous.continuousOn.mono (Set.subset_univ s)) (fun x hx => hsel x hx)
  -- the ambient normal frame
  have hamb : ContinuousOn (fun x => ambFrame (orthFrame E ND t x)) s := by
    rw [continuousOn_pi]
    intro a
    exact (ambEquiv k).continuous.comp_continuousOn
      ((continuousOn_orthFrame E ND t a).mono (fun x hx => hselt x hx))
  -- the frame matrix of the normal frame, and its inverse
  have hfm : Continuous (fun F : Fin k → Amb (k+8) => frameMatrix S F) := by
    refine continuous_matrix fun i j => ?_
    exact (EuclideanSpace.proj (𝕜 := ℝ)
      (((S.1.equivFinOfCardEq S.2).symm i : ↥S.1) : Fin (k+8))).continuous.comp
        (continuous_apply j)
  have hframe : ContinuousOn (fun x => frameMatrix S (ambFrame (orthFrame E ND t x))) s :=
    hfm.comp_continuousOn hamb
  have hinv : ContinuousOn (fun x => (frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹) s :=
    (continuousOn_matrix_inv k).comp hframe
      (fun x hx => det_frameMatrix_orthFrame_ne_zero E ND S t (hselt x hx) (hsel x hx))
  have hprod : ContinuousOn (fun x => (frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹
      * orientMat S (gauss E ND x)) s := hinv.mul hgauss
  have hfinal : ContinuousOn (fun x => matLin (phiMat E ND S t x)) s :=
    continuous_matLin.comp_continuousOn hprod
  simpa [hs, phiCLM] using hfinal

end

end Work.ThomBordism.Gauss

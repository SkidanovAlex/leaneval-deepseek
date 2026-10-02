import Mathlib
import Submission.Work.ThomBordism.OrthFrame.Cocycle
import Submission.Work.ThomBordism.FrameSigns.Assembly

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The cocycle law of the explicit frame sign `frameSign · framePairSign`

`Work.ThomBordism.FrameSigns.frameSign V i x` is the *explicit* sign of the chart tangent frame of
the closed oriented `8`-manifold `V` against the given fundamental class `V.c`
(`FrameSigns/Charts.lean`), and `Work.ThomBordism.framePairSign E ND i x` is the sign of the
concatenated tangent/normal frame of the normal data of an embedding `E : V ↪ ℝ^{8+k}`
(`OrthFrame/Assembly.lean`).  The product

  `sigmaFS i x = FrameSigns.frameSign V i.1 x * framePairSign E ND i x`

is the *canonical* (non-opaque) sign cocycle of the coorientation of the normal bundle.

The content here is the cocycle law of that product: on the overlap of two base sets it is the sign
of the determinant of the change-of-frame matrix `frameChange E ND i j x`.  The two inputs are

* `Work.ThomBordism.FrameSigns.frameSign_mul` — the cocycle law of the *tangent* frame signs
  (the product of the two chart frame signs is the sign of the transition Jacobian, i.e. of the
  determinant of the chart change, see `OrthFrame.tanFrame_change`), and
* `Work.ThomBordism.OrthFrame.sign_det_pairMat` — the determinant sign of a pair frame is the product
  of the two block determinant signs (the algebraic content of `TV ⊕ ν` being trivial).
-/

open scoped Manifold ContDiff Topology BigOperators

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.ThomBordism.OrthFrame

noncomputable section

variable {V : Man8} {k : ℕ}

theorem frameSign_fps_cocycle {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (i j : Work.ThomBordism.PontryaginThom.CoverIdx V k) {x : V.pt}
    (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j) :
    (Work.ThomBordism.FrameSigns.frameSign V i.1 x * Work.ThomBordism.framePairSign E ND i x)
      * (Work.ThomBordism.FrameSigns.frameSign V j.1 x * Work.ThomBordism.framePairSign E ND j x)
      = Real.sign ((Work.ThomBordism.frameChange E ND i j x).det) := by
  -- the change-of-frame matrix `C` of the tangent frames, with its determinant identity
  obtain ⟨C, hCrel, hCdet, hCeq⟩ := tanFrame_change E ND i j hx.1 hx.2
  have hMdet : (frameChange E ND i j x).det ≠ 0 := frameChange_det_ne_zero E ND i j hx
  -- the block-determinant rule for the pair frames
  have hA2 := sign_det_pairMat hCrel (frameChange_expand E ND i j hx)
    (pairMat_det_ne_zero E ND j hx.2) hCdet hMdet
  -- the cocycle law of the tangent frame signs, in the syntactic form of `hCeq`
  have hδ := FrameSigns.frameSign_mul V i.1 j.1 (ND.baseSet_sub i.1 i.2 x hx.1)
    (ND.baseSet_sub j.1 j.2 x hx.2)
  have hδc : FrameSigns.frameSign V i.1 x * FrameSigns.frameSign V j.1 x
      = Real.sign (LinearMap.det (ContinuousLinearMap.toLinearMap (fderiv ℝ
          (fun y => (Work.ThomBordism.PontryaginThom.coverChart j).1
            ((Work.ThomBordism.PontryaginThom.coverChart i).1.symm y))
          ((Work.ThomBordism.PontryaginThom.coverChart i).1 x)))) := hδ
  have hδ' : FrameSigns.frameSign V i.1 x * FrameSigns.frameSign V j.1 x = Real.sign C.det := by
    rw [hδc, ← hCeq]
  have hprod : framePairSign E ND i x * framePairSign E ND j x
      = Real.sign C.det * Real.sign ((frameChange E ND i j x).det) := hA2
  have hc1 : Real.sign C.det = -1 ∨ Real.sign C.det = 1 :=
    Real.sign_apply_eq_of_ne_zero C.det hCdet
  -- the two `ℝ`-factors commute, and `sign C.det = ±1` absorbs itself
  calc (FrameSigns.frameSign V i.1 x * framePairSign E ND i x)
        * (FrameSigns.frameSign V j.1 x * framePairSign E ND j x)
      = (FrameSigns.frameSign V i.1 x * FrameSigns.frameSign V j.1 x)
        * (framePairSign E ND i x * framePairSign E ND j x) := by ring
    _ = Real.sign C.det * (Real.sign C.det * Real.sign ((frameChange E ND i j x).det)) := by
          rw [hδ', hprod]
    _ = Real.sign ((frameChange E ND i j x).det) := by
          rcases hc1 with h | h <;> rw [h] <;> ring

end

end Work.ThomBordism

import Mathlib
import Submission.Work.ThomBordism.OrthFrame.Assembly
import Submission.Work.ThomBordism.OrthFrame.tanFrame_change
import Submission.Work.ThomBordism.tangentFrameSigns

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# The orientation cocycle of the chartwise normal frames

Combining the chart-atlas signs `Work.ThomBordism.tangentFrameSigns` with the block-determinant rule
`Work.ThomBordism.OrthFrame.sign_det_pairMat` (via the chart-transition bridge
`Work.ThomBordism.OrthFrame.tanFrame_change`), the corrected pair signs
`ε i x = δ i.1 x · framePairSign E ND i x` satisfy the normal-bundle orientation cocycle
`ε i x · ε j x = sign (det (frameChange E ND i j x))`.
-/

open scoped Manifold ContDiff Topology BigOperators

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.ThomBordism.OrthFrame

noncomputable section

variable {V : Man8} {k : ℕ}

/-- `Real.sign` of a real number is that number when the latter is `±1`. -/
theorem sign_eq_self_of_eq_one_or_neg_one {t : ℝ} (h : t = 1 ∨ t = -1) : Real.sign t = t := by
  rcases h with h | h <;> rw [h] <;> norm_num [Real.sign_of_pos, Real.sign_of_neg]

/-- **The orientation cocycle of the chartwise normal frames.** -/
theorem framePairSign_cocycle (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    ∃ δ : (i : Fin (Work.Thom.chartCoverSize (H := Euc 8) (M := V.pt))) → V.pt → ℝ,
      (∀ (i : Fin (Work.Thom.chartCoverSize (H := Euc 8) (M := V.pt))) (x : V.pt),
        δ i x = 1 ∨ δ i x = -1) ∧
      (∀ i, ContinuousOn (δ i)
        (Work.Thom.chartCover (H := Euc 8) (M := V.pt) i).1.source) ∧
      (∀ (i j : Fin (Work.Thom.chartCoverSize (H := Euc 8) (M := V.pt)))
        (x : V.pt)
        (_hi : x ∈ (Work.Thom.chartCover (H := Euc 8) (M := V.pt) i).1.source)
        (_hj : x ∈ (Work.Thom.chartCover (H := Euc 8) (M := V.pt) j).1.source),
        δ i x * δ j x = Real.sign (LinearMap.det (ContinuousLinearMap.toLinearMap
          (fderiv ℝ
            (fun y => (Work.Thom.chartCover (H := Euc 8) (M := V.pt) j).1
              ((Work.Thom.chartCover (H := Euc 8) (M := V.pt) i).1.symm y))
            ((Work.Thom.chartCover (H := Euc 8) (M := V.pt) i).1 x))))) ∧
      (∀ (i j : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j),
        (δ i.1 x * framePairSign E ND i x) * (δ j.1 x * framePairSign E ND j x)
          = Real.sign ((frameChange E ND i j x).det)) := by
  obtain ⟨δ, hval, hcont, hrule⟩ := tangentFrameSigns (V := V)
  refine ⟨δ, hval, hcont, hrule, ?_⟩
  intro i j x hx
  obtain ⟨C, hCrel, hCdet, hCeq⟩ := tanFrame_change E ND i j hx.1 hx.2
  have hMdet : (frameChange E ND i j x).det ≠ 0 := frameChange_det_ne_zero E ND i j hx
  have hA2 := sign_det_pairMat hCrel (frameChange_expand E ND i j hx)
    (pairMat_det_ne_zero E ND j hx.2) hCdet hMdet
  have hδ := hrule i.1 j.1 x (ND.baseSet_sub i.1 i.2 x hx.1) (ND.baseSet_sub j.1 j.2 x hx.2)
  have hδ' : δ i.1 x * δ j.1 x = Real.sign C.det := by
    rw [hδ, ← hCeq]
  have hprod : framePairSign E ND i x * framePairSign E ND j x
      = Real.sign C.det * Real.sign ((frameChange E ND i j x).det) := hA2
  have hc1 : Real.sign C.det = -1 ∨ Real.sign C.det = 1 :=
    Real.sign_apply_eq_of_ne_zero C.det hCdet
  calc (δ i.1 x * framePairSign E ND i x) * (δ j.1 x * framePairSign E ND j x)
      = (δ i.1 x * δ j.1 x) * (framePairSign E ND i x * framePairSign E ND j x) := by ring
    _ = Real.sign C.det * (Real.sign C.det * Real.sign ((frameChange E ND i j x).det)) := by
          rw [hδ', hprod]
    _ = Real.sign ((frameChange E ND i j x).det) := by
          rcases hc1 with h | h <;> rw [h] <;> ring

end

end Work.ThomBordism

import Mathlib
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.ThomBordism.Grassmann.Grassmannian
import Submission.Work.ThomBordism.PontryaginThom.NormalData
import Submission.Work.ThomBordism.OrthFrame.Defs
import Submission.Work.ThomBordism.OrthFrame.sign_det_combMat
import Submission.Work.ThomBordism.OrthFrame.FrameAlgebra
import Submission.Work.ThomBordism.OrthFrame.Assembly
import Submission.Work.ThomBordism.OrthFrame.Cocycle

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
# The orientation correction of the chartwise normal frames

For the normal data `ND` of an embedding `E : V ↪ ℝ^{8+k}` of a closed oriented `8`-manifold, the
chartwise orthonormal frames `Work.Tubular.orthFrame E ND i x` of the normal plane `ν_x` are only
`O(k)`-related on the overlap of two indices; `orthFrameOrientation` produces the signs `ε i x = ±1`,
continuous on `ND.D.baseSet i`, that make the corrected frames `ε i x • orthFrame E ND i x` differ by
an element of `SO(k)` on the overlap.

The content is the orientability of the normal bundle `ν ≅ TV^⊥`, hence of `V`, which follows from
the fundamental class `V.c` (`V.c_fund`).  The proof assembled here uses

* `Work.ThomBordism.tangentFrameSigns` — the chart-atlas sign cocycle of `V` splits (the deep input,
  derived from `V.c_fund`);
* `Work.ThomBordism.OrthFrame.sign_det_pairMat` — the determinant sign of the concatenation of the
  tangent and the normal frame is the product of the two block determinant signs ("`TV ⊕ ν` is
  trivial");
* `Work.ThomBordism.OrthFrame.frameChange_transpose_mul`, `..._det_ne_zero`,
  `Work.ThomBordism.OrthFrame.framePairSign_eq_one_or`,
  `Work.ThomBordism.OrthFrame.continuousOn_framePairSign` — the frame algebra of the normal frames;
* `Work.ThomBordism.OrthFrame.isSO_smul_of_det` — for odd `k` a `±` multiple of an orthogonal matrix
  with `det = ±1` and determinant equal to that sign is special orthogonal (this is where `hk` is
  used).
-/

open scoped Manifold ContDiff Topology BigOperators

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.ThomBordism.OrthFrame

noncomputable section

variable {V : Man8} {k : ℕ}

/-- **The orientation correction of the chartwise normal frames.** -/
theorem orthFrameOrientation {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (hk : Odd k) :
    ∃ ε : (i : Work.ThomBordism.PontryaginThom.CoverIdx V k) → V.pt → ℝ,
      (∀ (i : Work.ThomBordism.PontryaginThom.CoverIdx V k) (x : V.pt), ε i x = 1 ∨ ε i x = -1) ∧
      (∀ i, ContinuousOn (ε i) (ND.D.baseSet i)) ∧
      ∀ (i j : Work.ThomBordism.PontryaginThom.CoverIdx V k) (x : V.pt)
        (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j),
        ∃ A : Work.ThomBordism.Grassmann.SOk k,
          ∀ a : Fin k, ε i x • Work.Tubular.orthFrame E ND i x a
            = ∑ b : Fin k, A.1 b a • (ε j x • Work.Tubular.orthFrame E ND j x b) := by
  classical
  obtain ⟨δ, hval, hcont, hrule, hcoc⟩ := framePairSign_cocycle E ND
  refine ⟨fun i x => if h : x ∈ ND.D.baseSet i then
      δ i.1 x * framePairSign E ND i x else 1, ?_, ?_, ?_⟩
  · intro i x
    by_cases h : x ∈ ND.D.baseSet i
    · simp only [dif_pos h]
      rcases hval i.1 x with h1 | h1 <;>
        rcases framePairSign_eq_one_or E ND i h with h2 | h2 <;>
        rw [h1, h2] <;> norm_num
    · simp only [dif_neg h]; norm_num
  · intro i
    refine ContinuousOn.congr (f := fun x => δ i.1 x * framePairSign E ND i x) ?_ ?_
    · exact ((hcont i.1).mono (fun x hx => ND.baseSet_sub i.1 i.2 x hx)).mul
        (continuousOn_framePairSign E ND i)
    · intro x hx
      simp only [dif_pos hx]
  · intro i j x hx
    simp only [dif_pos hx.1, dif_pos hx.2]
    have hc : (δ i.1 x * framePairSign E ND i x) * (δ j.1 x * framePairSign E ND j x)
        = Real.sign ((frameChange E ND i j x).det) := hcoc i j x hx
    have hMdet : (frameChange E ND i j x).det ≠ 0 := frameChange_det_ne_zero E ND i j hx
    have hM1 : (frameChange E ND i j x).det = 1 ∨ (frameChange E ND i j x).det = -1 := by
      have h1 := congrArg Matrix.det (frameChange_transpose_mul E ND i j hx)
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← sq] at h1
      exact sq_eq_one_iff.mp h1
    have hsignM : Real.sign ((frameChange E ND i j x).det) = (frameChange E ND i j x).det :=
      sign_eq_self_of_eq_one_or_neg_one hM1
    have hc' : (δ i.1 x * framePairSign E ND i x) * (δ j.1 x * framePairSign E ND j x)
        = (frameChange E ND i j x).det := by rw [hc, hsignM]
    have hAB : ((δ i.1 x * framePairSign E ND i x) * (δ j.1 x * framePairSign E ND j x)) = 1 ∨
        ((δ i.1 x * framePairSign E ND i x) * (δ j.1 x * framePairSign E ND j x)) = -1 := by
      rw [hc']; exact hM1
    have hssq : (δ j.1 x * framePairSign E ND j x) * (δ j.1 x * framePairSign E ND j x) = 1 := by
      rcases hval j.1 x with h1 | h1 <;>
        rcases framePairSign_eq_one_or E ND j hx.2 with h2 | h2 <;>
        rw [h1, h2] <;> norm_num
    have hmain : ∀ a : Fin k,
        (δ i.1 x * framePairSign E ND i x) • Work.Tubular.orthFrame E ND i x a
          = ∑ b : Fin k,
              (((δ i.1 x * framePairSign E ND i x) * (δ j.1 x * framePairSign E ND j x))
                * (frameChange E ND i j x) b a)
              • ((δ j.1 x * framePairSign E ND j x) • Work.Tubular.orthFrame E ND j x b) := by
      intro a
      rw [frameChange_expand E ND i j hx a, Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hscal : (δ i.1 x * framePairSign E ND i x) * (frameChange E ND i j x) b a
          = ((δ i.1 x * framePairSign E ND i x) * (δ j.1 x * framePairSign E ND j x))
              * (frameChange E ND i j x) b a * (δ j.1 x * framePairSign E ND j x) := by
        calc (δ i.1 x * framePairSign E ND i x) * (frameChange E ND i j x) b a
            = (δ i.1 x * framePairSign E ND i x) * (frameChange E ND i j x) b a * 1 := by ring
          _ = (δ i.1 x * framePairSign E ND i x) * (frameChange E ND i j x) b a
                * ((δ j.1 x * framePairSign E ND j x) * (δ j.1 x * framePairSign E ND j x)) := by
                rw [hssq]
          _ = ((δ i.1 x * framePairSign E ND i x) * (δ j.1 x * framePairSign E ND j x))
                * (frameChange E ND i j x) b a * (δ j.1 x * framePairSign E ND j x) := by ring
      simp only [smul_smul]
      rw [hscal]
    refine ⟨⟨((δ i.1 x * framePairSign E ND i x) * (δ j.1 x * framePairSign E ND j x))
      • frameChange E ND i j x, isSO_smul_of_det
        ((δ i.1 x * framePairSign E ND i x) * (δ j.1 x * framePairSign E ND j x))
        hAB (frameChange_transpose_mul E ND i j hx) hc' hk⟩, ?_⟩
    · intro a
      exact hmain a

end

end Work.ThomBordism

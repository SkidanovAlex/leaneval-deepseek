import Mathlib
import Submission.Work.ThomBordism.sigmaFSDefs
import Submission.Work.ThomBordism.sigmaExplicit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.ThomBordism.OrthFrame Work.Tubular

/-- **The `σ`-telescoping for the canonical frame-sign cocycle `σFS`.**

With `δ i x := FrameSigns.frameSign V i.1 x` (the *explicit* sign of the chart tangent frame against
the given fundamental class `V.c`, as opposed to the opaque `Classical.choose` witness), the canonical
sign cocycle `σFS = δ · fps` is exactly the correction that makes the corrected normal frame
`gframeFS` the one whose closing-up frame with the `V.c`-oriented tangent frame `flipTan E i x δ` is
the standard orientation of `ℝ^{8+k}`:

  `pairSign (flipTan E i x δ) (gframeFS E ND i x) = 1`.

This is the verbatim analogue of `Work.ThomBordism.sigmaTelescope` with the explicit `frameSign` in
place of `Classical.choose (framePairSign_cocycle E ND)`.

Proof: one application of the block-determinant rule `sign_det_pairMat` with the two diagonal changes
of frame `C = Hmat δ`, `M = Hmat σFS` gives

  `pairSign (flipTan δ) (gframeFS) · fps = sign δ · sign σFS = δ · σFS = δ · (δ · fps) = fps`,

and `fps = ±1 ≠ 0`, so `pairSign (flipTan δ) (gframeFS) = 1`. -/
theorem sigmaTelescope_frameSign {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (hk : 1 ≤ k)
    (i : Work.ThomBordism.PontryaginThom.CoverIdx V k) (x : V.pt)
    (hx : x ∈ ND.D.baseSet i) :
    Work.ThomBordism.OrthFrame.pairSign
      (Work.ThomBordism.flipTan E i x (Work.ThomBordism.FrameSigns.frameSign V i.1 x))
      (Work.ThomBordism.gframeFS E ND i x) = 1 := by
  classical
  let δ : ℝ := FrameSigns.frameSign V i.1 x
  have hδval : δ = 1 ∨ δ = -1 := FrameSigns.frameSign_eq_one_or_neg_one V i.1 x
  have hδ2 : δ * δ = 1 := by
    rcases hδval with h | h <;> rw [h] <;> norm_num
  have hσmem : sigmaFS E ND i x = δ * framePairSign E ND i x :=
    sigmaFS_of_mem E ND i x hx
  have hσval : sigmaFS E ND i x = 1 ∨ sigmaFS E ND i x = -1 := by
    rw [hσmem]
    rcases hδval with h | h <;>
      rcases framePairSign_eq_one_or E ND i hx with h2 | h2 <;>
      rw [h, h2] <;> norm_num
  have hfps : framePairSign E ND i x ≠ 0 := by
    rcases framePairSign_eq_one_or E ND i hx with h | h <;> rw [h] <;> norm_num
  -- The two diagonal changes of frame.
  have hC : ∀ a : Fin 8, flipTan E i x δ a
      = ∑ a', (Gauss.Hmat (k := 8) δ) a' a • tanFrame E i x a' := by
    intro a
    show flipTan E i x δ a = Gauss.frameAct (Gauss.Hmat (k := 8) δ) (tanFrame E i x) a
    rw [Gauss.frameAct_Hmat]
    unfold flipTan
    by_cases ha : (a : ℕ) = 0 <;> simp [ha]
  have hM : ∀ b : Fin k, gframeFS E ND i x b
      = ∑ b', Gauss.Hmat (k := k) (sigmaFS E ND i x) b' b
          • Work.Tubular.orthFrame E ND i x b' :=
    gframeFS_rel E ND i x
  have hdet : (pairMat (tanFrame E i x) (Work.Tubular.orthFrame E ND i x)).det ≠ 0 :=
    pairMat_det_ne_zero E ND i hx
  have hCdet : (Gauss.Hmat (k := 8) δ).det ≠ 0 := by
    rw [Gauss.Hmat_det (k := 8) (by norm_num) δ]
    rcases hδval with h | h <;> rw [h] <;> norm_num
  have hMdet : (Gauss.Hmat (k := k) (sigmaFS E ND i x)).det ≠ 0 := by
    rw [Gauss.Hmat_det (k := k) hk (sigmaFS E ND i x)]
    rcases hσval with h | h <;> rw [h] <;> norm_num
  have hmain := sign_det_pairMat (F := flipTan E i x δ) (F' := tanFrame E i x)
    (G := gframeFS E ND i x) (G' := Work.Tubular.orthFrame E ND i x)
    (C := Gauss.Hmat (k := 8) δ) (M := Gauss.Hmat (k := k) (sigmaFS E ND i x))
    hC hM hdet hCdet hMdet
  rw [Gauss.Hmat_det (k := 8) (by norm_num) δ, Gauss.Hmat_det (k := k) hk (sigmaFS E ND i x)]
    at hmain
  rw [sign_eq_self_of_eq_one_or_neg_one hδval,
    sign_eq_self_of_eq_one_or_neg_one hσval] at hmain
  have hmain' : pairSign (flipTan E i x δ) (gframeFS E ND i x) * framePairSign E ND i x
      = δ * sigmaFS E ND i x := hmain
  have htarget : pairSign (flipTan E i x δ) (gframeFS E ND i x) * framePairSign E ND i x
      = framePairSign E ND i x := by
    rw [hmain', hσmem]
    calc δ * (δ * framePairSign E ND i x) = (δ * δ) * framePairSign E ND i x := by rw [mul_assoc]
      _ = 1 * framePairSign E ND i x := by rw [hδ2]
      _ = framePairSign E ND i x := by rw [one_mul]
  refine mul_right_cancel₀ hfps ?_
  rw [one_mul]
  exact htarget

end Work.ThomBordism

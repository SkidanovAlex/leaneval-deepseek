import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs
import Submission.Work.FTS.EllSol.ShiftFT.AtwoAux.Defs
import Submission.Work.FTS.EllSol.ShiftFT.uTr_niceFlat
import Submission.Work.FTS.EllSol.Trunc.PassAux
import Submission.Work.FTS.EllSol.Trunc.chiMulDerivs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-- The pointwise expression `W` is a.e. strongly measurable on the half-strip: by the a.e.
identity `uTr_L2_eq` it agrees with the shifted second slot of the truncated datum `uTr N b u`,
which is `C²` on the open strip by `uTr_niceFlat`. -/
theorem uTrAtwo_W_aesm (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 2 ≤ N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ t : ℝ, u t 0 = 0) (h1 : ∀ t : ℝ, u t (Real.pi / 2) = 0) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (uTrAtwo_W N b u p) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := by
  have hnf : Work.FTS.EllSol.FlatFT.NiceFlat (uTr N b u) := uTr_niceFlat N b u hN hu h0 h1
  have hC2 : ContDiffOn ℝ 2 (Function.uncurry (uTr N b u))
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := hnf.1
  have hV : IsOpen ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    isOpen_univ.prod isOpen_Ioo
  have hpz : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz (uTr N b u)))
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllSol.Trunc.contDiffOn_uncurry_pz_succ hV 1 hC2
  have hpzpz : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz (uTr N b u))))
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllSol.Trunc.contDiffOn_uncurry_pz_succ hV 0 hpz
  have haesm_L2T : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (uTrAtwo_L2 b (uTr N b u) p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := by
    have hA : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pz (uTr N b u)) p.1 p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      Work.FTS.EllSol.Trunc.aesm_strip hpzpz.continuousOn
    have hB : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.pz (uTr N b u) p.1 p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      Work.FTS.EllSol.Trunc.aesm_strip hpz.continuousOn
    have hC : AEStronglyMeasurable (fun p : ℝ × ℝ => uTr N b u p.1 p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      Work.FTS.EllSol.Trunc.aesm_strip hC2.continuousOn
    have hwE : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.FTS.EllSol.FlatFT.wE p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      Work.FTS.EllSol.Trunc.aesm_strip Work.FTS.EllSol.Trunc.continuousOn_wE_comp
    change AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (Work.Spaces.pz (uTr N b u)) p.1 p.2
        - 2 * b * Work.Spaces.pz (uTr N b u) p.1 p.2
        + b ^ 2 * uTr N b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ))
    have hmain : AEMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.pz (uTr N b u)) p.1 p.2
          - 2 * b * Work.Spaces.pz (uTr N b u) p.1 p.2
          + b ^ 2 * uTr N b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      (((hA.aemeasurable.sub ((hB.aemeasurable).const_mul (2 * b))).add
        ((hC.aemeasurable).const_mul (b ^ 2))).pow_const 2).mul hwE.aemeasurable
    exact hmain.aestronglyMeasurable
  refine haesm_L2T.congr ?_
  filter_upwards [ae_uTr_L2_eq N b u hu] with p hp
  rw [hp]

end

end Work.FTS.EllSol.ShiftFT

import Mathlib
import Submission.Work.EKLC7.SmulMS
import Submission.Work.EKLC7.atom_smulMS
import Submission.Work.EKLC7.shape_smulMS
import Submission.Work.EKLC7.restrict_smulSt
import Submission.Work.EKLC7.isPlaqueAlgebra_smulMS
import Submission.Work.EKLC7.BigShapeFlowers
import Submission.Work.EKLC7.AeFreeStab
import Submission.Work.EKLRelCross.leafwise_propor
import Submission.Work.EKLRelCross.rightQuasiInv
import Submission.Work.EKLC7Ae.Endgame
import Submission.Work.EKLC7Ae.Inputs
import Submission.Work.EKLC7Ae.Closed

namespace Work.EKLC7

theorem AeHaar_of_isUInvariant (h2 : Work.EKLContract.P_X3)
    (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹)
      Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    (X' : Set Work.EKLContract.X3) (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hinv : Work.EKLContract.IsUInvariant μ U) :
    ∀ᵐ x ∂μ, ∀ u ∈ U, (ν x).map (fun g : Work.EKLContract.SL3 => g * u) = ν x := by
  obtain ⟨Z, G, m, R, hpa, hbase, -, hshape, hcover⟩ :=
    Work.EKLC7Ae.exists_shape_family h2 μ U hU t0 hmp hcontr
  obtain ⟨D, hDc, hDU, hDdense, hDsymm⟩ := Work.EKLC7Ae.exists_countable_dense_in_U U hU.1
  refine Work.EKLC7Ae.aeHaar_of_shape_propor h2 μ U hU t0 hmp hcontr ν X' hL hinv
    (Z := Z) (G := G) (m := m) (R := R) (fun n => (hbase n).2) hshape hcover D hDU hDc hDsymm
    hDdense ?_ ?_
  · exact Work.EKLC7Ae.shape_propor_ae h2 μ U hU t0 hmp hcontr ν X' hL hinv hpa D hDU hDc
  · intro x hx
    refine Work.EKLC7Ae.isClosed_quasiInvLeft (ν x) (hL.radon x hx) ?_
    intro h0
    have h1 := hL.normalised x hx
    rw [h0] at h1
    simp at h1

end Work.EKLC7

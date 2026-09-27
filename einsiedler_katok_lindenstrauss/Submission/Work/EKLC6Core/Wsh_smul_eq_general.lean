import Mathlib
import Submission.Work.EKLC6Core.AtomInfoSetup
import Submission.Work.EKLC6Core.HcondSig_aux
import Submission.Work.EKLRelCross.plaque.helper

namespace Work.EKLC6Core

theorem Wsh_smul_eq_general {U : Subgroup Work.EKLContract.SL3} {A : MeasurableSpace Work.EKLContract.X3}
    (t : Fin 3 → ℝ) {x : Work.EKLContract.X3} {u : Work.EKLContract.SL3}
    (hu : u ∈ Work.EKLC6Core.Wsh t ⟨A⟩ U x) :
    Work.EKLC6Core.Wsh t ⟨A⟩ U (u • x)
      = (fun v : Work.EKLContract.SL3 => v * u⁻¹) '' Work.EKLC6Core.Wsh t ⟨A⟩ U x := by
  have huU : u ∈ U := hu.1
  have huatom : u • x ∈ Work.EKLContract.atom (Work.EKLC6Core.betaAlg t ⟨A⟩) x := hu.2
  rw [Wsh_def]
  exact Work.EKLRelCross.shape_smul_right huU huatom

end Work.EKLC6Core

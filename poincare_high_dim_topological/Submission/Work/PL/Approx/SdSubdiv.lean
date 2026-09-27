import Submission.Work.PL.Approx.Defs
import Submission.Work.PL.Subdiv.SdBasic
import Submission.Work.PL.Subdiv.Util.Mesh.exists_fine_general

/-!
# The barycentric subdivision as a `Subdiv` (area A5 bridge)

Area A2 (`Submission.Work.PL.Subdiv`) provides the barycentric subdivision `Work.PL.Subdiv.sd`
of a geometric complex together with `sd_subdivides`, `sd_faces_finite` and the mesh theorem
`Work.PL.Subdiv.Util.Mesh.exists_fine_general`.  This file packages them as an element of the
`Subdiv` interface of `Submission.Work.PL.Approx.Defs`, so that the PL approximation theorems of
this area (`pl_approx`, `pl_approx_frozen`, ...) can be applied to the actual barycentric
subdivision.  The bridge `Subdiv.iter_sdSubdiv` makes A2's lemmas about `sdIter` available for
`Subdiv.iter`.
-/

open Set Metric
open scoped BigOperators

namespace Work.PL.Approx

noncomputable section

variable {N : ℕ}

/-- `iterAuxK` for the barycentric subdivision is the iterated barycentric subdivision `sdIter`. -/
theorem iterAuxK_bary (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite) :
    iterAuxK (fun K (_ : K.faces.Finite) => Work.PL.Subdiv.sd K)
      (fun K hK => Work.PL.Subdiv.sd_faces_finite hK) r K hK
      = Work.PL.Subdiv.sdIter r K hK := by
  induction r with
  | zero => rfl
  | succ r ih =>
    show Work.PL.Subdiv.sd (iterAuxK (fun K (_ : K.faces.Finite) => Work.PL.Subdiv.sd K)
        (fun K hK => Work.PL.Subdiv.sd_faces_finite hK) r K hK)
      = Work.PL.Subdiv.sd (Work.PL.Subdiv.sdIter r K hK)
    rw [ih]

/-- The barycentric subdivision `Work.PL.Subdiv.sd`, packaged as a `Subdiv`. -/
def sdSubdiv (N : ℕ) : Subdiv N where
  sd := fun K _ => Work.PL.Subdiv.sd K
  fin := fun K hK => Work.PL.Subdiv.sd_faces_finite hK
  subdivides := fun K _ => Work.PL.Subdiv.sd_subdivides K
  mesh := fun K hK δ hδ => by
    obtain ⟨r, hr⟩ := Work.PL.Subdiv.Util.Mesh.exists_fine_general K hK δ hδ
    exact ⟨r, by rw [iterAuxK_bary]; exact hr r le_rfl⟩

/-- The iterates of `sdSubdiv` are the iterated barycentric subdivisions `sdIter`. -/
theorem Subdiv.iter_sdSubdiv (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite) :
    (sdSubdiv N).iter r K hK = Work.PL.Subdiv.sdIter r K hK := iterAuxK_bary r K hK

end

end Work.PL.Approx

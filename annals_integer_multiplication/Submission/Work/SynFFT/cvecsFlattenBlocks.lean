import Mathlib
import Submission.Work.SynFFT.kit2

namespace Work.SynFFT

theorem cvecsFlattenBlocks (Vs : List (List (List (ℤ × ℤ)))) :
    Work.SynFFT.cvecs Vs.flatten = (Vs.map Work.SynFFT.cvecs).flatten := by
  simp only [Work.SynFFT.cvecs]
  exact List.map_flatten

example (Vs : List (List (List (ℤ × ℤ)))) :
    Work.SynFFT.cvecs Vs.flatten = (Vs.map Work.SynFFT.cvecs).flatten := by
  show (Vs.flatten).map HvdH.cvecVal = (Vs.map (List.map HvdH.cvecVal)).flatten
  exact List.map_flatten (f := HvdH.cvecVal) (L := Vs)

end Work.SynFFT

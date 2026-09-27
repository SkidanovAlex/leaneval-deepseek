import Mathlib
import Submission.Work.Drive.PushDisc.milnorLens

namespace Work.Drive.PushDisc

/-- Dropping the last block of a linearly independent juxtaposed family: if
`P ++ U ++ V` is linearly independent then so is its prefix `P ++ U`.

The prefix is the image of the full family under the injective map
`Fin.castAdd k : Fin (2 + k) → Fin ((2 + k) + k)`, so `LinearIndependent.comp`
applies; the only point to check is that `Fin.append (Fin.append P U) V` composed
with `Fin.castAdd k` is `Fin.append P U`, which is `Fin.append_left`. -/
theorem linIndDropLastBlock {k : ℕ} (P : Fin 2 → Work.Drive.Whitney.Mdl k)
    (U V : Fin k → Work.Drive.Whitney.Mdl k)
    (h : LinearIndependent ℝ (Fin.append (Fin.append P U) V)) :
    LinearIndependent ℝ (Fin.append P U) := by
  have hc := h.comp (Fin.castAdd k) (Fin.castAdd_injective (2 + k) k)
  convert hc using 1
  funext i
  simp [Function.comp, Fin.append_left]

end Work.Drive.PushDisc

import Mathlib
import Submission.Work.Diff.EXT.covK_valueDep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- The point-level evaluation `Kpt` of the tower `∇^k Rm` (defined via the field-level iteration
`ckt` on chosen smooth extensions) agrees with the `(0,k+4)`-tensor `covKRm` on the corresponding
split tuple: the first `k` slots are the `k` differentiation directions and the last four are the
curvature slots.  Both are `ckt`/`covKRmExt` on the same tuple of smooth extensions, packaged
according to `Fin.castAdd` / `Fin.natAdd`. -/
theorem Kpt_eq_covKRm_packed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (g : Submission.Diff.SMet I M) (x : M) (k : ℕ) (w : Fin (k + 4) → TangentSpace I x) :
    Work.Diff.EXT.Kpt g x k w
      = Work.Diff.EXT.covKRm g x k (fun r : Fin k => w (Fin.castAdd 4 r))
          (w (Fin.natAdd k 0)) (w (Fin.natAdd k 1)) (w (Fin.natAdd k 2)) (w (Fin.natAdd k 3)) := by
  rw [Kpt, covKRm, ckt_eq_covKRmExt]

end Work.Diff.EXT

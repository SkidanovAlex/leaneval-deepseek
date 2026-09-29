import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.axisScatterGetD
import Submission.Work.SynFFT.scatterCvecs

/-!
# `axisScatInDisc`: the scattered array of in-disc vectors is in-disc

The axis-by-axis synthetic FFT keeps its data as a list `W` of coefficient vectors (one per
array entry), and the scatter stage reads every entry of `W` at the *scattered* index

`i ↦ (i / (t * B) * B + i % B) * t + i / B % t`,  `i < A * t * B`

(see `Work.SynFFT.scatterCvecs`).  This file records the elementary datum that the scatter
preserves the pointwise predicate `InDiscVec p r`: it is a `List.range`-map of `W.getD` at
those scattered indices, and each scattered index is again in range
(`Work.SynFFT.scatterIdx_lt`), so each element produced is literally an element of `W`.
-/

set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

theorem axisScatInDisc (p r A t B : ℕ) (W : List (List (ℤ × ℤ))) (h : W.length = A * B * t)
    (hd : ∀ w ∈ W, HvdH.InDiscVec p r w) :
    ∀ w ∈ (List.range (A * t * B)).map
        (fun i => W.getD ((i / (t * B) * B + i % B) * t + i / B % t) []),
      HvdH.InDiscVec p r w := by
  intro w hw
  rw [List.mem_map] at hw
  obtain ⟨i, hi, rfl⟩ := hw
  rw [List.mem_range] at hi
  have hidx : ((i / (t * B) * B + i % B) * t + i / B % t) < W.length := by
    rw [h]
    exact Work.SynFFT.scatterIdx_lt A t B i hi
  rw [List.getD_eq_getElem _ ([] : List (ℤ × ℤ)) hidx]
  exact hd _ (List.getElem_mem hidx)

end Work.SynFFT

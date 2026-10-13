import Mathlib
import Submission.Work.WilG4c.AlSliceBase

namespace Work.WilG4c

theorem WordCountsLe {n m : ℕ} (v : Fin m → Fin (n + 1)) (i : Fin (n + 1)) :
    Work.WilkG4c.wordCounts v i ≤ m := by
  -- `wordCounts v i` counts the letter `i` among the `m` letters of the word `v`,
  -- so it is the cardinality of a subset of `Fin m`.
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun j : Fin m => v j = i)
  simpa [Work.WilkG4c.wordCounts] using h

end Work.WilG4c

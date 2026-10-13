import Mathlib
import Submission.Work.WilG4c.AlSliceBase

namespace Work.WilG4c

theorem SumWordCounts {n m : ℕ} (v : Fin m → Fin (n + 1)) :
    ∑ i : Fin (n + 1), Work.WilkG4c.wordCounts v i = m := by
  have h : ∑ j : Fin (n + 1), (Finset.univ.filter (fun i : Fin m => v i = j)).card = m := by
    have h0 := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin m))
      (Finset.univ : Finset (Fin (n + 1))) v
    simpa using h0
  simpa only [Work.WilkG4c.wordCounts] using h

end Work.WilG4c

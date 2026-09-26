import Mathlib
import Submission.Work.PTCert.ldlAux

namespace Work.PTCert.ldlAux

open Submission.PTCert

theorem foldStep_range_some (g : ℕ → List (List ℤ) → Option (List (List ℤ)))
    (accs0 : List (List ℤ)) (n : ℕ) {Z : List (List ℤ)}
    (h : Submission.PTCert.foldStep g (List.range n) accs0 = some Z) :
    ∀ i ≤ n, ∃ Y, Submission.PTCert.foldStep g (List.range i) accs0 = some Y := by
  intro i hi
  obtain ⟨rest, hrest⟩ : ∃ rest, List.range n = List.range i ++ rest :=
    ⟨_, range_take_append n i hi⟩
  rw [hrest, foldStep_append] at h
  exact exists_of_bind_eq_some h

end Work.PTCert.ldlAux

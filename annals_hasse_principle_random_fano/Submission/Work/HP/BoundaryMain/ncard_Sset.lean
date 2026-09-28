import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.SlabMono

/-!
# Cardinality of the special monomial set `Sset d n hd j`

`Sset d n hd j` is the range of the injection `i ↦ smon d n hd j i` out of `Fin (n+1)`, so it
has exactly `n + 1` elements; its complement in the `N_{d,n}`-element set `Mon d n` therefore
has `NN d n - (n+1)` elements.
-/

namespace Work.HP.BoundaryMain

open Work.HP

theorem ncard_Sset (d n : ℕ) (hd : 1 ≤ d) (j : Fin (n + 1)) :
    (Work.HP.Sset d n hd j).ncard = n + 1 ∧
      (Work.HP.Sset d n hd j)ᶜ.ncard = Work.HP.NN d n - (n + 1) := by
  have hS : (Sset d n hd j).ncard = n + 1 := by
    rw [Sset, Set.ncard_range_of_injective (smon_injective d n hd j)]
    exact Nat.card_fin (n + 1)
  refine ⟨hS, ?_⟩
  rw [Set.ncard_compl (Sset d n hd j), hS, Nat.card_eq_fintype_card]

end Work.HP.BoundaryMain

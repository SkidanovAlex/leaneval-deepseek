import Mathlib
import Submission.Work.Peluse.UControl.peluseFamily

/-!
# The cardinality of Peluse's index sets

`D.I j` is the type of *nonempty* subsets of the level-`j` slots `D.S j`; its cardinality is
`2 ^ |S j| - 1`.  This is the arithmetic behind the parity of `|I (l-1)|` used in the corner
argument for `PetChapter5` (`|I (l-1)| = 2^k - 1` is odd, so the "balanced" Boolean family
`b : Fin |I (l-1)| → Bool` of `linFamAvg_zero_term` exists).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

theorem card_I (D : IdxDatum) (j : ℕ) :
    Fintype.card (D.I j) = 2 ^ (Fintype.card (D.S j)) - 1 := by
  classical
  have hcard : Fintype.card {T : Finset (D.S j) // T.Nonempty}
      = 2 ^ Fintype.card (D.S j) - 1 := by
    rw [Fintype.card_subtype]
    have h : (Finset.univ.filter (fun T : Finset (D.S j) => T.Nonempty))
        = (Finset.univ : Finset (Finset (D.S j))).erase ∅ := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · intro hT
        exact ⟨fun h0 => (Finset.not_nonempty_iff_eq_empty.mpr h0) hT, trivial⟩
      · intro hT
        exact Finset.nonempty_iff_ne_empty.mpr hT.1
    rw [h, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_finset]
  exact hcard

end Work.Peluse.UControl

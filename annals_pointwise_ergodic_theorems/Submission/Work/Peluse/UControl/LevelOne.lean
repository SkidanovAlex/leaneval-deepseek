import Mathlib
import Submission.Work.Peluse.UControl.pelusePetChapterDefs

/-!
# The level-one datum attached to a terminal history state

The terminal state of the first phase of the PET chain (`Phase1Terminal d n lc X`) has live slots
`(P, h)` with `h : Fin n → Bool`, `h ≠ 0`, all of shift degree `d - 1` and leading coefficient
`C (d * lc) * shift h`.  Its slots are therefore in bijection with the *nonempty subsets* of
`Fin n`, i.e. with the level-`1` index set of the nested PET datum.

This file fixes that datum: `levelOneDatum n` has `S 0 = PUnit`, `S 1 = Fin n` (the `n` window
coordinates of the chain), all other slot types empty, and the attachment `par 0` the constant map
onto the full set.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

/-- The slot type of the level-one datum: a point at level `0`, `Fin n` at level `1`, and nothing
above. -/
def levelOneS (n : ℕ) : ℕ → Type
  | 0 => PUnit
  | 1 => Fin n
  | _ => PEmpty

instance levelOneS.instFintype (n j : ℕ) : Fintype (levelOneS n j) := by
  unfold levelOneS
  split <;> infer_instance

instance levelOneS.instDecidableEq (n j : ℕ) : DecidableEq (levelOneS n j) := by
  unfold levelOneS
  split <;> infer_instance

/-- **The level-one PET datum.** -/
def levelOneDatum (n : ℕ) : IdxDatum where
  S := levelOneS n
  finS := fun j => levelOneS.instFintype n j
  decS := fun j => levelOneS.instDecidableEq n j
  par := fun j => by
    rcases j with _ | j
    · exact fun _ => ⟨Finset.univ, ⟨PUnit.unit, Finset.mem_univ _⟩⟩
    · rcases j with _ | j
      · exact fun s => nomatch s
      · exact fun s => nomatch s

@[simp] lemma levelOneDatum_S_zero (n : ℕ) : (levelOneDatum n).S 0 = PUnit := rfl
@[simp] lemma levelOneDatum_S_one (n : ℕ) : (levelOneDatum n).S 1 = Fin n := rfl

/-- The level-`1` index set of the level-one datum is the type of nonempty subsets of `Fin n`. -/
lemma levelOneDatum_I_one (n : ℕ) :
    (levelOneDatum n).I 1 = {T : Finset (Fin n) // T.Nonempty} := rfl

/-- The cardinality of the type of nonempty subsets of `Fin n`. -/
lemma card_nonemptyFinset_fin (n : ℕ) :
    Fintype.card {T : Finset (Fin n) // T.Nonempty} = 2 ^ n - 1 := by
  classical
  have hfilter : Finset.univ.filter (fun T : Finset (Fin n) => T.Nonempty)
      = (Finset.univ : Finset (Finset (Fin n))).erase ∅ := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro hne
      exact ⟨Finset.nonempty_iff_ne_empty.mp hne, trivial⟩
    · rintro ⟨hne, -⟩
      exact Finset.nonempty_iff_ne_empty.mpr hne
  rw [Fintype.card_subtype, hfilter,
    Finset.card_erase_of_mem (Finset.mem_univ (∅ : Finset (Fin n))),
    Finset.card_univ, Fintype.card_finset, Fintype.card_fin]

/-- The cardinality of the level-`1` index set of the level-one datum. -/
lemma levelOneDatum_card_I_one (n : ℕ) :
    Fintype.card ((levelOneDatum n).I 1) = 2 ^ n - 1 := by
  rw [show Fintype.card ((levelOneDatum n).I 1)
      = Fintype.card {T : Finset (Fin n) // T.Nonempty} from rfl]
  exact card_nonemptyFinset_fin n

end

end Work.Peluse.UControl

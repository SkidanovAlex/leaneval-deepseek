import Mathlib
import Submission.Work.WilCrux.SheetDefs

namespace Work.WilCrux

/-!
# A `LexLt`-maximal word in a finite nonempty family of cells

`LexLt` (band `>` graph, compared from the bottom level up) is a strict total order on type
words (`LexLt.irrefl`, `LexLt.trans`, `LexLt.trichotomy` in `WilCrux/SheetDefs`).  Hence every
nonempty finite set of words has a `LexLt`-maximal element; transporting along
`w ↦ word m N w` gives the maximal element of a nonempty finite family of cells, which is the
node-N1 choice of the crux argument (`WilCrux/DESIGN.md`).
-/

/-- Every nonempty finite set of type words has an element that is not `LexLt`-below any other
element. -/
theorem exists_max_word_of_finset {N : ℕ} (s : Finset (Fin N → CellType)) (hne : s.Nonempty) :
    ∃ w ∈ s, ∀ w' ∈ s, ¬ LexLt w w' := by
  classical
  revert hne
  induction s using Finset.induction_on with
  | empty => intro h; exact absurd h Finset.not_nonempty_empty
  | insert a s ha ih =>
    intro hne
    by_cases hs : s.Nonempty
    · obtain ⟨w, hw, hwmax⟩ := ih hs
      rcases LexLt.trichotomy w a with h | h | h
      · -- `a` lies above `w`, and `w` is above all of `s`: take `a`.
        refine ⟨a, Finset.mem_insert_self a s, fun w' hw' => ?_⟩
        rcases Finset.mem_insert.mp hw' with hwa | hw's
        · rw [hwa]; exact LexLt.irrefl a
        · intro hlt
          exact hwmax w' hw's (LexLt.trans h hlt)
      · -- `w = a`: take `w`.
        refine ⟨w, Finset.mem_insert.mpr (Or.inr hw), fun w' hw' => ?_⟩
        rcases Finset.mem_insert.mp hw' with hwa | hw's
        · rw [hwa, h]; exact LexLt.irrefl a
        · exact hwmax w' hw's
      · -- `a` lies below `w`: keep `w`.
        refine ⟨w, Finset.mem_insert.mpr (Or.inr hw), fun w' hw' => ?_⟩
        rcases Finset.mem_insert.mp hw' with hwa | hw's
        · rw [hwa]
          intro hc
          exact LexLt.irrefl w (LexLt.trans hc h)
        · exact hwmax w' hw's
    · -- `s` is empty: take `a`.
      have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst hs'
      refine ⟨a, Finset.mem_insert_self a ∅, fun w' hw' => ?_⟩
      rcases Finset.mem_insert.mp hw' with hwa | hw'
      · rw [hwa]; exact LexLt.irrefl a
      · exact absurd hw' (by simp)

theorem exists_max_word {m N : ℕ} {K : Finset (Set (Fin (m + N) → ℝ))} (hKne : K.Nonempty) :
    ∃ κ ∈ K, ∀ κ' ∈ K, ¬ Work.WilCrux.LexLt (Work.WilCrux.word m N κ)
      (Work.WilCrux.word m N κ') := by
  classical
  obtain ⟨w, hwS, hwmax⟩ :=
    exists_max_word_of_finset (K.image (word m N)) (hKne.image (word m N))
  obtain ⟨κ, hκK, hκw⟩ := Finset.mem_image.mp hwS
  refine ⟨κ, hκK, fun κ' hκ' => ?_⟩
  rw [hκw]
  exact hwmax (word m N κ') (Finset.mem_image.mpr ⟨κ', hκ', rfl⟩)

end Work.WilCrux

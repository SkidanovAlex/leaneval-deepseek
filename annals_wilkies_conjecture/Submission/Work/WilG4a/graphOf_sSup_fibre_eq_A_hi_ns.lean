import Mathlib
import Submission.Work.WilG4a.NoStripDefs

namespace Work.WilG4a

/-- Order-theoretic characterisation of `y = sSup S` for an *arbitrary* set `S ⊆ ℝ`,
accounting for the junk value `sSup S = 0` when `S` is empty or not bounded above.

The right-hand side is the union of the two familiar cases:
* `S` nonempty and bounded above, and `y` is its least upper bound (`A ∧ B`, which
  already forces `S.Nonempty` and `BddAbove S`);
* `S` empty or unbounded above, in which case `sSup S = 0` and the value is the junk
  value `0` (`C ∧ y = 0`). -/
private lemma eq_sSup_iff_junk (S : Set ℝ) (y : ℝ) :
    y = sSup S ↔
      ((∀ t ∈ S, t ≤ y) ∧ (∀ u : ℝ, u < y → ∃ t ∈ S, u < t)) ∨
      ((¬ S.Nonempty ∨ ∀ v : ℝ, ∃ t ∈ S, v < t) ∧ y = 0) := by
  constructor
  · intro h
    by_cases hne : S.Nonempty
    · by_cases hbdd : BddAbove S
      · left
        exact (eq_sSup_iff S hne hbdd y).mpr h
      · right
        refine ⟨Or.inr ?_, h.trans (Real.sSup_of_not_bddAbove hbdd)⟩
        intro v
        obtain ⟨t, ht, hvt⟩ := not_bddAbove_iff.mp hbdd v
        exact ⟨t, ht, hvt⟩
    · right
      refine ⟨Or.inl hne, h.trans ?_⟩
      rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
  · rintro (⟨hA, hB⟩ | ⟨hC, hy0⟩)
    · have hbdd : BddAbove S := by
        rw [bddAbove_def]; exact ⟨y, hA⟩
      have hne : S.Nonempty := by
        obtain ⟨t, ht, _⟩ := hB (y - 1) (by linarith)
        exact ⟨t, ht⟩
      exact (eq_sSup_iff S hne hbdd y).mp ⟨hA, hB⟩
    · have hsSup : sSup S = 0 := by
        rcases hC with hne | hbdd
        · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
        · exact Real.sSup_of_not_bddAbove (not_bddAbove_iff.mpr hbdd)
      rw [hy0, hsSup]

theorem graphOf_sSup_fibre_eq_A_hi_ns (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) :
    WilkiesDesign.graphOf (fun l : Fin p → ℝ => sSup {x : ℝ | Fin.snoc l x ∈ Z}) =
      Work.WilG4a.A_hi_ns p Z := by
  ext z
  rw [WilkiesDesign.graphOf, Set.mem_ofPred_eq, mem_A_hi_ns]
  exact eq_sSup_iff_junk {x : ℝ | Fin.snoc (Fin.init z) x ∈ Z} (z (Fin.last p))

end Work.WilG4a

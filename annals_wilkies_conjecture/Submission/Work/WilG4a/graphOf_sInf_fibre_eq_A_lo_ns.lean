import Mathlib
import Submission.Work.WilG4a.NoStripDefs

namespace Work.WilG4a

open WilkiesDesign

/-- A fibre is unbounded below iff it contains elements below any prescribed real
(the fibre form of `not_bddBelow_iff`). -/
theorem not_bddBelow_fibre_iff (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) :
    ¬ BddBelow {x : ℝ | Fin.snoc l x ∈ Z} ↔
      ∀ y : ℝ, ∃ x : ℝ, Fin.snoc l x ∈ Z ∧ x < y := by
  rw [not_bddBelow_iff]
  constructor
  · intro h y
    obtain ⟨x, hx, hxy⟩ := h y
    exact ⟨x, hx, hxy⟩
  · intro h y
    obtain ⟨x, hx, hxy⟩ := h y
    exact ⟨x, hx, hxy⟩

/-- The `sInf` of a fibre `S = {x | (l,x) ∈ Z}`, with no hypothesis on `S`.  Either the
fibre is nonempty and bounded below and `y` is its greatest lower bound, or the fibre is
empty / unbounded below (`unbBelow1`) and `y = 0`, which is exactly the junk value that
`sInf` assigns in those two cases (`Real.sInf_empty`, `Real.sInf_of_not_bddBelow`). -/
theorem eq_sInf_fibre_iff (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ) (y : ℝ) :
    y = sInf {x : ℝ | Fin.snoc l x ∈ Z} ↔
      (((∀ x : ℝ, Fin.snoc l x ∈ Z → y ≤ x) ∧
          (∀ u : ℝ, y < u → ∃ x : ℝ, Fin.snoc l x ∈ Z ∧ x < u))
        ∨ ((¬ (∃ x : ℝ, Fin.snoc l x ∈ Z) ∨
              (∀ y' : ℝ, ∃ x : ℝ, Fin.snoc l x ∈ Z ∧ x < y')) ∧
            y = 0)) := by
  by_cases hne : ∃ x : ℝ, Fin.snoc l x ∈ Z
  · -- the fibre is nonempty
    by_cases hbd : BddBelow {x : ℝ | Fin.snoc l x ∈ Z}
    · -- nonempty and bounded below: `y` is the greatest lower bound
      have hne' : ({x : ℝ | Fin.snoc l x ∈ Z} : Set ℝ).Nonempty :=
        ⟨hne.choose, hne.choose_spec⟩
      constructor
      · intro h
        left
        exact (eq_sInf_iff _ hne' hbd y).mpr h
      · rintro (h | h)
        · exact (eq_sInf_iff _ hne' hbd y).mp h
        · rcases h.1 with hnn | hnb
          · exact absurd hne' hnn
          · exact absurd hbd ((not_bddBelow_fibre_iff p Z l).mpr hnb)
    · -- nonempty and unbounded below: the junk value is `sInf S = 0`
      rw [Real.sInf_of_not_bddBelow hbd]
      constructor
      · intro h
        right
        exact ⟨Or.inr ((not_bddBelow_fibre_iff p Z l).mp hbd), h⟩
      · rintro (⟨hA, -⟩ | ⟨-, h0⟩)
        · exact absurd ⟨y, hA⟩ hbd
        · exact h0
  · -- the fibre is empty: `sInf ∅ = 0`
    have hSeq : {x : ℝ | Fin.snoc l x ∈ Z} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      exact hne ⟨x, hx⟩
    rw [hSeq, Real.sInf_empty]
    constructor
    · intro h
      right
      exact ⟨Or.inl hne, h⟩
    · rintro (⟨-, h2⟩ | ⟨-, h0⟩)
      · obtain ⟨x, hx, -⟩ := h2 (y + 1) (lt_add_one y)
        exact absurd ⟨x, hx⟩ hne
      · exact h0

theorem graphOf_sInf_fibre_eq_A_lo_ns (p : ℕ) (Z : Set (Fin (p + 1) → ℝ)) :
    WilkiesDesign.graphOf (fun l : Fin p → ℝ => sInf {x : ℝ | Fin.snoc l x ∈ Z}) =
      Work.WilG4a.A_lo_ns p Z := by
  ext z
  rw [WilkiesDesign.graphOf, Set.mem_ofPred_eq, mem_A_lo_ns]
  exact eq_sInf_fibre_iff p Z (Fin.init z) (z (Fin.last p))

end Work.WilG4a

import Mathlib
import Submission.Work.WilE7.DimOneCells

namespace Work.WilE7.CylAux

/-- If two intervals `(a,b)` and `(c,d)` cut out by consecutive points of a finite set `U ⊆ ℝ`
meet, then they are equal.  Concretely: `a, b ∈ U` with no element of `U` strictly between them,
`c, d ∈ U` with no element of `U` strictly between them, and `(a,b) ∩ (c,d) ≠ ∅` force
`(a,b) = (c,d)`.

This is the uniqueness half of the statement that the cuts `cuts U` cut the line into the cells
indexed by consecutive pairs. -/
theorem cellIoo_eq_of_inter_nonempty {U : Finset ℝ} {a b c d : ℝ}
    (ha : a ∈ U) (hb : b ∈ U) (hnb : ∀ u ∈ U, ¬ (a < u ∧ u < b))
    (hc : c ∈ U) (hd : d ∈ U) (hnd : ∀ u ∈ U, ¬ (c < u ∧ u < d))
    (h : (Work.WilE7.cellIoo a b ∩ Work.WilE7.cellIoo c d).Nonempty) : (a, b) = (c, d) := by
  obtain ⟨x, hx⟩ := h
  rw [Set.mem_inter_iff, Work.WilE7.mem_cellIoo, Work.WilE7.mem_cellIoo] at hx
  obtain ⟨⟨hax, hxb⟩, hcx, hxd⟩ := hx
  -- a point of the intersection is strictly inside both intervals, so `a = c`
  have hac : a = c := by
    rcases lt_trichotomy a c with hlt | heq | hgt
    · exact absurd ⟨hlt, lt_trans hcx hxb⟩ (hnb c hc)
    · exact heq
    · exact absurd ⟨hgt, lt_trans hax hxd⟩ (hnd a ha)
  -- and then `b = d`
  have hbd : b = d := by
    rcases lt_trichotomy b d with hlt | heq | hgt
    · exact absurd ⟨hac ▸ lt_trans hax hxb, hlt⟩ (hnd b hb)
    · exact heq
    · exact absurd ⟨lt_trans hax hxd, hgt⟩ (hnb d hd)
  rw [hac, hbd]

end Work.WilE7.CylAux

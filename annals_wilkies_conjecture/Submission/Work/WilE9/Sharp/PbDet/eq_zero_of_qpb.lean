import Mathlib
import Submission.Work.WilE9.Sharp.PbDetDefs

namespace Work.WilE9.Sharp.PbDet

/-- The fibre indices `fS`, `fY i`, `fW i`, `fT`, `fU`, `fA b` exhaust `Fin (qpb n m)`:
`qpb n m = 2 * n + m + 3` and the six families of coordinates occupy exactly the blocks
`{0}`, `{1, …, n}`, `{n + 1, …, 2 * n}`, `{2 * n + 1}`, `{2 * n + 2}`, `{2 * n + 3, …, qpb - 1}`.
Hence a vector vanishing on all of them is zero. -/
theorem eq_zero_of_qpb {n m : ℕ} (v : Fin (Work.WilE9.Sharp.qpb n m) → ℝ)
    (h0 : v (Work.WilE9.Sharp.fS n m) = 0)
    (h1 : ∀ i : Fin n, v (Work.WilE9.Sharp.fY n m i) = 0)
    (h2 : ∀ i : Fin n, v (Work.WilE9.Sharp.fW n m i) = 0)
    (h3 : v (Work.WilE9.Sharp.fT n m) = 0)
    (h4 : v (Work.WilE9.Sharp.fU n m) = 0)
    (h5 : ∀ b : Fin m, v (Work.WilE9.Sharp.fA n m b) = 0) : v = 0 := by
  funext j
  have hj : (j : ℕ) < 2 * n + m + 3 := by
    have := j.isLt
    simp only [Work.WilE9.Sharp.qpb] at this
    exact this
  rcases lt_or_ge (j : ℕ) (n + 1) with h | h
  · rcases eq_or_lt_of_le (Nat.zero_le (j : ℕ)) with hz | hpos
    · have : j = Work.WilE9.Sharp.fS n m := by
        ext
        simp only [Work.WilE9.Sharp.fS]
        omega
      rw [this]
      exact h0
    · have : j = Work.WilE9.Sharp.fY n m ⟨(j : ℕ) - 1, by omega⟩ := by
        ext
        simp only [Work.WilE9.Sharp.fY, Fin.val_mk]
        omega
      rw [this]
      exact h1 _
  · rcases lt_or_ge (j : ℕ) (2 * n + 1) with h' | h'
    · have : j = Work.WilE9.Sharp.fW n m ⟨(j : ℕ) - (n + 1), by omega⟩ := by
        ext
        simp only [Work.WilE9.Sharp.fW, Fin.val_mk]
        omega
      rw [this]
      exact h2 _
    · rcases lt_or_ge (j : ℕ) (2 * n + 2) with h'' | h''
      · have : j = Work.WilE9.Sharp.fT n m := by
          ext
          simp only [Work.WilE9.Sharp.fT, Fin.val_mk]
          omega
        rw [this]
        exact h3
      · rcases lt_or_ge (j : ℕ) (2 * n + 3) with h''' | h'''
        · have : j = Work.WilE9.Sharp.fU n m := by
            ext
            simp only [Work.WilE9.Sharp.fU]
            omega
          rw [this]
          exact h4
        · have : j = Work.WilE9.Sharp.fA n m ⟨(j : ℕ) - (2 * n + 3), by omega⟩ := by
            ext
            simp only [Work.WilE9.Sharp.fA, Fin.val_mk]
            omega
          rw [this]
          exact h5 _

end Work.WilE9.Sharp.PbDet

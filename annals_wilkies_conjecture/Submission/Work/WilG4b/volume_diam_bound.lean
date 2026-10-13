import Mathlib

namespace Work.WilG4b

/-- The requested bound.  The hypothesis says every ordered pair of points of `C`
is at distance at most `M`; hence `C` is contained in an interval of length `2 * M`. -/
lemma volume_diam_bound {M : ℝ} (hM : 0 ≤ M) {C : Set ℝ}
    (hdiam : ∀ u ∈ C, ∀ v ∈ C, u < v → v - u ≤ M) :
    MeasureTheory.volume C ≤ ENNReal.ofReal (2 * M) := by
  rcases C.eq_empty_or_nonempty with h | ⟨p, hp⟩
  · subst h
    simp
  · have hsub : C ⊆ Set.Icc (p - M) (p + M) := by
      intro x hx
      rw [Set.mem_Icc]
      rcases lt_trichotomy x p with hlt | heq | hgt
      · have h1 : p - x ≤ M := hdiam x hx p hp hlt
        constructor <;> linarith
      · rw [heq]
        constructor <;> linarith
      · have h1 : x - p ≤ M := hdiam p hp x hx hgt
        constructor <;> linarith
    calc MeasureTheory.volume C
        ≤ MeasureTheory.volume (Set.Icc (p - M) (p + M)) :=
          MeasureTheory.measure_mono hsub
      _ = ENNReal.ofReal ((p + M) - (p - M)) := Real.volume_Icc
      _ = ENNReal.ofReal (2 * M) := by ring_nf

end Work.WilG4b

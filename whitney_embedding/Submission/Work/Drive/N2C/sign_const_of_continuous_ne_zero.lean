import Mathlib

/-!
# A continuous real function that never vanishes has constant sign

On the connected space `ℝ`, a continuous map into `ℝ \ {0}` lands in one of the two
connected components, i.e. its sign is constant.  This is the elementary input used
whenever a continuous "height"/"coordinate" function is shown to avoid `0` and one
needs to know that the set `{u > 0}` is either everything or nothing.

The proof is the intermediate value theorem on `ℝ` (`intermediate_value_univ`): if
`u a < 0 < u b` for some `a b`, then `0 ∈ Icc (u a) (u b) ⊆ range u`, contradicting
`∀ x, u x ≠ 0`.
-/

namespace Work.Drive.N2C

theorem sign_const_of_continuous_ne_zero {u : ℝ → ℝ} (hu : Continuous u) (h : ∀ x, u x ≠ 0) : (∀ x, 0 < u x) ∨ (∀ x, u x < 0) := by
  by_cases hpos : ∀ x, 0 < u x
  · exact Or.inl hpos
  · right
    rw [not_forall] at hpos
    obtain ⟨a, ha⟩ := hpos
    simp only [not_lt] at ha
    have ha' : u a < 0 := lt_of_le_of_ne ha (h a)
    intro b
    by_contra hb
    rw [not_lt] at hb
    have hb' : 0 < u b := lt_of_le_of_ne hb (Ne.symm (h b))
    have hmem : (0 : ℝ) ∈ Set.Icc (u a) (u b) := ⟨le_of_lt ha', le_of_lt hb'⟩
    obtain ⟨c, hc⟩ := intermediate_value_univ a b hu hmem
    exact h c hc

end Work.Drive.N2C

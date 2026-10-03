import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour

/-!
# Vocabulary for the ray/cycle crossing parity

`rayMeet` is the set of parameters at which the ray from `a` in the direction `1 + iε` meets the
closed polygonal curve `cycleSet k u`, and `lvl` is the level set of an argument function.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

/-- The parameters at which the ray from `a` in direction `1 + iε` meets the polygonal cycle. -/
def rayMeet (k : ℕ) (u : ℕ → ℤ × ℤ) (a : ℂ) (ε : ℝ) : Set ℝ :=
  {t : ℝ | 0 < t ∧ a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ∈ cycleSet k u}

/-- The set of parameters where an argument function attains a multiple of `2π`. -/
def lvlSet (Θ : ℝ → ℝ) : Set ℝ := {t : ℝ | ∃ n : ℤ, Θ t = (n : ℝ) * (2 * Real.pi)}

/-- The level set intersected with `[0,1)`. -/
def lvlSetIco (Θ : ℝ → ℝ) : Set ℝ := {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ n : ℤ,
  Θ t = (n : ℝ) * (2 * Real.pi)}

lemma mem_rayMeet {k : ℕ} {u : ℕ → ℤ × ℤ} {a : ℂ} {ε t : ℝ} :
    t ∈ rayMeet k u a ε ↔ 0 < t ∧ a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ∈ cycleSet k u := Iff.rfl

lemma mem_lvlSetIco {Θ : ℝ → ℝ} {t : ℝ} :
    t ∈ lvlSetIco Θ ↔ t ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ n : ℤ, Θ t = (n : ℝ) * (2 * Real.pi) :=
  Iff.rfl

end Work.HornSC.CellBoundaryJordan

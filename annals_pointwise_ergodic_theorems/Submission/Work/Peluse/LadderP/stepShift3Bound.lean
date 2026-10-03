import Mathlib
import Submission.Work.Peluse.LadderP.stepPState

/-!
# The size bound for the ladder-step shift `stepShift3`

The shift `stepShift3 h₁ h₁' h'_s ω = -(h'_s) - 1 + ω · (h₁ - h₁')` attached to the pattern `ω` is
built from the coordinates of the two shift tuples `h₁, h₁' ∈ [1,M₁]^j` and the averaged parameter
`h'_s ∈ [1,M₁]`.  Each coordinate of the difference tuple lies in `[-(M₁-1), M₁-1]`, and `ω` selects
a sub-sum of the coordinates, so `|ω · (h₁ - h₁')| ≤ j·M₁`; adding `|-(h'_s) - 1| ≤ M₁` gives the
stated bound `(j+1)·M₁`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderP

open Work.Peluse

/-- Each coordinate of the difference tuple `h - h'` of two tuples in `[1,M₁]^j` is bounded by `M₁`
in absolute value. -/
lemma abs_tupSub_le {j M₁ : ℕ} (h h' : Fin j → Fin M₁) :
    ∀ i : Fin j, |Concat.tupSub h h' i| ≤ (M₁ : ℤ) := by
  intro i
  have h1 : ((h i : ℕ) : ℤ) + 1 ≤ (M₁ : ℤ) := by
    have := (h i).isLt
    omega
  have h2 : ((h' i : ℕ) : ℤ) + 1 ≤ (M₁ : ℤ) := by
    have := (h' i).isLt
    omega
  have h3 : (0 : ℤ) ≤ ((h i : ℕ) : ℤ) + 1 := by omega
  have h4 : (0 : ℤ) ≤ ((h' i : ℕ) : ℤ) + 1 := by omega
  rw [Concat.tupSub]
  rw [abs_le]
  constructor <;> omega

/-- The integer `ω · u` of a direction tuple with coordinates bounded by `M₁` is bounded by `j·M₁`
in absolute value. -/
lemma abs_dotZ_le {j M₁ : ℕ} (ω : Fin j → Bool) (u : Fin j → ℤ)
    (hu : ∀ i : Fin j, |u i| ≤ (M₁ : ℤ)) :
    |Concat.dotZ ω u| ≤ (j : ℤ) * (M₁ : ℤ) := by
  rw [Concat.dotZ]
  calc |∑ i : Fin j, (if ω i then u i else 0)|
      ≤ ∑ i : Fin j, |(if ω i then u i else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin j, (M₁ : ℤ) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : ω i
        · simp [h]; exact hu i
        · simp [h]
    _ = (j : ℤ) * M₁ := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

theorem stepShift3Bound (j M₁ : ℕ) (hM₁ : 1 ≤ M₁) (h₁ h₁' : Fin j → Fin M₁) (h'_s : Fin M₁)
    (ω : Fin j → Bool) :
    |(Work.Peluse.LadderP.stepShift3 h₁ h₁' h'_s ω : ℤ)| ≤ ((j + 1 : ℕ) : ℤ) * (M₁ : ℤ) := by
  have hdot : |Concat.dotZ ω (Concat.tupSub h₁ h₁')| ≤ (j : ℤ) * (M₁ : ℤ) :=
    abs_dotZ_le ω _ (abs_tupSub_le h₁ h₁')
  have hhead : |(-(h'_s : ℤ) - 1)| ≤ (M₁ : ℤ) := by
    have hM₁z : (1 : ℤ) ≤ (M₁ : ℤ) := by exact_mod_cast hM₁
    have := h'_s.isLt
    rw [abs_le]
    constructor <;> omega
  rw [stepShift3]
  calc |(-(h'_s : ℤ) - 1) + Concat.dotZ ω (Concat.tupSub h₁ h₁')|
      ≤ |(-(h'_s : ℤ) - 1)| + |Concat.dotZ ω (Concat.tupSub h₁ h₁')| := abs_add_le _ _
    _ ≤ (M₁ : ℤ) + (j : ℤ) * M₁ := add_le_add hhead hdot
    _ = ((j + 1 : ℕ) : ℤ) * (M₁ : ℤ) := by push_cast; ring

end Work.Peluse.LadderP

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Removing the point `0` from an upward-closed set `S` that either is all of `ℝ`
or consists of nonnegative reals does not change the infimum: the point `0`, if it
lies in `S`, is never the unique source of an infimum strictly below the infimum of
`S \ {0}` because upward-closure forces `(0, ∞) ⊆ S` whenever `0 ∈ S`. -/
theorem basisRed_sInf_posPart {S : Set ℝ}
    (hup : ∀ ⦃s t : ℝ⦄, s ∈ S → s ≤ t → t ∈ S)
    (hpos : S = Set.univ ∨ S ⊆ Set.Ici 0) :
    sInf S = sInf (S ∩ Set.Ioi 0) := by
  rcases hpos with h | h
  · rw [h]; simp
  · by_cases h0 : (0:ℝ) ∈ S
    · -- `0 ∈ S`: upward-closure gives `(0, ∞) ⊆ S`, so both infima are `0`.
      have hIoi : Set.Ioi (0:ℝ) ⊆ S := fun x hx => hup h0 (le_of_lt hx)
      have hT : S ∩ Set.Ioi 0 = Set.Ioi 0 := Set.inter_eq_right.mpr hIoi
      have hbdd : BddBelow S := ⟨0, fun y hy => h hy⟩
      have h1 : sInf S ≤ sInf (Set.Ioi (0:ℝ)) := csInf_le_csInf hbdd ⟨1, by norm_num⟩ hIoi
      have h2 : (0:ℝ) ≤ sInf S := le_csInf ⟨0, h0⟩ (fun b hb => h hb)
      have h3 : sInf (Set.Ioi (0:ℝ)) = 0 := by simp
      rw [hT]; linarith
    · -- `0 ∉ S` with `S ⊆ [0, ∞)` forces `S ⊆ (0, ∞)`, hence `S ∩ (0, ∞) = S`.
      have hsub : S ⊆ Set.Ioi (0:ℝ) := by
        intro x hx
        exact lt_of_le_of_ne (h hx) (fun heq : (0:ℝ) = x => h0 (heq.symm ▸ hx))
      have : S ∩ Set.Ioi (0:ℝ) = S := Set.inter_eq_left.mpr hsub
      rw [this]

end Work.BW

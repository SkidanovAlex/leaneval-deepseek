import Mathlib.Analysis.Normed.Field.Basic

set_option linter.unnecessarySimpa false

namespace Commons.Analysis.Normed

/-- In a linear order, a finite set of strictly positive reals has a strictly
positive lower bound (its minimum, or any positive number if it is empty). -/
private lemma exists_pos_lower_bound (s : Finset ℝ) (hpos : ∀ r ∈ s, 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ s, δ ≤ r := by
  rcases Finset.eq_empty_or_nonempty s with rfl | hs
  · refine ⟨1, by norm_num, ?_⟩
    intro r hr
    exact False.elim (by simpa using hr)
  · refine ⟨s.min' hs, hpos (s.min' hs) (Finset.min'_mem s hs), ?_⟩
    intro r hr
    exact Finset.min'_le s r hr

/-- Any finite set of points of a normed field is separated: two distinct
points of the set are at distance at least some fixed positive real. -/
private lemma sep_finset {L : Type*} [NormedField L] (t : Finset L) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → δ ≤ ‖x - y‖ := by
  classical
  refine Finset.induction_on t ?empty ?insert
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx y hy hxy
    exact False.elim (by simpa using hx)
  · intro a s has ih
    rcases ih with ⟨δ₀, hδ₀pos, hδ₀⟩
    let m : Finset ℝ := s.image fun y => ‖a - y‖
    have hmpos : ∀ r ∈ m, 0 < r := by
      intro r hr
      rcases Finset.mem_image.mp hr with ⟨y, hy, rfl⟩
      exact norm_pos_iff.mpr (by
        rw [sub_ne_zero]
        intro h
        exact has (h ▸ hy))
    rcases exists_pos_lower_bound m hmpos with ⟨δ₁, hδ₁pos, hδ₁⟩
    let δ : ℝ := min δ₀ δ₁
    refine ⟨δ, lt_min hδ₀pos hδ₁pos, ?_⟩
    intro x hx y hy hxy
    by_cases hxa : x = a
    · subst x
      have hys : y ∈ s := by
        rcases Finset.mem_insert.mp hy with hyeq | hys
        · exact False.elim (hxy hyeq.symm)
        · exact hys
      have hmem : ‖a - y‖ ∈ m := Finset.mem_image.mpr ⟨y, hys, rfl⟩
      exact le_trans (min_le_right δ₀ δ₁) (hδ₁ ‖a - y‖ hmem)
    · have hxs : x ∈ s := by
        rcases Finset.mem_insert.mp hx with hxeq | hxs
        · exact False.elim (hxa hxeq)
        · exact hxs
      by_cases hya : y = a
      · subst y
        have hmem : ‖a - x‖ ∈ m := Finset.mem_image.mpr ⟨x, hxs, rfl⟩
        have hle : δ₁ ≤ ‖a - x‖ := hδ₁ ‖a - x‖ hmem
        have hsym : ‖a - x‖ = ‖x - a‖ := by
          rw [← norm_neg]
          congr 1
          abel
        exact le_trans (min_le_right δ₀ δ₁) (by simpa [hsym] using hle)
      · have hys : y ∈ s := by
          rcases Finset.mem_insert.mp hy with hyeq | hys
          · exact False.elim (hya hyeq)
          · exact hys
        exact le_trans (min_le_left δ₀ δ₁) (hδ₀ x hxs y hys hxy)

lemma exists_separation_of_finite {L : Type*} [NormedField L] (S : Set L) (hS : S.Finite) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃x : L⦄, x ∈ S → ∀ ⦃y : L⦄, y ∈ S → x ≠ y → δ ≤ ‖x - y‖ := by
  classical
  rcases sep_finset hS.toFinset with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro x hx y hy hxy
  rw [← hS.coe_toFinset] at hx hy
  exact hδ x (by simpa using hx) y (by simpa using hy) hxy

end Commons.Analysis.Normed
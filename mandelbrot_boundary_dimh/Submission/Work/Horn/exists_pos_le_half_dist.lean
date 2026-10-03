import Mathlib

namespace Work.Horn

/-- For a finite set of complex numbers there is a strictly positive "radius"
function which at every point of `S` is at most half the distance to every
other point of `S`.  Equivalently: finitely many points have a uniform positive
separation. -/
theorem exists_pos_le_half_dist (S : Finset ℂ) :
    ∃ m : ℂ → ℝ, (∀ x ∈ S, 0 < m x) ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → m x ≤ dist x y / 2 := by
  classical
  set T : Finset (ℂ × ℂ) := (S.product S).filter (fun p => p.1 ≠ p.2) with hTdef
  refine ⟨fun _ => if h : T.Nonempty then T.inf' h (fun p => dist p.1 p.2 / 2) else 1,
    ?_, ?_⟩
  · intro x _
    by_cases h : T.Nonempty
    · rw [dite_eq_left h, Finset.lt_inf'_iff h]
      rintro ⟨a, b⟩ hp
      have hne : a ≠ b := by
        have := hp; rw [hTdef] at this
        simpa using (Finset.mem_filter.mp this).2
      exact div_pos (dist_pos.mpr hne) two_pos
    · rw [dite_eq_right h]
      norm_num
  · intro x hx y hy hxy
    have hmem : (x, y) ∈ T := by
      rw [hTdef]
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩
    have hT : T.Nonempty := ⟨(x, y), hmem⟩
    rw [dite_eq_left hT]
    exact (Finset.inf'_le_iff hT).mpr ⟨(x, y), hmem, le_refl _⟩

end Work.Horn

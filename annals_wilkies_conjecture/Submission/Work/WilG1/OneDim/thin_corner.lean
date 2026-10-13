import Submission.Work.WilG1.OneDim.thin_ev

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG1.OneDim

open WilkiesDesign

/-! ## 9. The corner sets are countable -/

theorem cornerMax_countable (g : ℝ → ℝ) (q : ℝ) : (cornerMax g q).Countable := by
  have key : ∀ x ∈ cornerMax g q, ∃ p r : ℚ, (p:ℝ) < x ∧ x < (r:ℝ) ∧
      ∀ y : ℝ, (p:ℝ) < y → y < (r:ℝ) → y ≠ x → g y - q * y < g x - q * x := by
    intro x hx
    rw [cornerMax] at hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨⟨δ₁, hδ₁, h₁⟩, ⟨δ₂, hδ₂, h₂⟩⟩ := hx
    have hmin : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show x - min δ₁ δ₂ / 2 < x by linarith)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show x < x + min δ₁ δ₂ / 2 by linarith)
    refine ⟨p, r, hp2, hr1, fun y hy1 hy2 hyne => ?_⟩
    rcases lt_or_gt_of_ne hyne with hy_lt | hy_gt
    · have hmem : x - δ₂ < y := by
        have h2' : min δ₁ δ₂ / 2 < δ₂ := by
          have := min_le_right δ₁ δ₂; linarith
        linarith
      have hyx := h₂ y hmem hy_lt
      linarith
    · have hmem : y < x + δ₁ := by
        have h2' : min δ₁ δ₂ / 2 < δ₁ := by
          have := min_le_left δ₁ δ₂; linarith
        linarith
      have hyx := h₁ y hy_gt hmem
      linarith
  have hsub : ∀ z : ℚ × ℚ, ({x : ℝ | (z.1:ℝ) < x ∧ x < (z.2:ℝ) ∧
      ∀ y : ℝ, (z.1:ℝ) < y → y < (z.2:ℝ) → y ≠ x →
        g y - q * y < g x - q * x} : Set ℝ).Subsingleton := by
    rintro ⟨p, r⟩ x ⟨hx1, hx2, hx⟩ x' ⟨hx1', hx2', hx'⟩
    rcases lt_trichotomy x x' with hlt | heq | hgt
    · exfalso
      have h1 := hx x' hx1' hx2' (ne_of_gt hlt)
      have h2 := hx' x hx1 hx2 (ne_of_lt hlt)
      linarith
    · exact heq
    · exfalso
      have h1 := hx x' hx1' hx2' (ne_of_lt hgt)
      have h2 := hx' x hx1 hx2 (ne_of_gt hgt)
      linarith
  refine Set.Countable.mono ?_ (Set.countable_iUnion (fun z : ℚ × ℚ => (hsub z).countable))
  intro x hx
  obtain ⟨p, r, hp, hr, h⟩ := key x hx
  exact Set.mem_iUnion.mpr ⟨(p, r), hp, hr, h⟩

theorem cornerMin_countable (g : ℝ → ℝ) (q : ℝ) : (cornerMin g q).Countable := by
  have key : ∀ x ∈ cornerMin g q, ∃ p r : ℚ, (p:ℝ) < x ∧ x < (r:ℝ) ∧
      ∀ y : ℝ, (p:ℝ) < y → y < (r:ℝ) → y ≠ x → g x - q * x < g y - q * y := by
    intro x hx
    rw [cornerMin] at hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨⟨δ₁, hδ₁, h₁⟩, ⟨δ₂, hδ₂, h₂⟩⟩ := hx
    have hmin : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show x - min δ₁ δ₂ / 2 < x by linarith)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show x < x + min δ₁ δ₂ / 2 by linarith)
    refine ⟨p, r, hp2, hr1, fun y hy1 hy2 hyne => ?_⟩
    rcases lt_or_gt_of_ne hyne with hy_lt | hy_gt
    · have hmem : x - δ₂ < y := by
        have h2' : min δ₁ δ₂ / 2 < δ₂ := by
          have := min_le_right δ₁ δ₂; linarith
        linarith
      have hyx := h₂ y hmem hy_lt
      linarith
    · have hmem : y < x + δ₁ := by
        have h2' : min δ₁ δ₂ / 2 < δ₁ := by
          have := min_le_left δ₁ δ₂; linarith
        linarith
      have hyx := h₁ y hy_gt hmem
      linarith
  have hsub : ∀ z : ℚ × ℚ, ({x : ℝ | (z.1:ℝ) < x ∧ x < (z.2:ℝ) ∧
      ∀ y : ℝ, (z.1:ℝ) < y → y < (z.2:ℝ) → y ≠ x →
        g x - q * x < g y - q * y} : Set ℝ).Subsingleton := by
    rintro ⟨p, r⟩ x ⟨hx1, hx2, hx⟩ x' ⟨hx1', hx2', hx'⟩
    rcases lt_trichotomy x x' with hlt | heq | hgt
    · exfalso
      have h1 := hx x' hx1' hx2' (ne_of_gt hlt)
      have h2 := hx' x hx1 hx2 (ne_of_lt hlt)
      linarith
    · exact heq
    · exfalso
      have h1 := hx x' hx1' hx2' (ne_of_lt hgt)
      have h2 := hx' x hx1 hx2 (ne_of_gt hgt)
      linarith
  refine Set.Countable.mono ?_ (Set.countable_iUnion (fun z : ℚ × ℚ => (hsub z).countable))
  intro x hx
  obtain ⟨p, r, hp, hr, h⟩ := key x hx
  exact Set.mem_iUnion.mpr ⟨(p, r), hp, hr, h⟩
end Work.WilG1.OneDim

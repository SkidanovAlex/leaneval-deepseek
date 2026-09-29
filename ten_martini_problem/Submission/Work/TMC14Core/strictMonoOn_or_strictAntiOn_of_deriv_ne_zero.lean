import Mathlib
import Submission.Work.TMC14Core.RatRot

namespace Work.TMC14Core

/-- A continuous real function that never vanishes on an open interval has constant sign there.
This is the intermediate-value argument behind the `deriv ≠ 0` monotonicity dichotomy. -/
lemma eq_sign_of_continuousOn_Ioo_ne_zero {a c : ℝ} {g : ℝ → ℝ} (hg : Continuous g)
    (h : ∀ E ∈ Set.Ioo a c, g E ≠ 0) :
    (∀ E ∈ Set.Ioo a c, 0 < g E) ∨ (∀ E ∈ Set.Ioo a c, g E < 0) := by
  by_cases hcase : ∃ E ∈ Set.Ioo a c, 0 < g E
  · left
    obtain ⟨x, hx, hxpos⟩ := hcase
    intro y hy
    by_contra hcon
    rw [not_lt] at hcon
    have hyneg : g y < 0 := lt_of_le_of_ne hcon (h y hy)
    have hxy : x ≠ y := by
      intro heq
      rw [heq] at hxpos
      exact absurd hxpos (not_lt.mpr (le_of_lt hyneg))
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · have hcont : ContinuousOn g (Set.Icc x y) := hg.continuousOn
      have hz : (0 : ℝ) ∈ Set.Ioo (g y) (g x) := ⟨hyneg, hxpos⟩
      have hmem : (0 : ℝ) ∈ g '' Set.Ioo x y :=
        (intermediate_value_Ioo' (le_of_lt hlt) hcont) hz
      obtain ⟨z, hzmem, hz0⟩ := hmem
      exact (h z ⟨lt_trans hx.1 hzmem.1, lt_trans hzmem.2 hy.2⟩) hz0
    · have hcont : ContinuousOn g (Set.Icc y x) := hg.continuousOn
      have hz : (0 : ℝ) ∈ Set.Ioo (g y) (g x) := ⟨hyneg, hxpos⟩
      have hmem : (0 : ℝ) ∈ g '' Set.Ioo y x :=
        (intermediate_value_Ioo (le_of_lt hlt) hcont) hz
      obtain ⟨z, hzmem, hz0⟩ := hmem
      exact (h z ⟨lt_trans hy.1 hzmem.1, lt_trans hzmem.2 hx.2⟩) hz0
  · right
    intro y hy
    have : ¬ 0 < g y := fun hp => hcase ⟨y, hy, hp⟩
    rw [not_lt] at this
    exact lt_of_le_of_ne this (h y hy)

theorem strictMonoOn_or_strictAntiOn_of_deriv_ne_zero (p : Polynomial ℝ) (a c : ℝ)
    (h : ∀ E ∈ Set.Ioo a c, (Polynomial.derivative p).eval E ≠ 0) :
    (StrictMonoOn (fun E => p.eval E) (Set.Ioo a c) ∨
      StrictAntiOn (fun E => p.eval E) (Set.Ioo a c)) := by
  have hgc : Continuous (fun E : ℝ => (Polynomial.derivative p).eval E) :=
    Polynomial.continuous (Polynomial.derivative p)
  rcases eq_sign_of_continuousOn_Ioo_ne_zero hgc h with hpos | hneg
  · left
    apply strictMonoOn_of_deriv_pos (convex_Ioo a c)
    · exact (Polynomial.continuous p).continuousOn
    · intro z hz
      rw [isOpen_Ioo.interior_eq] at hz
      rw [Polynomial.deriv]
      exact hpos z hz
  · right
    apply strictAntiOn_of_deriv_neg (convex_Ioo a c)
    · exact (Polynomial.continuous p).continuousOn
    · intro z hz
      rw [isOpen_Ioo.interior_eq] at hz
      rw [Polynomial.deriv]
      exact hneg z hz

end Work.TMC14Core

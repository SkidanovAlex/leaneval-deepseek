import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.crossing_lemma_paths

set_option autoImplicit false

/-!
# The Maehara rectangle and its crossing lemma

This file collects the vocabulary used by the Maehara proof of the uniqueness of the bounded
component of the complement of a Jordan curve: the rectangle `rect = [-1,1] × [-2,2]`, its
supporting lines `rectB`, and the crossing lemma for `rect` (obtained from
`Work.RPB1a.Caratheodory.Brouwer.crossing_lemma_paths` by rescaling the second coordinate by `1/2`).
-/

namespace Work.RPB1a.Caratheodory.Brouwer

open Set Metric

/-- The rectangle `[-1,1] × [-2,2]`. -/
def rect : Set (ℝ × ℝ) := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-2 : ℝ) 2

/-- The union of the four supporting lines of `rect`. -/
def rectB : Set (ℝ × ℝ) := {p | p.1 = -1 ∨ p.1 = 1 ∨ p.2 = -2 ∨ p.2 = 2}

@[simp] theorem mem_rect {p : ℝ × ℝ} :
    p ∈ rect ↔ -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -2 ≤ p.2 ∧ p.2 ≤ 2 := by
  simp only [rect, Set.mem_prod, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩

@[simp] theorem mem_rectB {p : ℝ × ℝ} :
    p ∈ rectB ↔ p.1 = -1 ∨ p.1 = 1 ∨ p.2 = -2 ∨ p.2 = 2 := Iff.rfl

theorem rect_convex : Convex ℝ rect := by
  rw [show rect = Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-2 : ℝ) 2 from rfl]
  exact Convex.prod (convex_Icc (-1) 1) (convex_Icc (-2) 2)

theorem rect_closed : IsClosed rect := by
  rw [show rect = Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-2 : ℝ) 2 from rfl]
  exact isClosed_Icc.prod isClosed_Icc

/-- The crossing lemma for the rectangle `rect`: a path from the left side `x = -1` to the right
side `x = 1` and a path from the bottom `y = -2` to the top `y = 2`, both staying in `rect`, must
meet.  Obtained from `crossing_lemma_paths` by the rescaling `(x,y) ↦ (x, y/2)` which maps `rect`
onto `[-1,1] × [-1,1]`. -/
theorem crossing_lemma_rect {h v : ℝ → ℝ × ℝ} (hh : Continuous h) (hv : Continuous v)
    (hhm : ∀ t, h t ∈ rect) (hvm : ∀ t, v t ∈ rect)
    (hh_left : (h (-1)).1 = -1) (hh_right : (h 1).1 = 1)
    (hv_bot : (v (-1)).2 = -2) (hv_top : (v 1).2 = 2) :
    ∃ s t : ℝ, h s = v t := by
  have hHc : Continuous fun t : ℝ => ((h t).1, (h t).2 / 2) :=
    (continuous_fst.comp hh).prodMk ((continuous_snd.comp hh).div_const 2)
  have hVc : Continuous fun t : ℝ => ((v t).1, (v t).2 / 2) :=
    (continuous_fst.comp hv).prodMk ((continuous_snd.comp hv).div_const 2)
  have hHm : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      ((h t).1, (h t).2 / 2) ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    intro t _
    have ht' := hhm t
    rw [mem_rect] at ht'
    exact ⟨⟨ht'.1, ht'.2.1⟩, ⟨by linarith [ht'.2.2.1], by linarith [ht'.2.2.2]⟩⟩
  have hVm : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      ((v t).1, (v t).2 / 2) ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    intro t _
    have ht' := hvm t
    rw [mem_rect] at ht'
    exact ⟨⟨ht'.1, ht'.2.1⟩, ⟨by linarith [ht'.2.2.1], by linarith [ht'.2.2.2]⟩⟩
  obtain ⟨s, _, t, _, hst⟩ :=
    crossing_lemma_paths hHc hVc hHm hVm hh_left hh_right
      (by simp [hv_bot]) (by simp [hv_top])
  have h1 : (h s).1 = (v t).1 := by
    simpa using congrArg (fun p : ℝ × ℝ => p.1) hst
  have h2 : (h s).2 = (v t).2 := by
    have h2' := congrArg (fun p : ℝ × ℝ => p.2) hst
    simp only at h2'
    linarith
  exact ⟨s, t, Prod.ext h1 h2⟩

/-- The crossing lemma for `rect` in the form that records the parameters of the intersection point
and only asks the two paths to lie in `rect` on `[-1,1]`. -/
theorem crossing_lemma_rect_of_Icc {h v : ℝ → ℝ × ℝ} (hh : Continuous h) (hv : Continuous v)
    (hhm : ∀ t ∈ Set.Icc (-1 : ℝ) 1, h t ∈ rect)
    (hvm : ∀ t ∈ Set.Icc (-1 : ℝ) 1, v t ∈ rect)
    (hh_left : (h (-1)).1 = -1) (hh_right : (h 1).1 = 1)
    (hv_bot : (v (-1)).2 = -2) (hv_top : (v 1).2 = 2) :
    ∃ s ∈ Set.Icc (-1 : ℝ) 1, ∃ t ∈ Set.Icc (-1 : ℝ) 1, h s = v t := by
  have hHc : Continuous fun t : ℝ => ((h t).1, (h t).2 / 2) :=
    (continuous_fst.comp hh).prodMk ((continuous_snd.comp hh).div_const 2)
  have hVc : Continuous fun t : ℝ => ((v t).1, (v t).2 / 2) :=
    (continuous_fst.comp hv).prodMk ((continuous_snd.comp hv).div_const 2)
  have hHm : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      ((h t).1, (h t).2 / 2) ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    intro t ht
    have ht' := hhm t ht
    rw [mem_rect] at ht'
    exact ⟨⟨ht'.1, ht'.2.1⟩, ⟨by linarith [ht'.2.2.1], by linarith [ht'.2.2.2]⟩⟩
  have hVm : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      ((v t).1, (v t).2 / 2) ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    intro t ht
    have ht' := hvm t ht
    rw [mem_rect] at ht'
    exact ⟨⟨ht'.1, ht'.2.1⟩, ⟨by linarith [ht'.2.2.1], by linarith [ht'.2.2.2]⟩⟩
  obtain ⟨s, hs, t, ht, hst⟩ :=
    crossing_lemma_paths hHc hVc hHm hVm hh_left hh_right
      (by simp [hv_bot]) (by simp [hv_top])
  refine ⟨s, hs, t, ht, ?_⟩
  have h1 : (h s).1 = (v t).1 := by
    simpa using congrArg (fun p : ℝ × ℝ => p.1) hst
  have h2 : (h s).2 = (v t).2 := by
    have h2' := congrArg (fun p : ℝ × ℝ => p.2) hst
    simp only at h2'
    linarith
  exact Prod.ext h1 h2

end Work.RPB1a.Caratheodory.Brouwer

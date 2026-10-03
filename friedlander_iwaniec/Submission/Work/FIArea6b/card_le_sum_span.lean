import Mathlib
import Submission.Work.FIArea6b.Basic

namespace Work.FIArea6b

/-- `y` lies in the `y`-values of `A` in column `t` iff it is the second coordinate of a
point of `A` whose first coordinate is `t`. -/
lemma mem_ys {A : Finset (ℤ × ℤ)} {t y : ℤ} :
    y ∈ ys A t ↔ ∃ p ∈ A, p.1 = t ∧ p.2 = y := by
  simp [ys, and_assoc]

/-- Every column index of `A` actually carries a point, so the `y`-values in it are nonempty. -/
lemma ys_nonempty_of_mem_cols {A : Finset (ℤ × ℤ)} {t : ℤ} (ht : t ∈ cols A) :
    (ys A t).Nonempty := by
  rw [cols, Finset.mem_image] at ht
  obtain ⟨p, hp, hpt⟩ := ht
  exact ⟨p.2, (mem_ys).mpr ⟨p, hp, hpt, rfl⟩⟩

/-- The `y`-values of `A` in column `t` all lie between `loOf A t` and `hiOf A t`. -/
lemma ys_subset_Icc (A : Finset (ℤ × ℤ)) {t : ℤ} (ht : t ∈ cols A) :
    ys A t ⊆ Finset.Icc (loOf A t) (hiOf A t) := by
  have hne := ys_nonempty_of_mem_cols ht
  have hlo : loOf A t = (ys A t).min' hne := by rw [loOf, dif_pos hne]
  have hhi : hiOf A t = (ys A t).max' hne := by rw [hiOf, dif_pos hne]
  intro y hy
  rw [Finset.mem_Icc]
  exact ⟨hlo ▸ Finset.min'_le _ _ hy, hhi ▸ Finset.le_max' _ _ hy⟩

/-- The number of points of `A` in a nonempty column `t` is at most the vertical span
(taken over `ℝ`) plus one. -/
lemma card_ys_le_span (A : Finset (ℤ × ℤ)) {t : ℤ} (ht : t ∈ cols A) :
    ((ys A t).card : ℝ) ≤ spanOf A t + 1 := by
  have hsub := ys_subset_Icc A ht
  have hcard : ((ys A t).card : ℝ)
      ≤ ((Finset.Icc (loOf A t) (hiOf A t)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hne := ys_nonempty_of_mem_cols ht
  have hle : loOf A t ≤ hiOf A t := by
    have hlo : loOf A t = (ys A t).min' hne := by rw [loOf, dif_pos hne]
    have hhi : hiOf A t = (ys A t).max' hne := by rw [hiOf, dif_pos hne]
    rw [hlo, hhi]
    exact Finset.min'_le _ _ (Finset.max'_mem _ _)
  have hIcc : ((Finset.Icc (loOf A t) (hiOf A t)).card : ℝ)
      = (hiOf A t : ℝ) + 1 - (loOf A t : ℝ) := by
    have h := Int.card_Icc_of_le (a := loOf A t) (b := hiOf A t) (by omega)
    exact_mod_cast h
  rw [hIcc] at hcard
  rw [spanOf]
  linarith

theorem card_le_sum_span (A : Finset (ℤ × ℤ)) :
    (A.card : ℝ) ≤ ∑ t ∈ cols A, (spanOf A t + 1) := by
  have hfiber : (A.card : ℝ)
      = ∑ t ∈ cols A, ((A.filter (fun p => p.1 = t)).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : ℤ × ℤ => p.1) (t := cols A)
      (by intro x hx; exact Finset.mem_image.mpr ⟨x, hx, rfl⟩)]
    push_cast
    rfl
  rw [hfiber]
  refine Finset.sum_le_sum fun t ht => ?_
  have hinj : Set.InjOn (fun p : ℤ × ℤ => p.2)
      ((A.filter (fun p => p.1 = t) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
    intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
    exact Prod.ext (by rw [hp.2, hq.2]) hpq
  have hcard_eq : (A.filter (fun p => p.1 = t)).card = (ys A t).card := by
    rw [ys]; exact (Finset.card_image_of_injOn hinj).symm
  calc ((A.filter (fun p => p.1 = t)).card : ℝ)
      = ((ys A t).card : ℝ) := by rw [hcard_eq]
    _ ≤ spanOf A t + 1 := card_ys_le_span A ht

end Work.FIArea6b

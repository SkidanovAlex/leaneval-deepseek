import Mathlib
import Submission.Work.WilC4.ULPMDev

namespace Work.WilC4

/-- If a point `m` lies strictly between `min ρ (a k)` and `max ρ (a k)` for *no* `k`, and
`a k → lam`, then `m` also does not lie strictly between `min ρ lam` and `max ρ lam`.

Indeed, if `min ρ lam < m < max ρ lam` then `ρ ≠ lam`; if `ρ < lam` then `ρ < m < lam` and
`a k > m` for all large `k`, whence `min ρ (a k) ≤ ρ < m < a k ≤ max ρ (a k)`; if `lam < ρ`
then `lam < m < ρ` and `a k < m` for all large `k`, whence
`min ρ (a k) ≤ a k < m < ρ ≤ max ρ (a k)`.  Both contradict `hb`. -/
theorem cbz_no_between_limit {E : Set ℝ} {ρ : ℝ} {a : ℕ → ℝ} {lam : ℝ}
    (hb : ∀ k : ℕ, ∀ m ∈ Work.WilC4.Mid E, ¬ (min ρ (a k) < m ∧ m < max ρ (a k)))
    (ha : Filter.Tendsto a Filter.atTop (nhds lam)) :
    ∀ m ∈ Work.WilC4.Mid E, ¬ (min ρ lam < m ∧ m < max ρ lam) := by
  intro m hm h
  obtain ⟨h1, h2⟩ := h
  have hne : ρ ≠ lam := by
    intro heq
    have hlt : min ρ lam < max ρ lam := lt_trans h1 h2
    rw [heq] at hlt
    simp at hlt
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `ρ < lam`
    have hmin : min ρ lam = ρ := min_eq_left hlt.le
    have hmax : max ρ lam = lam := max_eq_right hlt.le
    rw [hmin] at h1
    rw [hmax] at h2
    -- `h1 : ρ < m`, `h2 : m < lam`
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m < a k :=
      (Filter.eventually_atTop.mp (ha.eventually (Ioi_mem_nhds h2))).imp fun k hk => hk k le_rfl
    exact hb k m hm ⟨lt_of_le_of_lt (min_le_left _ _) h1, lt_of_lt_of_le hk (le_max_right _ _)⟩
  · -- `lam < ρ`
    have hmin : min ρ lam = lam := min_eq_right hgt.le
    have hmax : max ρ lam = ρ := max_eq_left hgt.le
    rw [hmin] at h1
    rw [hmax] at h2
    -- `h1 : lam < m`, `h2 : m < ρ`
    obtain ⟨k, hk⟩ : ∃ k : ℕ, a k < m :=
      (Filter.eventually_atTop.mp (ha.eventually (Iio_mem_nhds h1))).imp fun k hk => hk k le_rfl
    exact hb k m hm ⟨lt_of_le_of_lt (min_le_right _ _) hk, lt_of_lt_of_le h2 (le_max_left _ _)⟩

end Work.WilC4

import Mathlib
import Submission.Work.WilC4.ULPMDev

namespace Work.WilC4

/-- If `m` is not strictly between `a` and `b`, then `m` is weakly below both `a` and `b`, or
weakly above both.  (Formally: `¬ (min a b < m ∧ m < max a b)` implies
`(m ≤ a ∧ m ≤ b) ∨ (a ≤ m ∧ b ≤ m)`.) -/
lemma le_both_or_ge_both_of_not_between {a b m : ℝ}
    (h : ¬ (min a b < m ∧ m < max a b)) :
    (m ≤ a ∧ m ≤ b) ∨ (a ≤ m ∧ b ≤ m) := by
  by_cases hle : m ≤ min a b
  · exact Or.inl ⟨le_trans hle (min_le_left a b), le_trans hle (min_le_right a b)⟩
  · have hlt : min a b < m := lt_of_not_ge hle
    have hmax : max a b ≤ m := not_lt.mp (fun hc => h ⟨hlt, hc⟩)
    exact Or.inr ⟨le_trans (le_max_left a b) hmax, le_trans (le_max_right a b) hmax⟩

theorem cbz_not_between_trans {E : Set ℝ} {w ρ lam m : ℝ} (hw : w ∉ Work.WilC4.Mid E)
    (hm : m ∈ Work.WilC4.Mid E)
    (h1 : ¬ (min w ρ < m ∧ m < max w ρ)) (h2 : ¬ (min w lam < m ∧ m < max w lam)) :
    ¬ (min ρ lam < m ∧ m < max ρ lam) := by
  have h1' := le_both_or_ge_both_of_not_between h1
  have h2' := le_both_or_ge_both_of_not_between h2
  rintro ⟨hmin, hmax⟩
  rcases h1' with ⟨hmw, hmρ⟩ | ⟨hwm, hρm⟩
  · -- `m` is weakly below both `w` and `ρ`
    rcases h2' with ⟨_, hmlam⟩ | ⟨hwm2, _⟩
    · -- `m` is weakly below both `w` and `lam`: hence `m ≤ min ρ lam`
      exact absurd hmin (not_lt.mpr (le_min hmρ hmlam))
    · -- mixed: `m ≤ w` and `w ≤ m`, so `m = w ∈ Mid E`, contradicting `w ∉ Mid E`
      exact hw (by rw [← le_antisymm hmw hwm2]; exact hm)
  · -- `m` is weakly above both `w` and `ρ`
    rcases h2' with ⟨hmw2, _⟩ | ⟨_, hlam⟩
    · -- mixed: `w ≤ m` and `m ≤ w`, so `m = w ∈ Mid E`, contradicting `w ∉ Mid E`
      exact hw (by rw [← le_antisymm hmw2 hwm]; exact hm)
    · -- `m` is weakly above both `w` and `lam`: hence `max ρ lam ≤ m`
      exact absurd hmax (not_lt.mpr (max_le hρm hlam))

end Work.WilC4

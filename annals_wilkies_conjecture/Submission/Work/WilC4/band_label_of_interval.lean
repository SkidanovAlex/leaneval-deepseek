import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.mid_band_unique
import Submission.Work.WilC4.mb_exists_mid_between
import Submission.Work.WilC4.mb_mid_gap_unique

namespace Work.WilC4

/-- Auxiliary lemma: if `r < s` are positive elements of a finite set `E`, and `x₁` (resp. `x₂`)
is a point of `(a, b)` whose band is `r` (resp. `s`), while `(a, b)` contains no element of
`Mid E`, we get a contradiction.  The geometric mean `m` of `r` and `s` exists in `Mid E` and lies
strictly between `r` and `s`; since `m ∉ (a, b)`, either `m ≤ a` (then `m` is trapped in the band
`(r, x₁)`, contradicting that `x₁` has band `r`) or `b ≤ m` (then `m` is trapped in the band
`(x₂, s)`, contradicting that `x₂` has band `s`). -/
lemma band_mono {E : Set ℝ} (hE : E.Finite) {a b x₁ x₂ : ℝ}
    (hax : a < x₁) (hxb : x₂ < b)
    (hfree : ∀ s ∈ Set.Ioo a b, s ∉ Work.WilC4.Mid E)
    {r s : ℝ} (hrE : r ∈ E) (hr0 : 0 < r)
    (hrgood : ∀ m ∈ Work.WilC4.Mid E, ¬ (min x₁ r < m ∧ m < max x₁ r))
    (hsE : s ∈ E) (hs0 : 0 < s)
    (hsgood : ∀ m ∈ Work.WilC4.Mid E, ¬ (min x₂ s < m ∧ m < max x₂ s))
    (hrs : r < s) : False := by
  obtain ⟨m, hmMid, hm1, hm2⟩ := mb_exists_mid_between hE hrE hr0 hsE hrs
  -- `m ∉ (a, b)`
  have hmin : ¬ (a < m ∧ m < b) := by
    intro h
    exact hfree m (by rw [Set.mem_Ioo]; exact h) hmMid
  rw [not_and_or, not_lt, not_lt] at hmin
  rcases hmin with h | h
  · -- `m ≤ a < x₁`, so `m` lies strictly between `r` and `x₁`
    have hmx : m < x₁ := lt_of_le_of_lt h hax
    exact hrgood m hmMid
      ⟨lt_of_le_of_lt (min_le_right _ _) hm1, lt_of_lt_of_le hmx (le_max_left _ _)⟩
  · -- `x₂ < b ≤ m`, so `m` lies strictly between `x₂` and `s`
    have hxm : x₂ < m := lt_of_lt_of_le hxb h
    exact hsgood m hmMid
      ⟨lt_of_le_of_lt (min_le_left _ _) hxm, lt_of_lt_of_le hm2 (le_max_right _ _)⟩

theorem band_label_of_interval {E : Set ℝ} (hE : E.Finite) (hne : ∃ ρ ∈ E, 0 < ρ)
    {a b x x' : ℝ} (hax : a < x) (hxb : x < b) (hax' : a < x') (hx'b : x' < b)
    (hfree : ∀ s ∈ Set.Ioo a b, s ∉ Work.WilC4.Mid E) (hx0 : 0 < x) (hx'0 : 0 < x')
    {ρ ρ' : ℝ} (hρ : ρ ∈ E ∧ 0 < ρ ∧ ∀ m ∈ Work.WilC4.Mid E, ¬(min x ρ < m ∧ m < max x ρ))
    (hρ' : ρ' ∈ E ∧ 0 < ρ' ∧ ∀ m ∈ Work.WilC4.Mid E, ¬(min x' ρ' < m ∧ m < max x' ρ')) :
    ρ = ρ' := by
  obtain ⟨hρE, hρ0, hρgood⟩ := hρ
  obtain ⟨hρ'E, hρ'0, hρ'good⟩ := hρ'
  rcases lt_trichotomy ρ ρ' with h | h | h
  · exact absurd (band_mono hE hax hx'b hfree hρE hρ0 hρgood hρ'E hρ'0 hρ'good h) (by simp)
  · exact h
  · exact absurd (band_mono hE hax' hxb hfree hρ'E hρ'0 hρ'good hρE hρ0 hρgood h) (by simp)

end Work.WilC4

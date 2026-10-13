import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.mid_band_unique
import Submission.Work.WilC4.mb_exists_mid_between
import Submission.Work.WilC4.mb_mid_gap_unique

namespace Work.WilC4

/-! ## The band label is constant on a `Mid`-free interval

`Mid E` is the set of geometric means of consecutive positive elements of `E` (see `ULPMDev.lean`).
For `x > 0` with `x ∉ Mid E`, `mid_band_unique` produces a *unique* positive `ρ ∈ E` whose band
around `x` — the interval between `x` and `ρ` — contains no element of `Mid E`.  The lemmas here
show that this label depends only on the `Mid`-free interval ("slot") in which `x` lies: two points
`x, x'` with no element of `Mid E` strictly between them get the same label. -/

/-- Read off the position of `x` from the band condition: if `ρ < m` with `m ∈ Mid E` and no
element of `Mid E` lies in the band between `x` and `ρ`, then `x ≤ m`.  Indeed, if `m < x` then
`m` would lie strictly in that band (`min x ρ ≤ ρ < m` and `m < x ≤ max x ρ`). -/
lemma band_label_witness_le {E : Set ℝ} {x ρ m : ℝ} (hρm : ρ < m) (hm : m ∈ Mid E)
    (hgood : ∀ m ∈ Mid E, ¬ (min x ρ < m ∧ m < max x ρ)) : x ≤ m := by
  by_contra hx
  have hmx : m < x := not_le.mp hx
  exact hgood m hm
    ⟨lt_of_le_of_lt (min_le_right x ρ) hρm, lt_of_lt_of_le hmx (le_max_left x ρ)⟩

/-- The mirror of `band_label_witness_le`: if `m < ρ` with `m ∈ Mid E` and no element of `Mid E`
lies in the band between `x` and `ρ`, then `m ≤ x`.  Indeed, if `x < m` then `m` lies strictly in
that band (`min x ρ ≤ x < m` and `m < ρ ≤ max x ρ`). -/
lemma band_label_witness_ge {E : Set ℝ} {x ρ m : ℝ} (hmρ : m < ρ) (hm : m ∈ Mid E)
    (hgood : ∀ m ∈ Mid E, ¬ (min x ρ < m ∧ m < max x ρ)) : m ≤ x := by
  by_contra hx
  have hxm : x < m := not_le.mp hx
  exact hgood m hm
    ⟨lt_of_le_of_lt (min_le_left x ρ) hxm, lt_of_lt_of_le hmρ (le_max_right x ρ)⟩

/-- If `a ≤ m ≤ b` and no element of `Mid E` lies *strictly* between `a` and `b` (the hypothesis
`hfree`), then `m` coincides with `a` or with `b`. -/
lemma band_label_free_split {a b m : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (hfree : ¬ (a < m ∧ m < b)) : a = m ∨ b = m := by
  rcases lt_or_eq_of_le ham with h | h
  · rcases lt_or_eq_of_le hmb with h' | h'
    · exact absurd ⟨h, h'⟩ hfree
    · exact Or.inr h'.symm
  · exact Or.inl h

/-- **The band label is closed.**  For a finite `E ⊆ ℝ` containing a positive element, and points
`x, x' > 0` outside `Mid E` with no element of `Mid E` strictly between them, the positive
`ρ ∈ E` whose band around `x` avoids `Mid E` equals the corresponding witness `ρ'` for `x'`.

The proof: if `ρ < ρ'` then the pair of consecutive positive elements of `E` supplied by
`mb_exists_mid_between` has a geometric mean `m ∈ Mid E` with `ρ < m < ρ'`; the two band
conditions force `x ≤ m ≤ x'`, so `m` lies weakly between `x` and `x'`.  Since `Mid E` has no
element *strictly* between `x` and `x'` while `x, x' ∉ Mid E`, this is impossible.  The case
`ρ' < ρ` is symmetric. -/
theorem band_label_closed {E : Set ℝ} (hE : E.Finite) (hne : ∃ ρ ∈ E, 0 < ρ)
    {x x' ρ ρ' : ℝ} (hx0 : 0 < x) (hx'0 : 0 < x') (hxm : x ∉ Work.WilC4.Mid E)
    (hx'm : x' ∉ Work.WilC4.Mid E)
    (hfree : ∀ m ∈ Work.WilC4.Mid E, ¬(min x x' < m ∧ m < max x x'))
    (hρ : ρ ∈ E ∧ 0 < ρ ∧ ∀ m ∈ Work.WilC4.Mid E, ¬(min x ρ < m ∧ m < max x ρ))
    (hρ' : ρ' ∈ E ∧ 0 < ρ' ∧ ∀ m ∈ Work.WilC4.Mid E, ¬(min x' ρ' < m ∧ m < max x' ρ')) :
    ρ = ρ' := by
  obtain ⟨hρE, hρ0, hρgood⟩ := hρ
  obtain ⟨hρ'E, hρ'0, hρ'good⟩ := hρ'
  rcases lt_trichotomy ρ ρ' with hlt | heq | hlt
  · -- `ρ < ρ'`: a geometric mean of consecutive positive elements lies strictly between them.
    obtain ⟨m, hmMid, hρm, hmρ'⟩ := mb_exists_mid_between hE hρE hρ0 hρ'E hlt
    have hx_le : x ≤ m := band_label_witness_le hρm hmMid hρgood
    have hm_le_x' : m ≤ x' := band_label_witness_ge hmρ' hmMid hρ'good
    have hpair : ¬ (x < m ∧ m < x') := fun hc => hfree m hmMid
      ⟨lt_of_le_of_lt (min_le_left x x') hc.1, lt_of_lt_of_le hc.2 (le_max_right x x')⟩
    rcases band_label_free_split hx_le hm_le_x' hpair with h | h
    · exfalso
      exact hxm (by rw [h]; exact hmMid)
    · exfalso
      exact hx'm (by rw [h]; exact hmMid)
  · exact heq
  · -- `ρ' < ρ`: the symmetric situation, with the roles of `x` and `x'` interchanged.
    obtain ⟨m, hmMid, hρ'm, hmρ⟩ := mb_exists_mid_between hE hρ'E hρ'0 hρE hlt
    have hx'_le : x' ≤ m := band_label_witness_le hρ'm hmMid hρ'good
    have hm_le_x : m ≤ x := band_label_witness_ge hmρ hmMid hρgood
    have hpair' : ¬ (x' < m ∧ m < x) := fun hc => hfree m hmMid
      ⟨lt_of_le_of_lt (min_le_right x x') hc.1, lt_of_lt_of_le hc.2 (le_max_left x x')⟩
    rcases band_label_free_split hx'_le hm_le_x hpair' with h | h
    · exfalso
      exact hx'm (by rw [h]; exact hmMid)
    · exfalso
      exact hxm (by rw [h]; exact hmMid)

end Work.WilC4

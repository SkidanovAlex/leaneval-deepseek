import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.mb_exists_mid_between
import Submission.Work.WilC4.mid_band_unique

namespace Work.WilC4

/-- If `m` lies strictly between `a` and `b`, then `m` is strictly closer to `b` than `a` is. -/
private lemma abs_sub_lt_abs_sub_of_between {a b m : ℝ}
    (h : min a b < m ∧ m < max a b) : |m - b| < |a - b| := by
  rcases lt_or_ge a b with hab | hab
  · rw [min_eq_left (le_of_lt hab), max_eq_right (le_of_lt hab)] at h
    rw [abs_of_neg (by linarith : m - b < 0), abs_of_nonpos (by linarith : a - b ≤ 0)]
    linarith
  · rw [min_eq_right hab, max_eq_left hab] at h
    rw [abs_of_pos (by linarith : 0 < m - b), abs_of_pos (by linarith : 0 < a - b)]
    linarith

/-- **A scale close to a good band is the same scale.**  Let `E` be a finite set of reals, `δ > 0`
a separation constant separating the positive elements of `E` from the geometric midpoints
`Mid E`, and suppose `ρ ∈ E` is a positive element whose band `(min w ρ, max w ρ)` avoids `Mid E`.
If `ρ' ∈ E` is positive and the ratio `w / ρ'` is within `ε < δ` of `1`, then `ρ' = ρ`.

Indeed `|w - ρ'| < δ ρ' ≤ |ρ' - m|` for every `m ∈ Mid E`: so `w` itself is not in `Mid E`, and no
`m ∈ Mid E` can lie strictly between `w` and `ρ'`.  Thus `ρ'` is a good band for `w` too, and
uniqueness of the good band (`band_good_unique`) gives `ρ' = ρ`. -/
theorem eq_of_close_band {E : Set ℝ} (hE : E.Finite) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r ∈ E, 0 < r → ∀ m ∈ Work.WilC4.Mid E, δ * r ≤ |r - m|)
    {w ρ ρ' ε : ℝ} (hρE : ρ ∈ E) (hρ0 : 0 < ρ) (hρ'E : ρ' ∈ E) (hρ'0 : 0 < ρ')
    (hband : ∀ m ∈ Work.WilC4.Mid E, ¬ (min w ρ < m ∧ m < max w ρ))
    (hε : ε < δ) (hclose : |w / ρ' - 1| ≤ ε) : ρ' = ρ := by
  -- Multiplicative closeness of `w` to `ρ'` gives `|w - ρ'| < δ * ρ'`.
  have hwclose : |w - ρ'| < δ * ρ' := by
    have h1 : |w / ρ' - 1| < δ := lt_of_le_of_lt hclose hε
    rw [show w / ρ' - 1 = (w - ρ') / ρ' from by
          rw [sub_div, div_self (ne_of_gt hρ'0)], abs_div, abs_of_pos hρ'0] at h1
    rwa [div_lt_iff₀ hρ'0] at h1
  -- Hence `w ∉ Mid E`.
  have hwmid : w ∉ Work.WilC4.Mid E := by
    intro hw
    have h := hsep ρ' hρ'E hρ'0 w hw
    rw [abs_sub_comm] at h
    linarith
  -- And `ρ'` is a good band for `w`.
  have hgood' : ∀ m ∈ Work.WilC4.Mid E, ¬ (min w ρ' < m ∧ m < max w ρ') := by
    intro m hm hcon
    have h := hsep ρ' hρ'E hρ'0 m hm
    rw [abs_sub_comm] at h
    have hlt : |m - ρ'| < |w - ρ'| := abs_sub_lt_abs_sub_of_between hcon
    linarith
  exact (band_good_unique hE hwmid hρE hρ0 hband hρ'E hρ'0 hgood').symm

end Work.WilC4

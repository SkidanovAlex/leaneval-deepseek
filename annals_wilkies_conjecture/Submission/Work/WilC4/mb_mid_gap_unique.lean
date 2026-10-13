import Mathlib
import Submission.Work.WilC4.ULPMDev

namespace Work.WilC4

/-- If `m ∈ Mid E` lies strictly between `a, b ∈ E` and `(a,b)` contains no positive element of
`E`, then `a, b` are exactly the two consecutive positive elements of `E` whose geometric mean
is `m`. -/
theorem mb_mid_gap_unique {E : Set ℝ} {a b m : ℝ}
    (ha : a ∈ E) (ha0 : 0 < a) (hb : b ∈ E) (hab : a < b)
    (hno : ∀ c ∈ E, 0 < c → ¬ (a < c ∧ c < b))
    (hm : m ∈ Work.WilC4.Mid E) (hma : a < m) (hmb : m < b) :
    m * m = a * b := by
  obtain ⟨ρ₁, hρ₁, ρ₂, hρ₂, hρ₁pos, hρ₁ρ₂, hsep, hm2, hmpos⟩ := hm
  have hρ₂pos : 0 < ρ₂ := lt_trans hρ₁pos hρ₁ρ₂
  -- `m` lies strictly between `ρ₁` and `ρ₂`, since `m ^ 2 = ρ₁ * ρ₂` with `ρ₁ < ρ₂`.
  have hρ₁_lt_m : ρ₁ < m := by
    have hsq : ρ₁ * ρ₁ < m * m := by rw [hm2]; exact mul_lt_mul_of_pos_left hρ₁ρ₂ hρ₁pos
    nlinarith [hsq, hρ₁pos, hmpos]
  have hm_lt_ρ₂ : m < ρ₂ := by
    have hsq : m * m < ρ₂ * ρ₂ := by rw [hm2]; exact mul_lt_mul_of_pos_right hρ₁ρ₂ hρ₂pos
    nlinarith [hsq, hρ₁pos, hmpos]
  -- `a ≤ ρ₁`: otherwise `a` is a positive element of `E` strictly between `ρ₁` and `ρ₂`.
  have ha_le : a ≤ ρ₁ := by
    by_contra h
    rcases hsep a ha ha0 with h' | h'
    · linarith [not_le.mp h]
    · linarith
  -- `ρ₁ ≤ a`: otherwise `ρ₁` is a positive element of `E` strictly between `a` and `b`.
  have hρ₁_le : ρ₁ ≤ a := by
    by_contra h
    exact hno ρ₁ hρ₁ hρ₁pos ⟨not_le.mp h, lt_trans hρ₁_lt_m hmb⟩
  -- `ρ₂ ≤ b`: otherwise `b` is a positive element of `E` strictly between `ρ₁` and `ρ₂`.
  have hρ₂_le : ρ₂ ≤ b := by
    by_contra h
    rcases hsep b hb (lt_trans ha0 hab) with h' | h'
    · linarith [not_le.mp h]
    · linarith
  -- `b ≤ ρ₂`: otherwise `ρ₂` is a positive element of `E` strictly between `a` and `b`.
  have hb_le : b ≤ ρ₂ := by
    by_contra h
    exact hno ρ₂ hρ₂ hρ₂pos ⟨lt_trans hma hm_lt_ρ₂, not_le.mp h⟩
  have ha_eq : a = ρ₁ := le_antisymm ha_le hρ₁_le
  have hb_eq : b = ρ₂ := le_antisymm hb_le hρ₂_le
  rw [ha_eq, hb_eq, hm2]

end Work.WilC4

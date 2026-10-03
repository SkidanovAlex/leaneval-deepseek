import Mathlib
import Submission.Work.KMTPlan.A6.SsuPhi

set_option autoImplicit false

namespace Work.KMTPlan.A6

/-- `diffFreqs ρ l` is a subset of `iwArithFreqs ρ l` (it is either the whole set, for `l = 0`, or
the set difference `(ℚ/ℤ)_{≤l} \ (ℚ/ℤ)_{≤l-1}`), whence its cardinality is bounded by the IW height
count of `hCshle`. -/
theorem diffFreqs_card_le_iwArithFreqs (ρ : ℝ) (l : ℕ) :
    (Work.KMTAreas.A7.diffFreqs ρ l).card
      ≤ (Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card := by
  rcases eq_or_ne l 0 with h | h
  · subst h
    simp [Work.KMTAreas.A7.diffFreqs]
  · have hss : Work.KMTAreas.A7.diffFreqs ρ l
        ⊆ Work.Analysis.IonescuWainger.iwArithFreqs ρ l := by
      rw [Work.KMTAreas.A7.diffFreqs, if_neg h]
      exact Finset.sdiff_subset
    exact Finset.card_le_card hss

/-- **Bookkeeping bound `ssu-nb`.**  If the IW arithmetic frequency set `(ℚ/ℤ)_{≤l}` has at most
`Csh · 2^{2^{ρ l}}` elements then the product of the two exact-height level counts
`#(A_{l₁}) · #(A_{l₂})` with `max l₁ l₂ = L` is at most `Csh² · 2^{2·2^{ρ L}}`. -/
theorem ssuNbBound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (Csh : ℝ) (hCsh : 1 ≤ Csh)
    (hCshle : ∀ l : ℕ, ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ)
      ≤ Csh * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l : ℝ))))
    (L : ℕ) :
    ∀ l₁ l₂ : ℕ, max l₁ l₂ = L →
      ((Work.KMTAreas.A7.diffFreqs ρ l₁).card : ℝ) * ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ)
        ≤ Csh ^ 2 * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (L : ℝ))) := by
  intro l₁ l₂ hL
  have hc₁ : ((Work.KMTAreas.A7.diffFreqs ρ l₁).card : ℝ)
      ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ) := by
    exact_mod_cast diffFreqs_card_le_iwArithFreqs ρ l₁
  have hc₂ : ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ)
      ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ) := by
    exact_mod_cast diffFreqs_card_le_iwArithFreqs ρ l₂
  have hb₁ : ((Work.KMTAreas.A7.diffFreqs ρ l₁).card : ℝ)
      ≤ Csh * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₁ : ℝ))) := le_trans hc₁ (hCshle l₁)
  have hb₂ : ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ)
      ≤ Csh * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₂ : ℝ))) := le_trans hc₂ (hCshle l₂)
  have hc0 : (0 : ℝ) ≤ Csh := le_trans zero_le_one hCsh
  have hA₁ : (0 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₁ : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hcard₂0 : (0 : ℝ) ≤ ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul hb₁ hb₂ hcard₂0 (mul_nonneg hc0 hA₁)
  refine le_trans hmul ?_
  have hl₁ : l₁ ≤ L := by rw [← hL]; exact le_max_left _ _
  have hl₂ : l₂ ≤ L := by rw [← hL]; exact le_max_right _ _
  have hpow₁ : (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    have hcast : (l₁ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hl₁
    exact mul_le_mul_of_nonneg_left hcast hρ.le
  have hpow₂ : (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    have hcast : (l₂ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hl₂
    exact mul_le_mul_of_nonneg_left hcast hρ.le
  have hAA : (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₁ : ℝ)))
        * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₂ : ℝ)))
      ≤ (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (L : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  calc (Csh * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₁ : ℝ))))
        * (Csh * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₂ : ℝ))))
      = Csh ^ 2 * ((2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₁ : ℝ)))
          * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₂ : ℝ)))) := by ring
    _ ≤ Csh ^ 2 * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (L : ℝ))) :=
        mul_le_mul_of_nonneg_left hAA (sq_nonneg Csh)

end Work.KMTPlan.A6

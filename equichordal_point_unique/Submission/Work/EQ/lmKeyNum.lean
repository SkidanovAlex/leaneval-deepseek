import Mathlib
import Submission.Work.EQ.LocModelDefs

namespace Work.EQ

/-- Pure numerical core of `lmKeyNum`: for `S = lmS a a₀ = a/2 - a₀`, `T = lmT a a₀ = a₀ + 1 + a/2`
(with `S + T = 1 + a` and `a > 0`), the quantity `min S T / 16 + 16 * (min S T / 16)/(15 S)`
is at most `T/2`. -/
private lemma lmKeyNum_aux {S T a : ℝ} (hS : 0 < S) (hT : 0 < T)
    (hsum : S + T = 1 + a) (ha : 0 < a) :
    min S T / 16 + 16 * (min S T / 16) / (15 * S) ≤ T / 2 := by
  rcases le_total S T with hle | hle
  · rw [min_eq_left hle]
    have hkey : (16:ℝ) * (S / 16) / (15 * S) = 1/15 := by field_simp
    rw [hkey]
    have hT' : (1+a)/2 ≤ T := by linarith
    linarith
  · rw [min_eq_right hle]
    have hkey : (16:ℝ) * (T / 16) / (15 * S) = T / (15 * S) := by field_simp
    rw [hkey]
    have hS' : (1+a)/2 ≤ S := by linarith
    have hSpos : (0:ℝ) < 15 * S := by linarith
    have hbound : T / (15 * S) ≤ 7 * T / 16 := by
      rw [div_le_iff₀ hSpos]
      have h1 : (1:ℝ) ≤ 105 * S / 16 := by linarith
      have h2 : (7:ℝ) * T / 16 * (15 * S) = T * (105 * S / 16) := by ring
      rw [h2]
      calc T = T * 1 := by ring
        _ ≤ T * (105 * S / 16) := mul_le_mul_of_nonneg_left h1 (le_of_lt hT)
    linarith

theorem lmKeyNum {a a₀ : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (h1 : a/2 - 1 < a₀) (h2 : a₀ < -(a/2)) :
    Work.EQ.lmH a a₀ + 16 * Work.EQ.lmH a a₀ / (15 * Work.EQ.lmS a a₀) ≤ Work.EQ.lmT a a₀ / 2 := by
  have hS : 0 < lmS a a₀ := by rw [lmS]; linarith
  have hT : 0 < lmT a a₀ := by rw [lmT]; linarith
  have hsum : lmS a a₀ + lmT a a₀ = 1 + a := by rw [lmS, lmT]; ring
  have hH : lmH a a₀ = min (lmS a a₀) (lmT a a₀) / 16 := by rw [lmH]
  rw [hH]
  exact lmKeyNum_aux hS hT hsum ha0

end Work.EQ

import Mathlib

namespace Work.BG

theorem signOrthContra {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) {a b c d : ℤ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1)
    (h1 : (a : ℂ) * (c : ℂ) + (b : ℂ) * (d : ℂ) = 0)
    (h2 : ((a : ℂ) - (c : ℂ)) * x + ((b : ℂ) - (d : ℂ)) * y = 0) : False := by
  have ha2 : (a : ℂ) ^ 2 = 1 := by rcases ha with h | h <;> simp [h]
  have hb2 : (b : ℂ) ^ 2 = 1 := by rcases hb with h | h <;> simp [h]
  have hc2 : (c : ℂ) ^ 2 = 1 := by rcases hc with h | h <;> simp [h]
  have hd2 : (d : ℂ) ^ 2 = 1 := by rcases hd with h | h <;> simp [h]
  have hAc : ((a : ℂ) - (c : ℂ)) * ((a : ℂ) + (c : ℂ)) = 0 := by
    linear_combination ha2 - hc2
  have hBd : ((b : ℂ) - (d : ℂ)) * ((b : ℂ) + (d : ℂ)) = 0 := by
    linear_combination hb2 - hd2
  -- Multiply h2 by (a+c): the x-term dies since (a-c)(a+c)=0; then use y ≠ 0.
  have hA : ((b : ℂ) - (d : ℂ)) * ((a : ℂ) + (c : ℂ)) = 0 := by
    have hmain : ((a : ℂ) - (c : ℂ)) * ((a : ℂ) + (c : ℂ)) * x
        + ((b : ℂ) - (d : ℂ)) * ((a : ℂ) + (c : ℂ)) * y = 0 := by
      have h := congrArg (fun t : ℂ => t * ((a : ℂ) + (c : ℂ))) h2
      rw [zero_mul] at h
      rw [← h]; ring
    rw [hAc, zero_mul, zero_add] at hmain
    exact (mul_eq_zero.mp hmain).resolve_right hy
  -- Multiply h2 by (b+d): the y-term dies since (b-d)(b+d)=0; then use x ≠ 0.
  have hB : ((a : ℂ) - (c : ℂ)) * ((b : ℂ) + (d : ℂ)) = 0 := by
    have hmain : ((a : ℂ) - (c : ℂ)) * ((b : ℂ) + (d : ℂ)) * x
        + ((b : ℂ) - (d : ℂ)) * ((b : ℂ) + (d : ℂ)) * y = 0 := by
      have h := congrArg (fun t : ℂ => t * ((b : ℂ) + (d : ℂ))) h2
      rw [zero_mul] at h
      rw [← h]; ring
    rw [hBd, zero_mul, add_zero] at hmain
    exact (mul_eq_zero.mp hmain).resolve_right hx
  -- hA + hB = 2(ab - cd), so ab = cd.
  have hAB : (a : ℂ) * (b : ℂ) = (c : ℂ) * (d : ℂ) := by
    linear_combination (hA + hB) / 2
  -- bc = (ab)(ac) = (cd)(-bd) = -bc, using hAB, h1, a² = d² = 1.
  have h2bc : 2 * ((b : ℂ) * (c : ℂ)) = 0 := by
    linear_combination ((a : ℂ) * (c : ℂ)) * hAB + ((c : ℂ) * (d : ℂ)) * h1
      - ((b : ℂ) * (c : ℂ)) * ha2 - ((b : ℂ) * (c : ℂ)) * hd2
  have hbc : (b : ℂ) * (c : ℂ) = 0 := by
    rcases mul_eq_zero.mp h2bc with h | h
    · norm_num at h
    · exact h
  have hbc_ne : (b : ℂ) * (c : ℂ) ≠ 0 := by
    rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num
  exact hbc_ne hbc

end Work.BG

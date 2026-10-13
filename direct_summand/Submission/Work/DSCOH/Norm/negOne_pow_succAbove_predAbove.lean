import Mathlib

namespace Work.DSCOH.Norm

/-- `(-1 : ℤ) ^ m` depends only on `m % 2`. -/
private lemma negOne_pow_eq_of_mod_two {m n : ℕ} (h : m % 2 = n % 2) :
    (-1 : ℤ) ^ m = (-1 : ℤ) ^ n := by
  have h2 : (-1 : ℤ) ^ 2 = 1 := by norm_num
  rw [pow_eq_pow_mod m h2, pow_eq_pow_mod n h2, h]

/-- Value of `Fin.succAbove` on a numeral. -/
private lemma val_succAbove {N : ℕ} (b : Fin (N + 3)) (c : Fin (N + 2)) :
    (b.succAbove c).val = if c.val < b.val then c.val else c.val + 1 := by
  by_cases h : c.val < b.val
  · have h' : c.castSucc < b := by simpa [Fin.lt_def] using h
    rw [Fin.succAbove_of_castSucc_lt _ _ h', ite_eq_left h]
    simp
  · have h' : b ≤ c.castSucc := by
      simp only [Fin.le_def, Fin.val_castSucc]; omega
    rw [Fin.succAbove_of_le_castSucc _ _ h', ite_eq_right h]
    simp

/-- Value of `Fin.predAbove` on a numeral. -/
private lemma val_predAbove {N : ℕ} (b : Fin (N + 3)) (c : Fin (N + 2)) :
    (c.predAbove b).val = if c.val < b.val then b.val - 1 else b.val := by
  by_cases h : c.val < b.val
  · have h' : c.castSucc < b := by simpa [Fin.lt_def] using h
    rw [Fin.predAbove_of_castSucc_lt _ _ h', ite_eq_left h]
    simp
  · have h' : b ≤ c.castSucc := by
      simp only [Fin.le_def, Fin.val_castSucc]; omega
    rw [Fin.predAbove_of_le_castSucc _ _ h', ite_eq_right h]
    simp

theorem negOne_pow_succAbove_predAbove {N : ℕ} (b : Fin (N+3)) (c : Fin (N+2)) :
    (-1 : ℤ) ^ (b.succAbove c).val * (-1 : ℤ) ^ (c.predAbove b).val
      = -((-1 : ℤ) ^ b.val * (-1 : ℤ) ^ c.val) := by
  have ha := val_succAbove b c
  have hd := val_predAbove b c
  rw [← pow_add, ← pow_add]
  have hb : -((-1 : ℤ) ^ (b.val + c.val)) = (-1 : ℤ) ^ (b.val + c.val + 1) := by
    rw [pow_succ]; ring
  rw [hb]
  apply negOne_pow_eq_of_mod_two
  rw [ha, hd]
  by_cases h : c.val < b.val
  · rw [ite_eq_left h, ite_eq_left h]
    have : b.val + c.val + 1 = c.val + (b.val - 1) + 2 := by omega
    rw [this]; omega
  · rw [ite_eq_right h, ite_eq_right h]
    have : c.val + 1 + b.val = b.val + c.val + 1 := by omega
    rw [this]

end Work.DSCOH.Norm

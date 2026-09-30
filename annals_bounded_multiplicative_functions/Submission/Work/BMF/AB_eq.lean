import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- The exponent bookkeeping for the `A`-side: the natural number `2 * r * s - 2 * s`
(which is `2 * s * (r - 1)` for `r ≥ 1`) casts to `2 * (s:ℝ) * ((r:ℝ) - 1)`. -/
private lemma cast_e1 (r s : ℕ) (hr : 1 ≤ r) :
    ((2 * r * s - 2 * s : ℕ) : ℝ) = 2 * (s:ℝ) * ((r:ℝ) - 1) := by
  have h : (2 * s * (r - 1) : ℕ) = 2 * r * s - 2 * s := by
    rw [Nat.mul_sub_left_distrib]; ring_nf
  rw [← h]; push_cast [Nat.cast_sub hr]; ring

/-- The exponent bookkeeping for the `B`-side: the natural number `r * (2 * s - 2)`
(which is `2 * r * (s - 1)` for `s ≥ 1`) casts to `2 * (r:ℝ) * ((s:ℝ) - 1)`. -/
private lemma cast_e2 (r s : ℕ) (hs : 1 ≤ s) :
    ((r * (2 * s - 2) : ℕ) : ℝ) = 2 * (r:ℝ) * ((s:ℝ) - 1) := by
  have h2 : (2 * (s - 1) : ℕ) = 2 * s - 2 := Nat.mul_sub_left_distrib 2 s 1
  have h : (2 * r * (s - 1) : ℕ) = r * (2 * s - 2) := by rw [← h2]; ring
  rw [← h]; push_cast [Nat.cast_sub hs]; ring

/-- `k * (k + 1) / 2` casts to `(k:ℝ) * ((k:ℝ) + 1) / 2`. -/
private lemma cast_e3 (k : ℕ) :
    ((k * (k + 1) / 2 : ℕ) : ℝ) = (k:ℝ) * ((k:ℝ) + 1) / 2 := by
  rw [Nat.cast_div (by rw [Nat.dvd_iff_mod_eq_zero, ← Nat.even_iff]; exact Nat.even_mul_succ_self k)
        (by norm_num : (2:ℝ) ≠ 0)]
  push_cast; ring

theorem AB_eq (k r s : ℕ) (M₁ M₂ : ℕ) (J Jincom W : ℝ) (hr : 1 ≤ r) (hs : 1 ≤ s) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) :
    (M₂ : ℝ) ^ (2 * r * s - 2 * s) * (M₁ : ℝ) ^ (r * (2 * s - 2)) * J
        * ((5 * (r : ℝ)) ^ k * (M₁ : ℝ) ^ (k * (k + 1) / 2) * Jincom * W)
      = ((M₁ : ℝ) * (M₂ : ℝ)) ^ (2 * r * s)
        * ((5 * (r : ℝ)) ^ k * (M₂ : ℝ) ^ (-(2 * (s : ℝ)))
            * (M₁ : ℝ) ^ (-(2 * (r : ℝ)) + (k : ℝ) * ((k : ℝ) + 1) / 2) * J * Jincom * W) := by
  have hA : (0:ℝ) < (M₁:ℝ) := by
    have : (0:ℕ) < M₁ := lt_of_lt_of_le Nat.zero_lt_one hM₁
    exact_mod_cast this
  have hB : (0:ℝ) < (M₂:ℝ) := by
    have : (0:ℕ) < M₂ := lt_of_lt_of_le Nat.zero_lt_one hM₂
    exact_mod_cast this
  have he1 := cast_e1 r s hr
  have he2 := cast_e2 r s hs
  have he3 := cast_e3 k
  have he4 : ((2 * r * s : ℕ) : ℝ) = 2 * (r:ℝ) * (s:ℝ) := by push_cast; ring
  simp only [← Real.rpow_natCast]
  rw [he1, he2, he3, he4]
  rw [Real.mul_rpow (le_of_lt hA) (le_of_lt hB)]
  rw [show (M₂ : ℝ) ^ (2 * (s:ℝ) * ((r:ℝ) - 1)) * (M₁ : ℝ) ^ (2 * (r:ℝ) * ((s:ℝ) - 1)) * J * ((5 * (r:ℝ)) ^ (k:ℝ) * (M₁ : ℝ) ^ ((k:ℝ) * ((k:ℝ) + 1) / 2) * Jincom * W)
        = (M₂ : ℝ) ^ (2 * (s:ℝ) * ((r:ℝ) - 1)) * ((M₁ : ℝ) ^ (2 * (r:ℝ) * ((s:ℝ) - 1)) * (M₁ : ℝ) ^ ((k:ℝ) * ((k:ℝ) + 1) / 2)) * ((5 * (r:ℝ)) ^ (k:ℝ) * J * Jincom * W) from by ring]
  rw [← Real.rpow_add hA]
  rw [show (M₁ : ℝ) ^ (2 * (r:ℝ) * (s:ℝ)) * (M₂ : ℝ) ^ (2 * (r:ℝ) * (s:ℝ)) * ((5 * (r:ℝ)) ^ (k:ℝ) * (M₂ : ℝ) ^ (-(2 * (s:ℝ))) * (M₁ : ℝ) ^ (-(2 * (r:ℝ)) + (k:ℝ) * ((k:ℝ) + 1) / 2) * J * Jincom * W)
        = ((M₁ : ℝ) ^ (2 * (r:ℝ) * (s:ℝ)) * (M₁ : ℝ) ^ (-(2 * (r:ℝ)) + (k:ℝ) * ((k:ℝ) + 1) / 2)) * ((M₂ : ℝ) ^ (2 * (r:ℝ) * (s:ℝ)) * (M₂ : ℝ) ^ (-(2 * (s:ℝ)))) * ((5 * (r:ℝ)) ^ (k:ℝ) * J * Jincom * W) from by ring]
  rw [← Real.rpow_add hA, ← Real.rpow_add hB]
  rw [show (2 * (s:ℝ) * ((r:ℝ) - 1)) = 2 * (r:ℝ) * (s:ℝ) + (-(2 * (s:ℝ))) by ring]
  rw [show (2 * (r:ℝ) * ((s:ℝ) - 1) + (k:ℝ) * ((k:ℝ) + 1) / 2) = 2 * (r:ℝ) * (s:ℝ) + (-(2 * (r:ℝ)) + (k:ℝ) * ((k:ℝ) + 1) / 2) by ring]
  ring

end Work.BMF

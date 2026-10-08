import Mathlib

namespace Work.BG

theorem keySmallNeNegOne (N k : ℕ) (x y z : ℤ) (hy : Odd y)
    (hsum : 1 + x + y + z = 0)
    (heq : (N : ℤ) * (x * y * z + y * z + x * z + x * y) = 2 * (k : ℤ) ^ 2 * (x * y * z))
    (hk : k ≠ 0) :
    x ≠ -1 := by
  intro hx
  rw [hx] at hsum heq
  have hz : z = -y := by linarith
  rw [hz] at heq
  have hL : ((-1 : ℤ) * y * (-y) + y * (-y) + (-1) * (-y) + (-1) * y) = 0 := by ring
  rw [hL, mul_zero] at heq
  have hR : (-1 : ℤ) * y * (-y) = y ^ 2 := by ring
  rw [hR] at heq
  have hkz : (k : ℤ) ≠ 0 := by exact_mod_cast hk
  have hpos : (0 : ℤ) < 2 * (k : ℤ) ^ 2 := by positivity
  have hy2 : y ^ 2 = 0 := by
    have h : 2 * (k : ℤ) ^ 2 * y ^ 2 = 0 := heq.symm
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hpos)
  have hy0 : y = 0 := sq_eq_zero_iff.mp hy2
  obtain ⟨m, hm⟩ := hy
  rw [hy0] at hm
  omega

end Work.BG

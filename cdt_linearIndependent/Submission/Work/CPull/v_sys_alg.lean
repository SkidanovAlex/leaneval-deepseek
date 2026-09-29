import Mathlib

namespace Work.CPull

theorem v_sys_alg (u2 u4 u2' u4' y y' K K' V2 V4 : ℂ)
    (hK : K ≠ 0) (hy : y ≠ 0)
    (hK2 : K ^ 2 = y - 4) (hy' : y' = 2 * K * K')
    (hu2 : u2 = 2 * y + K * V2) (hu4 : u4 = K * V4)
    (hu2' : u2' = y' * ((2 - y) * u2 + y ^ 2) / (y * (4 - y)))
    (hu4' : u4' = y' * ((2 - y) * u4 + (4 - y) * u2 - 2 * y * (4 - y)) / (y * (4 - y))) :
    (u2' - 2 * y') * K - (u2 - 2 * y) * K' = (K * K' / y * V2 - 2 * K') * K ^ 2 ∧
    (u4' - K' * V4) * K - (u4 - K * V4) * K' = (K * K' / y * (V4 + 2 * V2)) * K ^ 2 := by
  have hy4 : y - 4 ≠ 0 := by rw [← hK2]; exact pow_ne_zero 2 hK
  have hy4' : (4 : ℂ) - y ≠ 0 := by
    rw [show (4:ℂ) - y = -(y - 4) by ring, neg_ne_zero]; exact hy4
  subst hu2 hu4 hu2' hu4' hy'
  constructor
  · field_simp
    ring_nf
    rw [show K ^ 3 = K * (y - 4) by rw [← hK2]; ring]
    ring
  · field_simp
    ring_nf
    rw [hK2]
    ring

end Work.CPull

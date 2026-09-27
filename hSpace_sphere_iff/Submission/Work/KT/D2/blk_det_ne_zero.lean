import Mathlib
import Submission.Work.KT.D2.Winding

namespace Work.KT.D2

/-- **The block determinant is nonzero.**  Let `e` be an idempotent matrix, and `u`, `v` invertible
matrices with `u * e = e * u`, `u * v = 1`, `v * u = 1`.  Then the "restriction of `u` to `im e`"
`e * u * e + (1 - e)` has nonzero determinant.

Route: first derive `v * e = e * v` by
`v * e = v * e * (u * v) = v * (e * u) * v = v * (u * e) * v = (v * u) * e * v = e * v`.  Then
`(e * u * e + (1 - e)) * (e * v * e + (1 - e)) = 1`: expanding, the cross terms
`(e * u * e) * (1 - e)` and `(1 - e) * (e * v * e)` vanish and `(1 - e) * (1 - e) = 1 - e` (using
`e * e = e`), while `e * u * e * v * e = e * u * v * e = e`.  Hence the left factor is invertible
and `1 = det 1 = det ((e * u * e + (1 - e)) * (e * v * e + (1 - e))) = det (e * u * e + (1 - e))
* det (e * v * e + (1 - e))`, so `det (e * u * e + (1 - e)) ≠ 0`. -/
theorem blk_det_ne_zero {n : ℕ} (e u v : Matrix (Fin n) (Fin n) ℂ) (he : e * e = e)
    (hu : u * e = e * u) (huv : u * v = 1) (hvu : v * u = 1) :
    Matrix.det (e * u * e + (1 - e)) ≠ 0 := by
  -- `u` and `v` both commute with `e`.
  have hvuv : v * e = e * v := by
    calc v * e = v * e * (u * v) := by rw [huv, mul_one]
      _ = v * (e * u) * v := by noncomm_ring
      _ = v * (u * e) * v := by rw [hu]
      _ = (v * u) * e * v := by noncomm_ring
      _ = e * v := by rw [hvu, one_mul]
  -- Two absorption identities coming from `e * e = e`.
  have hA : e * u * e * e = e * u * e := by
    rw [show e * u * e * e = (e * u) * (e * e) by noncomm_ring]
    rw [he]
  have hB : e * (e * v * e) = e * v * e := by
    rw [show e * (e * v * e) = (e * e) * (v * e) by noncomm_ring]
    rw [he]
    noncomm_ring
  have h1e : (1 - e) * e = 0 := by
    rw [sub_mul, one_mul, he, sub_self]
  -- The four terms of the expanded product.
  have h1 : e * u * e * (e * v * e) = e := by
    calc e * u * e * (e * v * e) = e * u * (e * e) * v * e := by noncomm_ring
      _ = e * u * e * v * e := by rw [he]
      _ = e * (u * e) * v * e := by noncomm_ring
      _ = e * (e * u) * v * e := by rw [hu]
      _ = e * e * u * v * e := by noncomm_ring
      _ = e * u * v * e := by rw [he]
      _ = e * (u * v) * e := by noncomm_ring
      _ = e * 1 * e := by rw [huv]
      _ = e := by rw [mul_one, he]
  have h2 : e * u * e * (1 - e) = 0 := by
    rw [mul_sub, mul_one, hA, sub_self]
  have h3 : (1 - e) * (e * v * e) = 0 := by
    rw [sub_mul, one_mul, hB, sub_self]
  have h4 : (1 - e) * (1 - e) = 1 - e := by
    rw [mul_sub, mul_one, h1e, sub_zero]
  -- The two factors are mutually inverse.
  have hAB : (e * u * e + (1 - e)) * (e * v * e + (1 - e)) = 1 := by
    rw [add_mul, mul_add, mul_add, h1, h2, h3, h4]
    noncomm_ring
  -- Hence the determinant of the left factor cannot vanish.
  have hdet : (Matrix.det (e * u * e + (1 - e))) * (Matrix.det (e * v * e + (1 - e))) = 1 := by
    rw [← Matrix.det_mul, hAB, Matrix.det_one]
  intro h
  rw [h, zero_mul] at hdet
  exact zero_ne_one hdet

end Work.KT.D2

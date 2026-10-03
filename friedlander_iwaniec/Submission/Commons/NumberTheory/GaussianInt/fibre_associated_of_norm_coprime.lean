import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Submission.Commons.NumberTheory.GaussianInt.ncard_assoc_norm_mul

set_option autoImplicit false

namespace Commons.NumberTheory.GaussianInt

open Zsqrtd

/-- **Fibres of the norm map over coprime values are associate classes.**
If `w * z = w' * z'` and `‖w‖ = ‖w'‖ = m`, `‖z‖ = ‖z'‖ = n` with `m`, `n`
coprime, then `w` and `w'` are associates. -/
theorem fibre_associated_of_norm_coprime {m n : ℕ} (hcop : Nat.Coprime m n)
    {w w' z z' : GaussianInt} (hw : w.norm.natAbs = m) (hw' : w'.norm.natAbs = m)
    (hz : z.norm.natAbs = n) (hz' : z'.norm.natAbs = n) (h : w * z = w' * z') :
    Associated w w' := by
  by_cases hm0 : m = 0
  · have hw0 : w = 0 :=
      GaussianInt.norm_eq_zero.mp (Int.natAbs_eq_zero.mp (by rw [hm0] at hw; exact hw))
    have hw'0 : w' = 0 :=
      GaussianInt.norm_eq_zero.mp (Int.natAbs_eq_zero.mp (by rw [hm0] at hw'; exact hw'))
    rw [hw0, hw'0]
  · by_cases hn0 : n = 0
    · have hm1 : m = 1 := (Nat.coprime_zero_right m).mp (by rw [← hn0]; exact hcop)
      have hu : IsUnit w := Zsqrtd.norm_eq_one_iff.mp (by rw [hm1] at hw; exact hw)
      have hu' : IsUnit w' := Zsqrtd.norm_eq_one_iff.mp (by rw [hm1] at hw'; exact hw')
      exact (associated_one_iff_isUnit.mpr hu).trans
        (associated_one_iff_isUnit.mpr hu').symm
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have h1 : Associated (gPart m (w * z)) w :=
        (gPart_mul_eq (a := w) (b := z) hm1 hn1 hcop hw hz).1
      have h2 : Associated (gPart m (w' * z')) w' :=
        (gPart_mul_eq (a := w') (b := z') hm1 hn1 hcop hw' hz').1
      rw [← h] at h2
      exact h1.symm.trans h2

end Commons.NumberTheory.GaussianInt

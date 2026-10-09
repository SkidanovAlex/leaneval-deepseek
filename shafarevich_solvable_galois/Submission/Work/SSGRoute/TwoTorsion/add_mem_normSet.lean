import Mathlib
import Submission.Work.SSGRoute.TwoTorsion.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm set of an involution is closed under addition

Let `Ω` be an algebraically closed field of characteristic zero and `c : Ω ≃+* Ω` an
involution (`c * c = 1`).  Say that `-1` is not a norm for `c`.  Then the norm set `normSet c`
(the set of `x * c x` with `x ≠ 0`) is closed under addition.

The point is that `-1 ∉ normSet c` forces a square root `i` of `-1` in `Ω` to satisfy
`c i = -i` (if `c i = i` then `-1 = i * c i` would be a norm).  Writing two norms as squares of
`c`-fixed elements, `w = m ^ 2`, `w' = m' ^ 2`, the element `x = m + i * m'` is non-zero and
`x * c x = (m + i m')(m - i m') = m ^ 2 + m' ^ 2 = w + w'`, so `w + w'` is again a norm.
-/

namespace Work.SSGRoute
namespace TwoTorsion

theorem add_mem_normSet {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (c : Ω ≃+* Ω) (hc : c * c = 1) (hneg : (-1 : Ω) ∉ normSet c)
    {w w' : Ω} (hw : w ∈ normSet c) (hw' : w' ∈ normSet c) : w + w' ∈ normSet c := by
  -- A square root of `-1`.
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_eq_mul_self (-1 : Ω)
  have hii : i * i = -1 := hi.symm
  have hi0 : i ≠ 0 := by rintro rfl; simp at hii
  -- `c i` is also a root of `X ^ 2 + 1`.
  have hcc : c i * c i = -1 := by rw [← map_mul, hii, map_neg, map_one]
  -- If `c i = i` then `-1 = i * c i` would be a norm, contradicting the hypothesis.
  have hci_ne : c i ≠ i := by
    intro h
    apply hneg
    refine ⟨i, hi0, ?_⟩
    rw [h]; exact hi
  -- Hence `c i = -i`, since `X ^ 2 + 1 = (X - i) * (X + i)` has only the roots `± i`.
  have hci : c i = -i := by
    have hprod : (c i - i) * (c i + i) = 0 := by
      have hsq : (c i - i) * (c i + i) = c i * c i - i * i := by ring
      rw [hsq, hcc, hii]; ring
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd (sub_eq_zero.mp h) hci_ne
    · exact add_eq_zero_iff_eq_neg.mp h
  -- Write both norms as squares of `c`-fixed elements.
  obtain ⟨m, hm_fix, hm0, hwm⟩ := exists_fixed_sq_of_mem_normSet hc hw
  obtain ⟨m', hm'_fix, hm'0, hw'm⟩ := exists_fixed_sq_of_mem_normSet hc hw'
  have hcx : c (m + i * m') = m - i * m' := by
    rw [map_add, map_mul, hci, hm_fix, hm'_fix]; ring
  refine ⟨m + i * m', ?_, ?_⟩
  · -- `m + i * m'` is non-zero: otherwise `x + c x = 2 * m = 0`, so `m = 0`.
    intro hx
    have hzero : m + i * m' + (m - i * m') = 0 := by
      have h' : c (m + i * m') = 0 := by rw [hx, map_zero]
      rw [hcx] at h'
      rw [hx, h', add_zero]
    have h2 : (2 : Ω) * m = 0 := by
      have hh : m + i * m' + (m - i * m') = 2 * m := by ring
      rw [← hh]; exact hzero
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (by norm_num)
    · exact hm0 h
  · -- `(m + i m') * (m - i m') = m ^ 2 + m' ^ 2 = w + w'`.
    rw [hwm, hw'm, hcx]
    have hisq : (i * m') ^ 2 = - m' ^ 2 := by rw [mul_pow, pow_two, hii]; ring
    have hfac : (m + i * m') * (m - i * m') = m ^ 2 - (i * m') ^ 2 := by ring
    rw [hfac, hisq]; ring

end TwoTorsion
end Work.SSGRoute

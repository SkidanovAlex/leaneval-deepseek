import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.TwoTorsion.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TwoTorsion

/-- `-1` is never the norm `x * c x` of a non-zero element under a non-trivial involution `c`
of an algebraically closed field of characteristic zero.

Suppose `-1 = x * c x`.  By `exists_fixed_sq_of_mem_normSet` there is then a fixed element
`m` of `c` with `m ^ 2 = -1`; this is the only place the hypothesis `IsAlgClosed` is used.  Now
let `y` be arbitrary and put `t = y - c y`, an anti-fixed element; choosing `s` with `s ^ 2 = t`
(again `IsAlgClosed`) and applying `c` gives `(c s) ^ 2 = c t = -t = -(s ^ 2)`, so
`s ^ 2 + (c s) ^ 2 = 0`.  Factoring this as `(s + m * c s) * (s - m * c s) = 0` forces
`s = m * c s` or `s = -m * c s`; in either case `c s = ± m * s`, and substituting the two
relations into each other yields `s = -s`, hence `s = 0` (characteristic zero) and therefore
`t = y - c y = 0`.  Thus every `y` is fixed by `c`, i.e. `c = 1`, contradicting `hc1`. -/
theorem neg_one_notMem_normSet {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (c : Ω ≃+* Ω) (hc : c * c = 1) (hc1 : c ≠ 1) : (-1 : Ω) ∉ normSet c := by
  intro h
  obtain ⟨m, hm, _, hmsq⟩ := exists_fixed_sq_of_mem_normSet hc h
  have hm2 : m ^ 2 = -1 := hmsq.symm
  apply hc1
  refine RingEquiv.ext fun y => ?_
  have ht_anti : c (y - c y) = -(y - c y) := by
    rw [map_sub, apply_apply hc y]; ring
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (y - c y)
  have hs_eq : s * s = y - c y := hs.symm
  have hcsq : c s * c s = -(y - c y) := by rw [← map_mul, hs_eq, ht_anti]
  have hsum : s * s + c s * c s = 0 := by rw [hs_eq, hcsq, add_neg_cancel]
  have hfac : (s + m * c s) * (s - m * c s) = 0 := by
    have h1 : (s + m * c s) * (s - m * c s) = s ^ 2 - m ^ 2 * (c s) ^ 2 := by ring
    have h2 : s ^ 2 - m ^ 2 * (c s) ^ 2 = 0 := by
      rw [hm2, neg_one_mul, sub_neg_eq_add]
      simpa [pow_two] using hsum
    rw [h1, h2]
  have hs0 : s = 0 := by
    rcases mul_eq_zero.mp hfac with h1 | h1
    · have h1c : c s + m * s = 0 := by
        have := congrArg c h1
        simp only [map_add, map_mul, map_zero, hm, apply_apply hc] at this
        exact this
      have e2 : c s = -(m * s) := (eq_neg_iff_add_eq_zero).mpr h1c
      have hmcs : m * c s = s := by
        rw [e2, mul_neg, ← mul_assoc, ← pow_two, hm2, neg_one_mul, neg_neg]
      rw [hmcs] at h1
      exact add_self_eq_zero.mp h1
    · have h1c : c s - m * s = 0 := by
        have := congrArg c h1
        simp only [map_sub, map_mul, map_zero, hm, apply_apply hc] at this
        exact this
      have e2 : c s = m * s := sub_eq_zero.mp h1c
      have hmcs : m * c s = -s := by
        rw [e2, ← mul_assoc, ← pow_two, hm2, neg_one_mul]
      rw [hmcs, sub_neg_eq_add] at h1
      exact add_self_eq_zero.mp h1
  have hyc : y - c y = 0 := by rw [← hs_eq, hs0]; ring
  exact (sub_eq_zero.mp hyc).symm

end Work.SSGRoute.TwoTorsion

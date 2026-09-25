import Mathlib

namespace Work.LT

/-- If `a.valMinAbs` and `b.valMinAbs` are both smaller than a quarter of the modulus in
absolute value, then the absolutely least residue of `a - b` is the ordinary difference
`a.valMinAbs - b.valMinAbs` (no wrap-around occurs). -/
theorem valMinAbs_sub_nowrap {n : ℕ} [NeZero n] (a b : ZMod n)
    (ha : 4 * a.valMinAbs.natAbs < n) (hb : 4 * b.valMinAbs.natAbs < n) :
    (a - b).valMinAbs = a.valMinAbs - b.valMinAbs := by
  have haI : (4 : ℤ) * |a.valMinAbs| < (n : ℤ) := by
    have h : (4 : ℤ) * (a.valMinAbs.natAbs : ℤ) < (n : ℤ) := by exact_mod_cast ha
    rwa [← Int.abs_eq_natAbs] at h
  have hbI : (4 : ℤ) * |b.valMinAbs| < (n : ℤ) := by
    have h : (4 : ℤ) * (b.valMinAbs.natAbs : ℤ) < (n : ℤ) := by exact_mod_cast hb
    rwa [← Int.abs_eq_natAbs] at h
  have key : |a.valMinAbs - b.valMinAbs| * 2 < (n : ℤ) := by
    have h1 : 2 * |a.valMinAbs| + 2 * |b.valMinAbs| < (n : ℤ) := by linarith
    have h2 : |a.valMinAbs - b.valMinAbs| ≤ |a.valMinAbs| + |b.valMinAbs| := abs_sub _ _
    linarith
  have hlt : |(a.valMinAbs - b.valMinAbs) * 2| < (n : ℤ) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℤ) ≤ 2)]
    exact key
  refine (ZMod.valMinAbs_spec (a - b) (a.valMinAbs - b.valMinAbs)).2 ⟨?_, ?_⟩
  · push_cast
    rfl
  · rw [Set.mem_Ioc]
    exact ⟨(abs_lt.1 hlt).1, (abs_lt.1 hlt).2.le⟩

end Work.LT

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

theorem one_rep_dvd (n : ℕ) (hn : 0 < n) :
    ((n : ℤ) : GaussianInt) ∣ (⟨((1 : ZMod n).val : ℤ), ((0 : ZMod n).val : ℤ)⟩ - 1) := by
  have : NeZero n := ⟨hn.ne'⟩
  have h1c : ((((1 : ZMod n).val : ℤ)) : ZMod n) = 1 := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have h0c : ((((0 : ZMod n).val : ℤ)) : ZMod n) = 0 := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hz1 : (((((1 : ZMod n).val : ℤ) - 1 : ℤ)) : ZMod n) = 0 := by
    rw [Int.cast_sub, Int.cast_one, h1c, sub_self]
  have hz0 : (((((0 : ZMod n).val : ℤ) - 0 : ℤ)) : ZMod n) = 0 := by
    rw [Int.cast_sub, Int.cast_zero, h0c, sub_self]
  rw [Zsqrtd.intCast_dvd]
  refine ⟨?_, ?_⟩
  · rw [Zsqrtd.re_sub, Zsqrtd.re_one]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp hz1
  · rw [Zsqrtd.im_sub, Zsqrtd.im_one]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp hz0

end Work.FIArea7

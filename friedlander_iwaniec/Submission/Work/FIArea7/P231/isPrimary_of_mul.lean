/-
# `Work.FIArea7.P231.isPrimary_of_mul`

*Cancellation* for the paper's primary condition (5.3)–(5.5), `Odd z.re`, `Even z.im`,
`z.im ≡ z.re - 1 (mod 4)`, i.e. `z ≡ 1 (mod (1+i)^3)`: if `e` and `e * w` are primary then so is
`w`.  (The converse, multiplicativity, is `Work.FITop3.Witness.primary_mul`.)

The proof is the elementary coordinate computation.  Write `e = a + bi`, `w = c + di`, so that

  `(e * w).re = a c - b d`,   `(e * w).im = a d + b c`.

Given `a` odd, `b` even, `b ≡ a - 1 (mod 4)` and `ac - bd` odd, `ad + bc` even,
`ad + bc ≡ ac - bd - 1 (mod 4)`, we must show `c` odd, `d` even, `d ≡ c - 1 (mod 4)`.  The parities
are immediate (an odd multiple is odd, and `a` is odd so `a d` even forces `d` even).  For the
congruence, work in `ZMod 4`: substituting `b ≡ a - 1` into the two linear relations gives

  `2 a d = c + d - 1`   in `ZMod 4`,

and since `d` is even `2 d = 0`, whence `c - 1 = d` in `ZMod 4`, i.e. `d ≡ c - 1 (mod 4)`.
-/
import Mathlib
import Submission.Work.FIPlan.Interface

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7.P231

open Zsqrtd

/-- If a product is odd then the second factor is odd. -/
private lemma odd_of_odd_mul {a b : ℤ} (hab : Odd (a * b)) : Odd b := by
  by_contra hb
  rw [Int.not_odd_iff_even] at hb
  exact (Int.not_even_iff_odd.mpr hab) (hb.mul_left a)

/-- If `a` is odd and `a * b` is even, then `b` is even. -/
private lemma even_of_odd_mul {a b : ℤ} (ha : Odd a) (hab : Even (a * b)) : Even b := by
  by_contra hb
  rw [Int.not_even_iff_odd] at hb
  exact (Int.not_odd_iff_even.mpr hab) (ha.mul hb)

theorem isPrimary_of_mul {e w : GaussianInt}
    (he : Work.FIPlan.IsPrimary e) (hew : Work.FIPlan.IsPrimary (e * w)) :
    Work.FIPlan.IsPrimary w := by
  obtain ⟨ha, hb, hbmod⟩ := he
  obtain ⟨hPodd, hQeven, hQmod⟩ := hew
  have hre : (e * w).re = e.re * w.re - e.im * w.im := by rw [Zsqrtd.re_mul]; ring
  have him : (e * w).im = e.re * w.im + e.im * w.re := by rw [Zsqrtd.im_mul]
  have hPodd' : Odd (e.re * w.re - e.im * w.im) := hre ▸ hPodd
  have hQeven' : Even (e.re * w.im + e.im * w.re) := him ▸ hQeven
  -- the real part of `w` is odd
  have hc : Odd w.re := by
    refine odd_of_odd_mul (a := e.re) ?_
    have h : Odd (e.re * w.re - e.im * w.im + e.im * w.im) :=
      hPodd'.add_even (hb.mul_right w.im)
    convert h using 1
    ring
  -- the imaginary part of `w` is even
  have hd : Even w.im := by
    refine even_of_odd_mul ha ?_
    have h : Even (e.re * w.im + e.im * w.re - e.im * w.re) :=
      hQeven'.sub (hb.mul_right w.re)
    convert h using 1
    ring
  -- the congruence, in `ZMod 4`
  have hb4 : ((e.im : ℤ) : ZMod 4) = ((e.re : ℤ) : ZMod 4) - 1 := by
    have h := (ZMod.intCast_eq_intCast_iff e.im (e.re - 1) 4).mpr hbmod
    push_cast at h
    exact h
  have hP4 : (((e * w).re : ℤ) : ZMod 4)
      = ((e.re : ℤ) : ZMod 4) * ((w.re : ℤ) : ZMod 4)
        - ((e.im : ℤ) : ZMod 4) * ((w.im : ℤ) : ZMod 4) := by
    rw [hre]; push_cast; ring
  have hQ4 : (((e * w).im : ℤ) : ZMod 4)
      = ((e.re : ℤ) : ZMod 4) * ((w.im : ℤ) : ZMod 4)
        + ((e.im : ℤ) : ZMod 4) * ((w.re : ℤ) : ZMod 4) := by
    rw [him]; push_cast; ring
  have hQeq4 : (((e * w).im : ℤ) : ZMod 4) = (((e * w).re : ℤ) : ZMod 4) - 1 := by
    have h := (ZMod.intCast_eq_intCast_iff (e * w).im ((e * w).re - 1) 4).mpr hQmod
    push_cast at h
    exact h
  have h5 : ((e.re : ℤ) : ZMod 4) * ((w.im : ℤ) : ZMod 4)
        + ((e.im : ℤ) : ZMod 4) * ((w.re : ℤ) : ZMod 4)
      = ((e.re : ℤ) : ZMod 4) * ((w.re : ℤ) : ZMod 4)
        - ((e.im : ℤ) : ZMod 4) * ((w.im : ℤ) : ZMod 4) - 1 := by
    rw [← hQ4, hQeq4, hP4]
  have key : (2 : ZMod 4) * ((e.re : ℤ) : ZMod 4) * ((w.im : ℤ) : ZMod 4)
      = ((w.re : ℤ) : ZMod 4) + ((w.im : ℤ) : ZMod 4) - 1 := by
    have h6 : ((e.re : ℤ) : ZMod 4) * ((w.im : ℤ) : ZMod 4)
          + (((e.re : ℤ) : ZMod 4) - 1) * ((w.re : ℤ) : ZMod 4)
        = ((e.re : ℤ) : ZMod 4) * ((w.re : ℤ) : ZMod 4)
          - (((e.re : ℤ) : ZMod 4) - 1) * ((w.im : ℤ) : ZMod 4) - 1 := by
      rw [← hb4]; exact h5
    linear_combination h6
  have hd4 : (2 : ZMod 4) * ((w.im : ℤ) : ZMod 4) = 0 := by
    obtain ⟨k, hk⟩ := hd
    rw [hk]
    push_cast
    rw [show (2 : ZMod 4) * ((k : ZMod 4) + (k : ZMod 4)) = (4 : ZMod 4) * (k : ZMod 4) by ring]
    rw [show (4 : ZMod 4) = 0 from ZMod.natCast_self 4, zero_mul]
  have hA : ((w.re : ℤ) : ZMod 4) + ((w.im : ℤ) : ZMod 4) - 1 = 0 := by
    have k2 : (2 : ZMod 4) * ((e.re : ℤ) : ZMod 4) * ((w.im : ℤ) : ZMod 4) = 0 := by
      rw [show (2 : ZMod 4) * ((e.re : ℤ) : ZMod 4) * ((w.im : ℤ) : ZMod 4)
            = ((e.re : ℤ) : ZMod 4) * ((2 : ZMod 4) * ((w.im : ℤ) : ZMod 4)) by ring,
          hd4, mul_zero]
    rw [← key, k2]
  have hfinal : ((w.re : ℤ) : ZMod 4) - 1 = ((w.im : ℤ) : ZMod 4) := by
    linear_combination hA - hd4
  have hdmod : w.im ≡ w.re - 1 [ZMOD 4] := by
    have h := (ZMod.intCast_eq_intCast_iff (w.re - 1) w.im 4).mp ?_
    · exact h.symm
    push_cast
    exact hfinal
  exact ⟨hc, hd, hdmod⟩

end Work.FIArea7.P231

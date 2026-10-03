/-
# `Submission.Work.FITop3.Witness.primary_mul`

The set of **primary** Gaussian integers (paper (5.3)–(5.5): `Odd z.re`, `Even z.im`,
`z.im ≡ z.re - 1 (mod 4)`, i.e. `z ≡ 1 (mod 2(1+i))`) is closed under multiplication.  This is
what lets the witness construction multiply primary primes one after another.

The arithmetic core is the elementary fact that for `a,c` odd and `b ≡ a-1`, `d ≡ c-1 (mod 4)`,

  `(a+bi)(c+di) = (ac-bd) + (ad+bc)i`,

where `ac-bd` is odd, `ad+bc` is even, and `ad+bc ≡ ac-bd-1 (mod 4)` because
`(ad+bc) - (ac-bd-1) = 2(a-1)(c-1) + ... ` vanishes modulo `4` as soon as `a`, `c` are odd.
-/
import Mathlib
import Submission.Work.FITop3.Defs3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FITop3.Witness

open Zsqrtd

/-- An odd integer reduces to `1` or `3` modulo `4`. -/
private lemma odd_cast_four {n : ℤ} (h : Odd n) : (n : ZMod 4) = 1 ∨ (n : ZMod 4) = 3 := by
  obtain ⟨k, rfl⟩ := h
  have hk : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  push_cast
  rcases hk (k : ZMod 4) with h | h | h | h <;> rw [h] <;> decide

/-- The arithmetic core of `primary_mul` on coordinates: for `a, c` odd, `b, d` even with
`b ≡ a-1` and `d ≡ c-1` mod `4`, the product coordinates `ac-bd`, `ad+bc` satisfy the primary
conditions. -/
private lemma primary_aux (a b c d : ℤ) (ha : Odd a) (hb : Even b)
    (hac : b ≡ a - 1 [ZMOD 4]) (hc : Odd c) (hd : Even d) (hdc : d ≡ c - 1 [ZMOD 4]) :
    Odd (a*c - b*d) ∧ Even (a*d + b*c) ∧
      (a*d + b*c ≡ a*c - b*d - 1 [ZMOD 4]) := by
  have h1 : (b : ZMod 4) = (a : ZMod 4) - 1 := by
    have := (ZMod.intCast_eq_intCast_iff b (a - 1) 4).mpr hac
    push_cast at this
    exact this
  have h2 : (d : ZMod 4) = (c : ZMod 4) - 1 := by
    have := (ZMod.intCast_eq_intCast_iff d (c - 1) 4).mpr hdc
    push_cast at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · have heq : a * c - b * d = a * c + (-(b * d)) := by ring
    rw [heq]
    exact (ha.mul hc).add_even ((hb.mul_right d).neg)
  · exact (hd.mul_left a).add (hb.mul_right c)
  · refine (ZMod.intCast_eq_intCast_iff (a*d + b*c) (a*c - b*d - 1) 4).mp ?_
    push_cast
    rw [h1, h2]
    rcases odd_cast_four ha with h | h <;> rcases odd_cast_four hc with h' | h' <;>
      rw [h, h'] <;> decide

theorem primary_mul {z w : GaussianInt} (hz : Work.FIPlan.IsPrimary z) (hw : Work.FIPlan.IsPrimary w) :
    Work.FIPlan.IsPrimary (z * w) := by
  obtain ⟨hzo, hze, hzc⟩ := hz
  obtain ⟨hwo, hwe, hwc⟩ := hw
  obtain ⟨h1, h2, h3⟩ := primary_aux z.re z.im w.re w.im hzo hze hzc hwo hwe hwc
  have hre : (z * w).re = z.re * w.re - z.im * w.im := by rw [Zsqrtd.re_mul]; ring
  have him : (z * w).im = z.re * w.im + z.im * w.re := by rw [Zsqrtd.im_mul]
  exact ⟨by rw [hre]; exact h1, by rw [him]; exact h2, by rw [him, hre]; exact h3⟩

end Work.FITop3.Witness

import Mathlib
import Submission.Work.IntLib.AddSub.ValLemmas

/-!
# `IntLib` / add–sub: the two value-level branch computations

* `same_val` — same sign glyphs: the magnitude sum, signed, is the value sum;
* `diff_val` — opposite sign glyphs: the borrow-chain difference with the sign of the larger
  operand is the value sum.
-/

set_option autoImplicit false

namespace Work.IntLib
namespace AddSub

open HvdH

/-- Same sign glyphs: adding the magnitudes and applying the (common) sign gives the value
`a + (if flip then -b else b)`. -/
theorem same_val (a b : ℤ) (flip : Bool) {sga sgb : Glyph} {m1 m2 : ℕ}
    (hm1 : (m1 : ℤ) = (a.natAbs : ℤ)) (hm2 : (m2 : ℤ) = (b.natAbs : ℤ))
    (ha : sga = sgnGlyph a) (heq : sga = sgb)
    (hb : sgb = (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b)) :
    sgz sga * ((m1 : ℤ) + (m2 : ℤ)) = a + (if flip then -b else b) := by
  have h1 : sgz sga * (m1 : ℤ) = a := by rw [hm1, ha, sgz_sgnGlyph_mul_natAbs]
  have h2 : sgz sga * (m2 : ℤ) = (if flip then -b else b) := by
    rw [hm2, heq, hb]
    cases flip
    · simpa using sgz_sgnGlyph_mul_natAbs b
    · simpa using sgz_flip_sgnGlyph_mul_natAbs b
  rw [mul_add, h1, h2]

/-- Opposite sign glyphs: whichever of the two borrow-chain differences is nonnegative (its
borrow is `false`) is the magnitude of the value sum, with the right sign glyph. -/
theorem diff_val (a b : ℤ) (flip : Bool) {sga sgb : Glyph} {m1 m2 n1 n2 : ℕ} {bw1 bw2 : Bool}
    (hd1 : (m1 : ℤ) = ((a.natAbs : ℤ) - (b.natAbs : ℤ)) + 2 ^ n1 * bw1.toNat)
    (hd2 : (m2 : ℤ) = -(((a.natAbs : ℤ) - (b.natAbs : ℤ))) + 2 ^ n2 * bw2.toNat)
    (hl1 : m1 < 2 ^ n1) (hl2 : m2 < 2 ^ n2)
    (ha : sga = sgnGlyph a)
    (hb : sgb = (if flip then flipGlyph (sgnGlyph b) else sgnGlyph b))
    (hne : sga ≠ sgb) :
    (bw1 = false → sgz sga * (m1 : ℤ) = a + (if flip then -b else b)) ∧
    (bw1 = true → sgz sgb * (m2 : ℤ) = a + (if flip then -b else b)) := by
  have hga : sga = Glyph.pos ∨ sga = Glyph.neg := by rw [ha]; exact sgnGlyph_cases a
  have hgb : sgb = Glyph.pos ∨ sgb = Glyph.neg := by
    rw [hb]; cases flip
    · exact sgnGlyph_cases b
    · exact flipGlyph_cases _ (sgnGlyph_cases b)
  have hsg : sgz sga = -sgz sgb := sgz_neg_of_ne hga hgb hne
  have hA : sgz sga * (a.natAbs : ℤ) = a := by rw [ha, sgz_sgnGlyph_mul_natAbs]
  have hbb : (if flip then -b else b) = sgz sgb * (b.natAbs : ℤ) := by
    rw [hb]
    cases flip
    · exact (sgz_sgnGlyph_mul_natAbs b).symm
    · exact (sgz_flip_sgnGlyph_mul_natAbs b).symm
  have hB : sgz sgb * (b.natAbs : ℤ) = (if flip then -b else b) := hbb.symm
  have hgs : sgz sgb = -sgz sga := by rw [hsg]; ring
  have hC : sgz sgb * (a.natAbs : ℤ) = -a := by rw [hgs, neg_mul, hA]
  constructor
  · intro hb1
    have hm1 : (m1 : ℤ) = (a.natAbs : ℤ) - (b.natAbs : ℤ) := by
      rw [hd1, show bw1.toNat = 0 from by simp [hb1]]; ring
    have hB' : sgz sga * (b.natAbs : ℤ) = -(if flip then -b else b) := by
      rw [hsg, hbb]; ring
    calc sgz sga * (m1 : ℤ)
        = sgz sga * ((a.natAbs : ℤ) - (b.natAbs : ℤ)) := by rw [hm1]
      _ = sgz sga * (a.natAbs : ℤ) - sgz sga * (b.natAbs : ℤ) := by ring
      _ = a - -(if flip then -b else b) := by rw [hA, hB']
      _ = a + (if flip then -b else b) := by ring
  · intro hb1
    have hbw1 : bw1.toNat = 1 := by simp [hb1]
    have hD : (a.natAbs : ℤ) - (b.natAbs : ℤ) < 0 := by
      have h : (m1 : ℤ) = ((a.natAbs : ℤ) - (b.natAbs : ℤ)) + 2 ^ n1 := by
        rw [hd1, hbw1]; ring
      have h2 : (m1 : ℤ) < ((2 ^ n1 : ℕ) : ℤ) := by exact_mod_cast hl1
      linarith
    have hbw2 : bw2 = false := by
      by_contra hc
      have hc' : bw2 = true := by simpa using hc
      have h2 : (m2 : ℤ) = -(((a.natAbs : ℤ) - (b.natAbs : ℤ))) + 2 ^ n2 := by
        rw [hd2, show bw2.toNat = 1 from by simp [hc']]; ring
      have h3 : (m2 : ℤ) < ((2 ^ n2 : ℕ) : ℤ) := by exact_mod_cast hl2
      have h4 : (0 : ℤ) < -(((a.natAbs : ℤ) - (b.natAbs : ℤ))) := by linarith
      have : ((2 ^ n2 : ℕ) : ℤ) ≤ (m2 : ℤ) := by rw [h2]; linarith
      linarith
    have hm2 : (m2 : ℤ) = (b.natAbs : ℤ) - (a.natAbs : ℤ) := by
      rw [hd2, show bw2.toNat = 0 from by simp [hbw2]]; ring
    calc sgz sgb * (m2 : ℤ)
        = sgz sgb * ((b.natAbs : ℤ) - (a.natAbs : ℤ)) := by rw [hm2]
      _ = sgz sgb * (b.natAbs : ℤ) - sgz sgb * (a.natAbs : ℤ) := by ring
      _ = (if flip then -b else b) - (-a) := by rw [hB, hC]
      _ = a + (if flip then -b else b) := by ring

end AddSub
end Work.IntLib

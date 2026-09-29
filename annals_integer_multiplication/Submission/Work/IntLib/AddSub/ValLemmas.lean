import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.ofBitsAPI
import Submission.Work.IntLib.encodeNatBridge

/-!
# `IntLib` / add–sub: value-level lemmas

Sign bookkeeping for the signed-integer words: the sign glyph of an integer, the sign flip,
and the fact that a canonical bit list `em` together with a sign glyph `sgg` is exactly the
`Val.enc` of the integer `sgz sgg * ofBits em`.
-/

set_option autoImplicit false

namespace Work.IntLib
namespace AddSub

open HvdH

/-- The integer sign represented by a sign glyph. -/
def sgz (g : Glyph) : ℤ := if g = Glyph.pos then 1 else -1

/-- The glyph-level sign flip. -/
def flipGlyph (g : Glyph) : Glyph := if g = Glyph.pos then Glyph.neg else Glyph.pos

/-- The sign glyph stored by `Val.enc`. -/
def sgnGlyph (z : ℤ) : Glyph := if z < 0 then Glyph.neg else Glyph.pos

@[simp] theorem sgz_pos : sgz Glyph.pos = 1 := rfl

@[simp] theorem sgz_neg : sgz Glyph.neg = -1 := by simp [sgz]

@[simp] theorem flipGlyph_pos : flipGlyph Glyph.pos = Glyph.neg := rfl

@[simp] theorem flipGlyph_neg : flipGlyph Glyph.neg = Glyph.pos := by simp [flipGlyph]

theorem sgz_cases (g : Glyph) : sgz g = 1 ∨ sgz g = -1 := by
  by_cases h : g = Glyph.pos
  · exact Or.inl (by simp [sgz, h])
  · exact Or.inr (by simp [sgz, h])

theorem sgnGlyph_cases (z : ℤ) : sgnGlyph z = Glyph.pos ∨ sgnGlyph z = Glyph.neg := by
  by_cases h : z < 0 <;> simp [sgnGlyph, h]

theorem flipGlyph_cases (g : Glyph) (hg : g = Glyph.pos ∨ g = Glyph.neg) :
    flipGlyph g = Glyph.pos ∨ flipGlyph g = Glyph.neg := by
  rcases hg with rfl | rfl <;> simp

theorem sgz_neg_of_ne {g g' : Glyph} (hg : g = Glyph.pos ∨ g = Glyph.neg)
    (hg' : g' = Glyph.pos ∨ g' = Glyph.neg) (hne : g ≠ g') : sgz g = -sgz g' := by
  rcases hg with rfl | rfl <;> rcases hg' with rfl | rfl <;> simp_all

/-- `natAbs` of a negative integer, as an integer equation. -/
theorem natAbs_eq_neg {z : ℤ} (h : z < 0) : (z.natAbs : ℤ) = -z := by
  have h1 : (((-z).natAbs : ℕ) : ℤ) = -z := Int.natAbs_of_nonneg (by omega)
  rwa [Int.natAbs_neg] at h1

/-! ## Sign and magnitude -/

theorem sgz_sgnGlyph_mul_natAbs (z : ℤ) : sgz (sgnGlyph z) * (z.natAbs : ℤ) = z := by
  rcases lt_or_ge z 0 with h | h
  · have hna : (z.natAbs : ℤ) = -z := natAbs_eq_neg h
    simp only [sgnGlyph, if_pos h, sgz_neg, hna]
    ring
  · have hna : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg h
    simp only [sgnGlyph, if_neg (not_lt.mpr h), sgz_pos, one_mul, hna]

theorem sgz_flip_sgnGlyph_mul_natAbs (z : ℤ) :
    sgz (flipGlyph (sgnGlyph z)) * (z.natAbs : ℤ) = -z := by
  rcases lt_or_ge z 0 with h | h
  · have hna : (z.natAbs : ℤ) = -z := natAbs_eq_neg h
    simp only [sgnGlyph, if_pos h, flipGlyph_neg, sgz_pos, one_mul, hna]
  · have hna : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg h
    simp only [sgnGlyph, if_neg (not_lt.mpr h), flipGlyph_pos, sgz_neg, hna]
    ring

theorem sgnGlyph_eq_pos_iff (z : ℤ) : sgnGlyph z = Glyph.pos ↔ 0 ≤ z := by
  by_cases h : z < 0
  · have hz : ¬ (0 ≤ z) := by omega
    simp [sgnGlyph, h, hz]
  · have hz : 0 ≤ z := by omega
    simp [sgnGlyph, h, hz]

theorem sgnGlyph_eq_neg_iff (z : ℤ) : sgnGlyph z = Glyph.neg ↔ z < 0 := by
  by_cases h : z < 0 <;> simp [sgnGlyph, h]

/-! ## From a canonical bit list to an integer value -/

@[simp] theorem ofBits_nil : ofBits ([] : List Bool) = 0 := rfl

/-- `natAbs` of a natural number, cast to `ℤ`. -/
theorem addSub_natAbs_natCast (n : ℕ) : (((n : ℤ)).natAbs) = n := by
  have h := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ (n : ℤ) by positivity)
  simpa using h

theorem enc_bits_zero : ((Glyph.pos :: [Glyph.iend]) : List Glyph) = (Val.int (0 : ℤ)).enc := by
  rw [enc_int, show ((0 : ℤ).natAbs) = 0 from rfl, encodeNat_eq_bits, Nat.zero_bits]
  rfl

theorem enc_bits_pos {m : ℕ} {em : List Bool} (h : IsBits em) (hv : ofBits em = m) :
    (Glyph.pos :: (em.map Glyph.bit ++ [Glyph.iend])) = (Val.int (m : ℤ)).enc := by
  have hem : em = m.bits := by
    have hb := bits_ofBits_of_isBits em h
    rw [hv] at hb
    exact hb.symm
  rw [enc_int, if_neg (by simp : ¬ ((m : ℤ) < 0)), addSub_natAbs_natCast m, encodeNat_eq_bits,
    ← hem]

theorem enc_bits_neg {m : ℕ} {em : List Bool} (h : IsBits em) (hv : ofBits em = m) (hm : m ≠ 0) :
    (Glyph.neg :: (em.map Glyph.bit ++ [Glyph.iend])) = (Val.int (-(m : ℤ))).enc := by
  have hem : em = m.bits := by
    have hb := bits_ofBits_of_isBits em h
    rw [hv] at hb
    exact hb.symm
  have hna : ((-(m : ℤ)).natAbs) = m := by
    rw [Int.natAbs_neg, addSub_natAbs_natCast m]
  have hneg : (-(m : ℤ)) < 0 := by
    have : (0 : ℤ) < (m : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    omega
  rw [enc_int, if_pos hneg, hna, encodeNat_eq_bits, ← hem]

/-- A canonical bit list `em` and a sign glyph `sgg` encode the integer `sgz sgg * ofBits em`:
the list built by `asw_finish` is exactly a `Val.enc`. -/
theorem enc_bits_sign {m : ℕ} {em : List Bool} (h : IsBits em) (hv : ofBits em = m)
    {sgg : Glyph} (hgg : sgg = Glyph.pos ∨ sgg = Glyph.neg) :
    (if em = [] then Glyph.pos else sgg) :: (em.map Glyph.bit ++ [Glyph.iend])
      = (Val.int (sgz sgg * (m : ℤ))).enc := by
  by_cases hm : m = 0
  · subst hm
    have hem0 : em = [] := by
      have h0 : ofBits em = 0 := hv
      exact (ofBits_eq_zero_iff_of_isBits em h).mp h0
    rw [if_pos hem0, hem0]
    simp only [List.map_nil, List.nil_append]
    rw [show sgz sgg * ((0 : ℕ) : ℤ) = 0 by simp]
    exact enc_bits_zero
  · have hemne : em ≠ [] := fun hc => hm (by rw [← hv, hc]; rfl)
    rw [if_neg hemne]
    rcases hgg with rfl | rfl
    · rw [sgz_pos, one_mul]
      exact enc_bits_pos h hv
    · rw [sgz_neg]
      simp only [neg_one_mul]
      exact enc_bits_neg h hv hm

end AddSub
end Work.IntLib

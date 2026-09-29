import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.IsqrtSpec

/-!
# `Work.CNum.MemIvS` — soundness of the mantissa-level interval square root `IvS`

`IvS I = ⟨sqrtLo I.lo, sqrtHi I.hi⟩` with `sqrtLo n = isqrt (n.toNat * SC.toNat)` and
`sqrtHi n = isqrt (n.toNat * SC.toNat) + 1`, where `isqrt` is the 70-step binary search of
`Work.CNum.Fx` (specified by `Work.CNum.IsqrtSpec` for arguments `< 2 ^ 70`).

We prove that `IvS` is a sound enclosure of the real square root: if `x ∈ I` and the lower endpoint
of `I` is nonnegative (so that `I` lies in `[0,∞)`), then `√x ∈ IvS I`, provided the mantissa
`I.hi.toNat * SC.toNat` stays below the binary-search range `2 ^ 70`.

The two halves are the two directions of `isqrt`'s specification: `isqrt n ≤ n < (isqrt n + 1)²`.
-/

namespace Work.CNum

open Work.ANum

/-! ## Elementary mantissa facts -/

lemma m2r_nonneg {n : ℤ} (h : 0 ≤ n) : 0 ≤ m2r n := by
  simp only [m2r]
  exact div_nonneg (by exact_mod_cast h) SC_posR.le

lemma m2r_pos {n : ℤ} (h : 0 < n) : 0 < m2r n := by
  simp only [m2r]
  exact div_pos (by exact_mod_cast h) SC_posR

lemma nonneg_of_m2r_nonneg {n : ℤ} (h : 0 ≤ m2r n) : 0 ≤ n := by
  have h1 : (0 : ℝ) ≤ m2r n * (SC : ℝ) := mul_nonneg h SC_posR.le
  rw [Iv.m2r_mul_SC] at h1
  exact_mod_cast h1

lemma le_of_m2r_le {a b : ℤ} (h : m2r a ≤ m2r b) : a ≤ b := by
  have h1 : (a : ℝ) ≤ (b : ℝ) := by
    have h2 := mul_le_mul_of_nonneg_right h SC_posR.le
    rwa [Iv.m2r_mul_SC, Iv.m2r_mul_SC] at h2
  exact_mod_cast h1

/-- The native cast of `a.toNat * SC.toNat` back to `ℤ` is `a * SC` for `a ≥ 0`. -/
lemma toNat_mul_SC {a : ℤ} (ha : 0 ≤ a) : ((a.toNat * SC.toNat : ℕ) : ℤ) = a * SC := by
  rw [Nat.cast_mul, Int.toNat_of_nonneg ha, Int.toNat_of_nonneg (le_of_lt SC_pos)]

/-! ## The two halves of `sqrtLo` / `sqrtHi` -/

/-- `sqrtLo a / SC ≤ √(a / SC)` for `a ≥ 0` within the binary-search range. -/
lemma sqrtLo_le {a : ℤ} (ha : 0 ≤ a) (hb : a.toNat * SC.toNat < 2 ^ 70) :
    m2r (sqrtLo a) ≤ Real.sqrt (m2r a) := by
  have haR : 0 ≤ m2r a := m2r_nonneg ha
  obtain ⟨hl, -⟩ := IsqrtSpec (a.toNat * SC.toNat) hb
  have hcast : ((isqrt (a.toNat * SC.toNat) : ℕ) : ℤ) * ((isqrt (a.toNat * SC.toNat) : ℕ) : ℤ)
      ≤ a * SC := by
    have h1 : (((isqrt (a.toNat * SC.toNat) * isqrt (a.toNat * SC.toNat) : ℕ)) : ℤ)
        ≤ ((a.toNat * SC.toNat : ℕ) : ℤ) := by exact_mod_cast hl
    rw [Nat.cast_mul, toNat_mul_SC ha] at h1
    exact h1
  have hsq : m2r (sqrtLo a) * m2r (sqrtLo a) ≤ m2r a := by
    have h3 : m2r (((isqrt (a.toNat * SC.toNat) : ℕ) : ℤ)
          * ((isqrt (a.toNat * SC.toNat) : ℕ) : ℤ)) ≤ m2r (a * SC) := m2r_le hcast
    simp only [m2r_mul, m2r_SC, mul_one] at h3
    have h4 : m2r ((isqrt (a.toNat * SC.toNat) : ℕ) : ℤ)
        * m2r ((isqrt (a.toNat * SC.toNat) : ℕ) : ℤ) ≤ m2r a :=
      le_of_mul_le_mul_left h3 SC_posR
    simpa only [sqrtLo] using h4
  have hs0 : 0 ≤ m2r (sqrtLo a) := m2r_nonneg (by simp [sqrtLo])
  rw [← pow_two] at hsq
  exact (Real.le_sqrt hs0 haR).mpr hsq

/-- `√(a / SC) ≤ sqrtHi a / SC` for `a ≥ 0` within the binary-search range. -/
lemma le_sqrtHi {a : ℤ} (ha : 0 ≤ a) (hb : a.toNat * SC.toNat < 2 ^ 70) :
    Real.sqrt (m2r a) ≤ m2r (sqrtHi a) := by
  obtain ⟨-, hu⟩ := IsqrtSpec (a.toNat * SC.toNat) hb
  have hcast : a * SC
      < (((isqrt (a.toNat * SC.toNat) : ℕ) : ℤ) + 1)
        * (((isqrt (a.toNat * SC.toNat) : ℕ) : ℤ) + 1) := by
    have h1 : ((a.toNat * SC.toNat : ℕ) : ℤ)
        < (((isqrt (a.toNat * SC.toNat) + 1 : ℕ)) : ℤ)
          * (((isqrt (a.toNat * SC.toNat) + 1 : ℕ)) : ℤ) := by exact_mod_cast hu
    rw [toNat_mul_SC ha] at h1
    simpa only [Nat.cast_add, Nat.cast_one] using h1
  have h3 : m2r a
      < m2r (((isqrt (a.toNat * SC.toNat) : ℕ) : ℤ) + 1)
        * m2r (((isqrt (a.toNat * SC.toNat) : ℕ) : ℤ) + 1) := by
    have h4 : m2r (a * SC)
        < m2r ((((isqrt (a.toNat * SC.toNat) : ℕ) : ℤ) + 1)
            * (((isqrt (a.toNat * SC.toNat) : ℕ) : ℤ) + 1)) := m2r_lt hcast
    simp only [m2r_mul, m2r_SC, mul_one] at h4
    exact lt_of_mul_lt_mul_left h4 SC_posR.le
  have hpos : 0 < m2r (((isqrt (a.toNat * SC.toNat) : ℕ) : ℤ) + 1) :=
    m2r_pos (by have := Int.natCast_nonneg (isqrt (a.toNat * SC.toNat)); linarith)
  have hfin : Real.sqrt (m2r a) < m2r (((isqrt (a.toNat * SC.toNat) : ℕ) : ℤ) + 1) :=
    (Real.sqrt_lt' hpos).mpr (by rw [pow_two]; exact h3)
  simpa only [sqrtHi, Nat.cast_add, Nat.cast_one] using le_of_lt hfin

/-! ## The main statement -/

theorem MemIvS {I : Work.ANum.Iv} {x : ℝ} (hx : Work.ANum.Iv.Mem I x) (h0 : 0 ≤ Work.ANum.m2r I.lo) (hb : I.hi.toNat * Work.ANum.SC.toNat < 2 ^ 70) : Work.ANum.Iv.Mem (IvS I) (Real.sqrt x) := by
  have hlo0 : 0 ≤ I.lo := nonneg_of_m2r_nonneg h0
  have hhiR : 0 ≤ m2r I.hi := le_trans h0 (le_trans hx.1 hx.2)
  have hhi0 : 0 ≤ I.hi := nonneg_of_m2r_nonneg hhiR
  have hle : I.lo ≤ I.hi := le_of_m2r_le (le_trans hx.1 hx.2)
  have hAN : I.lo.toNat ≤ I.hi.toNat := Int.toNat_le_toNat hle
  have hblo : I.lo.toNat * SC.toNat < 2 ^ 70 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right SC.toNat hAN) hb
  simp only [Iv.Mem, IvS]
  constructor
  · exact le_trans (sqrtLo_le hlo0 hblo) (Real.sqrt_le_sqrt hx.1)
  · exact le_trans (Real.sqrt_le_sqrt hx.2) (le_sqrtHi hhi0 hb)

end Work.CNum

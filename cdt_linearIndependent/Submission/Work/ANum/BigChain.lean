import Submission.Work.ANum.BigS2
import Submission.Work.ANum.CondEncl
import Submission.Work.ANum.ACert

/-! # The Theorem-A contour chain at scale `S` (definitions)

`Work.ANum.BigS`/`BigS2` provide a scale-parameterized copy of the interval operations (value of a
mantissa `n` at scale `S` is `m2rS S n = n/S`) and the soundness interfaces `IvHiSound S` /
`CDHiSound S` (proved in `Work.ANum.IvHiCore` / `Work.ANum.CDHiCore`).

This module re-states the Theorem-A contour chain (`Work.ANum.psiAEnclC`, the five-stage enclosure
of `psiA`) with those operations.  Nothing is proved here; the soundness statement of the chain is
`Work.ANum.psiASEncl_mem`.

Scale bookkeeping: for `S = SC · 2^k` (`SCsh k`) the *irrational* constants of the SC layer (the
rotations `RW1..RW4` and the `2π/4096` step `W4096`) are transported by multiplying the mantissas by
`2^k` (`shIv`, `shCD`), which preserves the enclosed value exactly; the *rational* constants
(`S491`, `cA1..cG4`, `cBl/cC2l/cDcl/cRC`, the circle scalings `cK`) are re-rounded directly at scale
`S` with `IvHi.ratIv S p q`. -/

namespace Work.ANum

noncomputable section

open Submission.CDTPlan Complex

/-- The mantissa `SC · 2^k`. -/
def SCsh (k : ℕ) : ℤ := SC * (2 : ℤ) ^ k

/-- Mantissa shift `n ↦ n · 2^k` (the value at scale `SC · 2^k` equals the value at scale `SC`). -/
def sh (k : ℕ) (n : ℤ) : ℤ := n * 2 ^ k

/-- Shift of an interval. -/
def shIv (k : ℕ) (I : Iv) : Iv := ⟨sh k I.lo, sh k I.hi⟩

/-- Shift of a rectangle. -/
def shCD (k : ℕ) (D : CD) : CD := ⟨shIv k D.re, shIv k D.im⟩

lemma m2rS_sh (k : ℕ) (n : ℤ) : m2rS (SCsh k) (sh k n) = m2r n := by
  simp only [m2rS, sh, SCsh, m2r]
  push_cast
  rw [mul_div_mul_right _ _ (pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0))]

lemma mem_sh {k : ℕ} {I : Iv} {x : ℝ} : IvHi.Mem (SCsh k) (shIv k I) x ↔ Iv.Mem I x := by
  simp only [IvHi.Mem, Iv.Mem, shIv, m2rS_sh]

lemma mem_shCD {k : ℕ} {D : CD} {z : ℂ} : CDHi.Mem (SCsh k) (shCD k D) z ↔ D.Mem z := by
  constructor
  · intro h
    exact ⟨(mem_sh.mp h.1), (mem_sh.mp h.2)⟩
  · intro h
    exact ⟨(mem_sh.mpr h.1), (mem_sh.mpr h.2)⟩

/-! ## The scale-`S` contour stages (expressions only) -/

/-- The radicand `A - B·w + A·w²` of a slit stage at scale `S`. -/
def slitRadS (S : ℤ) (A B : Iv) (D : CD) : CD :=
  CDHi.add (CDHi.sub (CDHi.cst A) (CDHi.mul S (CDHi.cst B) D))
    (CDHi.mul S (CDHi.cst A) (CDHi.mul S D D))

/-- Its square root (the sign-aware, rationalized `CDHi.sqrt`). -/
def slitSqrtIS (S : ℤ) (A B : Iv) (D : CD) : CD := CDHi.sqrt S (slitRadS S A B D)

/-- The numerator `A - E·w + A·w² + C(w-1)S` of a slit stage. -/
def slitNumS (S : ℤ) (A E C : Iv) (D Sq : CD) : CD :=
  CDHi.add (CDHi.add (CDHi.sub (CDHi.cst A) (CDHi.mul S (CDHi.cst E) D))
      (CDHi.mul S (CDHi.cst A) (CDHi.mul S D D)))
    (CDHi.mul S (CDHi.cst C) (CDHi.mul S (CDHi.sub D (CDHi.ONE S)) Sq))

/-- The classical slit enclosure at scale `S`. -/
def slitEnclIS (S : ℤ) (A B E C G : Iv) (D : CD) : CD :=
  CDHi.mul S (slitNumS S A E C D (slitSqrtIS S A B D))
    (CDHi.inv S (CDHi.mul S (CDHi.cst G) D))

/-- The rationalized slit denominator `A(1+w²) - Ew - C(w-1)S`. -/
def slitDenS (S : ℤ) (A E C : Iv) (D Sq : CD) : CD :=
  CDHi.sub (CDHi.sub (CDHi.mul S (CDHi.cst A) (CDHi.add (CDHi.ONE S) (CDHi.mul S D D)))
      (CDHi.mul S (CDHi.cst E) D))
    (CDHi.mul S (CDHi.cst C) (CDHi.mul S (CDHi.sub D (CDHi.ONE S)) Sq))

/-- The rationalized slit enclosure at scale `S`. -/
def slitEnclRIS (S : ℤ) (A B E C G : Iv) (D : CD) : CD :=
  CDHi.mul S (CDHi.mul S (CDHi.cst G) D)
    (CDHi.inv S (slitDenS S A E C D (slitSqrtIS S A B D)))

/-- The intersected (repaired) slit enclosure at scale `S`. -/
def slitEnclS (S : ℤ) (A B E C G : Iv) (D : CD) : CD :=
  CDHi.inter (slitEnclIS S A B E C G D) (slitEnclRIS S A B E C G D)

/-- The lune radicand `B²(1+z)² - C2·z` at scale `S`. -/
def luneRadS (S : ℤ) (B C2 : Iv) (D : CD) : CD :=
  CDHi.sub (CDHi.mul S (CDHi.mul S (CDHi.cst B) (CDHi.cst B))
      (CDHi.mul S (CDHi.add (CDHi.ONE S) D) (CDHi.add (CDHi.ONE S) D)))
    (CDHi.mul S (CDHi.cst C2) D)

/-- The lune numerator `B·z - B + S`. -/
def luneNumS (S : ℤ) (B : Iv) (D Sq : CD) : CD :=
  CDHi.add (CDHi.sub (CDHi.mul S D (CDHi.cst B)) (CDHi.cst B)) Sq

/-- The classical lune enclosure at scale `S`. -/
def luneEnclIS (S : ℤ) (B C2 Dc : Iv) (D : CD) : CD :=
  CDHi.mul S (luneNumS S B D (CDHi.sqrt S (luneRadS S B C2 D))) (CDHi.inv S (CDHi.cst Dc))

/-- The rationalized lune denominator `B(1-z) + S`. -/
def luneDenS (S : ℤ) (B : Iv) (D Sq : CD) : CD :=
  CDHi.add (CDHi.mul S (CDHi.cst B) (CDHi.sub (CDHi.ONE S) D)) Sq

/-- The rationalized lune enclosure at scale `S`. -/
def luneEnclRIS (S : ℤ) (B C2 Dc : Iv) (D : CD) : CD :=
  CDHi.mul S (CDHi.mul S (CDHi.cst Dc) D)
    (CDHi.inv S (luneDenS S B D (CDHi.sqrt S (luneRadS S B C2 D))))

/-- The intersected (repaired) lune enclosure at scale `S`. -/
def luneEnclS (S : ℤ) (B C2 Dc : Iv) (D : CD) : CD :=
  CDHi.inter (luneEnclIS S B C2 Dc D) (luneEnclRIS S B C2 Dc D)

/-! ## The per-stage inputs and the whole chain -/

/-- Input of slit stage 1: `(491/500)·D`. -/
def sIn1S (S : ℤ) (S491 : CD) (D : CD) : CD := CDHi.mul S S491 D

/-- Input of slit stage 2. -/
def sIn2S (S : ℤ) (S491 R1 : CD) (A B E C G : Iv) (D : CD) : CD :=
  CDHi.mul S R1 (slitEnclS S A B E C G (sIn1S S S491 D))

/-- Input of slit stage 3. -/
def sIn3S (S : ℤ) (S491 R1 R2 : CD) (A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 : Iv) (D : CD) : CD :=
  CDHi.mul S R2 (slitEnclS S A2 B2 E2 C2 G2 (sIn2S S S491 R1 A1 B1 E1 C1 G1 D))

/-- Input of slit stage 4. -/
def sIn4S (S : ℤ) (S491 R1 R2 R3 : CD)
    (A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 : Iv) (D : CD) : CD :=
  CDHi.mul S R3 (slitEnclS S A3 B3 E3 C3 G3
    (sIn3S S S491 R1 R2 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 D))

/-- Output of the four-slit composition (before the lune). -/
def sOut4S (S : ℤ) (S491 R1 R2 R3 R4 : CD)
    (A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 A4 B4 E4 C4 G4 : Iv) (D : CD) : CD :=
  CDHi.mul S R4 (slitEnclS S A4 B4 E4 C4 G4
    (sIn4S S S491 R1 R2 R3 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 D))

/-- The rectangle enclosure of `psiA` at scale `S` (same expression as `Work.ANum.psiAEnclC`). -/
def psiASEncl (S : ℤ) (S491 R1 R2 R3 R4 : CD)
    (A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 A4 B4 E4 C4 G4 : Iv)
    (Bl C2l Dcl RC : Iv) (D : CD) : CD :=
  CDHi.mul S (CDHi.cst RC) (luneEnclS S Bl C2l Dcl
    (sOut4S S S491 R1 R2 R3 R4 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3
      A4 B4 E4 C4 G4 D).neg)

/-! ## Binary exponentiation of a rotation at scale `S` -/

/-- Binary exponentiation of a rectangle (fuel `k`, exponent `< 2^k`). -/
def rotPowAuxS (S : ℤ) : ℕ → CD → CD → ℕ → CD
  | 0, acc, _, _ => acc
  | (k + 1), acc, b, e =>
      if e = 0 then acc
      else rotPowAuxS S k (if e % 2 = 1 then CDHi.mul S acc b else acc)
        (CDHi.mul S b b) (e / 2)

/-- `W^n` for `n < 2^14` at scale `S`. -/
def rotPow2S (S : ℤ) (W : CD) (n : ℕ) : CD := rotPowAuxS S 14 (CDHi.ONE S) W n

end

end Work.ANum

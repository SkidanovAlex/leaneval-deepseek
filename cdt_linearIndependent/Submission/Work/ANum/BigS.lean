import Mathlib
import Submission.Work.ANum.Ivl
import Submission.Work.ANum.CDisc
import Submission.Work.ANum.isqrtSpec

/-! # A second, higher-precision copy of the interval layer (scale `S` instead of `SC`)

WHY.  The ANum certificate evaluates `ψ_A` at ~10⁵ points; the fixed-point interval chain
(`Ivl`/`CDisc`/`CSqrt`) is *sound* but its accumulated rounding error at the scale `SC = 2³⁰` is
`ε ≈ 1.2·10⁻³` (mean, unit circle) — see `STATUS5.md` §1–§3, §7.  The certificate pays
`≈ 24ε/(1−R)² ≈ 650·ε` for that error, which is 0.28 of the 0.23 budget on its own; measured, the
whole certificate comes out at `11.252` instead of the lead's validated `11.041` (margin 0.16).
Recomputing the same certificate with `ε/64` gives **11.049** — so a 64× finer scale (`S = 2³⁶`)
suffices, with margin.

HOW.  `SC` is shared with area CNum (which hard-codes `SC = 2³⁰` in ~20 lemmas), so it must not be
changed unilaterally.  This module therefore *adds* a scale-parameterized copy of the operations:
every definition takes the scale `S : ℤ` explicitly and every soundness statement is about
`IvHi.Mem S`/`CDHi.Mem S`.  The proofs are verbatim copies of the corresponding `Ivl`/`CDisc`/
`CSqrt` proofs with `SC → S`; the ANum chain is then rebuilt on top at `S = 2³⁶`.

This file only *defines*; the soundness lemmas are `Work.ANum.BigSound` (delegated). -/

namespace Work.ANum

noncomputable section

/-- The real value of a mantissa at scale `S`. -/
def m2rS (S : ℤ) (n : ℤ) : ℝ := (n : ℝ) / (S : ℝ)

namespace IvHi

/-- Membership in an interval at scale `S`. -/
def Mem (S : ℤ) (I : Iv) (x : ℝ) : Prop := m2rS S I.lo ≤ x ∧ x ≤ m2rS S I.hi

/-- `⌊a b / S⌋`. -/
def mulLo (S : ℤ) (a b : ℤ) : ℤ := Int.ediv (a * b) S

/-- `⌈a b / S⌉`. -/
def mulHi (S : ℤ) (a b : ℤ) : ℤ := -Int.ediv (-(a * b)) S

/-- Addition (scale-free). -/
def add (I J : Iv) : Iv := ⟨I.lo + J.lo, I.hi + J.hi⟩

/-- Negation (scale-free). -/
def neg (I : Iv) : Iv := ⟨-I.hi, -I.lo⟩

/-- Subtraction (scale-free). -/
def sub (I J : Iv) : Iv := add I (neg J)

/-- Square, with outward rounding. -/
def sq (S : ℤ) (I : Iv) : Iv :=
  if I.lo ≤ 0 ∧ 0 ≤ I.hi then ⟨0, max (mulHi S I.lo I.lo) (mulHi S I.hi I.hi)⟩
  else ⟨min (mulLo S I.lo I.lo) (mulLo S I.hi I.hi), max (mulHi S I.lo I.lo) (mulHi S I.hi I.hi)⟩

/-- Multiplication by `1/2`. -/
def scale2 (S : ℤ) (I : Iv) : Iv := ⟨mulLo S I.lo (S / 2), mulHi S I.hi (S / 2)⟩

/-- The four-corner product. -/
def mul (S : ℤ) (I J : Iv) : Iv :=
  ⟨min (min (mulLo S I.lo J.lo) (mulLo S I.lo J.hi)) (min (mulLo S I.hi J.lo) (mulLo S I.hi J.hi)),
   max (max (mulHi S I.lo J.lo) (mulHi S I.lo J.hi)) (max (mulHi S I.hi J.lo) (mulHi S I.hi J.hi))⟩

/-- Reciprocal of a positive interval. -/
def invPos (S : ℤ) (I : Iv) : Iv := ⟨Int.ediv (S * S) I.hi, -Int.ediv (-(S * S)) I.lo⟩

/-- Clamp to be nonnegative. -/
def nonneg (I : Iv) : Iv := ⟨max I.lo 0, I.hi⟩

/-- Square root, with outward rounding (`isqrt` is scale-free). -/
def sqrt (S : ℤ) (I : Iv) : Iv :=
  ⟨(isqrt ((I.lo * S).toNat) : ℤ), (isqrt ((I.hi * S).toNat) : ℤ) + 1⟩

/-- The point interval `n/S`. -/
def pt (n : ℤ) : Iv := ⟨n, n⟩

/-- `(p/q)·S` rounded outward. -/
def ratIv (S : ℤ) (p : ℤ) (q : ℕ) : Iv :=
  ⟨Int.ediv (p * S) (q : ℤ), -Int.ediv (-(p * S)) (q : ℤ)⟩

end IvHi

namespace CDHi

/-- Membership in a complex rectangle at scale `S`. -/
def Mem (S : ℤ) (D : CD) (z : ℂ) : Prop :=
  IvHi.Mem S D.re z.re ∧ IvHi.Mem S D.im z.im

/-- Addition (scale-free). -/
def add (D E : CD) : CD := ⟨IvHi.add D.re E.re, IvHi.add D.im E.im⟩

/-- Negation (scale-free). -/
def neg (D : CD) : CD := ⟨IvHi.neg D.re, IvHi.neg D.im⟩

/-- Subtraction (scale-free). -/
def sub (D E : CD) : CD := add D (neg E)

/-- Multiplication. -/
def mul (S : ℤ) (D E : CD) : CD :=
  ⟨IvHi.sub (IvHi.mul S D.re E.re) (IvHi.mul S D.im E.im),
   IvHi.add (IvHi.mul S D.re E.im) (IvHi.mul S D.im E.re)⟩

/-- Reciprocal of a rectangle avoiding `0`. -/
def inv (S : ℤ) (D : CD) : CD :=
  ⟨IvHi.mul S D.re (IvHi.invPos S (IvHi.add (IvHi.sq S D.re) (IvHi.sq S D.im))),
   IvHi.neg (IvHi.mul S D.im (IvHi.invPos S (IvHi.add (IvHi.sq S D.re) (IvHi.sq S D.im))))⟩

/-- The argument `(‖z‖ + z.re)/2` of the real part of `√z`. -/
def sqrtArgRe (S : ℤ) (D : CD) : Iv :=
  IvHi.nonneg (IvHi.scale2 S (IvHi.add (IvHi.sqrt S (IvHi.add (IvHi.sq S D.re) (IvHi.sq S D.im))) D.re))

/-- The argument `(‖z‖ - z.re)/2` of `|Im √z|`. -/
def sqrtArgIm (S : ℤ) (D : CD) : Iv :=
  IvHi.nonneg (IvHi.scale2 S (IvHi.sub (IvHi.sqrt S (IvHi.add (IvHi.sq S D.re) (IvHi.sq S D.im))) D.re))

/-- `Re √z`. -/
def sqrtRe (S : ℤ) (D : CD) : Iv := IvHi.sqrt S (sqrtArgRe S D)

/-- The rationalized upper bound `|Im z|/(2 Re √z)` for `|Im √z|`. -/
def sqrtImAbsAux (S : ℤ) (D : CD) : ℤ :=
  -Int.ediv (-(max D.im.lo.natAbs D.im.hi.natAbs * S)) (2 * (IvHi.sqrt S (sqrtArgRe S D)).lo)

/-- `|Im √z|`, with the rationalized tightening (as in `CD.sqrtImAbsI`). -/
def sqrtImAbs (S : ℤ) (D : CD) : Iv :=
  if 0 < 2 * (IvHi.sqrt S (sqrtArgRe S D)).lo then
    ⟨(IvHi.sqrt S (sqrtArgIm S D)).lo,
      min (IvHi.sqrt S (sqrtArgIm S D)).hi (sqrtImAbsAux S D)⟩
  else IvHi.sqrt S (sqrtArgIm S D)

/-- The principal square root of a rectangle (sign-aware, with the repaired imaginary bound). -/
def sqrt (S : ℤ) (D : CD) : CD :=
  if 0 < D.im.lo then ⟨sqrtRe S D, sqrtImAbs S D⟩
  else if D.im.hi < 0 then ⟨sqrtRe S D, (sqrtImAbs S D).neg⟩
  else ⟨sqrtRe S D, ⟨-(sqrtImAbs S D).hi, (sqrtImAbs S D).hi⟩⟩

end CDHi

end

end Work.ANum

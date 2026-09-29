import Mathlib
import Submission.Work.ANum.Ivl

/-! # Complex interval (rectangle) arithmetic for the certified numerics of Theorem A

A complex enclosure is a pair of real intervals (a rectangle in `ℂ`); membership is componentwise
membership.  Built on the fixed-point library `Work.ANum.Ivl`.  This is the layer in which the
five stages of the Theorem-A contour (`slit r`, `lune c`) are evaluated per arc.

Proved here: `Mem`, `add`, `neg`, `sub`, `mul`, `inv` (for rectangles avoiding `0`), `pt`,
and a modulus bound.  The missing piece is the principal square root of a rectangle avoiding
`(-∞,0]` (see `Submission/Work/ANum/STATUS.md` for the design). -/

namespace Work.ANum

noncomputable section

/-- A complex rectangle. -/
structure CD where
  re : Iv
  im : Iv
  deriving DecidableEq, Repr

namespace CD

/-- Membership of a complex number in a rectangle. -/
def Mem (D : CD) (z : ℂ) : Prop := D.re.Mem z.re ∧ D.im.Mem z.im

theorem Mem.re {D : CD} {z : ℂ} (h : D.Mem z) : D.re.Mem z.re := h.1
theorem Mem.im {D : CD} {z : ℂ} (h : D.Mem z) : D.im.Mem z.im := h.2

/-- The point rectangle `(a + b i)/SC`. -/
def pt (a b : ℤ) : CD := ⟨Iv.pt a, Iv.pt b⟩
theorem mem_pt (a b : ℤ) : (pt a b).Mem (m2r a + m2r b * Complex.I) := by
  refine ⟨?_, ?_⟩
  · show (Iv.pt a).Mem (m2r a + m2r b * Complex.I).re
    simpa using Iv.mem_pt a
  · show (Iv.pt b).Mem (m2r a + m2r b * Complex.I).im
    simpa using Iv.mem_pt b

/-- Addition. -/
def add (D E : CD) : CD := ⟨D.re.add E.re, D.im.add E.im⟩
theorem mem_add {D E : CD} {z w : ℂ} (hz : D.Mem z) (hw : E.Mem w) :
    (add D E).Mem (z + w) := by
  refine ⟨?_, ?_⟩
  · simpa [add, Complex.add_re] using Iv.mem_add hz.1 hw.1
  · simpa [add, Complex.add_im] using Iv.mem_add hz.2 hw.2

/-- Negation. -/
def neg (D : CD) : CD := ⟨D.re.neg, D.im.neg⟩
theorem mem_neg {D : CD} {z : ℂ} (hz : D.Mem z) : (neg D).Mem (-z) := by
  refine ⟨?_, ?_⟩
  · simpa [neg, Complex.neg_re] using Iv.mem_neg hz.1
  · simpa [neg, Complex.neg_im] using Iv.mem_neg hz.2

/-- Subtraction. -/
def sub (D E : CD) : CD := add D (neg E)
theorem mem_sub {D E : CD} {z w : ℂ} (hz : D.Mem z) (hw : E.Mem w) :
    (sub D E).Mem (z - w) := by
  simpa [sub, sub_eq_add_neg] using mem_add hz (mem_neg hw)

/-- Multiplication. -/
def mul (D E : CD) : CD :=
  ⟨(D.re.mul E.re).sub (D.im.mul E.im), (D.re.mul E.im).add (D.im.mul E.re)⟩
theorem mem_mul {D E : CD} {z w : ℂ} (hz : D.Mem z) (hw : E.Mem w) :
    (mul D E).Mem (z * w) := by
  refine ⟨?_, ?_⟩
  · simpa [mul, Complex.mul_re] using Iv.mem_sub (Iv.mem_mul hz.1 hw.1) (Iv.mem_mul hz.2 hw.2)
  · simpa [mul, Complex.mul_im] using Iv.mem_add (Iv.mem_mul hz.1 hw.2) (Iv.mem_mul hz.2 hw.1)

/-- Reciprocal of a rectangle avoiding `0` (via `1/(a+bi) = (a-bi)/(a²+b²)`). -/
def inv (D : CD) : CD :=
  ⟨(D.re.mul (D.re.sq.add D.im.sq).invPos), ((D.im.mul (D.re.sq.add D.im.sq).invPos).neg)⟩

theorem mem_inv {D : CD} {z : ℂ} (hz : D.Mem z) (hpos : 0 < m2r (D.re.sq.add D.im.sq).lo) :
    (inv D).Mem (1 / z) := by
  have hden : z.re * z.re + z.im * z.im ≠ 0 := by
    have hpos' : 0 < m2r (D.re.sq.add D.im.sq).lo := hpos
    have h1 : 0 < z.re * z.re + z.im * z.im := by
      have h2 : (D.re.sq.add D.im.sq).Mem (z.re * z.re + z.im * z.im) :=
        Iv.mem_add (Iv.mem_sq hz.1) (Iv.mem_sq hz.2)
      linarith [h2.1, hpos']
    exact ne_of_gt h1
  have hdenpos : 0 < m2r (D.re.sq.add D.im.sq).lo := hpos
  refine ⟨?_, ?_⟩
  · -- real part: `z.re * (1/(z.re²+z.im²))`
    have h1 : (D.re.mul (D.re.sq.add D.im.sq).invPos).Mem
        (z.re * (1 / (z.re * z.re + z.im * z.im))) :=
      Iv.mem_mul hz.1 (Iv.mem_invPos (Iv.mem_add (Iv.mem_sq hz.1) (Iv.mem_sq hz.2)) hdenpos)
    have he : (1 / z).re = z.re * (1 / (z.re * z.re + z.im * z.im)) := by
      rw [one_div, Complex.inv_re, Complex.normSq_apply]
      ring
    rwa [he]
  · have h1 : ((D.im.mul (D.re.sq.add D.im.sq).invPos).neg).Mem
        (-(z.im * (1 / (z.re * z.re + z.im * z.im)))) :=
      Iv.mem_neg (Iv.mem_mul hz.2 (Iv.mem_invPos (Iv.mem_add (Iv.mem_sq hz.1) (Iv.mem_sq hz.2)) hdenpos))
    have he : (1 / z).im = -(z.im * (1 / (z.re * z.re + z.im * z.im))) := by
      rw [one_div, Complex.inv_im, Complex.normSq_apply]
      ring
    rwa [he]

/-- A modulus bound: if all coordinates of `D` lie in `[-K, K]` then every `z ∈ D` has
`‖z‖ ≤ √2 · m2r K`. -/
theorem mem_norm_le {D : CD} {z : ℂ} (hz : D.Mem z) {K : ℤ} (hK : 0 ≤ K)
    (h1 : D.re.hi ≤ K) (h2 : D.im.hi ≤ K) (h3 : -K ≤ D.re.lo) (h4 : -K ≤ D.im.lo) :
    ‖z‖ ≤ Real.sqrt 2 * m2r K := by
  have hK0 : 0 ≤ m2r K := by
    simp only [m2r]
    exact div_nonneg (by exact_mod_cast hK) SC_posR.le
  have hre : |z.re| ≤ m2r K := by
    rw [abs_le]
    refine ⟨?_, le_trans hz.1.2 (m2r_le h1)⟩
    rw [← m2r_neg]
    exact le_trans (m2r_le h3) hz.1.1
  have him : |z.im| ≤ m2r K := by
    rw [abs_le]
    refine ⟨?_, le_trans hz.2.2 (m2r_le h2)⟩
    rw [← m2r_neg]
    exact le_trans (m2r_le h4) hz.2.1
  have hsq : z.re * z.re + z.im * z.im ≤ 2 * (m2r K * m2r K) := by
    nlinarith [abs_nonneg z.re, abs_nonneg z.im, hre, him,
      sq_abs z.re, sq_abs z.im, hK0]
  have hnorm : ‖z‖ = Real.sqrt (z.re * z.re + z.im * z.im) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; ring_nf
  rw [hnorm, ← Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg 2) hK0)]
  apply Real.sqrt_le_sqrt
  rw [sq]
  nlinarith [hsq, hK0, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

end CD

end

end Work.ANum

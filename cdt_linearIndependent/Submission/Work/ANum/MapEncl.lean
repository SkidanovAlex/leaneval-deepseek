import Mathlib
import Submission.CDTPlan.InterfacesA
import Submission.Work.ANum.CSqrt

/-! # Per-stage rectangle enclosures of the Theorem-A contour (interface)

This module *defines* the rectangle expressions through which the five stages of
`Submission.CDTPlan.psiA` are evaluated on a complex interval.  The enclosure theorems about them
(`slitEncl_mem`, `luneEncl_mem`, …) are stated and proved in sibling modules; the numerical
constants (`1+r`, `(1+r)²`, …) are supplied as `Iv` data with their rounding hypotheses.

The point of the decomposition: `slit r` and `lune c` are built from `+`, `×`, the principal `√`
(`CD.sqrt`, proved in `Work.ANum.CSqrt`) and one reciprocal, so a rectangle enclosure is a *term*
built from the proved operations of `Work.ANum.Ivl`/`Work.ANum.CDisc`/`Work.ANum.CSqrt`. -/

namespace Work.ANum

noncomputable section

open Submission.CDTPlan Complex

/-- A real constant `v`, packaged as a complex rectangle: the interval `I` on the real axis
(`I.Mem v`). -/
def cst (I : Iv) : CD := ⟨I, Iv.pt 0⟩

theorem mem_cst {I : Iv} {v : ℝ} (h : I.Mem v) : (cst I).Mem (v : ℂ) := by
  refine ⟨?_, ?_⟩
  · show I.Mem v
    exact h
  · show (Iv.pt 0).Mem ((v : ℂ).im)
    rw [Complex.ofReal_im]
    simpa [m2r_zero] using Iv.mem_pt 0

/-- A real number enclosed by a rectangle, viewed as a complex number. -/
theorem mem_ofReal {D : CD} {v : ℝ} (h1 : D.re.Mem v) (h2 : D.im.Mem 0) : D.Mem ((v : ℂ)) := by
  refine ⟨?_, ?_⟩
  · show D.re.Mem (v : ℂ).re
    rw [Complex.ofReal_re]
    exact h1
  · show D.im.Mem (v : ℂ).im
    rw [Complex.ofReal_im]
    exact h2

/-- A real constant `v` packaged as a complex rectangle, stated for a complex `v` with `v.im = 0`
(avoids the real/complex coercion mismatch of `mem_cst` at call sites). -/
theorem mem_cst_c (I : Iv) (v : ℂ) (h1 : I.Mem v.re) (h2 : v.im = 0) : (cst I).Mem v := by
  refine ⟨?_, ?_⟩
  · show I.Mem v.re
    exact h1
  · show (Iv.pt 0).Mem v.im
    rw [h2]
    simpa [m2r_zero] using Iv.mem_pt 0

/-- The complex constant `1` (as `m2r SC`). -/
def ONE : CD := cst (Iv.pt SC)
theorem mem_ONE : ONE.Mem 1 := by
  have h : (Iv.pt SC).Mem (m2r SC) := Iv.mem_pt SC
  rw [m2r_SC] at h
  exact mem_cst h

/-- The radicand `A - B·w + A·w²` of the slit map, with `A = (1+r)²`, `B = 2(1-6r+r²)`
(so that `A - B·w = (1+r)² - 2(1-6r+r²)w` is exactly `slit`'s radicand `slitQ r w`). -/
def slitRad (A B : Iv) (D : CD) : CD :=
  ((cst A).sub ((cst B).mul D)).add ((cst A).mul (D.mul D))

/-- Its principal square root. -/
def slitSqrt (A B : Iv) (D : CD) : CD := (slitRad A B D).sqrt

/-- The numerator `A - E·w + A·w² + C·(w-1)·σ` of the slit map, with `E = 2(r-1)²`, `C = 1+r`. -/
def slitNum (A E C : Iv) (D S : CD) : CD :=
  (((cst A).sub ((cst E).mul D)).add ((cst A).mul (D.mul D))).add
    ((cst C).mul ((D.sub ONE).mul S))

/-- `slit r` over a rectangle: `S = √(A - Bw + Aw²)`, then `(A - Ew + Aw² + C(w-1)S)·(8rw)⁻¹`. -/
def slitEncl (A B E C G : Iv) (D : CD) : CD :=
  (slitNum A E C D (slitSqrt A B D)).mul (((cst G).mul D).inv)

/-- The radicand `B²(1+z)² - 16c²z` of the lune map, with `B = 1+c²`, `C2 = 16c²`. -/
def luneRad (BB C2 : Iv) (D : CD) : CD :=
  (((cst BB).mul (cst BB)).mul ((ONE.add D).mul (ONE.add D))).sub (((cst C2).mul D))

/-- Its principal square root. -/
def luneSqrt (BB C2 : Iv) (D : CD) : CD := (luneRad BB C2 D).sqrt

/-- The numerator `z·B - B + σ` of the lune map (`B = 1+c²`). -/
def luneNum (B : Iv) (D S : CD) : CD := ((D.mul (cst B)).sub (cst B)).add S

/-- `lune c` over a rectangle with `Dc = 2(c²-1)`: `(zB - B + σ)·Dc⁻¹`. -/
def luneEncl (B C2 Dc : Iv) (D : CD) : CD :=
  (luneNum B D (luneSqrt B C2 D)).mul ((cst Dc).inv)

/-- A symmetric square rectangle around `(a + b i)/SC` of radius `r/SC` (used for the arcs
`t ↦ e^{2πi t}`: the centre is a rational approximation of the midpoint, the radius covers the
arc half-length plus the approximation error). -/
def sqAround (a b r : ℤ) : CD := ⟨⟨a - r, a + r⟩, ⟨b - r, b + r⟩⟩

/-- `j`-fold product of a rectangle `W`; used for the powers of `rot (1/N)`. -/
def rotPow (W : CD) : ℕ → CD
  | 0 => ONE
  | (j + 1) => (rotPow W j).mul W

/-- `rot (a + b) = rot a * rot b`. -/
theorem rot_add (a b : ℝ) : rot (a + b) = rot a * rot b := by
  simp only [rot]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A disc of radius `m2r r` around `m2r a + m2r b·I` is contained in `sqAround a b r`. -/
theorem mem_sqAround {a b r : ℤ} (hr : 0 ≤ r) {z : ℂ}
    (h : ‖z - (m2r a + m2r b * Complex.I)‖ ≤ m2r r) : (sqAround a b r).Mem z := by
  have hrR : 0 ≤ m2r r := by
    simp only [m2r]
    exact div_nonneg (by exact_mod_cast hr) SC_posR.le
  have hre : |z.re - m2r a| ≤ m2r r := by
    have h1 := Complex.abs_re_le_norm (z - (m2r a + m2r b * Complex.I))
    have h2 : (z - (m2r a + m2r b * Complex.I)).re = z.re - m2r a := by
      simp
    rw [h2] at h1
    exact le_trans h1 h
  have him : |z.im - m2r b| ≤ m2r r := by
    have h1 := Complex.abs_im_le_norm (z - (m2r a + m2r b * Complex.I))
    have h2 : (z - (m2r a + m2r b * Complex.I)).im = z.im - m2r b := by
      simp
    rw [h2] at h1
    exact le_trans h1 h
  constructor
  · have hab := abs_le.mp hre
    constructor
    · show m2r (a - r) ≤ z.re
      rw [m2r_sub]; linarith [hab.1]
    · show z.re ≤ m2r (a + r)
      rw [m2r_add]; linarith [hab.2]
  · have hab := abs_le.mp him
    constructor
    · show m2r (b - r) ≤ z.im
      rw [m2r_sub]; linarith [hab.1]
    · show z.im ≤ m2r (b + r)
      rw [m2r_add]; linarith [hab.2]

end

end Work.ANum

namespace Work.ANum

noncomputable section

theorem m2r_ediv_two (n : ℤ) : |m2r (n / 2) - m2r n / 2| ≤ 1 / (2 * (SC : ℝ)) := by
  have h2 : (2 : ℤ) * (n / 2) + n % 2 = n := Int.mul_ediv_add_emod n 2
  have hcast : (2 : ℝ) * ((n / 2 : ℤ) : ℝ) + ((n % 2 : ℤ) : ℝ) = (n : ℝ) := by
    exact_mod_cast h2
  have hA : (2:ℝ) * ((n/2 : ℤ) : ℝ) - (n:ℝ) = -(((n % 2 : ℤ) : ℝ)) := by linarith
  have hgoal : m2r (n/2) - m2r n/2 = ((2:ℝ) * ((n/2:ℤ):ℝ) - (n:ℝ)) / (2*(SC:ℝ)) := by
    simp only [m2r]; ring
  have hR : |(((n % 2 : ℤ) : ℝ))| ≤ 1 := by
    rw [abs_le]
    constructor
    · have h : (-1 : ℤ) ≤ n % 2 := by omega
      exact_mod_cast h
    · have h : (n % 2 : ℤ) ≤ 1 := by omega
      exact_mod_cast h
  rw [hgoal, hA, neg_div, abs_neg, abs_div,
    abs_of_pos (by have := SC_posR; linarith : (0 : ℝ) < 2 * (SC : ℝ))]
  exact div_le_div_of_nonneg_right hR (by have := SC_posR; linarith)

theorem m2r_two_mul (K : ℤ) : m2r (2 * K) = 2 * m2r K := by
  simp only [m2r]; push_cast; ring

theorem m2r_one : m2r (1 : ℤ) = 1 / (SC : ℝ) := by simp [m2r]

namespace CD

/-- The centre of a rectangle (midpoints of the two sides). -/
def ctr (D : CD) : ℂ :=
  m2r ((D.re.lo + D.re.hi) / 2) + m2r ((D.im.lo + D.im.hi) / 2) * Complex.I

theorem ctr_re (D : CD) : (ctr D).re = m2r ((D.re.lo + D.re.hi) / 2) := by
  simp [ctr]
theorem ctr_im (D : CD) : (ctr D).im = m2r ((D.im.lo + D.im.hi) / 2) := by
  simp [ctr]

/-- Every point of a rectangle is within `√2 · m2r K` of its centre. -/
theorem mem_ball_ctr {D : CD} {q : ℂ} (hq : D.Mem q) {K : ℤ} (hK : 0 ≤ K)
    (hre : D.re.hi - D.re.lo + 1 ≤ 2 * K) (him : D.im.hi - D.im.lo + 1 ≤ 2 * K) :
    ‖q - ctr D‖ ≤ Real.sqrt 2 * m2r K := by
  have hK0 : 0 ≤ m2r K := div_nonneg (by exact_mod_cast hK) SC_posR.le
  have hlen_re : m2r D.re.hi - m2r D.re.lo ≤ 2 * m2r K - 1 / (SC : ℝ) := by
    have h := m2r_le hre
    rw [m2r_add, m2r_sub, m2r_one, m2r_two_mul] at h
    linarith
  have hlen_im : m2r D.im.hi - m2r D.im.lo ≤ 2 * m2r K - 1 / (SC : ℝ) := by
    have h := m2r_le him
    rw [m2r_add, m2r_sub, m2r_one, m2r_two_mul] at h
    linarith
  have hmid_re : |(ctr D).re - (m2r D.re.lo + m2r D.re.hi) / 2| ≤ 1 / (2 * (SC : ℝ)) := by
    rw [ctr_re]
    have h := m2r_ediv_two (D.re.lo + D.re.hi)
    rw [m2r_add] at h
    convert h using 2
  have hmid_im : |(ctr D).im - (m2r D.im.lo + m2r D.im.hi) / 2| ≤ 1 / (2 * (SC : ℝ)) := by
    rw [ctr_im]
    have h := m2r_ediv_two (D.im.lo + D.im.hi)
    rw [m2r_add] at h
    convert h using 2
  have hc : 1 / (SC : ℝ) = 2 * (1 / (2 * (SC : ℝ))) := by ring
  have h1 : |q.re - (ctr D).re| ≤ m2r K := by
    have hb := abs_le.mp hmid_re
    have hq1 := hq.1.1
    have hq2 := hq.1.2
    rw [hc] at hlen_re
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h3 : |q.im - (ctr D).im| ≤ m2r K := by
    have hb := abs_le.mp hmid_im
    have hq1 := hq.2.1
    have hq2 := hq.2.2
    rw [hc] at hlen_im
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hnorm : ‖q - ctr D‖ ≤ Real.sqrt 2 * m2r K := by
    have hsq : ‖q - ctr D‖ ^ 2 ≤ 2 * (m2r K * m2r K) := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      nlinarith [h1, h3, sq_abs (q.re - (ctr D).re), sq_abs (q.im - (ctr D).im),
        abs_nonneg (q.re - (ctr D).re), abs_nonneg (q.im - (ctr D).im)]
    calc ‖q - ctr D‖ = Real.sqrt (‖q - ctr D‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (2 * (m2r K * m2r K)) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt 2 * m2r K := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_mul_self hK0]
  exact hnorm

end CD

end

end Work.ANum

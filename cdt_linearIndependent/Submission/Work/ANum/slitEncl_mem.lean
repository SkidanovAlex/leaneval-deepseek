import Mathlib
import Submission.Work.ANum.MapEncl
import Submission.Work.APsi.defs

/-! # Enclosure of the slit map on a complex rectangle

`slitEncl A B E C G D` is the rectangle expression — built from the proved interval operations of
`Work.ANum.Ivl`/`Work.ANum.CDisc`/`Work.ANum.CSqrt` — that encloses `slit r w` for every `w ∈ D`,
provided the constant intervals `A, B, E, C, G` enclose `(1+r)²`, `2(1-6r+r²)`, `2(r-1)²`, `1+r`,
`8r` respectively and the denominator rectangle avoids `0` (`hden`, which also forces `w ≠ 0`).

The two algebraic facts that make this work are `slit_eq_formula` (`slit` away from `0` is the
quotient of `slitN` by `8rz`), and the identification `Complex.sqrt = ·^(1/2)` (`sqrt_eq_cpow_half`),
which makes Mathlib's `Complex.sqrt` and the `slit` definition's principal power agree. -/

namespace Work.ANum

open Submission.CDTPlan
open Work.APsi

noncomputable section

/-- `Complex.sqrt` is the principal `(1/2)`-power. -/
theorem sqrt_eq_cpow_half (z : ℂ) : Complex.sqrt z = z ^ (1 / 2 : ℂ) := by
  rw [Complex.sqrt, show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by norm_num]

/-- The rectangle `slitRad A B D` encloses the slit radicand `slitQ r w` whenever `A, B` enclose
its two coefficient constants and `D` encloses `w`. -/
theorem slitRad_mem (r : ℝ) (A B : Iv) (D : CD) {w : ℂ} (hw : D.Mem w)
    (hA : A.Mem ((1 + r) ^ 2)) (hB : B.Mem (2 * (1 - 6 * r + r ^ 2))) :
    (slitRad A B D).Mem (slitQ r w) := by
  have h1 : ((cst A).sub ((cst B).mul D)).Mem
      ((((1 + r) ^ 2 : ℝ) : ℂ) - (((2 * (1 - 6 * r + r ^ 2) : ℝ)) : ℂ) * w) :=
    CD.mem_sub (mem_cst hA) (CD.mem_mul (mem_cst hB) hw)
  have h2 : ((cst A).mul (D.mul D)).Mem ((((1 + r) ^ 2 : ℝ) : ℂ) * (w * w)) :=
    CD.mem_mul (mem_cst hA) (CD.mem_mul hw hw)
  have h3 := CD.mem_add h1 h2
  have hval : slitQ r w
      = ((((1 + r) ^ 2 : ℝ) : ℂ) - (((2 * (1 - 6 * r + r ^ 2) : ℝ)) : ℂ) * w)
        + (((1 + r) ^ 2 : ℝ) : ℂ) * (w * w) := by
    simp only [slitQ]
    push_cast
    ring
  simpa only [slitRad, hval] using h3

/-- The rectangle `slitNum A E C D S` encloses the slit numerator `slitN r w`, given `A, E, C`
enclose the coefficient constants, `D` encloses `w` and `S` encloses `√(slitQ r w)`. -/
theorem slitNum_mem (r : ℝ) (A E C : Iv) (D S : CD) {w : ℂ} (hw : D.Mem w)
    (hA : A.Mem ((1 + r) ^ 2)) (hE : E.Mem (2 * (r - 1) ^ 2)) (hC : C.Mem (1 + r))
    (hS : S.Mem (Complex.sqrt (slitQ r w))) :
    (slitNum A E C D S).Mem (slitN r w) := by
  have h1 : ((cst A).sub ((cst E).mul D)).Mem
      ((((1 + r) ^ 2 : ℝ) : ℂ) - (((2 * (r - 1) ^ 2 : ℝ)) : ℂ) * w) :=
    CD.mem_sub (mem_cst hA) (CD.mem_mul (mem_cst hE) hw)
  have h2 : ((cst A).mul (D.mul D)).Mem ((((1 + r) ^ 2 : ℝ) : ℂ) * (w * w)) :=
    CD.mem_mul (mem_cst hA) (CD.mem_mul hw hw)
  have h3 : (((cst A).sub ((cst E).mul D)).add ((cst A).mul (D.mul D))).Mem
      ((((1 + r) ^ 2 : ℝ) : ℂ) - (((2 * (r - 1) ^ 2 : ℝ)) : ℂ) * w
        + (((1 + r) ^ 2 : ℝ) : ℂ) * (w * w)) :=
    CD.mem_add h1 h2
  have h4 : ((cst C).mul ((D.sub ONE).mul S)).Mem
      ((((1 + r : ℝ)) : ℂ) * ((w - 1) * Complex.sqrt (slitQ r w))) :=
    CD.mem_mul (mem_cst hC) (CD.mem_mul (CD.mem_sub hw mem_ONE) hS)
  have h5 := CD.mem_add h3 h4
  have hval : slitN r w
      = ((((1 + r) ^ 2 : ℝ) : ℂ) - (((2 * (r - 1) ^ 2 : ℝ)) : ℂ) * w
          + (((1 + r) ^ 2 : ℝ) : ℂ) * (w * w))
        + ((((1 + r : ℝ)) : ℂ) * ((w - 1) * Complex.sqrt (slitQ r w))) := by
    rw [sqrt_eq_cpow_half, slitN, slitP, slitR]
    push_cast
    ring
  simpa only [slitNum, hval] using h5

theorem slitEncl_mem (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (A B E C G : Iv) (D : CD) {w : ℂ}
    (hw : D.Mem w) (hA : A.Mem ((1 + r) ^ 2)) (hB : B.Mem (2 * (1 - 6 * r + r ^ 2)))
    (hE : E.Mem (2 * (r - 1) ^ 2)) (hC : C.Mem (1 + r)) (hG : G.Mem (8 * r))
    (hRlo : 0 ≤ m2r ((slitRad A B D).re.sq.add (slitRad A B D).im.sq).lo)
    (hRhi : 0 ≤ m2r ((slitRad A B D).re.sq.add (slitRad A B D).im.sq).hi)
    (hPhi : 0 ≤ m2r (CD.sqrtArgRe (slitRad A B D)).hi)
    (hQhi : 0 ≤ m2r (CD.sqrtArgIm (slitRad A B D)).hi)
    (hSP : ∀ u : ℂ, (slitRad A B D).Mem u → u ∈ Complex.slitPlane)
    (hden : 0 < m2r ((((cst G).mul D).re.sq).add (((cst G).mul D).im.sq)).lo) :
    (slitEncl A B E C G D).Mem (slit r w) := by
  -- the denominator rectangle is invertible, hence `w ≠ 0`
  have hGmem : ((cst G).mul D).Mem (((8 * r : ℝ) : ℂ) * w) :=
    CD.mem_mul (mem_cst hG) hw
  have hwne : w ≠ 0 := by
    have hpos : 0 < (((8 * r : ℝ) : ℂ) * w).re * (((8 * r : ℝ) : ℂ) * w).re
        + (((8 * r : ℝ) : ℂ) * w).im * (((8 * r : ℝ) : ℂ) * w).im :=
      lt_of_lt_of_le hden (Iv.mem_add (Iv.mem_sq hGmem.1) (Iv.mem_sq hGmem.2)).1
    intro h0
    rw [h0, mul_zero] at hpos
    simp at hpos
  -- the radicand, its square root, the numerator and the reciprocal
  have hrad : (slitRad A B D).Mem (slitQ r w) := slitRad_mem r A B D hw hA hB
  have hsqrt : (slitSqrt A B D).Mem (Complex.sqrt (slitQ r w)) :=
    CD.mem_sqrt hrad (hSP _ hrad) hRlo hRhi hPhi hQhi
  have hnum : (slitNum A E C D (slitSqrt A B D)).Mem (slitN r w) :=
    slitNum_mem r A E C D (slitSqrt A B D) hw hA hE hC hsqrt
  have hinv : (((cst G).mul D).inv).Mem (1 / (((8 * r : ℝ) : ℂ) * w)) :=
    CD.mem_inv hGmem hden
  have hprod : (slitEncl A B E C G D).Mem
      (slitN r w * (1 / (((8 * r : ℝ) : ℂ) * w))) :=
    CD.mem_mul hnum hinv
  -- identify the enclosed value with `slit r w`
  have h8 : (((8 * r : ℝ)) : ℂ) = 8 * (r : ℂ) := by push_cast; ring
  have hval : slitN r w * (1 / (((8 * r : ℝ) : ℂ) * w)) = slit r w := by
    rw [slit_eq_formula r w hwne, h8]
    simp only [div_eq_mul_inv, one_mul]
  rwa [hval] at hprod

end

end Work.ANum

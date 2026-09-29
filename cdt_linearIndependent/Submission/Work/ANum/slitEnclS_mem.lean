import Mathlib
import Submission.Work.ANum.BigChain

namespace Work.ANum

open Submission.CDTPlan Complex
open Work.APsi

noncomputable section

/-- The rectangle `slitRadS S A B D` encloses the slit radicand `slitQ r w`. -/
theorem slitEnclS_rad_mem (S : ℤ) (hCD : CDHiSound S) (r : ℝ) (A B : Iv) (D : CD) {w : ℂ}
    (hw : CDHi.Mem S D w) (hA : IvHi.Mem S A ((1 + r) ^ 2))
    (hB : IvHi.Mem S B (2 * (1 - 6 * r + r ^ 2))) :
    CDHi.Mem S (slitRadS S A B D) (slitQ r w) := by
  have h1 : CDHi.Mem S (CDHi.sub (CDHi.cst A) (CDHi.mul S (CDHi.cst B) D))
      ((((1 + r) ^ 2 : ℝ) : ℂ) - (((2 * (1 - 6 * r + r ^ 2) : ℝ)) : ℂ) * w) :=
    hCD.mem_sub (hCD.mem_cst hA) (hCD.mem_mul (hCD.mem_cst hB) hw)
  have h2 : CDHi.Mem S (CDHi.mul S (CDHi.cst A) (CDHi.mul S D D))
      ((((1 + r) ^ 2 : ℝ) : ℂ) * (w * w)) :=
    hCD.mem_mul (hCD.mem_cst hA) (hCD.mem_mul hw hw)
  have h3 := hCD.mem_add h1 h2
  have hval : slitQ r w = ((((1 + r) ^ 2 : ℝ) : ℂ)
        - (((2 * (1 - 6 * r + r ^ 2) : ℝ)) : ℂ) * w)
      + (((1 + r) ^ 2 : ℝ) : ℂ) * (w * w) := by
    simp only [slitQ]
    push_cast
    ring
  simpa only [slitRadS, hval] using h3

/-- The rectangle `slitSqrtIS S A B D` encloses `√(slitQ r w)`. -/
theorem slitEnclS_sqrt_mem (S : ℤ) (hCD : CDHiSound S) (r : ℝ) (A B : Iv) (D : CD) {w : ℂ}
    (hw : CDHi.Mem S D w) (hA : IvHi.Mem S A ((1 + r) ^ 2))
    (hB : IvHi.Mem S B (2 * (1 - 6 * r + r ^ 2)))
    (hRlo : 0 ≤ m2rS S (IvHi.add (IvHi.sq S (slitRadS S A B D).re)
      (IvHi.sq S (slitRadS S A B D).im)).lo)
    (hRhi : 0 ≤ m2rS S (IvHi.add (IvHi.sq S (slitRadS S A B D).re)
      (IvHi.sq S (slitRadS S A B D).im)).hi)
    (hPhi : 0 ≤ m2rS S (CDHi.sqrtArgRe S (slitRadS S A B D)).hi)
    (hQhi : 0 ≤ m2rS S (CDHi.sqrtArgIm S (slitRadS S A B D)).hi)
    (hSP : ∀ u : ℂ, CDHi.Mem S (slitRadS S A B D) u → u ∈ Complex.slitPlane) :
    CDHi.Mem S (slitSqrtIS S A B D) (Complex.sqrt (slitQ r w)) := by
  have hrad : CDHi.Mem S (slitRadS S A B D) (slitQ r w) :=
    slitEnclS_rad_mem S hCD r A B D hw hA hB
  have h := hCD.mem_sqrt hrad (hSP _ hrad) hRlo hRhi hPhi hQhi
  simpa only [slitSqrtIS] using h

/-- The rectangle `slitNumS S A E C D Sq` encloses the slit numerator `slitN r w`. -/
theorem slitEnclS_num_mem (S : ℤ) (hCD : CDHiSound S) (r : ℝ) (A E C : Iv) (D Sq : CD) {w : ℂ}
    (hw : CDHi.Mem S D w) (hA : IvHi.Mem S A ((1 + r) ^ 2))
    (hE : IvHi.Mem S E (2 * (r - 1) ^ 2)) (hC : IvHi.Mem S C (1 + r))
    (hSq : CDHi.Mem S Sq (Complex.sqrt (slitQ r w))) :
    CDHi.Mem S (slitNumS S A E C D Sq) (slitN r w) := by
  have h1 : CDHi.Mem S (CDHi.sub (CDHi.cst A) (CDHi.mul S (CDHi.cst E) D))
      ((((1 + r) ^ 2 : ℝ) : ℂ) - (((2 * (r - 1) ^ 2 : ℝ)) : ℂ) * w) :=
    hCD.mem_sub (hCD.mem_cst hA) (hCD.mem_mul (hCD.mem_cst hE) hw)
  have h2 : CDHi.Mem S (CDHi.mul S (CDHi.cst A) (CDHi.mul S D D))
      ((((1 + r) ^ 2 : ℝ) : ℂ) * (w * w)) :=
    hCD.mem_mul (hCD.mem_cst hA) (hCD.mem_mul hw hw)
  have h3 : CDHi.Mem S
      (CDHi.add (CDHi.sub (CDHi.cst A) (CDHi.mul S (CDHi.cst E) D))
        (CDHi.mul S (CDHi.cst A) (CDHi.mul S D D)))
      ((((1 + r) ^ 2 : ℝ) : ℂ) - (((2 * (r - 1) ^ 2 : ℝ)) : ℂ) * w
        + (((1 + r) ^ 2 : ℝ) : ℂ) * (w * w)) :=
    hCD.mem_add h1 h2
  have h4 : CDHi.Mem S (CDHi.mul S (CDHi.cst C) (CDHi.mul S (CDHi.sub D (CDHi.ONE S)) Sq))
      ((((1 + r : ℝ)) : ℂ) * ((w - 1) * Complex.sqrt (slitQ r w))) :=
    hCD.mem_mul (hCD.mem_cst hC) (hCD.mem_mul (hCD.mem_sub hw hCD.mem_ONE) hSq)
  have h5 := hCD.mem_add h3 h4
  have hval : slitN r w
      = ((((1 + r) ^ 2 : ℝ) : ℂ) - (((2 * (r - 1) ^ 2 : ℝ)) : ℂ) * w
          + (((1 + r) ^ 2 : ℝ) : ℂ) * (w * w))
        + ((((1 + r : ℝ)) : ℂ) * ((w - 1) * Complex.sqrt (slitQ r w))) := by
    rw [sqrt_eq_cpow_half, slitN, slitP, slitR]
    push_cast
    ring
  simpa only [slitNumS, hval] using h5

/-- The rectangle `slitDenS S A E C D Sq` encloses `slitP r w - slitR r w`. -/
theorem slitEnclS_den_mem (S : ℤ) (hCD : CDHiSound S) (r : ℝ) (A E C : Iv) (D Sq : CD) {w : ℂ}
    (hw : CDHi.Mem S D w) (hA : IvHi.Mem S A ((1 + r) ^ 2))
    (hE : IvHi.Mem S E (2 * (r - 1) ^ 2)) (hC : IvHi.Mem S C (1 + r))
    (hSq : CDHi.Mem S Sq (Complex.sqrt (slitQ r w))) :
    CDHi.Mem S (slitDenS S A E C D Sq) (slitP r w - slitR r w) := by
  have hSq' : CDHi.Mem S Sq ((slitQ r w) ^ (1 / 2 : ℂ)) := by
    rwa [sqrt_eq_cpow_half] at hSq
  have h1 : CDHi.Mem S (CDHi.mul S (CDHi.cst A) (CDHi.add (CDHi.ONE S) (CDHi.mul S D D)))
      ((((1 + r) ^ 2 : ℝ) : ℂ) * (1 + w * w)) :=
    hCD.mem_mul (hCD.mem_cst hA) (hCD.mem_add hCD.mem_ONE (hCD.mem_mul hw hw))
  have h2 : CDHi.Mem S (CDHi.mul S (CDHi.cst E) D)
      ((((2 * (r - 1) ^ 2 : ℝ)) : ℂ) * w) :=
    hCD.mem_mul (hCD.mem_cst hE) hw
  have h4 : CDHi.Mem S (CDHi.mul S (CDHi.cst C) (CDHi.mul S (CDHi.sub D (CDHi.ONE S)) Sq))
      ((((1 + r : ℝ)) : ℂ) * ((w - 1) * (slitQ r w) ^ (1 / 2 : ℂ))) :=
    hCD.mem_mul (hCD.mem_cst hC) (hCD.mem_mul (hCD.mem_sub hw hCD.mem_ONE) hSq')
  have h5 := hCD.mem_sub (hCD.mem_sub h1 h2) h4
  have hval : slitP r w - slitR r w =
      ((((1 + r) ^ 2 : ℝ) : ℂ) * (1 + w * w)) - ((((2 * (r - 1) ^ 2 : ℝ)) : ℂ) * w)
        - ((((1 + r : ℝ)) : ℂ) * ((w - 1) * (slitQ r w) ^ (1 / 2 : ℂ))) := by
    simp only [slitP, slitR]
    push_cast
    ring
  simpa only [slitDenS, hval] using h5

/-- **Soundness of the classical scale-`S` slit enclosure `slitEnclIS`.** -/
theorem slitEnclIS_mem (S : ℤ) (hIv : IvHiSound S) (hCD : CDHiSound S)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (A B E C G : Iv) (D : CD) {w : ℂ}
    (hw : CDHi.Mem S D w) (hA : IvHi.Mem S A ((1 + r) ^ 2))
    (hB : IvHi.Mem S B (2 * (1 - 6 * r + r ^ 2)))
    (hE : IvHi.Mem S E (2 * (r - 1) ^ 2)) (hC : IvHi.Mem S C (1 + r))
    (hG : IvHi.Mem S G (8 * r))
    (hRlo : 0 ≤ m2rS S (IvHi.add (IvHi.sq S (slitRadS S A B D).re)
      (IvHi.sq S (slitRadS S A B D).im)).lo)
    (hRhi : 0 ≤ m2rS S (IvHi.add (IvHi.sq S (slitRadS S A B D).re)
      (IvHi.sq S (slitRadS S A B D).im)).hi)
    (hPhi : 0 ≤ m2rS S (CDHi.sqrtArgRe S (slitRadS S A B D)).hi)
    (hQhi : 0 ≤ m2rS S (CDHi.sqrtArgIm S (slitRadS S A B D)).hi)
    (hSP : ∀ u : ℂ, CDHi.Mem S (slitRadS S A B D) u → u ∈ Complex.slitPlane)
    (hden : 0 < m2rS S (IvHi.add (IvHi.sq S (CDHi.mul S (CDHi.cst G) D).re)
      (IvHi.sq S (CDHi.mul S (CDHi.cst G) D).im)).lo) :
    CDHi.Mem S (slitEnclIS S A B E C G D) (slit r w) := by
  have hGmem : CDHi.Mem S (CDHi.mul S (CDHi.cst G) D) (((8 * r : ℝ) : ℂ) * w) :=
    hCD.mem_mul (hCD.mem_cst hG) hw
  have hwne : w ≠ 0 := by
    have hpos : 0 < (((8 * r : ℝ) : ℂ) * w).re * (((8 * r : ℝ) : ℂ) * w).re
        + (((8 * r : ℝ) : ℂ) * w).im * (((8 * r : ℝ) : ℂ) * w).im :=
      lt_of_lt_of_le hden (hIv.mem_add (hIv.mem_sq hGmem.1) (hIv.mem_sq hGmem.2)).1
    intro h0
    rw [h0, mul_zero] at hpos
    simp at hpos
  have hsqrt : CDHi.Mem S (slitSqrtIS S A B D) (Complex.sqrt (slitQ r w)) :=
    slitEnclS_sqrt_mem S hCD r A B D hw hA hB hRlo hRhi hPhi hQhi hSP
  have hnum : CDHi.Mem S (slitNumS S A E C D (slitSqrtIS S A B D)) (slitN r w) :=
    slitEnclS_num_mem S hCD r A E C D (slitSqrtIS S A B D) hw hA hE hC hsqrt
  have hinv : CDHi.Mem S (CDHi.inv S (CDHi.mul S (CDHi.cst G) D))
      (1 / (((8 * r : ℝ) : ℂ) * w)) :=
    hCD.mem_inv hGmem hden
  have hprod : CDHi.Mem S (slitEnclIS S A B E C G D)
      (slitN r w * (1 / (((8 * r : ℝ) : ℂ) * w))) :=
    hCD.mem_mul hnum hinv
  have h8 : (((8 * r : ℝ)) : ℂ) = 8 * (r : ℂ) := by push_cast; ring
  have hval : slitN r w * (1 / (((8 * r : ℝ) : ℂ) * w)) = slit r w := by
    rw [slit_eq_formula r w hwne, h8]
    simp only [div_eq_mul_inv, one_mul]
  rwa [hval] at hprod

/-- **Soundness of the rationalized scale-`S` slit enclosure `slitEnclRIS`.** -/
theorem slitEnclRIS_mem (S : ℤ) (hIv : IvHiSound S) (hCD : CDHiSound S)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (A B E C G : Iv) (D : CD) {w : ℂ}
    (hw : CDHi.Mem S D w) (hA : IvHi.Mem S A ((1 + r) ^ 2))
    (hB : IvHi.Mem S B (2 * (1 - 6 * r + r ^ 2)))
    (hE : IvHi.Mem S E (2 * (r - 1) ^ 2)) (hC : IvHi.Mem S C (1 + r))
    (hG : IvHi.Mem S G (8 * r))
    (hRlo : 0 ≤ m2rS S (IvHi.add (IvHi.sq S (slitRadS S A B D).re)
      (IvHi.sq S (slitRadS S A B D).im)).lo)
    (hRhi : 0 ≤ m2rS S (IvHi.add (IvHi.sq S (slitRadS S A B D).re)
      (IvHi.sq S (slitRadS S A B D).im)).hi)
    (hPhi : 0 ≤ m2rS S (CDHi.sqrtArgRe S (slitRadS S A B D)).hi)
    (hQhi : 0 ≤ m2rS S (CDHi.sqrtArgIm S (slitRadS S A B D)).hi)
    (hSP : ∀ u : ℂ, CDHi.Mem S (slitRadS S A B D) u → u ∈ Complex.slitPlane)
    (hdenR : 0 < m2rS S (IvHi.add
      (IvHi.sq S (slitDenS S A E C D (slitSqrtIS S A B D)).re)
      (IvHi.sq S (slitDenS S A E C D (slitSqrtIS S A B D)).im)).lo) :
    CDHi.Mem S (slitEnclRIS S A B E C G D) (slit r w) := by
  have hsqrt : CDHi.Mem S (slitSqrtIS S A B D) (Complex.sqrt (slitQ r w)) :=
    slitEnclS_sqrt_mem S hCD r A B D hw hA hB hRlo hRhi hPhi hQhi hSP
  have hden : CDHi.Mem S (slitDenS S A E C D (slitSqrtIS S A B D)) (slitP r w - slitR r w) :=
    slitEnclS_den_mem S hCD r A E C D (slitSqrtIS S A B D) hw hA hE hC hsqrt
  have hinv : CDHi.Mem S (CDHi.inv S (slitDenS S A E C D (slitSqrtIS S A B D)))
      (1 / (slitP r w - slitR r w)) :=
    hCD.mem_inv hden hdenR
  have hnum : CDHi.Mem S (CDHi.mul S (CDHi.cst G) D) (((8 * r : ℝ) : ℂ) * w) :=
    hCD.mem_mul (hCD.mem_cst hG) hw
  have hprod := hCD.mem_mul hnum hinv
  have hval : ((((8 * r : ℝ) : ℂ) * w) * (1 / (slitP r w - slitR r w))) = slit r w := by
    rw [slit_den_formula r (ne_of_gt hr) w, div_eq_mul_inv]
    push_cast
    ring
  rwa [hval] at hprod

end


/-- **Soundness of the scale-`S` slit stage** (the scale-`S` analogue of
`Work.ANum.slitEncl2_mem`/`slitEncl3_mem`): if `D ∋ w` and the constants enclose `(1+r)²`,
`2(1-6r+r²)`, `2(r-1)²`, `1+r`, `8r`, and the numerical side conditions hold, then the intersected
enclosure `slitEnclS S A B E C G D` contains `slit r w`. -/
theorem slitEnclS_mem (S : ℤ) (hS : 0 < S) (hIv : Work.ANum.IvHiSound S)
    (hCD : Work.ANum.CDHiSound S)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (A B E C G : Work.ANum.Iv) (D : Work.ANum.CD) {w : ℂ}
    (hw : Work.ANum.CDHi.Mem S D w) (hA : Work.ANum.IvHi.Mem S A ((1 + r) ^ 2))
    (hB : Work.ANum.IvHi.Mem S B (2 * (1 - 6 * r + r ^ 2)))
    (hE : Work.ANum.IvHi.Mem S E (2 * (r - 1) ^ 2))
    (hC : Work.ANum.IvHi.Mem S C (1 + r)) (hG : Work.ANum.IvHi.Mem S G (8 * r))
    (hRlo : 0 ≤ Work.ANum.m2rS S (Work.ANum.IvHi.add
      (Work.ANum.IvHi.sq S (Work.ANum.CD.re (Work.ANum.slitRadS S A B D)))
      (Work.ANum.IvHi.sq S (Work.ANum.CD.im (Work.ANum.slitRadS S A B D)))).lo)
    (hRhi : 0 ≤ Work.ANum.m2rS S (Work.ANum.IvHi.add
      (Work.ANum.IvHi.sq S (Work.ANum.CD.re (Work.ANum.slitRadS S A B D)))
      (Work.ANum.IvHi.sq S (Work.ANum.CD.im (Work.ANum.slitRadS S A B D)))).hi)
    (hPhi : 0 ≤ Work.ANum.m2rS S (Work.ANum.CDHi.sqrtArgRe S (Work.ANum.slitRadS S A B D)).hi)
    (hQhi : 0 ≤ Work.ANum.m2rS S (Work.ANum.CDHi.sqrtArgIm S (Work.ANum.slitRadS S A B D)).hi)
    (hSP : ∀ u : ℂ, Work.ANum.CDHi.Mem S (Work.ANum.slitRadS S A B D) u →
      u ∈ Complex.slitPlane)
    (hden : 0 < Work.ANum.m2rS S (Work.ANum.IvHi.add
      (Work.ANum.IvHi.sq S (Work.ANum.CD.re (Work.ANum.CDHi.mul S (Work.ANum.CDHi.cst G) D)))
      (Work.ANum.IvHi.sq S (Work.ANum.CD.im (Work.ANum.CDHi.mul S (Work.ANum.CDHi.cst G) D)))).lo)
    (hdenR : 0 < Work.ANum.m2rS S (Work.ANum.IvHi.add
      (Work.ANum.IvHi.sq S (Work.ANum.CD.re (Work.ANum.slitDenS S A E C D
        (Work.ANum.slitSqrtIS S A B D))))
      (Work.ANum.IvHi.sq S (Work.ANum.CD.im (Work.ANum.slitDenS S A E C D
        (Work.ANum.slitSqrtIS S A B D))))).lo) :
    Work.ANum.CDHi.Mem S (Work.ANum.slitEnclS S A B E C G D)
      (Submission.CDTPlan.slit r w) := by
  have key : Work.ANum.CDHi.Mem S (Work.ANum.slitEnclS S A B E C G D) (Submission.CDTPlan.slit r w) :=
    hCD.mem_inter
      (slitEnclIS_mem S hIv hCD r hr hr1 A B E C G D hw hA hB hE hC hG
        hRlo hRhi hPhi hQhi hSP hden)
      (slitEnclRIS_mem S hIv hCD r hr hr1 A B E C G D hw hA hB hE hC hG
        hRlo hRhi hPhi hQhi hSP hdenR)
  exact key

end Work.ANum

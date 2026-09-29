import Mathlib
import Submission.Work.ANum.BigChain

namespace Work.ANum

open Submission.CDTPlan Complex
open Work.APsi

noncomputable section

/-! # Soundness of the scale-`S` lune enclosure

This is the scale-`S` analogue of `Work.ANum.psiAEnclC_luneEnclI_mem` /
`Work.ANum.psiAEnclC_luneEnclRI_mem` / `Work.ANum.psiAEnclC_luneEncl3_mem`: the same chain of
`CDHi`/`IvHi` soundness facts applied to `luneRadS`, `luneNumS`, `luneDenS`, `luneEnclIS`,
`luneEnclRIS` and `luneEnclS` (the scale-parameterized copy of the Theorem-A contour chain built in
`Submission.Work.ANum.BigChain`).

Mirrors the structure of the sibling `Submission.Work.ANum.slitEnclS_mem`. -/

/-- The rectangle `luneRadS S B C2 D` encloses the lune radicand `B²(1+z)² - 16c²z`. -/
theorem luneEnclS_rad_mem (S : ℤ) (hCD : CDHiSound S) (c : ℝ) (B C2 : Iv) (D : CD) {z : ℂ}
    (hz : CDHi.Mem S D z) (hB : IvHi.Mem S B (1 + c ^ 2)) (hC2 : IvHi.Mem S C2 (16 * c ^ 2)) :
    CDHi.Mem S (luneRadS S B C2 D)
      (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ) * ((1 + z) * (1 + z)) -
        ((16 * c ^ 2 : ℝ) : ℂ) * z) := by
  have h1 : CDHi.Mem S (CDHi.cst B) (((1 + c ^ 2 : ℝ) : ℂ)) := hCD.mem_cst hB
  have h2 : CDHi.Mem S (CDHi.cst C2) (((16 * c ^ 2 : ℝ) : ℂ)) := hCD.mem_cst hC2
  have h1z : CDHi.Mem S (CDHi.add (CDHi.ONE S) D) (1 + z) := hCD.mem_add hCD.mem_ONE hz
  have hBB : CDHi.Mem S
      (CDHi.mul S (CDHi.mul S (CDHi.cst B) (CDHi.cst B))
        (CDHi.mul S (CDHi.add (CDHi.ONE S) D) (CDHi.add (CDHi.ONE S) D)))
      (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ) * ((1 + z) * (1 + z))) :=
    hCD.mem_mul (hCD.mem_mul h1 h1) (hCD.mem_mul h1z h1z)
  have hC2z : CDHi.Mem S (CDHi.mul S (CDHi.cst C2) D) (((16 * c ^ 2 : ℝ) : ℂ) * z) :=
    hCD.mem_mul h2 hz
  have h := hCD.mem_sub hBB hC2z
  simpa only [luneRadS] using h

/-- The rectangle `CDHi.sqrt S (luneRadS S B C2 D)` encloses `√(B²(1+z)² - 16c²z)`. -/
theorem luneEnclS_sqrt_mem (S : ℤ) (hCD : CDHiSound S) (c : ℝ) (B C2 : Iv) (D : CD) {z : ℂ}
    (hz : CDHi.Mem S D z) (hB : IvHi.Mem S B (1 + c ^ 2)) (hC2 : IvHi.Mem S C2 (16 * c ^ 2))
    (hRlo : 0 ≤ m2rS S (IvHi.add (IvHi.sq S (luneRadS S B C2 D).re)
      (IvHi.sq S (luneRadS S B C2 D).im)).lo)
    (hRhi : 0 ≤ m2rS S (IvHi.add (IvHi.sq S (luneRadS S B C2 D).re)
      (IvHi.sq S (luneRadS S B C2 D).im)).hi)
    (hPhi : 0 ≤ m2rS S (CDHi.sqrtArgRe S (luneRadS S B C2 D)).hi)
    (hQhi : 0 ≤ m2rS S (CDHi.sqrtArgIm S (luneRadS S B C2 D)).hi)
    (hSP : ∀ u : ℂ, CDHi.Mem S (luneRadS S B C2 D) u → u ∈ Complex.slitPlane) :
    CDHi.Mem S (CDHi.sqrt S (luneRadS S B C2 D))
      (Complex.sqrt (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ) * ((1 + z) * (1 + z)) -
        ((16 * c ^ 2 : ℝ) : ℂ) * z)) := by
  have hrad : CDHi.Mem S (luneRadS S B C2 D)
      (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ) * ((1 + z) * (1 + z)) -
        ((16 * c ^ 2 : ℝ) : ℂ) * z) := luneEnclS_rad_mem S hCD c B C2 D hz hB hC2
  exact hCD.mem_sqrt hrad (hSP _ hrad) hRlo hRhi hPhi hQhi

/-- The rectangle `luneNumS S B D Sq` encloses the lune numerator `z·B - B + σ`. -/
theorem luneEnclS_num_mem (S : ℤ) (hCD : CDHiSound S) (c : ℝ) (B : Iv) (D Sq : CD) {z : ℂ}
    (hz : CDHi.Mem S D z) (hB : IvHi.Mem S B (1 + c ^ 2))
    (hSq : CDHi.Mem S Sq (Complex.sqrt (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ)
      * ((1 + z) * (1 + z)) - ((16 * c ^ 2 : ℝ) : ℂ) * z))) :
    CDHi.Mem S (luneNumS S B D Sq)
      (z * ((1 + c ^ 2 : ℝ) : ℂ) - ((1 + c ^ 2 : ℝ) : ℂ) +
        Complex.sqrt (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ)
          * ((1 + z) * (1 + z)) - ((16 * c ^ 2 : ℝ) : ℂ) * z)) := by
  have h1 : CDHi.Mem S (CDHi.cst B) (((1 + c ^ 2 : ℝ) : ℂ)) := hCD.mem_cst hB
  have h := hCD.mem_add (hCD.mem_sub (hCD.mem_mul hz h1) h1) hSq
  simpa only [luneNumS] using h

/-- The rectangle `luneDenS S B D Sq` encloses `B(1-z) + σ`. -/
theorem luneEnclS_den_mem (S : ℤ) (hCD : CDHiSound S) (c : ℝ) (B : Iv) (D Sq : CD) {z : ℂ}
    (hz : CDHi.Mem S D z) (hB : IvHi.Mem S B (1 + c ^ 2))
    (hSq : CDHi.Mem S Sq ((luneR c z) ^ (1 / 2 : ℂ))) :
    CDHi.Mem S (luneDenS S B D Sq) (luneB c * (1 - z) + (luneR c z) ^ (1 / 2 : ℂ)) := by
  have h1 : CDHi.Mem S (CDHi.mul S (CDHi.cst B) (CDHi.sub (CDHi.ONE S) D))
      ((((1 + c ^ 2 : ℝ)) : ℂ) * (1 - z)) :=
    hCD.mem_mul (hCD.mem_cst hB) (hCD.mem_sub hCD.mem_ONE hz)
  have hval : luneB c * (1 - z) + (luneR c z) ^ (1 / 2 : ℂ)
      = ((((1 + c ^ 2 : ℝ)) : ℂ) * (1 - z)) + (luneR c z) ^ (1 / 2 : ℂ) := by
    simp only [luneB, luneBr]
  rw [hval]
  exact hCD.mem_add h1 hSq

/-- **Soundness of the classical scale-`S` lune enclosure `luneEnclIS`.** -/
theorem luneEnclIS_mem (S : ℤ) (hCD : CDHiSound S) (c : ℝ) (hc : 1 < c)
    (B C2 Dc : Iv) (D : CD) {z : ℂ}
    (hz : CDHi.Mem S D z) (hB : IvHi.Mem S B (1 + c ^ 2)) (hC2 : IvHi.Mem S C2 (16 * c ^ 2))
    (hDc : IvHi.Mem S Dc (2 * (c ^ 2 - 1)))
    (hRlo : 0 ≤ m2rS S (IvHi.add (IvHi.sq S (luneRadS S B C2 D).re)
      (IvHi.sq S (luneRadS S B C2 D).im)).lo)
    (hRhi : 0 ≤ m2rS S (IvHi.add (IvHi.sq S (luneRadS S B C2 D).re)
      (IvHi.sq S (luneRadS S B C2 D).im)).hi)
    (hPhi : 0 ≤ m2rS S (CDHi.sqrtArgRe S (luneRadS S B C2 D)).hi)
    (hQhi : 0 ≤ m2rS S (CDHi.sqrtArgIm S (luneRadS S B C2 D)).hi)
    (hSP : ∀ u : ℂ, CDHi.Mem S (luneRadS S B C2 D) u → u ∈ Complex.slitPlane)
    (hden : 0 < m2rS S (IvHi.add (IvHi.sq S (CD.re (CDHi.cst Dc)))
      (IvHi.sq S (CD.im (CDHi.cst Dc)))).lo) :
    CDHi.Mem S (luneEnclIS S B C2 Dc D) (lune c z) := by
  have h3 : CDHi.Mem S (CDHi.cst Dc) (((2 * (c ^ 2 - 1) : ℝ) : ℂ)) := hCD.mem_cst hDc
  have hsqrt : CDHi.Mem S (CDHi.sqrt S (luneRadS S B C2 D))
      (Complex.sqrt (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ) * ((1 + z) * (1 + z)) -
        ((16 * c ^ 2 : ℝ) : ℂ) * z)) :=
    luneEnclS_sqrt_mem S hCD c B C2 D hz hB hC2 hRlo hRhi hPhi hQhi hSP
  have hnum : CDHi.Mem S (luneNumS S B D (CDHi.sqrt S (luneRadS S B C2 D)))
      (z * ((1 + c ^ 2 : ℝ) : ℂ) - ((1 + c ^ 2 : ℝ) : ℂ) +
        Complex.sqrt (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ)
          * ((1 + z) * (1 + z)) - ((16 * c ^ 2 : ℝ) : ℂ) * z)) :=
    luneEnclS_num_mem S hCD c B D (CDHi.sqrt S (luneRadS S B C2 D)) hz hB hsqrt
  have hinv : CDHi.Mem S (CDHi.inv S (CDHi.cst Dc))
      (1 / ((2 * (c ^ 2 - 1) : ℝ) : ℂ)) := hCD.mem_inv h3 hden
  have hprod : CDHi.Mem S (luneEnclIS S B C2 Dc D)
      ((z * ((1 + c ^ 2 : ℝ) : ℂ) - ((1 + c ^ 2 : ℝ) : ℂ) +
        Complex.sqrt (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ) *
          ((1 + z) * (1 + z)) - ((16 * c ^ 2 : ℝ) : ℂ) * z)) *
        (1 / ((2 * (c ^ 2 - 1) : ℝ) : ℂ))) := hCD.mem_mul hnum hinv
  rwa [luneEncl_val c z] at hprod

/-- **Soundness of the rationalized scale-`S` lune enclosure `luneEnclRIS`.** -/
theorem luneEnclRIS_mem (S : ℤ) (hCD : CDHiSound S) (c : ℝ) (hc : 1 < c)
    (B C2 Dc : Iv) (D : CD) {z : ℂ}
    (hz : CDHi.Mem S D z) (hB : IvHi.Mem S B (1 + c ^ 2)) (hC2 : IvHi.Mem S C2 (16 * c ^ 2))
    (hDc : IvHi.Mem S Dc (2 * (c ^ 2 - 1)))
    (hRlo : 0 ≤ m2rS S (IvHi.add (IvHi.sq S (luneRadS S B C2 D).re)
      (IvHi.sq S (luneRadS S B C2 D).im)).lo)
    (hRhi : 0 ≤ m2rS S (IvHi.add (IvHi.sq S (luneRadS S B C2 D).re)
      (IvHi.sq S (luneRadS S B C2 D).im)).hi)
    (hPhi : 0 ≤ m2rS S (CDHi.sqrtArgRe S (luneRadS S B C2 D)).hi)
    (hQhi : 0 ≤ m2rS S (CDHi.sqrtArgIm S (luneRadS S B C2 D)).hi)
    (hSP : ∀ u : ℂ, CDHi.Mem S (luneRadS S B C2 D) u → u ∈ Complex.slitPlane)
    (hdenR : 0 < m2rS S (IvHi.add
      (IvHi.sq S (CD.re (luneDenS S B D (CDHi.sqrt S (luneRadS S B C2 D)))))
      (IvHi.sq S (CD.im (luneDenS S B D (CDHi.sqrt S (luneRadS S B C2 D)))))).lo) :
    CDHi.Mem S (luneEnclRIS S B C2 Dc D) (lune c z) := by
  have hrad : CDHi.Mem S (luneRadS S B C2 D)
      (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ) * ((1 + z) * (1 + z)) -
        ((16 * c ^ 2 : ℝ) : ℂ) * z) := luneEnclS_rad_mem S hCD c B C2 D hz hB hC2
  have hsq : Complex.sqrt (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ)
      * ((1 + z) * (1 + z)) - (((16 * c ^ 2 : ℝ)) : ℂ) * z) = (luneR c z) ^ (1 / 2 : ℂ) := by
    rw [Complex.sqrt, one_div]
    congr 1
    simp only [luneR]
    push_cast
    ring
  have hsqrt0 : CDHi.Mem S (CDHi.sqrt S (luneRadS S B C2 D))
      (Complex.sqrt (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ)
        * ((1 + z) * (1 + z)) - ((16 * c ^ 2 : ℝ) : ℂ) * z)) :=
    luneEnclS_sqrt_mem S hCD c B C2 D hz hB hC2 hRlo hRhi hPhi hQhi hSP
  have hsqrt : CDHi.Mem S (CDHi.sqrt S (luneRadS S B C2 D)) ((luneR c z) ^ (1 / 2 : ℂ)) := by
    rwa [hsq] at hsqrt0
  have hden : CDHi.Mem S (luneDenS S B D (CDHi.sqrt S (luneRadS S B C2 D)))
      (luneB c * (1 - z) + (luneR c z) ^ (1 / 2 : ℂ)) :=
    luneEnclS_den_mem S hCD c B D (CDHi.sqrt S (luneRadS S B C2 D)) hz hB hsqrt
  have hinv : CDHi.Mem S
      (CDHi.inv S (luneDenS S B D (CDHi.sqrt S (luneRadS S B C2 D))))
      (1 / (luneB c * (1 - z) + (luneR c z) ^ (1 / 2 : ℂ))) := hCD.mem_inv hden hdenR
  have hnum : CDHi.Mem S (CDHi.mul S (CDHi.cst Dc) D) (((2 * (c ^ 2 - 1) : ℝ) : ℂ) * z) :=
    hCD.mem_mul (hCD.mem_cst hDc) hz
  have hprod : CDHi.Mem S (luneEnclRIS S B C2 Dc D)
      ((((2 * (c ^ 2 - 1) : ℝ) : ℂ) * z) *
        (1 / (luneB c * (1 - z) + (luneR c z) ^ (1 / 2 : ℂ)))) := hCD.mem_mul hnum hinv
  have hval : (((2 * (c ^ 2 - 1) : ℝ) : ℂ) * z) *
      (1 / (luneB c * (1 - z) + (luneR c z) ^ (1 / 2 : ℂ))) = lune c z := by
    rw [lune_den_formula c hc z, div_eq_mul_inv]
    push_cast
    ring
  rwa [hval] at hprod

/-- **Soundness of the scale-`S` lune stage** (the scale-`S` analogue of
`Work.ANum.luneEncl2_mem`/`luneEncl3_mem`): if `D ∋ z` and the constants enclose `1+c²`, `16c²`,
`2(c²-1)`, and the side conditions hold, then `luneEnclS S B C2 Dc D` contains `lune c z`. -/
theorem luneEnclS_mem (S : ℤ) (hS : 0 < S) (hIv : Work.ANum.IvHiSound S)
    (hCD : Work.ANum.CDHiSound S)
    (c : ℝ) (hc : 1 < c) (B C2 Dc : Work.ANum.Iv) (D : Work.ANum.CD) {z : ℂ}
    (hz : Work.ANum.CDHi.Mem S D z) (hB : Work.ANum.IvHi.Mem S B (1 + c ^ 2))
    (hC2 : Work.ANum.IvHi.Mem S C2 (16 * c ^ 2))
    (hDc : Work.ANum.IvHi.Mem S Dc (2 * (c ^ 2 - 1)))
    (hRlo : 0 ≤ Work.ANum.m2rS S (Work.ANum.IvHi.add
      (Work.ANum.IvHi.sq S (Work.ANum.CD.re (Work.ANum.luneRadS S B C2 D)))
      (Work.ANum.IvHi.sq S (Work.ANum.CD.im (Work.ANum.luneRadS S B C2 D)))).lo)
    (hRhi : 0 ≤ Work.ANum.m2rS S (Work.ANum.IvHi.add
      (Work.ANum.IvHi.sq S (Work.ANum.CD.re (Work.ANum.luneRadS S B C2 D)))
      (Work.ANum.IvHi.sq S (Work.ANum.CD.im (Work.ANum.luneRadS S B C2 D)))).hi)
    (hPhi : 0 ≤ Work.ANum.m2rS S (Work.ANum.CDHi.sqrtArgRe S (Work.ANum.luneRadS S B C2 D)).hi)
    (hQhi : 0 ≤ Work.ANum.m2rS S (Work.ANum.CDHi.sqrtArgIm S (Work.ANum.luneRadS S B C2 D)).hi)
    (hSP : ∀ u : ℂ, Work.ANum.CDHi.Mem S (Work.ANum.luneRadS S B C2 D) u →
      u ∈ Complex.slitPlane)
    (hden : 0 < Work.ANum.m2rS S (Work.ANum.IvHi.add
      (Work.ANum.IvHi.sq S (Work.ANum.CD.re (Work.ANum.CDHi.cst Dc)))
      (Work.ANum.IvHi.sq S (Work.ANum.CD.im (Work.ANum.CDHi.cst Dc)))).lo)
    (hdenR : 0 < Work.ANum.m2rS S (Work.ANum.IvHi.add
      (Work.ANum.IvHi.sq S (Work.ANum.CD.re (Work.ANum.luneDenS S B D
        (Work.ANum.CDHi.sqrt S (Work.ANum.luneRadS S B C2 D)))))
      (Work.ANum.IvHi.sq S (Work.ANum.CD.im (Work.ANum.luneDenS S B D
        (Work.ANum.CDHi.sqrt S (Work.ANum.luneRadS S B C2 D)))))).lo) :
    Work.ANum.CDHi.Mem S (Work.ANum.luneEnclS S B C2 Dc D)
      (Submission.CDTPlan.lune c z) := by
  exact hCD.mem_inter
    (luneEnclIS_mem S hCD c hc B C2 Dc D hz hB hC2 hDc hRlo hRhi hPhi hQhi hSP hden)
    (luneEnclRIS_mem S hCD c hc B C2 Dc D hz hB hC2 hDc hRlo hRhi hPhi hQhi hSP hdenR)

end

end Work.ANum

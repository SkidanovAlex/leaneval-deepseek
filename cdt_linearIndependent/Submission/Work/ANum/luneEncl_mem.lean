import Mathlib
import Submission.Work.ANum.MapEncl

namespace Work.ANum

open Submission.CDTPlan

/-- The algebraic value computed by `luneEncl`: the lune numerator times the reciprocal of the
denominator.  This is a pure algebra identity, isolated so that the enclosure proof is a chain of
`mem_*` lemmas ending in a rewrite by it. -/
theorem luneEncl_val (c : ℝ) (z : ℂ) :
    (z * ((1 + c ^ 2 : ℝ) : ℂ) - ((1 + c ^ 2 : ℝ) : ℂ) +
        Complex.sqrt (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ) * ((1 + z) * (1 + z)) -
          ((16 * c ^ 2 : ℝ) : ℂ) * z)) * (1 / ((2 * (c ^ 2 - 1) : ℝ) : ℂ)) =
      lune c z := by
  have hrad : ((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ) * ((1 + z) * (1 + z)) -
      ((16 * c ^ 2 : ℝ) : ℂ) * z =
      (1 + (c : ℂ) ^ 2) ^ 2 * (1 + z) ^ 2 - 16 * (c : ℂ) ^ 2 * z := by
    push_cast
    ring
  have hsq : Complex.sqrt (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ) * ((1 + z) * (1 + z)) -
        ((16 * c ^ 2 : ℝ) : ℂ) * z) =
      ((1 + (c : ℂ) ^ 2) ^ 2 * (1 + z) ^ 2 - 16 * (c : ℂ) ^ 2 * z) ^ (1 / 2 : ℂ) := by
    rw [Complex.sqrt, hrad, one_div]
  rw [lune, hsq]
  push_cast
  ring

theorem luneEncl_mem (c : ℝ) (hc : 1 < c)
    (B C2 Dc : Iv) (D : CD) {z : ℂ}
    (hz : D.Mem z) (hB : B.Mem (1 + c ^ 2)) (hC2 : C2.Mem (16 * c ^ 2))
    (hDc : Dc.Mem (2 * (c ^ 2 - 1)))
    (hRlo : 0 ≤ m2r ((luneRad B C2 D).re.sq.add (luneRad B C2 D).im.sq).lo)
    (hRhi : 0 ≤ m2r ((luneRad B C2 D).re.sq.add (luneRad B C2 D).im.sq).hi)
    (hPhi : 0 ≤ m2r (CD.sqrtArgRe (luneRad B C2 D)).hi)
    (hQhi : 0 ≤ m2r (CD.sqrtArgIm (luneRad B C2 D)).hi)
    (hSP : ∀ u : ℂ, (luneRad B C2 D).Mem u → u ∈ Complex.slitPlane)
    (hden : 0 < m2r (((cst Dc).re.sq).add ((cst Dc).im.sq)).lo) :
    (luneEncl B C2 Dc D).Mem (lune c z) := by
  have h1 : (cst B).Mem (((1 + c ^ 2 : ℝ) : ℂ)) := mem_cst hB
  have h2 : (cst C2).Mem (((16 * c ^ 2 : ℝ) : ℂ)) := mem_cst hC2
  have h3 : (cst Dc).Mem (((2 * (c ^ 2 - 1) : ℝ) : ℂ)) := mem_cst hDc
  have h1z : (ONE.add D).Mem (1 + z) := CD.mem_add mem_ONE hz
  have hBB : (((cst B).mul (cst B)).mul ((ONE.add D).mul (ONE.add D))).Mem
      (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ) * ((1 + z) * (1 + z))) :=
    CD.mem_mul (CD.mem_mul h1 h1) (CD.mem_mul h1z h1z)
  have hC2z : ((cst C2).mul D).Mem (((16 * c ^ 2 : ℝ) : ℂ) * z) := CD.mem_mul h2 hz
  have hRad : (luneRad B C2 D).Mem
      (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ) * ((1 + z) * (1 + z)) -
        ((16 * c ^ 2 : ℝ) : ℂ) * z) := by
    unfold luneRad
    exact CD.mem_sub hBB hC2z
  have hSqrt : (luneSqrt B C2 D).Mem (Complex.sqrt (((1 + c ^ 2 : ℝ) : ℂ) *
      ((1 + c ^ 2 : ℝ) : ℂ) * ((1 + z) * (1 + z)) - ((16 * c ^ 2 : ℝ) : ℂ) * z)) := by
    unfold luneSqrt
    exact CD.mem_sqrt hRad (hSP _ hRad) hRlo hRhi hPhi hQhi
  have hNum : (luneNum B D (luneSqrt B C2 D)).Mem
      (z * ((1 + c ^ 2 : ℝ) : ℂ) - ((1 + c ^ 2 : ℝ) : ℂ) +
        Complex.sqrt (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ) *
          ((1 + z) * (1 + z)) - ((16 * c ^ 2 : ℝ) : ℂ) * z)) := by
    unfold luneNum
    exact CD.mem_add (CD.mem_sub (CD.mem_mul hz h1) h1) hSqrt
  have hInv : ((cst Dc).inv).Mem (1 / ((2 * (c ^ 2 - 1) : ℝ) : ℂ)) := CD.mem_inv h3 hden
  have hRes : (luneEncl B C2 Dc D).Mem
      ((z * ((1 + c ^ 2 : ℝ) : ℂ) - ((1 + c ^ 2 : ℝ) : ℂ) +
        Complex.sqrt (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ) *
          ((1 + z) * (1 + z)) - ((16 * c ^ 2 : ℝ) : ℂ) * z)) *
        (1 / ((2 * (c ^ 2 - 1) : ℝ) : ℂ))) := by
    unfold luneEncl
    exact CD.mem_mul hNum hInv
  rwa [luneEncl_val c z] at hRes

end Work.ANum

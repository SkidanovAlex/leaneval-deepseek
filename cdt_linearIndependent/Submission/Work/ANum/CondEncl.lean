import Mathlib
import Submission.Work.ANum.MapEncl
import Submission.Work.ANum.slitEncl_mem
import Submission.Work.ANum.luneEncl_mem
import Submission.Work.APsi.defs
import Submission.Work.ANum.ACert

/-! # Better-conditioned (rationalized) enclosures of the slit and lune stages

The interval evaluation of `slit r` and `lune c` used in `Submission.Work.ANum.slitEncl` /
`luneEncl` is *sound* but ill-conditioned: the numerator `slitP + slitR` of the slit map vanishes
at `w = 0` (a complete cancellation of two `O(1)` terms), and the slit value is obtained by
dividing by `8 r w`, which is tiny for the `c = 1/10⁴` circle of the Theorem-A contour.
Measured (at scale `SC = 2³⁰`, `4096` arcs): the enclosure of `ψ_A` at a *point* has width up to
`1.2·10¹¹` ulps on the `|z| = 10⁻⁴` circle and `10⁷` ulps on the other two — far too wide for the
logarithm layer, which pays a factor `|h'/h|·radius`.

This module adds the *rationalized* forms, obtained from the algebraic identities

* `slit r w = 8 r w / (slitP r w - slitR r w)`  (from `slitKey`: `slitP² - slitR² = (8rw)²`),
* `lune c z = 2 (c²-1) z / (B(1-z) + √(R z))`   (`N·M = 4 C² z`),

whose denominators are `O(1)` and free of the cancellation, and takes the *intersection* of the two
enclosures.  Both are sound enclosures of the same value, so the intersection is sound and is
strictly tighter than either.  Measured effect on the width of the point enclosure of `ψ_A`:
`k = 0` (circle `10⁻⁴`): max `1.78·10¹¹ → 66` ulps; `k = 1` (`0.566`): `1.50·10⁹ → 3.49·10⁷`;
`k = 2` (unit circle): `1.62·10⁹ → 1.32·10⁹`. -/

namespace Work.ANum

open Submission.CDTPlan Complex
open Work.APsi

noncomputable section

/-! ## Intersection of two enclosures -/

namespace Iv

/-- Intersection of two intervals (used when both enclose the same value). -/
def inter (I J : Iv) : Iv := ⟨max I.lo J.lo, min I.hi J.hi⟩

theorem mem_inter {I J : Iv} {x : ℝ} (hI : I.Mem x) (hJ : J.Mem x) : (inter I J).Mem x := by
  refine ⟨?_, ?_⟩
  · show m2r (max I.lo J.lo) ≤ x
    rw [m2r_max]; exact max_le hI.1 hJ.1
  · show x ≤ m2r (min I.hi J.hi)
    rw [m2r_min]; exact le_min hI.2 hJ.2

end Iv

namespace CD

/-- Intersection of two rectangles. -/
def inter (D E : CD) : CD := ⟨D.re.inter E.re, D.im.inter E.im⟩

theorem mem_inter {D E : CD} {z : ℂ} (hD : D.Mem z) (hE : E.Mem z) : (inter D E).Mem z :=
  ⟨Iv.mem_inter hD.1 hE.1, Iv.mem_inter hD.2 hE.2⟩

end CD

/-! ## The rationalized algebraic forms -/

/-- **Rationalized slit formula**: the denominator `slitP r w - slitR r w` is `O(1)` at `w = 0`,
where the classical numerator `slitP + slitR` cancels completely. -/
theorem slit_den_formula (r : ℝ) (hr : r ≠ 0) (z : ℂ) :
    slit r z = (8 * (r : ℂ) * z) / (slitP r z - slitR r z) := by
  rcases eq_or_ne z 0 with hz | hz
  · subst hz
    rw [slit, if_pos rfl, mul_zero, zero_div]
  · have hAC : (slitP r z - slitR r z) * (slitP r z + slitR r z) = (8 * (r : ℂ) * z) ^ 2 := by
      have h1 := slitKey r z
      have h2 := slitR_sq r z
      linear_combination h1 - h2
    have hB : (8 * (r : ℂ) * z) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hr)) hz
    have hC : slitP r z - slitR r z ≠ 0 := by
      intro h
      rw [h, zero_mul] at hAC
      exact (pow_ne_zero 2 hB) hAC.symm
    rw [slit_eq_formula r z hz, slitN, div_eq_div_iff hB hC]
    linear_combination hAC

/-- **Rationalized lune formula**: the denominator `B(1-z) + √(R z)` is `O(1)` at `z = 0`. -/
theorem lune_den_formula (c : ℝ) (hc : 1 < c) (z : ℂ) :
    lune c z = (2 * ((c : ℂ) ^ 2 - 1) * z) /
      (luneB c * (1 - z) + (luneR c z) ^ (1 / 2 : ℂ)) := by
  rcases eq_or_ne z 0 with hz | hz
  · subst hz
    rw [lune_zero, mul_zero, zero_div]
  · have hC : luneC c ≠ 0 := luneC_ne_zero hc
    have hsq : ((luneR c z) ^ (1 / 2 : ℂ)) ^ 2 = luneR c z := by
      rw [one_div]; exact Complex.cpow_nat_inv_pow _ (by norm_num)
    have hNM : (z * luneB c - luneB c + (luneR c z) ^ (1/2:ℂ)) *
          (luneB c * (1 - z) + (luneR c z) ^ (1/2:ℂ)) = 4 * (luneC c)^2 * z := by
      have h1 : (z * luneB c - luneB c + (luneR c z) ^ (1/2:ℂ)) *
          (luneB c * (1 - z) + (luneR c z) ^ (1/2:ℂ))
          = ((luneR c z) ^ (1/2:ℂ))^2 - (luneB c * (1 - z))^2 := by ring
      rw [h1, hsq]
      simp only [luneR, luneB, luneBr, luneC, luneCr]
      push_cast
      ring
    have hM : luneB c * (1 - z) + (luneR c z) ^ (1 / 2 : ℂ) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hNM
      exact (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hC)) hz) hNM.symm
    rw [lune_eq, div_eq_div_iff (mul_ne_zero (by norm_num) hC) hM, hNM]
    simp only [luneC, luneCr]
    push_cast
    ring

/-! ## The rationalized enclosures -/

/-- The denominator `A(1+w²) - Ew - C(w-1)√Q` of the rationalized slit formula. -/
def slitDen (A E C : Iv) (D S : CD) : CD :=
  (((cst A).mul (ONE.add (D.mul D))).sub ((cst E).mul D)).sub
    ((cst C).mul ((D.sub ONE).mul S))

/-- The rationalized enclosure of `slit r`: numerator `8rw`, the denominator above. -/
def slitEnclR (A B E C G : Iv) (D : CD) : CD :=
  ((cst G).mul D).mul ((slitDen A E C D (slitRad A B D).sqrt).inv)

/-- The denominator `B(1-z) + √(R z)` of the rationalized lune formula. -/
def luneDen (B : Iv) (D S : CD) : CD := ((cst B).mul (ONE.sub D)).add S

/-- The rationalized enclosure of `lune c`: numerator `Dc·z`, the denominator above. -/
def luneEnclR (B C2 Dc : Iv) (D : CD) : CD :=
  ((cst Dc).mul D).mul ((luneDen B D (luneRad B C2 D).sqrt).inv)

theorem slitDen_mem (r : ℝ) (A E C : Iv) (D S : CD) {w : ℂ} (hw : D.Mem w)
    (hA : A.Mem ((1 + r) ^ 2)) (hE : E.Mem (2 * (r - 1) ^ 2)) (hC : C.Mem (1 + r))
    (hS : S.Mem (Complex.sqrt (slitQ r w))) :
    (slitDen A E C D S).Mem (slitP r w - slitR r w) := by
  have hS' : S.Mem ((slitQ r w) ^ (1 / 2 : ℂ)) := by
    rwa [sqrt_eq_cpow_half] at hS
  have h1 : ((cst A).mul (ONE.add (D.mul D))).Mem
      ((((1 + r) ^ 2 : ℝ) : ℂ) * (1 + w * w)) :=
    CD.mem_mul (mem_cst hA) (CD.mem_add mem_ONE (CD.mem_mul hw hw))
  have h2 : ((cst E).mul D).Mem ((((2 * (r - 1) ^ 2 : ℝ)) : ℂ) * w) :=
    CD.mem_mul (mem_cst hE) hw
  have h3 : ((cst C).mul ((D.sub ONE).mul S)).Mem
      ((((1 + r : ℝ)) : ℂ) * ((w - 1) * (slitQ r w) ^ (1 / 2 : ℂ))) :=
    CD.mem_mul (mem_cst hC) (CD.mem_mul (CD.mem_sub hw mem_ONE) hS')
  have hval : slitP r w - slitR r w =
      ((((1 + r) ^ 2 : ℝ) : ℂ) * (1 + w * w)) - ((((2 * (r - 1) ^ 2 : ℝ)) : ℂ) * w)
        - ((((1 + r : ℝ)) : ℂ) * ((w - 1) * (slitQ r w) ^ (1 / 2 : ℂ))) := by
    simp only [slitP, slitR]
    push_cast
    ring
  rw [hval]
  exact CD.mem_sub (CD.mem_sub h1 h2) h3

theorem luneDen_mem (c : ℝ) (B : Iv) (D S : CD) {z : ℂ} (hz : D.Mem z)
    (hB : B.Mem (1 + c ^ 2)) (hS : S.Mem ((luneR c z) ^ (1 / 2 : ℂ))) :
    (luneDen B D S).Mem (luneB c * (1 - z) + (luneR c z) ^ (1 / 2 : ℂ)) := by
  have h1 : ((cst B).mul (ONE.sub D)).Mem ((((1 + c ^ 2 : ℝ)) : ℂ) * (1 - z)) :=
    CD.mem_mul (mem_cst hB) (CD.mem_sub mem_ONE hz)
  have hval : luneB c * (1 - z) + (luneR c z) ^ (1 / 2 : ℂ)
      = ((((1 + c ^ 2 : ℝ)) : ℂ) * (1 - z)) + (luneR c z) ^ (1 / 2 : ℂ) := by
    simp only [luneB, luneBr]
  rw [hval]
  exact CD.mem_add h1 hS

/-- **Soundness of the rationalized slit enclosure.**  Same side conditions as
`slitEncl_mem` for the square root, plus the nondegeneracy of the *new* denominator. -/
theorem slitEnclR_mem (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (A B E C G : Iv) (D : CD) {w : ℂ}
    (hw : D.Mem w) (hA : A.Mem ((1 + r) ^ 2)) (hB : B.Mem (2 * (1 - 6 * r + r ^ 2)))
    (hE : E.Mem (2 * (r - 1) ^ 2)) (hC : C.Mem (1 + r)) (hG : G.Mem (8 * r))
    (hRlo : 0 ≤ m2r ((slitRad A B D).re.sq.add (slitRad A B D).im.sq).lo)
    (hRhi : 0 ≤ m2r ((slitRad A B D).re.sq.add (slitRad A B D).im.sq).hi)
    (hPhi : 0 ≤ m2r (CD.sqrtArgRe (slitRad A B D)).hi)
    (hQhi : 0 ≤ m2r (CD.sqrtArgIm (slitRad A B D)).hi)
    (hSP : ∀ u : ℂ, (slitRad A B D).Mem u → u ∈ Complex.slitPlane)
    (hdenR : 0 < m2r (((slitDen A E C D (slitRad A B D).sqrt).re.sq.add
      (slitDen A E C D (slitRad A B D).sqrt).im.sq)).lo) :
    (slitEnclR A B E C G D).Mem (slit r w) := by
  have hrad : (slitRad A B D).Mem (slitQ r w) := slitRad_mem r A B D hw hA hB
  have hsqrt : (slitSqrt A B D).Mem (Complex.sqrt (slitQ r w)) :=
    CD.mem_sqrt hrad (hSP _ hrad) hRlo hRhi hPhi hQhi
  have hden : (slitDen A E C D (slitSqrt A B D)).Mem (slitP r w - slitR r w) :=
    slitDen_mem r A E C D (slitSqrt A B D) hw hA hE hC hsqrt
  have hinv : ((slitDen A E C D (slitSqrt A B D)).inv).Mem (1 / (slitP r w - slitR r w)) :=
    CD.mem_inv hden (by simpa only [slitSqrt] using hdenR)
  have hnum : ((cst G).mul D).Mem (((8 * r : ℝ) : ℂ) * w) := CD.mem_mul (mem_cst hG) hw
  have hprod := CD.mem_mul hnum hinv
  have h8 : (((8 * r : ℝ)) : ℂ) = 8 * (r : ℂ) := by push_cast; ring
  have hval : ((((8 * r : ℝ) : ℂ) * w) * (1 / (slitP r w - slitR r w))) = slit r w := by
    rw [slit_den_formula r (ne_of_gt hr) w, div_eq_mul_inv]
    push_cast
    ring
  rwa [hval] at hprod

/-- **Soundness of the rationalized lune enclosure.** -/
theorem luneEnclR_mem (c : ℝ) (hc : 1 < c)
    (B C2 Dc : Iv) (D : CD) {z : ℂ}
    (hz : D.Mem z) (hB : B.Mem (1 + c ^ 2)) (hC2 : C2.Mem (16 * c ^ 2))
    (hDc : Dc.Mem (2 * (c ^ 2 - 1)))
    (hRlo : 0 ≤ m2r ((luneRad B C2 D).re.sq.add (luneRad B C2 D).im.sq).lo)
    (hRhi : 0 ≤ m2r ((luneRad B C2 D).re.sq.add (luneRad B C2 D).im.sq).hi)
    (hPhi : 0 ≤ m2r (CD.sqrtArgRe (luneRad B C2 D)).hi)
    (hQhi : 0 ≤ m2r (CD.sqrtArgIm (luneRad B C2 D)).hi)
    (hSP : ∀ u : ℂ, (luneRad B C2 D).Mem u → u ∈ Complex.slitPlane)
    (hdenR : 0 < m2r (((luneDen B D (luneRad B C2 D).sqrt).re.sq.add
      (luneDen B D (luneRad B C2 D).sqrt).im.sq)).lo) :
    (luneEnclR B C2 Dc D).Mem (lune c z) := by
  have h1 : (cst B).Mem (((1 + c ^ 2 : ℝ) : ℂ)) := mem_cst hB
  have h2 : (cst C2).Mem (((16 * c ^ 2 : ℝ) : ℂ)) := mem_cst hC2
  have h1z : (ONE.add D).Mem (1 + z) := CD.mem_add mem_ONE hz
  have hBB : (((cst B).mul (cst B)).mul ((ONE.add D).mul (ONE.add D))).Mem
      (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ) * ((1 + z) * (1 + z))) :=
    CD.mem_mul (CD.mem_mul h1 h1) (CD.mem_mul h1z h1z)
  have hC2z : ((cst C2).mul D).Mem (((16 * c ^ 2 : ℝ) : ℂ) * z) := CD.mem_mul h2 hz
  have hrad : (luneRad B C2 D).Mem
      (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ) * ((1 + z) * (1 + z)) -
        ((16 * c ^ 2 : ℝ) : ℂ) * z) := by
    unfold luneRad
    exact CD.mem_sub hBB hC2z
  have hsq : Complex.sqrt (((1 + c ^ 2 : ℝ) : ℂ) * ((1 + c ^ 2 : ℝ) : ℂ)
      * ((1 + z) * (1 + z)) - (((16 * c ^ 2 : ℝ)) : ℂ) * z) = (luneR c z) ^ (1 / 2 : ℂ) := by
    rw [Complex.sqrt, one_div]
    congr 1
    simp only [luneR]
    push_cast
    ring
  have hsqrt : (luneSqrt B C2 D).Mem ((luneR c z) ^ (1 / 2 : ℂ)) := by
    have h := CD.mem_sqrt hrad (hSP _ hrad) hRlo hRhi hPhi hQhi
    rwa [hsq] at h
  have hden : (luneDen B D (luneSqrt B C2 D)).Mem
      (luneB c * (1 - z) + (luneR c z) ^ (1 / 2 : ℂ)) :=
    luneDen_mem c B D (luneSqrt B C2 D) hz hB hsqrt
  have hinv : ((luneDen B D (luneSqrt B C2 D)).inv).Mem
      (1 / (luneB c * (1 - z) + (luneR c z) ^ (1 / 2 : ℂ))) :=
    CD.mem_inv hden (by simpa only [luneSqrt] using hdenR)
  have hnum : ((cst Dc).mul D).Mem (((2 * (c ^ 2 - 1) : ℝ) : ℂ) * z) :=
    CD.mem_mul (mem_cst hDc) hz
  have hprod := CD.mem_mul hnum hinv
  have hval : (((2 * (c ^ 2 - 1) : ℝ) : ℂ) * z) *
      (1 / (luneB c * (1 - z) + (luneR c z) ^ (1 / 2 : ℂ))) = lune c z := by
    rw [lune_den_formula c hc z, div_eq_mul_inv]
    push_cast
    ring
  rwa [hval] at hprod

/-! ## The intersections -/

/-- The intersection of the two enclosures of `slit r`. -/
def slitEncl2 (A B E C G : Iv) (D : CD) : CD :=
  (slitEncl A B E C G D).inter (slitEnclR A B E C G D)

theorem slitEncl2_mem (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (A B E C G : Iv) (D : CD) {w : ℂ}
    (hw : D.Mem w) (hA : A.Mem ((1 + r) ^ 2)) (hB : B.Mem (2 * (1 - 6 * r + r ^ 2)))
    (hE : E.Mem (2 * (r - 1) ^ 2)) (hC : C.Mem (1 + r)) (hG : G.Mem (8 * r))
    (hside : SlitSide A B E C G D)
    (hdenR : 0 < m2r (((slitDen A E C D (slitRad A B D).sqrt).re.sq.add
      (slitDen A E C D (slitRad A B D).sqrt).im.sq)).lo) :
    (slitEncl2 A B E C G D).Mem (slit r w) := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hside
  exact CD.mem_inter
    (slitEncl_mem r hr hr1 A B E C G D hw hA hB hE hC hG s1 s2 s3 s4 s5 s6)
    (slitEnclR_mem r hr hr1 A B E C G D hw hA hB hE hC hG s1 s2 s3 s4 s5 hdenR)

/-- The intersection of the two enclosures of `lune c`. -/
def luneEncl2 (B C2 Dc : Iv) (D : CD) : CD :=
  (luneEncl B C2 Dc D).inter (luneEnclR B C2 Dc D)

theorem luneEncl2_mem (c : ℝ) (hc : 1 < c)
    (B C2 Dc : Iv) (D : CD) {z : ℂ}
    (hz : D.Mem z) (hB : B.Mem (1 + c ^ 2)) (hC2 : C2.Mem (16 * c ^ 2))
    (hDc : Dc.Mem (2 * (c ^ 2 - 1)))
    (hside : LuneSide B C2 D)
    (hden : 0 < m2r (((cst Dc).re.sq).add ((cst Dc).im.sq)).lo)
    (hdenR : 0 < m2r (((luneDen B D (luneRad B C2 D).sqrt).re.sq.add
      (luneDen B D (luneRad B C2 D).sqrt).im.sq)).lo) :
    (luneEncl2 B C2 Dc D).Mem (lune c z) := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := hside
  exact CD.mem_inter
    (luneEncl_mem c hc B C2 Dc D hz hB hC2 hDc s1 s2 s3 s4 s5 hden)
    (luneEnclR_mem c hc B C2 Dc D hz hB hC2 hDc s1 s2 s3 s4 s5 hdenR)

/-! ## The side-condition bundles for the doubled enclosures -/

/-- The side conditions needed by *both* slit enclosures. -/
def SlitSide2 (A B E C G : Iv) (D : CD) : Prop :=
  SlitSide A B E C G D ∧
    0 < m2r (((slitDen A E C D (slitRad A B D).sqrt).re.sq.add
      (slitDen A E C D (slitRad A B D).sqrt).im.sq)).lo

/-- The side conditions needed by *both* lune enclosures. -/
def LuneSide2 (B C2 : Iv) (D : CD) : Prop :=
  LuneSide B C2 D ∧
    0 < m2r (((luneDen B D (luneRad B C2 D).sqrt).re.sq.add
      (luneDen B D (luneRad B C2 D).sqrt).im.sq)).lo

/-- The rectangle enclosure of `psiA` built from the *intersected* (doubled) stage enclosures.
Same shape as `Work.ANum.psiAEncl`. -/
def psiAEnclB (S491 R1 R2 R3 R4 : CD)
    (A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 A4 B4 E4 C4 G4 : Iv)
    (Bl C2l Dcl RC : Iv) (D : CD) : CD :=
  (cst RC).mul (luneEncl2 Bl C2l Dcl
    (R4.mul (slitEncl2 A4 B4 E4 C4 G4
      (R3.mul (slitEncl2 A3 B3 E3 C3 G3
        (R2.mul (slitEncl2 A2 B2 E2 C2 G2
          (R1.mul (slitEncl2 A1 B1 E1 C1 G1 (S491.mul D))))))))).neg)

end

end Work.ANum

/-! ## The fully instantiated version (the certificate's chain) -/

namespace Work.ANum

open Submission.CDTPlan

noncomputable section

/-- The rectangle enclosure of the whole contour, with the constants substituted and the
*doubled* (intersected) stage enclosures. -/
def psiAEnclBc (D : CD) : CD :=
  psiAEnclB S491 RW1 RW2 RW3 RW4
    cA1 cB1 cE1 cC1 cG1 cA2 cB2 cE2 cC2 cG2 cA3 cB3 cE3 cC3 cG3 cA4 cB4 cE4 cC4 cG4
    cBl cC2l cDcl cRC D

end

end Work.ANum

/-! ## The `sqrtI`-based stages: the (currently) tightest chain

`CD.sqrtI` (`Submission/Work/ANum/CSqrt.lean`) is the square root with the *rationalized* bound
`|Im z|/(2 Re √z)` for its imaginary part, which removes the catastrophic `‖z‖ - z.re` cancellation
whenever the radicand is close to the real axis.  Measured effect on the point enclosure of `ψ_A`
(`4096` arcs, `SC = 2³⁰`, on top of the intersected stage enclosures): `k=0` max `66 → 45` ulps,
`k=1` max `3.49·10⁷ → 1.64·10⁶`, `k=2` max `1.32·10⁹ → 5.52·10⁸` and `j = 2048` `9.86·10⁸ → 2.9·10⁶`.

The soundness of `CD.sqrtI` is `Work.ANum.mem_sqrtI` (module `Submission/Work/ANum/mem_sqrtI`); the
soundness of the chain below is `Work.ANum.psiAEnclCc_mem`. -/

namespace Work.ANum

open Submission.CDTPlan Complex

noncomputable section

/-- The `sqrtI`-based radicand square root of a slit stage. -/
def slitSqrtI (A B : Iv) (D : CD) : CD := (slitRad A B D).sqrtI

/-- The classical slit enclosure with the repaired square root. -/
def slitEnclI (A B E C G : Iv) (D : CD) : CD :=
  (slitNum A E C D (slitSqrtI A B D)).mul (((cst G).mul D).inv)

/-- The rationalized slit enclosure with the repaired square root. -/
def slitEnclRI (A B E C G : Iv) (D : CD) : CD :=
  ((cst G).mul D).mul ((slitDen A E C D (slitSqrtI A B D)).inv)

/-- The intersection of the two repaired slit enclosures. -/
def slitEncl3 (A B E C G : Iv) (D : CD) : CD :=
  (slitEnclI A B E C G D).inter (slitEnclRI A B E C G D)

/-- The classical lune enclosure with the repaired square root. -/
def luneEnclI (B C2 Dc : Iv) (D : CD) : CD :=
  (luneNum B D (luneRad B C2 D).sqrtI).mul ((cst Dc).inv)

/-- The rationalized lune enclosure with the repaired square root. -/
def luneEnclRI (B C2 Dc : Iv) (D : CD) : CD :=
  ((cst Dc).mul D).mul ((luneDen B D (luneRad B C2 D).sqrtI).inv)

/-- The intersection of the two repaired lune enclosures. -/
def luneEncl3 (B C2 Dc : Iv) (D : CD) : CD :=
  (luneEnclI B C2 Dc D).inter (luneEnclRI B C2 Dc D)

/-- The side conditions of one repaired slit stage. -/
def SlitSide3 (A B E C G : Iv) (D : CD) : Prop :=
  SlitSide A B E C G D ∧
    0 < m2r (((slitDen A E C D (slitSqrtI A B D)).re.sq.add
      (slitDen A E C D (slitSqrtI A B D)).im.sq)).lo

/-- The side conditions of the repaired lune stage. -/
def LuneSide3 (B C2 : Iv) (D : CD) : Prop :=
  LuneSide B C2 D ∧
    0 < m2r (((luneDen B D (luneRad B C2 D).sqrtI).re.sq.add
      (luneDen B D (luneRad B C2 D).sqrtI).im.sq)).lo

/-- The rectangle enclosure of `psiA` built from the repaired, intersected stage enclosures. -/
def psiAEnclC (S491 R1 R2 R3 R4 : CD)
    (A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 A4 B4 E4 C4 G4 : Iv)
    (Bl C2l Dcl RC : Iv) (D : CD) : CD :=
  (cst RC).mul (luneEncl3 Bl C2l Dcl
    (R4.mul (slitEncl3 A4 B4 E4 C4 G4
      (R3.mul (slitEncl3 A3 B3 E3 C3 G3
        (R2.mul (slitEncl3 A2 B2 E2 C2 G2
          (R1.mul (slitEncl3 A1 B1 E1 C1 G1 (S491.mul D))))))))).neg)

/-- Input of slit stage 1 of the repaired chain: `(491/500)·D`. -/
def sIn1C (S491 : CD) (D : CD) : CD := S491.mul D

/-- Input of slit stage 2 of the repaired chain. -/
def sIn2C (S491 R1 : CD) (A B E C G : Iv) (D : CD) : CD :=
  R1.mul (slitEncl3 A B E C G (sIn1C S491 D))

/-- Input of slit stage 3 of the repaired chain. -/
def sIn3C (S491 R1 R2 : CD) (A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 : Iv) (D : CD) : CD :=
  R2.mul (slitEncl3 A2 B2 E2 C2 G2 (sIn2C S491 R1 A1 B1 E1 C1 G1 D))

/-- Input of slit stage 4 of the repaired chain. -/
def sIn4C (S491 R1 R2 R3 : CD)
    (A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 : Iv) (D : CD) : CD :=
  R3.mul (slitEncl3 A3 B3 E3 C3 G3 (sIn3C S491 R1 R2 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 D))

/-- Output of the four-slit composition of the repaired chain. -/
def sOut4C (S491 R1 R2 R3 R4 : CD)
    (A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 A4 B4 E4 C4 G4 : Iv) (D : CD) : CD :=
  R4.mul (slitEncl3 A4 B4 E4 C4 G4
    (sIn4C S491 R1 R2 R3 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 D))

/-- The chain with the Theorem-A constants substituted. -/
def psiAEnclCc (D : CD) : CD :=
  psiAEnclC S491 RW1 RW2 RW3 RW4
    cA1 cB1 cE1 cC1 cG1 cA2 cB2 cE2 cC2 cG2 cA3 cB3 cE3 cC3 cG3 cA4 cB4 cE4 cC4 cG4
    cBl cC2l cDcl cRC D

end

end Work.ANum

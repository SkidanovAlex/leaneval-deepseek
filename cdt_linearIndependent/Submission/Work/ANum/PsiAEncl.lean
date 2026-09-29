import Mathlib
import Submission.Work.ANum.MapEncl
import Submission.Work.ANum.slitEncl_mem
import Submission.Work.ANum.luneEncl_mem

/-! # Rectangle enclosure of the whole Theorem-A contour map `psiA` (interface)

`psiA = -(4/5)·lune(36/5, -(w₄))` with the four-slit composition
`w₄ = rot t₄ · slit r₄ (rot t₃ · slit r₃ (rot t₂ · slit r₂ (rot t₁ · slit r₁ ((491/500)·z))))`,
`r = (9/10, 379/625, 673/1250, 7487/10000)`, `t = (2033/25000, 2927/25000, 453/12500, -1971/25000)`.

`psiAEncl` below is the corresponding *term* built from the proved operations: five `slitEncl`s
(`Work.ANum.slitEncl_mem`), one `luneEncl` (`Work.ANum.luneEncl_mem`), the rotations (as `CD` data),
the pre-scaling `491/500` and the outer factor `-4/5`.

The soundness theorem `psiAEncl_mem` (`(psiAEncl …).Mem (psiA z)` for `z ∈ D`) is the mechanical
composition of the per-stage lemmas with `CD.mem_mul`/`mem_neg`; its statement lists, for each of the
five stages, the stage's numerical side conditions (the four `CD.sqrt` conditions, the slit-plane
condition and the denominator positivity).  It is stated and proved in the sibling module
`Submission.Work.ANum.psiAEncl_mem`. -/

namespace Work.ANum

noncomputable section

open Submission.CDTPlan Complex

/-- The pre-scaled input rectangle `(491/500)·D`. -/
def pIn (S491 : CD) (D : CD) : CD := S491.mul D

/-- The rectangle enclosure of `psiA`. -/
def psiAEncl (S491 R1 R2 R3 R4 : CD)
    (A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 A4 B4 E4 C4 G4 : Iv)
    (Bl C2l Dcl RC : Iv) (D : CD) : CD :=
  (cst RC).mul (luneEncl Bl C2l Dcl
    (R4.mul (slitEncl A4 B4 E4 C4 G4
      (R3.mul (slitEncl A3 B3 E3 C3 G3
        (R2.mul (slitEncl A2 B2 E2 C2 G2
          (R1.mul (slitEncl A1 B1 E1 C1 G1 (S491.mul D))))))))).neg)

end

end Work.ANum

/-! ## Side-condition bundles and the stage lemmas -/

namespace Work.ANum

noncomputable section

open Submission.CDTPlan Complex

/-- The numerical side conditions of one slit stage (the four `CD.sqrt` conditions for the
radicand rectangle, the slit-plane condition, and the positivity of the denominator rectangle). -/
def SlitSide (A B E C G : Iv) (D : CD) : Prop :=
  0 ≤ m2r ((slitRad A B D).re.sq.add (slitRad A B D).im.sq).lo ∧
  0 ≤ m2r ((slitRad A B D).re.sq.add (slitRad A B D).im.sq).hi ∧
  0 ≤ m2r (CD.sqrtArgRe (slitRad A B D)).hi ∧
  0 ≤ m2r (CD.sqrtArgIm (slitRad A B D)).hi ∧
  (∀ u : ℂ, (slitRad A B D).Mem u → u ∈ Complex.slitPlane) ∧
  0 < m2r ((((cst G).mul D).re.sq).add (((cst G).mul D).im.sq)).lo

/-- The numerical side conditions of the lune stage. -/
def LuneSide (B C2 : Iv) (D : CD) : Prop :=
  0 ≤ m2r ((luneRad B C2 D).re.sq.add (luneRad B C2 D).im.sq).lo ∧
  0 ≤ m2r ((luneRad B C2 D).re.sq.add (luneRad B C2 D).im.sq).hi ∧
  0 ≤ m2r (CD.sqrtArgRe (luneRad B C2 D)).hi ∧
  0 ≤ m2r (CD.sqrtArgIm (luneRad B C2 D)).hi ∧
  (∀ u : ℂ, (luneRad B C2 D).Mem u → u ∈ Complex.slitPlane)

/-- **One slit stage**: rotation of `slit r` over a rectangle. -/
theorem slitStage_mem (r t : ℝ) (hr : 0 < r) (hr1 : r < 1) (R : CD) (hR : R.Mem (rot t))
    (A B E C G : Iv) (hA : A.Mem ((1 + r) ^ 2)) (hB : B.Mem (2 * (1 - 6 * r + r ^ 2)))
    (hE : E.Mem (2 * (r - 1) ^ 2)) (hC : C.Mem (1 + r)) (hG : G.Mem (8 * r))
    (D : CD) (hside : SlitSide A B E C G D) {w : ℂ} (hw : D.Mem w) :
    (R.mul (slitEncl A B E C G D)).Mem (rot t * slit r w) := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hside
  exact CD.mem_mul hR (slitEncl_mem r hr hr1 A B E C G D hw hA hB hE hC hG s1 s2 s3 s4 s5 s6)

/-- **The lune stage** with the outer factor `RC`: enclosure of `RC · lune c z`. -/
theorem luneStage_mem (c : ℝ) (hc : 1 < c) (RC : Iv) (hRC : RC.Mem (-(4 / 5)))
    (B C2 Dc : Iv) (hB : B.Mem (1 + c ^ 2)) (hC2 : C2.Mem (16 * c ^ 2))
    (hDc : Dc.Mem (2 * (c ^ 2 - 1)))
    (D : CD) (hside : LuneSide B C2 D) (hden : 0 < m2r (((cst Dc).re.sq).add ((cst Dc).im.sq)).lo)
    {z : ℂ} (hz : D.Mem z) :
    ((cst RC).mul (luneEncl B C2 Dc D)).Mem (-(4 / 5 : ℂ) * lune c z) := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := hside
  have hmemRC : (cst RC).Mem (-(4 / 5 : ℂ)) := by
    refine ⟨?_, ?_⟩
    · show RC.Mem (-(4 / 5 : ℂ)).re
      rw [show (-(4 / 5 : ℂ)).re = -(4 / 5) by simp]
      exact hRC
    · show (Iv.pt 0).Mem (-(4 / 5 : ℂ)).im
      have h : (-(4 / 5 : ℂ)).im = 0 := by simp
      rw [h]
      simpa [m2r_zero] using Iv.mem_pt 0
  exact CD.mem_mul hmemRC (luneEncl_mem c hc B C2 Dc D hz hB hC2 hDc s1 s2 s3 s4 s5 hden)

end

end Work.ANum

/-! ## The four-slit input rectangles and the final assembly -/

namespace Work.ANum

noncomputable section

open Submission.CDTPlan Complex

/-- Input of slit stage 1: `(491/500)·D`. -/
def sIn1 (S491 : CD) (D : CD) : CD := S491.mul D

/-- Input of slit stage 2: `R1 · slit r1 (sIn1)`. -/
def sIn2 (S491 R1 : CD) (A B E C G : Iv) (D : CD) : CD :=
  R1.mul (slitEncl A B E C G (sIn1 S491 D))

/-- Input of slit stage 3. -/
def sIn3 (S491 R1 R2 : CD) (A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 : Iv) (D : CD) : CD :=
  R2.mul (slitEncl A2 B2 E2 C2 G2 (sIn2 S491 R1 A1 B1 E1 C1 G1 D))

/-- Input of slit stage 4. -/
def sIn4 (S491 R1 R2 R3 : CD)
    (A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 : Iv) (D : CD) : CD :=
  R3.mul (slitEncl A3 B3 E3 C3 G3 (sIn3 S491 R1 R2 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 D))

/-- The output of the four-slit composition (before the lune): `rot t4 · slit r4 (sIn4)`. -/
def sOut4 (S491 R1 R2 R3 R4 : CD)
    (A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 A4 B4 E4 C4 G4 : Iv) (D : CD) : CD :=
  R4.mul (slitEncl A4 B4 E4 C4 G4
    (sIn4 S491 R1 R2 R3 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 D))

/-- **The whole contour**: `psiA z ∈ psiAEncl … D` for `z ∈ D`.

The hypotheses are, from the outside in: the pre-scaling `491/500`, the four rotations, the five
rounded constants of each of the four slit stages, the lune constants and the outer factor `-4/5`,
and one `SlitSide` (resp. `LuneSide`) bundle per stage. -/
theorem psiAEncl_mem {z : ℂ} {D : CD} (hz : D.Mem z)
    (S491 R1 R2 R3 R4 : CD) (hS : S491.re.Mem (491 / 500)) (hS0 : S491.im.Mem 0)
    (hR1 : R1.Mem (rot (2033 / 25000))) (hR2 : R2.Mem (rot (2927 / 25000)))
    (hR3 : R3.Mem (rot (453 / 12500))) (hR4 : R4.Mem (rot (-1971 / 25000)))
    (A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 A4 B4 E4 C4 G4 : Iv)
    (hA1 : A1.Mem ((1 + ((9 : ℝ) / 10)) ^ 2)) (hB1 : B1.Mem (2 * (1 - 6 * (9 / 10) + (9 / 10) ^ 2)))
    (hE1 : E1.Mem (2 * ((9 / 10) - 1) ^ 2)) (hC1 : C1.Mem (1 + 9 / 10)) (hG1 : G1.Mem (8 * (9 / 10)))
    (hA2 : A2.Mem ((1 + ((379 : ℝ) / 625)) ^ 2))
    (hB2 : B2.Mem (2 * (1 - 6 * (379 / 625) + (379 / 625) ^ 2)))
    (hE2 : E2.Mem (2 * ((379 / 625) - 1) ^ 2)) (hC2 : C2.Mem (1 + 379 / 625))
    (hG2 : G2.Mem (8 * (379 / 625)))
    (hA3 : A3.Mem ((1 + ((673 : ℝ) / 1250)) ^ 2))
    (hB3 : B3.Mem (2 * (1 - 6 * (673 / 1250) + (673 / 1250) ^ 2)))
    (hE3 : E3.Mem (2 * ((673 / 1250) - 1) ^ 2)) (hC3 : C3.Mem (1 + 673 / 1250))
    (hG3 : G3.Mem (8 * (673 / 1250)))
    (hA4 : A4.Mem ((1 + ((7487 : ℝ) / 10000)) ^ 2))
    (hB4 : B4.Mem (2 * (1 - 6 * (7487 / 10000) + (7487 / 10000) ^ 2)))
    (hE4 : E4.Mem (2 * ((7487 / 10000) - 1) ^ 2)) (hC4 : C4.Mem (1 + 7487 / 10000))
    (hG4 : G4.Mem (8 * (7487 / 10000)))
    (Bl C2l Dcl RC : Iv) (hBl : Bl.Mem (1 + ((36 : ℝ) / 5) ^ 2))
    (hC2l : C2l.Mem (16 * ((36 : ℝ) / 5) ^ 2))
    (hDcl : Dcl.Mem (2 * (((36 : ℝ) / 5) ^ 2 - 1))) (hRC : RC.Mem (-(4 / 5)))
    (hs1 : SlitSide A1 B1 E1 C1 G1 (sIn1 S491 D))
    (hs2 : SlitSide A2 B2 E2 C2 G2 (sIn2 S491 R1 A1 B1 E1 C1 G1 D))
    (hs3 : SlitSide A3 B3 E3 C3 G3 (sIn3 S491 R1 R2 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 D))
    (hs4 : SlitSide A4 B4 E4 C4 G4
      (sIn4 S491 R1 R2 R3 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 D))
    (hsl : LuneSide Bl C2l
      (sOut4 S491 R1 R2 R3 R4 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3
        A4 B4 E4 C4 G4 D).neg)
    (hdenl : 0 < m2r (((cst Dcl).re.sq).add ((cst Dcl).im.sq)).lo) :
    (psiAEncl S491 R1 R2 R3 R4 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3
      A4 B4 E4 C4 G4 Bl C2l Dcl RC D).Mem (psiA z) := by
  -- slit stage 1
  have h1 : (sIn2 S491 R1 A1 B1 E1 C1 G1 D).Mem
      (rot (2033 / 25000) * slit (9 / 10) ((((491 / 500 : ℝ)) : ℂ) * z)) :=
    slitStage_mem (9 / 10) (2033 / 25000) (by norm_num) (by norm_num) R1 hR1
      A1 B1 E1 C1 G1 hA1 hB1 hE1 hC1 hG1 (sIn1 S491 D) hs1
      (by
        show (S491.mul D).Mem ((((491 / 500 : ℝ)) : ℂ) * z)
        exact CD.mem_mul (mem_ofReal hS hS0) hz)
  -- slit stage 2
  have h2 : (sIn3 S491 R1 R2 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 D).Mem
      (rot (2927 / 25000) * slit (379 / 625)
        (rot (2033 / 25000) * slit (9 / 10) ((((491 / 500 : ℝ)) : ℂ) * z))) :=
    slitStage_mem (379 / 625) (2927 / 25000) (by norm_num) (by norm_num) R2 hR2
      A2 B2 E2 C2 G2 hA2 hB2 hE2 hC2 hG2 (sIn2 S491 R1 A1 B1 E1 C1 G1 D) hs2
      (by
        show (R1.mul (slitEncl A1 B1 E1 C1 G1 (sIn1 S491 D))).Mem
          (rot (2033 / 25000) * slit (9 / 10) ((((491 / 500 : ℝ)) : ℂ) * z))
        exact h1)
  -- slit stage 3
  have h3 : (sIn4 S491 R1 R2 R3 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 D).Mem
      (rot (453 / 12500) * slit (673 / 1250)
        (rot (2927 / 25000) * slit (379 / 625)
          (rot (2033 / 25000) * slit (9 / 10) ((((491 / 500 : ℝ)) : ℂ) * z)))) :=
    slitStage_mem (673 / 1250) (453 / 12500) (by norm_num) (by norm_num) R3 hR3
      A3 B3 E3 C3 G3 hA3 hB3 hE3 hC3 hG3
      (sIn3 S491 R1 R2 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 D) hs3
      (by
        show (R2.mul (slitEncl A2 B2 E2 C2 G2 (sIn2 S491 R1 A1 B1 E1 C1 G1 D))).Mem
          (rot (2927 / 25000) * slit (379 / 625)
            (rot (2033 / 25000) * slit (9 / 10) ((((491 / 500 : ℝ)) : ℂ) * z)))
        exact h2)
  -- slit stage 4
  have h4 : (sOut4 S491 R1 R2 R3 R4 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3
      A4 B4 E4 C4 G4 D).Mem
      (rot (-1971 / 25000) * slit (7487 / 10000)
        (rot (453 / 12500) * slit (673 / 1250)
          (rot (2927 / 25000) * slit (379 / 625)
            (rot (2033 / 25000) * slit (9 / 10) ((((491 / 500 : ℝ)) : ℂ) * z))))) :=
    slitStage_mem (7487 / 10000) (-1971 / 25000) (by norm_num) (by norm_num) R4 hR4
      A4 B4 E4 C4 G4 hA4 hB4 hE4 hC4 hG4
      (sIn4 S491 R1 R2 R3 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 D) hs4
      (by
        show (R3.mul (slitEncl A3 B3 E3 C3 G3
          (sIn3 S491 R1 R2 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 D))).Mem
          (rot (453 / 12500) * slit (673 / 1250)
            (rot (2927 / 25000) * slit (379 / 625)
              (rot (2033 / 25000) * slit (9 / 10) ((((491 / 500 : ℝ)) : ℂ) * z))))
        exact h3)
  -- the lune stage
  have h5 : ((sOut4 S491 R1 R2 R3 R4 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3
      A4 B4 E4 C4 G4 D).neg).Mem
      (-(rot (-1971 / 25000) * slit (7487 / 10000)
        (rot (453 / 12500) * slit (673 / 1250)
          (rot (2927 / 25000) * slit (379 / 625)
            (rot (2033 / 25000) * slit (9 / 10) ((((491 / 500 : ℝ)) : ℂ) * z)))))) :=
    CD.mem_neg h4
  have h6 := luneStage_mem (36 / 5) (by norm_num) RC hRC Bl C2l Dcl hBl hC2l hDcl
    ((sOut4 S491 R1 R2 R3 R4 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3
      A4 B4 E4 C4 G4 D).neg) hsl hdenl h5
  rw [show ((((491 / 500 : ℝ)) : ℂ)) = (491 / 500 : ℂ) by norm_num] at h6
  -- identify with `psiA z`
  have hval : (-(4 / 5 : ℂ)) * lune (36 / 5)
      (-(rot (-1971 / 25000) * slit (7487 / 10000)
        (rot (453 / 12500) * slit (673 / 1250)
          (rot (2927 / 25000) * slit (379 / 625)
            (rot (2033 / 25000) * slit (9 / 10) ((491 / 500 : ℂ) * z)))))) = psiA z := by
    simp only [psiA, slitsA]
  rw [← hval]
  rw [show psiAEncl S491 R1 R2 R3 R4 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3
        A4 B4 E4 C4 G4 Bl C2l Dcl RC D
      = (cst RC).mul (luneEncl Bl C2l Dcl
          (sOut4 S491 R1 R2 R3 R4 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3
            A4 B4 E4 C4 G4 D).neg) from rfl]
  exact h6

end

end Work.ANum

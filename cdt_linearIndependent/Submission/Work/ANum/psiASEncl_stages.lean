import Mathlib
import Submission.Work.ANum.BigChain

namespace Work.ANum

open Submission.CDTPlan

/-- **The scale-`S` contour chain, stage by stage**: given the per-stage enclosure facts (each
discharged separately by `slitEnclS_mem`/`luneEnclS_mem` plus the numeric side conditions), the
closures of the constants, and `z ∈ D`, every intermediate box of the chain `psiASEncl` contains the
corresponding partial composition of `psiA`. -/
theorem psiASEncl_stages (S : ℤ) (hS : 0 < S) (hIv : Work.ANum.IvHiSound S)
    (hCD : Work.ANum.CDHiSound S)
    (S491 R1 R2 R3 R4 : Work.ANum.CD)
    (A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 A4 B4 E4 C4 G4 Bl C2l Dcl RC : Work.ANum.Iv)
    (D : Work.ANum.CD) {z : ℂ}
    (hS491 : Work.ANum.CDHi.Mem S S491 ((491 / 500 : ℂ)))
    (hR1 : Work.ANum.CDHi.Mem S R1 (Submission.CDTPlan.rot (2033 / 25000)))
    (hR2 : Work.ANum.CDHi.Mem S R2 (Submission.CDTPlan.rot (2927 / 25000)))
    (hR3 : Work.ANum.CDHi.Mem S R3 (Submission.CDTPlan.rot (453 / 12500)))
    (hR4 : Work.ANum.CDHi.Mem S R4 (Submission.CDTPlan.rot (-1971 / 25000)))
    (hRC : Work.ANum.CDHi.Mem S (Work.ANum.CDHi.cst RC) ((-(4 / 5) : ℂ)))
    (hs1 : ∀ w : ℂ, Work.ANum.CDHi.Mem S (Work.ANum.sIn1S S S491 D) w →
      Work.ANum.CDHi.Mem S (Work.ANum.slitEnclS S A1 B1 E1 C1 G1 (Work.ANum.sIn1S S S491 D))
        (Submission.CDTPlan.slit (9 / 10) w))
    (hs2 : ∀ w : ℂ,
      Work.ANum.CDHi.Mem S (Work.ANum.sIn2S S S491 R1 A1 B1 E1 C1 G1 D) w →
      Work.ANum.CDHi.Mem S (Work.ANum.slitEnclS S A2 B2 E2 C2 G2
        (Work.ANum.sIn2S S S491 R1 A1 B1 E1 C1 G1 D)) (Submission.CDTPlan.slit (379 / 625) w))
    (hs3 : ∀ w : ℂ,
      Work.ANum.CDHi.Mem S
        (Work.ANum.sIn3S S S491 R1 R2 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 D) w →
      Work.ANum.CDHi.Mem S (Work.ANum.slitEnclS S A3 B3 E3 C3 G3
        (Work.ANum.sIn3S S S491 R1 R2 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 D))
        (Submission.CDTPlan.slit (673 / 1250) w))
    (hs4 : ∀ w : ℂ,
      Work.ANum.CDHi.Mem S (Work.ANum.sIn4S S S491 R1 R2 R3 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2
        A3 B3 E3 C3 G3 D) w →
      Work.ANum.CDHi.Mem S (Work.ANum.slitEnclS S A4 B4 E4 C4 G4
        (Work.ANum.sIn4S S S491 R1 R2 R3 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 D))
        (Submission.CDTPlan.slit (7487 / 10000) w))
    (hl : ∀ w : ℂ, Work.ANum.CDHi.Mem S (Work.ANum.CDHi.neg
        (Work.ANum.sOut4S S S491 R1 R2 R3 R4 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3
          A4 B4 E4 C4 G4 D)) w →
      Work.ANum.CDHi.Mem S (Work.ANum.luneEnclS S Bl C2l Dcl (Work.ANum.CDHi.neg
        (Work.ANum.sOut4S S S491 R1 R2 R3 R4 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3
          A4 B4 E4 C4 G4 D))) (Submission.CDTPlan.lune (36 / 5) w))
    (hz : Work.ANum.CDHi.Mem S D z) :
    Work.ANum.CDHi.Mem S (Work.ANum.sIn1S S S491 D) ((491 / 500 : ℂ) * z) ∧
    Work.ANum.CDHi.Mem S (Work.ANum.sIn2S S S491 R1 A1 B1 E1 C1 G1 D)
      (Submission.CDTPlan.rot (2033 / 25000) * Submission.CDTPlan.slit (9 / 10)
        ((491 / 500 : ℂ) * z)) ∧
    Work.ANum.CDHi.Mem S (Work.ANum.sIn3S S S491 R1 R2 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 D)
      (Submission.CDTPlan.rot (2927 / 25000) * Submission.CDTPlan.slit (379 / 625)
        (Submission.CDTPlan.rot (2033 / 25000) * Submission.CDTPlan.slit (9 / 10)
          ((491 / 500 : ℂ) * z))) ∧
    Work.ANum.CDHi.Mem S (Work.ANum.sIn4S S S491 R1 R2 R3 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3
        E3 C3 G3 D)
      (Submission.CDTPlan.rot (453 / 12500) * Submission.CDTPlan.slit (673 / 1250)
        (Submission.CDTPlan.rot (2927 / 25000) * Submission.CDTPlan.slit (379 / 625)
          (Submission.CDTPlan.rot (2033 / 25000) * Submission.CDTPlan.slit (9 / 10)
            ((491 / 500 : ℂ) * z)))) ∧
    Work.ANum.CDHi.Mem S
      (Work.ANum.sOut4S S S491 R1 R2 R3 R4 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3
        A4 B4 E4 C4 G4 D)
      (Submission.CDTPlan.rot (-1971 / 25000) * Submission.CDTPlan.slit (7487 / 10000)
        (Submission.CDTPlan.rot (453 / 12500) * Submission.CDTPlan.slit (673 / 1250)
          (Submission.CDTPlan.rot (2927 / 25000) * Submission.CDTPlan.slit (379 / 625)
            (Submission.CDTPlan.rot (2033 / 25000) * Submission.CDTPlan.slit (9 / 10)
              ((491 / 500 : ℂ) * z))))) ∧
    Work.ANum.CDHi.Mem S
      (Work.ANum.psiASEncl S S491 R1 R2 R3 R4 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3
        A4 B4 E4 C4 G4 Bl C2l Dcl RC D) (Submission.CDTPlan.psiA z) := by
  have h1 : CDHi.Mem S (sIn1S S S491 D) ((491 / 500 : ℂ) * z) := hCD.mem_mul hS491 hz
  have h2 : CDHi.Mem S (sIn2S S S491 R1 A1 B1 E1 C1 G1 D)
      (rot (2033 / 25000) * slit (9 / 10) ((491 / 500 : ℂ) * z)) :=
    hCD.mem_mul hR1 (hs1 _ h1)
  have h3 : CDHi.Mem S (sIn3S S S491 R1 R2 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 D)
      (rot (2927 / 25000) * slit (379 / 625)
        (rot (2033 / 25000) * slit (9 / 10) ((491 / 500 : ℂ) * z))) :=
    hCD.mem_mul hR2 (hs2 _ h2)
  have h4 : CDHi.Mem S (sIn4S S S491 R1 R2 R3 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3 D)
      (rot (453 / 12500) * slit (673 / 1250)
        (rot (2927 / 25000) * slit (379 / 625)
          (rot (2033 / 25000) * slit (9 / 10) ((491 / 500 : ℂ) * z)))) :=
    hCD.mem_mul hR3 (hs3 _ h3)
  have h5 : CDHi.Mem S
      (sOut4S S S491 R1 R2 R3 R4 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3
        A4 B4 E4 C4 G4 D)
      (rot (-1971 / 25000) * slit (7487 / 10000)
        (rot (453 / 12500) * slit (673 / 1250)
          (rot (2927 / 25000) * slit (379 / 625)
            (rot (2033 / 25000) * slit (9 / 10) ((491 / 500 : ℂ) * z))))) :=
    hCD.mem_mul hR4 (hs4 _ h4)
  have hneg : CDHi.Mem S (CDHi.neg
      (sOut4S S S491 R1 R2 R3 R4 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3
        A4 B4 E4 C4 G4 D))
      (-(rot (-1971 / 25000) * slit (7487 / 10000)
        (rot (453 / 12500) * slit (673 / 1250)
          (rot (2927 / 25000) * slit (379 / 625)
            (rot (2033 / 25000) * slit (9 / 10) ((491 / 500 : ℂ) * z)))))) :=
    hCD.mem_neg h5
  have hlune := hl _ hneg
  have hres := hCD.mem_mul hRC hlune
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  rw [show psiASEncl S S491 R1 R2 R3 R4 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3
        A4 B4 E4 C4 G4 Bl C2l Dcl RC D
      = CDHi.mul S (CDHi.cst RC) (luneEnclS S Bl C2l Dcl (CDHi.neg
        (sOut4S S S491 R1 R2 R3 R4 A1 B1 E1 C1 G1 A2 B2 E2 C2 G2 A3 B3 E3 C3 G3
          A4 B4 E4 C4 G4 D))) from by
    simp only [psiASEncl, CD.neg, CDHi.neg, Iv.neg, IvHi.neg]]
  simpa only [psiA, slitsA] using hres

end Work.ANum

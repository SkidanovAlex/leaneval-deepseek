import Mathlib
import Submission.Work.Pi6.SQM.Cup3CobSetup
import Submission.Work.Pi6.SQM.c4faces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff)

theorem cup3FaceSwapC4_faceU (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T4Idx n m) :
    faceU n m hn hm (swapC4 n m hn hm p) = faceU n m hn hm (Sum.inr (Sum.inr (Sum.inl p))) := by
  obtain ⟨⟨a,b,c,j⟩,h⟩ := p
  dsimp only at h
  dsimp only [faceU, swapC4]
  split_ifs
  · -- 1a: J = 0, 1 ≤ B ; T3 (A+1) (B-1) C (A+1)
    have hB : (1:ℕ) ≤ b.val := ‹(1:ℕ) ≤ b.val›
    dsimp only [idxC3, mkT3, C3a, C3b, C3c, C3j, C3h, c3U, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only [Nat.sub_add_cancel hB] using
      (B1 hn hm a.val (b.val - 1 + 1) (c.val + 1) (by omega) (by omega) (by omega)
        (by omega) (by omega)).1
  · -- 1b: J = 0, B = 0, 1 ≤ C ; T4 (A+1) 0 (C-1) 1
    have hB0' : ¬(1:ℕ) ≤ b.val := ‹¬(1:ℕ) ≤ b.val›
    have hC : (1:ℕ) ≤ c.val := ‹(1:ℕ) ≤ c.val›
    have hB0 : b.val = 0 := by omega
    dsimp only [idxC4, mkT4, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only [hB0, Nat.sub_add_cancel hC] using
      (B5ii hn hm a.val c.val (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)).1.symm
  · -- 1c-i: J = 0, B = C = 0, m = 2, A+3 = n ; T1 (A+1) 0
    have hB0' : ¬(1:ℕ) ≤ b.val := ‹¬(1:ℕ) ≤ b.val›
    have hC0' : ¬(1:ℕ) ≤ c.val := ‹¬(1:ℕ) ≤ c.val›
    have hm2 : m = 2 := ‹m = 2›
    have hAn : a.val + 3 = n := ‹a.val + 3 = n›
    have hB0 : b.val = 0 := by omega
    have hC0 : c.val = 0 := by omega
    dsimp only [idxT1, mkT1, t1U, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only [hB0, hC0] using (c4faceT1 n m hn hm a.val hm2 hAn).1
  · -- 1c-ii: J = 0, B = C = 0, m = 2, A+3 ≠ n ; T4 (A+1) 0 0 3
    have hB0' : ¬(1:ℕ) ≤ b.val := ‹¬(1:ℕ) ≤ b.val›
    have hC0' : ¬(1:ℕ) ≤ c.val := ‹¬(1:ℕ) ≤ c.val›
    have hm2 : m = 2 := ‹m = 2›
    have hAn : ¬(a.val + 3 = n) := ‹¬(a.val + 3 = n)›
    have hB0 : b.val = 0 := by omega
    have hC0 : c.val = 0 := by omega
    have hA4 : a.val + 4 ≤ n := by omega
    dsimp only [idxC4, mkT4, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only [hB0, hC0] using (c4faceT4a n m hn hm a.val hm2 hA4).1
  · -- 1d: J = 0, B = C = 0, m ≠ 2 ; T3 (A+1) 0 0 (A+3)
    have hB0' : ¬(1:ℕ) ≤ b.val := ‹¬(1:ℕ) ≤ b.val›
    have hC0' : ¬(1:ℕ) ≤ c.val := ‹¬(1:ℕ) ≤ c.val›
    have hm2 : ¬(m = 2) := ‹¬(m = 2)›
    have hm3 : 3 ≤ m := by omega
    have hB0 : b.val = 0 := by omega
    have hC0 : c.val = 0 := by omega
    dsimp only [idxC3, mkT3, C3a, C3b, C3c, C3j, C3h, c3U, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only [hB0, hC0] using
      (B3iii hn hm a.val (by omega) hm3 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)).1
  · -- 2: J ≠ 0, J ≤ B ; L (J+A) A (B-1) C
    have hJ0 : ¬(j.val = 0) := ‹¬(j.val = 0)›
    have hJB : j.val ≤ b.val := ‹j.val ≤ b.val›
    have hB : (1:ℕ) ≤ b.val := by omega
    dsimp only [idxL, mkL, L3k, L3a, L3b, L3c, L3h, lU, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only [Nat.sub_add_cancel hB] using
      @reg2u n m n m a.val (b.val - 1 + 1) (c.val + 1) (j.val + a.val) hn hm (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
  · -- 3a: ¬h1, ¬(J ≤ B), J ≤ B+1, 1 ≤ B ; T3 A (B-1) (C+1) (A+1)
    have hJB1 : ¬(j.val ≤ b.val) := ‹¬(j.val ≤ b.val)›
    have hJB2 : j.val ≤ b.val + 1 := ‹j.val ≤ b.val + 1›
    have hB : (1:ℕ) ≤ b.val := ‹(1:ℕ) ≤ b.val›
    have hsub : (b.val - 1) + 1 = b.val := Nat.sub_add_cancel hB
    have hsub' : (b.val + 1) - 1 = b.val := by omega
    dsimp only [idxC3, mkT3, C3a, C3b, C3c, C3j, C3h, c3U, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only [hsub, hsub'] using
      (B6i hn hm a.val (b.val + 1) (c.val + 1) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)).1.symm
  · -- 3b: ... , B = 0, 1 ≤ A ; T4 (A-1) 0 (C+1) 0
    have hJB1 : ¬(j.val ≤ b.val) := ‹¬(j.val ≤ b.val)›
    have hJB2 : j.val ≤ b.val + 1 := ‹j.val ≤ b.val + 1›
    have hB0' : ¬(1:ℕ) ≤ b.val := ‹¬(1:ℕ) ≤ b.val›
    have hA1 : (1:ℕ) ≤ a.val := ‹(1:ℕ) ≤ a.val›
    have hB0 : b.val = 0 := by omega
    dsimp only [idxC4, mkT4, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only [hB0, Nat.sub_add_cancel hA1] using
      (B5ii hn hm (a.val - 1) (c.val + 1) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).1
  · -- 3c: ..., B = 0, A = 0 ; T2 0 (C+1)
    have hJB1 : ¬(j.val ≤ b.val) := ‹¬(j.val ≤ b.val)›
    have hJB2 : j.val ≤ b.val + 1 := ‹j.val ≤ b.val + 1›
    have hB0' : ¬(1:ℕ) ≤ b.val := ‹¬(1:ℕ) ≤ b.val›
    have hA0' : ¬(1:ℕ) ≤ a.val := ‹¬(1:ℕ) ≤ a.val›
    have hA0 : a.val = 0 := by omega
    have hB0 : b.val = 0 := by omega
    dsimp only [idxT2, mkT2, t2U, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only [hA0, hB0] using
      (C3 hn hm (c.val + 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).1.symm
  · -- 4a: ..., J ≤ B+2, B+3 ≤ m ; T3 A B (C+1) (A+C+3)
    have hJB2 : ¬(j.val ≤ b.val + 1) := ‹¬(j.val ≤ b.val + 1)›
    have hJB3 : j.val ≤ b.val + 2 := ‹j.val ≤ b.val + 2›
    have hB3 : b.val + 3 ≤ m := ‹b.val + 3 ≤ m›
    have hidx : a.val + (c.val + 1) + 2 = a.val + c.val + 3 := by omega
    dsimp only [idxC3, mkT3, C3a, C3b, C3c, C3j, C3h, c3U, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only [hidx] using
      (B7i hn hm a.val (b.val + 1) (c.val + 1) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)).1.symm
  · -- 4b: ..., J ≤ B+2, ¬(B+3 ≤ m), A+C+4 ≤ n ; T4 A (m-2) (C+1) (m+1)
    have hJB2 : ¬(j.val ≤ b.val + 1) := ‹¬(j.val ≤ b.val + 1)›
    have hJB3 : j.val ≤ b.val + 2 := ‹j.val ≤ b.val + 2›
    have hB3 : ¬(b.val + 3 ≤ m) := ‹¬(b.val + 3 ≤ m)›
    have hAC4 : a.val + c.val + 4 ≤ n := ‹a.val + c.val + 4 ≤ n›
    have hBm : b.val + 1 = m - 1 := by omega
    have hwm : (m:ℕ) - 2 + 1 = m - 1 := by omega
    dsimp only [idxC4, mkT4, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only [hBm, hwm] using
      (B7ii hn hm a.val (c.val + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)).1.symm
  · -- 4c: ..., J ≤ B+2, ¬(B+3 ≤ m), ¬(A+C+4 ≤ n) ; T1 A (m-2)
    have hJB2 : ¬(j.val ≤ b.val + 1) := ‹¬(j.val ≤ b.val + 1)›
    have hJB3 : j.val ≤ b.val + 2 := ‹j.val ≤ b.val + 2›
    have hB3 : ¬(b.val + 3 ≤ m) := ‹¬(b.val + 3 ≤ m)›
    have hAC4 : ¬(a.val + c.val + 4 ≤ n) := ‹¬(a.val + c.val + 4 ≤ n)›
    have hBm : b.val + 1 = m - 1 := by omega
    have hwm : (m:ℕ) - 2 + 1 = m - 1 := by omega
    dsimp only [idxT1, mkT1, t1U, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only [hBm, hwm] using
      (C5 hn hm a.val (c.val + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)).1.symm
  · -- 5: ¬(J ≤ B+2), J ≤ m ; L (J+A+C) A B C
    have hJB3 : ¬(j.val ≤ b.val + 2) := ‹¬(j.val ≤ b.val + 2)›
    have hJm : j.val ≤ m := ‹j.val ≤ m›
    dsimp only [idxL, mkL, L3k, L3a, L3b, L3c, L3h, lU, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only using
      @reg4u n m n m a.val (b.val + 1) (c.val + 1) (j.val + a.val + c.val) hn hm (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
  · -- 6: ..., ¬(J ≤ m), B+3 ≤ m ; T3 A B C (A+C+3)
    have hJm : ¬(j.val ≤ m) := ‹¬(j.val ≤ m)›
    have hB3 : b.val + 3 ≤ m := ‹b.val + 3 ≤ m›
    have hidx : a.val + (c.val + 1) + 2 = a.val + c.val + 3 := by omega
    dsimp only [idxC3, mkT3, C3a, C3b, C3c, C3j, C3h, c3U, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only [hidx] using
      (B8i hn hm a.val (b.val + 1) (c.val + 1) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)).1.symm
  · -- 7: ..., ¬(B+3 ≤ m), 1 ≤ C ; T4 A (m-2) (C-1) m
    have hJm : ¬(j.val ≤ m) := ‹¬(j.val ≤ m)›
    have hB3 : ¬(b.val + 3 ≤ m) := ‹¬(b.val + 3 ≤ m)›
    have hC1 : (1:ℕ) ≤ c.val := ‹(1:ℕ) ≤ c.val›
    have hBm : b.val + 1 = m - 1 := by omega
    have hwm : (m:ℕ) - 2 + 1 = m - 1 := by omega
    dsimp only [idxC4, mkT4, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only [hBm, hwm, Nat.sub_add_cancel hC1] using
      (B7ii hn hm a.val c.val (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)).1
  · -- 8a: ..., ¬(1 ≤ C), m = 2, A = 0 ; T2 0 0
    have hJm : ¬(j.val ≤ m) := ‹¬(j.val ≤ m)›
    have hB3 : ¬(b.val + 3 ≤ m) := ‹¬(b.val + 3 ≤ m)›
    have hC0' : ¬(1:ℕ) ≤ c.val := ‹¬(1:ℕ) ≤ c.val›
    have hm2 : m = 2 := ‹m = 2›
    have hA0 : a.val = 0 := ‹a.val = 0›
    have hB0 : b.val = 0 := by omega
    have hC0 : c.val = 0 := by omega
    have hn3 : 3 ≤ n := by omega
    dsimp only [idxT2, mkT2, t2U, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only [hA0, hB0, hC0] using (c4faceT2b n m hn hm hm2 hn3).1
  · -- 8b: ..., ¬(1 ≤ C), m = 2, A ≠ 0 ; T4 (A-1) 0 0 0
    have hJm : ¬(j.val ≤ m) := ‹¬(j.val ≤ m)›
    have hB3 : ¬(b.val + 3 ≤ m) := ‹¬(b.val + 3 ≤ m)›
    have hC0' : ¬(1:ℕ) ≤ c.val := ‹¬(1:ℕ) ≤ c.val›
    have hm2 : m = 2 := ‹m = 2›
    have hA0' : ¬(a.val = 0) := ‹¬(a.val = 0)›
    have hA1 : (1:ℕ) ≤ a.val := by omega
    have hB0 : b.val = 0 := by omega
    have hC0 : c.val = 0 := by omega
    have hA3 : a.val + 3 ≤ n := by omega
    dsimp only [idxC4, mkT4, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only [hB0, hC0] using (c4faceT4b n m hn hm a.val hm2 hA1 hA3).1
  · -- 9: ..., ¬(1 ≤ C), ¬(m = 2) ; T3 A (m-3) 0 (A+1)
    have hJm : ¬(j.val ≤ m) := ‹¬(j.val ≤ m)›
    have hB3 : ¬(b.val + 3 ≤ m) := ‹¬(b.val + 3 ≤ m)›
    have hC0' : ¬(1:ℕ) ≤ c.val := ‹¬(1:ℕ) ≤ c.val›
    have hm2 : ¬(m = 2) := ‹¬(m = 2)›
    have hm3 : 3 ≤ m := by omega
    have hBm : b.val + 1 = m - 1 := by omega
    have hC0 : c.val = 0 := by omega
    have hwm : (m:ℕ) - 3 + 1 = m - 2 := by omega
    dsimp only [idxC3, mkT3, C3a, C3b, C3c, C3j, C3h, c3U, c4U, C4a, C4b, C4c, C4j, C4h]
    simpa only [hBm, hC0, hwm] using
      (B2iii hn hm hm3 a.val (by omega)).1
theorem cup3FaceSwapC4_faceV (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T4Idx n m) :
    faceV n m hn hm (swapC4 n m hn hm p) = faceV n m hn hm (Sum.inr (Sum.inr (Sum.inl p))) := by
  obtain ⟨⟨a,b,c,j⟩,h⟩ := p
  dsimp only at h
  dsimp only [faceV, swapC4]
  split_ifs
  · -- 1a: J = 0, 1 ≤ B ; T3 (A+1) (B-1) C (A+1)
    have hJ : j.val = 0 := ‹j.val = 0›
    have hB : (1:ℕ) ≤ b.val := ‹(1:ℕ) ≤ b.val›
    have hj : j = (⟨0, by omega⟩ : Fin (m+2)) := by ext; exact hJ
    dsimp only [idxC3, mkT3, C3a, C3b, C3c, C3j, C3h, c3V, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [hj, Nat.sub_add_cancel hB] using
      (B1 hn hm a.val (b.val - 1 + 1) (c.val + 1) (by omega) (by omega) (by omega)
        (by omega) (by omega)).2
  · -- 1b: J = 0, B = 0, 1 ≤ C ; T4 (A+1) 0 (C-1) 1
    have hJ : j.val = 0 := ‹j.val = 0›
    have hB0' : ¬(1:ℕ) ≤ b.val := ‹¬(1:ℕ) ≤ b.val›
    have hC : (1:ℕ) ≤ c.val := ‹(1:ℕ) ≤ c.val›
    have hB0 : b.val = 0 := by omega
    have hj : j = (⟨0, by omega⟩ : Fin (m+2)) := by ext; exact hJ
    dsimp only [idxC4, mkT4, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [hj, hB0, Nat.sub_add_cancel hC] using
      (B5ii hn hm a.val c.val (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)).2.symm
  · -- 1c-i: J = 0, B = C = 0, m = 2, A+3 = n ; T1 (A+1) 0
    have hJ : j.val = 0 := ‹j.val = 0›
    have hB0' : ¬(1:ℕ) ≤ b.val := ‹¬(1:ℕ) ≤ b.val›
    have hC0' : ¬(1:ℕ) ≤ c.val := ‹¬(1:ℕ) ≤ c.val›
    have hm2 : m = 2 := ‹m = 2›
    have hAn : a.val + 3 = n := ‹a.val + 3 = n›
    have hB0 : b.val = 0 := by omega
    have hC0 : c.val = 0 := by omega
    have hj : j = (⟨0, by omega⟩ : Fin (m+2)) := by ext; exact hJ
    dsimp only [idxT1, mkT1, t1V, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [hj, hB0, hC0] using (c4faceT1 n m hn hm a.val hm2 hAn).2
  · -- 1c-ii: J = 0, B = C = 0, m = 2, A+3 ≠ n ; T4 (A+1) 0 0 3
    have hJ : j.val = 0 := ‹j.val = 0›
    have hB0' : ¬(1:ℕ) ≤ b.val := ‹¬(1:ℕ) ≤ b.val›
    have hC0' : ¬(1:ℕ) ≤ c.val := ‹¬(1:ℕ) ≤ c.val›
    have hm2 : m = 2 := ‹m = 2›
    have hAn : ¬(a.val + 3 = n) := ‹¬(a.val + 3 = n)›
    have hB0 : b.val = 0 := by omega
    have hC0 : c.val = 0 := by omega
    have hA4 : a.val + 4 ≤ n := by omega
    have hj : j = (⟨0, by omega⟩ : Fin (m+2)) := by ext; exact hJ
    dsimp only [idxC4, mkT4, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [hj, hB0, hC0] using (c4faceT4a n m hn hm a.val hm2 hA4).2
  · -- 1d: J = 0, B = C = 0, m ≠ 2 ; T3 (A+1) 0 0 (A+3)
    have hJ : j.val = 0 := ‹j.val = 0›
    have hB0' : ¬(1:ℕ) ≤ b.val := ‹¬(1:ℕ) ≤ b.val›
    have hC0' : ¬(1:ℕ) ≤ c.val := ‹¬(1:ℕ) ≤ c.val›
    have hm2 : ¬(m = 2) := ‹¬(m = 2)›
    have hm3 : 3 ≤ m := by omega
    have hB0 : b.val = 0 := by omega
    have hC0 : c.val = 0 := by omega
    have hj : j = (⟨0, by omega⟩ : Fin (m+2)) := by ext; exact hJ
    dsimp only [idxC3, mkT3, C3a, C3b, C3c, C3j, C3h, c3V, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [hj, hB0, hC0] using
      (B3iii hn hm a.val (by omega) hm3 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)).2
  · -- 2: J ≠ 0, J ≤ B ; L (J+A) A (B-1) C
    have hJ0 : ¬(j.val = 0) := ‹¬(j.val = 0)›
    have hJB : j.val ≤ b.val := ‹j.val ≤ b.val›
    have hB : (1:ℕ) ≤ b.val := by omega
    have hsubA : (j.val + a.val) - a.val = j.val := by omega
    dsimp only [idxL, mkL, L3k, L3a, L3b, L3c, L3h, lV, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [Nat.sub_add_cancel hB, hsubA] using
      @reg2v n m n m a.val (b.val - 1 + 1) (c.val + 1) (j.val + a.val) hn hm (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
  · -- 3a: ¬h1, ¬(J ≤ B), J ≤ B+1, 1 ≤ B ; T3 A (B-1) (C+1) (A+1)
    have hJB1 : ¬(j.val ≤ b.val) := ‹¬(j.val ≤ b.val)›
    have hJB2 : j.val ≤ b.val + 1 := ‹j.val ≤ b.val + 1›
    have hB : (1:ℕ) ≤ b.val := ‹(1:ℕ) ≤ b.val›
    have hJB : j.val = b.val + 1 := by omega
    have hsub : (b.val - 1) + 1 = b.val := Nat.sub_add_cancel hB
    have hsub' : (b.val + 1) - 1 = b.val := by omega
    have hj : j = (⟨b.val + 1, by omega⟩ : Fin (m+2)) := by ext; exact hJB
    dsimp only [idxC3, mkT3, C3a, C3b, C3c, C3j, C3h, c3V, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [hsub, hsub', hj] using
      (B6i hn hm a.val (b.val + 1) (c.val + 1) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)).2.symm
  · -- 3b: ... , B = 0, 1 ≤ A ; T4 (A-1) 0 (C+1) 0
    have hJB1 : ¬(j.val ≤ b.val) := ‹¬(j.val ≤ b.val)›
    have hJB2 : j.val ≤ b.val + 1 := ‹j.val ≤ b.val + 1›
    have hB0' : ¬(1:ℕ) ≤ b.val := ‹¬(1:ℕ) ≤ b.val›
    have hA1 : (1:ℕ) ≤ a.val := ‹(1:ℕ) ≤ a.val›
    have hB0 : b.val = 0 := by omega
    have hJ1 : j.val = 1 := by omega
    have hj : j = (⟨1, by omega⟩ : Fin (m+2)) := by ext; exact hJ1
    dsimp only [idxC4, mkT4, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [hj, hB0, Nat.sub_add_cancel hA1] using
      (B5ii hn hm (a.val - 1) (c.val + 1) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).2
  · -- 3c: ..., B = 0, A = 0 ; T2 0 (C+1)
    have hJB1 : ¬(j.val ≤ b.val) := ‹¬(j.val ≤ b.val)›
    have hJB2 : j.val ≤ b.val + 1 := ‹j.val ≤ b.val + 1›
    have hB0' : ¬(1:ℕ) ≤ b.val := ‹¬(1:ℕ) ≤ b.val›
    have hA0' : ¬(1:ℕ) ≤ a.val := ‹¬(1:ℕ) ≤ a.val›
    have hA0 : a.val = 0 := by omega
    have hB0 : b.val = 0 := by omega
    have hJ1 : j.val = 1 := by omega
    have hj : j = (⟨1, by omega⟩ : Fin (m+2)) := by ext; exact hJ1
    dsimp only [idxT2, mkT2, t2V, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [hj, hA0, hB0] using
      (C3 hn hm (c.val + 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).2.symm
  · -- 4a: ..., J ≤ B+2, B+3 ≤ m ; T3 A B (C+1) (A+C+3)
    have hJB2 : ¬(j.val ≤ b.val + 1) := ‹¬(j.val ≤ b.val + 1)›
    have hJB3 : j.val ≤ b.val + 2 := ‹j.val ≤ b.val + 2›
    have hB3 : b.val + 3 ≤ m := ‹b.val + 3 ≤ m›
    have hJ2 : j.val = b.val + 2 := by omega
    have hj : j = (⟨b.val + 2, by omega⟩ : Fin (m+2)) := by ext; exact hJ2
    dsimp only [idxC3, mkT3, C3a, C3b, C3c, C3j, C3h, c3V, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [hj] using
      (B7i hn hm a.val (b.val + 1) (c.val + 1) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)).2.symm
  · -- 4b: ..., J ≤ B+2, ¬(B+3 ≤ m), A+C+4 ≤ n ; T4 A (m-2) (C+1) (m+1)
    have hJB2 : ¬(j.val ≤ b.val + 1) := ‹¬(j.val ≤ b.val + 1)›
    have hJB3 : j.val ≤ b.val + 2 := ‹j.val ≤ b.val + 2›
    have hB3 : ¬(b.val + 3 ≤ m) := ‹¬(b.val + 3 ≤ m)›
    have hAC4 : a.val + c.val + 4 ≤ n := ‹a.val + c.val + 4 ≤ n›
    have hBm : b.val + 1 = m - 1 := by omega
    have hwm : (m:ℕ) - 2 + 1 = m - 1 := by omega
    have hJm : j.val = m := by omega
    have hj : j = (⟨m, by omega⟩ : Fin (m+2)) := by ext; exact hJm
    dsimp only [idxC4, mkT4, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [hj, hBm, hwm] using
      (B7ii hn hm a.val (c.val + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)).2.symm
  · -- 4c: ..., J ≤ B+2, ¬(B+3 ≤ m), ¬(A+C+4 ≤ n) ; T1 A (m-2)
    have hJB2 : ¬(j.val ≤ b.val + 1) := ‹¬(j.val ≤ b.val + 1)›
    have hJB3 : j.val ≤ b.val + 2 := ‹j.val ≤ b.val + 2›
    have hB3 : ¬(b.val + 3 ≤ m) := ‹¬(b.val + 3 ≤ m)›
    have hAC4 : ¬(a.val + c.val + 4 ≤ n) := ‹¬(a.val + c.val + 4 ≤ n)›
    have hBm : b.val + 1 = m - 1 := by omega
    have hwm : (m:ℕ) - 2 + 1 = m - 1 := by omega
    have hJm : j.val = m := by omega
    have hj : j = (⟨m, by omega⟩ : Fin (m+2)) := by ext; exact hJm
    dsimp only [idxT1, mkT1, t1V, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [hj, hBm, hwm] using
      (C5 hn hm a.val (c.val + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)).2.symm
  · -- 5: ¬(J ≤ B+2), J ≤ m ; L (J+A+C) A B C
    have hJB3 : ¬(j.val ≤ b.val + 2) := ‹¬(j.val ≤ b.val + 2)›
    have hJm : j.val ≤ m := ‹j.val ≤ m›
    have hsub2 : (j.val + a.val + c.val) - a.val - (c.val + 1) + 1 = j.val := by omega
    dsimp only [idxL, mkL, L3k, L3a, L3b, L3c, L3h, lV, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [hsub2] using
      @reg4v n m n m a.val (b.val + 1) (c.val + 1) (j.val + a.val + c.val) hn hm (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
  · -- 6: ..., ¬(J ≤ m), B+3 ≤ m ; T3 A B C (A+C+3)
    have hJm : ¬(j.val ≤ m) := ‹¬(j.val ≤ m)›
    have hB3 : b.val + 3 ≤ m := ‹b.val + 3 ≤ m›
    have hJm1 : j.val = m + 1 := by omega
    have hj : j = (⟨m + 1, by omega⟩ : Fin (m+2)) := by ext; exact hJm1
    dsimp only [idxC3, mkT3, C3a, C3b, C3c, C3j, C3h, c3V, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [hj] using
      (B8i hn hm a.val (b.val + 1) (c.val + 1) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)).2.symm
  · -- 7: ..., ¬(B+3 ≤ m), 1 ≤ C ; T4 A (m-2) (C-1) m
    have hJm : ¬(j.val ≤ m) := ‹¬(j.val ≤ m)›
    have hB3 : ¬(b.val + 3 ≤ m) := ‹¬(b.val + 3 ≤ m)›
    have hC1 : (1:ℕ) ≤ c.val := ‹(1:ℕ) ≤ c.val›
    have hBm : b.val + 1 = m - 1 := by omega
    have hwm : (m:ℕ) - 2 + 1 = m - 1 := by omega
    have hJm1 : j.val = m + 1 := by omega
    have hCsub : (c.val - 1) + 1 = c.val := Nat.sub_add_cancel hC1
    have hj : j = (⟨m + 1, by omega⟩ : Fin (m+2)) := by ext; exact hJm1
    dsimp only [idxC4, mkT4, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [hj, hBm, hwm, hCsub] using
      (B7ii hn hm a.val c.val (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)).2
  · -- 8a: ..., ¬(1 ≤ C), m = 2, A = 0 ; T2 0 0
    have hJm : ¬(j.val ≤ m) := ‹¬(j.val ≤ m)›
    have hB3 : ¬(b.val + 3 ≤ m) := ‹¬(b.val + 3 ≤ m)›
    have hC0' : ¬(1:ℕ) ≤ c.val := ‹¬(1:ℕ) ≤ c.val›
    have hm2 : m = 2 := ‹m = 2›
    have hA0 : a.val = 0 := ‹a.val = 0›
    have hB0 : b.val = 0 := by omega
    have hC0 : c.val = 0 := by omega
    have hJ3 : j.val = 3 := by omega
    have hn3 : 3 ≤ n := by omega
    have hj : j = (⟨3, by omega⟩ : Fin (m+2)) := by ext; exact hJ3
    dsimp only [idxT2, mkT2, t2V, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [hj, hA0, hB0, hC0] using (c4faceT2b n m hn hm hm2 hn3).2
  · -- 8b: ..., ¬(1 ≤ C), m = 2, A ≠ 0 ; T4 (A-1) 0 0 0
    have hJm : ¬(j.val ≤ m) := ‹¬(j.val ≤ m)›
    have hB3 : ¬(b.val + 3 ≤ m) := ‹¬(b.val + 3 ≤ m)›
    have hC0' : ¬(1:ℕ) ≤ c.val := ‹¬(1:ℕ) ≤ c.val›
    have hm2 : m = 2 := ‹m = 2›
    have hA0' : ¬(a.val = 0) := ‹¬(a.val = 0)›
    have hA1 : (1:ℕ) ≤ a.val := by omega
    have hB0 : b.val = 0 := by omega
    have hC0 : c.val = 0 := by omega
    have hJ3 : j.val = 3 := by omega
    have hA3 : a.val + 3 ≤ n := by omega
    have hj : j = (⟨3, by omega⟩ : Fin (m+2)) := by ext; exact hJ3
    dsimp only [idxC4, mkT4, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [hj, hB0, hC0] using (c4faceT4b n m hn hm a.val hm2 hA1 hA3).2
  · -- 9: ..., ¬(1 ≤ C), ¬(m = 2) ; T3 A (m-3) 0 (A+1)
    have hJm : ¬(j.val ≤ m) := ‹¬(j.val ≤ m)›
    have hB3 : ¬(b.val + 3 ≤ m) := ‹¬(b.val + 3 ≤ m)›
    have hC0' : ¬(1:ℕ) ≤ c.val := ‹¬(1:ℕ) ≤ c.val›
    have hm2 : ¬(m = 2) := ‹¬(m = 2)›
    have hm3 : 3 ≤ m := by omega
    have hBm : b.val + 1 = m - 1 := by omega
    have hC0 : c.val = 0 := by omega
    have hwm : (m:ℕ) - 3 + 1 = m - 2 := by omega
    have hJm1 : j.val = m + 1 := by omega
    have hj : j = (⟨m + 1, by omega⟩ : Fin (m+2)) := by ext; exact hJm1
    dsimp only [idxC3, mkT3, C3a, C3b, C3c, C3j, C3h, c3V, c4V, C4a, C4b, C4c, C4j, C4h]
    simpa only [hj, hBm, hC0, hwm] using
      (B2iii hn hm hm3 a.val (by omega)).2

theorem cup3FaceSwapC4 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : Work.Pi6.SQM.T4Idx n m) :
    Work.Pi6.SQM.faceU n m hn hm (Work.Pi6.SQM.swapC4 n m hn hm p) = Work.Pi6.SQM.faceU n m hn hm (Sum.inr (Sum.inr (Sum.inl p))) ∧
    Work.Pi6.SQM.faceV n m hn hm (Work.Pi6.SQM.swapC4 n m hn hm p) = Work.Pi6.SQM.faceV n m hn hm (Sum.inr (Sum.inr (Sum.inl p))) := by
  exact ⟨cup3FaceSwapC4_faceU n m hn hm p, cup3FaceSwapC4_faceV n m hn hm p⟩

end

end Work.Pi6.SQM

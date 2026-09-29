import Mathlib
import Submission.Work.IntLib.cleanupSpec

/-!
# `Work.IntLib.cleanupSpecStk0`: `Div.cleanup` restores stack 0 as well

`Work.IntLib.cleanupSpec` records that `Div.cleanup` restores every stack but stack 0 (to its entry
content `b0`).  This file supplies the missing clause: stack 0 is *unchanged*, i.e. equal to its
entry content `s.stk 0` (which is not `b0.stk 0` in general, since stack 0 carries the value being
built).  The proof is the same induction on the nine regions (`dropRegions_le`), whose final clause
says precisely that a stack which is not one of the nine cleaned stacks is untouched; `0` is not one
of `stP … stY = 1 … 9`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib

open HvdH

theorem cleanupSpecStk0 (main : HvdH.Cmd) (b0 : HvdH.State) (s : HvdH.State)
    (lP lB lR lQ lS lC lD lX lY : List HvdH.Glyph)
    (hP : s.stk Work.IntLib.Div.stP = lP ++ [Work.IntLib.gP] ++ b0.stk Work.IntLib.Div.stP)
    (hB : s.stk Work.IntLib.Div.stB = lB ++ [Work.IntLib.gB] ++ b0.stk Work.IntLib.Div.stB)
    (hR : s.stk Work.IntLib.Div.stR = lR ++ [Work.IntLib.gR] ++ b0.stk Work.IntLib.Div.stR)
    (hQ : s.stk Work.IntLib.Div.stQ = lQ ++ [Work.IntLib.gQ] ++ b0.stk Work.IntLib.Div.stQ)
    (hS : s.stk Work.IntLib.Div.stS = lS ++ [Work.IntLib.gS] ++ b0.stk Work.IntLib.Div.stS)
    (hC : s.stk Work.IntLib.Div.stC = lC ++ [Work.IntLib.gC] ++ b0.stk Work.IntLib.Div.stC)
    (hDl : s.stk Work.IntLib.Div.stD = lD ++ [Work.IntLib.gD] ++ b0.stk Work.IntLib.Div.stD)
    (hX : s.stk Work.IntLib.Div.stX = lX ++ [Work.IntLib.gX] ++ b0.stk Work.IntLib.Div.stX)
    (hY : s.stk Work.IntLib.Div.stY = lY ++ [Work.IntLib.gY] ++ b0.stk Work.IntLib.Div.stY)
    (nP : ∀ g ∈ lP, g ≠ Work.IntLib.gP) (nB : ∀ g ∈ lB, g ≠ Work.IntLib.gB)
    (nR : ∀ g ∈ lR, g ≠ Work.IntLib.gR) (nQ : ∀ g ∈ lQ, g ≠ Work.IntLib.gQ)
    (nS : ∀ g ∈ lS, g ≠ Work.IntLib.gS) (nC : ∀ g ∈ lC, g ≠ Work.IntLib.gC)
    (nD : ∀ g ∈ lD, g ≠ Work.IntLib.gD) (nX : ∀ g ∈ lX, g ≠ Work.IntLib.gX)
    (nY : ∀ g ∈ lY, g ≠ Work.IntLib.gY)
    (hoth : ∀ k : HvdH.Stk, 10 ≤ k.val → s.stk k = b0.stk k) :
    ∃ s' n, HvdH.Eval main Work.IntLib.Div.cleanup s s' n ∧
      n ≤ 5 * (lP.length + lB.length + lR.length + lQ.length + lS.length + lC.length +
        lD.length + lX.length + lY.length) + 117 ∧
      s'.stk 0 = s.stk 0 ∧
      (∀ k : HvdH.Stk, k ≠ 0 → s'.stk k = b0.stk k) := by
  have hnodup : ((Work.IntLib.cleanupParts lP lB lR lQ lS lC lD lX lY).map (fun p => p.1)).Nodup := by
    simp only [Work.IntLib.cleanupParts, List.map_cons, List.map_nil]
    decide
  obtain ⟨s', n, hev, hn, hstk, hoth'⟩ :=
    Work.IntLib.dropRegions_le main b0 (Work.IntLib.cleanupParts lP lB lR lQ lS lC lD lX lY) s hnodup
      (by
        intro p hp
        simp only [Work.IntLib.cleanupParts, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simpa [List.append_assoc] using hP
        · simpa [List.append_assoc] using hB
        · simpa [List.append_assoc] using hR
        · simpa [List.append_assoc] using hQ
        · simpa [List.append_assoc] using hS
        · simpa [List.append_assoc] using hC
        · simpa [List.append_assoc] using hDl
        · simpa [List.append_assoc] using hX
        · simpa [List.append_assoc] using hY)
      (by
        intro p hp g hg
        simp only [Work.IntLib.cleanupParts, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact nP g hg
        · exact nB g hg
        · exact nR g hg
        · exact nQ g hg
        · exact nS g hg
        · exact nC g hg
        · exact nD g hg
        · exact nX g hg
        · exact nY g hg)
  have hev' : HvdH.Eval main Work.IntLib.Div.cleanup s s' n := by
    simpa [Work.IntLib.cleanup_eq_seqs] using hev
  refine ⟨s', n, hev', ?_, ?_, ?_⟩
  · have hmap : ((Work.IntLib.cleanupParts lP lB lR lQ lS lC lD lX lY).map
        (fun p => p.2.2.length)) =
        [lP.length, lB.length, lR.length, lQ.length, lS.length, lC.length, lD.length,
          lX.length, lY.length] := rfl
    have hlen : (Work.IntLib.cleanupParts lP lB lR lQ lS lC lD lX lY).length = 9 := by
      simp [Work.IntLib.cleanupParts]
    rw [hmap, hlen] at hn
    simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at hn
    omega
  · have h0not : ∀ p ∈ Work.IntLib.cleanupParts lP lB lR lQ lS lC lD lX lY,
        (0 : HvdH.Stk) ≠ p.1 := by
      intro p hp h0
      have hm : p.1 ∈ [Work.IntLib.Div.stP, Work.IntLib.Div.stB, Work.IntLib.Div.stR,
          Work.IntLib.Div.stQ, Work.IntLib.Div.stS, Work.IntLib.Div.stC, Work.IntLib.Div.stD,
          Work.IntLib.Div.stX, Work.IntLib.Div.stY] := by
        simpa [Work.IntLib.cleanupParts] using
          (List.mem_map.mpr ⟨p, hp, rfl⟩ :
            p.1 ∈ (Work.IntLib.cleanupParts lP lB lR lQ lS lC lD lX lY).map (fun p => p.1))
      rw [← h0] at hm
      exact absurd hm (by decide)
    exact hoth' 0 h0not
  · have hge10 : ∀ p ∈ Work.IntLib.cleanupParts lP lB lR lQ lS lC lD lX lY, ∀ j : HvdH.Stk,
        10 ≤ j.val → j ≠ p.1 := by
      intro p hp j hj hjp
      have hm : p.1 ∈ [Work.IntLib.Div.stP, Work.IntLib.Div.stB, Work.IntLib.Div.stR,
          Work.IntLib.Div.stQ, Work.IntLib.Div.stS, Work.IntLib.Div.stC, Work.IntLib.Div.stD,
          Work.IntLib.Div.stX, Work.IntLib.Div.stY] := by
        simpa [Work.IntLib.cleanupParts] using
          (List.mem_map.mpr ⟨p, hp, rfl⟩ :
            p.1 ∈ (Work.IntLib.cleanupParts lP lB lR lQ lS lC lD lX lY).map (fun p => p.1))
      have hlt : p.1.val < 10 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with h | h | h | h | h | h | h | h | h <;> (rw [h]; decide)
      have hjv : j.val = p.1.val := by rw [hjp]
      omega
    intro k hk
    fin_cases k
    · exact absurd rfl hk
    · exact hstk (Work.IntLib.Div.stP, Work.IntLib.gP, lP) (by simp [Work.IntLib.cleanupParts])
    · exact hstk (Work.IntLib.Div.stB, Work.IntLib.gB, lB) (by simp [Work.IntLib.cleanupParts])
    · exact hstk (Work.IntLib.Div.stR, Work.IntLib.gR, lR) (by simp [Work.IntLib.cleanupParts])
    · exact hstk (Work.IntLib.Div.stQ, Work.IntLib.gQ, lQ) (by simp [Work.IntLib.cleanupParts])
    · exact hstk (Work.IntLib.Div.stS, Work.IntLib.gS, lS) (by simp [Work.IntLib.cleanupParts])
    · exact hstk (Work.IntLib.Div.stC, Work.IntLib.gC, lC) (by simp [Work.IntLib.cleanupParts])
    · exact hstk (Work.IntLib.Div.stD, Work.IntLib.gD, lD) (by simp [Work.IntLib.cleanupParts])
    · exact hstk (Work.IntLib.Div.stX, Work.IntLib.gX, lX) (by simp [Work.IntLib.cleanupParts])
    · exact hstk (Work.IntLib.Div.stY, Work.IntLib.gY, lY) (by simp [Work.IntLib.cleanupParts])
    · exact (hoth' 10 (fun p hp => hge10 p hp 10 (by decide))).trans (hoth 10 (by decide))
    · exact (hoth' 11 (fun p hp => hge10 p hp 11 (by decide))).trans (hoth 11 (by decide))
    · exact (hoth' 12 (fun p hp => hge10 p hp 12 (by decide))).trans (hoth 12 (by decide))
    · exact (hoth' 13 (fun p hp => hge10 p hp 13 (by decide))).trans (hoth 13 (by decide))
    · exact (hoth' 14 (fun p hp => hge10 p hp 14 (by decide))).trans (hoth 14 (by decide))
    · exact (hoth' 15 (fun p hp => hge10 p hp 15 (by decide))).trans (hoth 15 (by decide))

end Work.IntLib
